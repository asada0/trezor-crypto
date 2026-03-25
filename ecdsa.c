/**
 * Copyright (c) 2013-2014 Tomas Dzetkulic
 * Copyright (c) 2013-2014 Pavol Rusnak
 * Copyright (c)      2015 Jochen Hoenicke
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES
 * OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
 * ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <cryptoaddress.h>

#ifdef ESP_PLATFORM
#include "esp_attr.h"
#include "esp_heap_caps.h"
#define PSRAM_ALLOC(size) heap_caps_malloc(size, MALLOC_CAP_SPIRAM)
#else
#define PSRAM_ALLOC(size) malloc(size)
#endif

#include "bignum.h"
#include "rand.h"
#include "sha2.h"
#include "ripemd160.h"
#include "hmac.h"
#include "ecdsa.h"
#include "base58.h"
#include "secp256k1.h"
#include "rfc6979.h"
#include "memzero.h"

// Set cp2 = cp1
void point_copy(const curve_point *cp1, curve_point *cp2)
{
	*cp2 = *cp1;
}

// cp2 = cp1 + cp2
void point_add(const ecdsa_curve *curve, const curve_point *cp1, curve_point *cp2)
{
	bignum256 lambda, inv, xr, yr;

	if (point_is_infinity(cp1)) {
		return;
	}
	if (point_is_infinity(cp2)) {
		point_copy(cp1, cp2);
		return;
	}
	if (point_is_equal(cp1, cp2)) {
		point_double(curve, cp2);
		return;
	}
	if (point_is_negative_of(cp1, cp2)) {
		point_set_infinity(cp2);
		return;
	}

	bn_subtractmod(&(cp2->x), &(cp1->x), &inv, &curve->prime);
	bn_inverse(&inv, &curve->prime);
	bn_subtractmod(&(cp2->y), &(cp1->y), &lambda, &curve->prime);
	bn_multiply(&inv, &lambda, &curve->prime);

	// xr = lambda^2 - x1 - x2
	xr = lambda;
	bn_multiply(&xr, &xr, &curve->prime);
	yr = cp1->x;
	bn_addmod(&yr, &(cp2->x), &curve->prime);
	bn_subtractmod(&xr, &yr, &xr, &curve->prime);
	bn_fast_mod(&xr, &curve->prime);
	bn_mod(&xr, &curve->prime);

	// yr = lambda (x1 - xr) - y1
	bn_subtractmod(&(cp1->x), &xr, &yr, &curve->prime);
	bn_multiply(&lambda, &yr, &curve->prime);
	bn_subtractmod(&yr, &(cp1->y), &yr, &curve->prime);
	bn_fast_mod(&yr, &curve->prime);
	bn_mod(&yr, &curve->prime);

	cp2->x = xr;
	cp2->y = yr;
}

// cp = cp + cp
void point_double(const ecdsa_curve *curve, curve_point *cp)
{
	bignum256 lambda, xr, yr;

	if (point_is_infinity(cp)) {
		return;
	}
	if (bn_is_zero(&(cp->y))) {
		point_set_infinity(cp);
		return;
	}

	// lambda = (3 x^2 + a) / (2 y)
	lambda = cp->y;
	bn_mult_k(&lambda, 2, &curve->prime);
	bn_inverse(&lambda, &curve->prime);

	xr = cp->x;
	bn_multiply(&xr, &xr, &curve->prime);
	bn_mult_k(&xr, 3, &curve->prime);
	bn_subi(&xr, -curve->a, &curve->prime);
	bn_multiply(&xr, &lambda, &curve->prime);

	// xr = lambda^2 - 2*x
	xr = lambda;
	bn_multiply(&xr, &xr, &curve->prime);
	yr = cp->x;
	bn_lshift(&yr);
	bn_subtractmod(&xr, &yr, &xr, &curve->prime);
	bn_fast_mod(&xr, &curve->prime);
	bn_mod(&xr, &curve->prime);

	// yr = lambda (x - xr) - y
	bn_subtractmod(&(cp->x), &xr, &yr, &curve->prime);
	bn_multiply(&lambda, &yr, &curve->prime);
	bn_subtractmod(&yr, &(cp->y), &yr, &curve->prime);
	bn_fast_mod(&yr, &curve->prime);
	bn_mod(&yr, &curve->prime);

	cp->x = xr;
	cp->y = yr;
}

// set point to internal representation of point at infinity
void point_set_infinity(curve_point *p)
{
	bn_zero(&(p->x));
	bn_zero(&(p->y));
}

// return true iff p represent point at infinity
// both coords are zero in internal representation
int point_is_infinity(const curve_point *p)
{
	return bn_is_zero(&(p->x)) && bn_is_zero(&(p->y));
}

// return true iff both points are equal
int point_is_equal(const curve_point *p, const curve_point *q)
{
	return bn_is_equal(&(p->x), &(q->x)) && bn_is_equal(&(p->y), &(q->y));
}

// returns true iff p == -q
// expects p and q be valid points on curve other than point at infinity
int point_is_negative_of(const curve_point *p, const curve_point *q)
{
	// if P == (x, y), then -P would be (x, -y) on this curve
	if (!bn_is_equal(&(p->x), &(q->x))) {
		return 0;
	}

	// we shouldn't hit this for a valid point
	if (bn_is_zero(&(p->y))) {
		return 0;
	}

	return !bn_is_equal(&(p->y), &(q->y));
}

// Negate a (modulo prime) if cond is 0xffffffff, keep it if cond is 0.
// The timing of this function does not depend on cond.
void conditional_negate(uint32_t cond, bignum256 *a, const bignum256 *prime)
{
	int j;
	uint32_t tmp = 1;
	assert(a->val[8] < 0x20000);
	for (j = 0; j < 8; j++) {
		tmp += 0x3fffffff + 2*prime->val[j] - a->val[j];
		a->val[j] = ((tmp & 0x3fffffff) & cond) | (a->val[j] & ~cond);
		tmp >>= 30;
	}
	tmp += 0x3fffffff + 2*prime->val[j] - a->val[j];
	a->val[j] = ((tmp & 0x3fffffff) & cond) | (a->val[j] & ~cond);
	assert(a->val[8] < 0x20000);
}

typedef struct jacobian_curve_point {
	bignum256 x, y, z;
} jacobian_curve_point;

/* Thread-safe workspace structs (replaces PSRAM_STATIC / static CONFIDENTIAL).
 * Each function allocates its own workspace via PSRAM_ALLOC, preventing
 * race conditions when multiple tasks call trezor_crypto concurrently. */
typedef struct {
	bignum256 r, h, r2;
	bignum256 hcby, hsqx;
	bignum256 xz, yz, az;
} pja_ws_t;

typedef struct {
	bignum256 az4, m, msq, ysq, xysq;
} pjd_ws_t;

typedef struct {
	bignum256 a;
	jacobian_curve_point jres;
	pja_ws_t pja;
	pjd_ws_t pjd;
} point_mult_ws_t;

typedef struct {
	bignum256 a;
	jacobian_curve_point jres;
	pja_ws_t pja;
} scalar_mult_ws_t;

typedef struct {
	curve_point R;
	bignum256 k, z, randk;
	rfc6979_state rng;
} sign_ws_t;

typedef struct {
	bignum256 r, s, e;
	curve_point cp, cp2;
} verify_recover_ws_t;

typedef struct {
	curve_point pub, res;
	bignum256 r, s, z;
} verify_digest_ws_t;

// generate random K for signing/side-channel noise
static void generate_k_random(bignum256 *k, const bignum256 *prime) {
	do {
		int i;
		for (i = 0; i < 8; i++) {
			k->val[i] = random32() & 0x3FFFFFFF;
		}
		k->val[8] = random32() & 0xFFFF;
		// check that k is in range and not zero.
	} while (bn_is_zero(k) || !bn_is_less(k, prime));
}

void curve_to_jacobian(const curve_point *p, jacobian_curve_point *jp, const bignum256 *prime) {
	// randomize z coordinate
	generate_k_random(&jp->z, prime);

	jp->x = jp->z;
	bn_multiply(&jp->z, &jp->x, prime);
	// x = z^2
	jp->y = jp->x;
	bn_multiply(&jp->z, &jp->y, prime);
	// y = z^3

	bn_multiply(&p->x, &jp->x, prime);
	bn_multiply(&p->y, &jp->y, prime);
}

void jacobian_to_curve(const jacobian_curve_point *jp, curve_point *p, const bignum256 *prime) {
	p->y = jp->z;
	bn_inverse(&p->y, prime);
	// p->y = z^-1
	p->x = p->y;
	bn_multiply(&p->x, &p->x, prime);
	// p->x = z^-2
	bn_multiply(&p->x, &p->y, prime);
	// p->y = z^-3
	bn_multiply(&jp->x, &p->x, prime);
	// p->x = jp->x * z^-2
	bn_multiply(&jp->y, &p->y, prime);
	// p->y = jp->y * z^-3
	bn_mod(&p->x, prime);
	bn_mod(&p->y, prime);
}

void point_jacobian_add(const curve_point *p1, jacobian_curve_point *p2, const ecdsa_curve *curve, pja_ws_t *ws) {
	int is_doubling;
	const bignum256 *prime = &curve->prime;
	int a = curve->a;

	assert (-3 <= a && a <= 0);

	/* First we bring p1 to the same denominator:
	 * x1' := x1 * z2^2
	 * y1' := y1 * z2^3
	 */
	/*
	 * lambda  = ((y1' - y2)/z2^3) / ((x1' - x2)/z2^2)
	 *         = (y1' - y2) / (x1' - x2) z2
	 * x3/z3^2 = lambda^2 - (x1' + x2)/z2^2
	 * y3/z3^3 = 1/2 lambda * (2x3/z3^2 - (x1' + x2)/z2^2) + (y1'+y2)/z2^3
	 *
	 * For the special case x1=x2, y1=y2 (doubling) we have
	 * lambda = 3/2 ((x2/z2^2)^2 + a) / (y2/z2^3)
	 *        = 3/2 (x2^2 + a*z2^4) / y2*z2)
	 *
	 * to get rid of fraction we write lambda as
	 * lambda = r / (h*z2)
	 * with  r = is_doubling ? 3/2 x2^2 + az2^4 : (y1 - y2)
	 *       h = is_doubling ?      y1+y2       : (x1 - x2)
	 *
	 * With z3 = h*z2  (the denominator of lambda)
	 * we get x3 = lambda^2*z3^2 - (x1' + x2)/z2^2*z3^2
	 *           = r^2 - h^2 * (x1' + x2)
	 *    and y3 = 1/2 r * (2x3 - h^2*(x1' + x2)) + h^3*(y1' + y2)
	 */

	/* h = x1 - x2
	 * r = y1 - y2
	 * x3 = r^2 - h^3 - 2*h^2*x2
	 * y3 = r*(h^2*x2 - x3) - h^3*y2
	 * z3 = h*z2
	 */

	ws->xz = p2->z;
	bn_multiply(&ws->xz, &ws->xz, prime); // xz = z2^2
	ws->yz = p2->z;
	bn_multiply(&ws->xz, &ws->yz, prime); // yz = z2^3

	if (a != 0) {
		ws->az  = ws->xz;
		bn_multiply(&ws->az, &ws->az, prime);   // az = z2^4
		bn_mult_k(&ws->az, -a, prime);      // az = -az2^4
	}

	bn_multiply(&p1->x, &ws->xz, prime);        // xz = x1' = x1*z2^2;
	ws->h = ws->xz;
	bn_subtractmod(&ws->h, &p2->x, &ws->h, prime);
	bn_fast_mod(&ws->h, prime);
	// h = x1' - x2;

	bn_add(&ws->xz, &p2->x);
	// xz = x1' + x2

	// check for h == 0 % prime.  Note that h never normalizes to
	// zero, since h = x1' + 2*prime - x2 > 0 and a positive
	// multiple of prime is always normalized to prime by
	// bn_fast_mod.
	is_doubling = bn_is_equal(&ws->h, prime);

	bn_multiply(&p1->y, &ws->yz, prime);        // yz = y1' = y1*z2^3;
	bn_subtractmod(&ws->yz, &p2->y, &ws->r, prime);
	// r = y1' - y2;

	bn_add(&ws->yz, &p2->y);
	// yz = y1' + y2

	ws->r2 = p2->x;
	bn_multiply(&ws->r2, &ws->r2, prime);
	bn_mult_k(&ws->r2, 3, prime);

	if (a != 0) {
		// subtract -a z2^4, i.e, add a z2^4
		bn_subtractmod(&ws->r2, &ws->az, &ws->r2, prime);
	}
	bn_cmov(&ws->r, is_doubling, &ws->r2, &ws->r);
	bn_cmov(&ws->h, is_doubling, &ws->yz, &ws->h);


	// hsqx = h^2
	ws->hsqx = ws->h;
	bn_multiply(&ws->hsqx, &ws->hsqx, prime);

	// hcby = h^3
	ws->hcby = ws->h;
	bn_multiply(&ws->hsqx, &ws->hcby, prime);

	// hsqx = h^2 * (x1 + x2)
	bn_multiply(&ws->xz, &ws->hsqx, prime);

	// hcby = h^3 * (y1 + y2)
	bn_multiply(&ws->yz, &ws->hcby, prime);

	// z3 = h*z2
	bn_multiply(&ws->h, &p2->z, prime);

	// x3 = r^2 - h^2 (x1 + x2)
	p2->x = ws->r;
	bn_multiply(&p2->x, &p2->x, prime);
	bn_subtractmod(&p2->x, &ws->hsqx, &p2->x, prime);
	bn_fast_mod(&p2->x, prime);

	// y3 = 1/2 (r*(h^2 (x1 + x2) - 2x3) - h^3 (y1 + y2))
	bn_subtractmod(&ws->hsqx, &p2->x, &p2->y, prime);
	bn_subtractmod(&p2->y, &p2->x, &p2->y, prime);
	bn_multiply(&ws->r, &p2->y, prime);
	bn_subtractmod(&p2->y, &ws->hcby, &p2->y, prime);
	bn_mult_half(&p2->y, prime);
	bn_fast_mod(&p2->y, prime);
}

void point_jacobian_double(jacobian_curve_point *p, const ecdsa_curve *curve, pjd_ws_t *ws) {
	const bignum256 *prime = &curve->prime;

	assert (-3 <= curve->a && curve->a <= 0);
	/* usual algorithm:
	 *
	 * lambda  = (3((x/z^2)^2 + a) / 2y/z^3) = (3x^2 + az^4)/2yz
	 * x3/z3^2 = lambda^2 - 2x/z^2
	 * y3/z3^3 = lambda * (x/z^2 - x3/z3^2) - y/z^3
	 *
	 * to get rid of fraction we set
	 *  m = (3 x^2 + az^4) / 2
	 * Hence,
	 *  lambda = m / yz = m / z3
	 *
	 * With z3 = yz  (the denominator of lambda)
	 * we get x3 = lambda^2*z3^2 - 2*x/z^2*z3^2
	 *           = m^2 - 2*xy^2
	 *    and y3 = (lambda * (x/z^2 - x3/z3^2) - y/z^3) * z3^3
	 *           = m * (xy^2 - x3) - y^4
	 */

	/* m = (3*x^2 + a z^4) / 2
	 * x3 = m^2 - 2*xy^2
	 * y3 = m*(xy^2 - x3) - 8y^4
	 * z3 = y*z
	 */

	ws->m = p->x;
	bn_multiply(&ws->m, &ws->m, prime);
	bn_mult_k(&ws->m, 3, prime);

	ws->az4 = p->z;
	bn_multiply(&ws->az4, &ws->az4, prime);
	bn_multiply(&ws->az4, &ws->az4, prime);
	bn_mult_k(&ws->az4, -curve->a, prime);
	bn_subtractmod(&ws->m, &ws->az4, &ws->m, prime);
	bn_mult_half(&ws->m, prime);

	// msq = m^2
	ws->msq = ws->m;
	bn_multiply(&ws->msq, &ws->msq, prime);
	// ysq = y^2
	ws->ysq = p->y;
	bn_multiply(&ws->ysq, &ws->ysq, prime);
	// xysq = xy^2
	ws->xysq = p->x;
	bn_multiply(&ws->ysq, &ws->xysq, prime);

	// z3 = yz
	bn_multiply(&p->y, &p->z, prime);

	// x3 = m^2 - 2*xy^2
	p->x = ws->xysq;
	bn_lshift(&p->x);
	bn_fast_mod(&p->x, prime);
	bn_subtractmod(&ws->msq, &p->x, &p->x, prime);
	bn_fast_mod(&p->x, prime);

	// y3 = m*(xy^2 - x3) - y^4
	bn_subtractmod(&ws->xysq, &p->x, &p->y, prime);
	bn_multiply(&ws->m, &p->y, prime);
	bn_multiply(&ws->ysq, &ws->ysq, prime);
	bn_subtractmod(&p->y, &ws->ysq, &p->y, prime);
	bn_fast_mod(&p->y, prime);
}

// res = k * p
void point_multiply(const ecdsa_curve *curve, const bignum256 *k, const curve_point *p, curve_point *res)
{
	// this algorithm is loosely based on
	//  Katsuyuki Okeya and Tsuyoshi Takagi, The Width-w NAF Method Provides
	//  Small Memory and Fast Elliptic Scalar Multiplications Secure against
	//  Side Channel Attacks.
	assert (bn_is_less(k, &curve->order));

	int i, j;
	point_mult_ws_t *ws = (point_mult_ws_t *)PSRAM_ALLOC(sizeof(point_mult_ws_t));
	if (!ws) return;
	uint32_t *aptr;
	uint32_t abits;
	int ashift;
	uint32_t is_even = (k->val[0] & 1) - 1;
	uint32_t bits, sign, nsign;
	curve_point pmult[8];
	const bignum256 *prime = &curve->prime;

	// is_even = 0xffffffff if k is even, 0 otherwise.

	// add 2^256.
	// make number odd: subtract curve->order if even
	uint32_t tmp = 1;
	uint32_t is_non_zero = 0;
	for (j = 0; j < 8; j++) {
		is_non_zero |= k->val[j];
		tmp += 0x3fffffff + k->val[j] - (curve->order.val[j] & is_even);
		ws->a.val[j] = tmp & 0x3fffffff;
		tmp >>= 30;
	}
	is_non_zero |= k->val[j];
	ws->a.val[j] = tmp + 0xffff + k->val[j] - (curve->order.val[j] & is_even);
	assert((ws->a.val[0] & 1) != 0);

	// special case 0*p:  just return zero. We don't care about constant time.
	if (!is_non_zero) {
		point_set_infinity(res);
		goto cleanup;
	}

	// Now a = k + 2^256 (mod curve->order) and a is odd.
	//
	// The idea is to bring the new a into the form.
	// sum_{i=0..64} a[i] 16^i,  where |a[i]| < 16 and a[i] is odd.
	// a[0] is odd, since a is odd.  If a[i] would be even, we can
	// add 1 to it and subtract 16 from a[i-1].  Afterwards,
	// a[64] = 1, which is the 2^256 that we added before.
	//
	// Since k = a - 2^256 (mod curve->order), we can compute
	//   k*p = sum_{i=0..63} a[i] 16^i * p
	//
	// We compute |a[i]| * p in advance for all possible
	// values of |a[i]| * p.  pmult[i] = (2*i+1) * p
	// We compute p, 3*p, ..., 15*p and store it in the table pmult.
	// store p^2 temporarily in pmult[7]
	pmult[7] = *p;
	point_double(curve, &pmult[7]);
	// compute 3*p, etc by repeatedly adding p^2.
	pmult[0] = *p;
	for (i = 1; i < 8; i++) {
		pmult[i] = pmult[7];
		point_add(curve, &pmult[i-1], &pmult[i]);
	}

	// now compute  res = sum_{i=0..63} a[i] * 16^i * p step by step,
	// starting with i = 63.
	// initialize jres = |a[63]| * p.
	// Note that a[i] = a>>(4*i) & 0xf if (a&0x10) != 0
	// and - (16 - (a>>(4*i) & 0xf)) otherwise.   We can compute this as
	//   ((a ^ (((a >> 4) & 1) - 1)) & 0xf) >> 1
	// since a is odd.
	aptr = &ws->a.val[8];
	abits = *aptr;
	ashift = 12;
	bits = abits >> ashift;
	sign = (bits >> 4) - 1;
	bits ^= sign;
	bits &= 15;
	curve_to_jacobian(&pmult[bits>>1], &ws->jres, prime);
	for (i = 62; i >= 0; i--) {
		// sign = sign(a[i+1])  (0xffffffff for negative, 0 for positive)
		// invariant jres = (-1)^sign sum_{j=i+1..63} (a[j] * 16^{j-i-1} * p)
		// abits >> (ashift - 4) = lowbits(a >> (i*4))

		point_jacobian_double(&ws->jres, curve, &ws->pjd);
		point_jacobian_double(&ws->jres, curve, &ws->pjd);
		point_jacobian_double(&ws->jres, curve, &ws->pjd);
		point_jacobian_double(&ws->jres, curve, &ws->pjd);

		// get lowest 5 bits of a >> (i*4).
		ashift -= 4;
		if (ashift < 0) {
			// the condition only depends on the iteration number and
			// leaks no private information to a side-channel.
			bits = abits << (-ashift);
			abits = *(--aptr);
			ashift += 30;
			bits |= abits >> ashift;
		} else {
			bits = abits >> ashift;
		}
		bits &= 31;
		nsign = (bits >> 4) - 1;
		bits ^= nsign;
		bits &= 15;

		// negate last result to make signs of this round and the
		// last round equal.
		conditional_negate(sign ^ nsign, &ws->jres.z, prime);

		// add odd factor
		point_jacobian_add(&pmult[bits >> 1], &ws->jres, curve, &ws->pja);
		sign = nsign;
	}
	conditional_negate(sign, &ws->jres.z, prime);
	jacobian_to_curve(&ws->jres, res, prime);

cleanup:
	memzero(ws, sizeof(point_mult_ws_t));
	free(ws);
}

#if USE_PRECOMPUTED_CP

// res = k * G
// k must be a normalized number with 0 <= k < curve->order
void scalar_multiply(const ecdsa_curve *curve, const bignum256 *k, curve_point *res)
{
	assert (bn_is_less(k, &curve->order));

	int i, j;
	scalar_mult_ws_t *ws = (scalar_mult_ws_t *)PSRAM_ALLOC(sizeof(scalar_mult_ws_t));
	if (!ws) return;
	uint32_t is_even = (k->val[0] & 1) - 1;
	uint32_t lowbits;
	const bignum256 *prime = &curve->prime;

	// is_even = 0xffffffff if k is even, 0 otherwise.

	// add 2^256.
	// make number odd: subtract curve->order if even
	uint32_t tmp = 1;
	uint32_t is_non_zero = 0;
	for (j = 0; j < 8; j++) {
		is_non_zero |= k->val[j];
		tmp += 0x3fffffff + k->val[j] - (curve->order.val[j] & is_even);
		ws->a.val[j] = tmp & 0x3fffffff;
		tmp >>= 30;
	}
	is_non_zero |= k->val[j];
	ws->a.val[j] = tmp + 0xffff + k->val[j] - (curve->order.val[j] & is_even);
	assert((ws->a.val[0] & 1) != 0);

	// special case 0*G:  just return zero. We don't care about constant time.
	if (!is_non_zero) {
		point_set_infinity(res);
		goto cleanup;
	}

	// Now a = k + 2^256 (mod curve->order) and a is odd.
	//
	// The idea is to bring the new a into the form.
	// sum_{i=0..64} a[i] 16^i,  where |a[i]| < 16 and a[i] is odd.
	// a[0] is odd, since a is odd.  If a[i] would be even, we can
	// add 1 to it and subtract 16 from a[i-1].  Afterwards,
	// a[64] = 1, which is the 2^256 that we added before.
	//
	// Since k = a - 2^256 (mod curve->order), we can compute
	//   k*G = sum_{i=0..63} a[i] 16^i * G
	//
	// We have a big table curve->cp that stores all possible
	// values of |a[i]| 16^i * G.
	// curve->cp[i][j] = (2*j+1) * 16^i * G

	// now compute  res = sum_{i=0..63} a[i] * 16^i * G step by step.
	// initial res = |a[0]| * G.  Note that a[0] = a & 0xf if (a&0x10) != 0
	// and - (16 - (a & 0xf)) otherwise.   We can compute this as
	//   ((a ^ (((a >> 4) & 1) - 1)) & 0xf) >> 1
	// since a is odd.
	lowbits = ws->a.val[0] & ((1 << 5) - 1);
	lowbits ^= (lowbits >> 4) - 1;
	lowbits &= 15;
	curve_to_jacobian(&curve->cp[0][lowbits >> 1], &ws->jres, prime);
	for (i = 1; i < 64; i ++) {
		// invariant res = sign(a[i-1]) sum_{j=0..i-1} (a[j] * 16^j * G)

		// shift a by 4 places.
		for (j = 0; j < 8; j++) {
			ws->a.val[j] = (ws->a.val[j] >> 4) | ((ws->a.val[j + 1] & 0xf) << 26);
		}
		ws->a.val[j] >>= 4;
		// a = old(a)>>(4*i)
		// a is even iff sign(a[i-1]) = -1

		lowbits = ws->a.val[0] & ((1 << 5) - 1);
		lowbits ^= (lowbits >> 4) - 1;
		lowbits &= 15;
		// negate last result to make signs of this round and the
		// last round equal.
		conditional_negate((lowbits & 1) - 1, &ws->jres.y, prime);

		// add odd factor
		point_jacobian_add(&curve->cp[i][lowbits >> 1], &ws->jres, curve, &ws->pja);
	}
	conditional_negate(((ws->a.val[0] >> 4) & 1) - 1, &ws->jres.y, prime);
	jacobian_to_curve(&ws->jres, res, prime);

cleanup:
	memzero(ws, sizeof(scalar_mult_ws_t));
	free(ws);
}

#else

void scalar_multiply(const ecdsa_curve *curve, const bignum256 *k, curve_point *res)
{
	point_multiply(curve, k, &curve->G, res);
}

#endif

int ecdh_multiply(const ecdsa_curve *curve, const uint8_t *priv_key, const uint8_t *pub_key, uint8_t *session_key)
{
	curve_point point;
	if (!ecdsa_read_pubkey(curve, pub_key, &point)) {
		return 1;
	}

	bignum256 k;
	bn_read_be(priv_key, &k);
	point_multiply(curve, &k, &point, &point);
	memzero(&k, sizeof(k));

	session_key[0] = 0x04;
	bn_write_be(&point.x, session_key + 1);
	bn_write_be(&point.y, session_key + 33);
	memzero(&point, sizeof(point));

	return 0;
}

void init_rfc6979(const uint8_t *priv_key, const uint8_t *hash, rfc6979_state *state) {
	uint8_t bx[2*32];
	uint8_t buf[32 + 1 + 2*32];

	memcpy(bx, priv_key, 32);
	memcpy(bx+32, hash, 32);

	memset(state->v, 1, sizeof(state->v));
	memset(state->k, 0, sizeof(state->k));

	memcpy(buf, state->v, sizeof(state->v));
	buf[sizeof(state->v)] = 0x00;
	memcpy(buf + sizeof(state->v) + 1, bx, 64);
	hmac_sha256(state->k, sizeof(state->k), buf, sizeof(buf), state->k);
	hmac_sha256(state->k, sizeof(state->k), state->v, sizeof(state->v), state->v);

	memcpy(buf, state->v, sizeof(state->v));
	buf[sizeof(state->v)] = 0x01;
	memcpy(buf + sizeof(state->v) + 1, bx, 64);
	hmac_sha256(state->k, sizeof(state->k), buf, sizeof(buf), state->k);
	hmac_sha256(state->k, sizeof(state->k), state->v, sizeof(state->v), state->v);

	memzero(bx, sizeof(bx));
	memzero(buf, sizeof(buf));
}

// generate next number from deterministic random number generator
void generate_rfc6979(uint8_t rnd[32], rfc6979_state *state)
{
	uint8_t buf[32 + 1];

	hmac_sha256(state->k, sizeof(state->k), state->v, sizeof(state->v), state->v);
	memcpy(buf, state->v, sizeof(state->v));
	buf[sizeof(state->v)] = 0x00;
	hmac_sha256(state->k, sizeof(state->k), buf, sizeof(state->v) + 1, state->k);
	hmac_sha256(state->k, sizeof(state->k), state->v, sizeof(state->v), state->v);
	memcpy(rnd, buf, 32);
	memzero(buf, sizeof(buf));
}

// generate K in a deterministic way, according to RFC6979
// http://tools.ietf.org/html/rfc6979
void generate_k_rfc6979(bignum256 *k, rfc6979_state *state)
{
	uint8_t buf[32];
	generate_rfc6979(buf, state);
	bn_read_be(buf, k);
	memzero(buf, sizeof(buf));
}

// msg is a data to be signed
// msg_len is the message length
int ecdsa_sign(const ecdsa_curve *curve, HasherType hasher_type, const uint8_t *priv_key, const uint8_t *msg, uint32_t msg_len, uint8_t *sig, uint8_t *pby, int (*is_canonical)(uint8_t by, uint8_t sig[64]))
{
	uint8_t hash[32];
	hasher_Raw(hasher_type, msg, msg_len, hash);
	int res = ecdsa_sign_digest(curve, priv_key, hash, sig, pby, is_canonical);
	memzero(hash, sizeof(hash));
	return res;

}

// msg is a data to be signed
// msg_len is the message length
int ecdsa_sign_double(const ecdsa_curve *curve, HasherType hasher_type, const uint8_t *priv_key, const uint8_t *msg, uint32_t msg_len, uint8_t *sig, uint8_t *pby, int (*is_canonical)(uint8_t by, uint8_t sig[64]))
{
	uint8_t hash[32];
	hasher_Raw(hasher_type, msg, msg_len, hash);
	hasher_Raw(hasher_type, hash, 32, hash);
	int res = ecdsa_sign_digest(curve, priv_key, hash, sig, pby, is_canonical);
	memzero(hash, sizeof(hash));
	return res;
}

// uses secp256k1 curve
// priv_key is a 32 byte big endian stored number
// sig is 64 bytes long array for the signature
// digest is 32 bytes of digest
// is_canonical is an optional function that checks if the signature
// conforms to additional coin-specific rules.
int ecdsa_sign_digest(const ecdsa_curve *curve, const uint8_t *priv_key, const uint8_t *digest, uint8_t *sig, uint8_t *pby, int (*is_canonical)(uint8_t by, uint8_t sig[64]))
{
	int i;
	int result = -1;
	sign_ws_t *ws = (sign_ws_t *)PSRAM_ALLOC(sizeof(sign_ws_t));
	if (!ws) return -1;
	bignum256 *s = &ws->R.y;
	uint8_t by; // signature recovery byte

#if USE_RFC6979
	init_rfc6979(priv_key, digest, &ws->rng);
#endif

	bn_read_be(digest, &ws->z);

	for (i = 0; i < 10000; i++) {

#if USE_RFC6979
		// generate K deterministically
		generate_k_rfc6979(&ws->k, &ws->rng);
		// if k is too big or too small, we don't like it
		if (bn_is_zero(&ws->k) || !bn_is_less(&ws->k, &curve->order)) {
			continue;
		}
#else
		// generate random number k
		generate_k_random(&ws->k, &curve->order);
#endif

		// compute k*G
		scalar_multiply(curve, &ws->k, &ws->R);
		by = ws->R.y.val[0] & 1;
		// r = (rx mod n)
		if (!bn_is_less(&ws->R.x, &curve->order)) {
			bn_subtract(&ws->R.x, &curve->order, &ws->R.x);
			by |= 2;
		}
		// if r is zero, we retry
		if (bn_is_zero(&ws->R.x)) {
			continue;
		}

		// randomize operations to counter side-channel attacks
		generate_k_random(&ws->randk, &curve->order);
		bn_multiply(&ws->randk, &ws->k, &curve->order); // k*rand
		bn_inverse(&ws->k, &curve->order);         // (k*rand)^-1
		bn_read_be(priv_key, s);               // priv
		bn_multiply(&ws->R.x, s, &curve->order);   // R.x*priv
		bn_add(s, &ws->z);                         // R.x*priv + z
		bn_multiply(&ws->k, s, &curve->order);     // (k*rand)^-1 (R.x*priv + z)
		bn_multiply(&ws->randk, s, &curve->order);  // k^-1 (R.x*priv + z)
		bn_mod(s, &curve->order);
		// if s is zero, we retry
		if (bn_is_zero(s)) {
			continue;
		}

		// if S > order/2 => S = -S
		if (bn_is_less(&curve->order_half, s)) {
			bn_subtract(&curve->order, s, s);
			by ^= 1;
		}
		// we are done, R.x and s is the result signature
		bn_write_be(&ws->R.x, sig);
		bn_write_be(s, sig + 32);

		// check if the signature is acceptable or retry
		if (is_canonical && !is_canonical(by, sig)) {
			continue;
		}

		if (pby) {
			*pby = by;
		}

		result = 0;
		goto cleanup;
	}

	// Too many retries without a valid signature
	// -> fail with an error
cleanup:
	memzero(ws, sizeof(sign_ws_t));
	free(ws);
	return result;
}

void ecdsa_get_public_key33(const ecdsa_curve *curve, const uint8_t *priv_key, uint8_t *pub_key)
{
	curve_point R;
	bignum256 k;

	bn_read_be(priv_key, &k);
	// compute k*G
	scalar_multiply(curve, &k, &R);
	pub_key[0] = 0x02 | (R.y.val[0] & 0x01);
	bn_write_be(&R.x, pub_key + 1);
	memzero(&R, sizeof(R));
	memzero(&k, sizeof(k));
}

void ecdsa_get_public_key65(const ecdsa_curve *curve, const uint8_t *priv_key, uint8_t *pub_key)
{
	curve_point R;
	bignum256 k;

	bn_read_be(priv_key, &k);
	// compute k*G
	scalar_multiply(curve, &k, &R);
	pub_key[0] = 0x04;
	bn_write_be(&R.x, pub_key + 1);
	bn_write_be(&R.y, pub_key + 33);
	memzero(&R, sizeof(R));
	memzero(&k, sizeof(k));
}

int ecdsa_uncompress_pubkey(const ecdsa_curve *curve, const uint8_t *pub_key, uint8_t *uncompressed)
{
	curve_point pub;

	if (!ecdsa_read_pubkey(curve, pub_key, &pub)) {
		return 0;
	}

	uncompressed[0] = 4;
	bn_write_be(&pub.x, uncompressed + 1);
	bn_write_be(&pub.y, uncompressed + 33);

	return 1;
}

void ecdsa_get_pubkeyhash(const uint8_t *pub_key, HasherType hasher_type, uint8_t *pubkeyhash)
{
	uint8_t h[HASHER_DIGEST_LENGTH];
	if (pub_key[0] == 0x04) {  // uncompressed format
		hasher_Raw(hasher_type, pub_key, 65, h);
	} else if (pub_key[0] == 0x00) { // point at infinity
		hasher_Raw(hasher_type, pub_key,  1, h);
	} else { // expecting compressed format
		hasher_Raw(hasher_type, pub_key, 33, h);
	}
	ripemd160(h, HASHER_DIGEST_LENGTH, pubkeyhash);
	memzero(h, sizeof(h));
}

void ecdsa_get_address_raw(const uint8_t *pub_key, uint32_t version, HasherType hasher_type, uint8_t *addr_raw)
{
	size_t prefix_len = address_prefix_bytes_len(version);
	address_write_prefix_bytes(version, addr_raw);
	ecdsa_get_pubkeyhash(pub_key, hasher_type, addr_raw + prefix_len);
}

void ecdsa_get_address(const uint8_t *pub_key, uint32_t version, HasherType hasher_type, char *addr, int addrsize)
{
	uint8_t raw[MAX_ADDR_RAW_SIZE];
	size_t prefix_len = address_prefix_bytes_len(version);
	ecdsa_get_address_raw(pub_key, version, hasher_type, raw);
	base58_encode_check(raw, 20 + prefix_len, hasher_type, addr, addrsize);
	// not as important to clear this one, but we might as well
	memzero(raw, sizeof(raw));
}

void ecdsa_get_address_segwit_p2sh_raw(const uint8_t *pub_key, uint32_t version, HasherType hasher_type, uint8_t *addr_raw)
{
	size_t prefix_len = address_prefix_bytes_len(version);
	uint8_t digest[32];
	addr_raw[0] = 0; // version byte
	addr_raw[1] = 20; // push 20 bytes
	ecdsa_get_pubkeyhash(pub_key, hasher_type, addr_raw + 2);
	hasher_Raw(hasher_type, addr_raw, 22, digest);
	address_write_prefix_bytes(version, addr_raw);
	ripemd160(digest, 32, addr_raw + prefix_len);
}

void ecdsa_get_address_segwit_p2sh(const uint8_t *pub_key, uint32_t version, HasherType hasher_type, char *addr, int addrsize)
{
	uint8_t raw[MAX_ADDR_RAW_SIZE];
	size_t prefix_len = address_prefix_bytes_len(version);
	ecdsa_get_address_segwit_p2sh_raw(pub_key, version, hasher_type, raw);
	base58_encode_check(raw, prefix_len + 20, hasher_type, addr, addrsize);
	memzero(raw, sizeof(raw));
}

void ecdsa_get_wif(const uint8_t *priv_key, uint32_t version, HasherType hasher_type, char *wif, int wifsize)
{
	uint8_t wif_raw[MAX_WIF_RAW_SIZE];
	size_t prefix_len = address_prefix_bytes_len(version);
	address_write_prefix_bytes(version, wif_raw);
	memcpy(wif_raw + prefix_len, priv_key, 32);
	wif_raw[prefix_len + 32] = 0x01;
	base58_encode_check(wif_raw, prefix_len + 32 + 1, hasher_type, wif, wifsize);
	// private keys running around our stack can cause trouble
	memzero(wif_raw, sizeof(wif_raw));
}

int ecdsa_address_decode(const char *addr, uint32_t version, HasherType hasher_type, uint8_t *out)
{
	if (!addr) return 0;
	int prefix_len = address_prefix_bytes_len(version);
	return base58_decode_check(addr, hasher_type, out, 20 + prefix_len) == 20 + prefix_len
		&& address_check_prefix(out, version);
}

void uncompress_coords(const ecdsa_curve *curve, uint8_t odd, const bignum256 *x, bignum256 *y)
{
	// y^2 = x^3 + a*x + b
	memcpy(y, x, sizeof(bignum256));         // y is x
	bn_multiply(x, y, &curve->prime);        // y is x^2
	bn_subi(y, -curve->a, &curve->prime);    // y is x^2 + a
	bn_multiply(x, y, &curve->prime);        // y is x^3 + ax
	bn_add(y, &curve->b);                    // y is x^3 + ax + b
	bn_sqrt(y, &curve->prime);               // y = sqrt(y)
	if ((odd & 0x01) != (y->val[0] & 1)) {
		bn_subtract(&curve->prime, y, y);   // y = -y
	}
}

int ecdsa_read_pubkey(const ecdsa_curve *curve, const uint8_t *pub_key, curve_point *pub)
{
	if (!curve) {
		curve = &secp256k1;
	}
	if (pub_key[0] == 0x04) {
		bn_read_be(pub_key + 1, &(pub->x));
		bn_read_be(pub_key + 33, &(pub->y));
		return ecdsa_validate_pubkey(curve, pub);
	}
	if (pub_key[0] == 0x02 || pub_key[0] == 0x03) { // compute missing y coords
		bn_read_be(pub_key + 1, &(pub->x));
		uncompress_coords(curve, pub_key[0], &(pub->x), &(pub->y));
		return ecdsa_validate_pubkey(curve, pub);
	}
	// error
	return 0;
}

// Verifies that:
//   - pub is not the point at infinity.
//   - pub->x and pub->y are in range [0,p-1].
//   - pub is on the curve.

int ecdsa_validate_pubkey(const ecdsa_curve *curve, const curve_point *pub)
{
	bignum256 y_2, x3_ax_b;

	if (point_is_infinity(pub)) {
		return 0;
	}

	if (!bn_is_less(&(pub->x), &curve->prime) || !bn_is_less(&(pub->y), &curve->prime)) {
		return 0;
	}

	memcpy(&y_2, &(pub->y), sizeof(bignum256));
	memcpy(&x3_ax_b, &(pub->x), sizeof(bignum256));

	// y^2
	bn_multiply(&(pub->y), &y_2, &curve->prime);
	bn_mod(&y_2, &curve->prime);

	// x^3 + ax + b
	bn_multiply(&(pub->x), &x3_ax_b, &curve->prime);  // x^2
	bn_subi(&x3_ax_b, -curve->a, &curve->prime);      // x^2 + a
	bn_multiply(&(pub->x), &x3_ax_b, &curve->prime);  // x^3 + ax
	bn_addmod(&x3_ax_b, &curve->b, &curve->prime);    // x^3 + ax + b
	bn_mod(&x3_ax_b, &curve->prime);

	if (!bn_is_equal(&x3_ax_b, &y_2)) {
		return 0;
	}

	return 1;
}

// uses secp256k1 curve
// pub_key - 65 bytes uncompressed key
// signature - 64 bytes signature
// msg is a data that was signed
// msg_len is the message length

int ecdsa_verify(const ecdsa_curve *curve, HasherType hasher_type, const uint8_t *pub_key, const uint8_t *sig, const uint8_t *msg, uint32_t msg_len)
{
	uint8_t hash[32];
	hasher_Raw(hasher_type, msg, msg_len, hash);
	int res = ecdsa_verify_digest(curve, pub_key, sig, hash);
	memzero(hash, sizeof(hash));
	return res;
}

int ecdsa_verify_double(const ecdsa_curve *curve, HasherType hasher_type, const uint8_t *pub_key, const uint8_t *sig, const uint8_t *msg, uint32_t msg_len)
{
	uint8_t hash[32];
	hasher_Raw(hasher_type, msg, msg_len, hash);
	hasher_Raw(hasher_type, hash, 32, hash);
	int res = ecdsa_verify_digest(curve, pub_key, sig, hash);
	memzero(hash, sizeof(hash));
	return res;
}

// Compute public key from signature and recovery id.
// returns 0 if verification succeeded
int ecdsa_verify_digest_recover(const ecdsa_curve *curve, uint8_t *pub_key, const uint8_t *sig, const uint8_t *digest, int recid)
{
	int result;
	verify_recover_ws_t *ws = (verify_recover_ws_t *)PSRAM_ALLOC(sizeof(verify_recover_ws_t));
	if (!ws) return 1;

	// read r and s
	bn_read_be(sig, &ws->r);
	bn_read_be(sig + 32, &ws->s);
	if (!bn_is_less(&ws->r, &curve->order) || bn_is_zero(&ws->r)) {
		result = 1; goto cleanup;
	}
	if (!bn_is_less(&ws->s, &curve->order) || bn_is_zero(&ws->s)) {
		result = 1; goto cleanup;
	}
	// cp = R = k * G (k is secret nonce when signing)
	memcpy(&ws->cp.x, &ws->r, sizeof(bignum256));
	if (recid & 2) {
		bn_add(&ws->cp.x, &curve->order);
		if (!bn_is_less(&ws->cp.x, &curve->prime)) {
			result = 1; goto cleanup;
		}
	}
	// compute y from x
	uncompress_coords(curve, recid & 1, &ws->cp.x, &ws->cp.y);
	if (!ecdsa_validate_pubkey(curve, &ws->cp)) {
		result = 1; goto cleanup;
	}
	// e = -digest
	bn_read_be(digest, &ws->e);
	bn_subtractmod(&curve->order, &ws->e, &ws->e, &curve->order);
	bn_fast_mod(&ws->e, &curve->order);
	bn_mod(&ws->e, &curve->order);
	// r := r^-1
	bn_inverse(&ws->r, &curve->order);
	// cp := s * R = s * k *G
	point_multiply(curve, &ws->s, &ws->cp, &ws->cp);
	// cp2 := -digest * G
	scalar_multiply(curve, &ws->e, &ws->cp2);
	// cp := (s * k - digest) * G = (r*priv) * G = r * Pub
	point_add(curve, &ws->cp2, &ws->cp);
	// cp := r^{-1} * r * Pub = Pub
	point_multiply(curve, &ws->r, &ws->cp, &ws->cp);
	pub_key[0] = 0x04;
	bn_write_be(&ws->cp.x, pub_key + 1);
	bn_write_be(&ws->cp.y, pub_key + 33);
	result = 0;

cleanup:
	memzero(ws, sizeof(verify_recover_ws_t));
	free(ws);
	return result;
}

// returns 0 if verification succeeded
int ecdsa_verify_digest(const ecdsa_curve *curve, const uint8_t *pub_key, const uint8_t *sig, const uint8_t *digest)
{
	int result;
	verify_digest_ws_t *ws = (verify_digest_ws_t *)PSRAM_ALLOC(sizeof(verify_digest_ws_t));
	if (!ws) return 1;

	if (!ecdsa_read_pubkey(curve, pub_key, &ws->pub)) {
		result = 1; goto cleanup;
	}

	bn_read_be(sig, &ws->r);
	bn_read_be(sig + 32, &ws->s);

	bn_read_be(digest, &ws->z);

	if (bn_is_zero(&ws->r) || bn_is_zero(&ws->s) ||
		(!bn_is_less(&ws->r, &curve->order)) ||
		(!bn_is_less(&ws->s, &curve->order))) {
		result = 2; goto cleanup;
	}

	bn_inverse(&ws->s, &curve->order); // s^-1
	bn_multiply(&ws->s, &ws->z, &curve->order); // z*s^-1
	bn_mod(&ws->z, &curve->order);
	bn_multiply(&ws->r, &ws->s, &curve->order); // r*s^-1
	bn_mod(&ws->s, &curve->order);

	result = 0;
	if (bn_is_zero(&ws->z)) {
		// our message hashes to zero
		// I don't expect this to happen any time soon
		result = 3;
	} else {
		scalar_multiply(curve, &ws->z, &ws->res);
	}

	if (result == 0) {
		// both pub and res can be infinity, can have y = 0 OR can be equal -> false negative
		point_multiply(curve, &ws->s, &ws->pub, &ws->pub);
		point_add(curve, &ws->pub, &ws->res);
		bn_mod(&(ws->res.x), &curve->order);
		// signature does not match
		if (!bn_is_equal(&ws->res.x, &ws->r)) {
			result = 5;
		}
	}

cleanup:
	memzero(ws, sizeof(verify_digest_ws_t));
	free(ws);
	return result;
}

int ecdsa_sig_to_der(const uint8_t *sig, uint8_t *der)
{
	int i;
	uint8_t *p = der, *len, *len1, *len2;
	*p = 0x30; p++;                        // sequence
	*p = 0x00; len = p; p++;               // len(sequence)

	*p = 0x02; p++;                        // integer
	*p = 0x00; len1 = p; p++;              // len(integer)

	// process R
	i = 0;
	while (sig[i] == 0 && i < 32) { i++; } // skip leading zeroes
	if (sig[i] >= 0x80) { // put zero in output if MSB set
		*p = 0x00; p++; *len1 = *len1 + 1;
	}
	while (i < 32) { // copy bytes to output
		*p = sig[i]; p++; *len1 = *len1 + 1; i++;
	}

	*p = 0x02; p++;                        // integer
	*p = 0x00; len2 = p; p++;              // len(integer)

	// process S
	i = 32;
	while (sig[i] == 0 && i < 64) { i++; } // skip leading zeroes
	if (sig[i] >= 0x80) { // put zero in output if MSB set
		*p = 0x00; p++; *len2 = *len2 + 1;
	}
	while (i < 64) { // copy bytes to output
		*p = sig[i]; p++; *len2 = *len2 + 1; i++;
	}

	*len = *len1 + *len2 + 4;
	return *len + 2;
}
