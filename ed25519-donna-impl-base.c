#include "ed25519-donna.h"
#include "memzero.h"

#ifdef ESP_PLATFORM
#include "esp_attr.h"
#include "esp_heap_caps.h"
#define PSRAM_STATIC static EXT_RAM_BSS_ATTR
#define PSRAM_ALLOC(size) heap_caps_malloc(size, MALLOC_CAP_SPIRAM)
#else
#define PSRAM_STATIC static
#define PSRAM_ALLOC(size) malloc(size)
#endif

/*
	Timing safe memory compare
*/
int ed25519_verify(const unsigned char *x, const unsigned char *y, size_t len) {
	size_t differentbits = 0;
	while (len--)
		differentbits |= (*x++ ^ *y++);
	return (int) (1 & ((differentbits - 1) >> 8));
}

/*
	conversions
*/

void ge25519_p1p1_to_partial(ge25519 *r, const ge25519_p1p1 *p) {
	curve25519_mul(r->x, p->x, p->t);
	curve25519_mul(r->y, p->y, p->z);
	curve25519_mul(r->z, p->z, p->t);
}

void ge25519_p1p1_to_full(ge25519 *r, const ge25519_p1p1 *p) {
	curve25519_mul(r->x, p->x, p->t);
	curve25519_mul(r->y, p->y, p->z);
	curve25519_mul(r->z, p->z, p->t);
	curve25519_mul(r->t, p->x, p->y);
}

void ge25519_full_to_pniels(ge25519_pniels *p, const ge25519 *r) {
	curve25519_sub(p->ysubx, r->y, r->x);
	curve25519_add(p->xaddy, r->y, r->x);
	curve25519_copy(p->z, r->z);
	curve25519_mul(p->t2d, r->t, ge25519_ec2d);
}

/*
	adding & doubling
*/

typedef struct { bignum25519 a,b,c; } ge25519_double_p1p1_ws_t;

void ge25519_double_p1p1(ge25519_p1p1 *r, const ge25519 *p) {
	ge25519_double_p1p1_ws_t *ws = (ge25519_double_p1p1_ws_t *)PSRAM_ALLOC(sizeof(ge25519_double_p1p1_ws_t));
	if (!ws) return;

	curve25519_square(ws->a, p->x);
	curve25519_square(ws->b, p->y);
	curve25519_square(ws->c, p->z);
	curve25519_add_reduce(ws->c, ws->c, ws->c);
	curve25519_add(r->x, p->x, p->y);
	curve25519_square(r->x, r->x);
	curve25519_add(r->y, ws->b, ws->a);
	curve25519_sub(r->z, ws->b, ws->a);
	curve25519_sub_after_basic(r->x, r->x, r->y);
	curve25519_sub_after_basic(r->t, ws->c, r->z);

	memzero(ws, sizeof(*ws));
	free(ws);
}

#ifndef ED25519_NO_PRECOMP
typedef struct { bignum25519 a,b,c; } ge25519_nielsadd2_p1p1_ws_t;

void ge25519_nielsadd2_p1p1(ge25519_p1p1 *r, const ge25519 *p, const ge25519_niels *q, unsigned char signbit) {
	const bignum25519 *qb = (const bignum25519 *)q;
	bignum25519 *rb = (bignum25519 *)r;
	ge25519_nielsadd2_p1p1_ws_t *ws = (ge25519_nielsadd2_p1p1_ws_t *)PSRAM_ALLOC(sizeof(ge25519_nielsadd2_p1p1_ws_t));
	if (!ws) return;

	curve25519_sub(ws->a, p->y, p->x);
	curve25519_add(ws->b, p->y, p->x);
	curve25519_mul(ws->a, ws->a, qb[signbit]); /* x for +, y for - */
	curve25519_mul(r->x, ws->b, qb[signbit^1]); /* y for +, x for - */
	curve25519_add(r->y, r->x, ws->a);
	curve25519_sub(r->x, r->x, ws->a);
	curve25519_mul(ws->c, p->t, q->t2d);
	curve25519_add_reduce(r->t, p->z, p->z);
	curve25519_copy(r->z, r->t);
	curve25519_add(rb[2+signbit], rb[2+signbit], ws->c); /* z for +, t for - */
	curve25519_sub(rb[2+(signbit^1)], rb[2+(signbit^1)], ws->c); /* t for +, z for - */

	memzero(ws, sizeof(*ws));
	free(ws);
}
#endif

typedef struct { bignum25519 a,b,c; } ge25519_pnielsadd_p1p1_ws_t;

void ge25519_pnielsadd_p1p1(ge25519_p1p1 *r, const ge25519 *p, const ge25519_pniels *q, unsigned char signbit) {
	const bignum25519 *qb = (const bignum25519 *)q;
	bignum25519 *rb = (bignum25519 *)r;
	ge25519_pnielsadd_p1p1_ws_t *ws = (ge25519_pnielsadd_p1p1_ws_t *)PSRAM_ALLOC(sizeof(ge25519_pnielsadd_p1p1_ws_t));
	if (!ws) return;

	curve25519_sub(ws->a, p->y, p->x);
	curve25519_add(ws->b, p->y, p->x);
	curve25519_mul(ws->a, ws->a, qb[signbit]); /* ysubx for +, xaddy for - */
	curve25519_mul(r->x, ws->b, qb[signbit^1]); /* xaddy for +, ysubx for - */
	curve25519_add(r->y, r->x, ws->a);
	curve25519_sub(r->x, r->x, ws->a);
	curve25519_mul(ws->c, p->t, q->t2d);
	curve25519_mul(r->t, p->z, q->z);
	curve25519_add_reduce(r->t, r->t, r->t);
	curve25519_copy(r->z, r->t);
	curve25519_add(rb[2+signbit], rb[2+signbit], ws->c); /* z for +, t for - */
	curve25519_sub(rb[2+(signbit^1)], rb[2+(signbit^1)], ws->c); /* t for +, z for - */

	memzero(ws, sizeof(*ws));
	free(ws);
}

void ge25519_double_partial(ge25519 *r, const ge25519 *p) {
	ge25519_p1p1 *t = (ge25519_p1p1 *)PSRAM_ALLOC(sizeof(ge25519_p1p1));
	if (!t) return;
	ge25519_double_p1p1(t, p);
	ge25519_p1p1_to_partial(r, t);
	memzero(t, sizeof(*t));
	free(t);
}

void ge25519_double(ge25519 *r, const ge25519 *p) {
	ge25519_p1p1 *t = (ge25519_p1p1 *)PSRAM_ALLOC(sizeof(ge25519_p1p1));
	if (!t) return;
	ge25519_double_p1p1(t, p);
	ge25519_p1p1_to_full(r, t);
	memzero(t, sizeof(*t));
	free(t);
}

typedef struct { bignum25519 a,b,c,e,f,g,h; } ge25519_nielsadd2_ws_t;

void ge25519_nielsadd2(ge25519 *r, const ge25519_niels *q) {
	ge25519_nielsadd2_ws_t *ws = (ge25519_nielsadd2_ws_t *)PSRAM_ALLOC(sizeof(ge25519_nielsadd2_ws_t));
	if (!ws) return;

	curve25519_sub(ws->a, r->y, r->x);
	curve25519_add(ws->b, r->y, r->x);
	curve25519_mul(ws->a, ws->a, q->ysubx);
	curve25519_mul(ws->e, ws->b, q->xaddy);
	curve25519_add(ws->h, ws->e, ws->a);
	curve25519_sub(ws->e, ws->e, ws->a);
	curve25519_mul(ws->c, r->t, q->t2d);
	curve25519_add(ws->f, r->z, r->z);
	curve25519_add_after_basic(ws->g, ws->f, ws->c);
	curve25519_sub_after_basic(ws->f, ws->f, ws->c);
	curve25519_mul(r->x, ws->e, ws->f);
	curve25519_mul(r->y, ws->h, ws->g);
	curve25519_mul(r->z, ws->g, ws->f);
	curve25519_mul(r->t, ws->e, ws->h);

	memzero(ws, sizeof(*ws));
	free(ws);
}

typedef struct { bignum25519 a,b,c,x,y,z,t; } ge25519_pnielsadd_ws_t;

void ge25519_pnielsadd(ge25519_pniels *r, const ge25519 *p, const ge25519_pniels *q) {
	ge25519_pnielsadd_ws_t *ws = (ge25519_pnielsadd_ws_t *)PSRAM_ALLOC(sizeof(ge25519_pnielsadd_ws_t));
	if (!ws) return;

	curve25519_sub(ws->a, p->y, p->x);
	curve25519_add(ws->b, p->y, p->x);
	curve25519_mul(ws->a, ws->a, q->ysubx);
	curve25519_mul(ws->x, ws->b, q->xaddy);
	curve25519_add(ws->y, ws->x, ws->a);
	curve25519_sub(ws->x, ws->x, ws->a);
	curve25519_mul(ws->c, p->t, q->t2d);
	curve25519_mul(ws->t, p->z, q->z);
	curve25519_add(ws->t, ws->t, ws->t);
	curve25519_add_after_basic(ws->z, ws->t, ws->c);
	curve25519_sub_after_basic(ws->t, ws->t, ws->c);
	curve25519_mul(r->xaddy, ws->x, ws->t);
	curve25519_mul(r->ysubx, ws->y, ws->z);
	curve25519_mul(r->z, ws->z, ws->t);
	curve25519_mul(r->t2d, ws->x, ws->y);
	curve25519_copy(ws->y, r->ysubx);
	curve25519_sub(r->ysubx, r->ysubx, r->xaddy);
	curve25519_add(r->xaddy, r->xaddy, ws->y);
	curve25519_mul(r->t2d, r->t2d, ge25519_ec2d);

	memzero(ws, sizeof(*ws));
	free(ws);
}


/*
	pack & unpack
*/

typedef struct { bignum25519 tx, ty, zi; unsigned char parity[32]; } ge25519_pack_ws_t;

void ge25519_pack(unsigned char r[32], const ge25519 *p) {
	ge25519_pack_ws_t *ws = (ge25519_pack_ws_t *)PSRAM_ALLOC(sizeof(ge25519_pack_ws_t));
	if (!ws) return;
	curve25519_recip(ws->zi, p->z);
	curve25519_mul(ws->tx, p->x, ws->zi);
	curve25519_mul(ws->ty, p->y, ws->zi);
	curve25519_contract(r, ws->ty);
	curve25519_contract(ws->parity, ws->tx);
	r[31] ^= ((ws->parity[0] & 1) << 7);

	memzero(ws, sizeof(*ws));
	free(ws);
}

typedef struct { unsigned char check[32]; bignum25519 t, root, num, den, d3; } ge25519_unpack_negative_vartime_ws_t;

int ge25519_unpack_negative_vartime(ge25519 *r, const unsigned char p[32]) {
	const unsigned char zero[32] = {0};
	const bignum25519 one = {1};
	unsigned char parity = p[31] >> 7;
	int result = 1;
	ge25519_unpack_negative_vartime_ws_t *ws = (ge25519_unpack_negative_vartime_ws_t *)PSRAM_ALLOC(sizeof(ge25519_unpack_negative_vartime_ws_t));
	if (!ws) return 0;

	curve25519_expand(r->y, p);
	curve25519_copy(r->z, one);
	curve25519_square(ws->num, r->y); /* x = y^2 */
	curve25519_mul(ws->den, ws->num, ge25519_ecd); /* den = dy^2 */
	curve25519_sub_reduce(ws->num, ws->num, r->z); /* x = y^1 - 1 */
	curve25519_add(ws->den, ws->den, r->z); /* den = dy^2 + 1 */

	/* Computation of sqrt(num/den) */
	/* 1.: computation of num^((p-5)/8)*den^((7p-35)/8) = (num*den^7)^((p-5)/8) */
	curve25519_square(ws->t, ws->den);
	curve25519_mul(ws->d3, ws->t, ws->den);
	curve25519_square(r->x, ws->d3);
	curve25519_mul(r->x, r->x, ws->den);
	curve25519_mul(r->x, r->x, ws->num);
	curve25519_pow_two252m3(r->x, r->x);

	/* 2. computation of r->x = num * den^3 * (num*den^7)^((p-5)/8) */
	curve25519_mul(r->x, r->x, ws->d3);
	curve25519_mul(r->x, r->x, ws->num);

	/* 3. Check if either of the roots works: */
	curve25519_square(ws->t, r->x);
	curve25519_mul(ws->t, ws->t, ws->den);
	curve25519_sub_reduce(ws->root, ws->t, ws->num);
	curve25519_contract(ws->check, ws->root);
	if (!ed25519_verify(ws->check, zero, 32)) {
		curve25519_add_reduce(ws->t, ws->t, ws->num);
		curve25519_contract(ws->check, ws->t);
		if (!ed25519_verify(ws->check, zero, 32)) {
			result = 0;
			goto cleanup;
		}
		curve25519_mul(r->x, r->x, ge25519_sqrtneg1);
	}

	curve25519_contract(ws->check, r->x);
	if ((ws->check[0] & 1) == parity) {
		curve25519_copy(ws->t, r->x);
		curve25519_neg(r->x, ws->t);
	}
	curve25519_mul(r->t, r->x, r->y);
	result = 1;

cleanup:
	memzero(ws, sizeof(*ws));
	free(ws);
	return result;
}

/*
	scalarmults
*/

void ge25519_set_neutral(ge25519 *r)
{
	memset(r, 0, sizeof(ge25519));
	r->y[0] = 1;
	r->z[0] = 1;
}

#define S1_SWINDOWSIZE 5
#define S1_TABLE_SIZE (1<<(S1_SWINDOWSIZE-2))
#ifdef ED25519_NO_PRECOMP
#define S2_SWINDOWSIZE 5
#else
#define S2_SWINDOWSIZE 7
#endif
#define S2_TABLE_SIZE (1<<(S2_SWINDOWSIZE-2))

typedef struct {
	signed char slide1[256], slide2[256];
	ge25519_pniels pre1[S1_TABLE_SIZE];
#ifdef ED25519_NO_PRECOMP
	ge25519_pniels pre2[S2_TABLE_SIZE];
#endif
	ge25519 dp;
	ge25519_p1p1 t;
} ge25519_double_scalarmult_vartime_ws_t;

/* computes [s1]p1 + [s2]base */
void ge25519_double_scalarmult_vartime(ge25519 *r, const ge25519 *p1, const bignum256modm s1, const bignum256modm s2) {
	ge25519_double_scalarmult_vartime_ws_t *ws = (ge25519_double_scalarmult_vartime_ws_t *)PSRAM_ALLOC(sizeof(ge25519_double_scalarmult_vartime_ws_t));
	if (!ws) return;
	int32_t i;

	contract256_slidingwindow_modm(ws->slide1, s1, S1_SWINDOWSIZE);
	contract256_slidingwindow_modm(ws->slide2, s2, S2_SWINDOWSIZE);

	ge25519_double(&ws->dp, p1);
	ge25519_full_to_pniels(ws->pre1, p1);
	for (i = 0; i < S1_TABLE_SIZE - 1; i++)
		ge25519_pnielsadd(&ws->pre1[i+1], &ws->dp, &ws->pre1[i]);

#ifdef ED25519_NO_PRECOMP
	ge25519_double(&ws->dp, &ge25519_basepoint);
	ge25519_full_to_pniels(ws->pre2, &ge25519_basepoint);
	for (i = 0; i < S2_TABLE_SIZE - 1; i++)
		ge25519_pnielsadd(&ws->pre2[i+1], &ws->dp, &ws->pre2[i]);
#endif

	ge25519_set_neutral(r);

	i = 255;
	while ((i >= 0) && !(ws->slide1[i] | ws->slide2[i]))
		i--;

	for (; i >= 0; i--) {
		ge25519_double_p1p1(&ws->t, r);

		if (ws->slide1[i]) {
			ge25519_p1p1_to_full(r, &ws->t);
			ge25519_pnielsadd_p1p1(&ws->t, r, &ws->pre1[abs(ws->slide1[i]) / 2], (unsigned char)ws->slide1[i] >> 7);
		}

		if (ws->slide2[i]) {
			ge25519_p1p1_to_full(r, &ws->t);
#ifdef ED25519_NO_PRECOMP
			ge25519_pnielsadd_p1p1(&ws->t, r, &ws->pre2[abs(ws->slide2[i]) / 2], (unsigned char)ws->slide2[i] >> 7);
#else
			ge25519_nielsadd2_p1p1(&ws->t, r, &ge25519_niels_sliding_multiples[abs(ws->slide2[i]) / 2], (unsigned char)ws->slide2[i] >> 7);
#endif
		}

		ge25519_p1p1_to_partial(r, &ws->t);
	}

	memzero(ws, sizeof(*ws));
	free(ws);
}

/*
 * The following conditional move stuff uses conditional moves.
 * I will check on which compilers this works, and provide suitable
 * workarounds for those where it doesn't.
 *
 * This works on gcc 4.x and above with -O3.  Don't use -O2, this will
 * cause the code to not generate conditional moves.  Don't use any -march=
 * with less than i686 on x86
 */
static void ge25519_cmove_stride4(long * r, long * p, long * pos, long * n, int stride) {
  long x0=r[0], x1=r[1], x2=r[2], x3=r[3], y0, y1, y2, y3;
  for(; p<n; p+=stride) {
    int flag=(p==pos);
    y0 = p[0];
    y1 = p[1];
    y2 = p[2];
    y3 = p[3];
    x0 = flag ? y0 : x0;
    x1 = flag ? y1 : x1;
    x2 = flag ? y2 : x2;
    x3 = flag ? y3 : x3;
  }
  r[0] = x0;
  r[1] = x1;
  r[2] = x2;
  r[3] = x3;
}
#define HAS_CMOVE_STRIDE4

static void ge25519_cmove_stride4b(long * r, long * p, long * pos, long * n, int stride) {
  long x0=p[0], x1=p[1], x2=p[2], x3=p[3], y0, y1, y2, y3;
  for(p+=stride; p<n; p+=stride) {
    int flag=(p==pos);
    y0 = p[0];
    y1 = p[1];
    y2 = p[2];
    y3 = p[3];
    x0 = flag ? y0 : x0;
    x1 = flag ? y1 : x1;
    x2 = flag ? y2 : x2;
    x3 = flag ? y3 : x3;
  }
  r[0] = x0;
  r[1] = x1;
  r[2] = x2;
  r[3] = x3;
}
#define HAS_CMOVE_STRIDE4B

void ge25519_move_conditional_pniels_array(ge25519_pniels * r, const ge25519_pniels * p, int pos, int n) {
#ifdef HAS_CMOVE_STRIDE4B
  size_t i;
  for(i=0; i<sizeof(ge25519_pniels)/sizeof(long); i+=4) {
    ge25519_cmove_stride4b(((long*)r)+i,
			   ((long*)p)+i,
			   ((long*)(p+pos))+i,
			   ((long*)(p+n))+i,
			   sizeof(ge25519_pniels)/sizeof(long));
  }
#else
  size_t i;
  for(i=0; i<n; i++) {
    ge25519_move_conditional_pniels(r, p+i, pos==i);
  }
#endif
}

void ge25519_move_conditional_niels_array(ge25519_niels * r, const uint8_t p[8][96], int pos, int n) {
  size_t i;
  for(i=0; i<96/sizeof(long); i+=4) {
    ge25519_cmove_stride4(((long*)r)+i,
			  ((long*)p)+i,
			  ((long*)(p+pos))+i,
			  ((long*)(p+n))+i,
			  96/sizeof(long));
  }
}

typedef struct {
	ge25519_pniels pre1[9];
	ge25519_pniels pre;
	ge25519 d1;
	ge25519_p1p1 t;
} ge25519_scalarmult_ws_t;

/* computes [s1]p1, constant time */
void ge25519_scalarmult(ge25519 *r, const ge25519 *p1, const bignum256modm s1) {
	signed char slide1[64];
	ge25519_scalarmult_ws_t *ws = (ge25519_scalarmult_ws_t *)PSRAM_ALLOC(sizeof(ge25519_scalarmult_ws_t));
	if (!ws) return;
	int32_t i;

	contract256_window4_modm(slide1, s1);

	/* set neutral */
	ge25519_set_neutral(r);

	ge25519_full_to_pniels(ws->pre1, r);
	ge25519_full_to_pniels(ws->pre1+1, p1);
	ge25519_double(&ws->d1, p1);
	ge25519_full_to_pniels(ws->pre1+2, &ws->d1);
	for (i = 1; i < 7; i++) {
		ge25519_pnielsadd(&ws->pre1[i+2], &ws->d1, &ws->pre1[i]);
	}

	for (i = 63; i >= 0; i--) {
		int k=abs(slide1[i]);
		ge25519_double_partial(r, r);
		ge25519_double_partial(r, r);
		ge25519_double_partial(r, r);
		ge25519_double_p1p1(&ws->t, r);
		ge25519_move_conditional_pniels_array(&ws->pre, ws->pre1, k, 9);
		ge25519_p1p1_to_full(r, &ws->t);
		ge25519_pnielsadd_p1p1(&ws->t, r, &ws->pre, (unsigned char)slide1[i] >> 7);
		ge25519_p1p1_to_partial(r, &ws->t);
	}

	memzero(slide1, sizeof(slide1));
	memzero(ws, sizeof(*ws));
	free(ws);
}

void ge25519_scalarmult_base_choose_niels(ge25519_niels *t, const uint8_t table[256][96], uint32_t pos, signed char b) {
	bignum25519 neg;
	uint32_t sign = (uint32_t)((unsigned char)b >> 7);
	uint32_t mask = ~(sign - 1);
	uint32_t u = (b + mask) ^ mask;

	/* ysubx, xaddy, t2d in packed form. initialize to ysubx = 1, xaddy = 1, t2d = 0 */
	uint8_t *packed = (uint8_t *)PSRAM_ALLOC(96);
	if (!packed) return;
	memset(packed, 0, 96);
	packed[0] = 1;
	packed[32] = 1;

	ge25519_move_conditional_niels_array((ge25519_niels *)packed, &table[pos*8], u-1, 8);

	/* expand in to t */
	curve25519_expand(t->ysubx, packed +  0);
	curve25519_expand(t->xaddy, packed + 32);
	curve25519_expand(t->t2d  , packed + 64);

	/* adjust for sign */
	curve25519_swap_conditional(t->ysubx, t->xaddy, sign);
	curve25519_neg(neg, t->t2d);
	curve25519_swap_conditional(t->t2d, neg, sign);

	memzero(packed, 96);
	free(packed);
}

/* computes [s]basepoint */
void ge25519_scalarmult_base_niels(ge25519 *r, const uint8_t basepoint_table[256][96], const bignum256modm s) {
	signed char b[64];
	uint32_t i;
	ge25519_niels *t = (ge25519_niels *)PSRAM_ALLOC(sizeof(ge25519_niels));
	if (!t) return;

	contract256_window4_modm(b, s);

	ge25519_scalarmult_base_choose_niels(t, basepoint_table, 0, b[1]);
	curve25519_sub_reduce(r->x, t->xaddy, t->ysubx);
	curve25519_add_reduce(r->y, t->xaddy, t->ysubx);
	memset(r->z, 0, sizeof(bignum25519));
	curve25519_copy(r->t, t->t2d);
	r->z[0] = 2;
	for (i = 3; i < 64; i += 2) {
		ge25519_scalarmult_base_choose_niels(t, basepoint_table, i / 2, b[i]);
		ge25519_nielsadd2(r, t);
	}
	ge25519_double_partial(r, r);
	ge25519_double_partial(r, r);
	ge25519_double_partial(r, r);
	ge25519_double(r, r);
	ge25519_scalarmult_base_choose_niels(t, basepoint_table, 0, b[0]);
	curve25519_mul(t->t2d, t->t2d, ge25519_ecd);
	ge25519_nielsadd2(r, t);
	for(i = 2; i < 64; i += 2) {
		ge25519_scalarmult_base_choose_niels(t, basepoint_table, i / 2, b[i]);
		ge25519_nielsadd2(r, t);
	}

	memzero(b, sizeof(b));
	memzero(t, sizeof(*t));
	free(t);
}
