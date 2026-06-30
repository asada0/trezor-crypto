#include "ed25519-donna.h"
#include "ed25519.h"
#include "memzero.h"

#ifdef ESP_PLATFORM
#include "esp_attr.h"
#include "esp_heap_caps.h"
#define PSRAM_ALLOC(size) heap_caps_malloc(size, MALLOC_CAP_SPIRAM)
#else
#define PSRAM_ALLOC(size) malloc(size)
#endif

typedef struct {
	bignum25519 nqpqx, nqpqz, nqz, nqx;
	bignum25519 q, qx, qpqx, qqx, zzz, zmone;
} curve25519_scalarmult_donna_ws_t;

/* Calculates nQ where Q is the x-coordinate of a point on the curve
 *
 *   mypublic: the packed little endian x coordinate of the resulting curve point
 *   n: a little endian, 32-byte number
 *   basepoint: a packed little endian point of the curve
 */

void curve25519_scalarmult_donna(curve25519_key mypublic, const curve25519_key n, const curve25519_key basepoint) {
	curve25519_scalarmult_donna_ws_t *ws = (curve25519_scalarmult_donna_ws_t *)PSRAM_ALLOC(sizeof(curve25519_scalarmult_donna_ws_t));
	if (!ws) return;
	size_t bit, lastbit;
	int32_t i;

	memset(ws->nqpqx, 0, sizeof(bignum25519)); ws->nqpqx[0] = 1;
	memset(ws->nqpqz, 0, sizeof(bignum25519));
	memset(ws->nqz, 0, sizeof(bignum25519)); ws->nqz[0] = 1;
	curve25519_expand(ws->q, basepoint);
	curve25519_copy(ws->nqx, ws->q);

	/* bit 255 is always 0, and bit 254 is always 1, so skip bit 255 and
	   start pre-swapped on bit 254 */
	lastbit = 1;

	/* we are doing bits 254..3 in the loop, but are swapping in bits 253..2 */
	for (i = 253; i >= 2; i--) {
		curve25519_add(ws->qx, ws->nqx, ws->nqz);
		curve25519_sub(ws->nqz, ws->nqx, ws->nqz);
		curve25519_add(ws->qpqx, ws->nqpqx, ws->nqpqz);
		curve25519_sub(ws->nqpqz, ws->nqpqx, ws->nqpqz);
		curve25519_mul(ws->nqpqx, ws->qpqx, ws->nqz);
		curve25519_mul(ws->nqpqz, ws->qx, ws->nqpqz);
		curve25519_add(ws->qqx, ws->nqpqx, ws->nqpqz);
		curve25519_sub(ws->nqpqz, ws->nqpqx, ws->nqpqz);
		curve25519_square(ws->nqpqz, ws->nqpqz);
		curve25519_square(ws->nqpqx, ws->qqx);
		curve25519_mul(ws->nqpqz, ws->nqpqz, ws->q);
		curve25519_square(ws->qx, ws->qx);
		curve25519_square(ws->nqz, ws->nqz);
		curve25519_mul(ws->nqx, ws->qx, ws->nqz);
		curve25519_sub(ws->nqz, ws->qx, ws->nqz);
		curve25519_scalar_product(ws->zzz, ws->nqz, 121665);
		curve25519_add(ws->zzz, ws->zzz, ws->qx);
		curve25519_mul(ws->nqz, ws->nqz, ws->zzz);

		bit = (n[i/8] >> (i & 7)) & 1;
		curve25519_swap_conditional(ws->nqx, ws->nqpqx, bit ^ lastbit);
		curve25519_swap_conditional(ws->nqz, ws->nqpqz, bit ^ lastbit);
		lastbit = bit;
	}

	/* the final 3 bits are always zero, so we only need to double */
	for (i = 0; i < 3; i++) {
		curve25519_add(ws->qx, ws->nqx, ws->nqz);
		curve25519_sub(ws->nqz, ws->nqx, ws->nqz);
		curve25519_square(ws->qx, ws->qx);
		curve25519_square(ws->nqz, ws->nqz);
		curve25519_mul(ws->nqx, ws->qx, ws->nqz);
		curve25519_sub(ws->nqz, ws->qx, ws->nqz);
		curve25519_scalar_product(ws->zzz, ws->nqz, 121665);
		curve25519_add(ws->zzz, ws->zzz, ws->qx);
		curve25519_mul(ws->nqz, ws->nqz, ws->zzz);
	}

	curve25519_recip(ws->zmone, ws->nqz);
	curve25519_mul(ws->nqz, ws->nqx, ws->zmone);
	curve25519_contract(mypublic, ws->nqz);

	memzero(ws, sizeof(curve25519_scalarmult_donna_ws_t));
	free(ws);
}
