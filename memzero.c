/*
 * memzero.c — secure memory clearing (volatile implementation)
 *
 * Phase 2.5: Upgraded from `memset` wrapper to volatile byte-loop to resist
 * dead-store elimination by the optimizer. Affects all 1700+ project-wide
 * `memzero(...)` call sites in one shot.
 *
 * Pattern adapted from trezor-firmware/crypto/memzero.c (libsodium-style).
 * On ESP-IDF (newlib) none of the HAVE_* macros are defined, so we always
 * fall through to the portable volatile loop.
 *
 * Performance note: this is ~4-8x slower than libc memset for word-aligned
 * buffers, but the cost is negligible for the small secret buffers used
 * here (32-byte keys, 64-byte seeds). Large-buffer callers should prefer
 * `memset` directly if the buffer does not contain secrets.
 */

#include "memzero.h"

void memzero(void *const pnt, const size_t len)
{
    volatile unsigned char *volatile pnt_ =
        (volatile unsigned char *volatile)pnt;
    size_t i = (size_t)0U;

    while (i < len) {
        pnt_[i++] = 0U;
    }
}
