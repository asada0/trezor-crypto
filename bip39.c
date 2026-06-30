/**
 * Copyright (c) 2013-2014 Tomas Dzetkulic
 * Copyright (c) 2013-2014 Pavol Rusnak
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

#include <string.h>
#include <stdbool.h>
#include <stdlib.h>

#ifdef ESP_PLATFORM
#include "esp_heap_caps.h"
#define PSRAM_ALLOC(size) heap_caps_malloc(size, MALLOC_CAP_SPIRAM)
#else
#define PSRAM_ALLOC(size) malloc(size)
#endif

#include "bip39.h"
#include "hmac.h"
#include "rand.h"
#include "sha2.h"
#include "pbkdf2.h"
#include "bip39_english.h"
#include "options.h"
#include "memzero.h"

#if USE_BIP39_CACHE

static int bip39_cache_index = 0;

static CONFIDENTIAL struct {
	bool set;
	char mnemonic[256];
	char passphrase[64];
	uint8_t seed[512 / 8];
} bip39_cache[BIP39_CACHE_SIZE];

#endif

/* Static buffers for mnemonic_from_data / mnemonic_from_data_indexes return
 * values. Moved to file scope (from function-local static) on 2026-05-31 to
 * enable mnemonic_clear() to wipe them — see upstream trezor-firmware
 * components/trezor-firmware/crypto/bip39.c which uses the same pattern. */
static CONFIDENTIAL char mnemo[24 * 10];
static CONFIDENTIAL uint16_t mnemo_idx[24];

const char *mnemonic_generate(int strength)
{
	if (strength % 32 || strength < 128 || strength > 256) {
		return 0;
	}
	uint8_t data[32];
	random_buffer(data, 32);
	const char *r = mnemonic_from_data(data, strength / 8);
	memzero(data, sizeof(data));
	return r;
}

const uint16_t *mnemonic_generate_indexes(int strength)
{
	if (strength % 32 || strength < 128 || strength > 256) {
		return 0;
	}
	uint8_t data[32];
	random_buffer(data, 32);
	const uint16_t *r = mnemonic_from_data_indexes(data, strength / 8);
	memzero(data, sizeof(data));
	return r;
}

const char *mnemonic_from_data(const uint8_t *data, int len)
{
	if (len % 4 || len < 16 || len > 32) {
		return 0;
	}

	uint8_t bits[32 + 1];

	sha256_Raw(data, len, bits);
	// checksum
	bits[len] = bits[0];
	// data
	memcpy(bits, data, len);

	int mlen = len * 3 / 4;
	/* `mnemo` is file-scope static (see top of file). Caller is expected
	 * to call mnemonic_clear() once the returned string is consumed. */

	int i, j, idx;
	char *p = mnemo;
	for (i = 0; i < mlen; i++) {
		idx = 0;
		for (j = 0; j < 11; j++) {
			idx <<= 1;
			idx += (bits[(i * 11 + j) / 8] & (1 << (7 - ((i * 11 + j) % 8)))) > 0;
		}
		strcpy(p, wordlist[idx]);
		p += strlen(wordlist[idx]);
		*p = (i < mlen - 1) ? ' ' : 0;
		p++;
	}
	memzero(bits, sizeof(bits));

	return mnemo;
}

const uint16_t *mnemonic_from_data_indexes(const uint8_t *data, int len)
{
	if (len % 4 || len < 16 || len > 32) {
		return 0;
	}

	uint8_t bits[32 + 1];

	sha256_Raw(data, len, bits);
	// checksum
	bits[len] = bits[0];
	// data
	memcpy(bits, data, len);

	int mlen = len * 3 / 4;
	/* `mnemo_idx` is file-scope static (see top of file). Caller is
	 * expected to call mnemonic_clear() once consumed. */

	int i, j, idx;
	for (i = 0; i < mlen; i++) {
		idx = 0;
		for (j = 0; j < 11; j++) {
			idx <<= 1;
			idx += (bits[(i * 11 + j) / 8] & (1 << (7 - ((i * 11 + j) % 8)))) > 0;
		}
		mnemo_idx[i] = idx;
	}
	memzero(bits, sizeof(bits));

	return mnemo_idx;
}

/* Wipe the static return buffers used by mnemonic_from_data and
 * mnemonic_from_data_indexes. Callers must invoke this once they are done
 * with the returned pointer; otherwise the BIP39 mnemonic (24-word seed
 * phrase, the most sensitive data on the device) remains in .bss until
 * the next call. Matches upstream trezor-firmware's mnemonic_clear(). */
void mnemonic_clear(void)
{
	memzero(mnemo, sizeof(mnemo));
	memzero(mnemo_idx, sizeof(mnemo_idx));
}

int mnemonic_check(const char *mnemonic)
{
	if (!mnemonic) {
		return 0;
	}

	uint32_t i, n;

	i = 0; n = 0;
	while (mnemonic[i]) {
		if (mnemonic[i] == ' ') {
			n++;
		}
		i++;
	}
	n++;
	// check number of words
	if (n != 12 && n != 18 && n != 24) {
		return 0;
	}

	char current_word[10];
	uint32_t j, k, ki, bi;
	uint8_t bits[32 + 1];

	memzero(bits, sizeof(bits));
	i = 0; bi = 0;
	while (mnemonic[i]) {
		j = 0;
		while (mnemonic[i] != ' ' && mnemonic[i] != 0) {
			if (j >= sizeof(current_word) - 1) {
				return 0;
			}
			current_word[j] = mnemonic[i];
			i++; j++;
		}
		current_word[j] = 0;
		if (mnemonic[i] != 0) i++;
		k = 0;
		for (;;) {
			if (!wordlist[k]) { // word not found
				return 0;
			}
			if (strcmp(current_word, wordlist[k]) == 0) { // word found on index k
				for (ki = 0; ki < 11; ki++) {
					if (k & (1 << (10 - ki))) {
						bits[bi / 8] |= 1 << (7 - (bi % 8));
					}
					bi++;
				}
				break;
			}
			k++;
		}
	}
	if (bi != n * 11) {
		return 0;
	}
	bits[32] = bits[n * 4 / 3];
	sha256_Raw(bits, n * 4 / 3, bits);
	if (n == 12) {
		return (bits[0] & 0xF0) == (bits[32] & 0xF0); // compare first 4 bits
	} else
	if (n == 18) {
		return (bits[0] & 0xFC) == (bits[32] & 0xFC); // compare first 6 bits
	} else
	if (n == 24) {
		return bits[0] == bits[32]; // compare 8 bits
	}
	return 0;
}

// Per-call work buffers for mnemonic_to_seed, moved off the (formerly static)
// .bss into a single PSRAM allocation that is memzero'd + freed on every exit.
// pctx holds PBKDF2-HMAC-SHA512 seed-derivation state = SECRET.
typedef struct {
	PBKDF2_HMAC_SHA512_CTX pctx;
} mnemonic_to_seed_ws_t;

// passphrase must be at most 256 characters or code may crash
void mnemonic_to_seed(const char *mnemonic, const char *passphrase, uint8_t seed[512 / 8], void (*progress_callback)(uint32_t current, uint32_t total))
{
	int passphraselen = strlen(passphrase);
#if USE_BIP39_CACHE
	int mnemoniclen = strlen(mnemonic);
	// check cache
	if (mnemoniclen < 256 && passphraselen < 64) {
		for (int i = 0; i < BIP39_CACHE_SIZE; i++) {
			if (!bip39_cache[i].set) continue;
			if (strcmp(bip39_cache[i].mnemonic, mnemonic) != 0) continue;
			if (strcmp(bip39_cache[i].passphrase, passphrase) != 0) continue;
			// found the correct entry
			memcpy(seed, bip39_cache[i].seed, 512 / 8);
			return;
		}
	}
#endif
	uint8_t salt[8 + 256];
	memcpy(salt, "mnemonic", 8);
	memcpy(salt + 8, passphrase, passphraselen);
	mnemonic_to_seed_ws_t *ws = (mnemonic_to_seed_ws_t *)PSRAM_ALLOC(sizeof(mnemonic_to_seed_ws_t));
	if (!ws) {
		memzero(salt, sizeof(salt));
		memzero(seed, 512 / 8);
		return;
	}
	pbkdf2_hmac_sha512_Init(&ws->pctx, (const uint8_t *)mnemonic, strlen(mnemonic), salt, passphraselen + 8);
	if (progress_callback) {
		progress_callback(0, BIP39_PBKDF2_ROUNDS);
	}
	for (int i = 0; i < 16; i++) {
		pbkdf2_hmac_sha512_Update(&ws->pctx, BIP39_PBKDF2_ROUNDS / 16);
		if (progress_callback) {
			progress_callback((i + 1) * BIP39_PBKDF2_ROUNDS / 16, BIP39_PBKDF2_ROUNDS);
		}
	}
	pbkdf2_hmac_sha512_Final(&ws->pctx, seed);
	memzero(salt, sizeof(salt));
#if USE_BIP39_CACHE
	// store to cache
	if (mnemoniclen < 256 && passphraselen < 64) {
		bip39_cache[bip39_cache_index].set = true;
		strcpy(bip39_cache[bip39_cache_index].mnemonic, mnemonic);
		strcpy(bip39_cache[bip39_cache_index].passphrase, passphrase);
		memcpy(bip39_cache[bip39_cache_index].seed, seed, 512 / 8);
		bip39_cache_index = (bip39_cache_index + 1) % BIP39_CACHE_SIZE;
	}
#endif
	memzero(ws, sizeof(*ws));
	free(ws);
}

const char * const *mnemonic_wordlist(void)
{
	return wordlist;
}
