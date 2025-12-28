set(SOURCES
    bignum.c
    ecdsa.c
    curves.c
    secp256k1.c
    nist256p1.c
    rand.c
    hmac.c
    bip32.c
    bip39.c
    pbkdf2.c
    base58.c
    base32.c
    cryptoaddress.c
    script.c
    ripemd160.c
    segwit_addr.c
    sha2.c
    sha3.c
    hasher.c
    aes/aescrypt.c
    aes/aeskey.c
    aes/aestab.c
    aes/aes_modes.c
    curve25519-donna-32bit.c
    curve25519-donna-helpers.c
    modm-donna-32bit.c
    ed25519-donna-basepoint-table.c
    ed25519-donna-32bit-tables.c
    ed25519-donna-impl-base.c
    ed25519.c
    curve25519-donna-scalarmult-base.c
    ed25519-sha3.c
    ed25519-keccak.c
    blake256.c
    blake2b.c
    blake2s.c
    chacha20poly1305.c
    chacha_merged.c
    poly1305-donna.c
    rfc7539.c
    rc4.c
    nem.c
    memzero.c
)

idf_component_register(
    SRCS ${SOURCES}
    INCLUDE_DIRS "." "aes"
    REQUIRES esp_common
)

target_compile_options(${COMPONENT_LIB} PRIVATE
    "-std=c99"
    "-Wno-stringop-overread"
    "-Wno-array-parameter"
)

# AES key size definitions (required for aes_encrypt_key function)
target_compile_definitions(${COMPONENT_LIB} PUBLIC
    AES_128
    AES_192
    AES_VAR
)
