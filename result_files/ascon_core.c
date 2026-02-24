
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;

/* ── Round constants for p^12 (Table 3 of [1]) ─────────────────────────── */
static const u64 RC[12] = {
    0x00000000000000f0ULL, /* round  0 */
    0x00000000000000e1ULL, /* round  1 */
    0x00000000000000d2ULL, /* round  2 */
    0x00000000000000c3ULL, /* round  3 */
    0x00000000000000b4ULL, /* round  4 */
    0x00000000000000a5ULL, /* round  5 */
    0x0000000000000096ULL, /* round  6 */
    0x0000000000000087ULL, /* round  7 */
    0x0000000000000078ULL, /* round  8 */
    0x0000000000000069ULL, /* round  9 */
    0x000000000000005aULL, /* round 10 */
    0x000000000000004bULL  /* round 11 */
};

/* ── Bit-rotation helper ────────────────────────────────────────────────── */
static inline u64 ror64(u64 x, int n)
{
    return (x >> n) | (x << (64 - n));
}

/* ── Ascon permutation p^rounds ─────────────────────────────────────────── *
 * Implements pC ◦ pS ◦ pL per Section 3 of [1].
 * For Ascon-MAC, this is ALWAYS called with rounds=12.                      */
static void ascon_permutation(u64 s[5], int rounds)
{
    int start = 12 - rounds;

    for (int i = start; i < 12; i++) {

        /* pC: add round constant to word x2 */
        s[2] ^= RC[i];

        /* pS: bit-sliced 5-bit S-box (Figure 4a of [1]) */
        s[0] ^= s[4];   s[4] ^= s[3];   s[2] ^= s[1];
        u64 t0 = ~s[0] & s[1];
        u64 t1 = ~s[1] & s[2];
        u64 t2 = ~s[2] & s[3];
        u64 t3 = ~s[3] & s[4];
        u64 t4 = ~s[4] & s[0];
        s[0] ^= t1;  s[1] ^= t2;  s[2] ^= t3;  s[3] ^= t4;  s[4] ^= t0;
        s[1] ^= s[0];  s[0] ^= s[4];  s[3] ^= s[2];  s[2] = ~s[2];

        /* pL: linear diffusion layer — Σᵢ functions (Figure 4b of [1]) */
        s[0] ^= ror64(s[0], 19) ^ ror64(s[0], 28);
        s[1] ^= ror64(s[1], 61) ^ ror64(s[1], 39);
        s[2] ^= ror64(s[2],  1) ^ ror64(s[2],  6);
        s[3] ^= ror64(s[3], 10) ^ ror64(s[3], 17);
        s[4] ^= ror64(s[4],  7) ^ ror64(s[4], 41);
    }
}

/* ── Big-endian 64-bit load/store (§2.1 of [1]: MSB first) ─────────────── */
static inline u64 load64_be(const uint8_t *p)
{
    return ((u64)p[0] << 56) | ((u64)p[1] << 48)
         | ((u64)p[2] << 40) | ((u64)p[3] << 32)
         | ((u64)p[4] << 24) | ((u64)p[5] << 16)
         | ((u64)p[6] <<  8) |  (u64)p[7];
}

static inline void store64_be(uint8_t *p, u64 x)
{
    p[0] = (uint8_t)(x >> 56);  p[1] = (uint8_t)(x >> 48);
    p[2] = (uint8_t)(x >> 40);  p[3] = (uint8_t)(x >> 32);
    p[4] = (uint8_t)(x >> 24);  p[5] = (uint8_t)(x >> 16);
    p[6] = (uint8_t)(x >>  8);  p[7] = (uint8_t)(x);
}

/* ── Ascon-MAC ─────────────────────────────────────────────────────────── *
 * Implements Algorithms 1+2 of [1] with parameters:
 *   k=128, ri=256, ro=128, t=128, a=12
 *
 * key  : 16-byte (128-bit) secret key
 * msg  : input message, arbitrary length
 * len  : byte-length of msg
 * tag  : output — exactly 16 bytes (128-bit tag)                           */
void ascon_mac(const uint8_t *key, const uint8_t *msg,
               uint64_t len, uint8_t *tag)
{
    u64 s[5];

    /* ── INITIALIZATION ───────────────────────────────────────────────────
     * IV encoding (§2.4 of [1]):
     *   k=128  → 0x80
     *   ro=128 → 0x80
     *   enc(a) = (1∥0⁷) ⊕ a = 0x80 ⊕ 0x0C = 0x8C   [a=12=0x0C rounds]
     *   pad    = 0x00
     *   t=128  → 0x00000080  (big-endian 32-bit)
     * → IV as 64-bit big-endian word: 0x80808C0000000080
     *
     * Initial 320-bit state = IV ∥ K ∥ 0^192 :
     *   s[0] = IV
     *   s[1] = K[0..63]   (high 8 bytes of key)
     *   s[2] = K[64..127] (low  8 bytes of key)
     *   s[3] = 0
     *   s[4] = 0                                                           */
    s[0] = 0x80808C0000000080ULL;           /* FIX: was 0x8080840000000080 */
    s[1] = load64_be(key);
    s[2] = load64_be(key + 8);
    s[3] = 0ULL;
    s[4] = 0ULL;

    ascon_permutation(s, 12);               /* p^a — 12 rounds              */

    /* ── ABSORB ───────────────────────────────────────────────────────────
     * Process message in 256-bit (32-byte) blocks.
     * XOR each block into the rate words s[0]…s[3].
     * s[4] (64-bit capacity) is NEVER XORed with message data.
     *
     * Padding scheme (1∥0*): append byte 0x80, then zero bytes until the
     * padded length is a multiple of 32.  The message is always padded, so
     * there is always at least one final block.
     *
     * Domain separation for the last block:
     *   XOR (0^319 ∥ 1) into the state = flip the LSB of s[4]:  s[4] ^= 1
     *   This separates the absorb phase from the squeeze phase.            */

    uint64_t full_blocks = len / 32;        /* complete 32-byte blocks      */

    /* Non-final blocks: absorb then permute (no domain-sep bit) */
    for (uint64_t i = 0; i < full_blocks; i++) {
        const uint8_t *blk = msg + i * 32;
        s[0] ^= load64_be(blk);
        s[1] ^= load64_be(blk +  8);
        s[2] ^= load64_be(blk + 16);
        s[3] ^= load64_be(blk + 24);
        ascon_permutation(s, 12);           /* p^a — 12 rounds              */
    }

    /* Final padded block (always present, even for empty message) */
    uint8_t buf[32];
    memset(buf, 0, 32);
    uint64_t remaining = len - full_blocks * 32; /* 0 … 31 bytes            */
    if (remaining > 0)
        memcpy(buf, msg + full_blocks * 32, remaining);
    buf[remaining] = 0x80;                  /* 1∥0* padding                 */

    s[0] ^= load64_be(buf);
    s[1] ^= load64_be(buf +  8);
    s[2] ^= load64_be(buf + 16);
    s[3] ^= load64_be(buf + 24);
    s[4] ^= 1ULL;                           /* domain separation (0^319∥1) */

    ascon_permutation(s, 12);               /* p^a on final block           */

    /* ── SQUEEZE ──────────────────────────────────────────────────────────
     * ro = 128 bits → tag = ⌊S⌋_128 = s[0] ∥ s[1]
     * For a single 128-bit tag we read immediately — no extra p^a call.
     *
     * NOTE: There is NO doubly-keyed finalization (no K XOR before/after
     * p^a here). That belongs to Ascon-128 AEAD only. Ascon-MAC's security
     * comes entirely from the keyed initialization and sponge structure.   */
    store64_be(tag,     s[0]);
    store64_be(tag + 8, s[1]);
}
