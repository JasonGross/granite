#include <stdio.h>
#include <stdint.h> // we use 32-bit words
// #include <inttypes.h>

// rotate x to left by n bits, the bits that go over the left edge reappear on the right
#define R(x,n) (((x) << (n)) | ((x) >> (32-(n))))

// addition wraps modulo 2^32
// the choice of 7,9,13,18 "doesn't seem very important" (spec)
#define quarter(a,b,c,d) do {\
	b ^= R(d+a, 7);\
	c ^= R(a+b, 9);\
	d ^= R(b+c, 13);\
	a ^= R(c+d, 18);\
} while (0)

void salsa20_words(uint32_t *out, uint32_t in[16]) {
	uint32_t x[4][4];
	int i;
	for (i=0; i<16; ++i) x[i/4][i%4] = in[i];
	for (i=0; i<10; ++i) { // 10 double rounds = 20 rounds
		// column round: quarter round on each column; start at ith element and wrap
		quarter(x[0][0], x[1][0], x[2][0], x[3][0]);
		quarter(x[1][1], x[2][1], x[3][1], x[0][1]);
		quarter(x[2][2], x[3][2], x[0][2], x[1][2]);
		quarter(x[3][3], x[0][3], x[1][3], x[2][3]);
		// row round: quarter round on each row; start at ith element and wrap around
		quarter(x[0][0], x[0][1], x[0][2], x[0][3]);
		quarter(x[1][1], x[1][2], x[1][3], x[1][0]);
		quarter(x[2][2], x[2][3], x[2][0], x[2][1]);
		quarter(x[3][3], x[3][0], x[3][1], x[3][2]);
	}
	for (i=0; i<16; ++i) out[i] = x[i/4][i%4] + in[i];

#ifdef BAREMETAL
	// Make output visible on the bare-metal target: write the 16 result
	// words to the MMIO region (0x40000000..0x40000100). Using a volatile
	// word-aligned uint32_t* guarantees SW stores (and LW loads of out[i])
	// only -- no byte-wise ops, which the SymbExec ISA does not model.
	volatile uint32_t *mmio = (volatile uint32_t *)0x40000000u;
	for (i=0; i<16; ++i) mmio[i] = out[i];
#endif
}

// inputting a key, message nonce, keystream index and constants to that transormation
void salsa20_block(uint32_t out[16], const uint32_t key[8], uint64_t nonce, uint64_t index) {
	static const uint32_t c[4] = {
		0x61707865, 0x3320646e, 0x79622d32, 0x6b206574
	}; // "expand 32-byte k" as little-endian words

	uint32_t in[16] = {
		c[0],            key[0],            key[1],            key[2],
		key[3],          c[1],              (uint32_t)nonce,   (uint32_t)(nonce >> 32),
		(uint32_t)index, (uint32_t)(index >> 32), c[2],        key[4],
		key[5],          key[6],            key[7],            c[3]
	};

	salsa20_words(out, in);
}

// enc/dec: xor a message with transformations of key, a per-message nonce and block index
void salsa20(uint32_t *message, uint32_t mlen_words, const uint32_t key[8], uint64_t nonce) {
	uint32_t i;
	uint32_t block[16];
	for (i=0; i<mlen_words; i++) {
		if ((i & 15u) == 0) salsa20_block(block, key, nonce, i >> 4);
		message[i] ^= block[i & 15u];
	}
}

//Set 2, vector# 0:
//                         key = 00000000000000000000000000000000
//                               00000000000000000000000000000000
//                          IV = 0000000000000000
//               stream[0..63] = 9A97F65B9B4C721B960A672145FCA8D4
//                               E32E67F9111EA979CE9C4826806AEEE6
//                               3DE9C0DA2BD7F91EBCB2639BF989C625
//                               1B29BF38D39A9BDCE7C55F4B2AC12A39

uint32_t key[8] = {0};
uint64_t nonce = 0;
uint32_t msg[16] = {0};

#ifndef BAREMETAL
// Native (host) correctness test. Excluded from the bare-metal build, whose
// entry point is _start (startup.S) and which has no libc for printf.
//
// Expected keystream for Set 2, vector #0, as little-endian 32-bit words.
// (msg is XORed with the keystream; since msg starts all-zero, it becomes
//  the keystream. Each word is the byte-reversal of the stream[] hex above,
//  e.g. bytes 9A 97 F6 5B -> word 0x5BF6979A.)
static const uint32_t expected[16] = {
	0x5BF6979A, 0x1B724C9B, 0x21670A96, 0xD4A8FC45,
	0xF9672EE3, 0x79A91E11, 0x26489CCE, 0xE6EE6A80,
	0xDAC0E93D, 0x1EF9D72B, 0x9B63B2BC, 0x25C689F9,
	0x38BF291B, 0xDC9B9AD3, 0x4B5FC5E7, 0x392AC12A
};

int  main () {
	int i, ok = 1;
	salsa20(msg, 16, key, nonce);
	printf("keystream:");
	for (i = 0; i < 16; ++i) {
		printf(" %08X", msg[i]);
		if (msg[i] != expected[i]) ok = 0;
	}
	printf("\n%s\n", ok ? "PASS" : "FAIL");
	return ok ? 0 : 1;
}
#endif
