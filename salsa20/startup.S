/* Minimal bare-metal startup for granite SymbExec analysis.
 *
 * Sets up a stack, allocates zeroed in[16] and out[16] buffers,
 * calls salsa20_words(out, in), then spins forever.
 * The spin (beq x0, x0, 0 with mie=0) is the Safe termination
 * condition recognized by the symbolic executor.
 */

    .section .text.startup
    .global _start
_start:
    /* Stack at top of 64 KiB RAM (address 0x10000). */
    lui   sp, 0x10

    /* Allocate 128 bytes: out[16] at sp+0..sp+63, in[16] at sp+64..sp+127. */
    addi  sp, sp, -128

    /* Zero out[16] (offsets 0..60). */
    sw    x0,   0(sp)
    sw    x0,   4(sp)
    sw    x0,   8(sp)
    sw    x0,  12(sp)
    sw    x0,  16(sp)
    sw    x0,  20(sp)
    sw    x0,  24(sp)
    sw    x0,  28(sp)
    sw    x0,  32(sp)
    sw    x0,  36(sp)
    sw    x0,  40(sp)
    sw    x0,  44(sp)
    sw    x0,  48(sp)
    sw    x0,  52(sp)
    sw    x0,  56(sp)
    sw    x0,  60(sp)

    /* Zero in[16] (offsets 64..124). */
    sw    x0,  64(sp)
    sw    x0,  68(sp)
    sw    x0,  72(sp)
    sw    x0,  76(sp)
    sw    x0,  80(sp)
    sw    x0,  84(sp)
    sw    x0,  88(sp)
    sw    x0,  92(sp)
    sw    x0,  96(sp)
    sw    x0, 100(sp)
    sw    x0, 104(sp)
    sw    x0, 108(sp)
    sw    x0, 112(sp)
    sw    x0, 116(sp)
    sw    x0, 120(sp)
    sw    x0, 124(sp)

    /* a0 = out, a1 = in. */
    addi  a0, sp, 0
    addi  a1, sp, 64
    /* "call" emits auipc+jalr; with -Wl,--no-relax the linker will not
     * relax this to a jal, so Jal need not be added to the ISA. */
    call  salsa20_words

spin:
    beq   x0, x0, spin
