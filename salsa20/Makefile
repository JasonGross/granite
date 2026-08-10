# Build salsa20.c for a simple RV32 target.
#
# Default target only compiles (no link), so it works even without an RV32 libc.
# Use `make elf` if your toolchain provides a C runtime + libc.

CROSS      ?= riscv64-unknown-elf-
CC         := $(CROSS)gcc
OBJDUMP    := $(CROSS)objdump

SRC        := salsa20.c
BASE       := salsa20

ARCH       ?= rv32i
ABI        ?= ilp32
CFLAGS     ?= -O2 -funroll-loops -Wall -Wextra -march=$(ARCH) -mabi=$(ABI)
LDFLAGS    ?= -march=$(ARCH) -mabi=$(ABI)

# Flags for the bare-metal flat binary (no libc, text at 0x0).
# -Wl,--no-relax: keep auipc+jalr call pairs; prevents linker from relaxing
#                 them into jal, so Jal need not be added to the ISA.
# -DBAREMETAL: enable the MMIO output path in salsa20_words.
FLAT_CFLAGS := -O2 -funroll-loops -march=$(ARCH) -mabi=$(ABI) \
               -nostdlib -ffreestanding -Wl,--no-relax -DBAREMETAL

# Host (native) compiler for the runnable correctness test.
HOSTCC     ?= cc

.PHONY: all elf dump flat coq test clean

# Compile-only outputs (safe default)
all: $(BASE).rv32.o $(BASE).rv32.s

$(BASE).rv32.o: $(SRC)
	$(CC) $(CFLAGS) -c $< -o $@

$(BASE).rv32.s: $(SRC)
	$(CC) $(CFLAGS) -S $< -o $@

# Optional linked ELF (requires target libc/startup files)
elf: $(BASE).rv32.elf

$(BASE).rv32.elf: $(SRC)
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)

# Disassembly of linked ELF
dump: $(BASE).rv32.dump

$(BASE).rv32.dump: $(BASE).rv32.elf
	$(OBJDUMP) -d $< > $@

# Bare-metal flat binary for granite SymbExec analysis.
# Text section placed at 0x0; entry is _start in startup.S which calls
# salsa20_words with zeroed buffers then spins (beq x0,x0,0).
flat: $(BASE).flat.elf $(BASE).flat.bin $(BASE).flat.dump

$(BASE).flat.elf: $(SRC) startup.S linker.ld
	$(CC) $(FLAT_CFLAGS) -T linker.ld startup.S $(SRC) -o $@

$(BASE).flat.bin: $(BASE).flat.elf
	$(CROSS)objcopy -O binary --only-section=.text $< $@

$(BASE).flat.dump: $(BASE).flat.elf
	$(OBJDUMP) -d $< > $@

# Coq program definition wrapping the flat binary.
coq: Salsa20Prog.v

Salsa20Prog.v: $(BASE).flat.bin bin_to_coq.py
	python3 bin_to_coq.py $< -o $@

# Native correctness test: build with the host compiler (no -DBAREMETAL, so
# the MMIO path is excluded) and run, checking against Set 2 vector #0.
test: $(BASE).test
	./$(BASE).test

$(BASE).test: $(SRC)
	$(HOSTCC) -O2 -Wall -Wextra $< -o $@

clean:
	rm -f $(BASE).rv32.o $(BASE).rv32.s $(BASE).rv32.elf $(BASE).rv32.dump \
	      $(BASE).flat.elf $(BASE).flat.bin $(BASE).flat.dump \
	      $(BASE).test \
	      Salsa20Prog.v
