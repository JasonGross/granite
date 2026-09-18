# Granite

This repository contains the mechanized Rocq artifact accompanying the paper
*"Granite: A Modular Methodology for Foundational Verification of Hardware–Software Leakage Contracts."*

## Requirements

Tested with the following toolchain (via [opam](https://opam.ocaml.org/doc/Install.html)):

| Component            | Version   |
|----------------------|-----------|
| OCaml                | 5.4.1     |
| Dune                 | 3.22.2    |
| Rocq (Coq)           | 9.1.1     |
| rocq-stdlib          | 9.1.0     |
| rocq-stdpp           | 1.13.0    |
| rocq-stdpp-bitvector | 1.11.0    |
| coq-record-update    | 0.3.4     |

## Building

```sh
git submodule update --init --recursive   # fetch quartz/
opam install . --deps-only                 # or install the versions above by hand
dune build                                 # builds core, app, isaSpec, quartz, salsa20
```

`riscvConnection/` (statements only, see mit-plv/granite#1) additionally needs
[coqutil](https://github.com/mit-plv/coqutil) and [riscv-coq](https://github.com/mit-plv/riscv-coq)
built from source (stdlib-bits versions, i.e. coqutil master and riscv-coq master), found through
`COQPATH`:

```sh
COQPATH=/path/to/coqutil/src:/path/to/riscv-coq/src dune build
```

## License

See [LICENSE](LICENSE).
