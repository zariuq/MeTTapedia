# ATP Hammer Test Files

This directory contains TPTP format files generated from Megalodon's ATP hammer integration during testing and proof development.

## File Types

### hammer_test.*.fof.p (2,386 files)
- TPTP first-order format exports from hammer testing
- Generated during development of ramsey36 proofs
- Contain axioms and theorems translated from Megalodon

### adj17sym.*.fof.p (67 files)
- TPTP exports related to adj17_with_sym.mg proof development
- Part of the Ramsey(3,6) formalization

## Purpose

These files are useful for:
- Testing external ATP provers (E, Vampire, etc.)
- Verifying proof obligations with automated theorem provers
- Benchmarking ATP performance on formalized mathematics

## Usage

To test a file with E prover:
```bash
eprover --auto hammer_test.1058.fof.p
```

To test with Vampire:
```bash
vampire -t 60 hammer_test.1058.fof.p
```

## Status

These files are kept for reference and future ATP integration work. They are not required for kernel verification of Megalodon proofs.
