# Mettapedia — Encyclopedia of Formalized Mathematics

Lean 4 library of formalizations across probability, information theory, logic, set theory, and related areas.

## Layout (high‑level)

```
Mettapedia/
├── ProbabilityTheory/
├── InformationTheory/
├── Logic/
├── UniversalAI/
├── Algebra/
├── SetTheory/
├── OSLF/
└── ...
```

## Toolchain

- Lean 4.27.0 (see `lean-toolchain`)
- Mathlib v4.27.0 (see `lakefile.toml`)
- Local dependencies are included as subdirectories when needed (e.g., `Algebra/OrderedSemigroups/`).

## Build

```bash
cd lean-projects/mettapedia
lake update && lake exe cache get   # first-time only

export LAKE_JOBS=3
ulimit -Sv 6291456
nice -n 19 lake build
```

## Notable subprojects (see their READMEs for status)

- `ProbabilityTheory/KnuthSkilling/` — Knuth–Skilling Foundations of Inference
- `ProbabilityTheory/Cox/` — Cox-style probability calculus
- `InformationTheory/ShannonEntropy/`
- `Logic/` — PLN and related logical formalisms, including a **WorldModel calculus** for agent/environment reasoning
- `SetTheory/BorelDeterminacy/`
- `OSLF/` — ρ‑calculus / OSLF formalizations
- `Algebra/OrderedSemigroups/`

## Status & review

Proof completeness varies by subproject. To check local gaps:

```bash
rg -n "sorry" Mettapedia/
```

For Knuth–Skilling specific structure and build targets, see:
`Mettapedia/ProbabilityTheory/KnuthSkilling/README.md`.

## Contributing

1. Keep proofs explicit; avoid axioms unless clearly justified.
2. Document sources in theorem headers.
3. Build frequently (`lake build`).
