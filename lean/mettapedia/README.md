# Mettapedia — Encyclopedia of Formalized Mathematics

Lean 4 library of formalizations across probability, information theory, logic, set theory, and related areas.

## Layout (high-level)

```
Mettapedia/
├── Algebra/              Ordered semigroups, algebraic structures
├── Analysis/             (placeholder)
├── Bridge/               Cross-module bridges (bit-vector evidence geometry)
├── CategoricalLogic/     Categorical logic (external port, lean-catLogic)
├── CategoryTheory/       NativeTypeTheory, PLN instance, de Finetti categorical
├── CognitiveArchitecture/  MetaMo, OpenPsi, MicroPsi, value systems
├── Combinatorics/        (placeholder)
├── Computability/        Arithmetical hierarchy (Σ⁰₂, Π⁰₂, Δ⁰₂)
├── Examples/             Concrete instances (KS symmetry framework)
├── GraphTheory/          Basic graph theory (Bondy & Murty, Diestel)
├── GSLT/                 Graph-Structured Lambda Theories (OSLF spec layer)
├── Implementation/       MeTTa PLN formula verification
├── InformationTheory/    Shannon entropy, information measures
├── Languages/            GF (Czech + English), π-calculus, ρ-calculus
├── Lists/                List-Set bridge lemmas
├── Logic/                PLN, evidence quantales, Solomonoff, exchangeability
├── MeasureTheory/        Measure theory from KS symmetry foundations
├── Metatheory/           Metalogic (model theory, proof theory)
├── NumberTheory/         (placeholder)
├── OSLF/                 Operational Semantics in Logical Form
├── ProbabilityTheory/    Knuth-Skilling, Cox, Bayesian networks, hypercube
├── QuantumTheory/        Quantum from symmetry (Skilling & Knuth 2018)
├── SetTheory/            Borel determinacy
├── UniversalAI/          AIXI, Solomonoff, reflective oracles, grain of truth
└── external/             Vendored sub-packages (exchangeability)
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

- `ProbabilityTheory/KnuthSkilling/` — Knuth-Skilling Foundations of Inference
- `ProbabilityTheory/Cox/` — Cox-style probability calculus
- `InformationTheory/ShannonEntropy/`
- `Logic/` — PLN, evidence quantales, Solomonoff, exchangeability, WorldModel calculus
- `SetTheory/BorelDeterminacy/`
- `OSLF/` — core OSLF/GSLT formalizations
- `GSLT/` — Graph-Structured Lambda Theories (categorical spec layer for OSLF)
- `Languages/GF/` — GF abstract syntax + Czech morphology + English clause construction + semantic bridge to NTT
- `Languages/ProcessCalculi/` — pi-calculus, rho-calculus, spice calculus, pi-to-rho encoding
- `CategoryTheory/` — NativeTypeTheory (Grothendieck construction), PLN categorical instance, de Finetti categorical
- `CognitiveArchitecture/` — MetaMo motivational framework, OpenPsi, MicroPsi, value systems
- `Algebra/OrderedSemigroups/`

## Lean -> mettail-rust example

MeTTaMinimal can be exported from Lean and checked end-to-end in
`hyperon/mettail-rust`:

```bash
cd ~/claude/hyperon/mettail-rust

# Full roundtrip check (Lean export -> Rust build -> one-step rewrite check)
./scripts/roundtrip_mettaminimal.sh

# Benchmark command (default 3 runs)
./scripts/bench_mettaminimal_roundtrip.sh
```

Exporter used by the script:
- `hyperon/mettail-rust/scripts/lean/ExportMeTTaMinimalRoundTrip.lean`

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

## External Repo Policy

Use godelclaw forks as origin and zariuq repos as upstream for embedded external repos.
See EXTERNAL_REPOS.md for the exact remotes and sync commands.
