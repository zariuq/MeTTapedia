# Mettapedia formalized mathematics encyclopedia

Mettapedia hosts formalizations across probability theory, information theory, logic, set theory, and related areas.

## High-level structure

the structure presents the high-level Mettapedia directory layout.

```
Mettapedia/
├── Algebra/
├── Bridge/
├── CategoricalLogic/
├── CategoryTheory/
├── CognitiveArchitecture/
├── Computability/
├── Examples/
├── GraphTheory/
├── GSLT/
├── Implementation/
├── InformationTheory/
├── Languages/
├── Logic/
├── MeasureTheory/
├── Metatheory/
├── OSLF/
├── ProbabilityTheory/
├── QuantumTheory/
├── SetTheory/
├── UniversalAI/
└── external/
```

## Toolchain

- The toolchain uses Lean 4.27.0 (see lean-toolchain).
- The toolchain uses Mathlib v4.27.0 (see lakefile.toml).
- Local dependencies live in local subdirectories when needed.

## Build

```bash
cd lean-projects/mettapedia
lake update && lake exe cache get

export LAKE_JOBS=3
ulimit -Sv 6291456
nice -n 19 lake build
```

- the build runs from lean-projects/mettapedia.
- The first build runs lake update and lake exe cache get.
- the build uses LAKE_JOBS=3 by default.
- the build uses a 6 GiB memory cap via ulimit -Sv 6291456.
- the build runs nice -n 19 lake build.

## Notable subprojects

- `ProbabilityTheory/KnuthSkilling/`
  - ProbabilityTheory/KnuthSkilling hosts Knuth-Skilling Foundations of Inference proofs

- `ProbabilityTheory/Cox/`
  - ProbabilityTheory/Cox hosts Cox-style probability calculus formalization

- `InformationTheory/ShannonEntropy/`
  - InformationTheory/ShannonEntropy hosts Shannon entropy formalization

- `Logic/`
  - Logic hosts PLN, evidence quantales, Solomonoff induction, exchangeability, and world model calculus

- `SetTheory/BorelDeterminacy/`
  - SetTheory/BorelDeterminacy hosts Borel determinacy formalization

- `OSLF/`
  - OSLF hosts core OSLF and GSLT formalizations

- `GSLT/`
  - GSLT hosts the categorical specification layer for OSLF

- `Languages/GF/`
  - Languages/GF hosts GF abstract syntax, Czech morphology, English clause construction, and an NTT semantic bridge

- `Languages/ProcessCalculi/`
  - Languages/ProcessCalculi hosts pi-calculus, rho-calculus, spice calculus, and pi-to-rho encoding

- `CategoryTheory/`
  - CategoryTheory hosts NativeTypeTheory, a PLN categorical instance, and de Finetti categorical development

- `CognitiveArchitecture/`
  - CognitiveArchitecture hosts MetaMo, OpenPsi, MicroPsi, and value-system models

- `Algebra/OrderedSemigroups/`
  - Algebra/OrderedSemigroups hosts ordered semigroup formalization

## Lean to mettail-rust example

The roundtrip script checks Lean export, Rust build, and one-step rewrite behavior.
The benchmark script runs three rounds by default.

```bash
cd ~/claude/hyperon/mettail-rust

./scripts/roundtrip_mettaminimal.sh
./scripts/bench_mettaminimal_roundtrip.sh
```

- the exporter is hyperon/mettail-rust/scripts/lean/ExportMeTTaMinimalRoundTrip.lean.

## Status review

- the proof completeness varies by the subproject.
- the local check runs rg -n "sorry" Mettapedia/ to find proof gaps.
- Mettapedia/ProbabilityTheory/KnuthSkilling/README.md contains the Knuth-Skilling structure and build targets.

```bash
rg -n "sorry" Mettapedia/
```

## Contribution

- the contribution requires explicit proofs.
- the contribution requires documented theorem sources.
- the contribution requires frequent lake build checks.

## External repo policy

- the policy uses godelclaw forks as origin remotes.
- the policy uses zariuq repos as upstream remotes.
- the policy references EXTERNAL_REPOS.md for exact commands.
