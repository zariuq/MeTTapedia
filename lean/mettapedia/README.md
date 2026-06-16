# Mettapedia formalized mathematics encyclopedia

Mettapedia hosts formalizations across probability theory, information theory, logic, set theory, and related areas.

## High-level structure

The package layout is:

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
└── externals/
```

## Toolchain

- The toolchain uses Lean 4.28.0 (see lean-toolchain).
- The toolchain uses Mathlib v4.28.0.
- The default local developer configuration is `lakefile.lean`, which uses
  local repos in `../externals/` for Foundation, exchangeability, provenance,
  OrderedSemigroups, Metatheory, CertifyingDatalog, and `mm-lean4`.
- `lakefile.toml` stays as the git-pinned fallback. If you remove
  `lakefile.lean`, Lake falls back to the pinned git dependency graph.

## Build

```bash
cd lean
./bootstrap_local_repos.sh
cd lean/mettapedia
lake exe cache get
lake build
```

- `bootstrap_local_repos.sh` clones the local editable repos into
  `lean/externals/` and `lean/standalone/` if they are missing, then leaves
  existing working trees alone.
- The build runs from `lean/mettapedia`.
- The first build should run `lake exe cache get` to fetch mathlib oleans.
- Prefer targeted `lake update <pkg>` over bare `lake update`; the bare form
  can bump transitive pins (e.g. batteries) past the v4.28.0 toolchain.

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

- `UniversalAI/`
  - UniversalAI hosts Hutter (2005) Chapters 4–7: AIXI agents, value functions, intelligence measure, time-bounded AIXI, problem classes, multi-agent extensions, self-modification, Gödel machines (~27K lines, 71 files)

- `Logic/HOL/`
  - Logic/HOL hosts Church-style higher-order logic: Henkin semantics, classical + intuitionistic soundness, Lindenbaum quotients, Henkinization, logical induction, probabilistic semantics (54 files)

- `Logic/UniversalPrediction/`
  - Logic/UniversalPrediction hosts Solomonoff–Hutter universal prediction theory (Chapters 2–3): prefix measures, enumeration, convergence, loss/error bounds, optimality (37 files, ~12.9K lines)

- `Languages/MeTTa/PureKernel/`
  - Languages/MeTTa/PureKernel hosts the trusted proof kernel for dependently-typed MeTTa Pure: Pi/Sigma/Id/universes, general declaration mechanism, pilot families (Bool, Nat, Unit)

- `Ethics/`
  - Ethics hosts Gewirth PGC formalization (port of Fuenmayor & Benzmüller AFP Isabelle/HOL work into Lean 4; drops 5 of 8 axioms as unnecessary)

- `Conformance/`
  - Conformance hosts runtime/spec boundary testing: kernel-checked I→O derivation proofs matching unit test expectations (6 files, ~2.7K lines)

- `CategoricalLogic/`
  - CategoricalLogic hosts categorical logic formalization

## Lean to mettail-rust example

The roundtrip and benchmark scripts live in the companion ai-agents workspace
(`hyperon/mettail-rust`), outside this repository.

```bash
# in the ai-agents workspace:
cd hyperon/mettail-rust
./scripts/roundtrip_mettaminimal.sh
./scripts/bench_mettaminimal_roundtrip.sh
```

- the exporter is hyperon/mettail-rust/scripts/lean/ExportMeTTaMinimalRoundTrip.lean (same workspace).

## Status review

- Proof completeness varies by subproject.
- Use `rg -n "sorry" Mettapedia/` to find proof gaps.
- `Mettapedia/ProbabilityTheory/KnuthSkilling/README.md` contains the
  Knuth-Skilling structure and build targets.

```bash
rg -n "sorry" Mettapedia/
```

## Contribution

- Contributions require explicit proofs.
- Contributions require documented theorem sources.
- Contributions require frequent `lake build` checks.

## External repo policy

- Use `zariuq` forks as `origin` remotes.
- Use source projects as `upstream` remotes, and use `godelclaw` only as a
  separate named remote when relevant.
- See `EXTERNAL_REPOS.md` for exact commands.
