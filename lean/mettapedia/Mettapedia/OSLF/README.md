# OSLF in Mettapedia

Operational Semantics in Logical Form (OSLF) over `LanguageDef` rewrite systems,
with premise-aware execution, checker soundness, and presheaf-topos bridge layers.

## Current Entry Points

- `Mettapedia/OSLF/CoreMain.lean`
  - Core-first entrypoint for the current OSLF/GSLT stack.
- `Mettapedia/OSLF/Main.lean`
  - Public OSLF surface (`CoreMain` plus framework/client exports), kept focused on OSLF.
- `Mettapedia/Languages/ProcessCalculi.lean`
  - Process-calculi facade (`PiCalculus`, `RhoCalculus`) under `Mettapedia/Languages/`.
  - Use this for language-specific process-calculus exploration without coupling it to OSLF entrypoints.

## What Is Implemented

### 1) LanguageDef → RewriteSystem → OSLFTypeSystem

Main synthesis pipeline:
- `Mettapedia/OSLF/Framework/TypeSynthesis.lean`
  - `langRewriteSystemUsing`
  - `langDiamondUsing`, `langBoxUsing`
  - `langGaloisUsing`
  - `langOSLF`

This is the core "derive a type system from operational semantics" path.

### 2) Premise-Aware Operational Semantics

- `Mettapedia/OSLF/MeTTaIL/Syntax.lean`
  - `Premise`, `RewriteRule`, `LanguageDef`
- `Mettapedia/OSLF/MeTTaIL/Engine.lean`
  - `RelationEnv`
  - `applyRuleWithPremisesUsing`
  - `rewriteWithContextWithPremisesUsing`
- `Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean`
  - executable/declarative bridge with soundness/completeness theorems

### 3) Formula Layer + Checker Soundness

- `Mettapedia/OSLF/Formula.lean`
  - `OSLFFormula`, `sem`, `checkLangUsing`
  - checker-soundness bridges into semantic satisfaction and sort-fiber predicates
  - graph-object checker soundness corollaries for both `.dia` and `.box`

### 4) Native Type Theory (NTT) Endpoints

The strict NTT claim surface tracked in
`Mettapedia/OSLF/Framework/NTTClaimTracker.lean` is formalized in
`Mettapedia/OSLF/NativeType/`:

- `Construction.lean` — NatType, piType, sigmaType, TheoryMorphism (id, comp,
  preservation proofs)
- `CodomainFibration.lean` — All 6 strict NTT endpoint theorems:
  - **Prop 12**: Indexed adjoints (∃f ⊣ f* ⊣ ∀f) with Beck-Chevalley
  - **Prop 14**: Cosmic fibration (Frame-structured fibers)
  - **Prop 17**: Reification right adjoint layer (χ.F = ⊓{φ ⇨ F(φ)})
  - **Def 21**: Codomain fibration (Arrow category) + **Cartesian lifts via
    pullbacks** with universal factorization
  - **Sec 4**: Image-comprehension adjunction i ⊣ c with **full ↔
    characterization** (`range(p) ≤ φ ↔ p factors through φ.ι`)
  - **Thm 23**: Internal language package + **functorial laws** (identity and
    composition of theory morphisms preserve Π/Ω/Prop)

The strict NTT claim tracker is:
- `Mettapedia/OSLF/Framework/NTTClaimTracker.lean` — 12/12 claims resolved
  (11 proven, 1 assumption-scoped: Pi/Sigma under nonempty-family guard,
  with necessity proven at `AssumptionNecessity.types_nonempty_necessary_for_piSigma`)

Scope note:
- This is strict theorem-level parity for the tracked NTT claim set, not a blanket
  claim over every future-work extension discussed in the source paper.

### 5) Presheaf/Topos Lift Integration Status

The authoritative tracker is:
- `Mettapedia/OSLF/Framework/FULLStatus.lean`

Use this file for done/in-progress/missing milestones with code anchors.

### 6) Concrete Clients

- `Mettapedia/OSLF/Framework/TinyMLInstance.lean`
- `Mettapedia/OSLF/Framework/MeTTaMinimalInstance.lean`
- `Mettapedia/OSLF/Framework/MeTTaFullInstance.lean`
- `Mettapedia/OSLF/MeTTaCore/FullLanguageDef.lean`
- `Mettapedia/OSLF/MeTTaCore/Premises.lean`

## Language Workflow (Practical)

1. Define a language in `LanguageDef`:
   - sorts (`types`)
   - constructors (`terms`)
   - rewrites (`rewrites`)
   - premises (`Premise`)
2. If needed, define external premise relations via `RelationEnv`.
3. Instantiate `langOSLF` (usually with your process sort).
4. Use `checkLangUsing` + soundness bridges in `Formula.lean`.
5. Add an instance file with end-to-end theorem(s) (TinyML/MeTTa pattern).

## Build

```bash
cd lean-projects/mettapedia
lake build Mettapedia.OSLF.CoreMain
lake build Mettapedia.OSLF.Main
```

## Notes

- `CoreMain` is the recommended target for core OSLF/GSLT validation.
- `Main` is now aligned with the same focused OSLF boundary.
- Process-calculus modules are available via:
  - `Mettapedia/Languages/ProcessCalculi/PiCalculus.lean`
  - `Mettapedia/Languages/ProcessCalculi/RhoCalculus.lean`
- For exact completion claims, rely on `FULLStatus.lean` and concrete theorem names,
  not static line-count snapshots.

## Lean ↔ Rust Roundtrip Status

Validated roundtrip scripts in `hyperon/mettail-rust`:
- `scripts/roundtrip_tinymlsmoke.sh` — passes
- `scripts/roundtrip_mettaminimal.sh` — passes

Current ingestion boundary:
- `scripts/lean/ExportMeTTaMinimalRoundTrip.lean` exports a premise-free subset
  (`rw.premises.isEmpty`) for current Rust ingestion, so this validates the
  current export/runtime path but is not yet full premise-rich MeTTaFull ingestion.
