# OSLF in Mettapedia

Operational Semantics in Logical Form (OSLF) turns operational rewrite systems
into a logical/type-theoretic interface that is mechanically justified in Lean.
The core idea is: start from a `LanguageDef` (syntax + rewrites + premises),
define a declarative step relation, connect it to an executable engine, and
derive modal operators (`◇`, `□`) with a Galois connection.

## What OSLF Is

OSLF is a construction that:
- Takes a rewrite system with premises (`LanguageDef`).
- Defines a one-step reduction relation and proves it matches the executable engine.
- Derives modal operators `◇` and `□` and proves `◇ ⊣ □`.
- Provides a formula semantics and a sound checker for modal properties.

The outcome is a reusable logical interface on top of operational semantics,
grounded in definitional equality and theorem-level contracts, not ad hoc proofs.

Survey (end-to-end):
Start with a `LanguageDef` (syntax + rewrites + premises) and, if needed, a
`RelationEnv` for premise evaluation. Use `langRewriteSystemUsing` to get the
step relation, then `langDiamondUsing`/`langBoxUsing` to derive `◇/□` with
`langGaloisUsing` proving the adjunction. `langOSLF` packages the derived type
system. At the logic layer, `OSLFFormula.sem` is satisfaction and
`checkLangUsing` is the executable checker with soundness back to semantics.

## How To Use OSLF in Lean

Minimal path (sketch):

```lean
import Mettapedia.OSLF.CoreMain

open Mettapedia.OSLF

-- 1) Define a LanguageDef with types, terms, rewrites, and premises.
-- 2) Supply a RelationEnv for external premises if needed.
-- 3) Use langOSLF to derive the type system and modal operators.
-- 4) Use Formula.sem and checkLangUsing for properties.
```

Canonical APIs are in:
- `Mettapedia/OSLF/Framework/TypeSynthesis.lean`
  - `langRewriteSystemUsing`
  - `langDiamondUsing`, `langBoxUsing`
  - `langGaloisUsing`
  - `langOSLF`
- `Mettapedia/OSLF/Formula.lean`
  - `OSLFFormula`, `sem`, `checkLangUsing`
- `Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean`
  - Soundness/completeness bridge between declarative and executable reduction.

If you want a starting point with end-to-end instances, use:
- `Mettapedia/OSLF/CoreMain.lean` (recommended)
- `Mettapedia/OSLF/Main.lean` (same core plus public surface re-exports)

Where to start (beginners):
- `Mettapedia/OSLF/CoreMain.lean` — canonical entrypoint and contracts
- `Mettapedia/OSLF/Framework/TypeSynthesis.lean` — derive `◇/□` and `langOSLF`
- `Mettapedia/OSLF/Formula.lean` — formulas, semantics, checker soundness
- `Mettapedia/OSLF/MeTTaIL/Syntax.lean` — how `LanguageDef` is structured

What OSLF is not:
- Not a claim of global decidability: the checker is sound, not complete.
- Not a full MeTTa interpreter or parser; the MeTTa slice here is spec-facing.
- Not a promise that every premise relation is computable in Lean.

Paper/literature alignment boundary:
- Treat `Mettapedia/OSLF/Framework/PaperClaimTracker.lean`,
  `Mettapedia/OSLF/Framework/NTTClaimTracker.lean`, and
  `Mettapedia/OSLF/Framework/FULLStatus.lean` as authoritative for current
  formalized-claim status; anything outside those trackers is context, not a
  theorem-level project claim.

## MeTTa Slice (Spec-Facing, Pretty-Printed Syntax)

The spec-facing MeTTa slice is defined in:
- `Mettapedia/OSLF/MeTTaCore/FullLanguageDef.lean`

It uses explicit syntax patterns for display. Examples from the definition:
- State syntax: `"<" instr "|" space "|" out ">"`
- Instruction syntax: `eval(src)`, `unify(lhs,rhs)`, `type-of(atom,ty)`, `cast(atom,ty)`
- Grounded operations: `grounded1(op,arg)`, `grounded2(op,lhs,rhs)`
- Atom constructors: `true`, `false`, `gint(token)`, `gstring(token)`

Lean-level usage is still `Pattern.apply`, but those syntax patterns are the
canonical pretty-printing surface for the MeTTa slice. Example pretty forms:

Positive example (well-formed State/Space/Atom):
```
< eval(true) | space(nil, nil) | false >
```

Negative example (ill-formed Space; `true` is an Atom, not a Space):
```
< eval(true) | true | false >
```

For the same example at the Lean level:

```lean
import Mettapedia.OSLF.MeTTaCore.FullLanguageDef
import Mettapedia.OSLF.MeTTaCore.Premises

open Mettapedia.OSLF.MeTTaIL.Syntax

def exState : Pattern :=
  .apply "State"
    [ .apply "Eval" [.apply "ATrue" []]
    , Mettapedia.OSLF.MeTTaCore.Premises.space0Pattern
    , .apply "AFalse" [] ]
```

This is the canonical spec-facing representation used by the engine and
the OSLF synthesis pipeline.

## Current Entry Points

- `Mettapedia/OSLF/CoreMain.lean`
  - Core-first entrypoint for the OSLF/GSLT stack.
- `Mettapedia/OSLF/Main.lean`
  - Public OSLF surface (`CoreMain` plus framework/client exports), kept focused on OSLF.
- `Mettapedia/Languages/ProcessCalculi.lean`
  - Process-calculi facade (`PiCalculus`, `RhoCalculus`) under `Mettapedia/Languages/`.
  - Use this for process-calculus exploration without coupling to OSLF entrypoints.

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
  - **Def 21**: Codomain fibration (Arrow category) + Cartesian lifts via pullbacks
    with universal factorization
  - **Sec 4**: Image-comprehension adjunction i ⊣ c with full ↔ characterization
    (`range(p) ≤ φ ↔ p factors through φ.ι`)
  - **Thm 23**: Internal language package + functorial laws (identity and
    composition of theory morphisms preserve Π/Ω/Prop)

Strict NTT claim tracker:
- `Mettapedia/OSLF/Framework/NTTClaimTracker.lean` — authoritative source for
  current claim counts/status (including assumption-scoped items and necessity
  counterexamples such as
  `AssumptionNecessity.types_nonempty_necessary_for_piSigma`)

Scope note:
- This is theorem-level parity for the tracked NTT claim set, not a blanket
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

## Practical Workflow

1. Define a language in `LanguageDef`:
   - sorts (`types`)
   - constructors (`terms`)
   - rewrites (`rewrites`)
   - premises (`Premise`)
2. If needed, define external premise relations via `RelationEnv`.
3. Instantiate `langOSLF` (usually with your process sort).
4. Use `checkLangUsing` and its soundness bridges in `Formula.lean`.
5. Add an instance file with end-to-end theorems (TinyML/MeTTa pattern).

## Build

```bash
cd lean-projects/mettapedia
lake build Mettapedia.OSLF.CoreMain
lake build Mettapedia.OSLF.Main
```

## Notes

- `CoreMain` is the recommended target for core OSLF/GSLT validation.
- `Main` is aligned with the same focused OSLF boundary.
- Process-calculus modules are available via:
  - `Mettapedia/Languages/ProcessCalculi/PiCalculus.lean`
  - `Mettapedia/Languages/ProcessCalculi/RhoCalculus.lean`
- For exact completion claims, rely on `FULLStatus.lean` and concrete theorem names.

## What OSLF Is Not

- It is not a parser or a surface syntax standard: OSLF works on `Pattern` and `LanguageDef`.
- It is not a proof of “all desired properties”: only theorems stated and tracked
  in the claim trackers are asserted.
- It is not a substitute for a concrete semantics implementation: the executable
  engine is proven correct, but external premise relations must still be provided.

## Lean ↔ Rust Roundtrip Status

Validated roundtrip scripts in `hyperon/mettail-rust`:
- `scripts/roundtrip_tinymlsmoke.sh` — passes
- `scripts/roundtrip_mettaminimal.sh` — passes

Current ingestion boundary:
- `scripts/lean/ExportMeTTaMinimalRoundTrip.lean` exports a premise-free subset
  (`rw.premises.isEmpty`) for current Rust ingestion, so this validates the
  current export/runtime path but is not yet full premise-rich MeTTaFull ingestion.
