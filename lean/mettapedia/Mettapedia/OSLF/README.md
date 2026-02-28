# OSLF overview

OSLF turns operational rewrite systems into a logical/type-theoretic interface.
Lean justifies the interface mechanically.
The core idea starts from `LanguageDef`.
The core idea connects the step relation to the executable engine.
The core idea derives modal operators with a Galois connection.

## OSLF is a construction

OSLF is a construction.

- It takes a rewrite system with premises.
- It defines a one-step reduction relation.
- The one-step reduction relation matches the executable engine.
- It derives modal operators for `◇` and `□`.
- It proves `◇ ⊣ □`.
- It provides a formula semantics and a sound checker for modal properties.

The outcome is a reusable logical interface on top of operational semantics.
Definitional equality and theorem-level contracts ground the interface.
Ad hoc proofs don't ground the interface.

### End-to-end survey

`RelationEnv` is needed for premise evaluation.
`langRewriteSystemUsing` gets the step relation.
`langDiamondUsing` and `langBoxUsing` derive modal operators.
`langGaloisUsing` proves the adjunction.
`langOSLF` packages the derived type system.
`checkLangUsing` provides an executable checker.
Checker soundness connects the checker to semantics.

## OSLF usage in Lean

### Minimal path sketch

```lean
import Mettapedia.OSLF.CoreMain

open Mettapedia.OSLF

-- 1) Define a LanguageDef with types, terms, rewrites, and premises.
-- 2) Supply a RelationEnv for external premises if needed.
-- 3) Use langOSLF to derive the type system and modal operators.
-- 4) Use Formula.sem and checkLangUsing for properties.
```

### Canonical APIs

- `Mettapedia/OSLF/Framework/TypeSynthesis.lean`
  - `langRewriteSystemUsing`
  - `langDiamondUsing`
  - `langBoxUsing`
  - `langGaloisUsing`
  - `langOSLF`
- `Mettapedia/OSLF/Formula.lean`
  - `OSLFFormula`
  - `sem`
  - `checkLangUsing`
- `Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean`

- `Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean` is a soundness-completeness bridge.

### Starting points

- `Mettapedia/OSLF/CoreMain.lean`
- `Mettapedia/OSLF/Main.lean`

### Beginner paths

- `Mettapedia/OSLF/CoreMain.lean`
- `Mettapedia/OSLF/Framework/TypeSynthesis.lean`
- `Mettapedia/OSLF/Formula.lean`
- `Mettapedia/OSLF/MeTTaIL/Syntax.lean`

### OSLF limit

- It isn't a claim of global decidability.
- It isn't a full MeTTa interpreter or a parser.
- It doesn't promise computability for premise relations in Lean.

### Paper/literature alignment boundary

- `Mettapedia/OSLF/Framework/PaperClaimTracker.lean`
- `Mettapedia/OSLF/Framework/NTTClaimTracker.lean`
- `Mettapedia/OSLF/Framework/FULLStatus.lean`

## MeTTa spec-facing slice

The spec-facing MeTTa slice uses `Mettapedia/OSLF/MeTTaCore/FullLanguageDef.lean`.

It uses explicit syntax patterns for display.

### Examples from the definition

- State syntax: `"<" instr "|" space "|" out ">"`
- Instruction syntax: `eval(src), unify(lhs,rhs), type-of(atom,ty), cast(atom,ty)`
- Grounded operations: `grounded1(op,arg), grounded2(op,lhs,rhs)`
- Atom constructors: `true, false, gint(token), gstring(token)`

### Positive example

```
< eval(true) | space(nil, nil) | false >
```

### Negative example

```
< eval(true) | true | false >
```

### Same example at the Lean level

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

This is the canonical spec-facing representation.

The engine and the OSLF synthesis pipeline use this canonical representation.

## Current entry point

- `Mettapedia/OSLF/CoreMain.lean`
- `Mettapedia/OSLF/Main.lean`
- `Mettapedia/Languages/ProcessCalculi.lean`

## Implemented components

### LanguageDef derives RewriteSystem and OSLFTypeSystem

- `Mettapedia/OSLF/Framework/TypeSynthesis.lean`
  - `langRewriteSystemUsing`
  - `langDiamondUsing`
  - `langBoxUsing`
  - `langGaloisUsing`
  - `langOSLF`

This is the core "derive a type system from operational semantics" path.

### Premise-aware operational semantics

- `Mettapedia/OSLF/MeTTaIL/Syntax.lean`
  - `Premise`
  - `RewriteRule`
  - `LanguageDef`
- `Mettapedia/OSLF/MeTTaIL/Engine.lean`
  - `RelationEnv`
  - `applyRuleWithPremisesUsing`
  - `rewriteWithContextWithPremisesUsing`
- `Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean`

- `Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean` is an executable-declarative bridge.

### Formula-layer checker-soundness status

- `Mettapedia/OSLF/Formula.lean`
  - `OSLFFormula`
  - `sem`
  - `checkLangUsing`

- `Mettapedia/OSLF/Formula.lean` includes checker-soundness bridges.
- `Mettapedia/OSLF/Formula.lean` includes graph-object checker corollaries for .dia and .box.

### Native-type endpoints

`Mettapedia/OSLF/NativeType/` formalizes the strict NTT claim surface.
`Mettapedia/OSLF/Framework/NTTClaimTracker.lean` is the authoritative tracker.
The scope is tracked-claim parity.
The scope isn't blanket future-work parity.

- `Construction.lean`
  - `NatType`
  - `piType`
  - `sigmaType`
  - `TheoryMorphism`
- `CodomainFibration.lean`
  - `Prop 12`
  - `Prop 14`
  - `Prop 17`
  - `Def 21`
  - `Sec 4`
  - `Thm 23`
- `Mettapedia/OSLF/Framework/NTTClaimTracker.lean`
  - `AssumptionNecessity.types_nonempty_necessary_for_piSigma`

### Presheaf/topos-lift status

- `Mettapedia/OSLF/Framework/FULLStatus.lean`

### Concrete clients

- `Mettapedia/OSLF/Framework/TinyMLInstance.lean`
- `Mettapedia/OSLF/Framework/MeTTaMinimalInstance.lean`
- `Mettapedia/OSLF/Framework/MeTTaFullInstance.lean`
- `Mettapedia/OSLF/MeTTaCore/FullLanguageDef.lean`
- `Mettapedia/OSLF/MeTTaCore/Premises.lean`

## Practical workflow

- LanguageDef: `types, terms, rewrites, Premise`
- RelationEnv: `if needed`
- langOSLF: `instantiation`
- checkLangUsing: `plus soundness bridges`

- The workflow ends with an instance file and end-to-end theorems.

## Build

```bash
cd lean-projects/mettapedia
lake build Mettapedia.OSLF.CoreMain
lake build Mettapedia.OSLF.Main
```

## Notes

- `CoreMain` is the recommended target for core OSLF/GSLT validation.
- `Main` aligns the same focused OSLF boundary.
- Process-calculus modules are available.
- Maintainers rely `FULLStatus.lean` and concrete theorem names for exact completion claims.

- `Mettapedia/Languages/ProcessCalculi/PiCalculus.lean`
- `Mettapedia/Languages/ProcessCalculi/RhoCalculus.lean`

## OSLF limit

- It isn't a parser or a surface syntax standard.
- It isn't a proof of "all desired properties".
- It isn't a substitute for a concrete semantics implementation.

## Lean-Rust-roundtrip status

It validates roundtrip scripts in `hyperon/mettail-rust`.

- `scripts/roundtrip_tinymlsmoke.sh`
- `scripts/roundtrip_mettaminimal.sh`

It exports a premise-free subset for current Rust ingestion.
The current boundary isn't full premise-rich MeTTaFull ingestion.
