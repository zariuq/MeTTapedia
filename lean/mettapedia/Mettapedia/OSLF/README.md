# OSLF — Operational Semantics in Logical Form (Lean 4)

OSLF turns operational systems into a logical/type-theoretic interface.
This development proves relational modal constructions and executable results
for specified fragments, starting from `LanguageDef`. The full source
construction remains open: context-labelled transitions, higher-order label
comparison, freely generated type-system structure, and several NTT categorical
obligations are not established by the elementary modal adjunction.

Reference orientation: OSLF is the Lean-formalized bridge from operational rules to modal/type-theoretic structure; [Native Type Theory](https://arxiv.org/abs/2102.04672) supplies the broader categorical foundation, [Generating Hypercubes of Type Systems](https://github.com/F1R3FLY-io/publications/blob/main/drafts/Hypercube/main.pdf) refines the generated type-system family, and [MeTTaIL](https://github.com/F1R3FLY-io/mettail-rust) is the executable-language-generation side.

## OSLF is a construction

OSLF is a construction.

- It takes a rewrite system with premises.
- It defines a one-step reduction relation.
- Executable correspondence has its own fuel, premise, and matching hypotheses.
- It derives modal operators for `◇` and `□`.
- It proves `◇ ⊣ □`.
- It provides a formula semantics and a sound checker for modal properties.

The proved outcome is a reusable relational logical interface on top of the
specified operational semantics. Its theorem-level contracts do not imply
correspondence with every runtime implementation or with the full source OSLF.

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

-- 1) Define a LanguageDef with types, terms, equations, and conditional rewrites.
-- 2) Supply a RelationEnv for external premises if needed.
-- 3) Use langOSLF to derive the type system and modal operators.
-- 4) Use Formula.sem and checkLangUsing for properties.
```

### Inspect a LanguageDef and its native predicate interface

A `LanguageDef` records declared syntax, equations, and conditional rewrite
rules. The relational construction exposes an `OSLFTypeSystem`
(predicates-as-frames with `◇`/`□` and a proven Galois connection), native
predicate objects `(sort, predicate)`, and a sort-crossing constructor diagram.
These components are not the full freely generated type system or the complete
categorical Native Type Theory construction.

Inspect the worked ρ-calculus declaration (requires a built tree) from
`lean/mettapedia/`:

```bash
lake env lean Mettapedia/OSLF/Tools/OSLFRunDemo.lean
```

which prints the declared unary sort crossings:

```
"rho NTT crossing count = 2"
[("PDrop", "Name", "Proc"), ("NQuote", "Proc", "Name")]
```

Those rows inspect the declared operations `NQuote : Proc → Name` and
`PDrop : Name → Proc`; they do not construct generated logical formers or prove
a function-object adjunction. `langNativeType` separately packages a chosen
`(sort, predicate)` as a native predicate object.

To inspect the same interface for another definition (fill in `myGSLT`; `procSort`
defaults to `"Proc"`):

```lean
import Mettapedia.OSLF.CoreMain
import Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF
open Mettapedia.OSLF.Framework.ConstructorCategory

def myGSLT : LanguageDef := { /- name, types, terms, equations, rewrites -/ }

-- OSLF type system + modal operators (◇ ⊣ □):
#check langOSLF myGSLT                    -- : OSLFTypeSystem …
#check langDiamond myGSLT                 -- ◇ : (Pattern → Prop) → (Pattern → Prop)
#check langBox myGSLT                     -- □
#check langGaloisUsing RelationEnv.empty myGSLT  -- proof ◇ ⊣ □ (use a non-empty RelationEnv if the GSLT has premise relations)

-- Native predicate objects and declared sort crossings:
#check langNativeType myGSLT              -- native (sort, predicate) type
#eval  unaryCrossings myGSLT              -- declaration inspection, as above

-- Check a modal property of a term (see Formula.lean: `sem`, `checkLang`/`checkLangUsing`):
#check checkLang myGSLT
```

Fuller worked GSLTs to copy from: `Framework/TinyMLInstance.lean`,
`Framework/MeTTaMinimalInstance.lean`, `Framework/MeTTaFullInstance.lean`; the
ρ-calculus DSL at `Languages/ProcessCalculi/RhoCalculus/LanguageDefDSL.lean`.

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
- `Mettapedia/OSLF/MeTTaIL/ContextualStep.lean`

- `Mettapedia/OSLF/MeTTaIL/ContextualStep.lean` derives the least contextual
  reduction from authored congruence premises and proves its bounded executor exact.
  This least authored closure is distinct from constructing least enabling
  context labels by relative pushouts.

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

The spec-facing MeTTa slice uses `Mettapedia/Languages/MeTTa/OSLFCore/FullLanguageDef.lean`.

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
import Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef
import Mettapedia.Languages.MeTTa.OSLFCore.Premises

open Mettapedia.OSLF.MeTTaIL.Syntax

def exState : Pattern :=
  .apply "State"
    [ .apply "Eval" [.apply "ATrue" []]
    , Mettapedia.Languages.MeTTa.OSLFCore.Premises.space0Pattern
    , .apply "AFalse" [] ]
```

This is the canonical spec-facing representation.

The engine and the OSLF synthesis pipeline use this canonical representation.

## MeTTaIL vs runtime boundary

`Mettapedia/OSLF/MeTTaIL` is the semantic IL and export boundary:

- `Syntax`, `LanguageDef`, declarative/executable reduction bridges
- OSLF synthesis hooks (`langRewriteSystem`, `langOSLF`, `langGalois`)
- export-oriented tooling and metadata paths

Executable runtime implementations belong in the separate lightweight project:

- `Mettapedia/lean/algorithms/Algorithms/MeTTa/...`
- simple interpreter/runtime path
- staged/specialized runtime path

### Positive example

- proving a language-level property (`langGalois` / `ContextualStep.Step`) belongs in `OSLF/MeTTaIL`.

### Negative example

- putting mutable runtime/session implementation details into `OSLF/MeTTaIL` does not belong there; keep that in `algorithms`.

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
  - `rewriteStepWithPremisesUsing`
- `Mettapedia/OSLF/MeTTaIL/ContextualStep.lean`

- `Mettapedia/OSLF/MeTTaIL/ContextualStep.lean` defines the least authored
  contextual relation and proves the fuel-indexed compiler sound and complete.

### Formula-layer checker-soundness status

- `Mettapedia/OSLF/Formula.lean`
  - `OSLFFormula`
  - `sem`
  - `checkLangUsing`

- `Mettapedia/OSLF/Formula.lean` includes checker-soundness bridges.
- `Mettapedia/OSLF/Formula.lean` includes graph-object checker corollaries for .dia and .box.

### Native-type endpoints

`Mettapedia/OSLF/NativeType/` implements the components identified by
`Mettapedia/OSLF/Framework/NTTClaimTracker.lean`. The tracker distinguishes proved
endpoints from remaining source obligations; its metadata checks do not prove
that an endpoint has the mathematical strength of the cited paper statement.

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
- `Mettapedia/Languages/MeTTa/OSLFCore/FullLanguageDef.lean`
- `Mettapedia/Languages/MeTTa/OSLFCore/Premises.lean`

## Practical workflow

- LanguageDef: `name, types, terms, equations, rewrites`; premises belong to rules.
- RelationEnv: `if needed`
- langOSLF: `instantiation`
- checkLangUsing: `plus soundness bridges`

- Each instance needs correspondence theorems for its advertised executable domain.

## Build

```bash
cd Mettapedia/lean/mettapedia
lake build Mettapedia.OSLF.CoreMain
lake build Mettapedia.OSLF.Main
```

## Notes

- `CoreMain` is the recommended target for core OSLF/GSLT validation.
- `Main` aligns the same focused OSLF boundary.
- Process-calculus modules are available.
- Use `FULLStatus.lean`, source-ledger obligations, and actual theorem statements
  together when assessing completion.
- Source placeholder searches, compiled axiom-closure audits, and completed
  dependency builds check different boundaries. None establishes source fidelity
  by itself; claim-tracker checks validate the inventory, not full paper parity.

- `Mettapedia/Languages/ProcessCalculi/PiCalculus.lean`
- `Mettapedia/Languages/ProcessCalculi/RhoCalculus.lean`

## OSLF limit

- It isn't a parser or a concrete syntax standard.
- It isn't a proof of "all desired properties".
- It isn't a substitute for a concrete semantics implementation.

## Lean-Rust-roundtrip status

It validates roundtrip scripts in `hyperon/mettail-rust`.

- `scripts/roundtrip_tinymlsmoke.sh`
- `scripts/roundtrip_mettaminimal.sh`

It exports a premise-free subset for current Rust ingestion.
The current boundary isn't full premise-rich MeTTaFull ingestion.

## References

- L. Gregory Meredith and Mike Stay, ["Operational Semantics in Logical Form" (2020)](../../../../papers/references.bib) — the source OSLF algorithm, cited in the local bibliography; see also this project's [Lean 4 OSLF writeup](../../../../papers/leanOSLF.pdf).
- Christian Williams and Mike Stay, ["Native Type Theory"](https://arxiv.org/abs/2102.04672) — categorical foundation for the [`NativeType/`](NativeType/) endpoints and [`NTTClaimTracker.lean`](Framework/NTTClaimTracker.lean).
- Mike Stay, L. Gregory Meredith, and Christian Wells, ["Generating Hypercubes of Type Systems"](https://github.com/F1R3FLY-io/publications/blob/main/drafts/Hypercube/main.pdf) — modal type-former and hypercube background for [`ModalHypercube.lean`](Framework/ModalHypercube.lean) and related GSLT functor files.
- [`../../../../papers/leanOSLF.pdf`](../../../../papers/leanOSLF.pdf) — this project's Lean 4 formalization writeup.
- [`../../../../papers/MeTTaIL.pdf`](../../../../papers/MeTTaIL.pdf) and [`F1R3FLY-io/mettail-rust`](https://github.com/F1R3FLY-io/mettail-rust) — the MeTTaIL specification/runtime-generation companion.
- [`../../../../papers/process-calculi.pdf`](../../../../papers/process-calculi.pdf) — the ρ/π/Petri-net instance writeups.
