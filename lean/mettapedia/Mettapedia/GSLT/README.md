# GSLT in Mettapedia

`GSLT` here means **Graph-Structured Lambda Theories**: a categorical way to
specify languages (contexts/substitutions/equality/reduction) so that OSLF can
derive modal/native type structure from operational semantics.

This README answers:
1. What is a GSLT, precisely?
2. What spec do I need to feed a programming language to OSLF?

## Where the Formal Spec Lives

- Top-level module:
  - `Mettapedia/GSLT.lean`
- Core categorical objects:
  - `Mettapedia/GSLT/Core/LambdaTheoryCategory.lean`
  - `Mettapedia/GSLT/Core/ChangeOfBase.lean`
- Presheaf/topos layer:
  - `Mettapedia/GSLT/Topos/SubobjectClassifier.lean`
  - `Mettapedia/GSLT/Topos/PredicateFibration.lean`

## 1) Category-Theoretic Definition (Core GSLT)

In this codebase, the core object is a lambda-theory with equality and
fibration structure:

1. `SubobjectFibration C`
  - `Sub : C -> Type`
  - each fiber `Sub X` is a `Frame` (complete Heyting algebra)
2. `LambdaTheoryWithEquality`
  - object type `Obj`
  - category structure on `Obj`
  - cartesian monoidal + monoidal closed + finite limits
  - attached `SubobjectFibration`
3. `ChangeOfBase` on that fibration
  - pullback `f*`
  - direct image `exists_f`
  - universal image `forall_f`
  - adjunctions: `exists_f ⊣ f* ⊣ forall_f`
4. Beck-Chevalley condition
  - substitution/quantification compatibility on pullback squares
5. `LambdaTheoryWithFibration`
  - bundles lambda-theory + change-of-base + Beck-Chevalley

Concrete names:
- `SubobjectFibration`:
  `Mettapedia/GSLT/Core/LambdaTheoryCategory.lean`
- `LambdaTheoryWithEquality`:
  `Mettapedia/GSLT/Core/LambdaTheoryCategory.lean`
- `ChangeOfBase`, `BeckChevalley`, `LambdaTheoryWithFibration`:
  `Mettapedia/GSLT/Core/ChangeOfBase.lean`

## 2) Grammar/Operational Interface Used by OSLF Today

For feeding a language into OSLF now, use the operational `LanguageDef`
front-end (MeTTaIL syntax) in:

- `Mettapedia/OSLF/MeTTaIL/Syntax.lean`

### 2.1 Type and Term Grammar

- `TypeExpr`:
  - `base String`
  - `arrow TypeExpr TypeExpr`
  - `multiBinder TypeExpr`
  - `collection CollType TypeExpr`
- `CollType`:
  - `vec | hashBag | hashSet`
- `GrammarRule`:
  - `label : String`
  - `category : String`
  - `params : List TermParam`
  - `syntaxPattern : List SyntaxItem`
- `TermParam`:
  - `simple name ty`
  - `abstraction name ty`
  - `multiAbstraction name ty`

### 2.2 Pattern Language for Equations/Rewrites

- `Pattern` constructors:
  - `bvar Nat` (bound var, de Bruijn index)
  - `fvar String` (free/meta var)
  - `apply String (List Pattern)`
  - `lambda Pattern`
  - `multiLambda Nat Pattern`
  - `subst Pattern Pattern`
  - `collection CollType (List Pattern) (Option String)` (rest-variable optional)

### 2.3 Premises

- `Premise`:
  - `freshness : FreshnessCondition -> Premise`
  - `congruence : Pattern -> Pattern -> Premise`
  - `relationQuery : String -> List Pattern -> Premise`

### 2.4 Full Language Spec

- `LanguageDef` fields:
  - `name : String`
  - `types : List String`
  - `terms : List GrammarRule`
  - `equations : List Equation`
  - `rewrites : List RewriteRule`
  - `congruenceCollections : List CollType` (default all three)

This is the spec you provide to the OSLF synthesis pipeline.

## 3) Exact OSLF Pipeline Entry Points

From `Mettapedia/OSLF/Framework/TypeSynthesis.lean`:

1. `langRewriteSystemUsing` / `langRewriteSystem`
2. `langDiamondUsing` / `langDiamond`
3. `langBoxUsing` / `langBox`
4. `langGaloisUsing` / `langGalois`
5. `langOSLF`

So the practical contract is:

`LanguageDef (+ optional RelationEnv for relationQuery premises) -> langOSLF`

## 4) What You Must Provide for a New PL

If you want OSLF types for your language, provide:

1. Sorts (`types`) and designate a process sort (default `"Proc"`).
2. Constructors (`terms`) for your syntax/state representation.
3. Equations (`equations`) for structural equality/normalization.
4. Rewrite rules (`rewrites`) for one-step operational semantics.
5. Premises (`Premise`) where needed.
6. Optional `RelationEnv` implementation for external relations used by
   `relationQuery`.

Minimal Lean workflow:

```lean
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.Engine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Engine

def myLang : LanguageDef := { ... }
def myRelEnv : RelationEnv := RelationEnv.empty -- or custom

def myOSLF := langOSLF myLang "Proc"
def myDiamond := langDiamondUsing myRelEnv myLang
def myBox := langBoxUsing myRelEnv myLang
```

## 5) Is This "Any Language"?

Yes for any language you can present as small-step rewrites over a structured
term/state syntax (plus premise queries/oracles where needed).

Typical encoding pattern:
- functional language: term-reduction rules
- imperative language: rewrite over machine states `(pc, store, heap, ...)`
- concurrent language: rewrite over process networks/messages

## 6) Practical Demos to Copy

- TinyML instance:
  - `Mettapedia/OSLF/Framework/TinyMLInstance.lean`
- MeTTa minimal/full instances:
  - `Mettapedia/OSLF/Framework/MeTTaMinimalInstance.lean`
  - `Mettapedia/OSLF/Framework/MeTTaFullInstance.lean`
- Premise-aware execution:
  - `Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean`
- Lean-to-Rust roundtrip smoke path:
  - `Mettapedia/OSLF/Tools/ExportTinyMLSmokeRoundTrip.lean`
  - <https://github.com/zariuq/mettail-rust/tree/feature/lean-language-export-tinyml-smoke>

## 7) Relation to Full Presheaf/Topos GSLT

The `LanguageDef` front-end is operational and executable. The full categorical
stack (subobject classifier, predicate fibration, Beck-Chevalley) is in the
`Mettapedia/GSLT/Topos/*` files and is the semantic/categorical foundation.

Use both together:
- operational ingestion and execution via `LanguageDef`
- categorical guarantees and lifted semantics via GSLT/topos modules
