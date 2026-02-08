import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.RhoCalculus.Engine

/-!
# Generic MeTTaIL Rewrite Engine

Language-parametric rewrite engine that applies the rewrite rules from any
`LanguageDef` to concrete terms. This is the generic counterpart of the
specialized `RhoCalculus/Engine.lean`.

The engine uses the generic pattern matcher from `Match.lean` to:
1. Match concrete terms against rule LHS patterns
2. Produce variable bindings
3. Apply bindings to rule RHS patterns to produce reducts

## Architecture

```
LanguageDef (from Syntax.lean)
    |
    | .rewrites : List RewriteRule
    v
matchPattern (from Match.lean)  -- match rule.left against term
    |
    | bindings : List (String x Pattern)
    v
applyBindings (from Match.lean) -- apply bindings to rule.right
    |
    v
reducts : List Pattern
```

## Key Functions

- `rewriteStep` — apply all rules from a LanguageDef to a term
- `rewriteWithContext` — also try rules on subterms (congruence)
- `rewriteToNormalForm` — iterate to normal form

## Validation

The executable tests below demonstrate that `rewriteStep rhoCalc` produces
the same results as the specialized `RhoCalculus.Engine.reduceStep` for
all test cases.
-/

namespace Mettapedia.OSLF.MeTTaIL.Engine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.RhoCalculus.Engine (patternToString)

instance : ToString Pattern := ⟨patternToString⟩

/-! ## Congruence: Apply rules to subterms -/

/-- Apply all rules to subterms of a collection (PAR/PAR_SET congruence).
    Returns all possible reducts where one element was rewritten. -/
def rewriteInCollection (lang : LanguageDef) (ct : CollType) (elems : List Pattern)
    (rest : Option String) : List Pattern :=
  elems.zipIdx.flatMap fun (elem, i) =>
    let subReducts := rewriteStep lang elem
    subReducts.map fun elem' =>
      .collection ct (elems.set i elem') rest

/-- Apply all rules to a term, including subterms (one level of congruence).
    This handles both top-level rewriting and PAR-like congruence. -/
def rewriteWithContext (lang : LanguageDef) (term : Pattern) : List Pattern :=
  -- Top-level rewrites
  let topReducts := rewriteStep lang term
  -- Subterm rewrites (congruence)
  let subReducts := match term with
    | .collection ct elems rest => rewriteInCollection lang ct elems rest
    | _ => []
  topReducts ++ subReducts

/-- Reduce to normal form with congruence (deterministic, with fuel). -/
def fullRewriteToNormalForm (lang : LanguageDef) (term : Pattern)
    (fuel : Nat := 1000) : Pattern :=
  match fuel with
  | 0 => term
  | fuel + 1 =>
    match rewriteWithContext lang term with
    | [] => term
    | q :: _ => fullRewriteToNormalForm lang q fuel

/-! ## Executable Tests: Generic Engine on rhoCalc -/

-- Helper: create common patterns (same as in RhoCalculus/Engine.lean)
private def pzero : Pattern := .apply "PZero" []
private def pdrop (n : Pattern) : Pattern := .apply "PDrop" [n]
private def nquote (p : Pattern) : Pattern := .apply "NQuote" [p]
private def poutput (n q : Pattern) : Pattern := .apply "POutput" [n, q]
private def pinput (n : Pattern) (body : Pattern) : Pattern :=
  .apply "PInput" [n, .lambda body]
private def ppar (elems : List Pattern) : Pattern :=
  .collection .hashBag elems none

-- Test 1: Generic COMM — same as specialized test
-- Generic COMM: {x!(0) | for(y<-x){y}} should reduce via rhoCalc COMM rule
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar [poutput x pzero, pinput x (.bvar 0)]
  let reducts := rewriteStep rhoCalc term
  IO.println s!"Generic COMM test: {term}"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Test 2: Generic COMM with congruence — nested reduction
-- Generic nested test: {*(@0) | x!(0)} — no top-level COMM, but DROP inside
#eval! do
  let term := ppar [pdrop (nquote pzero), poutput (.fvar "x") pzero]
  let topReducts := rewriteStep rhoCalc term
  let fullReducts := rewriteWithContext rhoCalc term
  IO.println s!"Generic nested test: {term}"
  IO.println s!"  top-level reducts ({topReducts.length}): {if topReducts.isEmpty then "none" else "unexpected"}"
  IO.println s!"  with congruence ({fullReducts.length}):"
  for r in fullReducts do
    IO.println s!"    -> {r}"

-- Test 3: Race — two inputs competing
-- Generic race: {x!(0) | for(y<-x){y} | for(z<-x){*z}} should have 2 reducts
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar [
    poutput x pzero,
    pinput x (.bvar 0),
    pinput x (pdrop (.bvar 0))
  ]
  let reducts := rewriteStep rhoCalc term
  IO.println s!"Generic race test: {term}"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Test 4: Multi-step using generic engine
-- Generic multi-step: {x!(*(@0)) | for(y<-x){*y}} should eventually reach 0
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar [poutput x (pdrop (nquote pzero)), pinput x (pdrop (.bvar 0))]
  IO.println s!"Generic multi-step test: {term}"
  let result := fullRewriteToNormalForm rhoCalc term
  IO.println s!"  normal form: {result}"

-- Test 5: Comparison — show generic and specialized give same results
-- Comparison: generic rewriteStep vs specialized reduceStep
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar [poutput x pzero, pinput x (.bvar 0)]
  let genericReducts := rewriteStep rhoCalc term
  let specialReducts := Mettapedia.OSLF.RhoCalculus.Engine.reduceStep term
  IO.println s!"Comparison test: {term}"
  IO.println s!"  generic  ({genericReducts.length}): {genericReducts.map toString}"
  IO.println s!"  special  ({specialReducts.length}): {specialReducts.map toString}"
  IO.println s!"  match: {genericReducts.length == specialReducts.length}"

/-! ## Agreement Tests: Generic vs Specialized

Systematic comparison of `rewriteStep rhoCalc` (generic) against
`RhoCalculus.Engine.reduceStep` (specialized) on all test cases.
The generic engine handles COMM and DROP at top level; the specialized
engine also handles PAR (congruence). We compare `rewriteWithContext`
(generic + congruence) against `reduceStep` (specialized). -/

-- Agreement test: run both engines on a term and check equality
private def checkAgreement (label : String) (term : Pattern) : IO Unit := do
  let genericReducts := (rewriteWithContext rhoCalc term).map toString
  let specialReducts := (Mettapedia.OSLF.RhoCalculus.Engine.reduceStep term).map toString
  -- Sort for order-independent comparison
  let gSorted := genericReducts.mergeSort (· < ·)
  let sSorted := specialReducts.mergeSort (· < ·)
  let agree := gSorted == sSorted
  IO.println s!"  {label}: generic={genericReducts.length} special={specialReducts.length} agree={agree}"
  unless agree do
    IO.println s!"    MISMATCH!"
    IO.println s!"    generic: {gSorted}"
    IO.println s!"    special: {sSorted}"

-- Agreement suite
#eval! do
  IO.println "=== Generic vs Specialized Agreement Suite ==="
  let x := Pattern.fvar "x"
  let y := Pattern.fvar "y"
  -- 1. Simple COMM
  checkAgreement "COMM" (ppar [poutput x pzero, pinput x (.bvar 0)])
  -- 2. Race (2 reducts)
  checkAgreement "Race" (ppar [poutput x pzero, pinput x (.bvar 0),
                                pinput x (pdrop (.bvar 0))])
  -- 3. DROP (top-level)
  checkAgreement "DROP" (pdrop (nquote pzero))
  -- 4. Normal form
  checkAgreement "NormalForm" pzero
  -- 5. Nested PAR (DROP inside bag)
  checkAgreement "NestedPAR" (ppar [pdrop (nquote pzero), poutput x pzero])
  -- 6. Pure bag, no redex
  checkAgreement "NoRedex" (ppar [poutput x pzero, poutput y pzero])
  -- 7. Empty bag
  checkAgreement "EmptyBag" (ppar [])
  -- 8. Single element bag
  checkAgreement "SingleBag" (ppar [pdrop (nquote pzero)])

end Mettapedia.OSLF.MeTTaIL.Engine
