import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.Languages.GF.Typing
import Mettapedia.Languages.GF.VisibleLayer
import Mettapedia.Languages.GF.VisibleLayerGFInstance
import Mettapedia.Languages.GF.StoreToLogicalForm
import Mettapedia.Languages.GF.WorldModelVisibleBridge
import Mettapedia.OSLF.QuantifiedFormula2

/-!
# End-to-End Example: "Every man walks"

This module threads a single sentence through the entire GF → OSLF → Evidence
pipeline, proving correctness at each stage:

1. **GF tree**: `PredVP(DetCN(every_Det, UseN(man_N)), UseV(walk_V))`
2. **GF → Pattern**: `gfAbstractToPattern` converts to OSLF pattern
3. **V1 step**: NP replacement produces `⊛NPVar(q1)` + store atom
4. **Store → QFormula2**: Assembly yields `∀q1. man_N(q1) → walk_V(q1)`
5. **Evidence structure**: `qsemE2` unfolds to `⨅ d, I "man_N" [d] p ⇨ I "walk_V" [d] p`

This is the first worked example demonstrating the complete horizontal wiring.
-/

namespace Mettapedia.Languages.GF.Examples.EveryManWalks

open Mettapedia.Languages.GF.Core
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.Typing
open Mettapedia.Languages.GF.VisibleLayer
open Mettapedia.Languages.GF.VisibleLayerGFInstance
open Mettapedia.Languages.GF.StoreToLogicalForm
open Mettapedia.Languages.GF.WorldModelVisibleBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.QuantifiedFormula2

/-! ## Stage 1: GF Abstract Syntax Tree -/

/-- "Every man walks" as a GF abstract syntax tree. -/
def everyManWalks : AbstractNode :=
  mkApp2 "PredVP" "NP" "VP" "Cl"
    (mkApp2 "DetCN" "Det" "CN" "NP"
      (mkLeaf "every_Det" "Det")
      (mkApp1 "UseN" "N" "CN" (mkLeaf "man_N" "N")))
    (mkApp1 "UseV" "V" "VP" (mkLeaf "walk_V" "V"))

/-! ## Stage 2: GF → OSLF Pattern -/

/-- The OSLF pattern representation of "every man walks". -/
def emw_pattern : Pattern := gfAbstractToPattern everyManWalks

/-- Concrete value of the pattern (verified by computation). -/
theorem emw_pattern_val : emw_pattern =
    .apply "PredVP"
      [.apply "DetCN" [.fvar "every_Det", .apply "UseN" [.fvar "man_N"]],
       .apply "UseV" [.fvar "walk_V"]] := by
  simp [emw_pattern, everyManWalks, mkApp2, mkApp1, mkLeaf]

/-! ## Stage 3: V1 — Quantifier Introduction -/

/-- Initial grammar state: the pattern with empty store. -/
def emw_state0 : GrammarState := ⟨emw_pattern, ∅⟩

/-- The term after V1 replaces the subject NP with ⊛NPVar(q1). -/
def emw_afterV1_term : Pattern :=
  .apply "PredVP" [npVar "q1", .apply "UseV" [.fvar "walk_V"]]

/-- V1 NP replacement finds the DetCN and replaces it. -/
theorem emw_V1_replacement :
    replaceFirstNP emw_pattern "q1" = some emw_afterV1_term := by
  simp [emw_pattern, everyManWalks, mkApp2, mkApp1, mkLeaf,
        emw_afterV1_term, replaceFirstNP, replaceFirstNPInList, isNPConstructor, npVar]

/-- The determiner and restrictor extracted from the NP. -/
def emw_det : Pattern := .fvar "every_Det"
def emw_restr : Pattern := .apply "UseN" [.fvar "man_N"]

/-- Grammar state after V1: NP replaced, quantifier recorded in store. -/
def emw_state1 : GrammarState :=
  ⟨emw_afterV1_term, {StoreAtom.quant "q1" emw_det emw_restr}⟩

/-- V1 is a valid visible step from state0 to state1. -/
theorem emw_V1_step : VisibleStep gfVisibleCfg emw_state0 emw_state1 := by
  have hterm : gfVisibleCfg.npReplacer.replaceNPWithVar emw_state0.term "q1" =
      some emw_afterV1_term := by
    simp [gfVisibleCfg, gfNPReplacer, emw_state0]
    exact emw_V1_replacement
  have hfresh : ∀ d r, StoreAtom.quant "q1" d r ∉ emw_state0.store := by
    simp [emw_state0]
  exact VisibleStep.quantIntro "q1" emw_det emw_restr emw_state0 hfresh
    emw_afterV1_term hterm

/-! ## Stage 4: Store → QFormula2

The store has `quant "q1" every_Det (UseN man_N)`, and the term has
`PredVP(⊛NPVar(q1), UseV(walk_V))`. Assembly produces:

  ∀q1. man_N(q1) → walk_V(q1)
-/

/-- The expected logical form: "for every q1, if q1 is a man then q1 walks." -/
def emw_formula : QFormula2 :=
  .qforall "q1" (.qimp (.qatom ⟨"man_N", [.var "q1"]⟩)
                        (.qatom ⟨"walk_V", [.var "q1"]⟩))

/-- Body extraction: the term produces `walk_V(q1)`. -/
theorem emw_body : termToBody emw_afterV1_term =
    .qatom ⟨"walk_V", [.var "q1"]⟩ := rfl

/-- Full assembly: single-quantifier wrapping produces the expected formula. -/
theorem emw_assembly :
    storeToQFormula2_ordered
      (singleQuantEntry "q1" emw_det emw_restr)
      emw_state1 = emw_formula := rfl

/-- Auto-assembly agrees with manual assembly: `storeToQFormula2` (the full
    noncomputable pipeline) produces the same formula as the manual `emw_formula`.

    Proof chains `storeToQFormula2_single_spec` (auto = ordered) with
    `emw_assembly` (ordered = manual). -/
theorem emw_auto_assembly :
    storeToQFormula2 emw_state1 = emw_formula :=
  (storeToQFormula2_single_spec "q1" emw_det emw_restr emw_afterV1_term).trans emw_assembly

/-! ## Stage 5: Closedness -/

/-- The formula ∀q1. man_N(q1) → walk_V(q1) is closed (no free variables). -/
theorem emw_closed : closedQF2 emw_formula := by
  simp [closedQF2, emw_formula, freeVarsQF2, freeVarsAtom,
        freeVarsTerms, freeVarsTerm]

/-! ## Stage 6: Evidence Structure

Evaluating the formula under `qsemE2` with empty environment unfolds to
an infimum over the domain: for each domain element d, the evidence that
d is a man implies the evidence that d walks. -/

/-- The evidence value of "every man walks" is the infimum of
    `man_N(d) ⇨ walk_V(d)` over all domain elements d.

    This is the quantitative generalization of the classical semantics
    `⟦∀x. man(x) → walks(x)⟧ = ⋀ₓ (man(x) → walks(x))`. -/
theorem emw_evidence_structure
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem) (Dom : Domain2) :
    qsemE2 R I Dom emptyEnv2 emw_formula emw_afterV1_term =
    ⨅ (d : Dom), (I "man_N" [d.val] emw_afterV1_term ⇨
                   I "walk_V" [d.val] emw_afterV1_term) := by
  simp only [emw_formula, qsemE2, extendEnv2, evalTerms, evalTerm]
  rfl

/-! ## Summary

The complete pipeline for "every man walks":

```
  GF Tree:       PredVP(DetCN(every_Det, UseN(man_N)), UseV(walk_V))
       ↓ gfAbstractToPattern
  Pattern:       .apply "PredVP" [.apply "DetCN" [...], .apply "UseV" [...]]
       ↓ V1 (quantifier intro)
  GrammarState:  term = PredVP(⊛NPVar(q1), UseV(walk_V))
                 store = {quant "q1" every_Det (UseN man_N)}
       ↓ storeToQFormula2_ordered
  QFormula2:     ∀q1. man_N(q1) → walk_V(q1)
       ↓ qsemE2 R I Dom emptyEnv2
  Evidence:      ⨅ d : Dom, I "man_N" [d] p ⇨ I "walk_V" [d] p
```

All steps proven; no proof gaps.
-/

end Mettapedia.Languages.GF.Examples.EveryManWalks
