import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.Languages.GF.Typing
import Mettapedia.Languages.GF.VisibleLayer
import Mettapedia.Languages.GF.VisibleLayerGFInstance
import Mettapedia.Languages.GF.StoreToLogicalForm
import Mettapedia.Languages.GF.WorldModelVisibleBridge
import Mettapedia.OSLF.QuantifiedFormula2

/-!
# End-to-End Example: "Every man loves a woman" (Scope Ambiguity)

This module demonstrates the complete GF → OSLF → Evidence pipeline for a
sentence with **two quantifiers**, producing two genuinely distinct readings
via V2 scope choice:

- **Surface scope**: `∀q1. man(q1) → ∃q2. woman(q2) ∧ loves(q1,q2)`
  "For every man there exists (possibly different) a woman he loves"
- **Inverse scope**: `∃q2. woman(q2) ∧ ∀q1. man(q1) → loves(q1,q2)`
  "There exists a single woman that every man loves"

The two readings are ordered: inverse ≤ surface (by `scope_ordering_qsemE2`).

## Pipeline

1. **GF tree**: `PredVP(DetCN(every_Det, UseN(man_N)), ComplSlash(SlashV2a(love_V2), DetCN(someSg_Det, UseN(woman_N))))`
2. **V1 × 2**: Two NP replacements (q1 for subject, q2 for object)
3. **V2**: Scope choice — surface `scope q1 q2` or inverse `scope q2 q1`
4. **Store → QFormula2**: Two distinct logical forms
5. **Evidence ordering**: `∃∀ ≤ ∀∃`
-/

namespace Mettapedia.Languages.GF.Examples.ScopeAmbiguity

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

/-- "Every man loves a woman" as a GF abstract syntax tree. -/
def everyManLovesAWoman : AbstractNode :=
  mkApp2 "PredVP" "NP" "VP" "Cl"
    (mkApp2 "DetCN" "Det" "CN" "NP"
      (mkLeaf "every_Det" "Det")
      (mkApp1 "UseN" "N" "CN" (mkLeaf "man_N" "N")))
    (mkApp2 "ComplSlash" "VPSlash" "NP" "VP"
      (mkApp1 "SlashV2a" "V2" "VPSlash" (mkLeaf "love_V2" "V2"))
      (mkApp2 "DetCN" "Det" "CN" "NP"
        (mkLeaf "someSg_Det" "Det")
        (mkApp1 "UseN" "N" "CN" (mkLeaf "woman_N" "N"))))

/-! ## Stage 2: GF → Pattern -/

def emla_pattern : Pattern := gfAbstractToPattern everyManLovesAWoman

theorem emla_pattern_val : emla_pattern =
    .apply "PredVP"
      [.apply "DetCN" [.fvar "every_Det", .apply "UseN" [.fvar "man_N"]],
       .apply "ComplSlash"
         [.apply "SlashV2a" [.fvar "love_V2"],
          .apply "DetCN" [.fvar "someSg_Det", .apply "UseN" [.fvar "woman_N"]]]] := by
  simp [emla_pattern, everyManLovesAWoman, mkApp2, mkApp1, mkLeaf]

/-! ## Stage 3: V1 × 2 — Two Quantifier Introductions -/

def emla_state0 : GrammarState := ⟨emla_pattern, ∅⟩

/-- After first V1: subject NP → ⊛NPVar(q1) -/
def emla_afterV1a : Pattern :=
  .apply "PredVP"
    [npVar "q1",
     .apply "ComplSlash"
       [.apply "SlashV2a" [.fvar "love_V2"],
        .apply "DetCN" [.fvar "someSg_Det", .apply "UseN" [.fvar "woman_N"]]]]

theorem emla_V1a_replacement :
    replaceFirstNP emla_pattern "q1" = some emla_afterV1a := by
  simp [emla_pattern, everyManLovesAWoman, mkApp2, mkApp1, mkLeaf, emla_afterV1a,
        replaceFirstNP, replaceFirstNPInList, isNPConstructor, npVar]

/-- Store after first V1 -/
def emla_det1 : Pattern := .fvar "every_Det"
def emla_restr1 : Pattern := .apply "UseN" [.fvar "man_N"]

def emla_state1 : GrammarState :=
  ⟨emla_afterV1a, {StoreAtom.quant "q1" emla_det1 emla_restr1}⟩

/-- First V1 is a valid visible step. -/
theorem emla_V1a_step : VisibleStep gfVisibleCfg emla_state0 emla_state1 := by
  have hterm : gfVisibleCfg.npReplacer.replaceNPWithVar emla_state0.term "q1" =
      some emla_afterV1a := by
    simp [gfVisibleCfg, gfNPReplacer, emla_state0]
    exact emla_V1a_replacement
  have hfresh : ∀ d r, StoreAtom.quant "q1" d r ∉ emla_state0.store := by
    simp [emla_state0]
  exact VisibleStep.quantIntro "q1" emla_det1 emla_restr1 emla_state0 hfresh
    emla_afterV1a hterm

/-- After second V1: object NP → ⊛NPVar(q2) -/
def emla_afterV1b : Pattern :=
  .apply "PredVP"
    [npVar "q1",
     .apply "ComplSlash"
       [.apply "SlashV2a" [.fvar "love_V2"],
        npVar "q2"]]

theorem emla_V1b_replacement :
    replaceFirstNP emla_afterV1a "q2" = some emla_afterV1b := by
  simp [emla_afterV1a, emla_afterV1b, npVar,
        replaceFirstNP, replaceFirstNPInList, isNPConstructor]

def emla_det2 : Pattern := .fvar "someSg_Det"
def emla_restr2 : Pattern := .apply "UseN" [.fvar "woman_N"]

def emla_state2 : GrammarState :=
  ⟨emla_afterV1b,
   {StoreAtom.quant "q1" emla_det1 emla_restr1} +
   {StoreAtom.quant "q2" emla_det2 emla_restr2}⟩

/-- Second V1 is a valid visible step from state1. -/
theorem emla_V1b_step : VisibleStep gfVisibleCfg emla_state1 emla_state2 := by
  have hterm : gfVisibleCfg.npReplacer.replaceNPWithVar emla_state1.term "q2" =
      some emla_afterV1b := by
    simp [gfVisibleCfg, gfNPReplacer, emla_state1]
    exact emla_V1b_replacement
  have hfresh : ∀ d r, StoreAtom.quant "q2" d r ∉ emla_state1.store := by
    simp [emla_state1, emla_det1, emla_restr1]
  exact VisibleStep.quantIntro "q2" emla_det2 emla_restr2 emla_state1 hfresh
    emla_afterV1b hterm

/-! ## Stage 4: V2 — Scope Choice (Nondeterministic)

Two quantifiers q1, q2 are in the store with no relative ordering.
V2 allows either `scope q1 q2` (surface) or `scope q2 q1` (inverse). -/

/-- Both scope orderings are reachable from state2. -/
theorem emla_scope_nondet :
    VisibleStep gfVisibleCfg emla_state2
      ⟨emla_state2.term, emla_state2.store + {StoreAtom.scope "q1" "q2"}⟩ ∧
    VisibleStep gfVisibleCfg emla_state2
      ⟨emla_state2.term, emla_state2.store + {StoreAtom.scope "q2" "q1"}⟩ := by
  constructor
  · apply VisibleStep.scopeChoice "q1" "q2" emla_state2
    · decide
    · exact ⟨emla_det1, emla_restr1, Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _))⟩
    · exact ⟨emla_det2, emla_restr2, Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))⟩
    · simp [emla_state2, emla_det1, emla_restr1, emla_det2, emla_restr2]
  · apply VisibleStep.scopeChoice "q2" "q1" emla_state2
    · decide
    · exact ⟨emla_det2, emla_restr2, Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))⟩
    · exact ⟨emla_det1, emla_restr1, Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _))⟩
    · simp [emla_state2, emla_det1, emla_restr1, emla_det2, emla_restr2]

/-! ## Stage 5: Store → QFormula2 — Two Readings -/

/-- Body: love_V2(q1, q2) -/
theorem emla_body : termToBody emla_afterV1b =
    .qatom ⟨"love_V2", [.var "q1", .var "q2"]⟩ := rfl

/-- Surface scope: ∀q1. man(q1) → ∃q2. woman(q2) ∧ loves(q1,q2) -/
def surfaceScope : QFormula2 :=
  .qforall "q1" (.qimp (.qatom ⟨"man_N", [.var "q1"]⟩)
    (.qexists "q2" (.qand (.qatom ⟨"woman_N", [.var "q2"]⟩)
                          (.qatom ⟨"love_V2", [.var "q1", .var "q2"]⟩))))

/-- Inverse scope: ∃q2. woman(q2) ∧ ∀q1. man(q1) → loves(q1,q2) -/
def inverseScope : QFormula2 :=
  .qexists "q2" (.qand (.qatom ⟨"woman_N", [.var "q2"]⟩)
    (.qforall "q1" (.qimp (.qatom ⟨"man_N", [.var "q1"]⟩)
                          (.qatom ⟨"love_V2", [.var "q1", .var "q2"]⟩))))

/-- Surface scope assembly: q1 outermost (surface order). -/
theorem emla_surface_assembly :
    storeToQFormula2_ordered
      (twoQuantEntries "q1" emla_det1 emla_restr1
                        "q2" emla_det2 emla_restr2 true)
      emla_state2 = surfaceScope := rfl

/-- Inverse scope assembly: q2 outermost (inverse order). -/
theorem emla_inverse_assembly :
    storeToQFormula2_ordered
      (twoQuantEntries "q1" emla_det1 emla_restr1
                        "q2" emla_det2 emla_restr2 false)
      emla_state2 = inverseScope := rfl

/-- Grammar state after V2 surface scope choice: `scope q1 q2` added. -/
def emla_state3_surface : GrammarState :=
  ⟨emla_afterV1b, emla_state2.store + {StoreAtom.scope "q1" "q2"}⟩

/-- Grammar state after V2 inverse scope choice: `scope q2 q1` added. -/
def emla_state3_inverse : GrammarState :=
  ⟨emla_afterV1b, emla_state2.store + {StoreAtom.scope "q2" "q1"}⟩

/-- Auto-assembly (surface): `storeToQFormula2` on the surface-scoped state
    agrees with the manual `surfaceScope` formula.

    Proof: rewrite store to literal form, apply `scopeOrderedQuants_two_surface_spec`,
    then reduce `assembleFromQuants`. -/
theorem emla_surface_auto_assembly :
    storeToQFormula2 emla_state3_surface = surfaceScope := by
  simp only [storeToQFormula2, emla_state3_surface, emla_state2,
             emla_afterV1b, emla_det1, emla_restr1, emla_det2, emla_restr2]
  -- Store is {quant q1 ...} + {quant q2 ...} + {scope q1 q2}
  -- Need: scopeOrderedQuants store = [(q1,...), (q2,...)]
  have hstore : ({StoreAtom.quant "q1" (.fvar "every_Det") (.apply "UseN" [.fvar "man_N"])} +
      {StoreAtom.quant "q2" (.fvar "someSg_Det") (.apply "UseN" [.fvar "woman_N"])} +
      ({StoreAtom.scope "q1" "q2"} : Multiset StoreAtom)) =
    ({StoreAtom.quant "q1" (.fvar "every_Det") (.apply "UseN" [.fvar "man_N"]),
      StoreAtom.quant "q2" (.fvar "someSg_Det") (.apply "UseN" [.fvar "woman_N"]),
      StoreAtom.scope "q1" "q2"} : Multiset StoreAtom) := by
    simp [Multiset.singleton_add, Multiset.cons_add]
  rw [hstore]
  rw [scopeOrderedQuants_two_surface_spec
    "q1" (.fvar "every_Det") (.apply "UseN" [.fvar "man_N"])
    "q2" (.fvar "someSg_Det") (.apply "UseN" [.fvar "woman_N"])
    (by simp) (by simp)]
  rfl

/-- Auto-assembly (inverse): `storeToQFormula2` on the inverse-scoped state
    agrees with the manual `inverseScope` formula. -/
theorem emla_inverse_auto_assembly :
    storeToQFormula2 emla_state3_inverse = inverseScope := by
  simp only [storeToQFormula2, emla_state3_inverse, emla_state2,
             emla_afterV1b, emla_det1, emla_restr1, emla_det2, emla_restr2]
  have hstore : ({StoreAtom.quant "q1" (.fvar "every_Det") (.apply "UseN" [.fvar "man_N"])} +
      {StoreAtom.quant "q2" (.fvar "someSg_Det") (.apply "UseN" [.fvar "woman_N"])} +
      ({StoreAtom.scope "q2" "q1"} : Multiset StoreAtom)) =
    ({StoreAtom.quant "q2" (.fvar "someSg_Det") (.apply "UseN" [.fvar "woman_N"]),
      StoreAtom.quant "q1" (.fvar "every_Det") (.apply "UseN" [.fvar "man_N"]),
      StoreAtom.scope "q2" "q1"} : Multiset StoreAtom) := by
    simp [Multiset.singleton_add, Multiset.cons_add]
    exact Multiset.cons_swap _ _ _
  rw [hstore]
  rw [scopeOrderedQuants_two_surface_spec
    "q2" (.fvar "someSg_Det") (.apply "UseN" [.fvar "woman_N"])
    "q1" (.fvar "every_Det") (.apply "UseN" [.fvar "man_N"])
    (by simp) (by simp)]
  rfl

/-! ## Stage 6: Closedness -/

theorem surfaceScope_closed : closedQF2 surfaceScope := by
  simp [closedQF2, surfaceScope, freeVarsQF2, freeVarsAtom,
        freeVarsTerms, freeVarsTerm]

theorem inverseScope_closed : closedQF2 inverseScope := by
  simp [closedQF2, inverseScope, freeVarsQF2, freeVarsAtom,
        freeVarsTerms, freeVarsTerm]

/-! ## Stage 7: Evidence Structure -/

/-- Surface scope unfolds to ⨅q1. (man(q1) ⇨ ⨆q2. (woman(q2) ⊓ love(q1,q2))). -/
theorem surfaceScope_evidence
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem) (Dom : Domain2) :
    qsemE2 R I Dom emptyEnv2 surfaceScope emla_afterV1b =
    ⨅ (d1 : Dom), (I "man_N" [d1.val] emla_afterV1b ⇨
      ⨆ (d2 : Dom), (I "woman_N" [d2.val] emla_afterV1b ⊓
                      I "love_V2" [d1.val, d2.val] emla_afterV1b)) := by
  simp only [surfaceScope, qsemE2, extendEnv2, evalTerms, evalTerm]
  rfl

/-- Inverse scope unfolds to ⨆q2. (woman(q2) ⊓ ⨅q1. (man(q1) ⇨ love(q1,q2))). -/
theorem inverseScope_evidence
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem) (Dom : Domain2) :
    qsemE2 R I Dom emptyEnv2 inverseScope emla_afterV1b =
    ⨆ (d2 : Dom), (I "woman_N" [d2.val] emla_afterV1b ⊓
      ⨅ (d1 : Dom), (I "man_N" [d1.val] emla_afterV1b ⇨
                      I "love_V2" [d1.val, d2.val] emla_afterV1b)) := by
  simp only [inverseScope, qsemE2, extendEnv2, evalTerms, evalTerm]
  rfl

/-! ## Stage 8: Scope Ordering — ∃∀ ≤ ∀∃

The inverse scope (∃∀) implies the surface scope (∀∃). This is a fundamental
semantic fact: if there exists a specific woman that every man loves, then
for every man there exists some woman he loves. -/

/-- Scope ordering for the body formula: love_V2(q1,q2). -/
theorem emla_scope_ordering
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem) (Dom : Domain2)
    (env : VarEnv2) (p : Pattern) :
    qsemE2 R I Dom env
      (.qexists "q2" (.qforall "q1"
        (.qimp (.qatom ⟨"man_N", [.var "q1"]⟩)
          (.qand (.qatom ⟨"woman_N", [.var "q2"]⟩)
                 (.qatom ⟨"love_V2", [.var "q1", .var "q2"]⟩))))) p ≤
    qsemE2 R I Dom env
      (.qforall "q1" (.qexists "q2"
        (.qimp (.qatom ⟨"man_N", [.var "q1"]⟩)
          (.qand (.qatom ⟨"woman_N", [.var "q2"]⟩)
                 (.qatom ⟨"love_V2", [.var "q1", .var "q2"]⟩))))) p :=
  scope_ordering_qsemE2 R I Dom env (by decide) _ p

/-! ## Summary

```
  GF Tree:       PredVP(DetCN(every_Det, UseN(man_N)),
                        ComplSlash(SlashV2a(love_V2), DetCN(someSg_Det, UseN(woman_N))))
       ↓ gfAbstractToPattern
  Pattern:       .apply "PredVP" [.apply "DetCN" [...], .apply "ComplSlash" [...]]
       ↓ V1 (q1: subject)
  State1:        term = PredVP(⊛NPVar(q1), ComplSlash(SlashV2a(love_V2), DetCN(...)))
                 store = {quant q1 every_Det (UseN man_N)}
       ↓ V1 (q2: object)
  State2:        term = PredVP(⊛NPVar(q1), ComplSlash(SlashV2a(love_V2), ⊛NPVar(q2)))
                 store = {quant q1 every_Det (UseN man_N), quant q2 someSg_Det (UseN woman_N)}
       ↓ V2 (scope choice — nondeterministic)
  Surface:       scope q1 q2 → ∀q1. man(q1) → ∃q2. woman(q2) ∧ loves(q1,q2)
  Inverse:       scope q2 q1 → ∃q2. woman(q2) ∧ ∀q1. man(q1) → loves(q1,q2)
       ↓ Evidence
  Ordering:      ∃∀ ≤ ∀∃ (inverse implies surface)
```

All steps proven; no proof gaps.
-/

end Mettapedia.Languages.GF.Examples.ScopeAmbiguity
