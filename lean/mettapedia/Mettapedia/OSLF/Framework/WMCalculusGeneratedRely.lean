import Mettapedia.OSLF.Framework.GeneratedModality
import Mettapedia.OSLF.Framework.WMCalculusEncoding

/-!
# A generated rely modality for world-model evidence distribution

The authored `WM_EvidenceAdd` rule has a state-valued focus at the first
argument of `Extract`, with the query as its sole rely parameter. The
existing generic one-hole modality therefore applies at a non-root position
of this actual WM rule. This is a concrete rule-schema position, unlike the
positions in running terms recorded by `WMCalculusRedexPosition`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusGeneratedRely

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedModality
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding

/-- The left-hand side's first child is the revised state, so the query
appears in the context rather than the focused subterm. -/
def evidenceAddPosition : Position := [0]

theorem evidenceAdd_focus :
    subtermAt ruleEvidenceAdd.left evidenceAddPosition =
      some (pRevise (.fvar "W1") (.fvar "W2")) := by
  decide +kernel

theorem evidenceAdd_stable :
    StablePath ruleEvidenceAdd.left evidenceAddPosition = true := by
  decide +kernel

theorem evidenceAdd_relyVars :
    relyVars ruleEvidenceAdd.left evidenceAddPosition = ["q"] := by
  decide +kernel

theorem evidenceAdd_slotCount :
    slotCount ruleEvidenceAdd.left evidenceAddPosition = 2 := by
  decide +kernel

/-- Every instance of the authored distribution rule produces combined
evidence. No assumption on the query predicate is needed for introduction;
the operational premise still guards the modality's meaning. -/
theorem evidenceAdd_relyPossibly (base : BasePremiseEvaluator)
    (A : String → Pattern → Prop) :
    RelyPossibly base wmCoreLanguageDef ruleEvidenceAdd
      evidenceAddPosition A isCombined
        (pRevise (.fvar "W1") (.fvar "W2")) := by
  apply relyPossibly_intro evidenceAdd_stable evidenceAdd_focus
  intro bindings _ _
  unfold isCombined
  simp [Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings,
    ruleEvidenceAdd, pCombine]

private def specimenBindings : Bindings :=
  [("q", .fvar "x"), ("W2", .fvar "b"), ("W1", .fvar "a")]

/-- The modality's firing premise has an actual authored WM instance; the
previous introduction theorem is therefore not merely vacuous. -/
theorem specimen_fires :
    RuleFires (engineBasePremises RelationEnv.empty) wmCoreLanguageDef
      ruleEvidenceAdd specimenBindings := by
  have sourceEq :
      applyBindings specimenBindings ruleEvidenceAdd.left =
        encodeWM (.extract (.revise (.state "a") (.state "b")) (.query "x")) := by
    simp [specimenBindings, ruleEvidenceAdd, encodeWM, pExtract, pRevise,
      applyBindings]
  have targetEq :
      applyRuleBindings ruleEvidenceAdd specimenBindings =
        encodeWM (.combine
          (.extract (.state "a") (.query "x"))
          (.extract (.state "b") (.query "x"))) := by
    simp [specimenBindings, ruleEvidenceAdd, encodeWM, pExtract, pCombine,
      applyRuleBindings, applyBindings]
  rw [RuleFires, sourceEq, targetEq]
  exact wmStep_sound _ _
    (.evidence_add (.state "a") (.state "b") (.query "x"))

/-- With the sole rely parameter allowed, the generated modality supplies a
real one-step result at the authored focus. -/
theorem specimen_modal_step :
    ∃ source target : Pattern,
      plug (applyBindings specimenBindings ruleEvidenceAdd.left)
        evidenceAddPosition
        (applyBindings specimenBindings
          (pRevise (.fvar "W1") (.fvar "W2"))) = some source ∧
      Step (engineBasePremises RelationEnv.empty) wmCoreLanguageDef source target := by
  exact relyPossibly_step
    (evidenceAdd_relyPossibly (engineBasePremises RelationEnv.empty)
      (fun _ _ => True))
    (by simp [RelySatisfied]) specimen_fires

/-- The current generic rely guard only checks values supplied by a binding;
it does not require every rely name to be supplied. The empty binding is
therefore admissible for every predicate family. -/
theorem empty_rely_satisfied (A : String → Pattern → Prop) :
    RelySatisfied ruleEvidenceAdd evidenceAddPosition A [] := by
  simp [RelySatisfied, Bindings.lookup]

/-- The authored rule can still fire on its own uninstantiated variable
names. Thus a rely predicate alone does not force coverage of the query slot. -/
theorem empty_bindings_fire :
    RuleFires (engineBasePremises RelationEnv.empty) wmCoreLanguageDef
      ruleEvidenceAdd [] := by
  have sourceEq :
      applyBindings ([] : Bindings) ruleEvidenceAdd.left =
        encodeWM (.extract
          (.revise (.state "W1") (.state "W2")) (.query "q")) := by
    simp [ruleEvidenceAdd, encodeWM, pExtract, pRevise, applyBindings]
  have targetEq :
      applyRuleBindings ruleEvidenceAdd ([] : Bindings) =
        encodeWM (.combine
          (.extract (.state "W1") (.query "q"))
          (.extract (.state "W2") (.query "q"))) := by
    simp [ruleEvidenceAdd, encodeWM, pExtract, pCombine,
      applyRuleBindings, applyBindings]
  rw [RuleFires, sourceEq, targetEq]
  exact wmStep_sound _ _
    (.evidence_add (.state "W1") (.state "W2") (.query "q"))

/-- In particular the generated modality with an impossible result is not
made true by making the query rely predicate impossible: the empty binding
still fires. This is a boundary of this pattern-level guard, not a claim
about the separately scoped presentation. -/
theorem impossible_result_rejected_for_every_rely
    (A : String → Pattern → Prop) :
    ¬ RelyPossibly (engineBasePremises RelationEnv.empty)
      wmCoreLanguageDef ruleEvidenceAdd evidenceAddPosition A
      (fun _ => False) (pRevise (.fvar "W1") (.fvar "W2")) := by
  intro inhabitant
  obtain ⟨_, _, _, _, impossible⟩ :=
    inhabitant [] (empty_rely_satisfied A) empty_bindings_fire
  exact impossible

end Mettapedia.OSLF.Framework.WMCalculusGeneratedRely
