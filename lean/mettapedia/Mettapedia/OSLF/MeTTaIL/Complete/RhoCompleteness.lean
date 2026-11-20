import Mettapedia.OSLF.MeTTaIL.Complete.RhoWrappers
import Mettapedia.OSLF.MeTTaIL.Complete.RhoReference
import Mettapedia.OSLF.MeTTaIL.GeneralRhoDepthOne
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-!
# Every step of the established rho calculus is a step of the model

The established rho GSLT (`LanguageDefGSLT.rhoLanguageDefGSLT`) has closed, well-sorted, quotation-sealed
processes as terms, the canonical equations as its equality and the authored COMM and parallel descent as
its rewrites. Each of its steps is a step of the plan modulo the declared collection algebra and the name
equation (`established_step`), with a structurally congruent result: the authored step on its redex is
matched by COMM on the canonical form (`CanonicalStepperCompleteness`), COMM there is a valid receipt of
the plan at the root, and the source is congruent to that canonical form, hence equal in the model.

So every closed process reachable in the established calculus is explored, up to structural congruence
(`established_explored`).

Conversely, object terms equal in the model are structurally congruent (`sc_of_modelEquiv`), and every
step of the model from an object term is a reduction of the reference rho calculus
(`model_step_reduces`): a model step fires a primitive receipt between two model equalities.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.RhoCompleteness

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission CanonicalBags
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus (StructuralCongruence)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize canonicalize_sound
  structuralCongruence_of_canonicalize_eq canonicalize_isCanonical)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping (canonicalize_procWellSorted
  canonicalize_binderSafeAt)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open RhoQuoteDrop (presentation)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (HashSetFree)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary (rhoProcWellSorted_hashSetFree)

/-- The plan's model, at closed processes. -/
abbrev model : Mettapedia.GSLT.GSLT :=
  WrapperCoherence.gslt GeneralRho.Standard.plan [] (.base "Proc") presentation

/-- A receipt of the depth-one plan is a receipt of the standard plan: both have the same rule and
environment, and the depth-one plan fires only at the root. -/
theorem depthOne_receipt_standard {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid GeneralRho.DepthOne.plan [] (.base "Proc") source) :
    receipt.Valid GeneralRho.Standard.plan [] (.base "Proc") source := by
  obtain ⟨⟨declared, licensed⟩, firing, accepted, filled, typed⟩ := valid
  obtain ⟨_, _, siteRoot⟩ := GeneralRho.DepthOne.job_root ⟨declared, licensed⟩
  have sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language
      GeneralRho.Standard.plan.snapshot.free [] (.base "Proc") source := by
    rw [siteRoot] at firing
    cases firing with
    | fire _ _ _ sourceTyped _ _ _ _ _ => exact sourceTyped
  have declaredStandard : (receipt.job.declaration, receipt.job.ordinal) ∈ GeneralRho.Standard.plan.rules.zipIdx := by
    rw [GeneralRho.Standard.compiled_rules]
    rw [GeneralRho.DepthOne.compiled_rules] at declared
    exact declared
  refine ⟨⟨declaredStandard, ?_⟩, firing, accepted, filled, typed⟩
  rw [siteRoot]
  exact .here rfl sourceTyped.2.2.1 sourceTyped.1

/-- Structurally congruent object terms without sets are equal in the model. -/
theorem modelEquiv_of_sc {left right : Pattern} (object : isObjectPattern left = true) (pure : HashSetFree left)
    (congruent : StructuralCongruence left right) :
    WrapperCoherence.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc") presentation left right := by
  have reference := (RhoReference.sc_iff_reference object pure).mp congruent
  exact Relation.EqvGen.mono (fun a b step => .inr ((RhoReference.referenceStep_iff_modelMove a b).mp step)) _ _
    reference

/-- Object terms without sets equal in the model are structurally congruent. -/
theorem sc_of_modelEquiv {left right : Pattern} (object : isObjectPattern left = true) (pure : HashSetFree left)
    (equal : WrapperCoherence.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc") presentation left right) :
    StructuralCongruence left right := by
  apply (RhoReference.sc_iff_reference object pure).mpr
  refine Relation.EqvGen.mono (fun a b step => ?_) _ _ equal
  rcases step with equation | moved
  · exact absurd equation (RhoPresented.noEquations [] (.base "Proc") a b)
  · exact (RhoReference.referenceStep_iff_modelMove a b).mpr moved

/-- **Every step of the model from an object term without sets is a reduction of the reference rho
calculus.** -/
theorem model_step_reduces {source target : Pattern} (object : isObjectPattern source = true) (pure : HashSetFree source)
    (step : model.Step source target) :
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces source target) := by
  obtain ⟨_, receipt, before, fired, after⟩ := step
  obtain ⟨reduced⟩ := RhoReference.primitive_reduces fired
  have targetObject : isObjectPattern receipt.target = true := fired.2.2.2.2.2.2.1
  exact ⟨.equiv (sc_of_modelEquiv object pure before) reduced
    (sc_of_modelEquiv targetObject (RhoReference.primitive_target_hashSetFree fired) after)⟩

/-- A closed process of the established calculus is an object term. -/
theorem process_object (process : RhoProcess) : isObjectPattern process.1 = true :=
  (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefTypingAgreement.procWellSorted_object_canonical
    ((rhoClosedTermWellSorted_process_iff process.1).mp process.2).1).1

/-- A closed process of the established calculus holds no set. -/
theorem process_hashSetFree (process : RhoProcess) : HashSetFree process.1 :=
  rhoProcWellSorted_hashSetFree ((rhoClosedTermWellSorted_process_iff process.1).mp process.2).1

/-- **Every step of the established rho calculus is a step of the model**, to a structurally congruent
result. -/
theorem established_step {source target : RhoProcess} (step : rhoLanguageDefGSLT.Step source target) :
    ∃ target', model.Step source.1 target' ∧ StructuralCongruence target' target.1 := by
  obtain ⟨redex, contractum, sourceRedex, baseStep, contractumTarget⟩ := step
  obtain ⟨redexTyped, redexSafe⟩ := (rhoClosedTermWellSorted_process_iff redex.1).mp redex.2
  obtain ⟨target', canonicalStep, sameCanonical⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness.canonicalStep_complete_of_rhoStep
      redexTyped baseStep
  obtain ⟨receipt, valid, targetEq⟩ := GeneralRho.DepthOne.step_receipt
    (canonicalize_procWellSorted [] redexTyped) (canonicalize_binderSafeAt _ 0 redexSafe)
    (GeneralRho.DepthOne.isCanonical_channelsDecided (canonicalize_isCanonical _)) canonicalStep
  have congruent : StructuralCongruence source.1 (canonicalize redex.1) :=
    StructuralCongruence.trans _ _ _ (structuralCongruence_of_canonicalize_eq sourceRedex) (canonicalize_sound _)
  refine ⟨target', ⟨canonicalize redex.1, receipt,
    modelEquiv_of_sc (process_object source) (process_hashSetFree source) congruent,
    depthOne_receipt_standard valid, by rw [targetEq]; exact .refl _⟩, ?_⟩
  exact structuralCongruence_of_canonicalize_eq (sameCanonical.trans contractumTarget)

/-- Multi-steps of the model move with model equality at their source. -/
theorem multiStep_resp_left : ∀ {source source' target : Pattern}, model.MultiStep source target →
    WrapperCoherence.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc") presentation source source' →
    ∃ target', model.MultiStep source' target' ∧
      WrapperCoherence.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc") presentation target target'
  | _, source', _, .refl _, equal => ⟨source', .refl _, equal⟩
  | _, _, _, .step stepped rest, equal => by
    obtain ⟨middle', stepped', middleEqual⟩ := model.rewrites_resp_left equal stepped
    obtain ⟨last', reaches', lastEqual⟩ := multiStep_resp_left rest middleEqual
    exact ⟨last', .step stepped' reaches', lastEqual⟩

/-- Structurally congruent closed processes are equal in the model. -/
theorem modelEquiv_of_process_sc {left : Pattern} {right : RhoProcess}
    (congruent : StructuralCongruence left right.1) :
    WrapperCoherence.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc") presentation left right.1 :=
  .symm _ _ (modelEquiv_of_sc (process_object right) (process_hashSetFree right) (.symm _ _ congruent))

/-- **Every multi-step of the established rho calculus is a multi-step of the model**, to a result equal in
the model. -/
theorem established_multiStep : ∀ {source target : RhoProcess}, rhoLanguageDefGSLT.MultiStep source target →
    ∃ target', model.MultiStep source.1 target' ∧
      WrapperCoherence.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc") presentation target' target.1
  | process, _, .refl _ => ⟨process.1, .refl _, .refl _⟩
  | _, _, .step stepped rest => by
    obtain ⟨reached, modelStep, congruent⟩ := established_step stepped
    obtain ⟨last', reaches', lastEqual⟩ := established_multiStep rest
    obtain ⟨last'', reaches'', lastEqual'⟩ := multiStep_resp_left reaches'
      (.symm _ _ (modelEquiv_of_process_sc congruent))
    exact ⟨last'', .step modelStep reaches'', .trans _ _ _ (.symm _ _ lastEqual') lastEqual⟩

/-- **Every closed process reachable in the established rho calculus is explored**, from the canonical
form of the source, up to structural congruence. -/
theorem established_explored {source target : RhoProcess} (reaches : rhoLanguageDefGSLT.MultiStep source target) :
    ∃ state, Explore.Explored (S := WrapperCoherence.search GeneralRho.Standard.plan [] (.base "Proc") presentation)
        (WrapperCoherence.commit GeneralRho.Standard.plan presentation source.1) state ∧
      StructuralCongruence state target.1 := by
  obtain ⟨reached, modelReaches, reachedEqual⟩ := established_multiStep reaches
  obtain ⟨state, explored, stateEqual⟩ := RhoWrappers.rho_explores_wrappers source.1 modelReaches
  refine ⟨state, explored, ?_⟩
  have equal : WrapperCoherence.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc") presentation target.1 state :=
    .symm _ _ (.trans _ _ _ stateEqual reachedEqual)
  exact .symm _ _ (sc_of_modelEquiv (process_object target) (process_hashSetFree target) equal)

end Mettapedia.OSLF.MeTTaIL.Complete.RhoCompleteness
