import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SpaceOperationalViewBoundary
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ReductionChoiceNormalFormBoundary

/-!
# Quotation/choice specimen for operational space views

On the validated quotation-and-choice presentation, inert and triggered
views share residency, reduction carrier and observation, yet differ on
whether the resident choice occurrence can fire.  This is a selected workload
instance of the generic operational-view interface, not a universal space
taxonomy or activation policy.
-/


open Mettapedia.OSLF.Framework
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SpaceOperationalViewCanary

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa.PrimeCandidates.QuotationChoiceGluing
open ReductionViewIndexedModalities
open ReductionChoiceNormalFormBoundary
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SpaceOperationalViewBoundary

def processReductionView : ReductionView quoteAndChoice where
  carrier := ⟨"Process", by decide⟩

def choiceEnvironment : RelationEnv :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.NucleusDerivedModalTyping.noFacts

def inert := inertView quoteAndChoice processReductionView choiceEnvironment 1
def triggered :=
  rewriteTriggeredView quoteAndChoice processReductionView choiceEnvironment 1

def initialStore : List Pattern := [choiceDemo]
def successorStore : List Pattern := [leftDemo, rightDemo]

def choiceReceipt : RewriteReceipt quoteAndChoice choiceEnvironment 1 where
  source := choiceDemo
  successors := successorStore
  exact := by
    simpa [choiceEnvironment, validatedChoiceLanguage, successorStore,
      successors] using choice_successors_exact.symm

theorem same_visible_substrate :
    OperationalView.SameVisibleSubstrate inert triggered :=
  inert_and_triggered_same_visible_substrate
    quoteAndChoice processReductionView choiceEnvironment 1

theorem same_reduction_view : inert.reduction = triggered.reduction :=
  inert_and_triggered_same_reduction
    quoteAndChoice processReductionView choiceEnvironment 1

theorem choice_is_resident_in_both :
    inert.resident initialStore choiceDemo ∧
      triggered.resident initialStore choiceDemo := by
  constructor <;> simp [inert, triggered, inertView, rewriteTriggeredView,
    initialStore]

theorem triggered_choice_can_fire :
    OperationalView.CanFire triggered initialStore choiceDemo := by
  refine ⟨successorStore, choiceReceipt, ?_⟩
  exact ⟨rfl, rfl, rfl, by simp [choiceReceipt, successorStore]⟩

theorem inert_choice_cannot_fire :
    ¬ OperationalView.CanFire inert initialStore choiceDemo := by
  rintro ⟨next, receipt, step⟩
  exact step

/-- Same residents, same reduction carrier, and the same observation do not
determine firing.  Activation is a separate authored capability. -/
theorem residency_and_reduction_do_not_determine_firing :
    OperationalView.SameVisibleSubstrate inert triggered ∧
      inert.reduction = triggered.reduction ∧
      ¬ OperationalView.CanFire inert initialStore choiceDemo ∧
      OperationalView.CanFire triggered initialStore choiceDemo :=
  ⟨same_visible_substrate, same_reduction_view,
    inert_choice_cannot_fire, triggered_choice_can_fire⟩


#print axioms triggered_choice_can_fire
#print axioms inert_choice_cannot_fire
#print axioms residency_and_reduction_do_not_determine_firing

end Mettapedia.Languages.MeTTa.PrimeCandidates.SpaceOperationalViewCanary
