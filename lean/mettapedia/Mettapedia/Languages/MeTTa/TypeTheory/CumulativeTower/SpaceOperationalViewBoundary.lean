import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ReductionChoiceNormalFormBoundary
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ReductionViewIndexedModalities

/-!
# Space residency, reduction view, activation, and observation are independent

Several operational space kinds may share one occurrence store and one
authored language.  Selecting the sort that carries reduction is still not the
same as authorizing every resident occurrence to fire.  A space must also
supply an activation/transition handler, and any consumer sees the result
through an explicit observer.

This module gives the smallest proof-relevant boundary expressing those four
coordinates.  It includes generic inert and rewrite-triggered views over the
same list occurrence store, then instantiates both on the validated Prime
quotation-and-choice presentation.  The two instances have identical
residency, reduction carrier, and observation, but only the triggered view can
fire the resident choice occurrence.  Thus neither storage nor a reduction
sort can silently determine execution policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace SpaceOperationalViewBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.DialectGluing
open ReductionViewIndexedModalities
open ReductionChoiceNormalFormBoundary

universe uStore uObservation uReceipt

/-- A narrow operational view over one store.  The record deliberately does
not prescribe a final taxonomy of spaces; it only separates the coordinates
that the counterexample below proves independent. -/
structure OperationalView (language : LanguageDef)
    (Store : Type uStore) (Observation : Type uObservation)
    (Receipt : Type uReceipt) where
  reduction : ReductionView language
  resident : Store → Pattern → Prop
  step : Store → Pattern → Store → Receipt → Prop
  observe : Store → Observation

namespace OperationalView

def CanFire {language : LanguageDef} {Store : Type uStore}
    {Observation : Type uObservation} {Receipt : Type uReceipt}
    (view : OperationalView language Store Observation Receipt)
    (store : Store) (occurrence : Pattern) : Prop :=
  ∃ next receipt, view.step store occurrence next receipt

/-- Two operational views expose the same resident occurrences and the same
store observation.  Their transition handlers are intentionally absent from
this relation. -/
def SameVisibleSubstrate {language : LanguageDef} {Store : Type uStore}
    {Observation : Type uObservation} {Receipt : Type uReceipt}
    (first second : OperationalView language Store Observation Receipt) : Prop :=
  (∀ store occurrence,
      first.resident store occurrence ↔ second.resident store occurrence) ∧
    (∀ store, first.observe store = second.observe store)

end OperationalView

/-! ## Generic inert and rewrite-triggered views -/

/-- A proof-carrying exact engine step. -/
structure RewriteReceipt (language : LanguageDef) (environment : RelationEnv)
    (depth : Nat) where
  source : Pattern
  successors : List Pattern
  exact : successors =
    rewriteAt (engineBasePremises environment) language depth source

def inertView (language : LanguageDef) (reduction : ReductionView language)
    (environment : RelationEnv) (depth : Nat) :
    OperationalView language (List Pattern) (List Pattern)
      (RewriteReceipt language environment depth) where
  reduction := reduction
  resident := fun store occurrence => occurrence ∈ store
  step := fun _store _occurrence _next _receipt => False
  observe := id

/-- A one-cell triggered view.  Firing replaces the selected resident source
with the exact nonempty successor occurrence list carried by its receipt. -/
def rewriteTriggeredView (language : LanguageDef)
    (reduction : ReductionView language) (environment : RelationEnv)
    (depth : Nat) :
    OperationalView language (List Pattern) (List Pattern)
      (RewriteReceipt language environment depth) where
  reduction := reduction
  resident := fun store occurrence => occurrence ∈ store
  step := fun store occurrence next receipt =>
    store = [occurrence] ∧
      receipt.source = occurrence ∧
      next = receipt.successors ∧
      receipt.successors ≠ []
  observe := id

theorem inert_and_triggered_same_visible_substrate
    (language : LanguageDef) (reduction : ReductionView language)
    (environment : RelationEnv) (depth : Nat) :
    OperationalView.SameVisibleSubstrate
      (inertView language reduction environment depth)
      (rewriteTriggeredView language reduction environment depth) := by
  constructor
  · intro store occurrence
    rfl
  · intro store
    rfl

theorem inert_and_triggered_same_reduction
    (language : LanguageDef) (reduction : ReductionView language)
    (environment : RelationEnv) (depth : Nat) :
    (inertView language reduction environment depth).reduction =
      (rewriteTriggeredView language reduction environment depth).reduction :=
  rfl

/-! ## Prime choice canary -/

namespace PrimeCanary

def processReductionView : ReductionView quoteAndChoice where
  carrier := ⟨"Process", by decide⟩

def choiceEnvironment : RelationEnv :=
  Mettapedia.Languages.MeTTa.Prime.NucleusDerivedModalTyping.noFacts

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

end PrimeCanary

#print axioms inert_and_triggered_same_visible_substrate
#print axioms PrimeCanary.triggered_choice_can_fire
#print axioms PrimeCanary.inert_choice_cannot_fire
#print axioms PrimeCanary.residency_and_reduction_do_not_determine_firing

end SpaceOperationalViewBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
