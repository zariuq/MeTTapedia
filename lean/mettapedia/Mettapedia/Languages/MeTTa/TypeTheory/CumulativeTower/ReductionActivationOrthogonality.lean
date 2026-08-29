import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ReductionViewIndexedModalities
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SpaceActivationPolicyBoundary

/-!
# Reduction meaning and activation authority are independent axes

An authored reduction carrier determines the modal role of constructor
crossings.  An activation policy determines which resident occurrences may
actually step.  Neither coordinate determines the other.

This module makes their product explicit and exercises all four combinations
on the validated quotation-and-choice presentation:

* Process-indexed modal meaning with an inert data policy;
* Process-indexed modal meaning with triggered evaluation;
* Atom-indexed modal meaning with an inert data policy;
* Atom-indexed modal meaning with triggered evaluation.

The canaries establish both independence directions.  Two profiles with the
same reduction view may disagree about firing, while two profiles with the
same activation policy may disagree about the modal role of quotation.  Thus
"atoms reduce" can describe the type-theoretic reduction locus without making
every resident atom eager.  Data, evaluation, and communication remain
authored capabilities of a space.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace ReductionActivationOrthogonality

open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
open Mettapedia.GSLT.LanguageDef.DialectGluing
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedTyping
open Mettapedia.OSLF.MeTTaIL.Syntax
open ReductionChoiceNormalFormBoundary
open ReductionViewIndexedModalities

universe uStore uTrigger uObservation uReceipt

/-- The product of a type-theoretic reduction view and an operational
activation policy over the same pattern carrier.  The record deliberately
adds no implication between the coordinates.  Exact transition provenance is
supplied separately by the policy's receipts. -/
structure Profile (language : LanguageDef) (Store : Type uStore)
    (Trigger : Type uTrigger) (Observation : Type uObservation)
    (Receipt : Type uReceipt) where
  reduction : ReductionView language
  activation : Policy Store Pattern Trigger Observation Receipt

namespace Profile

def role {language : LanguageDef} {Store : Type uStore}
    {Trigger : Type uTrigger} {Observation : Type uObservation}
    {Receipt : Type uReceipt}
    (profile : Profile language Store Trigger Observation Receipt)
    {domain codomain : LangSort language}
    (arrow : SortArrow language domain codomain) : ConstructorRole :=
  profile.reduction.role arrow

def CanFire {language : LanguageDef} {Store : Type uStore}
    {Trigger : Type uTrigger} {Observation : Type uObservation}
    {Receipt : Type uReceipt}
    (profile : Profile language Store Trigger Observation Receipt)
    (store : Store) (cause : Cause Trigger Pattern) : Prop :=
  profile.activation.CanFire store cause

end Profile

namespace PrimeCanary

open SpaceActivationPolicyBoundary.PrimeCanary
open SpaceOperationalViewBoundary
open SpaceOperationalViewBoundary.PrimeCanary

def atomSort : LangSort quoteAndChoice := ⟨"Atom", by decide⟩
def processSort : LangSort quoteAndChoice := ⟨"Process", by decide⟩
def nameSort : LangSort quoteAndChoice := ⟨"PrimeName", by decide⟩

def quoteArrow : SortArrow quoteAndChoice atomSort nameSort :=
  ⟨"prime-quote", quoteAndChoice_has_quote_crossing⟩

def processReduction : ReductionView quoteAndChoice where
  carrier := processSort

def atomReduction : ReductionView quoteAndChoice where
  carrier := atomSort

abbrev Store := List Pattern
abbrev Receipt := RewriteReceipt quoteAndChoice choiceEnvironment 1
abbrev OperationalProfile := Profile quoteAndChoice Store Unit Store Receipt

def processData : OperationalProfile where
  reduction := processReduction
  activation := inertPolicy

def processEval : OperationalProfile where
  reduction := processReduction
  activation := triggeredPolicy

def atomData : OperationalProfile where
  reduction := atomReduction
  activation := inertPolicy

def atomEval : OperationalProfile where
  reduction := atomReduction
  activation := triggeredPolicy

theorem quote_neutral_for_process_profiles :
    processData.role quoteArrow = .neutral ∧
      processEval.role quoteArrow = .neutral := by
  decide

theorem quote_quoting_for_atom_profiles :
    atomData.role quoteArrow = .quoting ∧
      atomEval.role quoteArrow = .quoting := by
  decide

theorem processData_cannot_fire :
    ¬ processData.CanFire initialStore (.requested () choiceDemo) :=
  inert_choice_requested_cannot_fire

theorem atomData_cannot_fire :
    ¬ atomData.CanFire initialStore (.requested () choiceDemo) :=
  inert_choice_requested_cannot_fire

theorem processEval_can_fire :
    processEval.CanFire initialStore (.requested () choiceDemo) :=
  triggered_choice_requested_can_fire

theorem atomEval_can_fire :
    atomEval.CanFire initialStore (.requested () choiceDemo) :=
  triggered_choice_requested_can_fire

/-- Fixing modal meaning does not fix activation: the Process-indexed profiles
assign quotation the same role, but only the triggered profile may step. -/
theorem same_reduction_does_not_determine_activation :
    processData.reduction = processEval.reduction ∧
      processData.role quoteArrow = processEval.role quoteArrow ∧
      ¬ processData.CanFire initialStore (.requested () choiceDemo) ∧
      processEval.CanFire initialStore (.requested () choiceDemo) :=
  ⟨rfl, rfl, processData_cannot_fire, processEval_can_fire⟩

/-- Fixing activation does not fix modal meaning: these profiles use the same
triggered transition policy, yet quotation is neutral in the Process view and
quoting in the Atom view. -/
theorem same_activation_does_not_determine_reduction_role :
    processEval.activation = atomEval.activation ∧
      processEval.role quoteArrow = .neutral ∧
      atomEval.role quoteArrow = .quoting ∧
      processEval.CanFire initialStore (.requested () choiceDemo) ∧
      atomEval.CanFire initialStore (.requested () choiceDemo) :=
  ⟨rfl, quote_neutral_for_process_profiles.2,
    quote_quoting_for_atom_profiles.2, processEval_can_fire,
    atomEval_can_fire⟩

/-- No Boolean decision based only on quote's modal role can reproduce the
two Process profiles' firing behavior. -/
theorem no_modal_role_only_firing_classifier :
    ¬ ∃ classifier : ConstructorRole → Bool,
      (classifier (processData.role quoteArrow) = true ↔
        processData.CanFire initialStore (.requested () choiceDemo)) ∧
      (classifier (processEval.role quoteArrow) = true ↔
        processEval.CanFire initialStore (.requested () choiceDemo)) := by
  rintro ⟨classifier, dataClassifies, evalClassifies⟩
  have evalTrue : classifier (processEval.role quoteArrow) = true :=
    evalClassifies.mpr processEval_can_fire
  have dataTrue : classifier (processData.role quoteArrow) = true := by
    simpa [processData, processEval, Profile.role] using evalTrue
  exact processData_cannot_fire (dataClassifies.mp dataTrue)

/-- A common activation policy cannot supply a view-independent modal role
for quotation. -/
theorem no_activation_only_quote_role :
    ¬ ∃ role : ConstructorRole,
      processEval.role quoteArrow = role ∧
      atomEval.role quoteArrow = role := by
  rintro ⟨role, processRole, atomRole⟩
  rw [quote_neutral_for_process_profiles.2] at processRole
  rw [quote_quoting_for_atom_profiles.2] at atomRole
  exact ConstructorRole.noConfusion (processRole.trans atomRole.symm)

/-- The full two-by-two canary matrix.  Atom reduction is compatible with an
inert data space as well as a triggered evaluation space; triggering is
compatible with either modal reduction view. -/
theorem four_profiles_realize_the_product_boundary :
    ¬ processData.CanFire initialStore (.requested () choiceDemo) ∧
      processEval.CanFire initialStore (.requested () choiceDemo) ∧
      ¬ atomData.CanFire initialStore (.requested () choiceDemo) ∧
      atomEval.CanFire initialStore (.requested () choiceDemo) ∧
      processEval.role quoteArrow = .neutral ∧
      atomEval.role quoteArrow = .quoting :=
  ⟨processData_cannot_fire, processEval_can_fire, atomData_cannot_fire,
    atomEval_can_fire, quote_neutral_for_process_profiles.2,
    quote_quoting_for_atom_profiles.2⟩

end PrimeCanary

#print axioms PrimeCanary.same_reduction_does_not_determine_activation
#print axioms PrimeCanary.same_activation_does_not_determine_reduction_role
#print axioms PrimeCanary.no_modal_role_only_firing_classifier
#print axioms PrimeCanary.no_activation_only_quote_role
#print axioms PrimeCanary.four_profiles_realize_the_product_boundary

end ReductionActivationOrthogonality
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
