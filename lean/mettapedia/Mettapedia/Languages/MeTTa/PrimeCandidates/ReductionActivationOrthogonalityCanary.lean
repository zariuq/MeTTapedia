import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.ReductionActivationOrthogonality
import Mettapedia.Languages.MeTTa.PrimeCandidates.SpaceActivationPolicyCanary

/-!
# Reduction/activation independence in the quotation/choice workload

The same validated presentation admits four concrete profiles: Process or
Atom reduction, each with inert or triggered activation.  Their proved
firing and modal-role differences rule out both a modal-role-only firing
classifier and a view-independent role determined by the shared activation.

These controls instantiate the generic product interface.  They do not
select one reduction carrier or activation discipline for the language.
-/


open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.OSLF.Framework
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.ReductionActivationOrthogonalityCanary

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
open Mettapedia.Languages.MeTTa.PrimeCandidates.QuotationChoiceGluing
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedTyping
open Mettapedia.OSLF.MeTTaIL.Syntax
open ReductionChoiceNormalFormBoundary
open ReductionViewIndexedModalities
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ReductionActivationOrthogonality

open Mettapedia.Languages.MeTTa.PrimeCandidates.SpaceActivationPolicyCanary
open SpaceOperationalViewBoundary
open Mettapedia.Languages.MeTTa.PrimeCandidates.SpaceOperationalViewCanary

def atomSort : LangSort quoteAndChoice := ⟨"Atom", by decide⟩
def processSort : LangSort quoteAndChoice := ⟨"Process", by decide⟩
def nameSort : LangSort quoteAndChoice := ⟨"CandidateName", by decide⟩

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


#print axioms same_reduction_does_not_determine_activation
#print axioms same_activation_does_not_determine_reduction_role
#print axioms no_modal_role_only_firing_classifier
#print axioms no_activation_only_quote_role
#print axioms four_profiles_realize_the_product_boundary

end Mettapedia.Languages.MeTTa.PrimeCandidates.ReductionActivationOrthogonalityCanary
