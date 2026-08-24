import Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus

/-!
# Profitability selection over the semantic maximal frontier

The maximal-native calculus and profitability answer different questions.
A capability request first exposes its exact licensed semantic fibre.  Its
maximal elements are the realizations for which no strictly stronger eligible
calculus is available.  Only then may a declared finite cost policy choose
among those maximal elements.

This order matters.  A cheap but semantically non-maximal realization cannot
be promoted by cost, and equal costs do not create a canonical choice between
symmetry-related incomparable realizations.  The selected operation remains
the original admitted arrow; profitability adds neither a checker nor a new
semantic premise.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NIKProfitabilityFrontierSelection

open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus

universe uIndex uCapability uArtifact uCost

namespace RecognizedFamily.CapabilityRequest

variable {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
variable {source target : AdmissionObject.{uArtifact}}
variable {family : RecognizedFamily.{uIndex, uCapability, uArtifact} Index
  source target}

/-! ## The exact semantic frontier -/

/-- The finite set of semantically maximal realizations in one exact request
fibre.  This construction uses no cost observation. -/
noncomputable def semanticFrontier (request : family.CapabilityRequest) :
    Finset Index := by
  classical
  exact request.candidates.filter
    request.restrictedFamily.IsMaximalLicensed

theorem mem_semanticFrontier_iff
    (request : family.CapabilityRequest) (candidate : Index) :
    candidate ∈ semanticFrontier request ↔
      request.restrictedFamily.IsMaximalLicensed candidate := by
  classical
  constructor
  · intro member
    exact (Finset.mem_filter.mp member).2
  · intro maximal
    exact Finset.mem_filter.mpr ⟨maximal.1, maximal⟩

/-- Every feasible capability request has at least one semantic maximal
realization, independently of profitability. -/
theorem semanticFrontier_nonempty
    (request : family.CapabilityRequest) :
    (semanticFrontier request).Nonempty := by
  obtain ⟨candidate, maximal⟩ :=
    request.restrictedFamily.exists_maximalLicensed
  exact ⟨candidate, (mem_semanticFrontier_iff request candidate).mpr maximal⟩

/-! ## A declared cost policy over that frontier -/

/-- A profitability policy selects a semantically maximal realization whose
declared cost is minimal among all semantically maximal realizations for the
same request.  Cost never compares candidates outside the semantic frontier. -/
structure ProfitabilitySelection
    (request : family.CapabilityRequest) (Cost : Type uCost)
    [LinearOrder Cost] (cost : Index → Cost) where
  chosen : Index
  semanticMaximal :
    request.restrictedFamily.IsMaximalLicensed chosen
  costMinimal : ∀ candidate,
    request.restrictedFamily.IsMaximalLicensed candidate →
      cost chosen ≤ cost candidate

/-- Finite semantic frontiers admit a cost-minimal selection for every
linearly ordered declared cost. -/
theorem profitabilitySelection_inhabited
    (request : family.CapabilityRequest) (Cost : Type uCost)
    [LinearOrder Cost] (cost : Index → Cost) :
    Nonempty (ProfitabilitySelection request Cost cost) := by
  classical
  obtain ⟨chosen, chosenMember, minimal⟩ :=
    Finset.exists_min_image (semanticFrontier request) cost
      (semanticFrontier_nonempty request)
  refine ⟨⟨chosen,
    (mem_semanticFrontier_iff request chosen).mp chosenMember, ?_⟩⟩
  intro candidate candidateMaximal
  exact minimal candidate
    ((mem_semanticFrontier_iff request candidate).mpr candidateMaximal)

namespace ProfitabilitySelection

variable {request : family.CapabilityRequest} {Cost : Type uCost}
variable [LinearOrder Cost] {cost : Index → Cost}

/-- Profitability selection returns the original admitted semantic operation,
not a wrapper or a second authority. -/
def operation (selection : ProfitabilitySelection request Cost cost) :
    source ⟶ target :=
  family.package selection.chosen

theorem operation_preserves
    (selection : ProfitabilitySelection request Cost cost)
    (input : source.Carrier) (meaningful : source.Meaning input) :
    target.Meaning (selection.operation.run input) :=
  selection.operation.preserves input meaningful

theorem chosen_mem_exact_request
    (selection : ProfitabilitySelection request Cost cost) :
    selection.chosen ∈ request.candidates :=
  selection.semanticMaximal.1

theorem chosen_supports_required
    (selection : ProfitabilitySelection request Cost cost)
    {capability : family.Capability}
    (required : capability ∈ request.required) :
    family.supports selection.chosen capability :=
  ((request.candidates_exact selection.chosen).mp
    selection.chosen_mem_exact_request).2 capability required

end ProfitabilitySelection

end RecognizedFamily.CapabilityRequest

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus

abbrev Choice := NoGreatestCanary.Choice

private theorem leftMaximal :
    NoGreatestCanary.neutralRequest.restrictedFamily.IsMaximalLicensed
      NoGreatestCanary.Choice.left := by
  constructor
  · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
      NoGreatestCanary.neutralRequest]
  · intro candidate _ related
    exact related.symm

private theorem rightMaximal :
    NoGreatestCanary.neutralRequest.restrictedFamily.IsMaximalLicensed
      NoGreatestCanary.Choice.right := by
  constructor
  · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
      NoGreatestCanary.neutralRequest]
  · intro candidate _ related
    exact related.symm

def preferLeftCost : Choice → Nat
  | NoGreatestCanary.Choice.left => 0
  | NoGreatestCanary.Choice.right => 1

/-- A strict declared preference chooses the cheaper member of an incomparable
semantic frontier without calling it semantically stronger. -/
def preferLeftSelection :
    RecognizedFamily.CapabilityRequest.ProfitabilitySelection
      NoGreatestCanary.neutralRequest Nat preferLeftCost where
  chosen := NoGreatestCanary.Choice.left
  semanticMaximal := leftMaximal
  costMinimal := by
    intro candidate _
    cases candidate <;> simp [preferLeftCost]

theorem strict_cost_selection_runs_admitted_operation
    (input :
      Mettapedia.GSLT.LanguageDef.NIKMetalogic.AdmissionCanary.positiveNaturals.Carrier)
    (meaningful :
      Mettapedia.GSLT.LanguageDef.NIKMetalogic.AdmissionCanary.positiveNaturals.Meaning
        input) :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.AdmissionCanary.positiveNaturals.Meaning
      (preferLeftSelection.operation.run input) :=
  preferLeftSelection.operation_preserves input meaningful

def tiedCost : Choice → Nat := fun _ => 0

def tiedLeftSelection :
    RecognizedFamily.CapabilityRequest.ProfitabilitySelection
      NoGreatestCanary.neutralRequest Nat tiedCost where
  chosen := NoGreatestCanary.Choice.left
  semanticMaximal := leftMaximal
  costMinimal := by simp [tiedCost]

def tiedRightSelection :
    RecognizedFamily.CapabilityRequest.ProfitabilitySelection
      NoGreatestCanary.neutralRequest Nat tiedCost where
  chosen := NoGreatestCanary.Choice.right
  semanticMaximal := rightMaximal
  costMinimal := by simp [tiedCost]

theorem tied_cost_retains_two_valid_selections :
    tiedLeftSelection.chosen ≠ tiedRightSelection.chosen := by
  decide

def swap : Choice → Choice
  | NoGreatestCanary.Choice.left => NoGreatestCanary.Choice.right
  | NoGreatestCanary.Choice.right => NoGreatestCanary.Choice.left

theorem swap_ne_self (choice : Choice) : swap choice ≠ choice := by
  cases choice <;> simp [swap]

/-- When two incomparable realizations have the same cost and are exchanged
by a symmetry, no selected element is invariant under that symmetry.  A
deterministic implementation must therefore declare a tie-break policy or
retain both alternatives; the mathematics supplies no hidden canonical one. -/
theorem no_symmetry_invariant_tied_selection :
    ¬ ∃ selection :
        RecognizedFamily.CapabilityRequest.ProfitabilitySelection
          NoGreatestCanary.neutralRequest Nat tiedCost,
      swap selection.chosen = selection.chosen := by
  rintro ⟨selection, fixed⟩
  exact swap_ne_self selection.chosen fixed

/-! A cheaper non-maximal candidate is still excluded. -/

def linearNeutralRequest :
    Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus.Canary.linearFamily.CapabilityRequest where
  required := ∅
  candidates := Finset.univ
  candidates_exact := by
    intro candidate
    constructor
    · intro _
      constructor
      · simp [Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus.Canary.linearFamily]
      · intro capability required
        simp at required
    · intro _
      simp
  candidates_nonempty := Finset.univ_nonempty

def preferWeakerCost : Fin 2 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1

/-- Even when the weaker realization is cheaper, every profitability selection
must choose the semantically maximal realization. -/
theorem cheaper_nonmaximal_cannot_be_selected
    (selection :
      RecognizedFamily.CapabilityRequest.ProfitabilitySelection
        linearNeutralRequest Nat preferWeakerCost) :
    selection.chosen = (1 : Fin 2) := by
  apply Fin.eq_one_of_ne_zero selection.chosen
  intro chosenZero
  have oneMember :
      (1 : Fin 2) ∈ linearNeutralRequest.restrictedFamily.licensed := by
    simp [linearNeutralRequest,
      RecognizedFamily.CapabilityRequest.restrictedFamily]
  have chosenLeOne : selection.chosen ≤ (1 : Fin 2) := by
    rw [chosenZero]
    omega
  have reverse : (1 : Fin 2) ≤ selection.chosen :=
    selection.semanticMaximal.2 oneMember chosenLeOne
  rw [chosenZero] at reverse
  omega

end Canary

#print axioms RecognizedFamily.CapabilityRequest.semanticFrontier_nonempty
#print axioms RecognizedFamily.CapabilityRequest.profitabilitySelection_inhabited
#print axioms RecognizedFamily.CapabilityRequest.ProfitabilitySelection.operation_preserves
#print axioms Canary.strict_cost_selection_runs_admitted_operation
#print axioms Canary.tied_cost_retains_two_valid_selections
#print axioms Canary.no_symmetry_invariant_tied_selection
#print axioms Canary.cheaper_nonmaximal_cannot_be_selected

end Mettapedia.Languages.MeTTa.Prime.NIKProfitabilityFrontierSelection
