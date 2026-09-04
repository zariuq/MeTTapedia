import Mettapedia.Computability.ExactCodeDependentEvidenceComparison
import Mettapedia.TypeTheory.StratifiedSetFamilySemanticSpan

/-!
# Computational-trinity comparison inside a stratified Tarski model

The lower universe of the stratified set-family model internally codes the
proof-relevant evidence of a branching operational system.  Decoding that
internal family gives the program face of a computational-trinity comparison;
the operational state is its intermediate face and completion is its selected
extensional view.

Decoding is an equivalence of the comparison with its external operational
reading.  Adding exact representation layers gives another such equivalence.
Neither equivalence repairs the information deliberately forgotten by the
completion observer, and neither makes authentic work/span reconstructible
from that view.

This is a compatibility and non-collapse result.  It does not select a source
language, a type calculus, an observer, or a cost semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.StratifiedEvidenceComparison

open _root_.CategoryTheory
open Mettapedia.Algebra
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.DependentEvidenceComparison
open Mettapedia.Computability.ExactCodeDependentEvidenceComparison
open Mettapedia.Computability.OpenComputationalTrinity
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization
open Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy.TwoLevelSetFamilies
open Mettapedia.TypeTheory.ExactCodeFamilyRepresentation
open Mettapedia.TypeTheory.ExactCodeModalityModel
open Mettapedia.TypeTheory.StratifiedSetFamilySemanticSpan

/-! ## Internal decoding and the external operational reading -/

/-- The selected visible completion, lifted to the universe of the internal
state and evidence carriers. -/
abbrev CompletionView : Type 2 := ULift.{2, 0} Bool

def observeCompletion (state : OperationalContext) : CompletionView :=
  ULift.up (completion state)

/-- Evidence decoded from the lower internal Tarski universe. -/
abbrev DecodedEvidence (state : OperationalContext) : Type 2 :=
  hierarchy.{0}.el branchEvidenceCode state

/-- The same operational evidence read externally. -/
abbrev ExternalEvidence (state : OperationalContext) : Type 2 :=
  ULift.{2, 0} (exactFamily.Exact state.down)

/-- Internal decoding agrees fibrewise with the external operational evidence.
The state index is retained exactly. -/
def decodedEvidenceEquiv (state : OperationalContext) :
    DecodedEvidence state ≃ ExternalEvidence state := by
  rcases state with ⟨state⟩
  exact (branchEvidenceEquiv state).trans Equiv.ulift.symm

def decodedComparison : Comparison.{0, 0, 2} Context :=
  comparison DecodedEvidence observeCompletion

def externalComparison : Comparison.{0, 0, 2} Context :=
  comparison ExternalEvidence observeCompletion

/-- Fibrewise decoding induces an equivalence of the complete proof-relevant
program carriers. -/
def decodedTotalEquiv :
    TotalEvidence DecodedEvidence ≃ TotalEvidence ExternalEvidence :=
  totalEvidenceEquiv decodedEvidenceEquiv

def decodedProgramIso :
    evidenceFace DecodedEvidence ≅ evidenceFace ExternalEvidence :=
  (_root_.CategoryTheory.Functor.const Contextᵒᵖ).mapIso
    decodedTotalEquiv.toIso

/-- Decoding commutes with evidence erasure and the selected observation. -/
def decodeComparisonMap : ComparisonMap decodedComparison externalComparison where
  program := decodedProgramIso.hom
  logic := 𝟙 (stateFace (State := OperationalContext))
  space := 𝟙 (viewFace (View := CompletionView))
  programLogic := by
    ext context total
    rfl
  logicSpace := by
    simp [decodedComparison, externalComparison, comparison]

/-- Internal quotation supplies the inverse comparison map. -/
def encodeComparisonMap : ComparisonMap externalComparison decodedComparison where
  program := decodedProgramIso.inv
  logic := 𝟙 (stateFace (State := OperationalContext))
  space := 𝟙 (viewFace (View := CompletionView))
  programLogic := by
    ext context total
    rfl
  logicSpace := by
    simp [decodedComparison, externalComparison, comparison]

theorem decode_encode_program_map :
    decodeComparisonMap.program ≫ encodeComparisonMap.program =
      𝟙 (evidenceFace DecodedEvidence) :=
  decodedProgramIso.hom_inv_id

theorem encode_decode_program_map :
    encodeComparisonMap.program ≫ decodeComparisonMap.program =
      𝟙 (evidenceFace ExternalEvidence) :=
  decodedProgramIso.inv_hom_id

/-! ## The internal comparison retains the external information boundary -/

def externalRightFalse : TotalEvidence ExternalEvidence :=
  ⟨ULift.up SourceTerm.rightDone, ULift.up false⟩

def externalRightTrue : TotalEvidence ExternalEvidence :=
  ⟨ULift.up SourceTerm.rightDone, ULift.up true⟩

def externalLeftUnit : TotalEvidence ExternalEvidence :=
  ⟨ULift.up SourceTerm.leftDone, ULift.up PUnit.unit⟩

theorem external_right_values_distinct :
    externalRightFalse ≠ externalRightTrue := by
  intro equalTotals
  exact Bool.false_ne_true
    (congrArg ULift.down
      (eq_of_heq (Sigma.mk.inj_iff.mp equalTotals).2))

/-- The external comparison loses two proof-relevant values at one endpoint. -/
theorem external_comparison_loses_program_information :
    externalComparison.LosesProgramInformation :=
  comparison_loses_of_witness ExternalEvidence observeCompletion
    (left := externalRightFalse) (right := externalRightTrue)
    external_right_values_distinct rfl

/-- Internal Tarski coding neither creates nor repairs that loss. -/
theorem decoded_comparison_loses_program_information :
    decodedComparison.LosesProgramInformation :=
  (comparison_loses_congr_fibreEquiv observeCompletion
    decodedEvidenceEquiv).2 external_comparison_loses_program_information

/-- Work/span is still read from the authentic operational realization after
lifting the state into the internal semantic universe. -/
def externalWorkSpan : TotalEvidence ExternalEvidence → WorkSpan
  | ⟨state, evidence⟩ =>
      Mettapedia.Computability.DependentEvidenceComparison.Canary.totalEvidenceWorkSpan
        ⟨state.down, evidence.down⟩

@[simp] theorem external_left_workSpan :
    externalWorkSpan externalLeftUnit = ⟨2, 2⟩ :=
  rfl

@[simp] theorem external_right_workSpan :
    externalWorkSpan externalRightFalse = ⟨1, 1⟩ :=
  rfl

theorem external_workSpan_does_not_factor_through_completion :
    ¬ Factors
      (fun total : TotalEvidence ExternalEvidence =>
        observeCompletion total.1)
      externalWorkSpan := by
  let fibre : NonTrivialFiber
      (fun total : TotalEvidence ExternalEvidence =>
        observeCompletion total.1)
      externalWorkSpan :=
    { left := externalLeftUnit
      right := externalRightFalse
      sameShadow := rfl
      differentValue := by decide }
  exact fibre.not_factors

/-- Transport authentic work/span across the internal decoding equivalence. -/
def decodedWorkSpan : TotalEvidence DecodedEvidence → WorkSpan :=
  externalWorkSpan ∘ decodedTotalEquiv

theorem decoded_workSpan_does_not_factor_through_completion :
    ¬ Factors
      (fun total : TotalEvidence DecodedEvidence =>
        observeCompletion total.1)
      decodedWorkSpan := by
  have transported :=
    (not_factors_precomp_equiv_iff decodedTotalEquiv
      (fun total : TotalEvidence ExternalEvidence =>
        observeCompletion total.1)
      externalWorkSpan).2
        external_workSpan_does_not_factor_through_completion
  simpa [decodedWorkSpan, Function.comp_def, decodedTotalEquiv] using transported

/-! ## Exact representation inside the same lower universe -/

abbrev DecodedExactEvidence (depth : Nat)
    (state : OperationalContext) : Type 2 :=
  hierarchy.{0}.el (exactBranchEvidenceCode depth) state

abbrev ExternalExactEvidence (depth : Nat)
    (state : OperationalContext) : Type 2 :=
  codeFamily depth ExternalEvidence state

def decodedExactEvidenceEquiv (depth : Nat) (state : OperationalContext) :
    DecodedExactEvidence depth state ≃ ExternalExactEvidence depth state := by
  rcases state with ⟨state⟩
  exact (exactBranchEvidenceEquiv depth state).trans
    (iterCongrEquiv depth Equiv.ulift.symm)

def decodedExactComparison (depth : Nat) : Comparison.{0, 0, 2} Context :=
  comparison (DecodedExactEvidence depth) observeCompletion

def externalExactComparison (depth : Nat) : Comparison.{0, 0, 2} Context :=
  comparison (ExternalExactEvidence depth) observeCompletion

def decodedExactTotalEquiv (depth : Nat) :
    TotalEvidence (DecodedExactEvidence depth) ≃
      TotalEvidence (ExternalExactEvidence depth) :=
  totalEvidenceEquiv (decodedExactEvidenceEquiv depth)

/-- Exact representation preserves the external comparison boundary. -/
theorem external_exact_comparison_loses_program_information (depth : Nat) :
    (externalExactComparison depth).LosesProgramInformation := by
  exact
    (exactCode_comparison_loses_iff depth ExternalEvidence
      observeCompletion).2 external_comparison_loses_program_information

/-- Internal Tarski decoding and exact representation together still preserve
the information-loss boundary. -/
theorem decoded_exact_comparison_loses_program_information (depth : Nat) :
    (decodedExactComparison depth).LosesProgramInformation :=
  (comparison_loses_congr_fibreEquiv observeCompletion
    (decodedExactEvidenceEquiv depth)).2
      (external_exact_comparison_loses_program_information depth)

def externalExactTotalEquiv (depth : Nat) :
    TotalEvidence (ExternalExactEvidence depth) ≃
      TotalEvidence ExternalEvidence :=
  codeTotalEquiv depth ExternalEvidence

@[simp] theorem externalExactTotalEquiv_fst (depth : Nat)
    (total : TotalEvidence (ExternalExactEvidence depth)) :
    (externalExactTotalEquiv depth total).1 = total.1 :=
  rfl

def externalExactWorkSpan (depth : Nat) :
    TotalEvidence (ExternalExactEvidence depth) → WorkSpan :=
  externalWorkSpan ∘ externalExactTotalEquiv depth

theorem external_exact_workSpan_does_not_factor (depth : Nat) :
    ¬ Factors
      (fun total : TotalEvidence (ExternalExactEvidence depth) =>
        observeCompletion total.1)
      (externalExactWorkSpan depth) := by
  have transported :=
    (not_factors_precomp_equiv_iff (externalExactTotalEquiv depth)
      (fun total : TotalEvidence ExternalEvidence =>
        observeCompletion total.1)
      externalWorkSpan).2
        external_workSpan_does_not_factor_through_completion
  have observerPreserved :
      (fun total : TotalEvidence ExternalEvidence =>
          observeCompletion total.1) ∘ externalExactTotalEquiv depth =
        (fun total : TotalEvidence (ExternalExactEvidence depth) =>
          observeCompletion total.1) := by
    funext total
    rfl
  simpa only [externalExactWorkSpan, observerPreserved] using transported

def decodedExactWorkSpan (depth : Nat) :
    TotalEvidence (DecodedExactEvidence depth) → WorkSpan :=
  externalExactWorkSpan depth ∘ decodedExactTotalEquiv depth

@[simp] theorem decodedExactTotalEquiv_fst (depth : Nat)
    (total : TotalEvidence (DecodedExactEvidence depth)) :
    (decodedExactTotalEquiv depth total).1 = total.1 :=
  rfl

theorem decoded_exact_workSpan_does_not_factor (depth : Nat) :
    ¬ Factors
      (fun total : TotalEvidence (DecodedExactEvidence depth) =>
        observeCompletion total.1)
      (decodedExactWorkSpan depth) := by
  have transported :=
    (not_factors_precomp_equiv_iff (decodedExactTotalEquiv depth)
      (fun total : TotalEvidence (ExternalExactEvidence depth) =>
        observeCompletion total.1)
      (externalExactWorkSpan depth)).2
        (external_exact_workSpan_does_not_factor depth)
  have observerPreserved :
      (fun total : TotalEvidence (ExternalExactEvidence depth) =>
          observeCompletion total.1) ∘ decodedExactTotalEquiv depth =
        (fun total : TotalEvidence (DecodedExactEvidence depth) =>
          observeCompletion total.1) := by
    funext total
    rfl
  simpa only [decodedExactWorkSpan, observerPreserved] using transported

/-- The complete boundary inside the stratified common model: the comparison
commutes, while both decoded evidence and decoded exact evidence remain richer
than completion and carry cost which completion cannot reconstruct. -/
theorem stratified_evidence_comparison_boundary (depth : Nat) :
    decodedComparison.LosesProgramInformation ∧
      (decodedExactComparison depth).LosesProgramInformation ∧
      ¬ Factors
        (fun total : TotalEvidence DecodedEvidence =>
          observeCompletion total.1)
        decodedWorkSpan ∧
      ¬ Factors
        (fun total : TotalEvidence (DecodedExactEvidence depth) =>
          observeCompletion total.1)
        (decodedExactWorkSpan depth) :=
  ⟨decoded_comparison_loses_program_information,
    decoded_exact_comparison_loses_program_information depth,
    decoded_workSpan_does_not_factor_through_completion,
    decoded_exact_workSpan_does_not_factor depth⟩

#print axioms decodedEvidenceEquiv
#print axioms decodeComparisonMap
#print axioms encodeComparisonMap
#print axioms decode_encode_program_map
#print axioms encode_decode_program_map
#print axioms decoded_comparison_loses_program_information
#print axioms decoded_workSpan_does_not_factor_through_completion
#print axioms decodedExactEvidenceEquiv
#print axioms decoded_exact_comparison_loses_program_information
#print axioms decoded_exact_workSpan_does_not_factor
#print axioms stratified_evidence_comparison_boundary

end Mettapedia.Computability.StratifiedEvidenceComparison
