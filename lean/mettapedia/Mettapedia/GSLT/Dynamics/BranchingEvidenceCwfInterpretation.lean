import Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization
import Mettapedia.TypeTheory.DependentExactCodeCommonModel
import Mettapedia.TypeTheory.DependentFamilyObserverFactorization

/-!
# A contextual-family interpretation of proof-relevant branching evidence

The evidence-indexed branching realization has a genuinely varying exact
evidence family over operational states.  This module interprets that family
inside the finite Tarski universe of the dependent exact-code model.  The
interpretation is fibrewise equivalent rather than judgmentally equal at the
unreachable entry state, making the semantic comparison explicit.

The completion observer identifies the two completed branches.  It therefore
cannot carry the decoded dependent evidence family: the corresponding fibres
are unit and Boolean.  The same observer also cannot reconstruct the
realization-derived cost, even though erasing answer evidence preserves each
already-selected history valuation.

This is a fragmentwise operational/intensional/extensional comparison.  It
does not identify execution histories with dependent terms, make cost part of
truth, or select a language calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.BranchingEvidenceCwfInterpretation

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ContextualEffectValuation
open Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization
open Mettapedia.TypeTheory.DependentExactCodeCommonModel
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization

/-- The exact operational evidence family encoded in the finite Tarski
universe. -/
def branchEvidenceCode : ordinaryCwf.Tm SourceTerm
    (finiteTarski.univ SourceTerm) :=
  fun state =>
    match state with
    | .entry => .empty
    | .leftDone => .unit
    | .rightDone => .bool

/-- The empty decoded type and the operational impossible-evidence type are
equivalent, despite being represented by different Lean inductives. -/
def emptyPEmptyEquiv : Empty ≃ PEmpty where
  toFun := Empty.elim
  invFun := PEmpty.elim
  left_inv value := value.elim
  right_inv value := value.elim

/-- Decoding the internal code recovers the operational exact-evidence family
at every state, up to a canonical equivalence. -/
def branchEvidenceEquiv (state : SourceTerm) :
    finiteTarski.el branchEvidenceCode state ≃ exactFamily.Exact state := by
  cases state with
  | entry => exact emptyPEmptyEquiv
  | leftDone => exact Equiv.refl PUnit
  | rightDone => exact Equiv.refl Bool

@[simp] theorem leftEvidence_decodes :
    finiteTarski.el branchEvidenceCode SourceTerm.leftDone = PUnit :=
  rfl

@[simp] theorem rightEvidence_decodes :
    finiteTarski.el branchEvidenceCode SourceTerm.rightDone = Bool :=
  rfl

/-- The completion readout identifies the two completed operational states. -/
theorem completed_states_same_observation :
    sourceCompletion.observe SourceTerm.leftDone =
      sourceCompletion.observe SourceTerm.rightDone :=
  rfl

/-- Consequently the decoded dependent evidence family cannot descend along
the completion observer. -/
theorem decodedEvidence_does_not_factor_through_completion :
    ¬ Nonempty
      (FamilyFactorization sourceCompletion.observe
        (finiteTarski.el branchEvidenceCode)) := by
  apply FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := SourceTerm.leftDone) (right := SourceTerm.rightDone)
    completed_states_same_observation
  simpa using
    Mettapedia.TypeTheory.DependentFamilyObserverFactorization.Canary.unit_not_equiv_bool

/-- The three relevant faces meet on one concrete fragment:

* the intensional face internally codes the varying exact-evidence family;
* the extensional completion face cannot retain that dependency;
* the operational face retains history and admits distinct lawful schedules,
  while realization-derived cost is not determined by the visible answer.
-/
theorem fragmentwise_operational_intensional_extensional_boundary :
    (∀ state, Nonempty
      (finiteTarski.el branchEvidenceCode state ≃ exactFamily.Exact state)) ∧
      ¬ Nonempty
        (FamilyFactorization sourceCompletion.observe
          (finiteTarski.el branchEvidenceCode)) ∧
      sharedHistory visibleProgram () = sharedHistory evidenceProgram () ∧
      sharedGrade sequentialWorkSpanValuation evidenceProgram () =
        some ⟨3, 3⟩ ∧
      sharedGrade parallelWorkSpanValuation evidenceProgram () =
        some ⟨3, 2⟩ ∧
      ¬ Factors visibleOutcome realizedOutcomeCost := by
  refine ⟨fun state => ⟨branchEvidenceEquiv state⟩,
    decodedEvidence_does_not_factor_through_completion,
    visible_erasure_preserves_history,
    evidenceProgram_sequential_workSpan,
    evidenceProgram_parallel_workSpan,
    realized_cost_not_visible_determined⟩

#print axioms branchEvidenceEquiv
#print axioms decodedEvidence_does_not_factor_through_completion
#print axioms fragmentwise_operational_intensional_extensional_boundary

end Mettapedia.GSLT.Dynamics.BranchingEvidenceCwfInterpretation
