import Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization
import Mettapedia.TypeTheory.CwfTarskiUniverse
import Mettapedia.TypeTheory.DependentFamilyObserverFactorization

/-!
# Branching operational evidence inside a dependent Tarski universe

The exact evidence carried by the branching-realization example is a small
dependent family over operational states.  The large set-family CwF codes
that family internally in its substitution-stable Tarski universe.  Decoding
recovers the evidence fibre by equivalence at every state.

The coarse completion observer identifies the two completed branches, whose
evidence fibres are respectively unit and Boolean.  The decoded family
therefore cannot descend through that observer.  This keeps exact evidence,
visible completion, execution history, and cost as distinct semantic axes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.BranchingEvidenceTarskiInterpretation

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ContextualEffectValuation
open Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization
open Mettapedia.TypeTheory.CwfTarskiUniverse.SetFamilies
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization

/-- Operational states lifted to the context universe of the large
set-family CwF. -/
abbrev OperationalContext := ULift.{1, 0} SourceTerm

/-- The exact evidence family over lifted operational states. -/
def liftedExactFamily : OperationalContext → Type :=
  fun state => exactFamily.Exact state.down

/-- Completion observation transported to the lifted operational context. -/
def liftedCompletion : OperationalContext → Bool :=
  fun state => sourceCompletion.observe state.down

/-- The exact branch-evidence family encoded in the large dependent Tarski
universe. -/
def branchEvidenceCode :
    semanticCwf.{0}.Tm OperationalContext
      (smallTypes.{0}.univ OperationalContext) :=
  codeFamily liftedExactFamily

/-- Decoding the code recovers the exact operational evidence at each state. -/
def branchEvidenceEquiv (state : SourceTerm) :
    smallTypes.{0}.el branchEvidenceCode (ULift.up state) ≃
      exactFamily.Exact state :=
  elCodeFamilyEquiv liftedExactFamily (ULift.up state)

@[simp] theorem leftEvidence_decodes :
    smallTypes.{0}.el branchEvidenceCode (ULift.up SourceTerm.leftDone) =
      ULift.{1, 0} PUnit :=
  rfl

@[simp] theorem rightEvidence_decodes :
    smallTypes.{0}.el branchEvidenceCode (ULift.up SourceTerm.rightDone) =
      ULift.{1, 0} Bool :=
  rfl

/-- The decoded evidence family cannot be represented over the completion
observer because its two identified completed fibres are inequivalent. -/
theorem decodedEvidence_does_not_factor_through_completion :
    ¬ Nonempty
      (FamilyFactorization liftedCompletion
        (smallTypes.{0}.el branchEvidenceCode)) := by
  apply FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := ULift.up SourceTerm.leftDone)
    (right := ULift.up SourceTerm.rightDone)
    (by rfl)
  rintro ⟨equivalent⟩
  have unitBool : PUnit ≃ Bool :=
    Equiv.ulift.symm.trans (equivalent.trans Equiv.ulift)
  exact
    Mettapedia.TypeTheory.DependentFamilyObserverFactorization.Canary.unit_not_equiv_bool
      ⟨unitBool⟩

/-- The internal evidence code and the existing operational/cost boundaries
hold simultaneously. -/
theorem tarski_operational_observer_boundary :
    (∀ state, Nonempty
      (smallTypes.{0}.el branchEvidenceCode (ULift.up state) ≃
        exactFamily.Exact state)) ∧
      ¬ Nonempty
        (FamilyFactorization liftedCompletion
          (smallTypes.{0}.el branchEvidenceCode)) ∧
      sharedHistory visibleProgram () = sharedHistory evidenceProgram () ∧
      sharedGrade sequentialWorkSpanValuation evidenceProgram () =
        some ⟨3, 3⟩ ∧
      sharedGrade parallelWorkSpanValuation evidenceProgram () =
        some ⟨3, 2⟩ ∧
      ¬ Factors visibleOutcome realizedOutcomeCost :=
  ⟨fun state => ⟨branchEvidenceEquiv state⟩,
    decodedEvidence_does_not_factor_through_completion,
    visible_erasure_preserves_history,
    evidenceProgram_sequential_workSpan,
    evidenceProgram_parallel_workSpan,
    realized_cost_not_visible_determined⟩

#print axioms branchEvidenceEquiv
#print axioms decodedEvidence_does_not_factor_through_completion
#print axioms tarski_operational_observer_boundary

end Mettapedia.GSLT.Dynamics.BranchingEvidenceTarskiInterpretation
