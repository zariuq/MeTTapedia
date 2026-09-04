import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DependentReflectiveCommunicationCell
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalCellThinness

/-!
# Thin mode cells and proof-relevant rho receipts are independent

The revisioned rho communication specimen contains two exact COMM receipts
with identical visible endpoints and distinguishable revisions.  This is real
proof relevance, but the receipts are elements of a dependent operational
fibre; they are not automatically two transformations between the same
modalities.

This module makes that level distinction formal.  It builds the parallel
receipt fibre over the common endpoint, proves that revision observation does
not descend through its thin reflection, and combines this with the inhabited
thin reflection of the mode factor cell.  Hence rho receipt non-collapse alone
does not force proof-relevant mode two-cells.  Such a choice requires a
declared consumer that distinguishes parallel mode transformations after the
selected coherence equations, not merely distinct terms or execution
receipts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ModeCellReceiptThinnessBoundary

open DependentReflectiveCommunicationCell
open RevisionedTypedCommunicationDemand
open Mettapedia.TypeTheory.LocallyThinCellReflection
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalCellThinness
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalTwoComputad

/-! ## The authentic parallel COMM-receipt fibre -/

/-- The visible endpoint shared by the revision-zero and revision-one exact
communications. -/
noncomputable def liveEndpoints : CommunicationEndpoints :=
  exactEndpoints zeroCommunication

/-- Exact typed COMM receipts whose visible boundary is the selected live
endpoint. -/
abbrev ParallelCommunication :=
  { communication : ExactCommunication //
    exactEndpoints communication = liveEndpoints }

/-- The exact COMM receipt retained at revision zero, in the common endpoint
fibre. -/
noncomputable def zeroParallelCommunication : ParallelCommunication :=
  ⟨zeroCommunication, rfl⟩

/-- The exact COMM receipt retained at revision one, in the same endpoint
fibre. -/
noncomputable def oneParallelCommunication : ParallelCommunication :=
  ⟨oneCommunication, zero_one_same_endpoints.symm⟩

/-- Observe the retained semantic revision of a parallel communication
receipt. -/
def receiptRevision (communication : ParallelCommunication) : Nat :=
  communication.1.1.revision

@[simp] theorem zeroParallelCommunication_revision :
    receiptRevision zeroParallelCommunication = 0 :=
  rfl

@[simp] theorem oneParallelCommunication_revision :
    receiptRevision oneParallelCommunication = 1 :=
  rfl

/-- Revision is a genuine discriminator on the fixed endpoint fibre. -/
noncomputable def revisionDiscriminator :
    Discriminator ParallelCommunication Nat where
  left := zeroParallelCommunication
  right := oneParallelCommunication
  observe := receiptRevision
  separates := by simp

/-- A locally thin quotient of the receipt fibre loses revision observation. -/
theorem receipt_revision_does_not_factor_through_thin_reflection :
    ¬ FactorsThrough receiptRevision :=
  revisionDiscriminator.not_factorsThrough

/-- The two receipts are distinct even though their endpoints agree by the
definition of `ParallelCommunication`. -/
theorem parallel_communications_distinct :
    zeroParallelCommunication ≠ oneParallelCommunication := by
  intro equality
  have revisionEquality := congrArg receiptRevision equality
  simp at revisionEquality

/-! ## Separation from mode-cell thinness -/

/-- The factor comparison can be retained in a locally thin mode-cell fibre
at the same time that the authentic rho receipt observer refuses to descend
through receipt thinning. -/
theorem thin_factor_cell_with_noncollapsed_receipt_observation :
    Nonempty
        (ThinReflection
          (ModeCell evidenceReadoutPath observePath)) /\
      Subsingleton
        (ThinReflection
          (ModeCell evidenceReadoutPath observePath)) /\
      ¬ FactorsThrough receiptRevision :=
  ⟨reflected_factor_cell_inhabited,
    inferInstance,
    receipt_revision_does_not_factor_through_thin_reflection⟩

/-- The complete checked boundary combines all three levels:

* primitive mode comparisons lose no identity under thinning;
* one raw administrative history is distinguished syntactically but identified
  by the categorical model; and
* the rho continuation and revision observations remain genuinely dependent
  operational data outside endpoint and receipt thinning.
-/
theorem mode_cell_receipt_thinness_boundary :
    (∀ {source target : Mode} {first second : ModePath source target},
      Function.Injective
        (@reflect (CellGenerator first second))) /\
      interpretCell factorRoundTrip = interpretCell factorIdentityCell /\
      Nonempty
        (ThinReflection
          (ModeCell evidenceReadoutPath observePath)) /\
      ¬ FactorsThrough receiptRevision /\
      Not (Nonempty
        (Mettapedia.TypeTheory.DependentFamilyObserverFactorization.FamilyFactorization
          exactEndpoints revisionContinuation)) :=
  ⟨by
      intro source target first second
      exact primitive_generator_reflection_injective,
    semantic_factor_history_identified,
    reflected_factor_cell_inhabited,
    receipt_revision_does_not_factor_through_thin_reflection,
    revisionContinuation_does_not_factor_through_endpoints⟩

/-! ## Axiom audit -/

#print axioms zeroParallelCommunication_revision
#print axioms oneParallelCommunication_revision
#print axioms receipt_revision_does_not_factor_through_thin_reflection
#print axioms parallel_communications_distinct
#print axioms thin_factor_cell_with_noncollapsed_receipt_observation
#print axioms mode_cell_receipt_thinness_boundary

end ModeCellReceiptThinnessBoundary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
