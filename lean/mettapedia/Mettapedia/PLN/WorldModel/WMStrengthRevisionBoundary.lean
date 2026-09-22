import Mettapedia.PLN.Evidence.EvidenceControlReadout

/-!
# A strength readout cannot be the state of an additive world model

The same current strength can hide different evidence totals. Revising
both hidden states by one positive observation separates their strengths.
Consequently there is no binary revision operation on strength values that
makes the evidence-to-strength map preserve every evidence revision.

The full evidence carrier retains the update information and already has
the corresponding positive policy-sufficiency theorem. This obstruction is
about quotienting the state to a readout, not about the usefulness of the
readout as a derived observation.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WMStrengthRevisionBoundary

open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Evidence.EvidenceControlReadout

/-- No operation on scalar strengths can make strength a homomorphism of
the evidence-revision action. Thus equal current readouts do not justify
identifying world-model states when later revision remains observable. -/
theorem no_induced_strength_revision :
    ¬ ∃ reviseStrength : ENNReal → ENNReal → ENNReal,
      ∀ first second : BinaryEvidence,
        BinaryEvidence.toStrength (first + second) =
          reviseStrength
            (BinaryEvidence.toStrength first)
            (BinaryEvidence.toStrength second) := by
  rintro ⟨reviseStrength, homomorphism⟩
  have sameStrength := revision_separates_equal_strengths.1
  have afterRevision :
      BinaryEvidence.toStrength (revisePositive light) =
        BinaryEvidence.toStrength (revisePositive heavy) := by
    calc
      BinaryEvidence.toStrength (revisePositive light) =
          reviseStrength (BinaryEvidence.toStrength light)
            (BinaryEvidence.toStrength positiveObservation) := by
        simpa [revisePositive] using homomorphism light positiveObservation
      _ = reviseStrength (BinaryEvidence.toStrength heavy)
            (BinaryEvidence.toStrength positiveObservation) := by
        rw [sameStrength]
      _ = BinaryEvidence.toStrength (revisePositive heavy) := by
        simpa [revisePositive] using
          (homomorphism heavy positiveObservation).symm
  exact revision_separates_equal_strengths.2 afterRevision

end Mettapedia.PLN.WorldModel.WMStrengthRevisionBoundary
