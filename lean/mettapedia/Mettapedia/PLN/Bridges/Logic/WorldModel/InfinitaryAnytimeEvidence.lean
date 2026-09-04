import Mettapedia.Logic.AnytimeEvidence
import Mettapedia.TypeTheory.InfinitaryProofAndObservationBoundary

/-!
# Finite evidence shapes for infinitary world-model formulas

Countable disjunction and conjunction have different finite interfaces.

* A satisfied countable disjunction has one finite witness.  Searching larger
  prefixes yields a monotone certificate which is sound and positively
  complete.
* A satisfied countable conjunction discharges every finite prefix
  obligation.  Those obligations restrict coherently from later stages to
  earlier stages, and their complete tower is equivalent to the infinitary
  formula.  No one stage is selected as final.

This module packages both sides using the generic evidence interfaces.  It
does not select a proof-search algorithm, probability calculus, or finite
cutoff.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.InfinitaryAnytimeEvidence

open Mettapedia.Logic.AnytimeEvidence
open Mettapedia.TypeTheory.InfinitaryProofAndObservationBoundary
open Mettapedia.TypeTheory.InfinitaryProofAndObservationBoundary.WorldModel
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary

universe u

/-! ## Countable disjunction: growing positive evidence -/

/-- The finite-stage certificate for a countable disjunction accepts when
one satisfying disjunct occurs before the current depth. -/
def iOrCertificate {L : LO.FirstOrder.Language.{u}}
    (model : PointedFOL L) (formulas : Nat → FOLInfQuery L) :
    MonotoneCertificate (SatisfiesInf model (.iOr formulas)) where
  acceptsAt depth := ∃ index, index < depth ∧
    SatisfiesInf model (formulas index)
  monotone := by
    intro earlier later bounded
    rintro ⟨index, within, satisfied⟩
    exact ⟨index, within.trans_le bounded, satisfied⟩
  sound := by
    intro depth
    rintro ⟨index, within, satisfied⟩
    exact (satisfiesInf_iOr_iff_some_finite_prefix model formulas).mpr
      ⟨depth, index, within, satisfied⟩

/-- Countable-disjunction evidence is positively complete: a true
disjunction exposes some witness at a finite prefix. -/
theorem iOrCertificate_eventuallyComplete
    {L : LO.FirstOrder.Language.{u}}
    (model : PointedFOL L) (formulas : Nat → FOLInfQuery L) :
    (iOrCertificate model formulas).EventuallyComplete := by
  intro satisfied
  exact (satisfiesInf_iOr_iff_some_finite_prefix model formulas).mp satisfied

/-! ## Countable conjunction: coherent finite obligations -/

/-- Finite prefixes of a countable conjunction form a coherent obligation
tower whose limit is exactly the infinitary conjunction. -/
def iAndObligationTower {L : LO.FirstOrder.Language.{u}}
    (model : PointedFOL L) (formulas : Nat → FOLInfQuery L) :
    CoherentObligationTower (SatisfiesInf model (.iAnd formulas)) where
  holdsAt depth := SatisfiesPrefix model formulas depth
  restrict := by
    intro earlier later bounded laterSatisfied index within
    exact laterSatisfied index (within.trans_le bounded)
  exact := satisfiesInf_iAnd_iff_every_finite_prefix model formulas

/-- A proof of the infinitary conjunction discharges each selected finite
prefix through the generic tower interface. -/
theorem iAnd_satisfies_every_finite_obligation
    {L : LO.FirstOrder.Language.{u}}
    (model : PointedFOL L) (formulas : Nat → FOLInfQuery L)
    (satisfied : SatisfiesInf model (.iAnd formulas)) (depth : Nat) :
    (iAndObligationTower model formulas).holdsAt depth :=
  (iAndObligationTower model formulas).holdsAt_of_claim satisfied depth

/-! ## Audited theorem crowns -/

#print axioms iOrCertificate_eventuallyComplete
#print axioms iAndObligationTower
#print axioms iAnd_satisfies_every_finite_obligation

end Mettapedia.PLN.Bridges.Logic.WorldModel.InfinitaryAnytimeEvidence
