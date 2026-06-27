import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.TypedITV

namespace Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex

open Mettapedia.PLN.WorldModel

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.TruthValues.PLNInformationGeometry
open Mettapedia.PLN.TruthValues.PLNAmplitudePhase
open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.Algebra.TwoDimClassification
open scoped ENNReal

universe u v


/-! ## Coherent desirable-gamble / lower-prevision forced queries -/

/-- A coherent desirable-gamble set avoids sure loss: no strictly negative
gamble is desirable. -/
theorem coherent_desirable_set_avoids_sure_loss
    {Ω : Type*}
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    ∀ f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω,
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble.StrictlyNegative f →
        f ∉ C.D :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.avoid_sure_loss C

/-- A coherent desirable-gamble set is a positive convex cone. -/
theorem coherent_desirable_set_is_positive_cone
    {Ω : Type*}
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    ∀ f g :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω,
      f ∈ C.D → g ∈ C.D → ∀ a b : ℝ, a > 0 → b > 0 →
        a • f + b • g ∈ C.D :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.desirable_is_cone C

/-- Coherent lower previsions are monotone. -/
theorem lower_prevision_is_monotone
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    {X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω}
    (h : X ≤ Y) :
    P X ≤ P Y :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision.mono P h

/-- Coherent lower previsions are superadditive. -/
theorem lower_prevision_is_superadditive
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    P X + P Y ≤ P (X + Y) := by
  exact P.superadd X Y

/-- The conjugate upper prevision is subadditive. -/
theorem upper_conjugate_prevision_is_subadditive
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    P.conjugate (X + Y) ≤ P.conjugate X + P.conjugate Y :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision.conjugate_subadditive
    P X Y

/-- Lower-prevision imprecision is nonnegative. -/
theorem lower_prevision_imprecision_is_nonnegative
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    0 ≤ Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision P X :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision_nonneg P X

/-- A regular lower prevision induces a coherent desirable-gamble set.  This is
the proved lower-prevision-to-desirability direction; it does not assert the
full converse natural-extension theorem. -/
noncomputable def regular_lower_prevision_induces_coherent_desirable_set
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (hReg : Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet
    P hReg

/-- Membership in the desirable set induced by a regular lower prevision is
exactly strict positivity of the lower prevision. -/
theorem regular_lower_prevision_desirable_membership
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (hReg : Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω) :
    X ∈ (regular_lower_prevision_induces_coherent_desirable_set P hReg).D ↔
      P X > 0 :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet_mem
    P hReg X

/-- Finite nonempty outcome spaces make regularity automatic for every lower
prevision. -/
theorem finite_lower_prevision_is_regular
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω) :
    Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finite_regular P

/-- The coherent desirable-gamble set induced by a lower prevision on a finite
nonempty outcome space. -/
noncomputable def finite_lower_prevision_induces_coherent_desirable_set
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
    P

/-- A finite credal lower envelope induces a coherent desirable-gamble set, and
membership is strict positivity of the lower envelope. -/
theorem finite_credal_lower_prevision_desirable_membership
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω) :
    X ∈
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCredalCoherentDesirableSet
          K hK).D ↔
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K X > 0 :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCredalCoherentDesirableSet_mem
    K hK X

/-- Finite coherent desirable-gamble sets induce genuine lower previsions via
Walley's natural-extension supremum formula.  This is the proved finite
converse direction, not the full infinite-dimensional representation theorem. -/
noncomputable def finite_desirable_set_induces_lower_prevision
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.DesirableLowerPrevisionBridge.finiteLowerPrevision
    C

/-- The finite desirable-gamble lower prevision is definitionally the
acceptable-price supremum already used by the desirable-gamble layer. -/
theorem finite_desirable_lower_prevision_apply
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω) :
    finite_desirable_set_induces_lower_prevision C X =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.DesirableLowerPrevisionBridge.finiteLowerPrevision_apply
    C X

/-- Lower-bound law for the finite desirable-gamble natural extension. -/
theorem finite_desirable_lower_prevision_lower_bound
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (c : ℝ) (hc : ∀ ω, c ≤ X ω) :
    c ≤ finite_desirable_set_induces_lower_prevision C X :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.DesirableLowerPrevisionBridge.lowerPrevision_lower_bound
    C X c hc

/-- Positive-homogeneity law for the finite desirable-gamble natural extension. -/
theorem finite_desirable_lower_prevision_pos_homog
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (r : ℝ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hr : 0 ≤ r) :
    finite_desirable_set_induces_lower_prevision C (r • X) =
      r * finite_desirable_set_induces_lower_prevision C X :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.DesirableLowerPrevisionBridge.lowerPrevision_pos_homog
    C r X hr

/-- Superadditivity law for the finite desirable-gamble natural extension. -/
theorem finite_desirable_lower_prevision_superadditive
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω) :
    finite_desirable_set_induces_lower_prevision C X +
      finite_desirable_set_induces_lower_prevision C Y ≤
        finite_desirable_set_induces_lower_prevision C (X + Y) :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.DesirableLowerPrevisionBridge.lowerPrevision_superadd
    C X Y

/-- A regular lower prevision round-trips through its induced desirable-gamble
set and the acceptable-price supremum construction. -/
theorem regular_lower_prevision_desirable_roundtrip
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (hReg : Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet
        P hReg) X = P X :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet_lowerPrevision_roundtrip
    P hReg X

/-- On finite nonempty outcome spaces, every lower prevision is regular, so the
lower-prevision → desirable-set → finite natural-extension round-trip recovers
the original lower prevision pointwise. -/
theorem finite_lower_prevision_desirable_roundtrip_apply
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    finite_desirable_set_induces_lower_prevision
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          P) X =
      P X :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet_lowerPrevision_roundtrip_apply
    P X

/-- On finite nonempty outcome spaces, the round-trip recovers the original
lower prevision as a structure. -/
theorem finite_lower_prevision_desirable_roundtrip
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω) :
    finite_desirable_set_induces_lower_prevision
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          P) = P :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet_lowerPrevision_roundtrip
    P

/-- The finite strict reconstruction operator: project a coherent
desirable-gamble set to its finite lower prevision, then reconstruct
`{X | P X > 0}`. -/
noncomputable def finite_strict_roundtrip
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip
    C

@[simp] theorem finite_strict_roundtrip_mem
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈ (finite_strict_roundtrip C).D ↔
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X > 0 :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_mem
    C X

/-- The strict finite reconstruction preserves the lower prevision it was built
from. -/
theorem finite_strict_roundtrip_lower_prevision_eq
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    finite_desirable_set_induces_lower_prevision (finite_strict_roundtrip C) =
      finite_desirable_set_induces_lower_prevision C :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_finiteLowerPrevision_eq
    C

/-- Strict finite reconstruction factors through the finite lower-prevision
projection. -/
theorem same_finite_lower_prevision_same_strict_roundtrip_D
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (h :
      finite_desirable_set_induces_lower_prevision C =
        finite_desirable_set_induces_lower_prevision D) :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision C)).D =
      (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision D)).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.same_finiteLowerPrevision_same_strictRoundTrip_D
    C D h

/-- Membership form of strict finite reconstruction factorization through the
finite lower-prevision projection. -/
theorem same_finite_lower_prevision_same_strict_roundtrip_mem_iff
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (h :
      finite_desirable_set_induces_lower_prevision C =
        finite_desirable_set_induces_lower_prevision D)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision C)).D ↔
      X ∈
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision D)).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.same_finiteLowerPrevision_same_strictRoundTrip_mem_iff
    C D h X

/-- Finite strict reconstruction is idempotent at the membership-set level. -/
theorem finite_strict_roundtrip_idempotent_D
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    (finite_strict_roundtrip (finite_strict_roundtrip C)).D =
      (finite_strict_roundtrip C).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_idempotent_D
    C

/-- Membership form of finite strict reconstruction idempotence. -/
theorem finite_strict_roundtrip_idempotent_mem_iff
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈ (finite_strict_roundtrip (finite_strict_roundtrip C)).D ↔
      X ∈ (finite_strict_roundtrip C).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_idempotent_mem_iff
    C X

/-- Openness/Archimedeanness for desirable-gamble sets: each desirable gamble
remains desirable after subtracting some strictly positive constant. -/
def archimedean_desirable_set
    {Ω : Type*}
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    Prop :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.ArchimedeanDesirableSet
    C

/-- The canonical finite strict representative is contained in the original
coherent desirable set. -/
theorem finite_strict_roundtrip_subset_original
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    (finite_strict_roundtrip C).D ⊆ C.D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_subset_original
    C

/-- Boundary canary for the canonical finite strict representative. -/
theorem finite_strict_roundtrip_not_mem_of_nonpositive_lower_prevision
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    (hBoundary :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X ≤ 0) :
    X ∉ (finite_strict_roundtrip C).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_not_mem_of_nonpositive_lowerPrevision
    C X hBoundary

/-- Archimedean/open coherent desirable sets are fixed by the canonical finite
strict representative at the membership level. -/
theorem finite_strict_roundtrip_mem_iff_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈ (finite_strict_roundtrip C).D ↔ X ∈ C.D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_mem_iff_of_archimedean
    C hArch X

/-- Set-level fixed-point law for Archimedean/open coherent desirable sets. -/
theorem finite_strict_roundtrip_D_eq_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C) :
    (finite_strict_roundtrip C).D = C.D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_D_eq_of_archimedean
    C hArch

/-- Structure-level fixed-point law for Archimedean/open coherent desirable
sets. -/
theorem finite_strict_roundtrip_eq_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C) :
    finite_strict_roundtrip C = C :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_eq_of_archimedean
    C hArch

/-- The canonical finite strict representative is always Archimedean/open. -/
theorem finite_strict_roundtrip_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    archimedean_desirable_set (finite_strict_roundtrip C) :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_archimedean
    C

/-- Exact fixed-point characterization of the finite strict reconstruction
operator. -/
theorem finite_strict_roundtrip_eq_iff_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    finite_strict_roundtrip C = C ↔ archimedean_desirable_set C :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_eq_iff_archimedean
    C

/-- Inclusion of desirable-gamble sets makes the induced finite lower
prevision monotone. -/
theorem finite_desirable_lower_prevision_mono_of_subset
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hCD : C.D ⊆ D.D)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    finite_desirable_set_induces_lower_prevision C X ≤
      finite_desirable_set_induces_lower_prevision D X :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteLowerPrevision_mono_of_desirable_subset
    C D hCD X

/-- Monotonicity of the canonical finite strict reconstruction operator. -/
theorem finite_strict_roundtrip_mono_D
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hCD : C.D ⊆ D.D) :
    (finite_strict_roundtrip C).D ⊆ (finite_strict_roundtrip D).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_mono_D
    C D hCD

/-- Universal property: every Archimedean/open coherent desirable subset of
`C` is contained in the canonical finite strict representative of `C`. -/
theorem finite_strict_roundtrip_greatest_archimedean_subset_D
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hDArch : archimedean_desirable_set D)
    (hDC : D.D ⊆ C.D) :
    D.D ⊆ (finite_strict_roundtrip C).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_greatest_archimedean_subset_D
    C D hDArch hDC

/-- Adjunction-style universal property: for Archimedean/open `D`, inclusion
below the canonical finite strict representative of `C` is equivalent to
inclusion below `C` itself. -/
theorem finite_strict_roundtrip_archimedean_subset_iff
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hDArch : archimedean_desirable_set D) :
    D.D ⊆ (finite_strict_roundtrip C).D ↔ D.D ⊆ C.D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_archimedean_subset_iff
    C D hDArch

/-- The strict desirable set induced by the finite natural extension is always
contained in the original coherent desirable set. -/
theorem finite_desirable_roundtrip_subset_original
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision C)).D ⊆ C.D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteDesirableRoundTrip_subset_original
    C

/-- Boundary canary: a gamble whose induced lower prevision is nonpositive is
not recovered by the strict desirable set `{X | P X > 0}`. -/
theorem finite_desirable_boundary_not_recovered
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    (hBoundary :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X ≤ 0) :
    X ∉
      (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision C)).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.nonpositive_lowerPrevision_not_recovered_by_strict_roundtrip
    C X hBoundary

/-- Under Archimedean/open desirability, the original desirable set is contained
in the strict desirable set induced by the finite natural extension. -/
theorem original_subset_finite_desirable_roundtrip_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C) :
    C.D ⊆
      (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision C)).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.original_subset_finiteDesirableRoundTrip_of_archimedean
    C hArch

/-- For Archimedean/open coherent desirable sets, the finite
desirable-set → lower-prevision → strict-desirable-set round-trip recovers
membership exactly. -/
theorem finite_desirable_roundtrip_mem_iff_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision C)).D ↔
      X ∈ C.D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteDesirableRoundTrip_mem_iff_of_archimedean
    C hArch X

/-- For Archimedean/open coherent desirable sets, the finite round-trip recovers
the original desirable-gamble membership set. -/
theorem finite_desirable_roundtrip_D_eq_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C) :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision C)).D = C.D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteDesirableRoundTrip_D_eq_of_archimedean
    C hArch

/-- Finite pointwise minimum of a gamble on a nonempty finite outcome space. -/
noncomputable def finite_minimum
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) : ℝ :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.DesirableLowerPrevisionBridge.finiteMinimum X

/-- The finite minimum is no larger than every coordinate of the gamble. -/
theorem finite_minimum_le_apply
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) (ω : Ω) :
    finite_minimum X ≤ X ω :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.DesirableLowerPrevisionBridge.finiteMinimum_le_apply X ω

/-- The strict positive cone of gambles. -/
def strict_positive_desirable_set
    (Ω : Type*) [Nonempty Ω] :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.strictlyPositiveDesirableSet Ω

/-- On finite nonempty outcome spaces, the strict positive cone is
Archimedean/open. -/
theorem strict_positive_desirable_set_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    archimedean_desirable_set (strict_positive_desirable_set Ω) :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.strictlyPositiveDesirableSet_archimedean

/-- Positive contrast: the strict positive cone is recovered by the finite
desirable-set → lower-prevision → strict-desirable-set round-trip. -/
theorem strict_positive_roundtrip_D_eq
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision
        (strict_positive_desirable_set Ω))).D =
      (strict_positive_desirable_set Ω).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.strictlyPositiveDesirableSet_roundtrip_D_eq

/-- Membership version of the strict-positive positive contrast. -/
theorem strict_positive_roundtrip_mem_iff
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision
            (strict_positive_desirable_set Ω))).D ↔
      (∀ ω, 0 < X ω) :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.strictlyPositiveDesirableSet_roundtrip_mem_iff X

/-- The strict positive cone induces the vacuous finite lower expectation:
the pointwise finite minimum of the gamble. -/
theorem strict_positive_lower_prevision_eq_finite_minimum
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (strict_positive_desirable_set Ω) X =
        finite_minimum X :=
  by
    simpa [strict_positive_desirable_set, finite_minimum] using
      Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.strictlyPositiveDesirableSet_lowerPrevision_eq_finiteMinimum
        X

/-- The closed positive cone of nonzero nonnegative gambles.  It is coherent
but not open/Archimedean in general. -/
def nonnegative_nonzero_desirable_set
    (Ω : Type*) [Nonempty Ω] :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.nonnegativeNonzeroDesirableSet Ω

/-- The closed positive cone induces the same vacuous finite lower expectation:
the pointwise finite minimum of the gamble. -/
theorem nonnegative_nonzero_lower_prevision_eq_finite_minimum
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (nonnegative_nonzero_desirable_set Ω) X =
        finite_minimum X :=
  by
    simpa [nonnegative_nonzero_desirable_set, finite_minimum] using
      Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.nonnegativeNonzeroDesirableSet_lowerPrevision_eq_finiteMinimum
        X

/-- Exact boundary-forgetting mechanism: strict and closed positive cones
induce the same finite lower prevision. -/
theorem positive_cones_induce_same_lower_prevision
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (strict_positive_desirable_set Ω) X =
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (nonnegative_nonzero_desirable_set Ω) X :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.positiveCones_induce_same_lowerPrevision
    X

/-- Projection-level form of the same boundary-forgetting mechanism: the
strict and closed positive cones induce the same finite lower prevision. -/
theorem positive_cones_induce_same_finite_lower_prevision
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    finite_desirable_set_induces_lower_prevision
        (strict_positive_desirable_set Ω) =
      finite_desirable_set_induces_lower_prevision
        (nonnegative_nonzero_desirable_set Ω) :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.positiveCones_induce_same_finiteLowerPrevision

/-- Exact finite canonicalization result: projecting the closed positive cone
to a lower prevision and reconstructing by the strict/open rule recovers the
strict positive cone. -/
theorem nonnegative_nonzero_strict_roundtrip_D_eq_strict_positive
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision
        (nonnegative_nonzero_desirable_set Ω))).D =
      (strict_positive_desirable_set Ω).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.nonnegativeNonzeroDesirableSet_strictRoundTrip_D_eq_strictlyPositive

/-- Membership form of the finite canonicalization result. -/
theorem nonnegative_nonzero_strict_roundtrip_mem_iff
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision
            (nonnegative_nonzero_desirable_set Ω))).D ↔
      (∀ ω, 0 < X ω) :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.nonnegativeNonzeroDesirableSet_strictRoundTrip_mem_iff
    X

/-- Bool boundary gamble: zero at `false`, one at `true`. -/
def bool_boundary_gamble :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Bool :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.boolBoundaryGamble

/-- The Bool boundary gamble is desirable in the closed positive cone. -/
theorem bool_boundary_gamble_desirable :
    bool_boundary_gamble ∈ (nonnegative_nonzero_desirable_set Bool).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.boolBoundaryGamble_mem_nonnegativeNonzero

/-- The Bool boundary gamble is not desirable in the strict positive cone. -/
theorem bool_boundary_gamble_not_strict :
    bool_boundary_gamble ∉ (strict_positive_desirable_set Bool).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.boolBoundaryGamble_not_mem_strictlyPositive

/-- The strict/open and closed positive cones are genuinely different on Bool. -/
theorem bool_positive_cones_distinct :
    (strict_positive_desirable_set Bool).D ≠
      (nonnegative_nonzero_desirable_set Bool).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.strictAndClosedPositiveCones_distinct_bool

/-- Concrete non-injectivity canary for the desirable-set to finite
lower-prevision projection. -/
theorem bool_positive_cones_projection_not_injective :
    (strict_positive_desirable_set Bool).D ≠
        (nonnegative_nonzero_desirable_set Bool).D ∧
      finite_desirable_set_induces_lower_prevision
          (strict_positive_desirable_set Bool) =
        finite_desirable_set_induces_lower_prevision
          (nonnegative_nonzero_desirable_set Bool) :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.bool_positiveCones_projection_not_injective

/-- The Bool boundary gamble has induced lower prevision exactly zero in the
closed positive cone. -/
theorem bool_boundary_lower_prevision_eq_zero :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (nonnegative_nonzero_desirable_set Bool) bool_boundary_gamble = 0 :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.boolBoundaryGamble_lowerPrevision_eq_zero

/-- Concrete boundary canary: a desirable boundary gamble with lower prevision
zero is dropped by the strict lower-prevision-to-desirable-set round-trip. -/
theorem bool_boundary_not_recovered_by_strict_roundtrip :
    bool_boundary_gamble ∈ (nonnegative_nonzero_desirable_set Bool).D ∧
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (nonnegative_nonzero_desirable_set Bool) bool_boundary_gamble = 0 ∧
      bool_boundary_gamble ∉
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision
            (nonnegative_nonzero_desirable_set Bool))).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.concreteBool_boundary_desirable_not_recovered_by_strict_roundtrip

/-- The closed positive cone on Bool is not Archimedean/open. -/
theorem bool_nonnegative_nonzero_not_archimedean :
    ¬ archimedean_desirable_set (nonnegative_nonzero_desirable_set Bool) :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.nonnegativeNonzeroBool_not_archimedean

/-- Concrete set-level canary: without Archimedean openness, the finite
desirable-set → lower-prevision → strict-desirable-set round-trip need not
recover the original desirable-gamble set. -/
theorem bool_boundary_roundtrip_set_ne_original :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision
        (nonnegative_nonzero_desirable_set Bool))).D ≠
      (nonnegative_nonzero_desirable_set Bool).D :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.concreteBool_boundary_roundtrip_set_ne_original


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
