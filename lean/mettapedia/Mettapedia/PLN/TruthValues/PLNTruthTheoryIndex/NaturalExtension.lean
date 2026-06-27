import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.AmplitudePhase

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


/-! ## Natural-extension discipline profile -/

/-- Conservative profile for the natural-extension side of the tower.  It
records the coherent desirable-gamble and lower-prevision laws currently
formalized, plus the induced-lower-prevision forcedness.  It does not claim the
full Walley natural-extension existence/representation theorem. -/
structure NaturalExtensionProfile where
  desirableAvoidsSureLoss :
    ∀ {Ω : Type}
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      ∀ f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω,
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble.StrictlyNegative f →
          f ∉ C.D
  desirablePositiveCone :
    ∀ {Ω : Type}
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      ∀ f g :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω,
        f ∈ C.D → g ∈ C.D → ∀ a b : ℝ, a > 0 → b > 0 →
          a • f + b • g ∈ C.D
  inducedLowerPrevisionForced :
    ∀ {World Ω : Type}
      (desirable :
        World →
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      {W₁ W₂ : World}, desirable W₁ = desirable W₂ →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          (desirable W₁) f =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          (desirable W₂) f
  finiteDesirableInducesLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω
  finiteDesirableLowerPrevisionApply :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      finite_desirable_set_induces_lower_prevision C X =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          C X
  finiteDesirableLowerPrevisionLowerBound :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (c : ℝ), (∀ ω, c ≤ X ω) →
        c ≤ finite_desirable_set_induces_lower_prevision C X
  finiteDesirableLowerPrevisionPositiveHomogeneous :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (r : ℝ) (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      0 ≤ r →
        finite_desirable_set_induces_lower_prevision C (r • X) =
          r * finite_desirable_set_induces_lower_prevision C X
  finiteDesirableLowerPrevisionSuperadditive :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      finite_desirable_set_induces_lower_prevision C X +
        finite_desirable_set_induces_lower_prevision C Y ≤
          finite_desirable_set_induces_lower_prevision C (X + Y)
  regularLowerPrevisionDesirableRoundTrip :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (hReg :
        Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet
          P hReg) X = P X
  finiteLowerPrevisionDesirableRoundTripApply :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      finite_desirable_set_induces_lower_prevision
          (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            P) X = P X
  finiteLowerPrevisionDesirableRoundTrip :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      finite_desirable_set_induces_lower_prevision
          (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            P) = P
  finiteStrictRoundTrip :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω
  finiteStrictRoundTripMem :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      X ∈ (finite_strict_roundtrip C).D ↔
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          C X > 0
  finiteStrictRoundTripLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      finite_desirable_set_induces_lower_prevision (finite_strict_roundtrip C) =
        finite_desirable_set_induces_lower_prevision C
  finiteStrictRoundTripIdempotent :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      (finite_strict_roundtrip (finite_strict_roundtrip C)).D =
        (finite_strict_roundtrip C).D
  finiteStrictRoundTripSubsetOriginal :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      (finite_strict_roundtrip C).D ⊆ C.D
  finiteStrictRoundTripBoundaryNotRecovered :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X ≤ 0 →
        X ∉ (finite_strict_roundtrip C).D
  finiteStrictRoundTripMembershipIffOfArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (_hArch : archimedean_desirable_set C)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      X ∈ (finite_strict_roundtrip C).D ↔ X ∈ C.D
  finiteStrictRoundTripSetEqOfArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set C →
        (finite_strict_roundtrip C).D = C.D
  finiteStrictRoundTripEqOfArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set C → finite_strict_roundtrip C = C
  finiteStrictRoundTripArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set (finite_strict_roundtrip C)
  finiteStrictRoundTripEqIffArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      finite_strict_roundtrip C = C ↔ archimedean_desirable_set C
  finiteDesirableLowerPrevisionMonotoneOfSubset :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      C.D ⊆ D.D →
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω,
          finite_desirable_set_induces_lower_prevision C X ≤
            finite_desirable_set_induces_lower_prevision D X
  finiteStrictRoundTripMonotone :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      C.D ⊆ D.D → (finite_strict_roundtrip C).D ⊆ (finite_strict_roundtrip D).D
  finiteStrictRoundTripGreatestArchimedeanSubset :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set D →
        D.D ⊆ C.D → D.D ⊆ (finite_strict_roundtrip C).D
  finiteStrictRoundTripArchimedeanSubsetIff :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set D →
        (D.D ⊆ (finite_strict_roundtrip C).D ↔ D.D ⊆ C.D)
  finiteStrictRoundTripFactorsThroughLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      finite_desirable_set_induces_lower_prevision C =
          finite_desirable_set_induces_lower_prevision D →
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision C)).D =
          (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            (finite_desirable_set_induces_lower_prevision D)).D
  finiteStrictRoundTripMembershipFactorsThroughLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      finite_desirable_set_induces_lower_prevision C =
          finite_desirable_set_induces_lower_prevision D →
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω,
          X ∈
              (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
                (finite_desirable_set_induces_lower_prevision C)).D ↔
            X ∈
              (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
                (finite_desirable_set_induces_lower_prevision D)).D
  finiteDesirableRoundTripSubsetOriginal :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision C)).D ⊆ C.D
  finiteDesirableBoundaryNotRecovered :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X ≤ 0 →
        X ∉
          (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            (finite_desirable_set_induces_lower_prevision C)).D
  finiteDesirableRoundTripMembershipIffOfArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (_hArch : archimedean_desirable_set C)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      X ∈
          (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            (finite_desirable_set_induces_lower_prevision C)).D ↔
        X ∈ C.D
  finiteDesirableRoundTripSetEqOfArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set C →
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision C)).D = C.D
  strictPositiveArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      archimedean_desirable_set (strict_positive_desirable_set Ω)
  strictPositiveRoundTripSetEq :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision
          (strict_positive_desirable_set Ω))).D =
        (strict_positive_desirable_set Ω).D
  strictPositiveRoundTripMemIff :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      X ∈
          (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            (finite_desirable_set_induces_lower_prevision
              (strict_positive_desirable_set Ω))).D ↔
        (∀ ω, 0 < X ω)
  strictPositiveLowerPrevisionFiniteMinimum :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (strict_positive_desirable_set Ω) X =
          finite_minimum X
  closedPositiveLowerPrevisionFiniteMinimum :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (nonnegative_nonzero_desirable_set Ω) X =
          finite_minimum X
  positiveConesInduceSameLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (strict_positive_desirable_set Ω) X =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (nonnegative_nonzero_desirable_set Ω) X
  positiveConesInduceSameFiniteLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      finite_desirable_set_induces_lower_prevision
          (strict_positive_desirable_set Ω) =
        finite_desirable_set_induces_lower_prevision
          (nonnegative_nonzero_desirable_set Ω)
  closedPositiveStrictRoundTripSetEq :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision
          (nonnegative_nonzero_desirable_set Ω))).D =
        (strict_positive_desirable_set Ω).D
  closedPositiveStrictRoundTripMemIff :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      X ∈
          (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            (finite_desirable_set_induces_lower_prevision
              (nonnegative_nonzero_desirable_set Ω))).D ↔
        (∀ ω, 0 < X ω)
  boolBoundaryDesirable :
    bool_boundary_gamble ∈ (nonnegative_nonzero_desirable_set Bool).D
  boolBoundaryNotStrict :
    bool_boundary_gamble ∉ (strict_positive_desirable_set Bool).D
  boolPositiveConesDistinct :
    (strict_positive_desirable_set Bool).D ≠
      (nonnegative_nonzero_desirable_set Bool).D
  boolPositiveConesProjectionNotInjective :
    (strict_positive_desirable_set Bool).D ≠
        (nonnegative_nonzero_desirable_set Bool).D ∧
      finite_desirable_set_induces_lower_prevision
          (strict_positive_desirable_set Bool) =
        finite_desirable_set_induces_lower_prevision
          (nonnegative_nonzero_desirable_set Bool)
  boolBoundaryLowerPrevisionEqZero :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (nonnegative_nonzero_desirable_set Bool) bool_boundary_gamble = 0
  boolBoundaryNotRecovered :
    bool_boundary_gamble ∈ (nonnegative_nonzero_desirable_set Bool).D ∧
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (nonnegative_nonzero_desirable_set Bool) bool_boundary_gamble = 0 ∧
      bool_boundary_gamble ∉
        (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision
            (nonnegative_nonzero_desirable_set Bool))).D
  boolBoundaryNotArchimedean :
    ¬ archimedean_desirable_set (nonnegative_nonzero_desirable_set Bool)
  boolBoundaryRoundTripSetNeOriginal :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision
        (nonnegative_nonzero_desirable_set Bool))).D ≠
      (nonnegative_nonzero_desirable_set Bool).D
  lowerMonotone :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      {X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω},
      X ≤ Y → P X ≤ P Y
  lowerSuperadditive :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      P X + P Y ≤ P (X + Y)
  upperConjugateSubadditive :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      P.conjugate (X + Y) ≤ P.conjugate X + P.conjugate Y
  imprecisionNonnegative :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      0 ≤ Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision P X

/-- Current natural-extension discipline profile. -/
noncomputable def naturalExtensionProfile : NaturalExtensionProfile where
  desirableAvoidsSureLoss :=
    coherent_desirable_set_avoids_sure_loss
  desirablePositiveCone :=
    coherent_desirable_set_is_positive_cone
  inducedLowerPrevisionForced :=
    desirable_lower_prevision_is_forced_by_desirable_set
  finiteDesirableInducesLowerPrevision :=
    finite_desirable_set_induces_lower_prevision
  finiteDesirableLowerPrevisionApply :=
    finite_desirable_lower_prevision_apply
  finiteDesirableLowerPrevisionLowerBound := by
    intro Ω instΩ nonemptyΩ C X c hc
    exact finite_desirable_lower_prevision_lower_bound C X c hc
  finiteDesirableLowerPrevisionPositiveHomogeneous := by
    intro Ω instΩ nonemptyΩ C r X hr
    exact finite_desirable_lower_prevision_pos_homog C r X hr
  finiteDesirableLowerPrevisionSuperadditive :=
    finite_desirable_lower_prevision_superadditive
  regularLowerPrevisionDesirableRoundTrip :=
    regular_lower_prevision_desirable_roundtrip
  finiteLowerPrevisionDesirableRoundTripApply :=
    finite_lower_prevision_desirable_roundtrip_apply
  finiteLowerPrevisionDesirableRoundTrip :=
    finite_lower_prevision_desirable_roundtrip
  finiteStrictRoundTrip :=
    @finite_strict_roundtrip
  finiteStrictRoundTripMem :=
    finite_strict_roundtrip_mem
  finiteStrictRoundTripLowerPrevision :=
    finite_strict_roundtrip_lower_prevision_eq
  finiteStrictRoundTripIdempotent :=
    finite_strict_roundtrip_idempotent_D
  finiteStrictRoundTripSubsetOriginal :=
    finite_strict_roundtrip_subset_original
  finiteStrictRoundTripBoundaryNotRecovered :=
    finite_strict_roundtrip_not_mem_of_nonpositive_lower_prevision
  finiteStrictRoundTripMembershipIffOfArchimedean :=
    finite_strict_roundtrip_mem_iff_of_archimedean
  finiteStrictRoundTripSetEqOfArchimedean :=
    finite_strict_roundtrip_D_eq_of_archimedean
  finiteStrictRoundTripEqOfArchimedean :=
    finite_strict_roundtrip_eq_of_archimedean
  finiteStrictRoundTripArchimedean :=
    finite_strict_roundtrip_archimedean
  finiteStrictRoundTripEqIffArchimedean :=
    finite_strict_roundtrip_eq_iff_archimedean
  finiteDesirableLowerPrevisionMonotoneOfSubset :=
    finite_desirable_lower_prevision_mono_of_subset
  finiteStrictRoundTripMonotone :=
    finite_strict_roundtrip_mono_D
  finiteStrictRoundTripGreatestArchimedeanSubset :=
    finite_strict_roundtrip_greatest_archimedean_subset_D
  finiteStrictRoundTripArchimedeanSubsetIff :=
    finite_strict_roundtrip_archimedean_subset_iff
  finiteStrictRoundTripFactorsThroughLowerPrevision :=
    same_finite_lower_prevision_same_strict_roundtrip_D
  finiteStrictRoundTripMembershipFactorsThroughLowerPrevision :=
    same_finite_lower_prevision_same_strict_roundtrip_mem_iff
  finiteDesirableRoundTripSubsetOriginal :=
    finite_desirable_roundtrip_subset_original
  finiteDesirableBoundaryNotRecovered :=
    finite_desirable_boundary_not_recovered
  finiteDesirableRoundTripMembershipIffOfArchimedean :=
    finite_desirable_roundtrip_mem_iff_of_archimedean
  finiteDesirableRoundTripSetEqOfArchimedean :=
    finite_desirable_roundtrip_D_eq_of_archimedean
  strictPositiveArchimedean :=
    strict_positive_desirable_set_archimedean
  strictPositiveRoundTripSetEq :=
    strict_positive_roundtrip_D_eq
  strictPositiveRoundTripMemIff :=
    strict_positive_roundtrip_mem_iff
  strictPositiveLowerPrevisionFiniteMinimum :=
    strict_positive_lower_prevision_eq_finite_minimum
  closedPositiveLowerPrevisionFiniteMinimum :=
    nonnegative_nonzero_lower_prevision_eq_finite_minimum
  positiveConesInduceSameLowerPrevision :=
    positive_cones_induce_same_lower_prevision
  positiveConesInduceSameFiniteLowerPrevision :=
    @positive_cones_induce_same_finite_lower_prevision
  closedPositiveStrictRoundTripSetEq :=
    @nonnegative_nonzero_strict_roundtrip_D_eq_strict_positive
  closedPositiveStrictRoundTripMemIff :=
    nonnegative_nonzero_strict_roundtrip_mem_iff
  boolBoundaryDesirable :=
    bool_boundary_gamble_desirable
  boolBoundaryNotStrict :=
    bool_boundary_gamble_not_strict
  boolPositiveConesDistinct :=
    bool_positive_cones_distinct
  boolPositiveConesProjectionNotInjective :=
    bool_positive_cones_projection_not_injective
  boolBoundaryLowerPrevisionEqZero :=
    bool_boundary_lower_prevision_eq_zero
  boolBoundaryNotRecovered :=
    bool_boundary_not_recovered_by_strict_roundtrip
  boolBoundaryNotArchimedean :=
    bool_nonnegative_nonzero_not_archimedean
  boolBoundaryRoundTripSetNeOriginal :=
    bool_boundary_roundtrip_set_ne_original
  lowerMonotone := by
    intro Ω P X Y h
    exact lower_prevision_is_monotone P h
  lowerSuperadditive :=
    lower_prevision_is_superadditive
  upperConjugateSubadditive :=
    upper_conjugate_prevision_is_subadditive
  imprecisionNonnegative :=
    lower_prevision_imprecision_is_nonnegative


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
