import Mettapedia.Logic.EvidenceWeightedNormalGamma
import Mettapedia.Logic.SufficientStatisticSurface

/-!
# Weighted Normal-Gamma Surface

This module connects `WeightedNormalGammaEvidence` to the generic
world-model / sufficient-statistic layer.

The core observation is that a soft assignment `(w, x)` should contribute the
same weighted sufficient statistics that the EM M-step accumulates:

- effective count `w`
- weighted sum `w * x`
- weighted sum of squares `w * x^2`

This is not yet a full EM formalization. It is the additive WM-facing layer
that a soft-assignment Gaussian mixture would use.
-/

namespace Mettapedia.Logic

open scoped ENNReal
open Mettapedia.Logic.ConjugateEvidenceSurface
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceNormalGamma
open Mettapedia.Logic.EvidenceWeightedNormalGamma
open Mettapedia.Logic.EvidenceWeightedNormalGamma.WeightedNormalGammaEvidence
open Mettapedia.Logic.PLNWorldModelAdditive

namespace SufficientStatisticSurface

variable {Obs Query : Type*}

/-- Indicator responsibility for hard-labeled observations. -/
def indicatorResponsibility [DecidableEq Query]
    (label : Obs → Query) (o : Obs) (q : Query) : NNReal :=
  if label o = q then 1 else 0

@[simp] theorem indicatorResponsibility_eq_one [DecidableEq Query]
    (label : Obs → Query) (o : Obs) (q : Query) (h : label o = q) :
    indicatorResponsibility label o q = 1 := by
  simp [indicatorResponsibility, h]

@[simp] theorem indicatorResponsibility_eq_zero [DecidableEq Query]
    (label : Obs → Query) (o : Obs) (q : Query) (h : label o ≠ q) :
    indicatorResponsibility label o q = 0 := by
  simp [indicatorResponsibility, h]

/-- Query-indexed weighted Gaussian sufficient-statistic surface.

Each observation contributes a fractional responsibility mass and a real-valued
sample to the weighted Normal-Gamma sufficient statistics. -/
def weightedGaussianStatistic
    (responsibility : Obs → Query → NNReal)
    (value : Obs → Query → ℝ) :
    SufficientStatisticSurface Obs Query WeightedNormalGammaEvidence where
  observe o q := WeightedNormalGammaEvidence.single (responsibility o q) (value o q)

/-- The total observation count of the weighted aggregate is exactly the
aggregate responsibility mass. -/
theorem weightedGaussianStatistic_aggregate_observationCount
    (responsibility : Obs → Query → NNReal)
    (value : Obs → Query → ℝ)
    (σ : Multiset Obs) (q : Query) :
    ConjugateEvidence.observationCount
        (aggregate (weightedGaussianStatistic responsibility value) σ q) =
      genAdditiveExtension
        (Ev := ℝ≥0∞)
        (fun o q => (responsibility o q : ℝ≥0∞)) σ q := by
  change ConjugateEvidence.observationCount
      (genAdditiveExtension (weightedGaussianStatistic responsibility value).observe σ q) =
    genAdditiveExtension
      (Ev := ℝ≥0∞)
      (fun o q => (responsibility o q : ℝ≥0∞)) σ q
  rw [observationCount_genAdditiveExtension
      (a := (weightedGaussianStatistic responsibility value).observe) σ q]
  congr 1
  ext o q
  change ConjugateEvidence.observationCount
      (WeightedNormalGammaEvidence.single (responsibility o q) (value o q)) =
    (responsibility o q : ENNReal)
  exact WeightedNormalGammaEvidence.observationCount_single
    (w := responsibility o q) (x := value o q)

/-- Through the induced generic world model, weighted Gaussian observation count
is exactly the aggregated responsibility mass. -/
theorem weightedGaussianStatistic_queryObservationCount
    (responsibility : Obs → Query → NNReal)
    (value : Obs → Query → ℝ)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : WorldModel (Multiset Obs) Query WeightedNormalGammaEvidence :=
      (weightedGaussianStatistic responsibility value).inducedWorldModel
    AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := WeightedNormalGammaEvidence) σ q =
      genAdditiveExtension
        (Ev := ℝ≥0∞)
        (fun o q => (responsibility o q : ℝ≥0∞)) σ q := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query WeightedNormalGammaEvidence :=
    (weightedGaussianStatistic responsibility value).inducedWorldModel
  rw [queryObservationCount_inducedWorldModel_eq_aggregate_observationCount
      (S := weightedGaussianStatistic responsibility value)]
  exact weightedGaussianStatistic_aggregate_observationCount responsibility value σ q

/-- Through the induced generic world model, weighted Gaussian confidence is
the abstract count-based confidence of the weighted aggregate. -/
theorem weightedGaussianStatistic_queryObservationConfidence
    (κ : ℝ≥0∞)
    (responsibility : Obs → Query → NNReal)
    (value : Obs → Query → ℝ)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : WorldModel (Multiset Obs) Query WeightedNormalGammaEvidence :=
      (weightedGaussianStatistic responsibility value).inducedWorldModel
    AdditiveWorldModel.queryObservationConfidence
        (State := Multiset Obs) (Query := Query) (Ev := WeightedNormalGammaEvidence) κ σ q =
      observationConfidence κ
        (aggregate (weightedGaussianStatistic responsibility value) σ q) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query WeightedNormalGammaEvidence :=
    (weightedGaussianStatistic responsibility value).inducedWorldModel
  exact
    queryObservationConfidence_inducedWorldModel_eq_aggregate_observationConfidence
      (S := weightedGaussianStatistic responsibility value) κ σ q

/-- Weight-1 responsibilities recover the unit-observation law. -/
theorem weightedGaussianStatistic_unitObservation
    (value : Obs → Query → ℝ) :
    UnitObservation (weightedGaussianStatistic (fun _ _ => (1 : NNReal)) value) := by
  intro o q
  change ConjugateEvidence.observationCount
      (WeightedNormalGammaEvidence.single (1 : NNReal) (value o q)) = 1
  simpa using
    (WeightedNormalGammaEvidence.observationCount_single
      (w := (1 : NNReal)) (x := value o q))

/-- Hard labels embedded into the weighted carrier recover the existing
unweighted Gaussian aggregate exactly. -/
theorem weightedGaussianStatistic_one_aggregate_eq_ofDiscrete
    (value : Obs → Query → ℝ)
    (σ : Multiset Obs) (q : Query) :
    aggregate (weightedGaussianStatistic (fun _ _ => (1 : NNReal)) value) σ q =
      WeightedNormalGammaEvidence.ofDiscrete
        (aggregate (gaussianStatistic value) σ q) := by
  induction σ using Multiset.induction_on with
  | empty =>
      exact WeightedNormalGammaEvidence.ofDiscrete_zero.symm
  | @cons o σ ih =>
      rw [aggregate_cons, aggregate_cons, ih,
        WeightedNormalGammaEvidence.ofDiscrete_hplus]
      simp [weightedGaussianStatistic, gaussianStatistic,
        WeightedNormalGammaEvidence.ofDiscrete_single]

/-- Weight-1 responsibilities recover multiset cardinality as the generic WM
observation count. -/
theorem weightedGaussianStatistic_one_queryObservationCount
    (value : Obs → Query → ℝ)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : WorldModel (Multiset Obs) Query WeightedNormalGammaEvidence :=
      (weightedGaussianStatistic (fun _ _ => (1 : NNReal)) value).inducedWorldModel
    AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := WeightedNormalGammaEvidence) σ q =
      (σ.card : ℝ≥0∞) := by
  simpa using
    queryObservationCount_inducedWorldModel_of_unit
      (S := weightedGaussianStatistic (fun _ _ => (1 : NNReal)) value)
      (weightedGaussianStatistic_unitObservation value) σ q

/-- In the hard-label case, the weighted posterior update reduces exactly to
the existing Normal-Gamma posterior update over unweighted evidence. -/
theorem weightedGaussianStatistic_one_posterior_eq_gaussian
    (prior : Mettapedia.Logic.EvidenceNormalGamma.NormalGammaPrior)
    (value : Obs → Query → ℝ)
    (σ : Multiset Obs) (q : Query) :
    WeightedNormalGammaEvidence.posterior prior
        (aggregate (weightedGaussianStatistic (fun _ _ => (1 : NNReal)) value) σ q) =
      Mettapedia.Logic.EvidenceNormalGamma.posterior prior
        (aggregate (gaussianStatistic value) σ q) := by
  rw [weightedGaussianStatistic_one_aggregate_eq_ofDiscrete]
  simpa using
    WeightedNormalGammaEvidence.posterior_ofDiscrete_eq prior
      (aggregate (gaussianStatistic value) σ q)

/-- Hard labels reduce the weighted aggregate to the ordinary unweighted
per-label aggregate filtered by the component label. -/
theorem indicatorGaussianStatistic_aggregate_eq_ofDiscrete_filter
    [DecidableEq Query]
    (label : Obs → Query)
    (value : Obs → ℝ)
    (σ : Multiset Obs) (q : Query) :
    aggregate
        (weightedGaussianStatistic
          (indicatorResponsibility label)
          (fun o _ => value o)) σ q =
      WeightedNormalGammaEvidence.ofDiscrete
        (aggregate
          (gaussianStatistic (fun o _ => value o))
          (σ.filter fun o => label o = q) q) := by
  induction σ using Multiset.induction_on with
  | empty =>
      exact WeightedNormalGammaEvidence.ofDiscrete_zero.symm
  | @cons o σ ih =>
      by_cases h : label o = q
      · rw [aggregate_cons]
        rw [Multiset.filter_cons_of_pos σ h, aggregate_cons, ih,
          WeightedNormalGammaEvidence.ofDiscrete_hplus]
        simp [weightedGaussianStatistic, indicatorResponsibility, h,
          gaussianStatistic, WeightedNormalGammaEvidence.ofDiscrete_single]
      · rw [aggregate_cons]
        rw [Multiset.filter_cons_of_neg σ h, ih]
        simp [weightedGaussianStatistic, indicatorResponsibility, h,
          WeightedNormalGammaEvidence.zero_hplus,
          WeightedNormalGammaEvidence.single_zero]

/-- Hard-labeled weighted posterior update reduces exactly to the ordinary
unweighted Gaussian posterior on the filtered per-label observations. -/
theorem indicatorGaussianStatistic_posterior_eq_gaussian_filter
    [DecidableEq Query]
    (prior : Mettapedia.Logic.EvidenceNormalGamma.NormalGammaPrior)
    (label : Obs → Query)
    (value : Obs → ℝ)
    (σ : Multiset Obs) (q : Query) :
    WeightedNormalGammaEvidence.posterior prior
        (aggregate
          (weightedGaussianStatistic
            (indicatorResponsibility label)
            (fun o _ => value o)) σ q) =
      Mettapedia.Logic.EvidenceNormalGamma.posterior prior
        (aggregate
          (gaussianStatistic (fun o _ => value o))
          (σ.filter fun o => label o = q) q) := by
  rw [indicatorGaussianStatistic_aggregate_eq_ofDiscrete_filter
      (label := label) (value := value) (σ := σ) (q := q)]
  simpa using
    WeightedNormalGammaEvidence.posterior_ofDiscrete_eq prior
      (aggregate
        (gaussianStatistic (fun o _ => value o))
        (σ.filter fun o => label o = q) q)

end SufficientStatisticSurface

end Mettapedia.Logic
