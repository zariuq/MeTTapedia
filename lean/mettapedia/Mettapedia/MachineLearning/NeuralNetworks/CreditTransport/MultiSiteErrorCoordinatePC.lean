import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CarrierOutputPC

/-!
# Multi-site error-coordinate predictive credit

A single carrier-facing product cut can be represented either in state or
translated error coordinates, so that coordinate change alone does not define
a second learning mechanism.  A genuinely multi-site rule instead exposes a
finite family of predictive interfaces.  Each site has its own local
pullback, and the parameter credit is the sum of the adjacent detached
prediction-error credits.

This file proves the exact first-step ignition theorem for that finite
multi-site sum.  It also records a two-site fixture showing that deleting one
nonzero site changes the credit; the construction therefore does not reduce
definitionally to the one-cut rule.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace MultiSiteErrorCoordinatePC

open scoped BigOperators

noncomputable section

variable {ι State Parameter : Type*}
  [Fintype ι]
  [NormedAddCommGroup State] [NormedSpace ℝ State]
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

/-- Sum the reverse derivatives of all declared predictive sites at the
feed-forward state. -/
def multiSiteBPCredit
    (pullback : ι → State →ₗ[ℝ] Parameter)
    (prediction : ι → State)
    (taskGradient : (ι → State) → ι → State) : Parameter :=
  ∑ site, pullback site (taskGradient prediction site)

/-- Sum the local detached prediction-error credits over every site. -/
def multiSiteLocalCredit
    (pullback : ι → State →ₗ[ℝ] Parameter)
    (prediction settled : ι → State)
    (precision : ℝ) : Parameter :=
  ∑ site, pullback site
    (precision • (prediction site - settled site))

/-- One simultaneous error-coordinate inference step from zero error.  The
task-gradient field may couple all sites. -/
def firstSettledState
    (prediction : ι → State) (rate : ℝ)
    (taskGradient : (ι → State) → ι → State) : ι → State :=
  fun site => prediction site - rate • taskGradient prediction site

omit [Fintype ι] in
theorem prediction_sub_firstSettledState
    (prediction : ι → State) (rate : ℝ)
    (taskGradient : (ι → State) → ι → State) (site : ι) :
    prediction site -
        firstSettledState prediction rate taskGradient site =
      rate • taskGradient prediction site := by
  simp [firstSettledState]

/-- Every local site recovers its BP contribution at the common
`precision * rate` scale, so their finite sum does too. -/
theorem firstStep_multiSiteLocalCredit_eq_scaledBP
    (pullback : ι → State →ₗ[ℝ] Parameter)
    (prediction : ι → State) (precision rate : ℝ)
    (taskGradient : (ι → State) → ι → State) :
    multiSiteLocalCredit pullback prediction
        (firstSettledState prediction rate taskGradient) precision =
      (precision * rate) •
        multiSiteBPCredit pullback prediction taskGradient := by
  simp only [multiSiteLocalCredit, multiSiteBPCredit,
    prediction_sub_firstSettledState, smul_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro site _hsite
  exact (pullback site).map_smul
    (precision * rate) (taskGradient prediction site)

/-- Unit rate-times-precision is the exact multi-site BP ignition point. -/
theorem firstStep_multiSiteLocalCredit_eq_BP
    (pullback : ι → State →ₗ[ℝ] Parameter)
    (prediction : ι → State) (precision rate : ℝ)
    (taskGradient : (ι → State) → ι → State)
    (hscale : precision * rate = 1) :
    multiSiteLocalCredit pullback prediction
        (firstSettledState prediction rate taskGradient) precision =
      multiSiteBPCredit pullback prediction taskGradient := by
  rw [firstStep_multiSiteLocalCredit_eq_scaledBP, hscale, one_smul]

/-! ## Exact two-site fixtures -/

def twoSiteScalarPullback (_site : Fin 2) : ℝ →ₗ[ℝ] ℝ :=
  LinearMap.id

def zeroTwoSitePrediction (_site : Fin 2) : ℝ :=
  0

def unitTwoSiteTaskGradient
    (_state : Fin 2 → ℝ) (_site : Fin 2) : ℝ :=
  1

theorem twoSite_unitScale_recovers_BP :
    multiSiteLocalCredit twoSiteScalarPullback zeroTwoSitePrediction
        (firstSettledState zeroTwoSitePrediction (1 / 2)
          unitTwoSiteTaskGradient)
        2 =
      multiSiteBPCredit twoSiteScalarPullback zeroTwoSitePrediction
        unitTwoSiteTaskGradient := by
  apply firstStep_multiSiteLocalCredit_eq_BP
  norm_num

/-- A one-site projection misses a nonzero second local credit.  This is the
strict boundary separating the five-site executable rule from its one-cut
coordinate rewrite. -/
theorem firstSiteOnly_misses_nonzero_secondSite :
    let siteCredit : Fin 2 → ℝ := fun _ => 1
    siteCredit 0 ≠ ∑ site, siteCredit site := by
  norm_num [Fin.sum_univ_two]

/-- If the second site has zero credit, deleting it is harmless.  This
positive boundary complements the strict nonzero fixture. -/
theorem firstSiteOnly_recovers_zero_secondSite :
    let siteCredit : Fin 2 → ℝ := fun site => if site = 0 then 1 else 0
    siteCredit 0 = ∑ site, siteCredit site := by
  norm_num [Fin.sum_univ_two]

#print axioms firstStep_multiSiteLocalCredit_eq_scaledBP
#print axioms firstStep_multiSiteLocalCredit_eq_BP
#print axioms twoSite_unitScale_recovers_BP
#print axioms firstSiteOnly_misses_nonzero_secondSite
#print axioms firstSiteOnly_recovers_zero_secondSite

end

end MultiSiteErrorCoordinatePC

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
