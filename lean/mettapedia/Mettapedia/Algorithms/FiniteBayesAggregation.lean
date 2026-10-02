import Mettapedia.Algorithms.FiniteBayesRefinement
import Mettapedia.ProbabilityTheory.BayesianInference.Coarsening

/-! # Checked rational aggregation of finite Bayesian states -/

namespace Mettapedia.Algorithms.FiniteBayes

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.Cybernetics.ApproximateAdequacy

variable {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]

def aggregate (prior : S → ℚ) (view : S → C) : C → ℚ :=
  fun c => ∑ s, if view s = c then prior s else 0

def checkedAggregate (prior : S → ℚ) (view : S → C) : Option (C → ℚ) :=
  if checkDistribution prior then some (aggregate prior view) else none

theorem aggregate_distribution (prior : S → ℚ) (view : S → C)
    (valid : IsDistribution prior) : IsDistribution (aggregate prior view) := by
  constructor
  · intro c
    apply Finset.sum_nonneg
    intro s _
    split_ifs
    · exact valid.nonneg s
    · exact le_rfl
  · change (∑ c, ∑ s, if view s = c then prior s else 0) = 1
    rw [Finset.sum_comm]
    simpa [eq_comm] using valid.sum_eq_one

/-- The executable sum agrees with the independently defined probability pushforward. -/
theorem aggregate_refines (prior : S → ℚ) (view : S → C)
    (valid : IsDistribution prior) :
    realDistribution (aggregate prior view) (aggregate_distribution prior view valid) =
      Prob.coarsen (realDistribution prior valid) view := by
  apply Subtype.ext
  funext c
  simp only [realDistribution, aggregate, Prob.coarsen_apply, pushforward_eq_sum_ite,
    Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

theorem checkedAggregate_refines (prior : S → ℚ) (view : S → C) (output : C → ℚ)
    (accepted : checkedAggregate prior view = some output) :
    ∃ valid : IsDistribution prior,
      ∃ outputValid : IsDistribution output,
      realDistribution output outputValid = Prob.coarsen (realDistribution prior valid) view := by
  unfold checkedAggregate at accepted
  split_ifs at accepted with valid
  · cases Option.some.inj accepted
    exact ⟨(checkDistribution_iff prior).mp valid,
      aggregate_distribution prior view ((checkDistribution_iff prior).mp valid),
      aggregate_refines prior view ((checkDistribution_iff prior).mp valid)⟩

end Mettapedia.Algorithms.FiniteBayes
