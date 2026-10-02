import Mettapedia.Algorithms.FiniteBayesRefinement
import Mathlib.Tactic.FieldSimp

/-!
# Checked rational Bayesian prior reduction

Ordinary rational data gives the old prior, the new prior and an old posterior.
The algorithm checks that each is a distribution and that the new prior is
supported by the old prior, then reweights the old posterior by the new/old
density ratio through the existing update.

If that old posterior is the checked update for a likelihood and the new
evidence is positive, the result is exactly the checked update of the new prior
by the same likelihood. The identity is the rational mass calculation.
-/

namespace Mettapedia.Algorithms.FiniteBayesReduction

open Finset
open Mettapedia.Algorithms.FiniteBayes
open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference

section Reduction

variable {S : Type*} [Fintype S]

/-- Pointwise density ratio of two ordinary rational mass functions. -/
def priorMassRatio (old new : S → ℚ) : S → ℚ :=
  fun s => new s / old s

/-- Check both priors and the old posterior, then reweight by `new / old`. -/
def reduce (oldPrior newPrior oldPosterior : S → ℚ) : Option (S → ℚ) :=
  if checkDistribution oldPrior ∧ checkDistribution newPrior ∧
      checkDistribution oldPosterior ∧
      (∀ s, 0 < newPrior s → 0 < oldPrior s) then
    update oldPosterior (priorMassRatio oldPrior newPrior)
  else
    none

omit [Fintype S] in
theorem ratio_nonneg (old new : S → ℚ) (oldNonneg : ∀ s, 0 ≤ old s)
    (newNonneg : ∀ s, 0 ≤ new s) (s : S) : 0 ≤ priorMassRatio old new s := by
  unfold priorMassRatio
  exact div_nonneg (newNonneg s) (oldNonneg s)

/-- On the new prior's support, reweighting cancels the old prior mass. -/
theorem prior_ratio_reweight (old new likelihood : S → ℚ)
    (newNonneg : ∀ s, 0 ≤ new s)
    (support : ∀ s, 0 < new s → 0 < old s)
    (evidencePos : normalizer old likelihood ≠ 0) (s : S) :
    (old s * likelihood s / normalizer old likelihood) * priorMassRatio old new s =
      new s * likelihood s / normalizer old likelihood := by
  unfold priorMassRatio
  by_cases hold : old s = 0
  · have hnew : new s = 0 :=
      le_antisymm (le_of_not_gt fun hn => (support s hn).ne' hold) (newNonneg s)
    simp [hold, hnew]
  · field_simp [hold, evidencePos]

/-- The reweighted evidence is the new evidence divided by the old evidence. -/
theorem reweight_normalizer (old new likelihood : S → ℚ)
    (newNonneg : ∀ s, 0 ≤ new s)
    (support : ∀ s, 0 < new s → 0 < old s)
    (evidencePos : normalizer old likelihood ≠ 0) :
    normalizer (fun s => old s * likelihood s / normalizer old likelihood)
        (priorMassRatio old new) =
      normalizer new likelihood / normalizer old likelihood := by
  unfold normalizer
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  simpa [normalizer] using
    prior_ratio_reweight old new likelihood newNonneg support evidencePos s

theorem reduce_sound (oldPrior newPrior oldPosterior output : S → ℚ)
    (accepted : reduce oldPrior newPrior oldPosterior = some output) :
    IsDistribution output := by
  unfold reduce at accepted
  split_ifs at accepted
  exact update_sound oldPosterior (priorMassRatio oldPrior newPrior) output accepted

theorem reduce_invalid_oldPrior (oldPrior newPrior oldPosterior : S → ℚ)
    (invalid : ¬ IsDistribution oldPrior) :
    reduce oldPrior newPrior oldPosterior = none := by
  unfold reduce
  split_ifs with valid
  · exact (invalid ((checkDistribution_iff oldPrior).mp valid.1)).elim
  · rfl

theorem reduce_invalid_newPrior (oldPrior newPrior oldPosterior : S → ℚ)
    (invalid : ¬ IsDistribution newPrior) :
    reduce oldPrior newPrior oldPosterior = none := by
  unfold reduce
  split_ifs with valid
  · exact (invalid ((checkDistribution_iff newPrior).mp valid.2.1)).elim
  · rfl

theorem reduce_invalid_posterior (oldPrior newPrior oldPosterior : S → ℚ)
    (invalid : ¬ IsDistribution oldPosterior) :
    reduce oldPrior newPrior oldPosterior = none := by
  unfold reduce
  split_ifs with valid
  · exact (invalid ((checkDistribution_iff oldPosterior).mp valid.2.2.1)).elim
  · rfl

theorem reduce_expanded_support (oldPrior newPrior oldPosterior : S → ℚ)
    (expanded : ∃ s, 0 < newPrior s ∧ ¬ 0 < oldPrior s) :
    reduce oldPrior newPrior oldPosterior = none := by
  unfold reduce
  split_ifs with valid
  · obtain ⟨s, hnew, hold⟩ := expanded
    exact (hold (valid.2.2.2 s hnew)).elim
  · rfl

theorem reduce_zero_reweight (oldPrior newPrior oldPosterior : S → ℚ)
    (impossible : normalizer oldPosterior (priorMassRatio oldPrior newPrior) = 0) :
    reduce oldPrior newPrior oldPosterior = none := by
  unfold reduce
  split_ifs with valid
  · exact update_impossible oldPosterior (priorMassRatio oldPrior newPrior) impossible
  · rfl

/-- Checked reduction commutes with a change of prior for one fixed likelihood. -/
theorem reduce_eq_update (oldPrior newPrior likelihood oldPosterior : S → ℚ)
    (accepted : update oldPrior likelihood = some oldPosterior)
    (newPositive : 0 < normalizer newPrior likelihood)
    (support : ∀ s, 0 < newPrior s → 0 < oldPrior s) :
    reduce oldPrior newPrior oldPosterior = update newPrior likelihood := by
  obtain ⟨oldValid, likeNonneg, oldPositive, rfl⟩ :=
    update_accepted oldPrior likelihood oldPosterior accepted
  by_cases newValid : IsDistribution newPrior
  · have evidenceNe : normalizer oldPrior likelihood ≠ 0 := oldPositive.ne'
    have ratioNn : ∀ s, 0 ≤ priorMassRatio oldPrior newPrior s :=
      ratio_nonneg oldPrior newPrior oldValid.nonneg newValid.nonneg
    have posteriorValid : IsDistribution
        (fun s => oldPrior s * likelihood s / normalizer oldPrior likelihood) :=
      update_sound oldPrior likelihood _ accepted
    have reweightPos : 0 < normalizer
        (fun s => oldPrior s * likelihood s / normalizer oldPrior likelihood)
        (priorMassRatio oldPrior newPrior) := by
      rw [reweight_normalizer oldPrior newPrior likelihood newValid.nonneg support evidenceNe]
      exact div_pos newPositive oldPositive
    have reduceChecks :
        checkDistribution oldPrior ∧ checkDistribution newPrior ∧
          checkDistribution
            (fun s => oldPrior s * likelihood s / normalizer oldPrior likelihood) ∧
          (∀ s, 0 < newPrior s → 0 < oldPrior s) :=
      ⟨(checkDistribution_iff oldPrior).mpr oldValid,
        (checkDistribution_iff newPrior).mpr newValid,
        (checkDistribution_iff _).mpr posteriorValid, support⟩
    have directChecks :
        checkDistribution newPrior ∧ (∀ s, 0 ≤ likelihood s) ∧
          0 < normalizer newPrior likelihood :=
      ⟨(checkDistribution_iff newPrior).mpr newValid, likeNonneg, newPositive⟩
    have ratioChecks :
        checkDistribution
            (fun s => oldPrior s * likelihood s / normalizer oldPrior likelihood) ∧
          (∀ s, 0 ≤ priorMassRatio oldPrior newPrior s) ∧
          0 < normalizer
            (fun s => oldPrior s * likelihood s / normalizer oldPrior likelihood)
            (priorMassRatio oldPrior newPrior) :=
      ⟨(checkDistribution_iff _).mpr posteriorValid, ratioNn, reweightPos⟩
    have hreduce : reduce oldPrior newPrior
          (fun s => oldPrior s * likelihood s / normalizer oldPrior likelihood) =
        update (fun s => oldPrior s * likelihood s / normalizer oldPrior likelihood)
          (priorMassRatio oldPrior newPrior) := by
      unfold reduce
      exact if_pos reduceChecks
    have hreweight : update
          (fun s => oldPrior s * likelihood s / normalizer oldPrior likelihood)
          (priorMassRatio oldPrior newPrior) =
        some (fun s =>
          (oldPrior s * likelihood s / normalizer oldPrior likelihood) *
            priorMassRatio oldPrior newPrior s /
          normalizer (fun s => oldPrior s * likelihood s / normalizer oldPrior likelihood)
            (priorMassRatio oldPrior newPrior)) := by
      unfold update
      exact if_pos ratioChecks
    have hdirect : update newPrior likelihood =
        some (fun s => newPrior s * likelihood s / normalizer newPrior likelihood) := by
      unfold update
      exact if_pos directChecks
    rw [hreduce, hreweight, hdirect]
    congr 1
    funext s
    rw [reweight_normalizer oldPrior newPrior likelihood newValid.nonneg support evidenceNe,
      prior_ratio_reweight oldPrior newPrior likelihood newValid.nonneg support evidenceNe s]
    field_simp [evidenceNe, newPositive.ne']
  · rw [update_invalid_prior newPrior likelihood newValid]
    unfold reduce
    split_ifs with valid
    · exact (newValid ((checkDistribution_iff newPrior).mp valid.2.1)).elim
    · rfl

/-- A commuting reduction is the real posterior of the new prior. -/
theorem reduce_update_refines (oldPrior newPrior likelihood oldPosterior output : S → ℚ)
    (accepted : update oldPrior likelihood = some oldPosterior)
    (newPositive : 0 < normalizer newPrior likelihood)
    (support : ∀ s, 0 < newPrior s → 0 < oldPrior s)
    (reduced : reduce oldPrior newPrior oldPosterior = some output) :
    ∃ valid : IsDistribution newPrior,
      ∃ nonneg : ∀ s, 0 ≤ (likelihood s : ℝ),
      ∃ possible :
        0 < evidence (realDistribution newPrior valid) (fun s => (likelihood s : ℝ)),
        realDistribution output
            (update_sound newPrior likelihood output
              ((reduce_eq_update oldPrior newPrior likelihood oldPosterior accepted
                newPositive support).symm.trans reduced)) =
          posterior (realDistribution newPrior valid) (fun s => (likelihood s : ℝ))
            nonneg possible := by
  exact update_refines newPrior likelihood output
    ((reduce_eq_update oldPrior newPrior likelihood oldPosterior accepted newPositive
      support).symm.trans reduced)

end Reduction

/-! ## Controls -/

/-- Two rational masses on `Fin 2`, indexed from zero. -/
def twoMass (left right : ℚ) : Fin 2 → ℚ :=
  fun s => if s = 0 then left else right

theorem twoMass_distribution (left right : ℚ) (leftNonneg : 0 ≤ left) (rightNonneg : 0 ≤ right)
    (normalized : left + right = 1) : IsDistribution (twoMass left right) := by
  constructor
  · intro s
    fin_cases s
    · simpa [twoMass] using leftNonneg
    · simpa [twoMass] using rightNonneg
  · rw [Fin.sum_univ_two]
    simp [twoMass, normalized]

theorem twoMass_normalizer (priorLeft priorRight likeLeft likeRight : ℚ) :
    normalizer (twoMass priorLeft priorRight) (twoMass likeLeft likeRight) =
      priorLeft * likeLeft + priorRight * likeRight := by
  unfold normalizer twoMass
  rw [Fin.sum_univ_two]
  simp

theorem twoMass_likelihood_nonneg (left right : ℚ) (leftNonneg : 0 ≤ left)
    (rightNonneg : 0 ≤ right) : ∀ s, 0 ≤ twoMass left right s := by
  intro s
  fin_cases s
  · simpa [twoMass] using leftNonneg
  · simpa [twoMass] using rightNonneg

theorem update_twoMass (priorLeft priorRight likeLeft likeRight : ℚ)
    (priorDist : IsDistribution (twoMass priorLeft priorRight))
    (likeLeftNonneg : 0 ≤ likeLeft) (likeRightNonneg : 0 ≤ likeRight)
    (evidencePos : 0 < priorLeft * likeLeft + priorRight * likeRight)
    (outLeft outRight : ℚ)
    (leftFormula : outLeft = priorLeft * likeLeft /
      (priorLeft * likeLeft + priorRight * likeRight))
    (rightFormula : outRight = priorRight * likeRight /
      (priorLeft * likeLeft + priorRight * likeRight)) :
    update (twoMass priorLeft priorRight) (twoMass likeLeft likeRight) =
      some (twoMass outLeft outRight) := by
  unfold update
  rw [twoMass_normalizer]
  have likeNonneg :=
    twoMass_likelihood_nonneg likeLeft likeRight likeLeftNonneg likeRightNonneg
  split_ifs with valid
  · apply congrArg some
    funext s
    fin_cases s
    · simpa [twoMass] using leftFormula.symm
    · simpa [twoMass] using rightFormula.symm
  · exact (valid ⟨(checkDistribution_iff _).mpr priorDist, likeNonneg, evidencePos⟩).elim

theorem fair_old_update :
    update (twoMass (1 / 2) (1 / 2)) (twoMass 1 3) = some (twoMass (1 / 4) (3 / 4)) := by
  exact update_twoMass (1 / 2) (1 / 2) 1 3
    (twoMass_distribution (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (1 / 4) (3 / 4) (by norm_num) (by norm_num)

theorem shifted_direct_update :
    update (twoMass (3 / 4) (1 / 4)) (twoMass 1 3) = some (twoMass (1 / 2) (1 / 2)) := by
  exact update_twoMass (3 / 4) (1 / 4) 1 3
    (twoMass_distribution (3 / 4) (1 / 4) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (1 / 2) (1 / 2) (by norm_num) (by norm_num)

theorem shifted_uniform_likelihood_update :
    update (twoMass (3 / 4) (1 / 4)) (twoMass 1 1) = some (twoMass (3 / 4) (1 / 4)) := by
  exact update_twoMass (3 / 4) (1 / 4) 1 1
    (twoMass_distribution (3 / 4) (1 / 4) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (3 / 4) (1 / 4) (by norm_num) (by norm_num)

theorem same_likelihood_agrees :
    reduce (twoMass (1 / 2) (1 / 2)) (twoMass (3 / 4) (1 / 4)) (twoMass (1 / 4) (3 / 4)) =
      update (twoMass (3 / 4) (1 / 4)) (twoMass 1 3) := by
  have support : ∀ s, 0 < twoMass (3 / 4) (1 / 4) s → 0 < twoMass (1 / 2) (1 / 2) s := by
    intro s _
    fin_cases s <;> simp [twoMass]
  have newPositive : 0 < normalizer (twoMass (3 / 4) (1 / 4)) (twoMass 1 3) := by
    rw [twoMass_normalizer]
    norm_num
  exact reduce_eq_update (twoMass (1 / 2) (1 / 2)) (twoMass (3 / 4) (1 / 4)) (twoMass 1 3)
    (twoMass (1 / 4) (3 / 4)) fair_old_update newPositive support

/-- A different likelihood is not recovered by reweighting the old posterior. -/
theorem changed_likelihood_disagrees :
    reduce (twoMass (1 / 2) (1 / 2)) (twoMass (3 / 4) (1 / 4)) (twoMass (1 / 4) (3 / 4)) ≠
      update (twoMass (3 / 4) (1 / 4)) (twoMass 1 1) := by
  rw [same_likelihood_agrees, shifted_direct_update, shifted_uniform_likelihood_update]
  intro same
  have values := congrFun (Option.some.inj same) 0
  simp [twoMass] at values
  norm_num at values

theorem dirac_uniform_update :
    update (twoMass 1 0) (twoMass 1 1) = some (twoMass 1 0) := by
  exact update_twoMass 1 0 1 1
    (twoMass_distribution 1 0 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) 1 0 (by norm_num) (by norm_num)

theorem expanded_uniform_update :
    update (twoMass (1 / 2) (1 / 2)) (twoMass 1 1) = some (twoMass (1 / 2) (1 / 2)) := by
  exact update_twoMass (1 / 2) (1 / 2) 1 1
    (twoMass_distribution (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (1 / 2) (1 / 2) (by norm_num) (by norm_num)

/-- Mass outside the old support is refused, while the direct update still exists. -/
theorem support_expansion_refused :
    update (twoMass 1 0) (twoMass 1 1) = some (twoMass 1 0) ∧
      0 < normalizer (twoMass (1 / 2) (1 / 2)) (twoMass 1 1) ∧
      update (twoMass (1 / 2) (1 / 2)) (twoMass 1 1) = some (twoMass (1 / 2) (1 / 2)) ∧
      reduce (twoMass 1 0) (twoMass (1 / 2) (1 / 2)) (twoMass 1 0) = none := by
  refine ⟨dirac_uniform_update, ?_, expanded_uniform_update, ?_⟩
  · rw [twoMass_normalizer]
    norm_num
  · exact reduce_expanded_support (twoMass 1 0) (twoMass (1 / 2) (1 / 2)) (twoMass 1 0)
      ⟨1, by simp [twoMass], by simp [twoMass]⟩

end Mettapedia.Algorithms.FiniteBayesReduction
