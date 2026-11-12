import Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.Pressure

/-!
# Product references, fixed repertoires and integration

An independent reference and an additive cost give a product Gibbs law.
For fixed block marginals, reference-relative KL is exactly the existing
mutual-information functional. Certified global comparisons at two task
pressures therefore increase that information without Gaussian or
differentiability assumptions. The admissible set may impose further,
nonconvex restrictions, provided both comparisons use the same set.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy

open scoped BigOperators
open Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.BayesianInference

variable {A B : Type*} [Fintype A] [Fintype B]

def productLaw (left : Prob A) (right : Prob B) : Prob (A × B) := joint left (fun _ => right)

theorem productLaw_apply (left : Prob A) (right : Prob B) (pair : A × B) :
    (productLaw left right).1 pair = left.1 pair.1 * right.1 pair.2 := rfl

omit [Fintype A] [Fintype B] in
theorem weight_add (left : A → ℝ) (right : B → ℝ) (temperature : ℝ) (pair : A × B) :
    weight (fun pair : A × B => left pair.1 + right pair.2) temperature pair =
      weight left temperature pair.1 * weight right temperature pair.2 := by
  unfold weight
  rw [← Real.exp_add]
  congr 1
  ring

theorem partition_product (left : Prob A) (right : Prob B) (leftCost : A → ℝ) (rightCost : B → ℝ)
    (temperature : ℝ) :
    partition (productLaw left right) (fun pair => leftCost pair.1 + rightCost pair.2) temperature =
      partition left leftCost temperature * partition right rightCost temperature := by
  unfold partition evidence
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [productLaw_apply, weight_add]
  ring

theorem gibbs_product (left : Prob A) (right : Prob B) (leftCost : A → ℝ) (rightCost : B → ℝ)
    (temperature : ℝ) (positive : 0 < temperature) :
    gibbs (productLaw left right) (fun pair => leftCost pair.1 + rightCost pair.2) temperature positive =
      productLaw (gibbs left leftCost temperature positive) (gibbs right rightCost temperature positive) := by
  apply Subtype.ext
  funext pair
  simp only [gibbs_apply, productLaw_apply, weight_add, partition_product]
  ring

section Marginals

variable [DecidableEq A] [DecidableEq B]

def fixedMarginals (left : Prob A) (right : Prob B) : Set (Prob (A × B)) :=
  {law | Prob.coarsen law Prod.fst = left ∧ Prob.coarsen law Prod.snd = right}

theorem pairLaw_eq_self (law : Prob (A × B)) : law2 law.1 Prod.fst Prod.snd = law.1 := by
  funext pair
  exact pushforward_of_injective law.1 (fun pair : A × B => (pair.1, pair.2))
    (by intro first second same; exact same) pair

theorem fixed_marginals_supported (left : Prob A) (right : Prob B) (law : Prob (A × B))
    (fixed : law ∈ fixedMarginals left right) : SupportedBy law (productLaw left right).1 := by
  intro pair present
  have leftPositive := pushforward_pos_of_pos law.1 law.2.1 Prod.fst present
  have rightPositive := pushforward_pos_of_pos law.1 law.2.1 Prod.snd present
  have leftValue := congrArg (fun law : Prob A => law.1 pair.1) fixed.1
  have rightValue := congrArg (fun law : Prob B => law.1 pair.2) fixed.2
  change pushforward law.1 Prod.fst pair.1 = left.1 pair.1 at leftValue
  change pushforward law.1 Prod.snd pair.2 = right.1 pair.2 at rightValue
  rw [leftValue] at leftPositive
  rw [rightValue] at rightPositive
  exact mul_pos leftPositive rightPositive

theorem fixed_marginal_kl_eq_mutualInfo (left : Prob A) (right : Prob B) (law : Prob (A × B))
    (fixed : law ∈ fixedMarginals left right) :
    klSum law.1 (productLaw left right).1 = mutualInfo law.1 Prod.fst Prod.snd := by
  have leftValue : pushforward law.1 Prod.fst = left.1 := congrArg Subtype.val fixed.1
  have rightValue : pushforward law.1 Prod.snd = right.1 := congrArg Subtype.val fixed.2
  rw [mutualInfo, pairLaw_eq_self, leftValue, rightValue]
  rfl

theorem fixed_marginal_additive_utility (left : Prob A) (right : Prob B) (law : Prob (A × B))
    (fixed : law ∈ fixedMarginals left right) (leftUtility : A → ℝ) (rightUtility : B → ℝ) :
    expectedCost law (fun pair => leftUtility pair.1 + rightUtility pair.2) =
      expectedCost left leftUtility + expectedCost right rightUtility := by
  have leftValue : pushforward law.1 Prod.fst = left.1 := congrArg Subtype.val fixed.1
  have rightValue : pushforward law.1 Prod.snd = right.1 := congrArg Subtype.val fixed.2
  unfold expectedCost
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← sum_pushforward_mul law.1 Prod.fst leftUtility,
    ← sum_pushforward_mul law.1 Prod.snd rightUtility, leftValue, rightValue]

theorem additive_pressure_cannot_change_information (left : Prob A) (right : Prob B)
    (admissible : Set (Prob (A × B))) (included : admissible ⊆ fixedMarginals left right)
    (leftUtility : A → ℝ) (rightUtility : B → ℝ) (first second : Prob (A × B))
    (firstMember : first ∈ admissible) (secondMember : second ∈ admissible) (low high : ℝ)
    (firstMinimum : IsMinOn
      (pressureObjective (fun law : Prob (A × B) => klSum law.1 (productLaw left right).1)
        (fun law => expectedCost law (fun pair => leftUtility pair.1 + rightUtility pair.2)) low) admissible first)
    (secondMinimum : IsMinOn
      (pressureObjective (fun law : Prob (A × B) => klSum law.1 (productLaw left right).1)
        (fun law => expectedCost law (fun pair => leftUtility pair.1 + rightUtility pair.2)) high) admissible second) :
    mutualInfo first.1 Prod.fst Prod.snd = mutualInfo second.1 Prod.fst Prod.snd := by
  have one := firstMinimum secondMember
  have two := secondMinimum firstMember
  change klSum first.1 (productLaw left right).1 -
    low * expectedCost first (fun pair => leftUtility pair.1 + rightUtility pair.2) ≤
      klSum second.1 (productLaw left right).1 -
        low * expectedCost second (fun pair => leftUtility pair.1 + rightUtility pair.2) at one
  change klSum second.1 (productLaw left right).1 -
    high * expectedCost second (fun pair => leftUtility pair.1 + rightUtility pair.2) ≤
      klSum first.1 (productLaw left right).1 -
        high * expectedCost first (fun pair => leftUtility pair.1 + rightUtility pair.2) at two
  rw [fixed_marginal_additive_utility left right first (included firstMember),
    fixed_marginal_additive_utility left right second (included secondMember)] at one two
  have same : klSum first.1 (productLaw left right).1 = klSum second.1 (productLaw left right).1 := by
    linarith
  rwa [fixed_marginal_kl_eq_mutualInfo left right first (included firstMember),
    fixed_marginal_kl_eq_mutualInfo left right second (included secondMember)] at same

theorem fixed_marginal_pressure_comparison (left : Prob A) (right : Prob B)
    (admissible : Set (Prob (A × B))) (included : admissible ⊆ fixedMarginals left right)
    (utility : A × B → ℝ) (first second : Prob (A × B))
    (firstMember : first ∈ admissible) (secondMember : second ∈ admissible)
    (low high : ℝ) (increase : low < high)
    (firstMinimum : IsMinOn
      (pressureObjective (fun law : Prob (A × B) => klSum law.1 (productLaw left right).1)
        (fun law => expectedCost law utility) low) admissible first)
    (secondMinimum : IsMinOn
      (pressureObjective (fun law : Prob (A × B) => klSum law.1 (productLaw left right).1)
        (fun law => expectedCost law utility) high) admissible second) :
    0 ≤ expectedCost second utility - expectedCost first utility ∧
      low * (expectedCost second utility - expectedCost first utility) ≤
        mutualInfo second.1 Prod.fst Prod.snd - mutualInfo first.1 Prod.fst Prod.snd ∧
      mutualInfo second.1 Prod.fst Prod.snd - mutualInfo first.1 Prod.fst Prod.snd ≤
        high * (expectedCost second utility - expectedCost first utility) := by
  have compared := two_pressure_minima admissible
    (fun law : Prob (A × B) => klSum law.1 (productLaw left right).1)
    (fun law => expectedCost law utility) first second firstMember secondMember low high increase
    firstMinimum secondMinimum
  rwa [fixed_marginal_kl_eq_mutualInfo left right first (included firstMember),
    fixed_marginal_kl_eq_mutualInfo left right second (included secondMember)] at compared

theorem fixed_marginal_information_mono (left : Prob A) (right : Prob B)
    (admissible : Set (Prob (A × B))) (included : admissible ⊆ fixedMarginals left right)
    (utility : A × B → ℝ) (first second : Prob (A × B))
    (firstMember : first ∈ admissible) (secondMember : second ∈ admissible)
    (low high : ℝ) (nonnegative : 0 ≤ low) (increase : low < high)
    (firstMinimum : IsMinOn
      (pressureObjective (fun law : Prob (A × B) => klSum law.1 (productLaw left right).1)
        (fun law => expectedCost law utility) low) admissible first)
    (secondMinimum : IsMinOn
      (pressureObjective (fun law : Prob (A × B) => klSum law.1 (productLaw left right).1)
        (fun law => expectedCost law utility) high) admissible second) :
    mutualInfo first.1 Prod.fst Prod.snd ≤ mutualInfo second.1 Prod.fst Prod.snd := by
  have compared := fixed_marginal_pressure_comparison left right admissible included utility first second
    firstMember secondMember low high increase firstMinimum secondMinimum
  have lower := mul_nonneg nonnegative compared.1
  linarith [compared.2.1]

end Marginals

end Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy
