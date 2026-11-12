import Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.Parity

/-!
# Stationary higher-order histories with pairwise-independent coordinates

The finite noisy family has the density of Goertzel's three-unit mechanism,
parameterized by its sign correlation in `[0,1]`. Both endpoint laws remain
uniform. Every pair of the six input/output coordinates is independent,
while the complete input and output histories are dependent at positive
correlation. These facts do not require a Gaussian approximation.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 12000000

noncomputable section

namespace Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.NoisyParity

open scoped BigOperators
open Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV
open Parity (Bits sign transition initial)

abbrev History := Bits × Bits

def errors (history : History) : Bits :=
  (Bool.xor history.2.1 (transition history.1).1,
    Bool.xor history.2.2.1 (transition history.1).2.1,
    Bool.xor history.2.2.2 (transition history.1).2.2)

def mass (correlation : ℝ) (history : History) : ℝ :=
  (1 + correlation * sign (errors history).1) *
    (1 + correlation * sign (errors history).2.1) *
      (1 + correlation * sign (errors history).2.2) / 64

theorem mass_eq_paper (correlation : ℝ) (history : History) :
    mass correlation history =
      (1 + correlation * (sign history.2.1 * sign history.1.2.1 * sign history.1.2.2)) *
        (1 + correlation * (sign history.2.2.1 * sign history.1.1 * sign history.1.2.2)) *
          (1 + correlation * (sign history.2.2.2 * sign history.1.1 * sign history.1.2.1 * sign history.1.2.2)) / 64 := by
  rcases history with ⟨⟨a, b, c⟩, ⟨x, y, z⟩⟩
  cases a <;> cases b <;> cases c <;> cases x <;> cases y <;> cases z <;>
    norm_num [mass, errors, transition, sign]

theorem factor_nonnegative (correlation : ℝ) (nonnegative : 0 ≤ correlation) (bounded : correlation ≤ 1)
    (bit : Bool) : 0 ≤ 1 + correlation * sign bit := by
  cases bit <;> norm_num [sign] <;> linarith

theorem mass_nonnegative (correlation : ℝ) (nonnegative : 0 ≤ correlation) (bounded : correlation ≤ 1)
    (history : History) : 0 ≤ mass correlation history :=
  div_nonneg (mul_nonneg
    (mul_nonneg (factor_nonnegative correlation nonnegative bounded _)
      (factor_nonnegative correlation nonnegative bounded _))
    (factor_nonnegative correlation nonnegative bounded _)) (by norm_num)

theorem total_mass (correlation : ℝ) : ∑ history, mass correlation history = 1 := by
  norm_num [mass, errors, transition, sign, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

def law (correlation : ℝ) (nonnegative : 0 ≤ correlation) (bounded : correlation ≤ 1) : Prob History :=
  ⟨mass correlation, mass_nonnegative correlation nonnegative bounded, total_mass correlation⟩

theorem initial_uniform (correlation : ℝ) (nonnegative : 0 ≤ correlation) (bounded : correlation ≤ 1) :
    Prob.coarsen (law correlation nonnegative bounded) Prod.fst = initial := by
  apply Subtype.ext
  funext state
  rcases state with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;>
    norm_num [Prob.coarsen_apply, pushforward_eq_sum_ite, law, mass, errors,
      transition, sign, initial, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

theorem final_uniform (correlation : ℝ) (nonnegative : 0 ≤ correlation) (bounded : correlation ≤ 1) :
    Prob.coarsen (law correlation nonnegative bounded) Prod.snd = initial := by
  apply Subtype.ext
  funext state
  rcases state with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;>
    norm_num [Prob.coarsen_apply, pushforward_eq_sum_ite, law, mass, errors,
      transition, sign, initial, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

def coordinate (index : Fin 6) (history : History) : Bool :=
  ![history.1.1, history.1.2.1, history.1.2.2, history.2.1, history.2.2.1, history.2.2.2] index

theorem single_uniform (correlation : ℝ) (index : Fin 6) (value : Bool) :
    pushforward (mass correlation) (coordinate index) value = 1 / 2 := by
  fin_cases index <;> cases value <;>
    norm_num [pushforward_eq_sum_ite, mass, errors, transition, sign, coordinate,
      Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

theorem pairs_uniform (correlation : ℝ) (first second : Fin 6) (different : first ≠ second)
    (left right : Bool) :
    law2 (mass correlation) (coordinate first) (coordinate second) (left, right) = 1 / 4 := by
  fin_cases first <;> fin_cases second
  all_goals try exact (different rfl).elim
  all_goals cases left <;> cases right <;>
    norm_num [law2, pushforward_eq_sum_ite, mass, errors, transition, sign, coordinate,
      Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

theorem pairs_independent (correlation : ℝ) (nonnegative : 0 ≤ correlation) (bounded : correlation ≤ 1)
    (first second : Fin 6) (different : first ≠ second) (left right : Bool) :
    law2 (law correlation nonnegative bounded).1 (coordinate first) (coordinate second) (left, right) =
      pushforward (law correlation nonnegative bounded).1 (coordinate first) left *
        pushforward (law correlation nonnegative bounded).1 (coordinate second) right := by
  dsimp only [law]
  rw [pairs_uniform correlation first second different, single_uniform, single_uniform]
  norm_num

theorem single_sign_mean_zero (correlation : ℝ) (index : Fin 6) :
    (∑ history, mass correlation history * sign (coordinate index history)) = 0 := by
  rw [← sum_pushforward_mul (mass correlation) (coordinate index) sign]
  simp only [single_uniform]
  norm_num [Fintype.sum_bool, sign]

theorem cross_sign_moment_zero (correlation : ℝ) (first second : Fin 6) (different : first ≠ second) :
    (∑ history, mass correlation history *
      (sign (coordinate first history) * sign (coordinate second history))) = 0 := by
  rw [← sum_pushforward_mul (mass correlation)
    (fun history => (coordinate first history, coordinate second history))
    (fun pair : Bool × Bool => sign pair.1 * sign pair.2)]
  change (∑ pair, law2 (mass correlation) (coordinate first) (coordinate second) pair *
    (sign pair.1 * sign pair.2)) = 0
  rw [Fintype.sum_prod_type]
  simp only [pairs_uniform correlation first second different]
  norm_num [Fintype.sum_bool, sign]

theorem pair_information_zero (correlation : ℝ) (first second : Fin 6) (different : first ≠ second) :
    mutualInfo (mass correlation) (coordinate first) (coordinate second) = 0 := by
  have joint : law2 (mass correlation) (coordinate first) (coordinate second) =
      (fun _ : Bool × Bool => (1 : ℝ) / 4) :=
    funext fun pair => pairs_uniform correlation first second different pair.1 pair.2
  unfold mutualInfo
  rw [joint]
  simp only [single_uniform]
  norm_num [klSum_eq_sum]

theorem histories_dependent (correlation : ℝ) (positive : 0 < correlation) (bounded : correlation ≤ 1) :
    law correlation positive.le bounded ≠ productLaw initial initial := by
  intro same
  have masses := congrArg (fun distribution : Prob History =>
    distribution.1 ((false, false, false), (false, false, false))) same
  have large : 1 < (1 + correlation) ^ 3 := by
    nlinarith [sq_nonneg correlation, mul_nonneg positive.le (sq_nonneg correlation)]
  have entry : mass correlation ((false, false, false), (false, false, false)) =
      (1 + correlation) ^ 3 / 64 := by
    norm_num [mass, errors, transition, sign]
    ring
  change mass correlation _ = _ at masses
  rw [entry, productLaw_apply] at masses
  norm_num [initial] at masses
  nlinarith

theorem whole_history_information_positive (correlation : ℝ) (positive : 0 < correlation)
    (bounded : correlation ≤ 1) :
    0 < mutualInfo (law correlation positive.le bounded).1 Prod.fst Prod.snd := by
  let actual := law correlation positive.le bounded
  have fixed : actual ∈ fixedMarginals initial initial :=
    ⟨initial_uniform correlation positive.le bounded, final_uniform correlation positive.le bounded⟩
  rw [← fixed_marginal_kl_eq_mutualInfo initial initial actual fixed]
  have supported := fixed_marginals_supported initial initial actual fixed
  have nonnegative : 0 ≤ klSum actual.1 (productLaw initial initial).1 :=
    klSumOn_nonneg Finset.univ _ _ (fun x _ => actual.2.1 x)
      (fun x _ => (productLaw initial initial).2.1 x) (fun x _ => supported x)
      (by rw [actual.2.2, (productLaw initial initial).2.2])
  apply lt_of_le_of_ne nonnegative
  intro zero
  apply histories_dependent correlation positive bounded
  apply Subtype.ext
  funext x
  exact klSumOn_eq_zero_imp Finset.univ _ _ (fun y _ => actual.2.1 y)
    (fun y _ => (productLaw initial initial).2.1 y) (fun y _ => supported y)
    (by rw [actual.2.2, (productLaw initial initial).2.2]) zero.symm x (Finset.mem_univ x)

end Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.NoisyParity
