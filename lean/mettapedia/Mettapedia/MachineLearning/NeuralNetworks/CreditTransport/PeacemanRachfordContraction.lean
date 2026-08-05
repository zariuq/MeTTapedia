import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NonlinearForwardBackward

/-!
# Quantitative Peaceman--Rachford splitting

Winston and Kolter's monotone-equilibrium construction uses
Peaceman--Rachford splitting because, unlike an explicit forward step, its
stable-rate interval is not bounded above.  This file isolates the analytic
reason in a reusable Hilbert-space theorem.

An exact scaled resolvent of a monotone single-valued operator is firmly
nonexpansive, so its reflected resolvent is nonexpansive.  If the operator is
also strongly monotone and Lipschitz, its reflected resolvent is a strict
contraction for every positive rate.  Composing that contraction with the
reflected resolvent of another monotone operator gives a proof-carrying
Peaceman--Rachford solver.  Its decoded resolvent state is a zero of the
operator sum exactly when the reflected state is fixed.

The result is deliberately conditional on an exact resolvent equation and
global two-point operator bounds.  A final fixture records two sharp
boundaries: zero rate leaves the reflected map equal to the identity, and the
endpoint of the usual forward--backward rate interval can produce a period-two
orbit rather than linear convergence.

Source correspondence: Winston and Kolter, *Monotone Operator Equilibrium
Networks*, NeurIPS 2020, arXiv:2006.08591, especially equations (A5), (A9),
and (A10).  The strict forward--backward endpoint below sharpens the
non-strict inequality stated around equation (6).
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace PeacemanRachfordContraction

open scoped InnerProductSpace
open NonlinearResolvent
open NonlinearForwardBackward
open AmortizedInitialization

noncomputable section

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-! ## Scaled resolvents and reflected maps -/

/-- Exact resolvent equation for `(I + rate • operator)⁻¹`.  Existence is
carried as data rather than inferred from monotonicity alone. -/
def IsScaledResolventMapOf
    (rate : ℝ) (operator resolvent : State → State) : Prop :=
  ∀ input,
    resolvent input + rate • operator (resolvent input) = input

/-- The reflected resolvent, also called the Cayley map. -/
def reflectedResolvent (resolvent : State → State) (input : State) : State :=
  (2 : ℝ) • resolvent input - input

/-- Global norm nonexpansiveness. -/
def NonexpansiveMap (map : State → State) : Prop :=
  ∀ left right, ‖map left - map right‖ ≤ ‖left - right‖

/-- Global Lipschitzness with an explicit real-valued constant. -/
def LipschitzMap (constant : ℝ) (operator : State → State) : Prop :=
  ∀ left right,
    ‖operator left - operator right‖ ≤
      constant * ‖left - right‖

/-- Monotonicity makes every positive scaled shifted equation injective. -/
theorem monotone_scaled_shift_solution_unique
    {rate : ℝ} {operator : State → State}
    (rate_nonneg : 0 ≤ rate)
    (monotone : MonotoneMap operator)
    {left right input : State}
    (left_equation :
      left + rate • operator left = input)
    (right_equation :
      right + rate • operator right = input) :
    left = right := by
  let difference := left - right
  let operatorDifference := operator left - operator right
  have monotone_pair :
      0 ≤ ⟪difference, operatorDifference⟫_ℝ :=
    monotone left right
  have sum_zero :
      difference + rate • operatorDifference = 0 := by
    dsimp [difference, operatorDifference]
    calc
      (left - right) + rate • (operator left - operator right) =
          (left + rate • operator left) -
            (right + rate • operator right) := by module
      _ = input - input := by rw [left_equation, right_equation]
      _ = 0 := sub_self input
  have inner_zero :=
    congrArg (fun value : State => ⟪difference, value⟫_ℝ) sum_zero
  have self_nonpositive :
      ⟪difference, difference⟫_ℝ ≤ 0 := by
    rw [inner_add_right, real_inner_smul_right, inner_zero_right] at inner_zero
    nlinarith [mul_nonneg rate_nonneg monotone_pair]
  exact sub_eq_zero.mp (real_inner_self_nonpos.mp self_nonpositive)

/-- A monotone operator's exact scaled resolvent is firmly nonexpansive for
every nonnegative rate. -/
theorem firmlyNonexpansive_of_monotone_scaledResolvent
    {rate : ℝ} {operator resolvent : State → State}
    (rate_nonneg : 0 ≤ rate)
    (monotone : MonotoneMap operator)
    (resolvent_equation :
      IsScaledResolventMapOf rate operator resolvent) :
    FirmlyNonexpansiveMap resolvent := by
  intro left right
  let resolvedDifference := resolvent left - resolvent right
  let operatorDifference :=
    operator (resolvent left) - operator (resolvent right)
  have monotone_pair :
      0 ≤ ⟪resolvedDifference, operatorDifference⟫_ℝ :=
    monotone (resolvent left) (resolvent right)
  have input_difference :
      resolvedDifference + rate • operatorDifference = left - right := by
    dsimp [resolvedDifference, operatorDifference]
    calc
      (resolvent left - resolvent right) +
          rate •
            (operator (resolvent left) - operator (resolvent right)) =
        (resolvent left + rate • operator (resolvent left)) -
          (resolvent right + rate • operator (resolvent right)) := by
            module
      _ = left - right := by
        rw [resolvent_equation left, resolvent_equation right]
  calc
    ⟪resolvedDifference, resolvedDifference⟫_ℝ ≤
        ⟪resolvedDifference, resolvedDifference⟫_ℝ +
          rate * ⟪resolvedDifference, operatorDifference⟫_ℝ := by
            exact le_add_of_nonneg_right
              (mul_nonneg rate_nonneg monotone_pair)
    _ = ⟪resolvedDifference, left - right⟫_ℝ := by
      rw [← input_difference, inner_add_right, real_inner_smul_right]

/-- Reflecting a firmly nonexpansive map yields a nonexpansive map. -/
theorem reflectedResolvent_nonexpansive_of_firm
    {resolvent : State → State}
    (firm : FirmlyNonexpansiveMap resolvent) :
    NonexpansiveMap (reflectedResolvent resolvent) := by
  intro left right
  let resolvedDifference := resolvent left - resolvent right
  let inputDifference := left - right
  have firm_pair :
      ‖resolvedDifference‖ ^ 2 ≤
        ⟪resolvedDifference, inputDifference⟫_ℝ := by
    simpa [real_inner_self_eq_norm_sq] using firm left right
  have reflected_difference :
      reflectedResolvent resolvent left -
          reflectedResolvent resolvent right =
        (2 : ℝ) • resolvedDifference - inputDifference := by
    dsimp [reflectedResolvent, resolvedDifference, inputDifference]
    module
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [reflected_difference, norm_sub_sq_real, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    real_inner_smul_left, mul_pow]
  nlinarith

/-- A monotone scaled resolvent therefore has a nonexpansive reflected map. -/
theorem reflectedResolvent_nonexpansive
    {rate : ℝ} {operator resolvent : State → State}
    (rate_nonneg : 0 ≤ rate)
    (monotone : MonotoneMap operator)
    (resolvent_equation :
      IsScaledResolventMapOf rate operator resolvent) :
    NonexpansiveMap (reflectedResolvent resolvent) :=
  reflectedResolvent_nonexpansive_of_firm
    (firmlyNonexpansive_of_monotone_scaledResolvent
      rate_nonneg monotone resolvent_equation)

/-! ## Strong reflected-resolvent contraction -/

/-- Squared contraction factor for the reflected resolvent of an operator
that is `modulus`-strongly monotone and `lipschitz`-Lipschitz. -/
def reflectedContractionSq
    (rate modulus lipschitz : ℝ) : ℝ :=
  (1 + rate ^ 2 * lipschitz ^ 2 - 2 * rate * modulus) /
    (1 + rate ^ 2 * lipschitz ^ 2 + 2 * rate * modulus)

/-- Norm contraction factor obtained from `reflectedContractionSq`. -/
def reflectedContraction
    (rate modulus lipschitz : ℝ) : ℝ :=
  Real.sqrt (reflectedContractionSq rate modulus lipschitz)

theorem reflectedContractionSq_nonneg
    {rate modulus lipschitz : ℝ}
    (rate_nonneg : 0 ≤ rate)
    (modulus_nonneg : 0 ≤ modulus)
    (modulus_le_lipschitz : modulus ≤ lipschitz) :
    0 ≤ reflectedContractionSq rate modulus lipschitz := by
  have lipschitz_nonneg : 0 ≤ lipschitz :=
    modulus_nonneg.trans modulus_le_lipschitz
  have squares :
      modulus ^ 2 ≤ lipschitz ^ 2 :=
    (sq_le_sq₀ modulus_nonneg lipschitz_nonneg).2 modulus_le_lipschitz
  have numerator_nonneg :
      0 ≤ 1 + rate ^ 2 * lipschitz ^ 2 -
        2 * rate * modulus := by
    nlinarith [sq_nonneg (1 - rate * modulus),
      mul_nonneg (sq_nonneg rate) (sub_nonneg.mpr squares)]
  have denominator_pos :
      0 < 1 + rate ^ 2 * lipschitz ^ 2 +
        2 * rate * modulus := by
    nlinarith [mul_nonneg (sq_nonneg rate) (sq_nonneg lipschitz),
      mul_nonneg rate_nonneg modulus_nonneg]
  exact div_nonneg numerator_nonneg denominator_pos.le

theorem reflectedContraction_nonneg
    (rate modulus lipschitz : ℝ) :
    0 ≤ reflectedContraction rate modulus lipschitz :=
  Real.sqrt_nonneg _

/-- For every positive rate and positive strong-monotonicity modulus, the
reflected-resolvent factor is strictly below one.  There is no finite upper
rate boundary. -/
theorem reflectedContraction_lt_one
    {rate modulus lipschitz : ℝ}
    (rate_pos : 0 < rate)
    (modulus_pos : 0 < modulus)
    (modulus_le_lipschitz : modulus ≤ lipschitz) :
    reflectedContraction rate modulus lipschitz < 1 := by
  have coefficient_nonneg :=
    reflectedContractionSq_nonneg rate_pos.le modulus_pos.le
      modulus_le_lipschitz
  have denominator_pos :
      0 < 1 + rate ^ 2 * lipschitz ^ 2 +
        2 * rate * modulus := by
    nlinarith [sq_nonneg (rate * lipschitz)]
  rw [reflectedContraction]
  apply (Real.sqrt_lt coefficient_nonneg zero_le_one).2
  unfold reflectedContractionSq
  rw [one_pow]
  rw [div_lt_one denominator_pos]
  nlinarith [mul_pos rate_pos modulus_pos]

/-- Quantitative contraction of a strongly monotone Lipschitz operator's
reflected resolvent. -/
theorem reflectedResolvent_distance_le
    {rate modulus lipschitz : ℝ}
    {operator resolvent : State → State}
    (rate_nonneg : 0 ≤ rate)
    (modulus_nonneg : 0 ≤ modulus)
    (modulus_le_lipschitz : modulus ≤ lipschitz)
    (strongly_monotone : StronglyMonotoneMap modulus operator)
    (operator_lipschitz : LipschitzMap lipschitz operator)
    (resolvent_equation :
      IsScaledResolventMapOf rate operator resolvent)
    (left right : State) :
    ‖reflectedResolvent resolvent left -
        reflectedResolvent resolvent right‖ ≤
      reflectedContraction rate modulus lipschitz *
        ‖left - right‖ := by
  let resolvedDifference := resolvent left - resolvent right
  let operatorDifference :=
    operator (resolvent left) - operator (resolvent right)
  let common : ℝ := 1 + rate ^ 2 * lipschitz ^ 2
  let numerator : ℝ := common - 2 * rate * modulus
  let denominator : ℝ := common + 2 * rate * modulus
  have lipschitz_nonneg : 0 ≤ lipschitz :=
    modulus_nonneg.trans modulus_le_lipschitz
  have monotone_pair :
      modulus * ‖resolvedDifference‖ ^ 2 ≤
        ⟪resolvedDifference, operatorDifference⟫_ℝ :=
    strongly_monotone (resolvent left) (resolvent right)
  have lipschitz_pair :
      ‖operatorDifference‖ ≤
        lipschitz * ‖resolvedDifference‖ :=
    operator_lipschitz (resolvent left) (resolvent right)
  have lipschitz_pair_sq :
      ‖operatorDifference‖ ^ 2 ≤
        lipschitz ^ 2 * ‖resolvedDifference‖ ^ 2 := by
    have squared := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg lipschitz_nonneg (norm_nonneg _))).2 lipschitz_pair
    nlinarith [squared]
  have input_difference :
      left - right =
        resolvedDifference + rate • operatorDifference := by
    dsimp [resolvedDifference, operatorDifference]
    calc
      left - right =
          (resolvent left + rate • operator (resolvent left)) -
            (resolvent right + rate • operator (resolvent right)) := by
              rw [resolvent_equation left, resolvent_equation right]
      _ = (resolvent left - resolvent right) +
          rate •
            (operator (resolvent left) - operator (resolvent right)) := by
              module
  have reflected_difference :
      reflectedResolvent resolvent left -
          reflectedResolvent resolvent right =
        resolvedDifference - rate • operatorDifference := by
    calc
      reflectedResolvent resolvent left -
          reflectedResolvent resolvent right =
        (2 : ℝ) • resolvedDifference - (left - right) := by
          dsimp [reflectedResolvent, resolvedDifference]
          module
      _ = resolvedDifference - rate • operatorDifference := by
        rw [input_difference]
        module
  have common_nonneg : 0 ≤ common := by
    dsimp [common]
    nlinarith [mul_nonneg (sq_nonneg rate) (sq_nonneg lipschitz)]
  have denominator_pos : 0 < denominator := by
    have common_pos : 0 < common := by
      dsimp [common]
      nlinarith [mul_nonneg (sq_nonneg rate) (sq_nonneg lipschitz)]
    have scaled_nonneg : 0 ≤ 2 * rate * modulus :=
      mul_nonneg
        (mul_nonneg (by norm_num) rate_nonneg) modulus_nonneg
    dsimp [denominator]
    exact add_pos_of_pos_of_nonneg common_pos scaled_nonneg
  have numerator_nonneg : 0 ≤ numerator := by
    have squares :
        modulus ^ 2 ≤ lipschitz ^ 2 :=
      (sq_le_sq₀ modulus_nonneg lipschitz_nonneg).2 modulus_le_lipschitz
    dsimp [numerator, common]
    nlinarith [sq_nonneg (1 - rate * modulus),
      mul_nonneg (sq_nonneg rate) (sub_nonneg.mpr squares)]
  have weighted_operator_bound :
      modulus *
          (‖resolvedDifference‖ ^ 2 +
            rate ^ 2 * ‖operatorDifference‖ ^ 2) ≤
        common *
          ⟪resolvedDifference, operatorDifference⟫_ℝ := by
    have combined_norm_bound :
        ‖resolvedDifference‖ ^ 2 +
            rate ^ 2 * ‖operatorDifference‖ ^ 2 ≤
          common * ‖resolvedDifference‖ ^ 2 := by
      dsimp [common]
      nlinarith [mul_nonneg (sq_nonneg rate)
        (sub_nonneg.mpr lipschitz_pair_sq)]
    calc
      modulus *
          (‖resolvedDifference‖ ^ 2 +
            rate ^ 2 * ‖operatorDifference‖ ^ 2) ≤
        modulus * (common * ‖resolvedDifference‖ ^ 2) :=
          mul_le_mul_of_nonneg_left combined_norm_bound modulus_nonneg
      _ = common * (modulus * ‖resolvedDifference‖ ^ 2) := by ring
      _ ≤ common *
          ⟪resolvedDifference, operatorDifference⟫_ℝ :=
        mul_le_mul_of_nonneg_left monotone_pair common_nonneg
  have squared_cross_bound :
      denominator *
          ‖resolvedDifference - rate • operatorDifference‖ ^ 2 ≤
        numerator *
          ‖resolvedDifference + rate • operatorDifference‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_add_sq_real,
      real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg rate_nonneg, mul_pow]
    dsimp [denominator, numerator]
    nlinarith [mul_nonneg rate_nonneg
      (sub_nonneg.mpr weighted_operator_bound)]
  have squared_ratio_bound :
      ‖resolvedDifference - rate • operatorDifference‖ ^ 2 ≤
        reflectedContractionSq rate modulus lipschitz *
          ‖resolvedDifference + rate • operatorDifference‖ ^ 2 := by
    unfold reflectedContractionSq
    dsimp [denominator, numerator, common] at denominator_pos
    dsimp [denominator, numerator, common] at squared_cross_bound
    calc
      ‖resolvedDifference - rate • operatorDifference‖ ^ 2 ≤
          ((1 + rate ^ 2 * lipschitz ^ 2 -
              2 * rate * modulus) *
            ‖resolvedDifference + rate • operatorDifference‖ ^ 2) /
              (1 + rate ^ 2 * lipschitz ^ 2 +
                2 * rate * modulus) :=
        (le_div_iff₀ denominator_pos).2 (by
          nlinarith [squared_cross_bound])
      _ =
          (1 + rate ^ 2 * lipschitz ^ 2 -
              2 * rate * modulus) /
            (1 + rate ^ 2 * lipschitz ^ 2 +
              2 * rate * modulus) *
            ‖resolvedDifference + rate • operatorDifference‖ ^ 2 := by
        ring
  have coefficient_nonneg :=
    reflectedContractionSq_nonneg rate_nonneg modulus_nonneg
      modulus_le_lipschitz
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg
      (reflectedContraction_nonneg rate modulus lipschitz)
      (norm_nonneg _))).1
  rw [reflected_difference, input_difference, mul_pow,
    show reflectedContraction rate modulus lipschitz ^ 2 =
        reflectedContractionSq rate modulus lipschitz by
      exact Real.sq_sqrt coefficient_nonneg]
  exact squared_ratio_bound

/-- Package the quantitative result as the repository's standard contraction
certificate. -/
def reflectedResolventContractionCertificate
    {rate modulus lipschitz : ℝ}
    {operator resolvent : State → State}
    (rate_pos : 0 < rate)
    (modulus_pos : 0 < modulus)
    (modulus_le_lipschitz : modulus ≤ lipschitz)
    (strongly_monotone : StronglyMonotoneMap modulus operator)
    (operator_lipschitz : LipschitzMap lipschitz operator)
    (resolvent_equation :
      IsScaledResolventMapOf rate operator resolvent) :
    ContractionCertificate (reflectedResolvent resolvent) where
  factor := reflectedContraction rate modulus lipschitz
  factor_nonneg := reflectedContraction_nonneg _ _ _
  factor_lt_one :=
    reflectedContraction_lt_one rate_pos modulus_pos modulus_le_lipschitz
  contracts :=
    reflectedResolvent_distance_le rate_pos.le modulus_pos.le
      modulus_le_lipschitz strongly_monotone operator_lipschitz
      resolvent_equation

/-! ## Peaceman--Rachford composition and decoded zeros -/

/-- One Peaceman--Rachford step: reflect through the second operator, then
through the strongly monotone first operator. -/
def peacemanRachfordStep
    (firstResolvent secondResolvent : State → State)
    (state : State) : State :=
  reflectedResolvent firstResolvent
    (reflectedResolvent secondResolvent state)

/-- A contractive reflected resolvent composed after a nonexpansive reflected
resolvent retains the same contraction factor. -/
def peacemanRachfordContractionCertificate
    {rate modulus lipschitz : ℝ}
    {firstOperator firstResolvent secondOperator secondResolvent :
      State → State}
    (rate_pos : 0 < rate)
    (modulus_pos : 0 < modulus)
    (modulus_le_lipschitz : modulus ≤ lipschitz)
    (first_strongly_monotone :
      StronglyMonotoneMap modulus firstOperator)
    (first_lipschitz : LipschitzMap lipschitz firstOperator)
    (first_resolvent :
      IsScaledResolventMapOf rate firstOperator firstResolvent)
    (second_monotone : MonotoneMap secondOperator)
    (second_resolvent :
      IsScaledResolventMapOf rate secondOperator secondResolvent) :
    ContractionCertificate
      (peacemanRachfordStep firstResolvent secondResolvent) where
  factor := reflectedContraction rate modulus lipschitz
  factor_nonneg := reflectedContraction_nonneg _ _ _
  factor_lt_one :=
    reflectedContraction_lt_one rate_pos modulus_pos modulus_le_lipschitz
  contracts := by
    intro left right
    calc
      ‖peacemanRachfordStep firstResolvent secondResolvent left -
          peacemanRachfordStep firstResolvent secondResolvent right‖ ≤
        reflectedContraction rate modulus lipschitz *
          ‖reflectedResolvent secondResolvent left -
            reflectedResolvent secondResolvent right‖ :=
        reflectedResolvent_distance_le rate_pos.le modulus_pos.le
          modulus_le_lipschitz first_strongly_monotone first_lipschitz
          first_resolvent _ _
      _ ≤ reflectedContraction rate modulus lipschitz *
          ‖left - right‖ := by
        exact mul_le_mul_of_nonneg_left
          (reflectedResolvent_nonexpansive rate_pos.le second_monotone
            second_resolvent left right)
          (reflectedContraction_nonneg _ _ _)

/-- Decoding a fixed reflected state through the second resolvent produces a
zero of the operator sum. -/
theorem decoded_sum_zero_of_peacemanRachford_fixed
    {rate : ℝ}
    {firstOperator firstResolvent secondOperator secondResolvent :
      State → State}
    (rate_ne_zero : rate ≠ 0)
    (first_resolvent :
      IsScaledResolventMapOf rate firstOperator firstResolvent)
    (second_resolvent :
      IsScaledResolventMapOf rate secondOperator secondResolvent)
    {state : State}
    (fixed :
      peacemanRachfordStep firstResolvent secondResolvent state = state) :
    firstOperator (secondResolvent state) +
        secondOperator (secondResolvent state) = 0 := by
  let decoded := secondResolvent state
  let reflected := reflectedResolvent secondResolvent state
  have second_equation :
      decoded + rate • secondOperator decoded = state :=
    second_resolvent state
  have reflected_eq :
      reflected = decoded - rate • secondOperator decoded := by
    change (2 : ℝ) • decoded - state =
      decoded - rate • secondOperator decoded
    rw [← second_equation]
    module
  have first_reflected :
      reflectedResolvent firstResolvent reflected = state := by
    simpa [peacemanRachfordStep, reflected] using fixed
  have first_resolved_eq :
      firstResolvent reflected = decoded := by
    dsimp [reflectedResolvent] at first_reflected
    have doubled :
        (2 : ℝ) • firstResolvent reflected = (2 : ℝ) • decoded := by
      calc
        (2 : ℝ) • firstResolvent reflected =
            state + reflected :=
          sub_eq_iff_eq_add.mp first_reflected
        _ = (decoded + rate • secondOperator decoded) +
            (decoded - rate • secondOperator decoded) := by
          rw [second_equation, reflected_eq]
        _ = (2 : ℝ) • decoded := by module
    have scaled_difference :
        (2 : ℝ) • (firstResolvent reflected - decoded) = 0 := by
      rw [smul_sub, doubled, sub_self]
    have difference_zero :
        firstResolvent reflected - decoded = 0 :=
      (smul_eq_zero.mp scaled_difference).resolve_left
        (by norm_num : (2 : ℝ) ≠ 0)
    exact sub_eq_zero.mp difference_zero
  have first_equation := first_resolvent reflected
  rw [first_resolved_eq, reflected_eq] at first_equation
  have scaled_sum :
      rate •
        (firstOperator decoded + secondOperator decoded) = 0 := by
    calc
      rate •
          (firstOperator decoded + secondOperator decoded) =
        rate • firstOperator decoded +
          rate • secondOperator decoded := smul_add _ _ _
      _ = (decoded + rate • firstOperator decoded) -
          (decoded - rate • secondOperator decoded) := by module
      _ = 0 := by rw [first_equation]; simp
  exact (smul_eq_zero.mp scaled_sum).resolve_left rate_ne_zero

/-- Conversely, every zero of the sum induces a fixed reflected state when
both shifted equations are unique. -/
theorem peacemanRachford_fixed_of_sum_zero
    {rate : ℝ}
    {firstOperator firstResolvent secondOperator secondResolvent :
      State → State}
    (rate_pos : 0 < rate)
    (first_monotone : MonotoneMap firstOperator)
    (second_monotone : MonotoneMap secondOperator)
    (first_resolvent :
      IsScaledResolventMapOf rate firstOperator firstResolvent)
    (second_resolvent :
      IsScaledResolventMapOf rate secondOperator secondResolvent)
    {decoded : State}
    (sum_zero :
      firstOperator decoded + secondOperator decoded = 0) :
    peacemanRachfordStep firstResolvent secondResolvent
        (decoded + rate • secondOperator decoded) =
      decoded + rate • secondOperator decoded := by
  let state := decoded + rate • secondOperator decoded
  have second_decodes :
      secondResolvent state = decoded := by
    apply monotone_scaled_shift_solution_unique rate_pos.le second_monotone
      (second_resolvent state)
    exact rfl
  have reflected_second :
      reflectedResolvent secondResolvent state =
        decoded + rate • firstOperator decoded := by
    rw [reflectedResolvent, second_decodes]
    dsimp [state]
    have operator_balance :
        firstOperator decoded = -secondOperator decoded := by
      exact eq_neg_of_add_eq_zero_left sum_zero
    rw [operator_balance]
    module
  have first_decodes :
      firstResolvent
          (decoded + rate • firstOperator decoded) = decoded := by
    apply monotone_scaled_shift_solution_unique rate_pos.le first_monotone
      (first_resolvent
        (decoded + rate • firstOperator decoded))
    exact rfl
  unfold peacemanRachfordStep
  rw [reflected_second, reflectedResolvent, first_decodes]
  have operator_balance :
      firstOperator decoded = -secondOperator decoded := by
    exact eq_neg_of_add_eq_zero_left sum_zero
  rw [operator_balance]
  module

/-! ## Exact scalar fixtures and sharp boundaries -/

def identityOperator (state : ℝ) : ℝ := state

def zeroOperator (_state : ℝ) : ℝ := 0

def identityScaledResolvent (rate state : ℝ) : ℝ :=
  state / (1 + rate)

def zeroScaledResolvent (_rate state : ℝ) : ℝ := state

theorem identityOperator_stronglyMonotone :
    StronglyMonotoneMap 1 identityOperator := by
  intro left right
  simp [identityOperator, Real.norm_eq_abs, sq_abs]

theorem identityOperator_lipschitz :
    LipschitzMap 1 identityOperator := by
  intro left right
  simp [identityOperator]

theorem identityScaledResolvent_equation
    {rate : ℝ} (not_singular : rate ≠ -1) :
    IsScaledResolventMapOf rate identityOperator
      (identityScaledResolvent rate) := by
  intro state
  have denominator_ne : 1 + rate ≠ 0 := by
    intro denominator_zero
    apply not_singular
    linarith
  change state / (1 + rate) +
    rate * (state / (1 + rate)) = state
  field_simp [denominator_ne]

theorem zeroOperator_monotone :
    MonotoneMap zeroOperator := by
  intro left right
  simp [zeroOperator]

theorem zeroScaledResolvent_equation (rate : ℝ) :
    IsScaledResolventMapOf rate zeroOperator
      (zeroScaledResolvent rate) := by
  intro state
  simp [zeroScaledResolvent, zeroOperator]

/-- At positive unit rate, the identity/zero split reaches its unique decoded
zero in one Peaceman--Rachford step. -/
theorem identity_zero_peacemanRachford_unit :
    peacemanRachfordStep
      (identityScaledResolvent 1) (zeroScaledResolvent 1) =
        fun _state : ℝ => 0 := by
  funext state
  simp [peacemanRachfordStep, reflectedResolvent,
    identityScaledResolvent, zeroScaledResolvent]
  ring

/-- Positive-rate necessity is sharp: at rate zero even a strongly monotone
identity operator has identity reflected dynamics. -/
theorem identity_reflection_zero_rate :
    reflectedResolvent (identityScaledResolvent 0) =
      fun state : ℝ => state := by
  funext state
  simp [reflectedResolvent, identityScaledResolvent]
  ring

theorem identity_reflection_zero_rate_not_contractive :
    ¬ ∃ _certificate :
        ContractionCertificate
          (reflectedResolvent (identityScaledResolvent 0)),
      True := by
  rintro ⟨certificate, -⟩
  have contracted := certificate.contracts 1 0
  norm_num [reflectedResolvent, identityScaledResolvent,
    Real.norm_eq_abs] at contracted
  exact (not_lt_of_ge contracted) certificate.factor_lt_one

/-- Explicit forward splitting at the non-strict endpoint `rate = 2m/L²`
can be a sign flip. -/
def endpointForwardStep (state : ℝ) : ℝ :=
  state - 2 * identityOperator state

theorem endpointForwardStep_eq_neg :
    endpointForwardStep = fun state : ℝ => -state := by
  funext state
  simp [endpointForwardStep, identityOperator]
  ring

theorem endpointForwardStep_period_two (state : ℝ) :
    endpointForwardStep (endpointForwardStep state) = state := by
  simp only [endpointForwardStep, identityOperator]
  ring

theorem endpointForwardStep_not_converged_after_two :
    endpointForwardStep (endpointForwardStep 1) ≠
      endpointForwardStep 1 := by
  norm_num [endpointForwardStep, identityOperator]

#print axioms reflectedResolvent_distance_le
#print axioms peacemanRachfordContractionCertificate
#print axioms decoded_sum_zero_of_peacemanRachford_fixed
#print axioms peacemanRachford_fixed_of_sum_zero
#print axioms identity_zero_peacemanRachford_unit
#print axioms endpointForwardStep_not_converged_after_two

end

end PeacemanRachfordContraction

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
