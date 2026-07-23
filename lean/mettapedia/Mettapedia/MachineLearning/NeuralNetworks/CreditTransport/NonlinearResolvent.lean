import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OperatorSplitting

/-!
# Nonlinear monotone resolvents

The linear matrix classifier has a global nonlinear analogue that does not
require a scalar potential.  A resolvent is specified by its exact equation,
and a separately proved monotonicity property supplies firm
nonexpansiveness, uniqueness of each implicit solve, and equality between
resolvent fixed points and operator zeros.

A piecewise-linear positive-part operator provides a globally nonlinear
positive fixture.  An anti-monotone linear operator still has an exact
resolvent, but that resolvent is not firmly nonexpansive; thus the algebraic
inverse equation alone is not a convergence certificate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace NonlinearResolvent

open scoped InnerProductSpace

noncomputable section

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- Global monotonicity of a single-valued operator on a real inner-product
space. -/
def MonotoneMap (operator : State → State) : Prop :=
  ∀ x y, 0 ≤ ⟪x - y, operator x - operator y⟫_ℝ

/-- Strong monotonicity with an explicit modulus.  Keeping the modulus in the
definition makes the observable residual-to-distance constant available to
downstream solver certificates. -/
def StronglyMonotoneMap (modulus : ℝ) (operator : State → State) : Prop :=
  ∀ x y,
    modulus * ‖x - y‖ ^ 2 ≤
      ⟪x - y, operator x - operator y⟫_ℝ

/-- A quantitative lower bound on possible anti-monotonicity.  `rho = 0`
recovers ordinary monotonicity; positive `rho` permits bounded negative
curvature. -/
def HypomonotoneMap (rho : ℝ) (operator : State → State) : Prop :=
  ∀ x y,
    -(rho * ‖x - y‖ ^ 2) ≤
      ⟪x - y, operator x - operator y⟫_ℝ

theorem hypomonotone_zero_iff_monotone
    {operator : State → State} :
    HypomonotoneMap 0 operator ↔ MonotoneMap operator := by
  simp [HypomonotoneMap, MonotoneMap]

/-- Adding a scalar identity term dominates a `rho`-hypomonotone operator
with strong-monotonicity modulus `precision - rho`. -/
theorem stronglyMonotone_add_smul_id
    {rho precision : ℝ} {operator : State → State}
    (hypomonotone : HypomonotoneMap rho operator) :
    StronglyMonotoneMap (precision - rho)
      (fun state => operator state + precision • state) := by
  intro x y
  have hlower := hypomonotone x y
  have hrewrite :
      (operator x + precision • x) - (operator y + precision • y) =
        (operator x - operator y) + precision • (x - y) := by
    rw [smul_sub]
    abel
  rw [hrewrite, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  nlinarith

/-- A nonnegative strong-monotonicity modulus implies ordinary monotonicity. -/
theorem StronglyMonotoneMap.monotone
    {modulus : ℝ} {operator : State → State}
    (stronglyMonotone : StronglyMonotoneMap modulus operator)
    (hmodulus : 0 ≤ modulus) :
    MonotoneMap operator := by
  intro x y
  have hstrong := stronglyMonotone x y
  have hnonnegative : 0 ≤ modulus * ‖x - y‖ ^ 2 :=
    mul_nonneg hmodulus (sq_nonneg ‖x - y‖)
  exact hnonnegative.trans hstrong

/-- For a strongly monotone operator, its observable norm at a point bounds
distance to any exact zero. -/
theorem StronglyMonotoneMap.distance_root_le_norm_div
    {modulus : ℝ} {operator : State → State}
    (stronglyMonotone : StronglyMonotoneMap modulus operator)
    (hmodulus : 0 < modulus)
    {root state : State} (hroot : operator root = 0) :
    ‖state - root‖ ≤ ‖operator state‖ / modulus := by
  by_cases hstate : state = root
  · simp only [hstate, sub_self, norm_zero]
    positivity
  · have hdistance : 0 < ‖state - root‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hstate)
    have hstrong := stronglyMonotone state root
    rw [hroot, sub_zero] at hstrong
    have hupper :
        ⟪state - root, operator state⟫_ℝ ≤
          ‖state - root‖ * ‖operator state‖ :=
      real_inner_le_norm (state - root) (operator state)
    have hproduct :
        modulus * ‖state - root‖ ≤ ‖operator state‖ := by
      nlinarith [sq_nonneg ‖state - root‖]
    exact (le_div_iff₀ hmodulus).2 (by simpa [mul_comm] using hproduct)

/-- A strongly monotone operator with positive modulus has at most one zero. -/
theorem StronglyMonotoneMap.root_unique
    {modulus : ℝ} {operator : State → State}
    (stronglyMonotone : StronglyMonotoneMap modulus operator)
    (hmodulus : 0 < modulus)
    {left right : State}
    (hleft : operator left = 0) (hright : operator right = 0) :
    left = right := by
  have hdistance := stronglyMonotone.distance_root_le_norm_div
    hmodulus hright (state := left)
  rw [hleft, norm_zero, zero_div] at hdistance
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hdistance (norm_nonneg _)))

/-- Exact unit resolvent equation.  Existence is data: every input is mapped
to a state whose implicit operator equation reconstructs that input. -/
def IsUnitResolventMapOf
    (operator resolvent : State → State) : Prop :=
  ∀ x, resolvent x + operator (resolvent x) = x

/-- Global two-point firm nonexpansiveness. -/
def FirmlyNonexpansiveMap (resolvent : State → State) : Prop :=
  ∀ x y,
    ⟪resolvent x - resolvent y, resolvent x - resolvent y⟫_ℝ ≤
      ⟪resolvent x - resolvent y, x - y⟫_ℝ

/-- A monotone operator has at most one solution of each shifted equation
`u + A u = x`. -/
theorem monotone_shift_solution_unique
    {operator : State → State}
    (monotone : MonotoneMap operator)
    {u v x : State}
    (hu : u + operator u = x)
    (hv : v + operator v = x) :
    u = v := by
  let difference := u - v
  let operatorDifference := operator u - operator v
  have hmonotone : 0 ≤ ⟪difference, operatorDifference⟫_ℝ :=
    monotone u v
  have hsum : difference + operatorDifference = 0 := by
    dsimp [difference, operatorDifference]
    calc
      (u - v) + (operator u - operator v) =
          (u + operator u) - (v + operator v) := by abel
      _ = x - x := by rw [hu, hv]
      _ = 0 := sub_self x
  have hinner := congrArg (fun state : State => ⟪difference, state⟫_ℝ) hsum
  have hselfNonpositive : ⟪difference, difference⟫_ℝ ≤ 0 := by
    simp only [inner_add_right, inner_zero_right] at hinner
    linarith
  have hdifference : difference = 0 :=
    real_inner_self_nonpos.mp hselfNonpositive
  exact sub_eq_zero.mp hdifference

/-- The exact resolvent of a monotone operator is globally firmly
nonexpansive. -/
theorem firmlyNonexpansive_of_monotone_resolvent
    {operator resolvent : State → State}
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator resolvent) :
    FirmlyNonexpansiveMap resolvent := by
  intro x y
  let resolvedDifference := resolvent x - resolvent y
  let operatorDifference := operator (resolvent x) - operator (resolvent y)
  have hmonotone : 0 ≤ ⟪resolvedDifference, operatorDifference⟫_ℝ :=
    monotone (resolvent x) (resolvent y)
  have hdifference :
      resolvedDifference + operatorDifference = x - y := by
    dsimp [resolvedDifference, operatorDifference]
    calc
      (resolvent x - resolvent y) +
          (operator (resolvent x) - operator (resolvent y)) =
        (resolvent x + operator (resolvent x)) -
          (resolvent y + operator (resolvent y)) := by abel
      _ = x - y := by rw [resolventEquation x, resolventEquation y]
  calc
    ⟪resolvedDifference, resolvedDifference⟫_ℝ ≤
        ⟪resolvedDifference, resolvedDifference⟫_ℝ +
          ⟪resolvedDifference, operatorDifference⟫_ℝ := by linarith
    _ = ⟪resolvedDifference, x - y⟫_ℝ := by
      rw [← hdifference]
      simp only [inner_add_right]

/-- Resolvent fixed points are exactly zeros of a monotone operator.  The
reverse implication uses uniqueness of the shifted implicit equation, not an
unstated inverse-function assumption. -/
theorem fixed_iff_operator_zero_of_monotone_resolvent
    {operator resolvent : State → State}
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator resolvent)
    (x : State) :
    resolvent x = x ↔ operator x = 0 := by
  constructor
  · intro hfixed
    have hequation := resolventEquation x
    rw [hfixed] at hequation
    exact add_eq_left.mp hequation
  · intro hzero
    apply monotone_shift_solution_unique monotone (resolventEquation x)
    simp [hzero]

/-! ## A globally nonlinear positive fixture -/

/-- Positive-part operator on the line. -/
def positivePartOperator (x : ℝ) : ℝ := max x 0

/-- Exact unit resolvent of the positive-part operator. -/
def positivePartResolvent (x : ℝ) : ℝ :=
  if x ≤ 0 then x else x / 2

theorem positivePartOperator_monotone :
    MonotoneMap positivePartOperator := by
  intro x y
  simp only [positivePartOperator, RCLike.inner_apply, conj_trivial]
  by_cases hxy : x ≤ y
  · have hmax : max x 0 ≤ max y 0 := max_le_max_right 0 hxy
    nlinarith
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hmax : max y 0 ≤ max x 0 := max_le_max_right 0 hyx
    nlinarith

theorem positivePart_resolventEquation :
    IsUnitResolventMapOf positivePartOperator positivePartResolvent := by
  intro x
  by_cases hx : x ≤ 0
  · simp [positivePartResolvent, positivePartOperator, hx]
  · have hxPositive : 0 < x := lt_of_not_ge hx
    have hxHalf : 0 ≤ x / 2 := by positivity
    simp [positivePartResolvent, positivePartOperator, hx, max_eq_left hxHalf]

theorem positivePartResolvent_firmlyNonexpansive :
    FirmlyNonexpansiveMap positivePartResolvent :=
  firmlyNonexpansive_of_monotone_resolvent
    positivePartOperator_monotone positivePart_resolventEquation

theorem positivePartResolvent_fixed_iff (x : ℝ) :
    positivePartResolvent x = x ↔ x ≤ 0 := by
  rw [fixed_iff_operator_zero_of_monotone_resolvent
    positivePartOperator_monotone positivePart_resolventEquation]
  simp [positivePartOperator]

/-- The fixture is genuinely nonlinear: midpoint preservation fails. -/
theorem positivePartOperator_not_midpointLinear :
    positivePartOperator ((-1 + 1) / 2) ≠
      (positivePartOperator (-1) + positivePartOperator 1) / 2 := by
  norm_num [positivePartOperator]

/-! ## Monotonicity is necessary -/

/-- Anti-monotone operator with an algebraically exact resolvent. -/
def antiMonotoneOperator (x : ℝ) : ℝ := -2 * x

def antiMonotoneResolvent (x : ℝ) : ℝ := -x

theorem antiMonotone_resolventEquation :
    IsUnitResolventMapOf antiMonotoneOperator antiMonotoneResolvent := by
  intro x
  simp [antiMonotoneOperator, antiMonotoneResolvent]
  ring

theorem antiMonotoneOperator_not_monotone :
    ¬ MonotoneMap antiMonotoneOperator := by
  intro hmonotone
  have h := hmonotone 1 0
  norm_num [antiMonotoneOperator] at h

/-- The resolvent equation without monotonicity does not imply firm
nonexpansiveness. -/
theorem resolventEquation_alone_not_firmlyNonexpansive :
    IsUnitResolventMapOf antiMonotoneOperator antiMonotoneResolvent ∧
      ¬ FirmlyNonexpansiveMap antiMonotoneResolvent := by
  refine ⟨antiMonotone_resolventEquation, ?_⟩
  intro hfirm
  have h := hfirm 1 0
  norm_num [antiMonotoneResolvent] at h

#print axioms monotone_shift_solution_unique
#print axioms stronglyMonotone_add_smul_id
#print axioms hypomonotone_zero_iff_monotone
#print axioms StronglyMonotoneMap.distance_root_le_norm_div
#print axioms StronglyMonotoneMap.root_unique
#print axioms firmlyNonexpansive_of_monotone_resolvent
#print axioms fixed_iff_operator_zero_of_monotone_resolvent
#print axioms positivePartOperator_monotone
#print axioms positivePartResolvent_firmlyNonexpansive
#print axioms positivePartOperator_not_midpointLinear
#print axioms resolventEquation_alone_not_firmlyNonexpansive

end

end NonlinearResolvent

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
