import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FinitePrecisionExpressionCertificate

/-!
# Kernel-checked interval evaluation

This file reconstructs the algebraic inclusion theorem and splitting rule from
Daumas, Lester, and Muñoz, *Verified Real Number Calculations: A Library for
Interval Arithmetic* (2007), Sections III--IV.

The existing scalar-expression language is reused.  A certificate carries
asymmetric lower and upper bounds, composes the paper's endpoint operations
for addition and multiplication, and accepts a uniform enclosure at an external
unary node.  The proof kernel then derives inclusion of the exact real
evaluation by structural induction.

The interval dependency effect remains explicit.  Evaluating `2 * x - x`
over `[0, 1]` yields `[-1, 2]`, although its exact real value is `x`.
Splitting the input at `1/2` improves the enclosing hull to
`[-1/2, 3/2]`, but still does not recover the algebraic identity.

This module does not model floating-point rounding or claim completeness of
interval search.  Runtime roundoff remains a separate local certificate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CertifiedIntervalEvaluation

noncomputable section

open FinitePrecisionExpressionCertificate

universe u

/-- A closed real interval.  Improper endpoints denote an empty interval,
matching the source convention; every membership proof itself establishes
properness. -/
structure ClosedInterval where
  lower : ℝ
  upper : ℝ

namespace ClosedInterval

/-- Membership in a closed interval. -/
def Contains (interval : ClosedInterval) (value : ℝ) : Prop :=
  interval.lower ≤ value ∧ value ≤ interval.upper

/-- The point interval `[value, value]`. -/
def point (value : ℝ) : ClosedInterval :=
  ⟨value, value⟩

/-- The smallest endpoint hull of two intervals. -/
def hull (left right : ClosedInterval) : ClosedInterval :=
  ⟨min left.lower right.lower, max left.upper right.upper⟩

/-- Endpoint interval addition. -/
def add (left right : ClosedInterval) : ClosedInterval :=
  ⟨left.lower + right.lower, left.upper + right.upper⟩

/-- Endpoint interval negation. -/
def negate (interval : ClosedInterval) : ClosedInterval :=
  ⟨-interval.upper, -interval.lower⟩

/-- Endpoint interval subtraction. -/
def subtract (left right : ClosedInterval) : ClosedInterval :=
  add left (negate right)

/-- The lower hull of the four endpoint products. -/
def productLower (left right : ClosedInterval) : ℝ :=
  min (min (left.lower * right.lower) (left.lower * right.upper))
    (min (left.upper * right.lower) (left.upper * right.upper))

/-- The upper hull of the four endpoint products. -/
def productUpper (left right : ClosedInterval) : ℝ :=
  max (max (left.lower * right.lower) (left.lower * right.upper))
    (max (left.upper * right.lower) (left.upper * right.upper))

/-- Endpoint interval multiplication. -/
def multiply (left right : ClosedInterval) : ClosedInterval :=
  ⟨productLower left right, productUpper left right⟩

/-- Boolean masking as an interval operation. -/
def mask (active : Bool) (interval : ClosedInterval) : ClosedInterval :=
  if active then interval else point 0

/-- Endpoint width.  It is nonnegative for every inhabited interval. -/
def width (interval : ClosedInterval) : ℝ :=
  interval.upper - interval.lower

theorem contains_point (value : ℝ) : (point value).Contains value := by
  exact ⟨le_rfl, le_rfl⟩

theorem proper_of_contains {interval : ClosedInterval} {value : ℝ}
    (membership : interval.Contains value) :
    interval.lower ≤ interval.upper :=
  membership.1.trans membership.2

theorem contains_hull_left {left right : ClosedInterval} {value : ℝ}
    (membership : left.Contains value) :
    (hull left right).Contains value := by
  exact ⟨(min_le_left _ _).trans membership.1,
    membership.2.trans (le_max_left _ _)⟩

theorem contains_hull_right {left right : ClosedInterval} {value : ℝ}
    (membership : right.Contains value) :
    (hull left right).Contains value := by
  exact ⟨(min_le_right _ _).trans membership.1,
    membership.2.trans (le_max_right _ _)⟩

theorem contains_add {left right : ClosedInterval} {x y : ℝ}
    (leftMembership : left.Contains x)
    (rightMembership : right.Contains y) :
    (add left right).Contains (x + y) := by
  exact ⟨add_le_add leftMembership.1 rightMembership.1,
    add_le_add leftMembership.2 rightMembership.2⟩

theorem contains_negate {interval : ClosedInterval} {value : ℝ}
    (membership : interval.Contains value) :
    (negate interval).Contains (-value) := by
  exact ⟨neg_le_neg membership.2, neg_le_neg membership.1⟩

theorem contains_subtract {left right : ClosedInterval} {x y : ℝ}
    (leftMembership : left.Contains x)
    (rightMembership : right.Contains y) :
    (subtract left right).Contains (x - y) := by
  simpa [subtract, sub_eq_add_neg] using
    contains_add leftMembership (contains_negate rightMembership)

private theorem productLower_le_lower_lower
    (left right : ClosedInterval) :
    productLower left right ≤ left.lower * right.lower := by
  simp [productLower]

private theorem productLower_le_lower_upper
    (left right : ClosedInterval) :
    productLower left right ≤ left.lower * right.upper := by
  simp [productLower]

private theorem productLower_le_upper_lower
    (left right : ClosedInterval) :
    productLower left right ≤ left.upper * right.lower := by
  simp [productLower]

private theorem productLower_le_upper_upper
    (left right : ClosedInterval) :
    productLower left right ≤ left.upper * right.upper := by
  simp [productLower]

private theorem lower_lower_le_productUpper
    (left right : ClosedInterval) :
    left.lower * right.lower ≤ productUpper left right := by
  simp [productUpper]

private theorem lower_upper_le_productUpper
    (left right : ClosedInterval) :
    left.lower * right.upper ≤ productUpper left right := by
  simp [productUpper]

private theorem upper_lower_le_productUpper
    (left right : ClosedInterval) :
    left.upper * right.lower ≤ productUpper left right := by
  simp [productUpper]

private theorem upper_upper_le_productUpper
    (left right : ClosedInterval) :
    left.upper * right.upper ≤ productUpper left right := by
  simp [productUpper]

/-- Proposition 9's multiplication inclusion property, using the exact hull
of the four endpoint products. -/
theorem contains_multiply {left right : ClosedInterval} {x y : ℝ}
    (leftMembership : left.Contains x)
    (rightMembership : right.Contains y) :
    (multiply left right).Contains (x * y) := by
  rcases leftMembership with ⟨leftLower, leftUpper⟩
  rcases rightMembership with ⟨rightLower, rightUpper⟩
  constructor
  · change productLower left right ≤ x * y
    by_cases xNonnegative : 0 ≤ x
    · by_cases yNonnegative : 0 ≤ y
      · by_cases lowerNonnegative : 0 ≤ left.lower
        · exact (productLower_le_lower_lower left right).trans
            ((mul_le_mul_of_nonneg_left rightLower lowerNonnegative).trans
              (mul_le_mul_of_nonneg_right leftLower yNonnegative))
        · have lowerNonpositive : left.lower ≤ 0 := le_of_not_ge lowerNonnegative
          exact (productLower_le_lower_upper left right).trans
            ((mul_le_mul_of_nonpos_left rightUpper lowerNonpositive).trans
              (mul_le_mul_of_nonneg_right leftLower yNonnegative))
      · have yNonpositive : y ≤ 0 := le_of_not_ge yNonnegative
        have upperNonnegative : 0 ≤ left.upper := xNonnegative.trans leftUpper
        exact (productLower_le_upper_lower left right).trans
          ((mul_le_mul_of_nonneg_left rightLower upperNonnegative).trans
            (mul_le_mul_of_nonpos_right leftUpper yNonpositive))
    · have xNonpositive : x ≤ 0 := le_of_not_ge xNonnegative
      by_cases yNonnegative : 0 ≤ y
      · have lowerNonpositive : left.lower ≤ 0 := leftLower.trans xNonpositive
        exact (productLower_le_lower_upper left right).trans
          ((mul_le_mul_of_nonpos_left rightUpper lowerNonpositive).trans
            (mul_le_mul_of_nonneg_right leftLower yNonnegative))
      · have yNonpositive : y ≤ 0 := le_of_not_ge yNonnegative
        by_cases upperNonpositive : left.upper ≤ 0
        · by_cases rightUpperNonpositive : right.upper ≤ 0
          · exact (productLower_le_upper_upper left right).trans
              ((mul_le_mul_of_nonpos_right leftUpper rightUpperNonpositive).trans
                (mul_le_mul_of_nonpos_left rightUpper xNonpositive))
          · have rightUpperNonnegative : 0 ≤ right.upper :=
              le_of_not_ge rightUpperNonpositive
            exact (productLower_le_lower_upper left right).trans
              ((mul_nonpos_of_nonpos_of_nonneg
                (leftLower.trans xNonpositive) rightUpperNonnegative).trans
                  (mul_nonneg_of_nonpos_of_nonpos xNonpositive yNonpositive))
        · have upperNonnegative : 0 ≤ left.upper := le_of_not_ge upperNonpositive
          exact (productLower_le_upper_lower left right).trans
            (mul_nonpos_of_nonneg_of_nonpos upperNonnegative
              (rightLower.trans yNonpositive)
              |>.trans (mul_nonneg_of_nonpos_of_nonpos xNonpositive yNonpositive))
  · change x * y ≤ productUpper left right
    by_cases xNonnegative : 0 ≤ x
    · by_cases yNonnegative : 0 ≤ y
      · have upperNonnegative : 0 ≤ left.upper := xNonnegative.trans leftUpper
        exact ((mul_le_mul_of_nonneg_right leftUpper yNonnegative).trans
          (mul_le_mul_of_nonneg_left rightUpper upperNonnegative)).trans
            (upper_upper_le_productUpper left right)
      · have yNonpositive : y ≤ 0 := le_of_not_ge yNonnegative
        by_cases lowerNonnegative : 0 ≤ left.lower
        · exact ((mul_le_mul_of_nonpos_right leftLower yNonpositive).trans
            (mul_le_mul_of_nonneg_left rightUpper lowerNonnegative)).trans
              (lower_upper_le_productUpper left right)
        · have lowerNonpositive : left.lower ≤ 0 := le_of_not_ge lowerNonnegative
          exact (mul_nonpos_of_nonneg_of_nonpos xNonnegative yNonpositive).trans
            ((mul_nonneg_of_nonpos_of_nonpos lowerNonpositive
              (rightLower.trans yNonpositive)).trans
                (lower_lower_le_productUpper left right))
    · have xNonpositive : x ≤ 0 := le_of_not_ge xNonnegative
      by_cases yNonnegative : 0 ≤ y
      · by_cases upperNonpositive : left.upper ≤ 0
        · exact ((mul_le_mul_of_nonneg_right leftUpper yNonnegative).trans
            (mul_le_mul_of_nonpos_left rightLower upperNonpositive)).trans
              (upper_lower_le_productUpper left right)
        · have upperNonnegative : 0 ≤ left.upper := le_of_not_ge upperNonpositive
          exact (mul_nonpos_of_nonpos_of_nonneg xNonpositive yNonnegative).trans
            ((mul_nonneg upperNonnegative (yNonnegative.trans rightUpper)).trans
              (upper_upper_le_productUpper left right))
      · have yNonpositive : y ≤ 0 := le_of_not_ge yNonnegative
        have lowerNonpositive : left.lower ≤ 0 := leftLower.trans xNonpositive
        exact ((mul_le_mul_of_nonpos_right leftLower yNonpositive).trans
          (mul_le_mul_of_nonpos_left rightLower lowerNonpositive)).trans
            (lower_lower_le_productUpper left right)

theorem contains_mask {active : Bool} {interval : ClosedInterval} {value : ℝ}
    (membership : interval.Contains value) :
    (mask active interval).Contains
      (FinitePrecisionExpressionCertificate.boolScalar active * value) := by
  cases active with
  | false => simp [mask, FinitePrecisionExpressionCertificate.boolScalar,
      contains_point]
  | true => simpa [mask, FinitePrecisionExpressionCertificate.boolScalar]

end ClosedInterval

/-- A proof-carrying interval interpretation of the shared scalar expression
language.  Unary functions remain explicit enclosure leaves. -/
inductive IntervalCertificate {Variable : Type u}
    (realEnvironment : Variable → ℝ)
    (intervalEnvironment : Variable → ClosedInterval) :
    (expression : ScalarExpr Variable) → (interval : ClosedInterval) → Prop where
  | ofVariable (name : Variable)
      (membership :
        (intervalEnvironment name).Contains (realEnvironment name)) :
      IntervalCertificate realEnvironment intervalEnvironment
        (.variable name) (intervalEnvironment name)
  | constant (value : ℝ) :
      IntervalCertificate realEnvironment intervalEnvironment
        (.constant value) (.point value)
  | add {left right : ScalarExpr Variable}
      {leftInterval rightInterval : ClosedInterval}
      (leftCertificate :
        IntervalCertificate realEnvironment intervalEnvironment
          left leftInterval)
      (rightCertificate :
        IntervalCertificate realEnvironment intervalEnvironment
          right rightInterval) :
      IntervalCertificate realEnvironment intervalEnvironment (.add left right)
        (.add leftInterval rightInterval)
  | multiply {left right : ScalarExpr Variable}
      {leftInterval rightInterval : ClosedInterval}
      (leftCertificate :
        IntervalCertificate realEnvironment intervalEnvironment
          left leftInterval)
      (rightCertificate :
        IntervalCertificate realEnvironment intervalEnvironment
          right rightInterval) :
      IntervalCertificate realEnvironment intervalEnvironment
        (.multiply left right) (.multiply leftInterval rightInterval)
  | mask {body : ScalarExpr Variable} {bodyInterval : ClosedInterval}
      (active : Bool)
      (bodyCertificate :
        IntervalCertificate realEnvironment intervalEnvironment
          body bodyInterval) :
      IntervalCertificate realEnvironment intervalEnvironment
        (.mask active body) (.mask active bodyInterval)
  | unary {body : ScalarExpr Variable} (map : ℝ → ℝ)
      {bodyInterval outputInterval : ClosedInterval}
      (bodyCertificate :
        IntervalCertificate realEnvironment intervalEnvironment
          body bodyInterval)
      (mapsInto :
        ∀ value, bodyInterval.Contains value →
          outputInterval.Contains (map value)) :
      IntervalCertificate realEnvironment intervalEnvironment
        (.unary map body) outputInterval
  | weaken {expression : ScalarExpr Variable}
      {interval largerInterval : ClosedInterval}
      (certificate :
        IntervalCertificate realEnvironment intervalEnvironment
          expression interval)
      (includes :
        ∀ value, interval.Contains value → largerInterval.Contains value) :
      IntervalCertificate realEnvironment intervalEnvironment
        expression largerInterval

namespace IntervalCertificate

/-- The structural inclusion theorem corresponding to Theorem 1 of the
source: a checked interval certificate encloses the exact real evaluation. -/
theorem sound {Variable : Type u}
    {realEnvironment : Variable → ℝ}
    {intervalEnvironment : Variable → ClosedInterval}
    {expression : ScalarExpr Variable} {interval : ClosedInterval}
    (certificate :
      IntervalCertificate realEnvironment intervalEnvironment
        expression interval) :
    interval.Contains (expression.realEval realEnvironment) := by
  induction certificate with
  | ofVariable _ membership => exact membership
  | constant value => exact ClosedInterval.contains_point value
  | add leftCertificate rightCertificate leftIH rightIH =>
      simpa [ScalarExpr.realEval] using
        ClosedInterval.contains_add leftIH rightIH
  | multiply leftCertificate rightCertificate leftIH rightIH =>
      simpa [ScalarExpr.realEval] using
        ClosedInterval.contains_multiply leftIH rightIH
  | mask active bodyCertificate bodyIH =>
      simpa [ScalarExpr.realEval] using ClosedInterval.contains_mask bodyIH
  | unary map bodyCertificate mapsInto bodyIH =>
      exact mapsInto _ bodyIH
  | weaken certificate includes ih =>
      exact includes _ ih

end IntervalCertificate

/-- Proposition 14's finite splitting rule.  Every tile is checked locally,
and a cover proof transports those local enclosures back to the unsplit
domain. -/
theorem finite_split_sound
    (domain output : ClosedInterval) (tiles : List ClosedInterval)
    (map : ℝ → ℝ)
    (covers :
      ∀ value, domain.Contains value →
        ∃ tile ∈ tiles, tile.Contains value)
    (localSound :
      ∀ tile ∈ tiles, ∀ value, tile.Contains value →
        output.Contains (map value)) :
    ∀ value, domain.Contains value → output.Contains (map value) := by
  intro value membership
  obtain ⟨tile, tileIn, tileMembership⟩ := covers value membership
  exact localSound tile tileIn value tileMembership

/-- A binary split may use different local output enclosures; their hull
encloses the unsplit function. -/
theorem binary_split_hull_sound
    (domain leftDomain rightDomain leftOutput rightOutput : ClosedInterval)
    (map : ℝ → ℝ)
    (covers :
      ∀ value, domain.Contains value →
        leftDomain.Contains value ∨ rightDomain.Contains value)
    (leftSound :
      ∀ value, leftDomain.Contains value →
        leftOutput.Contains (map value))
    (rightSound :
      ∀ value, rightDomain.Contains value →
        rightOutput.Contains (map value)) :
    ∀ value, domain.Contains value →
      (ClosedInterval.hull leftOutput rightOutput).Contains (map value) := by
  intro value membership
  rcases covers value membership with leftMembership | rightMembership
  · exact ClosedInterval.contains_hull_left (leftSound value leftMembership)
  · exact ClosedInterval.contains_hull_right (rightSound value rightMembership)

/-! ## Positive and negative fixtures -/

inductive OneVariable where
  | x
  deriving DecidableEq

private def affineExpression : ScalarExpr OneVariable :=
  .add (.multiply (.constant 2) (.variable .x)) (.constant 3)

private def intervalFrom (lower upper : ℝ) : ClosedInterval :=
  ⟨lower, upper⟩

private def affineRealEnvironment : OneVariable → ℝ
  | .x => 3 / 2

private def affineIntervalEnvironment : OneVariable → ClosedInterval
  | .x => intervalFrom 1 2

private def affineCertificate :
    IntervalCertificate affineRealEnvironment affineIntervalEnvironment
      affineExpression
      (.add (.multiply (.point 2) (intervalFrom 1 2)) (.point 3)) :=
  .add (.multiply (.constant 2) (.ofVariable OneVariable.x (by
    norm_num [affineRealEnvironment,
    affineIntervalEnvironment, intervalFrom, ClosedInterval.Contains])))
    (.constant 3)

/-- A nontrivial affine expression is enclosed by the reconstructed endpoint
semantics. -/
theorem affine_expression_enclosed :
    (intervalFrom 5 7).Contains
      (affineExpression.realEval affineRealEnvironment) := by
  have sound := affineCertificate.sound
  norm_num [affineExpression, affineRealEnvironment, intervalFrom,
    ClosedInterval.point, ClosedInterval.add, ClosedInterval.multiply,
    ClosedInterval.productLower, ClosedInterval.productUpper,
    ClosedInterval.Contains] at sound ⊢
  exact sound

private def dependencyExpression : ScalarExpr OneVariable :=
  .add (.multiply (.constant 2) (.variable .x))
    (.multiply (.constant (-1)) (.variable .x))

private def dependencyRealEnvironment (value : ℝ) : OneVariable → ℝ
  | .x => value

private def dependencyIntervalEnvironment
    (interval : ClosedInterval) : OneVariable → ClosedInterval
  | .x => interval

private def dependencyOutput (input : ClosedInterval) : ClosedInterval :=
  .add (.multiply (.point 2) input) (.multiply (.point (-1)) input)

private def dependencyCertificate (value : ℝ) (input : ClosedInterval)
    (membership : input.Contains value) :
    IntervalCertificate (dependencyRealEnvironment value)
      (dependencyIntervalEnvironment input) dependencyExpression
      (dependencyOutput input) :=
  .add
    (.multiply (.constant 2) (.ofVariable OneVariable.x membership))
    (.multiply (.constant (-1)) (.ofVariable OneVariable.x membership))

theorem dependencyExpression_realEval (value : ℝ) :
    dependencyExpression.realEval (dependencyRealEnvironment value) = value := by
  simp [dependencyExpression, dependencyRealEnvironment, ScalarExpr.realEval]
  ring

private def unitInterval : ClosedInterval := intervalFrom 0 1
private def leftHalf : ClosedInterval := intervalFrom 0 (1 / 2)
private def rightHalf : ClosedInterval := intervalFrom (1 / 2) 1

/-- Direct evaluation reproduces the source's dependency-effect range
`2 * [0,1] - [0,1] = [-1,2]`. -/
theorem dependency_whole_endpoints :
    (dependencyOutput unitInterval).lower = -1 ∧
    (dependencyOutput unitInterval).upper = 2 := by
  norm_num [dependencyOutput, unitInterval, intervalFrom,
    ClosedInterval.point, ClosedInterval.add, ClosedInterval.multiply,
    ClosedInterval.productLower, ClosedInterval.productUpper]

theorem unitInterval_covered_by_halves (value : ℝ)
    (membership : unitInterval.Contains value) :
    leftHalf.Contains value ∨ rightHalf.Contains value := by
  by_cases left : value ≤ 1 / 2
  · exact Or.inl ⟨membership.1, left⟩
  · exact Or.inr ⟨le_of_not_ge left, membership.2⟩

private def splitDependencyOutput : ClosedInterval :=
  .hull (dependencyOutput leftHalf) (dependencyOutput rightHalf)

/-- Splitting at `1/2` reproduces the improved source hull
`[-1/2, 3/2]`. -/
theorem dependency_split_endpoints :
    splitDependencyOutput.lower = -(1 / 2) ∧
    splitDependencyOutput.upper = 3 / 2 := by
  norm_num [splitDependencyOutput, dependencyOutput, leftHalf, rightHalf,
    intervalFrom, ClosedInterval.point, ClosedInterval.add,
    ClosedInterval.multiply, ClosedInterval.productLower,
    ClosedInterval.productUpper, ClosedInterval.hull]

/-- The binary splitting theorem encloses `2*x-x` over the whole unit
interval using the two locally evaluated output ranges. -/
theorem dependency_split_sound (value : ℝ)
    (membership : unitInterval.Contains value) :
    splitDependencyOutput.Contains
      (dependencyExpression.realEval (dependencyRealEnvironment value)) := by
  apply binary_split_hull_sound unitInterval leftHalf rightHalf
    (dependencyOutput leftHalf) (dependencyOutput rightHalf)
    (fun input =>
      dependencyExpression.realEval (dependencyRealEnvironment input))
    unitInterval_covered_by_halves
  · intro input inputMembership
    exact (dependencyCertificate input leftHalf inputMembership).sound
  · intro input inputMembership
    exact (dependencyCertificate input rightHalf inputMembership).sound
  · exact membership

/-- Splitting strictly narrows this dependency-effect enclosure. -/
theorem dependency_split_strictly_narrower :
    splitDependencyOutput.width <
      (dependencyOutput unitInterval).width := by
  norm_num [splitDependencyOutput, dependencyOutput, unitInterval, leftHalf,
    rightHalf, intervalFrom, ClosedInterval.point, ClosedInterval.add,
    ClosedInterval.multiply, ClosedInterval.productLower,
    ClosedInterval.productUpper, ClosedInterval.hull, ClosedInterval.width]

/-- The unsplit interval cannot certify the true nonnegativity of `2*x-x`;
its lower endpoint is negative. -/
theorem dependency_whole_does_not_certify_nonnegative :
    ¬ 0 ≤ (dependencyOutput unitInterval).lower := by
  norm_num [dependencyOutput, unitInterval, intervalFrom,
    ClosedInterval.point, ClosedInterval.add, ClosedInterval.multiply,
    ClosedInterval.productLower, ClosedInterval.productUpper]

#print axioms ClosedInterval.contains_multiply
#print axioms IntervalCertificate.sound
#print axioms finite_split_sound
#print axioms dependency_split_sound
#print axioms dependency_whole_does_not_certify_nonnegative

end

end CertifiedIntervalEvaluation

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
