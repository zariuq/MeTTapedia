import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.TruncatedNeumannResidual

/-!
# Phantom-gradient alignment from a finite inverse residual

Geng et al. replace the exact implicit inverse in an equilibrium model by a
finite "phantom" inverse.  Their central optimization condition is not that
the approximation equal the inverse, but that its linear-system residual be
small enough relative to the parameter Jacobian's conditioning.  This file
formalizes and sharpens that condition.

The analytic theorem is stated for continuous linear maps between arbitrary
real Hilbert spaces.  A lower and upper bound on the exact parameter map,
together with an upper bound on the phantom residual, yields an explicit
lower bound on the inner product between phantom and exact gradients.  Strict
alignment requires a nonzero upstream gradient; the source theorem's
unqualified strict conclusion is false at the zero gradient.  Equality in the
residual threshold is also sharp.

The second half connects the theorem to damped truncated Neumann inversion.
For `B = (1-lambda) I + lambda H`, the finite inverse
`lambda (I + B + ... + B^(k-1))` has exact right residual `-B^k` against
`I-H`.  If `H` contracts by `q`, then `B` contracts by
`(1-lambda) + lambda q`, producing a directly checkable finite-depth
alignment condition.

Source correspondence: Geng et al., *On Training Implicit Models*,
arXiv:2111.05177, Theorems 1--2 and equations (6), (8), and (14)--(18).
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace PhantomGradientAlignment

open scoped InnerProductSpace
open TruncatedNeumannResidual

noncomputable section

variable {Hidden Parameter : Type*}
  [NormedAddCommGroup Hidden] [InnerProductSpace ℝ Hidden]
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-! ## Conditioning and alignment -/

/-- Pointwise upper operator bound, written without choosing an operator-norm
representation. -/
def UpperBoundedBy
    (constant : ℝ) (operator : Hidden →L[ℝ] Parameter) : Prop :=
  ∀ state, ‖operator state‖ ≤ constant * ‖state‖

/-- Pointwise lower singular-value bound. -/
def LowerBoundedBy
    (constant : ℝ) (operator : Hidden →L[ℝ] Parameter) : Prop :=
  ∀ state, constant * ‖state‖ ≤ ‖operator state‖

/-- The phantom direction is the exact direction plus its inverse-residual
error. -/
def phantomGradient
    (exactMap residualMap : Hidden →L[ℝ] Parameter)
    (upstream : Hidden) : Parameter :=
  exactMap upstream + residualMap upstream

/-- Quantitative core of the phantom-gradient theorem. -/
theorem phantomGradient_inner_exact_lower
    {lower upper error : ℝ}
    {exactMap residualMap : Hidden →L[ℝ] Parameter}
    (lower_nonneg : 0 ≤ lower)
    (_upper_nonneg : 0 ≤ upper)
    (error_nonneg : 0 ≤ error)
    (exact_lower : LowerBoundedBy lower exactMap)
    (exact_upper : UpperBoundedBy upper exactMap)
    (residual_upper : UpperBoundedBy error residualMap)
    (upstream : Hidden) :
    (lower ^ 2 - error * upper) * ‖upstream‖ ^ 2 ≤
      ⟪phantomGradient exactMap residualMap upstream,
        exactMap upstream⟫_ℝ := by
  have lower_norm := exact_lower upstream
  have lower_sq :
      lower ^ 2 * ‖upstream‖ ^ 2 ≤
        ‖exactMap upstream‖ ^ 2 := by
    have squared := (sq_le_sq₀
      (mul_nonneg lower_nonneg (norm_nonneg _))
      (norm_nonneg _)).2 lower_norm
    nlinarith [squared]
  have residual_norm := residual_upper upstream
  have exact_norm := exact_upper upstream
  have norm_product :
      ‖residualMap upstream‖ * ‖exactMap upstream‖ ≤
        error * upper * ‖upstream‖ ^ 2 := by
    calc
      ‖residualMap upstream‖ * ‖exactMap upstream‖ ≤
          (error * ‖upstream‖) * (upper * ‖upstream‖) :=
        mul_le_mul residual_norm exact_norm (norm_nonneg _)
          (mul_nonneg error_nonneg (norm_nonneg _))
      _ = error * upper * ‖upstream‖ ^ 2 := by ring
  have inner_lower :
      -(‖residualMap upstream‖ * ‖exactMap upstream‖) ≤
        ⟪residualMap upstream, exactMap upstream⟫_ℝ :=
    (neg_le_of_abs_le
      (abs_real_inner_le_norm
        (residualMap upstream) (exactMap upstream)))
  rw [phantomGradient, inner_add_left,
    real_inner_self_eq_norm_sq]
  nlinarith

/-- A strict residual margin makes every nonzero phantom direction positively
aligned with the exact gradient. -/
theorem phantomGradient_inner_exact_pos
    {lower upper error : ℝ}
    {exactMap residualMap : Hidden →L[ℝ] Parameter}
    (lower_nonneg : 0 ≤ lower)
    (upper_nonneg : 0 ≤ upper)
    (error_nonneg : 0 ≤ error)
    (margin : error * upper < lower ^ 2)
    (exact_lower : LowerBoundedBy lower exactMap)
    (exact_upper : UpperBoundedBy upper exactMap)
    (residual_upper : UpperBoundedBy error residualMap)
    {upstream : Hidden} (upstream_ne_zero : upstream ≠ 0) :
    0 <
      ⟪phantomGradient exactMap residualMap upstream,
        exactMap upstream⟫_ℝ := by
  have norm_pos : 0 < ‖upstream‖ :=
    norm_pos_iff.mpr upstream_ne_zero
  have lower_bound :=
    phantomGradient_inner_exact_lower lower_nonneg upper_nonneg
      error_nonneg exact_lower exact_upper residual_upper upstream
  have coefficient_pos : 0 < lower ^ 2 - error * upper := by
    linarith
  exact lt_of_lt_of_le
    (mul_pos coefficient_pos (sq_pos_of_pos norm_pos))
    lower_bound

/-- The ratio form used in the source implies the product-margin form when
the upper singular bound is positive. -/
theorem phantomGradient_inner_exact_pos_of_ratio
    {lower upper error : ℝ}
    {exactMap residualMap : Hidden →L[ℝ] Parameter}
    (lower_nonneg : 0 ≤ lower)
    (upper_pos : 0 < upper)
    (error_nonneg : 0 ≤ error)
    (ratio_margin : error < lower ^ 2 / upper)
    (exact_lower : LowerBoundedBy lower exactMap)
    (exact_upper : UpperBoundedBy upper exactMap)
    (residual_upper : UpperBoundedBy error residualMap)
    {upstream : Hidden} (upstream_ne_zero : upstream ≠ 0) :
    0 <
      ⟪phantomGradient exactMap residualMap upstream,
        exactMap upstream⟫_ℝ := by
  apply phantomGradient_inner_exact_pos lower_nonneg upper_pos.le
    error_nonneg _ exact_lower exact_upper residual_upper upstream_ne_zero
  exact (lt_div_iff₀ upper_pos).mp ratio_margin

/-! ## Damped Neumann residual -/

section DampedNeumann

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- Damped linearized fixed-point map
`B = (1-lambda) I + lambda H`. -/
def dampedOperator
    (damping : ℝ) (operator : State →L[ℝ] State) :
    State →L[ℝ] State :=
  (1 - damping) • ContinuousLinearMap.id ℝ State +
    damping • operator

/-- Pointwise contraction factor inherited by the damped map. -/
def dampedFactor (damping factor : ℝ) : ℝ :=
  (1 - damping) + damping * factor

theorem dampedFactor_nonneg
    {damping factor : ℝ}
    (damping_nonneg : 0 ≤ damping)
    (damping_le_one : damping ≤ 1)
    (factor_nonneg : 0 ≤ factor) :
    0 ≤ dampedFactor damping factor := by
  unfold dampedFactor
  exact add_nonneg (sub_nonneg.mpr damping_le_one)
    (mul_nonneg damping_nonneg factor_nonneg)

theorem dampedFactor_lt_one
    {damping factor : ℝ}
    (damping_pos : 0 < damping)
    (factor_lt_one : factor < 1) :
    dampedFactor damping factor < 1 := by
  unfold dampedFactor
  nlinarith [mul_pos damping_pos (sub_pos.mpr factor_lt_one)]

/-- Damping preserves a known contraction certificate, with the exact convex
combination factor. -/
theorem dampedOperator_contracts
    {damping factor : ℝ} {operator : State →L[ℝ] State}
    (damping_nonneg : 0 ≤ damping)
    (damping_le_one : damping ≤ 1)
    (operator_contracts : ContractsBy operator factor) :
    ContractsBy (dampedOperator damping operator)
      (dampedFactor damping factor) := by
  intro state
  have operator_bound := operator_contracts state
  have one_sub_nonneg : 0 ≤ 1 - damping :=
    sub_nonneg.mpr damping_le_one
  calc
    ‖dampedOperator damping operator state‖ =
        ‖(1 - damping) • state +
          damping • operator state‖ := by
      simp [dampedOperator]
    _ ≤ ‖(1 - damping) • state‖ +
          ‖damping • operator state‖ := norm_add_le _ _
    _ = (1 - damping) * ‖state‖ +
          damping * ‖operator state‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg one_sub_nonneg, abs_of_nonneg damping_nonneg]
    _ ≤ (1 - damping) * ‖state‖ +
          damping * (factor * ‖state‖) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left operator_bound damping_nonneg)
    _ = dampedFactor damping factor * ‖state‖ := by
      unfold dampedFactor
      ring

/-- Finite damped-Neumann approximation to `(I-H)⁻¹`. -/
def dampedNeumannInverse
    (damping : ℝ) (operator : State →L[ℝ] State)
    (terms : ℕ) : State →L[ℝ] State :=
  damping • partialSum (dampedOperator damping operator) terms

theorem one_sub_dampedOperator
    (damping : ℝ) (operator : State →L[ℝ] State) :
    1 - dampedOperator damping operator =
      damping • (1 - operator) := by
  ext state
  simp [dampedOperator]
  module

/-- Exact finite inverse residual.  This is the algebraic bridge between the
source's damped Neumann construction and an executable residual trace. -/
theorem dampedNeumannInverse_mul_one_sub
    (damping : ℝ) (operator : State →L[ℝ] State)
    (terms : ℕ) :
    dampedNeumannInverse damping operator terms * (1 - operator) =
      1 - dampedOperator damping operator ^ terms := by
  let damped := dampedOperator damping operator
  calc
    dampedNeumannInverse damping operator terms * (1 - operator) =
        partialSum damped terms *
          (damping • (1 - operator)) := by
      ext state
      simp [dampedNeumannInverse, damped]
    _ = partialSum damped terms * (1 - damped) := by
      rw [one_sub_dampedOperator]
    _ = 1 - damped ^ terms :=
      partialSum_mul_one_sub damped terms

/-- Subtracting the exact identity leaves precisely the negative omitted
power. -/
theorem dampedNeumann_inverseResidual_eq_neg_power
    (damping : ℝ) (operator : State →L[ℝ] State)
    (terms : ℕ) :
    dampedNeumannInverse damping operator terms * (1 - operator) - 1 =
      -(dampedOperator damping operator ^ terms) := by
  rw [dampedNeumannInverse_mul_one_sub]
  abel

/-- A finite damped-Neumann inverse has a geometric residual budget. -/
theorem dampedNeumann_inverseResidual_norm_le
    {damping factor : ℝ} {operator : State →L[ℝ] State}
    (damping_nonneg : 0 ≤ damping)
    (damping_le_one : damping ≤ 1)
    (factor_nonneg : 0 ≤ factor)
    (operator_contracts : ContractsBy operator factor)
    (terms : ℕ) (state : State) :
    ‖(dampedNeumannInverse damping operator terms *
          (1 - operator) - 1) state‖ ≤
      dampedFactor damping factor ^ terms * ‖state‖ := by
  rw [dampedNeumann_inverseResidual_eq_neg_power]
  simp only [neg_apply, norm_neg]
  exact pow_apply_norm_le
    (dampedOperator_contracts damping_nonneg damping_le_one
      operator_contracts)
    (dampedFactor_nonneg damping_nonneg damping_le_one factor_nonneg)
    terms state

/-- Parameter-space error map induced by the finite inverse residual. -/
def dampedNeumannParameterResidual
    (parameterMap : State →L[ℝ] Parameter)
    (damping : ℝ) (operator : State →L[ℝ] State)
    (terms : ℕ) : State →L[ℝ] Parameter :=
  parameterMap.comp
    (dampedNeumannInverse damping operator terms *
      (1 - operator) - 1)

theorem dampedNeumannParameterResidual_upper
    {damping factor upper : ℝ}
    {operator : State →L[ℝ] State}
    {parameterMap : State →L[ℝ] Parameter}
    (damping_nonneg : 0 ≤ damping)
    (damping_le_one : damping ≤ 1)
    (factor_nonneg : 0 ≤ factor)
    (upper_nonneg : 0 ≤ upper)
    (operator_contracts : ContractsBy operator factor)
    (parameter_upper : UpperBoundedBy upper parameterMap)
    (terms : ℕ) :
    UpperBoundedBy
      (upper * dampedFactor damping factor ^ terms)
      (dampedNeumannParameterResidual
        parameterMap damping operator terms) := by
  intro state
  let residualState :=
    (dampedNeumannInverse damping operator terms *
      (1 - operator) - 1) state
  have outer_bound := parameter_upper residualState
  have residual_bound :=
    dampedNeumann_inverseResidual_norm_le damping_nonneg damping_le_one
      factor_nonneg operator_contracts terms state
  calc
    ‖dampedNeumannParameterResidual
        parameterMap damping operator terms state‖ =
      ‖parameterMap residualState‖ := by
        rfl
    _ ≤ upper * ‖residualState‖ := outer_bound
    _ ≤ upper *
        (dampedFactor damping factor ^ terms * ‖state‖) :=
      mul_le_mul_of_nonneg_left residual_bound upper_nonneg
    _ =
        (upper * dampedFactor damping factor ^ terms) *
          ‖state‖ := by ring

/-- End-to-end finite-depth phantom-gradient alignment certificate. -/
theorem dampedNeumann_phantom_inner_exact_pos
    {damping factor lower upper : ℝ}
    {operator : State →L[ℝ] State}
    {parameterMap : State →L[ℝ] Parameter}
    (damping_nonneg : 0 ≤ damping)
    (damping_le_one : damping ≤ 1)
    (factor_nonneg : 0 ≤ factor)
    (lower_nonneg : 0 ≤ lower)
    (upper_nonneg : 0 ≤ upper)
    (operator_contracts : ContractsBy operator factor)
    (parameter_lower : LowerBoundedBy lower parameterMap)
    (parameter_upper : UpperBoundedBy upper parameterMap)
    (terms : ℕ)
    (finite_margin :
      upper ^ 2 * dampedFactor damping factor ^ terms <
        lower ^ 2)
    {upstream : State} (upstream_ne_zero : upstream ≠ 0) :
    0 <
      ⟪phantomGradient parameterMap
          (dampedNeumannParameterResidual
            parameterMap damping operator terms)
          upstream,
        parameterMap upstream⟫_ℝ := by
  apply phantomGradient_inner_exact_pos lower_nonneg upper_nonneg
    (mul_nonneg upper_nonneg
      (pow_nonneg
        (dampedFactor_nonneg damping_nonneg damping_le_one factor_nonneg)
        terms))
    _ parameter_lower parameter_upper
    (dampedNeumannParameterResidual_upper damping_nonneg damping_le_one
      factor_nonneg upper_nonneg operator_contracts parameter_upper terms)
    upstream_ne_zero
  nlinarith

end DampedNeumann

/-! ## Positive and negative fixtures -/

def scalarIdentity : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.id ℝ ℝ

def scalarNegativeIdentity : ℝ →L[ℝ] ℝ :=
  -(ContinuousLinearMap.id ℝ ℝ)

theorem scalarIdentity_lower :
    LowerBoundedBy 1 scalarIdentity := by
  intro state
  simp [scalarIdentity]

theorem scalarIdentity_upper :
    UpperBoundedBy 1 scalarIdentity := by
  intro state
  simp [scalarIdentity]

theorem scalarZero_upper :
    UpperBoundedBy 0 (0 : ℝ →L[ℝ] ℝ) := by
  intro state
  simp

theorem exact_phantom_positive :
    0 <
      ⟪phantomGradient scalarIdentity 0 (1 : ℝ),
        scalarIdentity 1⟫_ℝ := by
  norm_num [phantomGradient, scalarIdentity]

/-- The source theorem needs a nonzero-gradient premise: both gradients
vanish at a zero upstream signal. -/
theorem zero_upstream_not_strictly_aligned :
    ¬ 0 <
      ⟪phantomGradient scalarIdentity 0 (0 : ℝ),
        scalarIdentity 0⟫_ℝ := by
  norm_num [phantomGradient, scalarIdentity]

/-- Strictness of the residual margin is sharp.  At equality, the phantom
direction can vanish even when the exact direction is nonzero. -/
theorem equality_margin_not_strictly_aligned :
    ¬ 0 <
      ⟪phantomGradient scalarIdentity scalarNegativeIdentity (1 : ℝ),
        scalarIdentity 1⟫_ℝ := by
  norm_num [phantomGradient, scalarIdentity, scalarNegativeIdentity]

/-- A concrete two-term damped Neumann inverse satisfies the finite alignment
condition. -/
theorem halfOperator_two_term_phantom_positive :
    0 <
      ⟪phantomGradient scalarIdentity
          (dampedNeumannParameterResidual
            scalarIdentity 1 halfOperator 2)
          (1 : ℝ),
        scalarIdentity 1⟫_ℝ := by
  exact dampedNeumann_phantom_inner_exact_pos
    (damping := 1) (factor := 1 / 2)
    (lower := 1) (upper := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    halfOperator_contracts scalarIdentity_lower scalarIdentity_upper
    2 (by norm_num [dampedFactor]) (by norm_num)

#print axioms phantomGradient_inner_exact_pos
#print axioms dampedNeumannInverse_mul_one_sub
#print axioms dampedNeumann_phantom_inner_exact_pos
#print axioms zero_upstream_not_strictly_aligned
#print axioms equality_margin_not_strictly_aligned
#print axioms halfOperator_two_term_phantom_positive

end

end PhantomGradientAlignment

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
