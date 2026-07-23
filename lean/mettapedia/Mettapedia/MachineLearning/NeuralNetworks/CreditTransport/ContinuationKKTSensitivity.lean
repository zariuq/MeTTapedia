import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ImplicitEquilibrium

/-!
# Local KKT sensitivity under dual-leak continuation

At a hard-constraint KKT point, differentiating the regularized dual residual
`constraint - leak • multiplier` in the leak coordinate produces forcing only
in the multiplier equation.  Combining that identity with the implicit
equilibrium theorem yields an explicit inverse-Jacobian sensitivity and a
conditioning-aware norm certificate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ContinuationKKTSensitivity

universe uPrimal uDual

variable {Primal : Type uPrimal} [NormedAddCommGroup Primal]
  [NormedSpace ℝ Primal] [CompleteSpace Primal]
variable {Dual : Type uDual} [NormedAddCommGroup Dual]
  [NormedSpace ℝ Dual] [CompleteSpace Dual]

/-- The derivative of dual leak at a hard-constraint KKT point: no primal
forcing and multiplier-only dual forcing. -/
def dualLeakForcing (multiplier : Dual) : Primal × Dual :=
  (0, -multiplier)

omit [NormedSpace ℝ Primal] [CompleteSpace Primal]
  [NormedSpace ℝ Dual] [CompleteSpace Dual] in
@[simp]
theorem dualLeakForcing_fst (multiplier : Dual) :
    (dualLeakForcing (Primal := Primal) multiplier).1 = 0 := rfl

omit [NormedSpace ℝ Primal] [CompleteSpace Primal]
  [NormedSpace ℝ Dual] [CompleteSpace Dual] in
@[simp]
theorem dualLeakForcing_snd (multiplier : Dual) :
    (dualLeakForcing (Primal := Primal) multiplier).2 = -multiplier := rfl

omit [NormedSpace ℝ Primal] [CompleteSpace Primal]
  [NormedSpace ℝ Dual] [CompleteSpace Dual] in
@[simp]
theorem norm_dualLeakForcing (multiplier : Dual) :
    ‖dualLeakForcing (Primal := Primal) multiplier‖ = ‖multiplier‖ := by
  simp [dualLeakForcing, Prod.norm_def]

/-- Continuous linear form of multiplier-only leak forcing. -/
noncomputable def dualLeakParameterJacobian (multiplier : Dual) :
    ℝ →L[ℝ] Primal × Dual :=
  (0 : ℝ →L[ℝ] Primal).prod
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (-multiplier))

omit [CompleteSpace Primal] [CompleteSpace Dual] in
@[simp]
theorem dualLeakParameterJacobian_apply
    (multiplier : Dual) (direction : ℝ) :
    dualLeakParameterJacobian (Primal := Primal) multiplier direction =
      (0, direction • (-multiplier)) := by
  rfl

omit [CompleteSpace Primal] [CompleteSpace Dual] in
@[simp]
theorem dualLeakParameterJacobian_one (multiplier : Dual) :
    dualLeakParameterJacobian (Primal := Primal) multiplier 1 =
      dualLeakForcing (Primal := Primal) multiplier := by
  ext <;> simp [dualLeakForcing]

/-- Parameter slice of a KKT residual when primal state and multiplier are
held fixed.  Its leak dependence is exactly affine. -/
noncomputable def dualLeakResidualSlice
    (stationarity : Primal) (constraint multiplier : Dual) (leak : ℝ) :
    Primal × Dual :=
  (stationarity, constraint) +
    dualLeakParameterJacobian (Primal := Primal) multiplier leak

omit [CompleteSpace Primal] [CompleteSpace Dual] in
theorem dualLeakResidualSlice_formula
    (stationarity : Primal) (constraint multiplier : Dual) (leak : ℝ) :
    dualLeakResidualSlice stationarity constraint multiplier leak =
      (stationarity, constraint - leak • multiplier) := by
  ext <;>
    simp [dualLeakResidualSlice, dualLeakParameterJacobian, sub_eq_add_neg,
      smul_neg]

omit [CompleteSpace Primal] [CompleteSpace Dual] in
/-- The multiplier-only forcing identity follows directly from the KKT leak
term, independently of derivatives of the task or constraints. -/
theorem dualLeakResidualSlice_hasStrictFDerivAt
    (stationarity : Primal) (constraint multiplier : Dual) (leak : ℝ) :
    HasStrictFDerivAt
      (dualLeakResidualSlice stationarity constraint multiplier)
      (dualLeakParameterJacobian (Primal := Primal) multiplier) leak := by
  have hlinear : HasStrictFDerivAt
      (fun direction : ℝ =>
        (stationarity, constraint) +
          dualLeakParameterJacobian (Primal := Primal) multiplier direction)
      (dualLeakParameterJacobian (Primal := Primal) multiplier) leak :=
    ((dualLeakParameterJacobian (Primal := Primal) multiplier).hasStrictFDerivAt
      (x := leak)).const_add (stationarity, constraint)
  exact hlinear

/-- A real implicit KKT continuation together with the exact interpretation
of the dual coordinate and the leak forcing at the hard endpoint. -/
structure LeakKKTContinuationAt (Primal : Type uPrimal) (Dual : Type uDual)
    [NormedAddCommGroup Primal] [NormedSpace ℝ Primal] [CompleteSpace Primal]
    [NormedAddCommGroup Dual] [NormedSpace ℝ Dual] [CompleteSpace Dual] where
  implicitProblem : ImplicitEquilibriumAt ℝ (Primal × Dual)
  multiplier0 : Dual
  multiplierAtBase : implicitProblem.state0.2 = multiplier0
  leakForcingAtBase :
    implicitProblem.parameterJacobian 1 =
      dualLeakForcing (Primal := Primal) multiplier0

namespace LeakKKTContinuationAt

variable (problem : LeakKKTContinuationAt Primal Dual)

/-- Derivative of the locally constructed KKT equilibrium branch in the unit
leak direction. -/
noncomputable def sensitivity : Primal × Dual :=
  problem.implicitProblem.sensitivity 1

/-- Exact local response: inverse state Jacobian applied to multiplier-only
leak forcing. -/
theorem sensitivity_eq_inverse_forcing :
    problem.sensitivity =
      -(problem.implicitProblem.stateJacobian).inverse
        (dualLeakForcing (Primal := Primal) problem.multiplier0) := by
  simp [sensitivity, ImplicitEquilibriumAt.sensitivity,
    ContinuousLinearMap.comp_apply, problem.leakForcingAtBase]

/-- Conditioning-aware KKT continuation certificate.  The multiplier bound
and inverse-Jacobian bound remain separate premises. -/
theorem norm_sensitivity_le
    (inverseBound multiplierBound : ℝ)
    (hinverse :
      ‖(problem.implicitProblem.stateJacobian).inverse‖ ≤ inverseBound)
    (hmultiplier : ‖problem.multiplier0‖ ≤ multiplierBound) :
    ‖problem.sensitivity‖ ≤ inverseBound * multiplierBound := by
  have hinverseNonnegative : 0 ≤ inverseBound :=
    (norm_nonneg _).trans hinverse
  calc
    ‖problem.sensitivity‖ ≤
        ‖(problem.implicitProblem.stateJacobian).inverse‖ *
          ‖problem.implicitProblem.parameterJacobian 1‖ :=
      problem.implicitProblem.norm_sensitivity_apply_le 1
    _ = ‖(problem.implicitProblem.stateJacobian).inverse‖ *
          ‖problem.multiplier0‖ := by
      rw [problem.leakForcingAtBase, norm_dualLeakForcing]
    _ ≤ inverseBound * multiplierBound := by
      gcongr

end LeakKKTContinuationAt

/-! ## Nondegenerate linearized KKT fixture -/

private noncomputable def scalarKKTParameter :
    (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

private noncomputable def scalarKKTPrimal :
    (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ ∘L
    ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)

private noncomputable def scalarKKTMultiplier :
    (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ ℝ ℝ ∘L
    ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)

private noncomputable def scalarKKTDerivative :
    (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × ℝ) :=
  (2 • scalarKKTPrimal + scalarKKTMultiplier).prod
    (scalarKKTPrimal - scalarKKTParameter)

private noncomputable def scalarKKTStateJacobian :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  let primal := ContinuousLinearMap.fst ℝ ℝ ℝ
  let multiplier := ContinuousLinearMap.snd ℝ ℝ ℝ
  (2 • primal + multiplier).prod primal

private noncomputable def scalarKKTStateJacobianInverse :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  let primalResidual := ContinuousLinearMap.fst ℝ ℝ ℝ
  let constraintResidual := ContinuousLinearMap.snd ℝ ℝ ℝ
  constraintResidual.prod (primalResidual - 2 • constraintResidual)

private theorem scalarKKTStateJacobian_comp_inverse :
    scalarKKTStateJacobian ∘L scalarKKTStateJacobianInverse =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  apply ContinuousLinearMap.ext
  rintro ⟨first, second⟩
  ext <;>
    simp [scalarKKTStateJacobian, scalarKKTStateJacobianInverse,
      ContinuousLinearMap.comp_apply]

private theorem scalarKKTStateJacobian_inverse_comp :
    scalarKKTStateJacobianInverse ∘L scalarKKTStateJacobian =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  apply ContinuousLinearMap.ext
  rintro ⟨first, second⟩
  ext <;>
    simp [scalarKKTStateJacobian, scalarKKTStateJacobianInverse,
      ContinuousLinearMap.comp_apply]

private theorem scalarKKTStateJacobian_isInvertible :
    scalarKKTStateJacobian.IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    scalarKKTStateJacobian_comp_inverse
    scalarKKTStateJacobian_inverse_comp

private noncomputable def linearizedUnitKKTResidual
    (point : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (-1, 0) + scalarKKTDerivative point

theorem linearizedUnitKKTResidual_formula
    (leak primal multiplier : ℝ) :
    linearizedUnitKKTResidual (leak, (primal, multiplier)) =
      (2 * primal + multiplier - 1, primal - leak) := by
  apply Prod.ext
  · simp [linearizedUnitKKTResidual, scalarKKTDerivative, scalarKKTParameter,
      scalarKKTPrimal, scalarKKTMultiplier,
      ContinuousLinearMap.comp_apply]
    ring
  · simp [linearizedUnitKKTResidual, scalarKKTDerivative, scalarKKTParameter,
      scalarKKTPrimal, scalarKKTMultiplier,
      ContinuousLinearMap.comp_apply]

private noncomputable def linearizedUnitKKTImplicit :
    ImplicitEquilibriumAt ℝ (ℝ × ℝ) where
  residual := linearizedUnitKKTResidual
  state0 := (0, 1)
  derivative := scalarKKTDerivative
  hasStrictDerivative := by
    exact scalarKKTDerivative.hasStrictFDerivAt.const_add (-1, 0)
  stateJacobianInvertible := by
    have hpartial :
        scalarKKTDerivative ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) =
          scalarKKTStateJacobian := by
      apply ContinuousLinearMap.ext
      rintro ⟨primal, multiplier⟩
      ext <;>
        simp [scalarKKTDerivative, scalarKKTParameter, scalarKKTPrimal,
          scalarKKTMultiplier, scalarKKTStateJacobian,
          ContinuousLinearMap.comp_apply]
    rw [hpartial]
    exact scalarKKTStateJacobian_isInvertible
  residualAtFree := by
    norm_num [linearizedUnitKKTResidual_formula]

/-- Positive fixture: the hard endpoint has multiplier one and exact
multiplier-only leak forcing. -/
noncomputable def linearizedUnitKKTContinuation :
    LeakKKTContinuationAt ℝ ℝ where
  implicitProblem := linearizedUnitKKTImplicit
  multiplier0 := 1
  multiplierAtBase := rfl
  leakForcingAtBase := by
    ext <;>
      norm_num [ImplicitEquilibriumAt.parameterJacobian,
        linearizedUnitKKTImplicit, scalarKKTDerivative,
        scalarKKTParameter, scalarKKTPrimal, scalarKKTMultiplier,
        dualLeakForcing, ContinuousLinearMap.comp_apply]

/-- The nondegenerate fixture has a genuinely moving branch with derivative
`(1, -2)` in the leak direction. -/
theorem linearizedUnitKKTContinuation_sensitivity :
    linearizedUnitKKTContinuation.sensitivity = (1, -2) := by
  rw [LeakKKTContinuationAt.sensitivity_eq_inverse_forcing]
  change
    -(linearizedUnitKKTImplicit.stateJacobian).inverse
        (dualLeakForcing (Primal := ℝ) 1) = (1, -2)
  have hstate :
      linearizedUnitKKTImplicit.stateJacobian =
        scalarKKTStateJacobian := by
    apply ContinuousLinearMap.ext
    rintro ⟨primal, multiplier⟩
    ext <;>
      simp [ImplicitEquilibriumAt.stateJacobian, linearizedUnitKKTImplicit,
        scalarKKTDerivative, scalarKKTParameter, scalarKKTPrimal,
        scalarKKTMultiplier, scalarKKTStateJacobian,
        ContinuousLinearMap.comp_apply]
  have hinverse :
      (linearizedUnitKKTImplicit.stateJacobian).inverse =
        scalarKKTStateJacobianInverse := by
    rw [hstate]
    apply ContinuousLinearMap.inverse_eq
    · exact scalarKKTStateJacobian_comp_inverse
    · exact scalarKKTStateJacobian_inverse_comp
  rw [hinverse]
  norm_num [linearizedUnitKKTContinuation, dualLeakForcing,
    scalarKKTStateJacobianInverse]

/-! ## Conditioning boundary -/

/-- Scalar state Jacobian with a tunable singular-value scale. -/
noncomputable def scaledStateJacobian (scale : ℝ) : ℝ →L[ℝ] ℝ :=
  scale • ContinuousLinearMap.id ℝ ℝ

/-- Explicit inverse candidate for a nonzero scalar state Jacobian. -/
noncomputable def scaledStateJacobianInverse (scale : ℝ) : ℝ →L[ℝ] ℝ :=
  scale⁻¹ • ContinuousLinearMap.id ℝ ℝ

theorem scaledStateJacobian_comp_inverse
    {scale : ℝ} (hscale : scale ≠ 0) :
    scaledStateJacobian scale ∘L scaledStateJacobianInverse scale =
      ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro x
  simp [scaledStateJacobian, scaledStateJacobianInverse, hscale]

theorem scaledStateJacobian_inverse_comp
    {scale : ℝ} (hscale : scale ≠ 0) :
    scaledStateJacobianInverse scale ∘L scaledStateJacobian scale =
      ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro x
  simp [scaledStateJacobian, scaledStateJacobianInverse, hscale]

/-- Negative boundary: unit forcing can have arbitrarily large response when
the inverse-Jacobian norm is uncontrolled, even though every chosen Jacobian
is invertible. -/
theorem exists_unitForcing_response_gt (bound : ℝ) (hbound : 0 ≤ bound) :
    ∃ scale : ℝ,
      scale ≠ 0 ∧
      ‖scaledStateJacobianInverse scale 1‖ > bound := by
  refine ⟨1 / (bound + 1), ?_, ?_⟩
  · positivity
  · have hpositive : 0 < bound + 1 := by linarith
    rw [show scaledStateJacobianInverse (1 / (bound + 1)) 1 =
        bound + 1 by
      simp [scaledStateJacobianInverse]
    ]
    rw [Real.norm_eq_abs, abs_of_pos hpositive]
    linarith

#print axioms dualLeakResidualSlice_hasStrictFDerivAt
#print axioms LeakKKTContinuationAt.sensitivity_eq_inverse_forcing
#print axioms LeakKKTContinuationAt.norm_sensitivity_le
#print axioms linearizedUnitKKTResidual_formula
#print axioms linearizedUnitKKTContinuation_sensitivity
#print axioms scaledStateJacobian_comp_inverse
#print axioms scaledStateJacobian_inverse_comp
#print axioms exists_unitForcing_response_gt

end ContinuationKKTSensitivity

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
