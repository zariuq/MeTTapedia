import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.LinearSettling

/-!
# Linear deep-equilibrium bridge

This file applies mathlib's bivariate implicit-function theorem to the affine
linear workspace residual.  The derivative result is licensed by the same
spectral-radius condition as the settling results in `LinearSettling`; it makes
no claim about a trained nonlinear decoder or a state-dependent Jacobian.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Filter Topology
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

universe uParameter uState

namespace LinearWorkspaceModel

variable {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
  (model : LinearWorkspaceModel State)

/-- The settling spectral condition makes the fixed-point residual derivative
`I - L` an invertible continuous linear map, as required by mathlib's IFT. -/
theorem one_sub_linearPart_isInvertible
    [CompleteSpace State] [Nontrivial State]
    (hradius : spectralRadius ℂ model.linearPart < 1) :
    (1 - model.linearPart).IsInvertible := by
  let departure : State →L[ℂ] State := 1 - model.linearPart
  have hunit : IsUnit departure := by
    simpa [departure] using model.one_sub_linearPart_isUnit hradius
  have hbijective : Function.Bijective departure :=
    ContinuousLinearMap.isUnit_iff_bijective.mp
      hunit
  have hker : departure.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hbijective.injective
  have hrange : departure.range = ⊤ :=
    LinearMap.range_eq_top.mpr hbijective.surjective
  let equivalence := ContinuousLinearEquiv.ofBijective
    departure hker hrange
  have hequivalence : (equivalence : State →L[ℂ] State) = departure :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  exact ⟨equivalence, hequivalence.trans (by simp [departure])⟩

end LinearWorkspaceModel

/-! ## Explicit affine residual and its two partial derivatives -/

/-- Residual equation for a parameter-driven affine linear workspace:
`(I - L) state - drive parameter - bias`.  Its zero set is exactly the fixed
point equation. -/
noncomputable def linearDEQResidual
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (model : LinearWorkspaceModel State) (drive : Parameter →L[ℂ] State)
    (parameter : Parameter) (state : State) : State :=
  (1 - model.linearPart) state - drive parameter - model.bias

/-- Zero affine residual is equivalent to the parameter-driven fixed-point
equation.  This is the semantic equation differentiated below. -/
theorem linearDEQResidual_eq_zero_iff_fixedPoint
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (model : LinearWorkspaceModel State) (drive : Parameter →L[ℂ] State)
    (parameter : Parameter) (state : State) :
    linearDEQResidual model drive parameter state = 0 ↔
      model.linearPart state + drive parameter + model.bias = state := by
  simp only [linearDEQResidual, sub_apply]
  constructor
  · intro h
    have hbias : state - model.linearPart state - drive parameter = model.bias :=
      sub_eq_zero.mp h
    calc
      model.linearPart state + drive parameter + model.bias =
          model.linearPart state + drive parameter +
            (state - model.linearPart state - drive parameter) := by rw [hbias]
      _ = state := by abel
  · intro h
    apply sub_eq_zero.mpr
    calc
      state - model.linearPart state - drive parameter =
          (model.linearPart state + drive parameter + model.bias) -
            model.linearPart state - drive parameter := by rw [h]
      _ = model.bias := by abel

/-- The parameter partial derivative of the affine residual is `-drive`. -/
theorem linearDEQResidual_hasFDerivAt_parameter
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (model : LinearWorkspaceModel State) (drive : Parameter →L[ℂ] State)
    (parameter : Parameter) (state : State) :
    HasFDerivAt (linearDEQResidual model drive · state) (-drive) parameter := by
  simpa only [linearDEQResidual] using
    ((drive.hasFDerivAt.const_sub ((1 - model.linearPart) state)).sub_const model.bias)

/-- The state partial derivative of the affine residual is exactly `I - L`. -/
theorem linearDEQResidual_hasFDerivAt_state
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (model : LinearWorkspaceModel State) (drive : Parameter →L[ℂ] State)
    (parameter : Parameter) (state : State) :
    HasFDerivAt (linearDEQResidual model drive parameter)
      (1 - model.linearPart) state := by
  change HasFDerivAt
    (fun candidate => (1 - model.linearPart) candidate - drive parameter - model.bias)
    (1 - model.linearPart) state
  exact
    (((1 - model.linearPart).hasFDerivAt.sub_const (drive parameter)).sub_const model.bias)

/-- Constant field of parameter partial derivatives used by the bivariate IFT. -/
noncomputable def linearDEQParameterDerivative
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (drive : Parameter →L[ℂ] State) :
    Parameter → State → Parameter →L[ℂ] State :=
  fun _ _ => -drive

/-- Constant field of state partial derivatives used by the bivariate IFT. -/
noncomputable def linearDEQStateDerivative
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (model : LinearWorkspaceModel State) :
    Parameter → State → State →L[ℂ] State :=
  fun _ _ => 1 - model.linearPart

private theorem linearDEQParameterDerivative_eventually
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (model : LinearWorkspaceModel State) (drive : Parameter →L[ℂ] State)
    (center : Parameter × State) :
    ∀ᶠ point in 𝓝 center,
      HasFDerivAt (linearDEQResidual model drive · point.2)
        (linearDEQParameterDerivative drive point.1 point.2) point.1 := by
  filter_upwards [] with point
  exact linearDEQResidual_hasFDerivAt_parameter
    model drive point.1 point.2

private theorem linearDEQStateDerivative_eventually
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (model : LinearWorkspaceModel State) (drive : Parameter →L[ℂ] State)
    (center : Parameter × State) :
    ∀ᶠ point in 𝓝 center,
      HasFDerivAt (linearDEQResidual model drive point.1)
        (linearDEQStateDerivative model point.1 point.2) point.2 := by
  filter_upwards [] with point
  exact linearDEQResidual_hasFDerivAt_state
    model drive point.1 point.2

private theorem continuousAt_linearDEQParameterDerivative
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (drive : Parameter →L[ℂ] State) (center : Parameter × State) :
    ContinuousAt ↿(linearDEQParameterDerivative drive) center := by
  exact continuousAt_const

private theorem continuousAt_linearDEQStateDerivative
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (model : LinearWorkspaceModel State) (center : Parameter × State) :
    ContinuousAt ↿(linearDEQStateDerivative (Parameter := Parameter) model) center := by
  exact continuousAt_const

/-! ## The mathlib IFT specialization -/

/-- Local equilibrium branch selected by mathlib's bivariate implicit-function
theorem around a parameter/state center.  The branch is defined only in the
linear spectral regime certified by T2. -/
noncomputable def linearDEQImplicitEquilibrium
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter] [CompleteSpace Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State] [Nontrivial State]
    (model : LinearWorkspaceModel State) (drive : Parameter →L[ℂ] State)
    (parameter : Parameter) (state : State)
    (hradius : spectralRadius ℂ model.linearPart < 1) : Parameter → State :=
  implicitFunctionOfBivariate
    (linearDEQParameterDerivative_eventually model drive (parameter, state))
    (linearDEQStateDerivative_eventually model drive (parameter, state))
    (continuousAt_linearDEQParameterDerivative drive (parameter, state))
    (continuousAt_linearDEQStateDerivative model (parameter, state))
    (model.one_sub_linearPart_isInvertible hradius)

/-- The IFT branch remains on the residual level set through the center.  If
the center residual is zero, this is locally a branch of genuine fixed points. -/
theorem linearDEQImplicitEquilibrium_eventually_residual_eq
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter] [CompleteSpace Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State] [Nontrivial State]
    (model : LinearWorkspaceModel State) (drive : Parameter →L[ℂ] State)
    (parameter : Parameter) (state : State)
    (hradius : spectralRadius ℂ model.linearPart < 1) :
    ∀ᶠ nearbyParameter in 𝓝 parameter,
      linearDEQResidual model drive nearbyParameter
          (linearDEQImplicitEquilibrium model drive parameter state hradius nearbyParameter) =
        linearDEQResidual model drive parameter state := by
  unfold linearDEQImplicitEquilibrium
  exact eventually_apply_implicitFunctionOfBivariate
    (linearDEQParameterDerivative_eventually model drive (parameter, state))
    (linearDEQStateDerivative_eventually model drive (parameter, state))
    (continuousAt_linearDEQParameterDerivative drive (parameter, state))
    (continuousAt_linearDEQStateDerivative model (parameter, state))
    (model.one_sub_linearPart_isInvertible hradius)

/-- If the center is an affine fixed point, the IFT branch consists locally
of fixed points for the nearby parameters. -/
theorem linearDEQImplicitEquilibrium_eventually_fixedPoint
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter] [CompleteSpace Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State] [Nontrivial State]
    (model : LinearWorkspaceModel State) (drive : Parameter →L[ℂ] State)
    (parameter : Parameter) (state : State)
    (hradius : spectralRadius ℂ model.linearPart < 1)
    (hcenter : model.linearPart state + drive parameter + model.bias = state) :
    ∀ᶠ nearbyParameter in 𝓝 parameter,
      model.linearPart
          (linearDEQImplicitEquilibrium model drive parameter state hradius nearbyParameter) +
        drive nearbyParameter + model.bias =
          linearDEQImplicitEquilibrium model drive parameter state hradius nearbyParameter := by
  have hcenterZero : linearDEQResidual model drive parameter state = 0 :=
    (linearDEQResidual_eq_zero_iff_fixedPoint model drive parameter state).2 hcenter
  filter_upwards
    [linearDEQImplicitEquilibrium_eventually_residual_eq
      model drive parameter state hradius] with nearbyParameter hlevel
  apply (linearDEQResidual_eq_zero_iff_fixedPoint model drive nearbyParameter _).1
  exact hlevel.trans hcenterZero

/-- Stretch crown, linear scope: mathlib's IFT gives the equilibrium gradient
`(I - L)⁻¹ ∘ drive`.  Thus differentiating through the fixed point is sound
under the same spectral condition that licenses T2 settling. -/
theorem linearDEQImplicitEquilibrium_hasStrictFDerivAt
    {Parameter : Type uParameter} [NormedAddCommGroup Parameter]
    [NormedSpace ℂ Parameter] [CompleteSpace Parameter]
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State] [Nontrivial State]
    (model : LinearWorkspaceModel State) (drive : Parameter →L[ℂ] State)
    (parameter : Parameter) (state : State)
    (hradius : spectralRadius ℂ model.linearPart < 1) :
    HasStrictFDerivAt
      (linearDEQImplicitEquilibrium model drive parameter state hradius)
      ((1 - model.linearPart).inverse ∘L drive) parameter := by
  unfold linearDEQImplicitEquilibrium
  have hift := hasStrictFDerivAt_implicitFunctionOfBivariate
    (linearDEQParameterDerivative_eventually model drive (parameter, state))
    (linearDEQStateDerivative_eventually model drive (parameter, state))
    (continuousAt_linearDEQParameterDerivative drive (parameter, state))
    (continuousAt_linearDEQStateDerivative model (parameter, state))
    (model.one_sub_linearPart_isInvertible hradius)
  convert hift using 1
  ext direction
  simp [linearDEQParameterDerivative, linearDEQStateDerivative]

/-! ## Positive and negative spectral fixtures -/

/-- Positive boundary: the zero scalar linear part satisfies the exact DEQ
spectral license. -/
theorem zeroScalarLinearPart_satisfiesDEQCondition :
    spectralRadius ℂ (0 : ℂ →L[ℂ] ℂ) < 1 := by
  simp

/-- Negative boundary: the identity scalar linear part is not covered because
its spectral radius is exactly one. -/
theorem identityScalarLinearPart_failsDEQCondition :
    ¬ spectralRadius ℂ (1 : ℂ →L[ℂ] ℂ) < 1 := by
  simp

#print axioms LinearWorkspaceModel.one_sub_linearPart_isInvertible
#print axioms linearDEQResidual_eq_zero_iff_fixedPoint
#print axioms linearDEQImplicitEquilibrium_eventually_residual_eq
#print axioms linearDEQImplicitEquilibrium_eventually_fixedPoint
#print axioms linearDEQImplicitEquilibrium_hasStrictFDerivAt
#print axioms zeroScalarLinearPart_satisfiesDEQCondition
#print axioms identityScalarLinearPart_failsDEQCondition

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
