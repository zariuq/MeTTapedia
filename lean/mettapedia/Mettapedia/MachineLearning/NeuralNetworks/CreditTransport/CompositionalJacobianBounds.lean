import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NonlinearReadoutGradientTransport

/-!
# Compositional Jacobian bounds for masked residual readouts

A nonlinear adapter readout is assembled from affine maps, nonlinear hidden
transitions, and additive error injections.  This file gives a reusable
regional calculus for three quantities needed by nonlinear credit transport:

* a Lipschitz rate `R` for the forward map;
* an operator-norm bound `J` for its declared Jacobian;
* a Lipschitz rate `H` for variation of that Jacobian.

For a composition `g ∘ f`, the exact conservative recurrence is

`R = Rg * Rf`, `J = Jg * Jf`,
`H = Hg * Rf * Jf + Jg * Hf`.

The first term is the nonlinear chain-rule cost: the outer Jacobian moves as
the inner representation moves, and then acts through the inner Jacobian.
Regional preservation is an explicit premise, so a certificate cannot be
composed beyond the domain where its intermediate bounds were established.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CompositionalJacobianBounds

noncomputable section

open Filter

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A differentiable map together with regional forward, Jacobian-norm, and
Jacobian-variation bounds.  The derivative is declared rather than recovered
from `fderiv`, so source-facing constructions can retain their exact symbolic
Jacobian. -/
structure RegionalJacobianBudget
    (map : X → Y) (jacobian : X → X →L[ℝ] Y)
    (domain : X → Prop) (rate operatorBound variation : ℝ) where
  rate_nonneg : 0 ≤ rate
  operatorBound_nonneg : 0 ≤ operatorBound
  variation_nonneg : 0 ≤ variation
  hasFDerivAt_on_domain : ∀ state, domain state →
    HasFDerivAt map (jacobian state) state
  map_pair_bound : ∀ left right,
    domain left → domain right →
    ‖map left - map right‖ ≤ rate * ‖left - right‖
  jacobian_norm_bound : ∀ state, domain state →
    ‖jacobian state‖ ≤ operatorBound
  jacobian_pair_bound : ∀ left right,
    domain left → domain right →
    ‖jacobian left - jacobian right‖ ≤ variation * ‖left - right‖

/-- A valid regional budget remains valid after any of its three numeric
bounds is enlarged.  This lets a source-shaped map retain its exact internal
operator norms while an independently checked checkpoint certificate supplies
conservative external constants. -/
def RegionalJacobianBudget.weaken
    {map : X → Y} {jacobian : X → X →L[ℝ] Y}
    {domain : X → Prop}
    {rate operatorBound variation
      largerRate largerOperatorBound largerVariation : ℝ}
    (budget : RegionalJacobianBudget map jacobian domain
      rate operatorBound variation)
    (rate_le : rate ≤ largerRate)
    (operatorBound_le : operatorBound ≤ largerOperatorBound)
    (variation_le : variation ≤ largerVariation) :
    RegionalJacobianBudget map jacobian domain
      largerRate largerOperatorBound largerVariation where
  rate_nonneg := budget.rate_nonneg.trans rate_le
  operatorBound_nonneg :=
    budget.operatorBound_nonneg.trans operatorBound_le
  variation_nonneg := budget.variation_nonneg.trans variation_le
  hasFDerivAt_on_domain := budget.hasFDerivAt_on_domain
  map_pair_bound := by
    intro left right hleft hright
    calc
      ‖map left - map right‖ ≤ rate * ‖left - right‖ :=
        budget.map_pair_bound left right hleft hright
      _ ≤ largerRate * ‖left - right‖ :=
        mul_le_mul_of_nonneg_right rate_le (norm_nonneg _)
  jacobian_norm_bound := by
    intro state hstate
    exact (budget.jacobian_norm_bound state hstate).trans operatorBound_le
  jacobian_pair_bound := by
    intro left right hleft hright
    calc
      ‖jacobian left - jacobian right‖ ≤
          variation * ‖left - right‖ :=
        budget.jacobian_pair_bound left right hleft hright
      _ ≤ largerVariation * ‖left - right‖ :=
        mul_le_mul_of_nonneg_right variation_le (norm_nonneg _)

/-- Function-level composition, kept named so the exact readout assembled by
the budget can be inspected independently of its derivative proof. -/
def composeMap (outer : Y → Z) (inner : X → Y) (state : X) : Z :=
  outer (inner state)

/-- The symbolic chain-rule Jacobian of `composeMap`. -/
def composeJacobian
    (outerJacobian : Y → Y →L[ℝ] Z)
    (inner : X → Y) (innerJacobian : X → X →L[ℝ] Y)
    (state : X) : X →L[ℝ] Z :=
  (outerJacobian (inner state)).comp (innerJacobian state)

/-- Pointwise addition of two source maps. -/
def addMap (left right : X → Y) (state : X) : Y :=
  left state + right state

/-- Pointwise addition of their symbolic Jacobians. -/
def addJacobian
    (left right : X → X →L[ℝ] Y) (state : X) : X →L[ℝ] Y :=
  left state + right state

theorem composeJacobian_sub
    (outerJacobian : Y → Y →L[ℝ] Z)
    (inner : X → Y) (innerJacobian : X → X →L[ℝ] Y)
    (left right : X) :
    composeJacobian outerJacobian inner innerJacobian left -
        composeJacobian outerJacobian inner innerJacobian right =
      (outerJacobian (inner left) - outerJacobian (inner right)).comp
          (innerJacobian left) +
        (outerJacobian (inner right)).comp
          (innerJacobian left - innerJacobian right) := by
  ext direction
  change
    outerJacobian (inner left) (innerJacobian left direction) -
        outerJacobian (inner right) (innerJacobian right direction) =
      (outerJacobian (inner left) - outerJacobian (inner right))
          (innerJacobian left direction) +
        outerJacobian (inner right)
          ((innerJacobian left - innerJacobian right) direction)
  simp only [sub_apply, map_sub]
  abel

/-- The constant map has no forward motion and zero Jacobian. -/
def constantBudget (value : Y) (domain : X → Prop) :
    RegionalJacobianBudget (fun _ : X => value) (fun _ => 0) domain 0 0 0 where
  rate_nonneg := by norm_num
  operatorBound_nonneg := by norm_num
  variation_nonneg := by norm_num
  hasFDerivAt_on_domain := by
    intro state _
    exact hasFDerivAt_const (𝕜 := ℝ) value state
  map_pair_bound := by simp
  jacobian_norm_bound := by simp
  jacobian_pair_bound := by simp

/-- A continuous linear map has constant Jacobian and its operator norm is a
valid forward and derivative bound. -/
def linearBudget (linear : X →L[ℝ] Y) (domain : X → Prop) :
    RegionalJacobianBudget linear (fun _ => linear) domain
      ‖linear‖ ‖linear‖ 0 where
  rate_nonneg := norm_nonneg _
  operatorBound_nonneg := norm_nonneg _
  variation_nonneg := by norm_num
  hasFDerivAt_on_domain := by
    intro state _
    exact linear.hasFDerivAt
  map_pair_bound := by
    intro left right _ _
    rw [← map_sub]
    exact linear.le_opNorm (left - right)
  jacobian_norm_bound := by simp
  jacobian_pair_bound := by simp

/-- Affine map with a source-visible bias. -/
def affineMap (linear : X →L[ℝ] Y) (bias : Y) (state : X) : Y :=
  linear state + bias

/-- Adding a bias changes the forward values but not any pairwise or
Jacobian bound. -/
def affineBudget (linear : X →L[ℝ] Y) (bias : Y) (domain : X → Prop) :
    RegionalJacobianBudget (affineMap linear bias) (fun _ => linear) domain
      ‖linear‖ ‖linear‖ 0 where
  rate_nonneg := norm_nonneg _
  operatorBound_nonneg := norm_nonneg _
  variation_nonneg := by norm_num
  hasFDerivAt_on_domain := by
    intro state _
    have h := (linear.hasFDerivAt (x := state)).add_const bias
    have heq : affineMap linear bias =ᶠ[nhds state]
        (fun x => linear x + bias) := Eventually.of_forall fun _ => rfl
    exact h.congr_of_eventuallyEq heq
  map_pair_bound := by
    intro left right _ _
    rw [show affineMap linear bias left - affineMap linear bias right =
        linear (left - right) by simp [affineMap, map_sub]]
    exact linear.le_opNorm (left - right)
  jacobian_norm_bound := by simp
  jacobian_pair_bound := by simp

/-- Regional Jacobian budgets are closed under addition. -/
def RegionalJacobianBudget.add
    {leftMap rightMap : X → Y}
    {leftJacobian rightJacobian : X → X →L[ℝ] Y}
    {domain : X → Prop}
    {leftRate leftOperator leftVariation
      rightRate rightOperator rightVariation : ℝ}
    (leftBudget : RegionalJacobianBudget leftMap leftJacobian domain
      leftRate leftOperator leftVariation)
    (rightBudget : RegionalJacobianBudget rightMap rightJacobian domain
      rightRate rightOperator rightVariation) :
    RegionalJacobianBudget (addMap leftMap rightMap)
      (addJacobian leftJacobian rightJacobian) domain
      (leftRate + rightRate) (leftOperator + rightOperator)
      (leftVariation + rightVariation) where
  rate_nonneg := add_nonneg leftBudget.rate_nonneg rightBudget.rate_nonneg
  operatorBound_nonneg :=
    add_nonneg leftBudget.operatorBound_nonneg rightBudget.operatorBound_nonneg
  variation_nonneg :=
    add_nonneg leftBudget.variation_nonneg rightBudget.variation_nonneg
  hasFDerivAt_on_domain := by
    intro state hstate
    exact (leftBudget.hasFDerivAt_on_domain state hstate).add
      (rightBudget.hasFDerivAt_on_domain state hstate)
  map_pair_bound := by
    intro left right hleft hright
    have hleftMap := leftBudget.map_pair_bound left right hleft hright
    have hrightMap := rightBudget.map_pair_bound left right hleft hright
    rw [show addMap leftMap rightMap left - addMap leftMap rightMap right =
        (leftMap left - leftMap right) +
          (rightMap left - rightMap right) by
      simp [addMap]
      abel]
    calc
      ‖(leftMap left - leftMap right) +
          (rightMap left - rightMap right)‖ ≤
          ‖leftMap left - leftMap right‖ +
            ‖rightMap left - rightMap right‖ := norm_add_le _ _
      _ ≤ leftRate * ‖left - right‖ +
          rightRate * ‖left - right‖ := add_le_add hleftMap hrightMap
      _ = (leftRate + rightRate) * ‖left - right‖ := by ring
  jacobian_norm_bound := by
    intro state hstate
    calc
      ‖addJacobian leftJacobian rightJacobian state‖ ≤
          ‖leftJacobian state‖ + ‖rightJacobian state‖ := norm_add_le _ _
      _ ≤ leftOperator + rightOperator :=
        add_le_add (leftBudget.jacobian_norm_bound state hstate)
          (rightBudget.jacobian_norm_bound state hstate)
  jacobian_pair_bound := by
    intro left right hleft hright
    have hleftJacobian :=
      leftBudget.jacobian_pair_bound left right hleft hright
    have hrightJacobian :=
      rightBudget.jacobian_pair_bound left right hleft hright
    rw [show addJacobian leftJacobian rightJacobian left -
          addJacobian leftJacobian rightJacobian right =
        (leftJacobian left - leftJacobian right) +
          (rightJacobian left - rightJacobian right) by
      simp [addJacobian]
      abel]
    calc
      ‖(leftJacobian left - leftJacobian right) +
          (rightJacobian left - rightJacobian right)‖ ≤
          ‖leftJacobian left - leftJacobian right‖ +
            ‖rightJacobian left - rightJacobian right‖ := norm_add_le _ _
      _ ≤ leftVariation * ‖left - right‖ +
          rightVariation * ‖left - right‖ :=
        add_le_add hleftJacobian hrightJacobian
      _ = (leftVariation + rightVariation) * ‖left - right‖ := by ring

/-- Regional chain rule.  The domain-preservation premise is load-bearing:
the outer certificate is used only at intermediate states certified to lie in
its own region. -/
def RegionalJacobianBudget.comp
    {outerMap : Y → Z} {outerJacobian : Y → Y →L[ℝ] Z}
    {innerMap : X → Y} {innerJacobian : X → X →L[ℝ] Y}
    {outerDomain : Y → Prop} {innerDomain : X → Prop}
    {outerRate outerOperator outerVariation
      innerRate innerOperator innerVariation : ℝ}
    (outerBudget : RegionalJacobianBudget outerMap outerJacobian outerDomain
      outerRate outerOperator outerVariation)
    (innerBudget : RegionalJacobianBudget innerMap innerJacobian innerDomain
      innerRate innerOperator innerVariation)
    (mapsInto : ∀ state, innerDomain state → outerDomain (innerMap state)) :
    RegionalJacobianBudget (composeMap outerMap innerMap)
      (composeJacobian outerJacobian innerMap innerJacobian) innerDomain
      (outerRate * innerRate) (outerOperator * innerOperator)
      (outerVariation * innerRate * innerOperator +
        outerOperator * innerVariation) where
  rate_nonneg := mul_nonneg outerBudget.rate_nonneg innerBudget.rate_nonneg
  operatorBound_nonneg :=
    mul_nonneg outerBudget.operatorBound_nonneg
      innerBudget.operatorBound_nonneg
  variation_nonneg := add_nonneg
    (mul_nonneg
      (mul_nonneg outerBudget.variation_nonneg innerBudget.rate_nonneg)
      innerBudget.operatorBound_nonneg)
    (mul_nonneg outerBudget.operatorBound_nonneg
      innerBudget.variation_nonneg)
  hasFDerivAt_on_domain := by
    intro state hstate
    exact (outerBudget.hasFDerivAt_on_domain (innerMap state)
      (mapsInto state hstate)).comp state
        (innerBudget.hasFDerivAt_on_domain state hstate)
  map_pair_bound := by
    intro left right hleft hright
    have houter := outerBudget.map_pair_bound (innerMap left) (innerMap right)
      (mapsInto left hleft) (mapsInto right hright)
    have hinner := innerBudget.map_pair_bound left right hleft hright
    calc
      ‖composeMap outerMap innerMap left -
          composeMap outerMap innerMap right‖ ≤
          outerRate * ‖innerMap left - innerMap right‖ := houter
      _ ≤ outerRate * (innerRate * ‖left - right‖) :=
        mul_le_mul_of_nonneg_left hinner outerBudget.rate_nonneg
      _ = (outerRate * innerRate) * ‖left - right‖ := by ring
  jacobian_norm_bound := by
    intro state hstate
    have hcomp := (outerJacobian (innerMap state)).opNorm_comp_le
      (innerJacobian state)
    calc
      ‖composeJacobian outerJacobian innerMap innerJacobian state‖ ≤
          ‖outerJacobian (innerMap state)‖ * ‖innerJacobian state‖ := hcomp
      _ ≤ outerOperator * innerOperator := by
        exact mul_le_mul
          (outerBudget.jacobian_norm_bound (innerMap state)
            (mapsInto state hstate))
          (innerBudget.jacobian_norm_bound state hstate)
          (norm_nonneg _) outerBudget.operatorBound_nonneg
  jacobian_pair_bound := by
    intro left right hleft hright
    have houterVariation := outerBudget.jacobian_pair_bound
      (innerMap left) (innerMap right) (mapsInto left hleft)
      (mapsInto right hright)
    have hinnerMap := innerBudget.map_pair_bound left right hleft hright
    have hinnerNorm := innerBudget.jacobian_norm_bound left hleft
    have houterNorm := outerBudget.jacobian_norm_bound
      (innerMap right) (mapsInto right hright)
    have hinnerVariation :=
      innerBudget.jacobian_pair_bound left right hleft hright
    rw [composeJacobian_sub]
    calc
      ‖(outerJacobian (innerMap left) - outerJacobian (innerMap right)).comp
            (innerJacobian left) +
          (outerJacobian (innerMap right)).comp
            (innerJacobian left - innerJacobian right)‖ ≤
          ‖(outerJacobian (innerMap left) - outerJacobian (innerMap right)).comp
              (innerJacobian left)‖ +
            ‖(outerJacobian (innerMap right)).comp
              (innerJacobian left - innerJacobian right)‖ := norm_add_le _ _
      _ ≤
          ‖outerJacobian (innerMap left) - outerJacobian (innerMap right)‖ *
              ‖innerJacobian left‖ +
            ‖outerJacobian (innerMap right)‖ *
              ‖innerJacobian left - innerJacobian right‖ :=
        add_le_add
          ((outerJacobian (innerMap left) -
              outerJacobian (innerMap right)).opNorm_comp_le
                (innerJacobian left))
          ((outerJacobian (innerMap right)).opNorm_comp_le
            (innerJacobian left - innerJacobian right))
      _ ≤
          (outerVariation * ‖innerMap left - innerMap right‖) *
              innerOperator +
            outerOperator * (innerVariation * ‖left - right‖) := by
        exact add_le_add
          (mul_le_mul houterVariation hinnerNorm
            (norm_nonneg _) (mul_nonneg outerBudget.variation_nonneg
              (norm_nonneg _)))
          (mul_le_mul houterNorm hinnerVariation
            (norm_nonneg _) outerBudget.operatorBound_nonneg)
      _ ≤
          (outerVariation * (innerRate * ‖left - right‖)) *
              innerOperator +
            outerOperator * (innerVariation * ‖left - right‖) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinnerMap
              outerBudget.variation_nonneg)
            innerBudget.operatorBound_nonneg) (le_refl _)
      _ = (outerVariation * innerRate * innerOperator +
            outerOperator * innerVariation) * ‖left - right‖ := by ring

/-! ## The source-shaped three-site recurrence -/

/-- First hidden state: a fixed parent-dependent prediction plus the first
masked error injection. -/
def firstSiteState (base : Y) (injectOne : X →L[ℝ] Y) (error : X) : Y :=
  base + injectOne error

/-- A later hidden state: a nonlinear transition followed by an additive
masked error injection. -/
def nextSiteState (transition : Y → Y) (previous : X → Y)
    (inject : X →L[ℝ] Y) (error : X) : Y :=
  transition (previous error) + inject error

/-- Final residual readout after exactly three error-injection sites. -/
def threeSiteResidual
    (base : Y) (injectOne injectTwo injectThree : X →L[ℝ] Y)
    (transitionTwo transitionThree : Y → Y)
    (readout : Y →L[ℝ] Z) : X → Z :=
  composeMap readout
    (addMap
      (composeMap transitionThree
        (addMap
          (composeMap transitionTwo
            (addMap (fun _ : X => base) injectOne))
          injectTwo))
      injectThree)

/-- Symbolic Jacobian of the exact three-site recurrence. -/
def threeSiteResidualJacobian
    (base : Y) (injectOne injectTwo injectThree : X →L[ℝ] Y)
    (transitionTwo transitionThree : Y → Y)
    (transitionTwoJacobian transitionThreeJacobian : Y → Y →L[ℝ] Y)
    (readout : Y →L[ℝ] Z) : X → X →L[ℝ] Z :=
  composeJacobian (fun _ : Y => readout)
    (addMap
      (composeMap transitionThree
        (addMap
          (composeMap transitionTwo
            (addMap (fun _ : X => base) injectOne))
          injectTwo))
      injectThree)
    (addJacobian
      (composeJacobian transitionThreeJacobian
        (addMap
          (composeMap transitionTwo
            (addMap (fun _ : X => base) injectOne))
          injectTwo)
        (addJacobian
          (composeJacobian transitionTwoJacobian
            (addMap (fun _ : X => base) injectOne)
            (addJacobian (fun _ : X => 0) (fun _ => injectOne)))
          (fun _ => injectTwo)))
      (fun _ => injectThree))

/-- Exact source-shaped residual when the final checkpoint layer carries a
bias.  The earlier `threeSiteResidual` is the zero-bias specialization. -/
def threeSiteAffineResidual
    (base : Y) (injectOne injectTwo injectThree : X →L[ℝ] Y)
    (transitionTwo transitionThree : Y → Y)
    (readout : Y →L[ℝ] Z) (readoutBias : Z) : X → Z :=
  fun error =>
    threeSiteResidual base injectOne injectTwo injectThree
      transitionTwo transitionThree readout error + readoutBias

/-- The affine readout has the same error-coordinate Jacobian as its
bias-free specialization. -/
def threeSiteAffineResidualJacobian
    (base : Y) (injectOne injectTwo injectThree : X →L[ℝ] Y)
    (transitionTwo transitionThree : Y → Y)
    (transitionTwoJacobian transitionThreeJacobian : Y → Y →L[ℝ] Y)
    (readout : Y →L[ℝ] Z) (_readoutBias : Z) : X → X →L[ℝ] Z :=
  threeSiteResidualJacobian base injectOne injectTwo injectThree
    transitionTwo transitionThree transitionTwoJacobian
    transitionThreeJacobian readout

@[simp] theorem threeSiteAffineResidual_zeroBias
    (base : Y) (injectOne injectTwo injectThree : X →L[ℝ] Y)
    (transitionTwo transitionThree : Y → Y)
    (readout : Y →L[ℝ] Z) :
    threeSiteAffineResidual base injectOne injectTwo injectThree
        transitionTwo transitionThree readout 0 =
      threeSiteResidual base injectOne injectTwo injectThree
        transitionTwo transitionThree readout := by
  funext error
  simp [threeSiteAffineResidual]

/-- The exact bound recurrence generated by a nonlinear transition plus an
additive error injection. -/
def nextSiteRate (transitionRate previousRate injectionNorm : ℝ) : ℝ :=
  transitionRate * previousRate + injectionNorm

def nextSiteOperator
    (transitionOperator previousOperator injectionNorm : ℝ) : ℝ :=
  transitionOperator * previousOperator + injectionNorm

def nextSiteVariation
    (transitionVariation previousRate previousOperator
      transitionOperator previousVariation : ℝ) : ℝ :=
  transitionVariation * previousRate * previousOperator +
    transitionOperator * previousVariation

/-! ## Centered-ball propagation through the three-site recurrence -/

/-- Center of the first hidden site induced by a declared error center. -/
def firstSiteCenter
    (base : Y) (injectOne : X →L[ℝ] Y) (errorCenter : X) : Y :=
  firstSiteState base injectOne errorCenter

/-- Radius transported from the error ball through the first linear
injection. -/
def firstSiteRadius (injectOne : X →L[ℝ] Y) (errorRadius : ℝ) : ℝ :=
  ‖injectOne‖ * errorRadius

/-- Center of the second hidden site induced by the same error center. -/
def secondSiteCenter
    (base : Y) (injectOne injectTwo : X →L[ℝ] Y)
    (transitionTwo : Y → Y) (errorCenter : X) : Y :=
  nextSiteState transitionTwo (firstSiteState base injectOne) injectTwo
    errorCenter

/-- Radius transported through the first nonlinear transition and the second
linear injection. -/
def secondSiteRadius
    (transitionRate : ℝ) (injectOne injectTwo : X →L[ℝ] Y)
    (errorRadius : ℝ) : ℝ :=
  nextSiteRate transitionRate ‖injectOne‖ ‖injectTwo‖ * errorRadius

/-- The first hidden site automatically lies in the ball obtained by applying
the first injection norm to the declared error radius. -/
theorem firstSiteState_mem_centeredBall
    (base : Y) (injectOne : X →L[ℝ] Y)
    (errorCenter error : X) (errorRadius : ℝ)
    (herror : ‖error - errorCenter‖ ≤ errorRadius) :
    ‖firstSiteState base injectOne error -
        firstSiteCenter base injectOne errorCenter‖ ≤
      firstSiteRadius injectOne errorRadius := by
  have hinject := injectOne.le_opNorm (error - errorCenter)
  rw [show firstSiteState base injectOne error -
      firstSiteCenter base injectOne errorCenter =
        injectOne (error - errorCenter) by
    simp [firstSiteState, firstSiteCenter, map_sub]]
  calc
    ‖injectOne (error - errorCenter)‖ ≤
        ‖injectOne‖ * ‖error - errorCenter‖ := hinject
    _ ≤ ‖injectOne‖ * errorRadius := by
      exact mul_le_mul_of_nonneg_left herror (norm_nonneg _)
    _ = firstSiteRadius injectOne errorRadius := rfl

/-- Once the first transition has a centered-ball budget, the second hidden
site automatically lies in the ball whose radius follows `nextSiteRate`.
This discharges the intermediate-domain premise structurally. -/
theorem secondSiteState_mem_centeredBall
    (base : Y) (injectOne injectTwo : X →L[ℝ] Y)
    (transitionTwo : Y → Y) (transitionTwoJacobian : Y → Y →L[ℝ] Y)
    (errorCenter error : X) (errorRadius transitionRate
      transitionOperator transitionVariation : ℝ)
    (herrorRadius : 0 ≤ errorRadius)
    (budgetTwo : RegionalJacobianBudget transitionTwo transitionTwoJacobian
      (fun state => ‖state - firstSiteCenter base injectOne errorCenter‖ ≤
        firstSiteRadius injectOne errorRadius)
      transitionRate transitionOperator transitionVariation)
    (herror : ‖error - errorCenter‖ ≤ errorRadius) :
    ‖nextSiteState transitionTwo (firstSiteState base injectOne) injectTwo error -
        secondSiteCenter base injectOne injectTwo transitionTwo errorCenter‖ ≤
      secondSiteRadius transitionRate injectOne injectTwo errorRadius := by
  have hfirst := firstSiteState_mem_centeredBall base injectOne
    errorCenter error errorRadius herror
  have hfirstCenter :
      ‖firstSiteState base injectOne errorCenter -
          firstSiteCenter base injectOne errorCenter‖ ≤
        firstSiteRadius injectOne errorRadius := by
    simp [firstSiteCenter, firstSiteRadius]
    positivity
  have htransition := budgetTwo.map_pair_bound
    (firstSiteState base injectOne error)
    (firstSiteState base injectOne errorCenter) hfirst hfirstCenter
  have hinject := injectTwo.le_opNorm (error - errorCenter)
  have hnextRate :
      0 ≤ nextSiteRate transitionRate ‖injectOne‖ ‖injectTwo‖ := by
    exact add_nonneg (mul_nonneg budgetTwo.rate_nonneg (norm_nonneg _))
      (norm_nonneg _)
  rw [show nextSiteState transitionTwo (firstSiteState base injectOne) injectTwo
        error -
      secondSiteCenter base injectOne injectTwo transitionTwo errorCenter =
        (transitionTwo (firstSiteState base injectOne error) -
          transitionTwo (firstSiteState base injectOne errorCenter)) +
        injectTwo (error - errorCenter) by
    simp [nextSiteState, secondSiteCenter, map_sub]
    abel]
  calc
    ‖(transitionTwo (firstSiteState base injectOne error) -
          transitionTwo (firstSiteState base injectOne errorCenter)) +
        injectTwo (error - errorCenter)‖ ≤
      ‖transitionTwo (firstSiteState base injectOne error) -
          transitionTwo (firstSiteState base injectOne errorCenter)‖ +
        ‖injectTwo (error - errorCenter)‖ := norm_add_le _ _
    _ ≤ transitionRate *
          ‖firstSiteState base injectOne error -
            firstSiteState base injectOne errorCenter‖ +
        ‖injectTwo‖ * ‖error - errorCenter‖ :=
      add_le_add htransition hinject
    _ ≤ transitionRate * (‖injectOne‖ * ‖error - errorCenter‖) +
        ‖injectTwo‖ * ‖error - errorCenter‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (firstSiteState_mem_centeredBall base injectOne errorCenter error
            ‖error - errorCenter‖ (le_refl _))
          budgetTwo.rate_nonneg)
        (le_refl _)
    _ = nextSiteRate transitionRate ‖injectOne‖ ‖injectTwo‖ *
        ‖error - errorCenter‖ := by
      simp [nextSiteRate]
      ring
    _ ≤ nextSiteRate transitionRate ‖injectOne‖ ‖injectTwo‖ * errorRadius :=
      mul_le_mul_of_nonneg_left herror hnextRate
    _ = secondSiteRadius transitionRate injectOne injectTwo errorRadius := rfl

/-- A complete three-site source budget.  The first nonlinear hidden block is
independent of the error coordinates and is represented by `base`; the next
two nonlinear blocks and the final affine readout match the registered
three-error-site recurrence. -/
def threeSiteResidualBudget
    {errorDomain stateOneDomain stateTwoDomain : _ → Prop}
    (base : Y) (injectOne injectTwo injectThree : X →L[ℝ] Y)
    (transitionTwo transitionThree : Y → Y)
    (transitionTwoJacobian transitionThreeJacobian : Y → Y →L[ℝ] Y)
    (readout : Y →L[ℝ] Z)
    {rateTwo operatorTwo variationTwo
      rateThree operatorThree variationThree : ℝ}
    (budgetTwo : RegionalJacobianBudget transitionTwo transitionTwoJacobian
      stateOneDomain rateTwo operatorTwo variationTwo)
    (budgetThree : RegionalJacobianBudget transitionThree transitionThreeJacobian
      stateTwoDomain rateThree operatorThree variationThree)
    (firstMapsInto : ∀ error, errorDomain error →
      stateOneDomain (firstSiteState base injectOne error))
    (secondMapsInto : ∀ error, errorDomain error →
      stateTwoDomain (nextSiteState transitionTwo
        (firstSiteState base injectOne) injectTwo error)) :
    RegionalJacobianBudget
      (threeSiteResidual base injectOne injectTwo injectThree
        transitionTwo transitionThree readout)
      (threeSiteResidualJacobian base injectOne injectTwo injectThree
        transitionTwo transitionThree transitionTwoJacobian
        transitionThreeJacobian readout)
      errorDomain
      (‖readout‖ *
        nextSiteRate rateThree
          (nextSiteRate rateTwo ‖injectOne‖ ‖injectTwo‖)
          ‖injectThree‖)
      (‖readout‖ *
        nextSiteOperator operatorThree
          (nextSiteOperator operatorTwo ‖injectOne‖ ‖injectTwo‖)
          ‖injectThree‖)
      (‖readout‖ *
        nextSiteVariation variationThree
          (nextSiteRate rateTwo ‖injectOne‖ ‖injectTwo‖)
          (nextSiteOperator operatorTwo ‖injectOne‖ ‖injectTwo‖)
          operatorThree
          (nextSiteVariation variationTwo ‖injectOne‖ ‖injectOne‖
            operatorTwo 0)) := by
  let firstBudget :=
    (constantBudget base errorDomain).add (linearBudget injectOne errorDomain)
  let secondBudget :=
    (budgetTwo.comp firstBudget firstMapsInto).add
      (linearBudget injectTwo errorDomain)
  let thirdBudget :=
    (budgetThree.comp secondBudget secondMapsInto).add
      (linearBudget injectThree errorDomain)
  let finalBudget :=
    (linearBudget readout (fun state : Y => True)).comp thirdBudget
      (by intro state _; trivial)
  simpa only [firstBudget, secondBudget, thirdBudget, finalBudget,
    firstSiteState, nextSiteState, threeSiteResidual,
    threeSiteResidualJacobian, nextSiteRate, nextSiteOperator,
    nextSiteVariation, zero_add, add_zero, mul_zero, zero_mul] using finalBudget

/-- Complete three-site budget for the exact affine checkpoint readout.  The
readout bias changes the residual image but contributes zero to all three
derivative constants. -/
def threeSiteAffineResidualBudget
    {errorDomain stateOneDomain stateTwoDomain : _ → Prop}
    (base : Y) (injectOne injectTwo injectThree : X →L[ℝ] Y)
    (transitionTwo transitionThree : Y → Y)
    (transitionTwoJacobian transitionThreeJacobian : Y → Y →L[ℝ] Y)
    (readout : Y →L[ℝ] Z) (readoutBias : Z)
    {rateTwo operatorTwo variationTwo
      rateThree operatorThree variationThree : ℝ}
    (budgetTwo : RegionalJacobianBudget transitionTwo transitionTwoJacobian
      stateOneDomain rateTwo operatorTwo variationTwo)
    (budgetThree : RegionalJacobianBudget transitionThree transitionThreeJacobian
      stateTwoDomain rateThree operatorThree variationThree)
    (firstMapsInto : ∀ error, errorDomain error →
      stateOneDomain (firstSiteState base injectOne error))
    (secondMapsInto : ∀ error, errorDomain error →
      stateTwoDomain (nextSiteState transitionTwo
        (firstSiteState base injectOne) injectTwo error)) :
    RegionalJacobianBudget
      (threeSiteAffineResidual base injectOne injectTwo injectThree
        transitionTwo transitionThree readout readoutBias)
      (threeSiteAffineResidualJacobian base injectOne injectTwo injectThree
        transitionTwo transitionThree transitionTwoJacobian
        transitionThreeJacobian readout readoutBias)
      errorDomain
      (‖readout‖ *
        nextSiteRate rateThree
          (nextSiteRate rateTwo ‖injectOne‖ ‖injectTwo‖)
          ‖injectThree‖)
      (‖readout‖ *
        nextSiteOperator operatorThree
          (nextSiteOperator operatorTwo ‖injectOne‖ ‖injectTwo‖)
          ‖injectThree‖)
      (‖readout‖ *
        nextSiteVariation variationThree
          (nextSiteRate rateTwo ‖injectOne‖ ‖injectTwo‖)
          (nextSiteOperator operatorTwo ‖injectOne‖ ‖injectTwo‖)
          operatorThree
          (nextSiteVariation variationTwo ‖injectOne‖ ‖injectOne‖
            operatorTwo 0)) := by
  let coreBudget := threeSiteResidualBudget base injectOne injectTwo injectThree
    transitionTwo transitionThree transitionTwoJacobian
    transitionThreeJacobian readout budgetTwo budgetThree
    firstMapsInto secondMapsInto
  let biasBudget := constantBudget readoutBias errorDomain
  convert coreBudget.add biasBudget using 1
  · rfl
  · funext state
    simp [threeSiteAffineResidualJacobian, addJacobian]
  · simp
  · simp
  · simp

/-- Centered-ball specialization of `threeSiteResidualBudget`.  The first and
second intermediate-domain obligations are derived from the injection norms
and the second transition's forward rate, rather than supplied as independent
assumptions. -/
def threeSiteResidualBallBudget
    (base : Y) (injectOne injectTwo injectThree : X →L[ℝ] Y)
    (transitionTwo transitionThree : Y → Y)
    (transitionTwoJacobian transitionThreeJacobian : Y → Y →L[ℝ] Y)
    (readout : Y →L[ℝ] Z)
    (errorCenter : X) (errorRadius : ℝ) (herrorRadius : 0 ≤ errorRadius)
    {rateTwo operatorTwo variationTwo
      rateThree operatorThree variationThree : ℝ}
    (budgetTwo : RegionalJacobianBudget transitionTwo transitionTwoJacobian
      (fun state => ‖state - firstSiteCenter base injectOne errorCenter‖ ≤
        firstSiteRadius injectOne errorRadius)
      rateTwo operatorTwo variationTwo)
    (budgetThree : RegionalJacobianBudget transitionThree transitionThreeJacobian
      (fun state => ‖state - secondSiteCenter base injectOne injectTwo
        transitionTwo errorCenter‖ ≤
        secondSiteRadius rateTwo injectOne injectTwo errorRadius)
      rateThree operatorThree variationThree) :
    RegionalJacobianBudget
      (threeSiteResidual base injectOne injectTwo injectThree
        transitionTwo transitionThree readout)
      (threeSiteResidualJacobian base injectOne injectTwo injectThree
        transitionTwo transitionThree transitionTwoJacobian
        transitionThreeJacobian readout)
      (fun error => ‖error - errorCenter‖ ≤ errorRadius)
      (‖readout‖ *
        nextSiteRate rateThree
          (nextSiteRate rateTwo ‖injectOne‖ ‖injectTwo‖)
          ‖injectThree‖)
      (‖readout‖ *
        nextSiteOperator operatorThree
          (nextSiteOperator operatorTwo ‖injectOne‖ ‖injectTwo‖)
          ‖injectThree‖)
      (‖readout‖ *
        nextSiteVariation variationThree
          (nextSiteRate rateTwo ‖injectOne‖ ‖injectTwo‖)
          (nextSiteOperator operatorTwo ‖injectOne‖ ‖injectTwo‖)
          operatorThree
          (nextSiteVariation variationTwo ‖injectOne‖ ‖injectOne‖
            operatorTwo 0)) :=
  threeSiteResidualBudget base injectOne injectTwo injectThree
    transitionTwo transitionThree transitionTwoJacobian
    transitionThreeJacobian readout budgetTwo budgetThree
    (fun error herror =>
      firstSiteState_mem_centeredBall base injectOne errorCenter error
        errorRadius herror)
    (fun error herror =>
      secondSiteState_mem_centeredBall base injectOne injectTwo
        transitionTwo transitionTwoJacobian errorCenter error errorRadius
        rateTwo operatorTwo variationTwo herrorRadius budgetTwo herror)

/-- Centered-ball specialization for the exact affine checkpoint readout. -/
def threeSiteAffineResidualBallBudget
    (base : Y) (injectOne injectTwo injectThree : X →L[ℝ] Y)
    (transitionTwo transitionThree : Y → Y)
    (transitionTwoJacobian transitionThreeJacobian : Y → Y →L[ℝ] Y)
    (readout : Y →L[ℝ] Z) (readoutBias : Z)
    (errorCenter : X) (errorRadius : ℝ) (herrorRadius : 0 ≤ errorRadius)
    {rateTwo operatorTwo variationTwo
      rateThree operatorThree variationThree : ℝ}
    (budgetTwo : RegionalJacobianBudget transitionTwo transitionTwoJacobian
      (fun state => ‖state - firstSiteCenter base injectOne errorCenter‖ ≤
        firstSiteRadius injectOne errorRadius)
      rateTwo operatorTwo variationTwo)
    (budgetThree : RegionalJacobianBudget transitionThree transitionThreeJacobian
      (fun state => ‖state - secondSiteCenter base injectOne injectTwo
        transitionTwo errorCenter‖ ≤
        secondSiteRadius rateTwo injectOne injectTwo errorRadius)
      rateThree operatorThree variationThree) :
    RegionalJacobianBudget
      (threeSiteAffineResidual base injectOne injectTwo injectThree
        transitionTwo transitionThree readout readoutBias)
      (threeSiteAffineResidualJacobian base injectOne injectTwo injectThree
        transitionTwo transitionThree transitionTwoJacobian
        transitionThreeJacobian readout readoutBias)
      (fun error => ‖error - errorCenter‖ ≤ errorRadius)
      (‖readout‖ *
        nextSiteRate rateThree
          (nextSiteRate rateTwo ‖injectOne‖ ‖injectTwo‖)
          ‖injectThree‖)
      (‖readout‖ *
        nextSiteOperator operatorThree
          (nextSiteOperator operatorTwo ‖injectOne‖ ‖injectTwo‖)
          ‖injectThree‖)
      (‖readout‖ *
        nextSiteVariation variationThree
          (nextSiteRate rateTwo ‖injectOne‖ ‖injectTwo‖)
          (nextSiteOperator operatorTwo ‖injectOne‖ ‖injectTwo‖)
          operatorThree
          (nextSiteVariation variationTwo ‖injectOne‖ ‖injectOne‖
            operatorTwo 0)) :=
  threeSiteAffineResidualBudget base injectOne injectTwo injectThree
    transitionTwo transitionThree transitionTwoJacobian
    transitionThreeJacobian readout readoutBias budgetTwo budgetThree
    (fun error herror =>
      firstSiteState_mem_centeredBall base injectOne errorCenter error
        errorRadius herror)
    (fun error herror =>
      secondSiteState_mem_centeredBall base injectOne injectTwo
        transitionTwo transitionTwoJacobian errorCenter error errorRadius
        rateTwo operatorTwo variationTwo herrorRadius budgetTwo herror)

/-! ## Bridge to nonlinear credit transport -/

section TransportBridge

open AmortizedInitialization
open ErrorCoordinateResidualSemantics
open LocalAmortizedInitialization
open RegionalErrorCoordinateContraction
open NonlinearReadoutGradientTransport

variable {State Feature : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State] [CompleteSpace State]
  [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
  [CompleteSpace Feature]

/-- A compositional forward/Jacobian budget on a closed ball supplies exactly
the readout-side fields of the nonlinear credit-transport certificate.  The
two remaining premises concern the frozen task gradient on the readout image
and therefore remain separate from adapter geometry. -/
noncomputable def RegionalJacobianBudget.toForwardJacobianGradientBudget
    {readout : State → Feature}
    {jacobian : State → State →L[ℝ] Feature}
    {outputGradient : Feature → Feature}
    {center : State}
    {radius readoutRate jacobianRate jacobianVariation
      outputGradientRate outputGradientBound : ℝ}
    (budget : RegionalJacobianBudget readout jacobian
      (fun state => InClosedBall center radius state)
      readoutRate jacobianRate jacobianVariation)
    (radius_nonneg : 0 ≤ radius)
    (outputGradientRate_nonneg : 0 ≤ outputGradientRate)
    (outputGradientBound_nonneg : 0 ≤ outputGradientBound)
    (outputGradient_lipschitz_on_image : ∀ left right,
      InClosedBall center radius left → InClosedBall center radius right →
      ‖outputGradient (readout left) - outputGradient (readout right)‖ ≤
        outputGradientRate * ‖readout left - readout right‖)
    (outputGradient_norm_on_image : ∀ state,
      InClosedBall center radius state →
      ‖outputGradient (readout state)‖ ≤ outputGradientBound) :
    ForwardJacobianGradientBudget readout jacobian outputGradient
      center radius readoutRate jacobianRate jacobianVariation
      outputGradientRate outputGradientBound where
  radius_nonneg := radius_nonneg
  readoutRate_nonneg := budget.rate_nonneg
  jacobianRate_nonneg := budget.operatorBound_nonneg
  jacobianVariation_nonneg := budget.variation_nonneg
  outputGradientRate_nonneg := outputGradientRate_nonneg
  outputGradientBound_nonneg := outputGradientBound_nonneg
  readout_lipschitz_on_ball := budget.map_pair_bound
  jacobian_norm_on_ball := budget.jacobian_norm_bound
  jacobian_variation_on_ball := budget.jacobian_pair_bound
  outputGradient_lipschitz_on_image := outputGradient_lipschitz_on_image
  outputGradient_norm_on_image := outputGradient_norm_on_image

/-- End-to-end bridge: compositional source bounds plus frozen-task image
bounds yield the regional error-coordinate contraction interface already used
by finite-settling and residual-stopping theory. -/
noncomputable def RegionalJacobianBudget.toRegionalTaskGradientCertificate
    {readout : State → Feature}
    {jacobian : State → State →L[ℝ] Feature}
    {outputGradient : Feature → Feature}
    {center : State}
    {radius readoutRate jacobianRate jacobianVariation
      outputGradientRate outputGradientBound precision : ℝ}
    (budget : RegionalJacobianBudget readout jacobian
      (fun state => InClosedBall center radius state)
      readoutRate jacobianRate jacobianVariation)
    (radius_nonneg : 0 ≤ radius)
    (outputGradientRate_nonneg : 0 ≤ outputGradientRate)
    (outputGradientBound_nonneg : 0 ≤ outputGradientBound)
    (outputGradient_lipschitz_on_image : ∀ left right,
      InClosedBall center radius left → InClosedBall center radius right →
      ‖outputGradient (readout left) - outputGradient (readout right)‖ ≤
        outputGradientRate * ‖readout left - readout right‖)
    (outputGradient_norm_on_image : ∀ state,
      InClosedBall center radius state →
      ‖outputGradient (readout state)‖ ≤ outputGradientBound)
    (precision_dominates :
      pullbackGradientRate readoutRate jacobianRate jacobianVariation
        outputGradientRate outputGradientBound < precision)
    (stationary :
      errorCoordinateEnergyGradient precision
        (pullbackTaskGradient readout (adjointJacobianPullback jacobian)
          outputGradient) center = 0) :
    RegionalTaskGradientCertificate precision
      (pullbackGradientRate readoutRate jacobianRate jacobianVariation
        outputGradientRate outputGradientBound)
      (pullbackGradientRate readoutRate jacobianRate jacobianVariation
        outputGradientRate outputGradientBound)
      (pullbackTaskGradient readout (adjointJacobianPullback jacobian)
        outputGradient) center radius :=
  ((budget.toForwardJacobianGradientBudget radius_nonneg
      outputGradientRate_nonneg outputGradientBound_nonneg
      outputGradient_lipschitz_on_image outputGradient_norm_on_image).toPullbackGradientBudget)
    |>.toRegionalTaskGradientCertificate precision_dominates stationary

end TransportBridge

/-! ## Scalar fixture: the nonlinear chain-rule cross term is necessary -/

def scalarDouble : ℝ → ℝ := (2 : ℝ) • id

noncomputable def scalarDoubleJacobian (_state : ℝ) : ℝ →L[ℝ] ℝ :=
  (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ

/-- Dropping the injection operator norm from centered-ball propagation is
unsound: doubling maps the unit error displacement to a displacement of two. -/
theorem firstSiteRadius_without_injection_norm_fails :
    ¬ ‖firstSiteState (0 : ℝ) (scalarDoubleJacobian 0) 1 -
        firstSiteCenter 0 (scalarDoubleJacobian 0) 0‖ ≤ 1 := by
  norm_num [firstSiteState, firstSiteCenter, scalarDoubleJacobian,
    smul_apply]

def scalarHalfSquare : ℝ → ℝ :=
  (1 / 2 : ℝ) • fun state : ℝ => state ^ 2

noncomputable def scalarHalfSquareJacobian (state : ℝ) : ℝ →L[ℝ] ℝ :=
  state • ContinuousLinearMap.id ℝ ℝ

def unitBall (state : ℝ) : Prop := ‖state‖ ≤ 1
def doubleBall (state : ℝ) : Prop := ‖state‖ ≤ 2

noncomputable def scalarDoubleBudget :
    RegionalJacobianBudget scalarDouble scalarDoubleJacobian unitBall 2 2 0 where
  rate_nonneg := by norm_num
  operatorBound_nonneg := by norm_num
  variation_nonneg := by norm_num
  hasFDerivAt_on_domain := by
    intro state _
    simpa only [scalarDouble, scalarDoubleJacobian] using
      (hasFDerivAt_id state).const_smul (2 : ℝ)
  map_pair_bound := by
    intro left right _ _
    norm_num [scalarDouble, Real.norm_eq_abs]
    rw [show 2 * left - 2 * right = 2 * (left - right) by ring, abs_mul]
    norm_num
  jacobian_norm_bound := by
    intro state _
    rw [scalarDoubleJacobian, norm_smul, ContinuousLinearMap.norm_id]
    norm_num [Real.norm_eq_abs]
  jacobian_pair_bound := by
    intro left right _ _
    simp [scalarDoubleJacobian]

noncomputable def scalarHalfSquareBudget :
    RegionalJacobianBudget scalarHalfSquare scalarHalfSquareJacobian
      doubleBall 2 2 1 where
  rate_nonneg := by norm_num
  operatorBound_nonneg := by norm_num
  variation_nonneg := by norm_num
  hasFDerivAt_on_domain := by
    intro state _
    convert (hasFDerivAt_pow (𝕜 := ℝ) (x := state) 2).const_smul
      (1 / 2 : ℝ) using 1
    · rfl
    · ext
      simp [scalarHalfSquareJacobian]
  map_pair_bound := by
    intro left right hleft hright
    rw [show scalarHalfSquare left - scalarHalfSquare right =
        (left - right) * (left + right) / 2 by
      simp [scalarHalfSquare]
      ring]
    rw [Real.norm_eq_abs, abs_div, abs_mul]
    norm_num [doubleBall, Real.norm_eq_abs] at hleft hright ⊢
    have hsum : |left + right| ≤ 4 := by
      calc
        |left + right| ≤ |left| + |right| := abs_add_le _ _
        _ ≤ 4 := by linarith
    nlinarith [abs_nonneg (left - right)]
  jacobian_norm_bound := by
    intro state hstate
    rw [scalarHalfSquareJacobian, norm_smul,
      ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]
    simpa [doubleBall, Real.norm_eq_abs] using hstate
  jacobian_pair_bound := by
    intro left right _ _
    rw [show scalarHalfSquareJacobian left - scalarHalfSquareJacobian right =
        (left - right) • ContinuousLinearMap.id ℝ ℝ by
      ext
      simp [scalarHalfSquareJacobian]
      ]
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]
    simp

theorem scalarDouble_mapsInto (state : ℝ) (hstate : unitBall state) :
    doubleBall (scalarDouble state) := by
  norm_num [unitBall, doubleBall, scalarDouble, Real.norm_eq_abs] at hstate ⊢
  simpa [abs_mul] using mul_le_mul_of_nonneg_left hstate (by norm_num : 0 ≤ (2 : ℝ))

noncomputable def scalarComposedBudget :
    RegionalJacobianBudget
      (composeMap scalarHalfSquare scalarDouble)
      (composeJacobian scalarHalfSquareJacobian scalarDouble
        scalarDoubleJacobian)
      unitBall 4 4 4 := by
  convert scalarHalfSquareBudget.comp scalarDoubleBudget scalarDouble_mapsInto
    using 1 <;> norm_num

theorem scalarComposedJacobian_at (state : ℝ) :
    composeJacobian scalarHalfSquareJacobian scalarDouble
      scalarDoubleJacobian state =
        (4 * state) • ContinuousLinearMap.id ℝ ℝ := by
  ext
  simp [composeJacobian, scalarHalfSquareJacobian, scalarDouble,
    scalarDoubleJacobian]
  ring

theorem scalarComposedJacobian_sub_norm (left right : ℝ) :
    ‖composeJacobian scalarHalfSquareJacobian scalarDouble
          scalarDoubleJacobian left -
        composeJacobian scalarHalfSquareJacobian scalarDouble
          scalarDoubleJacobian right‖ = |4 * (left - right)| := by
  rw [scalarComposedJacobian_at, scalarComposedJacobian_at,
    show (4 * left) • ContinuousLinearMap.id ℝ ℝ -
        (4 * right) • ContinuousLinearMap.id ℝ ℝ =
      (4 * (left - right)) • ContinuousLinearMap.id ℝ ℝ by
        ext
        simp
        ring,
    norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]

/-- Omitting the inner forward rate from the nonlinear chain-rule term would
assign variation `1 * 2 = 2`; the actual composed Jacobian changes by four
between zero and one. -/
theorem scalarComposition_inner_rate_is_necessary :
    ¬ (∀ left right : ℝ,
      unitBall left → unitBall right →
      ‖composeJacobian scalarHalfSquareJacobian scalarDouble
          scalarDoubleJacobian left -
        composeJacobian scalarHalfSquareJacobian scalarDouble
          scalarDoubleJacobian right‖ ≤
        2 * ‖left - right‖) := by
  intro claimed
  have hbad := claimed 1 0 (by norm_num [unitBall]) (by norm_num [unitBall])
  rw [scalarComposedJacobian_sub_norm] at hbad
  norm_num at hbad

/-- Enlarging all three constants preserves the scalar doubling budget. -/
noncomputable def scalarDoubleWeakenedBudget :
    RegionalJacobianBudget scalarDouble scalarDoubleJacobian unitBall
      3 4 1 :=
  scalarDoubleBudget.weaken (by norm_num) (by norm_num) (by norm_num)

/-- A claimed rate below two is false for scalar doubling on the unit ball. -/
theorem scalarDouble_rate_cannot_be_tightened :
    ¬ ∀ left right : ℝ,
      unitBall left → unitBall right →
      |scalarDouble left - scalarDouble right| ≤
        (3 / 2 : ℝ) * |left - right| := by
  intro claimed
  have h := claimed 1 0 (by norm_num [unitBall]) (by norm_num [unitBall])
  norm_num [scalarDouble] at h

/-- A nonzero affine bias is observable even when the linear readout is zero;
it therefore cannot be erased from the source-level forward map. -/
theorem affineBias_cannot_be_erased :
    affineMap (0 : ℝ →L[ℝ] ℝ) 1 0 ≠ (0 : ℝ →L[ℝ] ℝ) 0 := by
  norm_num [affineMap]

#print axioms RegionalJacobianBudget.weaken
#print axioms RegionalJacobianBudget.add
#print axioms RegionalJacobianBudget.comp
#print axioms affineBudget
#print axioms threeSiteResidualBudget
#print axioms threeSiteResidualBallBudget
#print axioms threeSiteAffineResidualBudget
#print axioms threeSiteAffineResidualBallBudget
#print axioms RegionalJacobianBudget.toRegionalTaskGradientCertificate
#print axioms scalarComposedBudget
#print axioms scalarComposition_inner_rate_is_necessary
#print axioms firstSiteRadius_without_injection_norm_fails
#print axioms scalarDouble_rate_cannot_be_tightened
#print axioms affineBias_cannot_be_erased

end

end CompositionalJacobianBounds

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
