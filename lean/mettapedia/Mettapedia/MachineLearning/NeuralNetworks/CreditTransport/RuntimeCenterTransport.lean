import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CompositionalJacobianBounds

/-!
# Transport from audited runtime centers

The compositional readout theorem uses centers obtained by exact evaluation of
the declared real-valued recurrence.  A center decoded from a finite-precision
runtime need not be definitionally equal to that ideal center.  This file keeps
the distinction explicit: a certified center mismatch is added to the
transported radius, and the complete three-site budget is recovered on the
enlarged audited balls.

No floating-point error model is assumed here.  IEEE-754 analysis or another
trusted source may supply the two mismatch bounds later.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RuntimeCenterTransport

noncomputable section

open CompositionalJacobianBounds

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A regional Jacobian budget remains valid after restricting its domain. -/
def restrictRegionalJacobianBudgetDomain
    {map : X → Y} {jacobian : X → X →L[ℝ] Y}
    {domain : X → Prop} {rate operatorBound variation : ℝ}
    (budget : RegionalJacobianBudget map jacobian domain
      rate operatorBound variation)
    (subdomain : X → Prop)
    (subset : ∀ state, subdomain state → domain state) :
    RegionalJacobianBudget map jacobian subdomain
      rate operatorBound variation where
  rate_nonneg := budget.rate_nonneg
  operatorBound_nonneg := budget.operatorBound_nonneg
  variation_nonneg := budget.variation_nonneg
  hasFDerivAt_on_domain state hstate :=
    budget.hasFDerivAt_on_domain state (subset state hstate)
  map_pair_bound left right hleft hright :=
    budget.map_pair_bound left right
      (subset left hleft) (subset right hright)
  jacobian_norm_bound state hstate :=
    budget.jacobian_norm_bound state (subset state hstate)
  jacobian_pair_bound left right hleft hright :=
    budget.jacobian_pair_bound left right
      (subset left hleft) (subset right hright)

/-- Radius around an audited first-site center.  The exact transported radius
and the center mismatch are independent error sources and therefore add. -/
def auditedFirstSiteRadius
    (injectOne : X →L[ℝ] Y) (errorRadius centerMismatch : ℝ) : ℝ :=
  firstSiteRadius injectOne errorRadius + centerMismatch

/-- Radius around an audited second-site center. -/
def auditedSecondSiteRadius
    (transitionRate : ℝ) (injectOne injectTwo : X →L[ℝ] Y)
    (errorRadius centerMismatch : ℝ) : ℝ :=
  secondSiteRadius transitionRate injectOne injectTwo errorRadius +
    centerMismatch

/-- The exact first-site ball is contained in the enlarged ball around any
audited center whose mismatch is certified. -/
theorem exactFirstSiteBall_subset_auditedFirstSiteBall
    (base : Y) (injectOne : X →L[ℝ] Y) (errorCenter : X)
    (errorRadius : ℝ) (auditedCenter : Y) (centerMismatch : ℝ)
    (hcenter : ‖auditedCenter - firstSiteCenter base injectOne errorCenter‖ ≤
      centerMismatch) :
    ∀ state,
      ‖state - firstSiteCenter base injectOne errorCenter‖ ≤
          firstSiteRadius injectOne errorRadius →
      ‖state - auditedCenter‖ ≤
          auditedFirstSiteRadius injectOne errorRadius centerMismatch := by
  intro state hstate
  have hcenterReverse :
      ‖firstSiteCenter base injectOne errorCenter - auditedCenter‖ ≤
        centerMismatch := by
    rw [show firstSiteCenter base injectOne errorCenter - auditedCenter =
      -(auditedCenter - firstSiteCenter base injectOne errorCenter) by abel,
      norm_neg]
    exact hcenter
  rw [show state - auditedCenter =
    (state - firstSiteCenter base injectOne errorCenter) +
      (firstSiteCenter base injectOne errorCenter - auditedCenter) by abel]
  calc
    ‖(state - firstSiteCenter base injectOne errorCenter) +
        (firstSiteCenter base injectOne errorCenter - auditedCenter)‖ ≤
      ‖state - firstSiteCenter base injectOne errorCenter‖ +
        ‖firstSiteCenter base injectOne errorCenter - auditedCenter‖ :=
      norm_add_le _ _
    _ ≤ firstSiteRadius injectOne errorRadius + centerMismatch :=
      add_le_add hstate hcenterReverse
    _ = auditedFirstSiteRadius injectOne errorRadius centerMismatch := rfl

/-- A runtime-audited first center receives the exact error-ball transport plus
its independently certified center mismatch. -/
theorem firstSiteState_mem_auditedBall
    (base : Y) (injectOne : X →L[ℝ] Y)
    (errorCenter error : X) (errorRadius : ℝ)
    (auditedCenter : Y) (centerMismatch : ℝ)
    (hcenter : ‖auditedCenter - firstSiteCenter base injectOne errorCenter‖ ≤
      centerMismatch)
    (herror : ‖error - errorCenter‖ ≤ errorRadius) :
    ‖firstSiteState base injectOne error - auditedCenter‖ ≤
      auditedFirstSiteRadius injectOne errorRadius centerMismatch := by
  exact exactFirstSiteBall_subset_auditedFirstSiteBall
    base injectOne errorCenter errorRadius auditedCenter centerMismatch hcenter
    _ (firstSiteState_mem_centeredBall base injectOne
      errorCenter error errorRadius herror)

/-- The second exact transported ball can likewise be recentered around an
audited finite-precision value, provided both center mismatches are bounded. -/
theorem secondSiteState_mem_auditedBall
    (base : Y) (injectOne injectTwo : X →L[ℝ] Y)
    (transitionTwo : Y → Y) (transitionTwoJacobian : Y → Y →L[ℝ] Y)
    (errorCenter error : X) (errorRadius transitionRate
      transitionOperator transitionVariation : ℝ)
    (auditedFirst auditedSecond : Y)
    (firstCenterMismatch secondCenterMismatch : ℝ)
    (herrorRadius : 0 ≤ errorRadius)
    (hfirstCenter :
      ‖auditedFirst - firstSiteCenter base injectOne errorCenter‖ ≤
        firstCenterMismatch)
    (hsecondCenter :
      ‖auditedSecond - secondSiteCenter base injectOne injectTwo
        transitionTwo errorCenter‖ ≤ secondCenterMismatch)
    (budgetTwo : RegionalJacobianBudget transitionTwo transitionTwoJacobian
      (fun state => ‖state - auditedFirst‖ ≤
        auditedFirstSiteRadius injectOne errorRadius firstCenterMismatch)
      transitionRate transitionOperator transitionVariation)
    (herror : ‖error - errorCenter‖ ≤ errorRadius) :
    ‖nextSiteState transitionTwo (firstSiteState base injectOne) injectTwo error -
        auditedSecond‖ ≤
      auditedSecondSiteRadius transitionRate injectOne injectTwo
        errorRadius secondCenterMismatch := by
  let exactFirstDomain : Y → Prop := fun state =>
    ‖state - firstSiteCenter base injectOne errorCenter‖ ≤
      firstSiteRadius injectOne errorRadius
  let exactBudget : RegionalJacobianBudget transitionTwo transitionTwoJacobian
      exactFirstDomain transitionRate transitionOperator transitionVariation :=
    restrictRegionalJacobianBudgetDomain budgetTwo exactFirstDomain
      (exactFirstSiteBall_subset_auditedFirstSiteBall
        base injectOne errorCenter errorRadius auditedFirst
        firstCenterMismatch hfirstCenter)
  have hexact := secondSiteState_mem_centeredBall
    base injectOne injectTwo transitionTwo transitionTwoJacobian
    errorCenter error errorRadius transitionRate transitionOperator
    transitionVariation herrorRadius exactBudget herror
  have hcenterReverse :
      ‖secondSiteCenter base injectOne injectTwo transitionTwo errorCenter -
          auditedSecond‖ ≤ secondCenterMismatch := by
    rw [show secondSiteCenter base injectOne injectTwo transitionTwo errorCenter -
        auditedSecond =
      -(auditedSecond - secondSiteCenter base injectOne injectTwo
        transitionTwo errorCenter) by abel,
      norm_neg]
    exact hsecondCenter
  rw [show nextSiteState transitionTwo (firstSiteState base injectOne) injectTwo
        error - auditedSecond =
      (nextSiteState transitionTwo (firstSiteState base injectOne) injectTwo
          error -
        secondSiteCenter base injectOne injectTwo transitionTwo errorCenter) +
      (secondSiteCenter base injectOne injectTwo transitionTwo errorCenter -
        auditedSecond) by abel]
  calc
    ‖(nextSiteState transitionTwo (firstSiteState base injectOne) injectTwo
          error -
        secondSiteCenter base injectOne injectTwo transitionTwo errorCenter) +
      (secondSiteCenter base injectOne injectTwo transitionTwo errorCenter -
        auditedSecond)‖ ≤
      ‖nextSiteState transitionTwo (firstSiteState base injectOne) injectTwo
          error -
        secondSiteCenter base injectOne injectTwo transitionTwo errorCenter‖ +
      ‖secondSiteCenter base injectOne injectTwo transitionTwo errorCenter -
        auditedSecond‖ := norm_add_le _ _
    _ ≤ secondSiteRadius transitionRate injectOne injectTwo errorRadius +
        secondCenterMismatch := add_le_add hexact hcenterReverse
    _ = auditedSecondSiteRadius transitionRate injectOne injectTwo
        errorRadius secondCenterMismatch := rfl

/-- Complete three-site source budget on runtime-audited intermediate balls.
The analytic `R/J/H` recurrence is unchanged; finite-precision center mismatch
only enlarges the regional domains that each transition must certify. -/
def threeSiteResidualAuditedBallBudget
    (base : Y) (injectOne injectTwo injectThree : X →L[ℝ] Y)
    (transitionTwo transitionThree : Y → Y)
    (transitionTwoJacobian transitionThreeJacobian : Y → Y →L[ℝ] Y)
    (readout : Y →L[ℝ] Z)
    (errorCenter : X) (errorRadius : ℝ) (herrorRadius : 0 ≤ errorRadius)
    (auditedFirst auditedSecond : Y)
    (firstCenterMismatch secondCenterMismatch : ℝ)
    (hfirstCenter :
      ‖auditedFirst - firstSiteCenter base injectOne errorCenter‖ ≤
        firstCenterMismatch)
    (hsecondCenter :
      ‖auditedSecond - secondSiteCenter base injectOne injectTwo
        transitionTwo errorCenter‖ ≤ secondCenterMismatch)
    {rateTwo operatorTwo variationTwo
      rateThree operatorThree variationThree : ℝ}
    (budgetTwo : RegionalJacobianBudget transitionTwo transitionTwoJacobian
      (fun state => ‖state - auditedFirst‖ ≤
        auditedFirstSiteRadius injectOne errorRadius firstCenterMismatch)
      rateTwo operatorTwo variationTwo)
    (budgetThree : RegionalJacobianBudget transitionThree transitionThreeJacobian
      (fun state => ‖state - auditedSecond‖ ≤
        auditedSecondSiteRadius rateTwo injectOne injectTwo errorRadius
          secondCenterMismatch)
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
      firstSiteState_mem_auditedBall base injectOne errorCenter error
        errorRadius auditedFirst firstCenterMismatch hfirstCenter herror)
    (fun error herror =>
      secondSiteState_mem_auditedBall base injectOne injectTwo transitionTwo
        transitionTwoJacobian errorCenter error errorRadius rateTwo operatorTwo
        variationTwo auditedFirst auditedSecond firstCenterMismatch
        secondCenterMismatch herrorRadius hfirstCenter hsecondCenter budgetTwo
        herror)

/-! ## Positive and negative fixtures -/

/-- A unit center mismatch is admitted exactly when the transported radius is
zero and the audited center is one unit from the ideal center. -/
theorem unit_audited_center_mismatch_is_admitted :
    ‖firstSiteState (0 : ℝ) (0 : ℝ →L[ℝ] ℝ) 0 - 1‖ ≤
      auditedFirstSiteRadius (0 : ℝ →L[ℝ] ℝ) 0 1 := by
  norm_num [firstSiteState, auditedFirstSiteRadius, firstSiteRadius]

/-- Dropping the audited-center mismatch is unsound even when the exact
transported radius is zero. -/
theorem audited_center_mismatch_cannot_be_dropped :
    ¬ ‖firstSiteState (0 : ℝ) (0 : ℝ →L[ℝ] ℝ) 0 - 1‖ ≤
      firstSiteRadius (0 : ℝ →L[ℝ] ℝ) 0 := by
  norm_num [firstSiteState, firstSiteRadius]

#print axioms threeSiteResidualAuditedBallBudget
#print axioms audited_center_mismatch_cannot_be_dropped

end

end RuntimeCenterTransport

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
