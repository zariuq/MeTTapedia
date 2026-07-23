import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.FrozenAdapterRestriction
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.DAGScheduleExactness
import Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry.InterferenceGram

/-!
# The missing condition in a frozen-adapter advantage claim

Four individually useful facts do not by themselves compare source-task
forgetting after predictive-coding and backpropagation updates: an exact
frozen restriction, an exact DAG schedule, zero pairwise interference, and
matched target progress still leave a reflection ambiguity around the target
optimum.  This file gives a concrete scalar quadratic countermodel.

The missing fifth condition is branch consistency: both endpoints must lie on
the same side of the target optimum.  For scalar quadratic loss, matched
target progress plus branch consistency forces the endpoints to coincide, so
their source forgetting is equal.  The result is deliberately conditional;
none of the structural hypotheses is presented as an unconditional empirical
advantage of one learning rule.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry

/-! ## The four hypotheses as existing, non-vacuous certificates -/

/-- The one-edge fixture has no repeated outgoing target at its source. -/
theorem dagTwoNode_outgoingTargetsInjectiveAt_source :
    OutgoingTargetsInjectiveAt dagTwoNodeGraph 0 := by
  intro e₁ e₂ _hs₁ _hs₂ _htarget
  fin_cases e₁
  fin_cases e₂
  rfl

/-- The one-edge fixture has a nonzero transport gain at its source. -/
theorem dagTwoNode_gain_ne_zero_at_source :
    ∀ e, dagTwoNodeGraph.source e = 0 → dagTwoNodeGraph.gain e ≠ 0 := by
  intro e _hsource
  fin_cases e
  norm_num [dagTwoNodeGraph]

/-- H2 fixture: structural schedule exactness is exactly edge-counting
admissibility on the one-edge shared-latent DAG. -/
theorem dagTwoNode_universalExactness_iff_admissible :
    dagScheduleUniversallyExactAtNode dagTwoNodeGraph
          (fun _ : Fin 1 => 0) 0 0 ↔
      dagScheduleAdmissible dagTwoNodeGraph (fun _ : Fin 1 => 0) 0 0 := by
  exact dagScheduleUniversallyExactAtNode_iff_admissible_of_targetInjective
    dagTwoNodeGraph (fun _ : Fin 1 => 0) 0 0
    dagTwoNode_outgoingTargetsInjectiveAt_source
    dagTwoNode_gain_ne_zero_at_source

/-- H3 fixture: two parallel nonzero rank-one task curvatures have zero
degree-two interference energy. -/
theorem parallelUnitTask_interferenceEnergy_zero :
    pairwiseInterferenceEnergy axisRankOneCurvature
        (directionRankOneCurvature 1 0) = 0 := by
  exact parallel_rankOne_interferenceEnergy_zero_positiveExample 1

/-! ## Scalar task losses and matched progress -/

/-- Unit-curvature scalar quadratic loss around `center`. -/
def scalarQuadraticLoss (center parameter : ℝ) : ℝ :=
  (parameter - center) ^ 2

/-- Improvement in target loss from `initial` to `updated`. -/
def targetLossProgress
    (targetCenter initial updated : ℝ) : ℝ :=
  scalarQuadraticLoss targetCenter initial -
    scalarQuadraticLoss targetCenter updated

/-- Increase in source loss from `initial` to `updated`. -/
def sourceForgetting
    (sourceCenter initial updated : ℝ) : ℝ :=
  scalarQuadraticLoss sourceCenter updated -
    scalarQuadraticLoss sourceCenter initial

/-- H4: the two endpoints achieve the same improvement on the target task. -/
def MatchedTargetProgress
    (targetCenter initial pcEndpoint bpEndpoint : ℝ) : Prop :=
  targetLossProgress targetCenter initial pcEndpoint =
    targetLossProgress targetCenter initial bpEndpoint

/-- The four proposed hypotheses, instantiated by existing non-vacuous H1--H3
certificates and parameterized only by the H4 update endpoints. -/
def FrozenAdapterFourHypotheses
    (initial pcEndpoint bpEndpoint : ℝ) : Prop :=
  IsFrozenAdapterSlowModeRate 100 3 (1 / 2) ∧
    (dagScheduleUniversallyExactAtNode dagTwoNodeGraph
          (fun _ : Fin 1 => 0) 0 0 ↔
      dagScheduleAdmissible dagTwoNodeGraph (fun _ : Fin 1 => 0) 0 0) ∧
    pairwiseInterferenceEnergy axisRankOneCurvature
        (directionRankOneCurvature 1 0) = 0 ∧
    MatchedTargetProgress 1 initial pcEndpoint bpEndpoint

/-! ## H1--H4 are insufficient -/

/-- Positive fixture: the PC and BP endpoints make equal target progress even
though they lie on opposite sides of the target optimum. -/
theorem reflectedEndpoints_matchedTargetProgress :
    MatchedTargetProgress 1 0 (3 / 2) (1 / 2) := by
  norm_num [MatchedTargetProgress, targetLossProgress, scalarQuadraticLoss]

/-- The reflected endpoints satisfy all four hypotheses. -/
theorem reflectedEndpoints_satisfy_fourHypotheses :
    FrozenAdapterFourHypotheses 0 (3 / 2) (1 / 2) := by
  exact ⟨depthHundred_backbone_depthThree_adapter_frozen_rate,
    dagTwoNode_universalExactness_iff_admissible,
    parallelUnitTask_interferenceEnergy_zero,
    reflectedEndpoints_matchedTargetProgress⟩

/-- Negative fixture: despite matched target progress, the reflected PC
endpoint forgets the source task strictly more than the BP endpoint. -/
theorem reflectedEndpoints_pc_forgetting_gt_bp :
    sourceForgetting 0 0 (1 / 2) < sourceForgetting 0 0 (3 / 2) := by
  norm_num [sourceForgetting, scalarQuadraticLoss]

/-- Countermodel crown: H1--H4 do not imply that PC source forgetting is at
most BP source forgetting. -/
theorem frozenAdapter_four_hypotheses_insufficient :
    ∃ initial pcEndpoint bpEndpoint : ℝ,
      FrozenAdapterFourHypotheses initial pcEndpoint bpEndpoint ∧
        ¬ sourceForgetting 0 initial pcEndpoint ≤
          sourceForgetting 0 initial bpEndpoint := by
  refine ⟨0, 3 / 2, 1 / 2, reflectedEndpoints_satisfy_fourHypotheses, ?_⟩
  exact not_le_of_gt reflectedEndpoints_pc_forgetting_gt_bp

/-! ## H5: remove the reflection ambiguity -/

/-- H5 says that the endpoints' residuals have the same sign, so both
endpoints lie on the same side of the target optimum (or at the optimum). -/
def SameTargetResidualBranch
    (targetCenter pcEndpoint bpEndpoint : ℝ) : Prop :=
  0 ≤ (pcEndpoint - targetCenter) * (bpEndpoint - targetCenter)

/-- The countermodel genuinely violates H5. -/
theorem reflectedEndpoints_not_sameTargetResidualBranch :
    ¬ SameTargetResidualBranch 1 (3 / 2) (1 / 2) := by
  norm_num [SameTargetResidualBranch]

/-- For scalar quadratic target loss, matched progress and H5 remove the
reflection branch and force the two endpoints to be identical. -/
theorem matchedTargetProgress_sameBranch_endpoints_eq
    (targetCenter initial pcEndpoint bpEndpoint : ℝ)
    (hprogress : MatchedTargetProgress targetCenter initial
      pcEndpoint bpEndpoint)
    (hbranch : SameTargetResidualBranch targetCenter
      pcEndpoint bpEndpoint) :
    pcEndpoint = bpEndpoint := by
  unfold MatchedTargetProgress targetLossProgress scalarQuadraticLoss at hprogress
  unfold SameTargetResidualBranch at hbranch
  have hsquares :
      (pcEndpoint - targetCenter) ^ 2 =
        (bpEndpoint - targetCenter) ^ 2 := by
    linarith
  have hfactor :
      ((pcEndpoint - targetCenter) - (bpEndpoint - targetCenter)) *
        ((pcEndpoint - targetCenter) + (bpEndpoint - targetCenter)) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hsame | hopposite
  · linarith
  · have hpcZero : pcEndpoint - targetCenter = 0 := by
      nlinarith [sq_nonneg (pcEndpoint - targetCenter)]
    linarith

/-- Conditional advantage crown: under H5, matched scalar target progress
makes the two endpoints, and hence their source forgetting, equal.  In
particular PC forgetting is no larger. -/
theorem sameTargetResidualBranch_restores_sourceForgetting_bound
    (sourceCenter targetCenter initial pcEndpoint bpEndpoint : ℝ)
    (hprogress : MatchedTargetProgress targetCenter initial
      pcEndpoint bpEndpoint)
    (hbranch : SameTargetResidualBranch targetCenter
      pcEndpoint bpEndpoint) :
    sourceForgetting sourceCenter initial pcEndpoint ≤
      sourceForgetting sourceCenter initial bpEndpoint := by
  rw [matchedTargetProgress_sameBranch_endpoints_eq targetCenter initial
    pcEndpoint bpEndpoint hprogress hbranch]

/-- H1--H5 crown in the original frozen-adapter vocabulary.  The first three
structural certificates remain true and non-vacuous; H4 and H5 are the facts
that determine the scalar comparison. -/
theorem frozenAdapter_five_hypotheses_restore_sourceForgetting_bound
    (initial pcEndpoint bpEndpoint : ℝ)
    (hfour : FrozenAdapterFourHypotheses initial pcEndpoint bpEndpoint)
    (hfifth : SameTargetResidualBranch 1 pcEndpoint bpEndpoint) :
    sourceForgetting 0 initial pcEndpoint ≤
      sourceForgetting 0 initial bpEndpoint := by
  exact sameTargetResidualBranch_restores_sourceForgetting_bound
    0 1 initial pcEndpoint bpEndpoint hfour.2.2.2 hfifth

#print axioms frozenAdapter_four_hypotheses_insufficient
#print axioms frozenAdapter_five_hypotheses_restore_sourceForgetting_bound

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
