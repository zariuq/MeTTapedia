import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointGeometry
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ReplayGeometryBridge
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplayChunkedGeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite2Invocation0GeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplayReadoutInvocation0GeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedThreeHiddenStageResidualReplayInvocation0GeneratedFixture

/-!
# Authenticated checkpoint geometry for the registered three-site adapter

This module binds the exact binary32 tensors from one authenticated
generation-9 checkpoint invocation to the reusable regional geometry.  The
first hidden layer is rectangular (`256 → 64`), the next two hidden layers are
`64 → 64`, and the final affine readout is `64 → 256`.

The generated replay modules and their external hash chain own checkpoint and
invocation provenance.  The declarations below reuse the same embedded words;
the Lean kernel therefore checks the exact row-major affine maps and their
finite operator-norm bounds.  No center, radius, uniform floating-point
roundoff bound, frozen-parent task geometry, or efficacy claim is inferred.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32AuthenticatedCheckpointGeometry

noncomputable section

open Float32CheckpointGeometry
open Float32CheckpointGeometry.Float32AffineLayer
open Float32HiddenStageReplayCertificate
open Float32ThreeHiddenStageReplayCertificate
open Float32ReplayGeometryBridge
open CompositionalJacobianBounds
open SiLUTransitionBounds

/-- Exact first hidden affine layer (`256 → 64`). -/
def firstHiddenLayer : Float32AffineLayer 64 256 where
  weight :=
    GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0.weight
  bias :=
    GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0.bias

/-- Exact second hidden affine layer (`64 → 64`). -/
def secondHiddenLayer : Float32AffineLayer 64 64 where
  weight := GeneratedAuthenticatedAffineReplayChunkedFixture.replay0.weight
  bias := GeneratedAuthenticatedAffineReplayChunkedFixture.replay0.bias

/-- Exact third hidden affine layer (`64 → 64`). -/
def thirdHiddenLayer : Float32AffineLayer 64 64 where
  weight :=
    GeneratedAuthenticatedAffineReplaySite2Invocation0Fixture.replay0.weight
  bias :=
    GeneratedAuthenticatedAffineReplaySite2Invocation0Fixture.replay0.bias

/-- Exact final affine readout (`64 → 256`). -/
def finalReadoutLayer : Float32AffineLayer 256 64 where
  weight :=
    GeneratedAuthenticatedAffineReplayReadoutInvocation0Fixture.replay0.weight
  bias :=
    GeneratedAuthenticatedAffineReplayReadoutInvocation0Fixture.replay0.bias

theorem firstHidden_operatorNorm_le :
    ‖firstHiddenLayer.linear‖ ≤ firstHiddenLayer.weightBound :=
  firstHiddenLayer.linear_norm_le_weightBound

theorem secondHidden_operatorNorm_le :
    ‖secondHiddenLayer.linear‖ ≤ secondHiddenLayer.weightBound :=
  secondHiddenLayer.linear_norm_le_weightBound

theorem thirdHidden_operatorNorm_le :
    ‖thirdHiddenLayer.linear‖ ≤ thirdHiddenLayer.weightBound :=
  thirdHiddenLayer.linear_norm_le_weightBound

theorem finalReadout_operatorNorm_le :
    ‖finalReadoutLayer.linear‖ ≤ finalReadoutLayer.weightBound :=
  finalReadoutLayer.linear_norm_le_weightBound

theorem finalReadout_biasNorm_le :
    ‖finalReadoutLayer.biasVector‖ ≤ finalReadoutLayer.biasBound :=
  finalReadoutLayer.biasVector_norm_le_biasBound

/-! ## Authenticated invocation-local center bounds -/

/-- The complete word-connected hidden replay for authenticated invocation
zero.  This alias keeps the compact bounds below independent of generated
namespace length. -/
def invocation0HiddenReplay : Float32ThreeHiddenStageReplay 64 256 :=
  GeneratedAuthenticatedThreeHiddenStageResidualReplayInvocation0Fixture.hiddenReplay0

theorem invocation0HiddenReplay_is_accepted :
    invocation0HiddenReplay.check = true :=
  GeneratedAuthenticatedThreeHiddenStageResidualReplayInvocation0Fixture.hiddenReplay0_is_accepted

/-- Exact finite bound for the first ideal hidden center, computed from the
observed binary32 center and its checked local replay error. -/
noncomputable def invocation0FirstCenterBound : ℝ :=
  invocation0HiddenReplay.first.decodedOutputL1 +
    (invocation0HiddenReplay.first.totalCertifiedErrorRat : ℝ)

/-- Exact finite bound for the second ideal hidden center when evaluated at
the observed first-stage input.  Propagating the first-stage mismatch to the
fully exact two-stage center is a separate compositional obligation. -/
noncomputable def invocation0SecondLocalCenterBound : ℝ :=
  invocation0HiddenReplay.second.decodedOutputL1 +
    (invocation0HiddenReplay.second.totalCertifiedErrorRat : ℝ)

/-- Exact finite bound for the third ideal hidden center when evaluated at
the observed second-stage input. -/
noncomputable def invocation0ThirdLocalCenterBound : ℝ :=
  invocation0HiddenReplay.third.decodedOutputL1 +
    (invocation0HiddenReplay.third.totalCertifiedErrorRat : ℝ)

private theorem invocation0_first_check :
    invocation0HiddenReplay.first.check = true := by
  have hvalid :=
    (Float32ThreeHiddenStageReplay.check_eq_true_iff
      invocation0HiddenReplay).mp invocation0HiddenReplay_is_accepted
  exact
    (Float32HiddenStageReplay.check_eq_true_iff
      invocation0HiddenReplay.first).mpr hvalid.1

private theorem invocation0_second_check :
    invocation0HiddenReplay.second.check = true := by
  have hvalid :=
    (Float32ThreeHiddenStageReplay.check_eq_true_iff
      invocation0HiddenReplay).mp invocation0HiddenReplay_is_accepted
  exact
    (Float32HiddenStageReplay.check_eq_true_iff
      invocation0HiddenReplay.second).mpr hvalid.2.1

private theorem invocation0_third_check :
    invocation0HiddenReplay.third.check = true := by
  have hvalid :=
    (Float32ThreeHiddenStageReplay.check_eq_true_iff
      invocation0HiddenReplay).mp invocation0HiddenReplay_is_accepted
  exact
    (Float32HiddenStageReplay.check_eq_true_iff
      invocation0HiddenReplay.third).mpr hvalid.2.2.1

theorem invocation0FirstCenterBound_nonneg :
    0 ≤ invocation0FirstCenterBound := by
  exact add_nonneg invocation0HiddenReplay.first.decodedOutputL1_nonneg
    (invocation0HiddenReplay.first.toLocalEvaluationErrorCertificate
      invocation0_first_check).localError_nonneg

theorem invocation0SecondLocalCenterBound_nonneg :
    0 ≤ invocation0SecondLocalCenterBound := by
  exact add_nonneg invocation0HiddenReplay.second.decodedOutputL1_nonneg
    (invocation0HiddenReplay.second.toLocalEvaluationErrorCertificate
      invocation0_second_check).localError_nonneg

theorem invocation0ThirdLocalCenterBound_nonneg :
    0 ≤ invocation0ThirdLocalCenterBound := by
  exact add_nonneg invocation0HiddenReplay.third.decodedOutputL1_nonneg
    (invocation0HiddenReplay.third.toLocalEvaluationErrorCertificate
      invocation0_third_check).localError_nonneg

theorem invocation0_first_ideal_center_norm_le :
    ‖invocation0HiddenReplay.first.idealBlock
        invocation0HiddenReplay.first.decodedInput‖ ≤
      invocation0FirstCenterBound := by
  exact invocation0HiddenReplay.first.idealBlock_norm_le_observedL1_add_error
    invocation0_first_check

theorem invocation0_second_local_ideal_center_norm_le :
    ‖invocation0HiddenReplay.second.idealBlock
        invocation0HiddenReplay.second.decodedInput‖ ≤
      invocation0SecondLocalCenterBound := by
  exact invocation0HiddenReplay.second.idealBlock_norm_le_observedL1_add_error
    invocation0_second_check

theorem invocation0_third_local_ideal_center_norm_le :
    ‖invocation0HiddenReplay.third.idealBlock
        invocation0HiddenReplay.third.decodedInput‖ ≤
      invocation0ThirdLocalCenterBound := by
  exact invocation0HiddenReplay.third.idealBlock_norm_le_observedL1_add_error
    invocation0_third_check

/-- Complete geometry-derived mismatch radius for the authenticated
three-hidden-stage invocation when its exact and recorded initial inputs
coincide. -/
noncomputable def invocation0FullGeometryMismatchRadius : ℝ :=
  invocation0HiddenReplay.totalCertifiedError
    (threeStageFirstRate invocation0HiddenReplay 0)
    (threeStageSecondRate invocation0HiddenReplay 0)
    (threeStageThirdRate invocation0HiddenReplay 0)
    0

/-- Compact exact bound for the fully composed third hidden center, including
transport of all preceding binary32 replay errors. -/
noncomputable def invocation0ThirdExactCenterBound : ℝ :=
  invocation0HiddenReplay.third.decodedOutputL1 +
    invocation0FullGeometryMismatchRadius

theorem invocation0_full_geometry_mismatch_le :
    ‖invocation0HiddenReplay.third.decodedOutput -
      invocation0HiddenReplay.third.idealBlockAtRecordedError
        (invocation0HiddenReplay.second.idealBlockAtRecordedError
          (invocation0HiddenReplay.first.idealBlockAtRecordedError
            invocation0HiddenReplay.first.runtimePreviousCenter))‖ ≤
      invocation0FullGeometryMismatchRadius := by
  exact threeStageOutputMismatch_le_from_geometry
    invocation0HiddenReplay invocation0HiddenReplay_is_accepted
    invocation0HiddenReplay.first.runtimePreviousCenter 0
    (by norm_num) (by simp)

theorem invocation0_third_exact_center_norm_le :
    ‖invocation0HiddenReplay.third.idealBlockAtRecordedError
        (invocation0HiddenReplay.second.idealBlockAtRecordedError
          (invocation0HiddenReplay.first.idealBlockAtRecordedError
            invocation0HiddenReplay.first.runtimePreviousCenter))‖ ≤
      invocation0ThirdExactCenterBound := by
  exact threeStageExactCenter_norm_le_from_geometry
    invocation0HiddenReplay invocation0HiddenReplay_is_accepted
    invocation0HiddenReplay.first.runtimePreviousCenter 0
    (by norm_num) (by simp)

variable {Node : Type*} [Fintype Node] [DecidableEq Node]

/-- The exact first hidden checkpoint layer, shared independently over graph
nodes, retains its finite whole-state operator bound. -/
theorem sharedFirstHidden_operatorNorm_le :
    ‖firstHiddenLayer.sharedLinear (Node := Node)‖ ≤
      firstHiddenLayer.sharedWeightBound :=
  firstHiddenLayer.sharedLinear_norm_le_weightBound (Node := Node)

/-- The final checkpoint readout is likewise shared without introducing
cross-node coupling. -/
theorem sharedFinalReadout_operatorNorm_le :
    ‖finalReadoutLayer.sharedLinear (Node := Node)‖ ≤
      finalReadoutLayer.sharedWeightBound :=
  finalReadoutLayer.sharedLinear_norm_le_weightBound (Node := Node)

/-! ## Exact source-shaped masks and error-site injections -/

/-- Whole-graph parent features before the first adapter layer. -/
abbrev ParentFeatureState (Node : Type*) [Fintype Node] :=
  HiddenState (Node × Fin 256)

/-- Whole-graph hidden features at every error site. -/
abbrev HiddenFeatureState (Node : Type*) [Fintype Node] :=
  HiddenState (Node × Fin 64)

/-- The three raw error tensors with their source site order retained. -/
abbrev ThreeSiteErrorState (Node : Type*) [Fintype Node] :=
  PiLp 2 (fun _ : Fin 3 => HiddenFeatureState Node)

/-- Lift node validity uniformly over the hidden feature axis. -/
def hiddenNodeMask (nodeValid : Node → Prop) (index : Node × Fin 64) : Prop :=
  nodeValid index.1

/-- Lift the same node validity over the parent/readout feature axis. -/
def parentNodeMask (nodeValid : Node → Prop) (index : Node × Fin 256) : Prop :=
  nodeValid index.1

instance hiddenNodeMaskDecidable
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    DecidablePred (hiddenNodeMask nodeValid) :=
  fun index => inferInstanceAs (Decidable (nodeValid index.1))

instance parentNodeMaskDecidable
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    DecidablePred (parentNodeMask nodeValid) :=
  fun index => inferInstanceAs (Decidable (nodeValid index.1))

/-- Projection from the source-ordered three-site error bundle to one site. -/
noncomputable def siteProjection (site : Fin 3) :
    ThreeSiteErrorState Node →L[ℝ] HiddenFeatureState Node :=
  PiLp.proj 2 (fun _ : Fin 3 => HiddenFeatureState Node) site

omit [DecidableEq Node] in
theorem siteProjection_norm_le_one (site : Fin 3) :
    ‖siteProjection (Node := Node) site‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro error
  change ‖error site‖ ≤ 1 * ‖error‖
  simpa using PiLp.norm_apply_le error site

/-- The source adds an error only after applying the node mask. -/
noncomputable def siteInjection
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (site : Fin 3) :
    ThreeSiteErrorState Node →L[ℝ] HiddenFeatureState Node :=
  maskProjection (hiddenNodeMask nodeValid) ∘L
    siteProjection (Node := Node) site

omit [DecidableEq Node] in
theorem siteInjection_norm_le_one
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (site : Fin 3) :
    ‖siteInjection (Node := Node) nodeValid site‖ ≤ 1 := by
  calc
    ‖siteInjection (Node := Node) nodeValid site‖ ≤
        ‖maskProjection (hiddenNodeMask nodeValid)‖ *
          ‖siteProjection (Node := Node) site‖ :=
      (maskProjection (hiddenNodeMask nodeValid)).opNorm_comp_le
        (siteProjection (Node := Node) site)
    _ ≤ 1 * 1 := by
      exact mul_le_mul
        (maskProjection_norm_le_one (hiddenNodeMask nodeValid))
        (siteProjection_norm_le_one (Node := Node) site)
        (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- First hidden prediction from the frozen parent representation. -/
noncomputable def firstHiddenBase
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (memory : ParentFeatureState Node) : HiddenFeatureState Node :=
  rectangularMaskedAffineSiLU (hiddenNodeMask nodeValid)
    (firstHiddenLayer.sharedLinear (Node := Node))
    (firstHiddenLayer.sharedBiasVector (Node := Node)) memory

/-- Exact second hidden transition of the registered adapter. -/
noncomputable def secondHiddenTransition
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    HiddenFeatureState Node → HiddenFeatureState Node :=
  rectangularMaskedAffineSiLU (hiddenNodeMask nodeValid)
    (secondHiddenLayer.sharedLinear (Node := Node))
    (secondHiddenLayer.sharedBiasVector (Node := Node))

/-- Exact symbolic Jacobian of the second hidden transition. -/
noncomputable def secondHiddenTransitionJacobian
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    HiddenFeatureState Node →
      (HiddenFeatureState Node →L[ℝ] HiddenFeatureState Node) :=
  rectangularMaskedAffineSiLUJacobian (hiddenNodeMask nodeValid)
    (secondHiddenLayer.sharedLinear (Node := Node))
    (secondHiddenLayer.sharedBiasVector (Node := Node))

/-- Exact third hidden transition of the registered adapter. -/
noncomputable def thirdHiddenTransition
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    HiddenFeatureState Node → HiddenFeatureState Node :=
  rectangularMaskedAffineSiLU (hiddenNodeMask nodeValid)
    (thirdHiddenLayer.sharedLinear (Node := Node))
    (thirdHiddenLayer.sharedBiasVector (Node := Node))

/-- Exact symbolic Jacobian of the third hidden transition. -/
noncomputable def thirdHiddenTransitionJacobian
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    HiddenFeatureState Node →
      (HiddenFeatureState Node →L[ℝ] HiddenFeatureState Node) :=
  rectangularMaskedAffineSiLUJacobian (hiddenNodeMask nodeValid)
    (thirdHiddenLayer.sharedLinear (Node := Node))
    (thirdHiddenLayer.sharedBiasVector (Node := Node))

/-- Final readout linear map after the source's output node mask. -/
noncomputable def maskedFinalReadoutLinear
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    HiddenFeatureState Node →L[ℝ] ParentFeatureState Node :=
  maskProjection (parentNodeMask nodeValid) ∘L
    finalReadoutLayer.sharedLinear (Node := Node)

/-- Final readout bias after the same source mask. -/
noncomputable def maskedFinalReadoutBias
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    ParentFeatureState Node :=
  maskProjection (parentNodeMask nodeValid)
    (finalReadoutLayer.sharedBiasVector (Node := Node))

/-- Masking the source affine readout is exactly the masked linear map plus
the masked bias. -/
theorem maskedFinalReadout_eq
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (hidden : HiddenFeatureState Node) :
    maskProjection (parentNodeMask nodeValid)
        (finalReadoutLayer.sharedLinear (Node := Node) hidden +
          finalReadoutLayer.sharedBiasVector (Node := Node)) =
      maskedFinalReadoutLinear (Node := Node) nodeValid hidden +
        maskedFinalReadoutBias (Node := Node) nodeValid := by
  simp [maskedFinalReadoutLinear, maskedFinalReadoutBias]

theorem maskedFinalReadout_operatorNorm_le
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    ‖maskedFinalReadoutLinear (Node := Node) nodeValid‖ ≤
      finalReadoutLayer.sharedWeightBound := by
  calc
    ‖maskedFinalReadoutLinear (Node := Node) nodeValid‖ ≤
        ‖maskProjection (parentNodeMask nodeValid)‖ *
          ‖finalReadoutLayer.sharedLinear (Node := Node)‖ :=
      (maskProjection (parentNodeMask nodeValid)).opNorm_comp_le
        (finalReadoutLayer.sharedLinear (Node := Node))
    _ ≤ 1 * finalReadoutLayer.sharedWeightBound := by
      exact mul_le_mul
        (maskProjection_norm_le_one (parentNodeMask nodeValid))
        (finalReadoutLayer.sharedLinear_norm_le_weightBound (Node := Node))
        (norm_nonneg _) (by norm_num)
    _ = finalReadoutLayer.sharedWeightBound := by ring

theorem maskedFinalReadout_invalid_zero
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (hidden : HiddenFeatureState Node)
    (node : Node) (feature : Fin 256)
    (hinvalid : ¬ nodeValid node) :
    (maskedFinalReadoutLinear (Node := Node) nodeValid hidden +
        maskedFinalReadoutBias (Node := Node) nodeValid) (node, feature) = 0 := by
  rw [← maskedFinalReadout_eq]
  simp [maskProjection_apply, parentNodeMask, hinvalid]

/-! ## Authenticated three-site regional geometry -/

noncomputable def firstErrorInjection
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    ThreeSiteErrorState Node →L[ℝ] HiddenFeatureState Node :=
  siteInjection (Node := Node) nodeValid 0

noncomputable def secondErrorInjection
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    ThreeSiteErrorState Node →L[ℝ] HiddenFeatureState Node :=
  siteInjection (Node := Node) nodeValid 1

noncomputable def thirdErrorInjection
    (nodeValid : Node → Prop) [DecidablePred nodeValid] :
    ThreeSiteErrorState Node →L[ℝ] HiddenFeatureState Node :=
  siteInjection (Node := Node) nodeValid 2

noncomputable def adapterFirstCenter
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (memory : ParentFeatureState Node)
    (errorCenter : ThreeSiteErrorState Node) : HiddenFeatureState Node :=
  firstSiteCenter
    (firstHiddenBase (Node := Node) nodeValid memory)
    (firstErrorInjection (Node := Node) nodeValid) errorCenter

noncomputable def adapterFirstRadius
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (errorRadius : ℝ) : ℝ :=
  firstSiteRadius (firstErrorInjection (Node := Node) nodeValid) errorRadius

noncomputable def secondTransitionRateBound
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (firstCenterBound errorRadius : ℝ) : ℝ :=
  secondHiddenLayer.sharedTransitionBound (Node := Node) firstCenterBound
    (adapterFirstRadius (Node := Node) nodeValid errorRadius)

noncomputable def secondTransitionVariationBound
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (firstCenterBound errorRadius : ℝ) : ℝ :=
  secondHiddenLayer.sharedTransitionVariationBound (Node := Node)
    firstCenterBound
    (adapterFirstRadius (Node := Node) nodeValid errorRadius)

noncomputable def adapterSecondCenter
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (memory : ParentFeatureState Node)
    (errorCenter : ThreeSiteErrorState Node) : HiddenFeatureState Node :=
  secondSiteCenter
    (firstHiddenBase (Node := Node) nodeValid memory)
    (firstErrorInjection (Node := Node) nodeValid)
    (secondErrorInjection (Node := Node) nodeValid)
    (secondHiddenTransition (Node := Node) nodeValid) errorCenter

noncomputable def adapterSecondRadius
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (firstCenterBound errorRadius : ℝ) : ℝ :=
  secondSiteRadius
    (secondTransitionRateBound (Node := Node) nodeValid
      firstCenterBound errorRadius)
    (firstErrorInjection (Node := Node) nodeValid)
    (secondErrorInjection (Node := Node) nodeValid)
    errorRadius

noncomputable def thirdTransitionRateBound
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (firstCenterBound secondCenterBound errorRadius : ℝ) : ℝ :=
  thirdHiddenLayer.sharedTransitionBound (Node := Node) secondCenterBound
    (adapterSecondRadius (Node := Node) nodeValid
      firstCenterBound errorRadius)

noncomputable def thirdTransitionVariationBound
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (firstCenterBound secondCenterBound errorRadius : ℝ) : ℝ :=
  thirdHiddenLayer.sharedTransitionVariationBound (Node := Node)
    secondCenterBound
    (adapterSecondRadius (Node := Node) nodeValid
      firstCenterBound errorRadius)

/-- Exact source-shaped residual map of the authenticated adapter: fixed first
prediction, three masked error injections, two subsequent masked nonlinear
transitions, and the masked affine readout. -/
noncomputable def authenticatedAdapterResidual
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (memory : ParentFeatureState Node) :
    ThreeSiteErrorState Node → ParentFeatureState Node :=
  threeSiteAffineResidual
    (firstHiddenBase (Node := Node) nodeValid memory)
    (firstErrorInjection (Node := Node) nodeValid)
    (secondErrorInjection (Node := Node) nodeValid)
    (thirdErrorInjection (Node := Node) nodeValid)
    (secondHiddenTransition (Node := Node) nodeValid)
    (thirdHiddenTransition (Node := Node) nodeValid)
    (maskedFinalReadoutLinear (Node := Node) nodeValid)
    (maskedFinalReadoutBias (Node := Node) nodeValid)

/-- Symbolic error-coordinate Jacobian of the authenticated adapter. -/
noncomputable def authenticatedAdapterResidualJacobian
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (memory : ParentFeatureState Node) :
    ThreeSiteErrorState Node →
      (ThreeSiteErrorState Node →L[ℝ] ParentFeatureState Node) :=
  threeSiteAffineResidualJacobian
    (firstHiddenBase (Node := Node) nodeValid memory)
    (firstErrorInjection (Node := Node) nodeValid)
    (secondErrorInjection (Node := Node) nodeValid)
    (thirdErrorInjection (Node := Node) nodeValid)
    (secondHiddenTransition (Node := Node) nodeValid)
    (thirdHiddenTransition (Node := Node) nodeValid)
    (secondHiddenTransitionJacobian (Node := Node) nodeValid)
    (thirdHiddenTransitionJacobian (Node := Node) nodeValid)
    (maskedFinalReadoutLinear (Node := Node) nodeValid)
    (maskedFinalReadoutBias (Node := Node) nodeValid)

noncomputable def authenticatedAdapterRate
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (firstCenterBound secondCenterBound errorRadius : ℝ) : ℝ :=
  ‖maskedFinalReadoutLinear (Node := Node) nodeValid‖ *
    nextSiteRate
      (thirdTransitionRateBound (Node := Node) nodeValid
        firstCenterBound secondCenterBound errorRadius)
      (nextSiteRate
        (secondTransitionRateBound (Node := Node) nodeValid
          firstCenterBound errorRadius)
        ‖firstErrorInjection (Node := Node) nodeValid‖
        ‖secondErrorInjection (Node := Node) nodeValid‖)
      ‖thirdErrorInjection (Node := Node) nodeValid‖

noncomputable def authenticatedAdapterOperatorBound
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (firstCenterBound secondCenterBound errorRadius : ℝ) : ℝ :=
  ‖maskedFinalReadoutLinear (Node := Node) nodeValid‖ *
    nextSiteOperator
      (thirdTransitionRateBound (Node := Node) nodeValid
        firstCenterBound secondCenterBound errorRadius)
      (nextSiteOperator
        (secondTransitionRateBound (Node := Node) nodeValid
          firstCenterBound errorRadius)
        ‖firstErrorInjection (Node := Node) nodeValid‖
        ‖secondErrorInjection (Node := Node) nodeValid‖)
      ‖thirdErrorInjection (Node := Node) nodeValid‖

noncomputable def authenticatedAdapterVariationBound
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (firstCenterBound secondCenterBound errorRadius : ℝ) : ℝ :=
  ‖maskedFinalReadoutLinear (Node := Node) nodeValid‖ *
    nextSiteVariation
      (thirdTransitionVariationBound (Node := Node) nodeValid
        firstCenterBound secondCenterBound errorRadius)
      (nextSiteRate
        (secondTransitionRateBound (Node := Node) nodeValid
          firstCenterBound errorRadius)
        ‖firstErrorInjection (Node := Node) nodeValid‖
        ‖secondErrorInjection (Node := Node) nodeValid‖)
      (nextSiteOperator
        (secondTransitionRateBound (Node := Node) nodeValid
          firstCenterBound errorRadius)
        ‖firstErrorInjection (Node := Node) nodeValid‖
        ‖secondErrorInjection (Node := Node) nodeValid‖)
      (thirdTransitionRateBound (Node := Node) nodeValid
        firstCenterBound secondCenterBound errorRadius)
      (nextSiteVariation
        (secondTransitionVariationBound (Node := Node) nodeValid
          firstCenterBound errorRadius)
        ‖firstErrorInjection (Node := Node) nodeValid‖
        ‖firstErrorInjection (Node := Node) nodeValid‖
        (secondTransitionRateBound (Node := Node) nodeValid
          firstCenterBound errorRadius) 0)

/-- Exact checkpoint words and source masks compile to one regional
forward/Jacobian certificate once the two intermediate center norms and the
error ball radius are certified.  No tensor or operator bound is assumed. -/
noncomputable def authenticatedAdapterRegionalBudget
    (nodeValid : Node → Prop) [DecidablePred nodeValid]
    (memory : ParentFeatureState Node)
    (errorCenter : ThreeSiteErrorState Node)
    (errorRadius firstCenterBound secondCenterBound : ℝ)
    (herrorRadius : 0 ≤ errorRadius)
    (hfirstCenterBound : 0 ≤ firstCenterBound)
    (hfirstCenter :
      ‖adapterFirstCenter (Node := Node) nodeValid memory errorCenter‖ ≤
        firstCenterBound)
    (hsecondCenterBound : 0 ≤ secondCenterBound)
    (hsecondCenter :
      ‖adapterSecondCenter (Node := Node) nodeValid memory errorCenter‖ ≤
        secondCenterBound) :
    RegionalJacobianBudget
      (authenticatedAdapterResidual (Node := Node) nodeValid memory)
      (authenticatedAdapterResidualJacobian (Node := Node) nodeValid memory)
      (fun error => ‖error - errorCenter‖ ≤ errorRadius)
      (authenticatedAdapterRate (Node := Node) nodeValid
        firstCenterBound secondCenterBound errorRadius)
      (authenticatedAdapterOperatorBound (Node := Node) nodeValid
        firstCenterBound secondCenterBound errorRadius)
      (authenticatedAdapterVariationBound (Node := Node) nodeValid
        firstCenterBound secondCenterBound errorRadius) := by
  have hfirstRadius :
      0 ≤ adapterFirstRadius (Node := Node) nodeValid errorRadius := by
    exact mul_nonneg (norm_nonneg _) herrorRadius
  let budgetTwo :=
    secondHiddenLayer.sharedMaskedSiLUBudget
      (Node := Node) (hiddenNodeMask nodeValid)
      (adapterFirstCenter (Node := Node) nodeValid memory errorCenter)
      firstCenterBound
      (adapterFirstRadius (Node := Node) nodeValid errorRadius)
      hfirstCenterBound hfirstRadius hfirstCenter
  have hsecondRate :
      0 ≤ secondTransitionRateBound (Node := Node) nodeValid
        firstCenterBound errorRadius := by
    simpa only [secondTransitionRateBound] using budgetTwo.rate_nonneg
  have hsecondRadius :
      0 ≤ adapterSecondRadius (Node := Node) nodeValid
        firstCenterBound errorRadius := by
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg hsecondRate (norm_nonneg _))
        (norm_nonneg _))
      herrorRadius
  let budgetThree :=
    thirdHiddenLayer.sharedMaskedSiLUBudget
      (Node := Node) (hiddenNodeMask nodeValid)
      (adapterSecondCenter (Node := Node) nodeValid memory errorCenter)
      secondCenterBound
      (adapterSecondRadius (Node := Node) nodeValid
        firstCenterBound errorRadius)
      hsecondCenterBound hsecondRadius hsecondCenter
  simpa only [authenticatedAdapterResidual,
    authenticatedAdapterResidualJacobian, authenticatedAdapterRate,
    authenticatedAdapterOperatorBound, authenticatedAdapterVariationBound,
    secondTransitionRateBound, secondTransitionVariationBound,
    thirdTransitionRateBound, thirdTransitionVariationBound] using
    (threeSiteAffineResidualBallBudget
      (firstHiddenBase (Node := Node) nodeValid memory)
      (firstErrorInjection (Node := Node) nodeValid)
      (secondErrorInjection (Node := Node) nodeValid)
      (thirdErrorInjection (Node := Node) nodeValid)
      (secondHiddenTransition (Node := Node) nodeValid)
      (thirdHiddenTransition (Node := Node) nodeValid)
      (secondHiddenTransitionJacobian (Node := Node) nodeValid)
      (thirdHiddenTransitionJacobian (Node := Node) nodeValid)
      (maskedFinalReadoutLinear (Node := Node) nodeValid)
      (maskedFinalReadoutBias (Node := Node) nodeValid)
      errorCenter errorRadius herrorRadius budgetTwo budgetThree)

#print axioms firstHidden_operatorNorm_le
#print axioms secondHidden_operatorNorm_le
#print axioms thirdHidden_operatorNorm_le
#print axioms finalReadout_operatorNorm_le
#print axioms finalReadout_biasNorm_le
#print axioms invocation0HiddenReplay_is_accepted
#print axioms invocation0_first_ideal_center_norm_le
#print axioms invocation0_second_local_ideal_center_norm_le
#print axioms invocation0_third_local_ideal_center_norm_le
#print axioms invocation0_full_geometry_mismatch_le
#print axioms invocation0_third_exact_center_norm_le
#print axioms sharedFirstHidden_operatorNorm_le
#print axioms sharedFinalReadout_operatorNorm_le
#print axioms siteProjection_norm_le_one
#print axioms siteInjection_norm_le_one
#print axioms maskedFinalReadout_eq
#print axioms maskedFinalReadout_operatorNorm_le
#print axioms maskedFinalReadout_invalid_zero
#print axioms authenticatedAdapterRegionalBudget

end

end Float32AuthenticatedCheckpointGeometry

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
