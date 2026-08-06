import MeTTailCore.Crypto.SHA256
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.LinearSettling
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.TypedRegisters

/-!
# Preregistered workspace-decoder predictions

Prediction (a) is `finiteDepthMismatch_equilibrium`: in the exact linear
shift model, finite-depth fitting and equilibrium evaluation disagree, giving a
derived finite optimum.  It is not a claim about a trained nonlinear decoder.

Prediction (b) below uses a two-key equal-variance Gaussian read model.  Its
posterior log-odds are linear in a nonnegative residual magnitude.  Entropy is
therefore antitone in that magnitude and tends to uniform entropy when the
linear settling residual converges to zero.  Spectral stability alone does not
make the residual norm stepwise monotone, especially for nonnormal operators;
the observed per-step entropy trajectory remains the registered empirical
diagnostic outside the stated residual-order premise.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Filter Set Topology
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open MeTTailCore.Crypto.SHA256

universe uState

/-! ## Prediction (b): an honest linear-Gaussian entropy link -/

/-- Positive-key posterior mass for a binary, equal-prior, equal-variance
Gaussian read whose log-likelihood ratio is `scale * residual`.  This is a
specific linear-Gaussian diagnostic model, not arbitrary neural attention. -/
noncomputable def linearGaussianReadProbability (scale residual : ℝ) : ℝ :=
  Real.sigmoid (scale * residual)

/-- Binary read-distribution entropy in the specific linear-Gaussian model.
No entropy statement for arbitrary nonlinear attention is implied. -/
noncomputable def linearGaussianReadEntropy (scale residual : ℝ) : ℝ :=
  Real.binEntropy (linearGaussianReadProbability scale residual)

/-- In the linear-Gaussian diagnostic, positive scale and nonnegative residual
place the positive-key posterior between one half and one. -/
theorem linearGaussianReadProbability_mem_Icc
    (scale residual : ℝ) (hscale : 0 ≤ scale) (hresidual : 0 ≤ residual) :
    linearGaussianReadProbability scale residual ∈ Icc (2 : ℝ)⁻¹ 1 := by
  constructor
  · have hmono := Real.sigmoid_monotone (mul_nonneg hscale hresidual)
    simpa [linearGaussianReadProbability, Real.sigmoid_zero] using hmono
  · exact Real.sigmoid_le_one _

/-- Prediction (b), linear-Gaussian scope: read entropy is antitone in
nonnegative residual magnitude.  Thus a proved residual decrease entails an
entropy increase; no stepwise residual decrease is assumed by this theorem. -/
theorem linearGaussianReadEntropy_antitoneOn
    (scale : ℝ) (hscale : 0 ≤ scale) :
    AntitoneOn (linearGaussianReadEntropy scale) (Ici (0 : ℝ)) := by
  intro first hfirst second hsecond hle
  apply Real.binEntropy_strictAntiOn.antitoneOn
  · exact linearGaussianReadProbability_mem_Icc scale first hscale hfirst
  · exact linearGaussianReadProbability_mem_Icc scale second hscale hsecond
  · rw [linearGaussianReadProbability, linearGaussianReadProbability,
      Real.sigmoid_le_iff]
    exact mul_le_mul_of_nonneg_left hle hscale

/-- Linear-Gaussian scope: with positive scale, a strict residual increase
strictly lowers read entropy.  This exposes why nonnormal transient
amplification prevents an unconditional monotone-depth entropy theorem. -/
theorem linearGaussianReadEntropy_strictAntiOn
    (scale : ℝ) (hscale : 0 < scale) :
    StrictAntiOn (linearGaussianReadEntropy scale) (Ici (0 : ℝ)) := by
  intro first hfirst second hsecond hlt
  apply Real.binEntropy_strictAntiOn
  · exact linearGaussianReadProbability_mem_Icc scale first hscale.le hfirst
  · exact linearGaussianReadProbability_mem_Icc scale second hscale.le hsecond
  · rw [linearGaussianReadProbability, linearGaussianReadProbability,
      Real.sigmoid_lt_iff]
    exact mul_lt_mul_of_pos_left hlt hscale

/-- The linear-Gaussian read entropy is continuous in residual magnitude.  This
supports only the linear equilibrium-limit statement below. -/
theorem continuous_linearGaussianReadEntropy (scale : ℝ) :
    Continuous (linearGaussianReadEntropy scale) := by
  exact Real.binEntropy_continuous.comp
    (continuous_sigmoid.comp (continuous_const.mul continuous_id))

/-- Read entropy along the residual of an affine linear workspace model.  This
definition does not extend the diagnostic to nonlinear trained decoders. -/
noncomputable def linearWorkspaceReadEntropy
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (model : LinearWorkspaceModel State) (scale : ℝ)
    (initial : State) (depth : ℕ) : ℝ :=
  linearGaussianReadEntropy scale
    ‖model.step^[depth] initial - model.equilibrium‖

/-- Prediction (b), linear scope: under the same spectral condition as T2,
the linear-Gaussian read entropy tends to the uniform binary entropy.  The
theorem deliberately does not assert monotonicity at each depth. -/
theorem linearWorkspaceReadEntropy_tendsto_uniform
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State] [Nontrivial State]
    (model : LinearWorkspaceModel State) (scale : ℝ) (initial : State)
    (hradius : spectralRadius ℂ model.linearPart < 1) :
    Tendsto (linearWorkspaceReadEntropy model scale initial)
      atTop (𝓝 (Real.binEntropy (1 / 2))) := by
  have hstate := model.linearWorkspace_tendsto_equilibrium initial hradius
  have hresidual : Tendsto
      (fun depth : ℕ => ‖model.step^[depth] initial - model.equilibrium‖)
      atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hstate)
  have hentropy :=
    (continuous_linearGaussianReadEntropy scale).continuousAt.tendsto.comp hresidual
  change Tendsto
    (fun depth : ℕ => linearGaussianReadEntropy scale
      ‖model.step^[depth] initial - model.equilibrium‖)
    atTop (𝓝 (Real.binEntropy (1 / 2)))
  have hzero : linearGaussianReadEntropy scale 0 = Real.binEntropy (1 / 2) := by
    simp [linearGaussianReadEntropy, linearGaussianReadProbability,
      Real.sigmoid_zero]
  rw [← hzero]
  simpa only [Function.comp_def] using hentropy

/-- Negative boundary for prediction (b): residual amplification from one to
two strictly decreases entropy, so spectral convergence without a per-step
norm order cannot determine the observed entropy trajectory. -/
theorem amplifiedResidual_lowersEntropy_negativeExample :
    linearGaussianReadEntropy 1 2 < linearGaussianReadEntropy 1 1 := by
  exact linearGaussianReadEntropy_strictAntiOn 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-! ## Hash-pinned depth-probe fixture schema -/

/-- Canonical minified JSON Schema payload for the three-lineage depth probe.
Weighted evidence and Gaussian natural information are the recorded primal
coordinates.  Effective evidence, strength, confidence, mean, gain, and the
registered and derived decay schedules are observations; numeric observations
are data rather than formal claims. -/
def depthProbeSchemaPayload : String :=
  "{" ++
  "\"$schema\":\"https://json-schema.org/draft/2020-12/schema\"," ++
  "\"$id\":\"workspace_decoder.depth_probe.v2\"," ++
  "\"title\":\"Three-lineage weighted-evidence depth probe record\"," ++
  "\"type\":\"object\"," ++
  "\"additionalProperties\":false," ++
  "\"required\":[\"schema_version\",\"run_id\",\"lineage\",\"seed\"," ++
    "\"generation\",\"split\",\"example_id\",\"recurrence_depth\"," ++
    "\"target_action_id\",\"held_out_loss\",\"settling_residual_norm\"," ++
    "\"read_attention_entropy\",\"legal_action_count\",\"accepted\"," ++
    "\"confidence_kappa\",\"slot_evidence_trajectories\"]," ++
  "\"properties\":{" ++
    "\"schema_version\":{\"const\":\"workspace_decoder.depth_probe.v2\"}," ++
    "\"run_id\":{\"type\":\"string\",\"minLength\":1}," ++
    "\"lineage\":{\"enum\":[\"gru\",\"workspace\",\"selective_belief\"]}," ++
    "\"seed\":{\"type\":\"integer\",\"minimum\":0}," ++
    "\"generation\":{\"type\":\"integer\",\"minimum\":0}," ++
    "\"split\":{\"enum\":[\"calibration\",\"held_out\"]}," ++
    "\"example_id\":{\"type\":\"string\",\"minLength\":1}," ++
    "\"recurrence_depth\":{\"type\":\"integer\",\"minimum\":0}," ++
    "\"target_action_id\":{\"type\":\"string\",\"minLength\":1}," ++
    "\"held_out_loss\":{\"type\":\"number\",\"minimum\":0}," ++
    "\"settling_residual_norm\":{\"type\":\"number\",\"minimum\":0}," ++
    "\"read_attention_entropy\":{\"type\":\"number\",\"minimum\":0}," ++
    "\"legal_action_count\":{\"type\":\"integer\",\"minimum\":0}," ++
    "\"accepted\":{\"type\":\"boolean\"}," ++
    "\"confidence_kappa\":{\"type\":\"number\",\"exclusiveMinimum\":0}," ++
    "\"slot_evidence_trajectories\":{\"type\":\"array\",\"items\":{" ++
      "\"type\":\"object\",\"additionalProperties\":false," ++
      "\"required\":[\"slot_id\",\"steps\"]," ++
      "\"properties\":{" ++
        "\"slot_id\":{\"type\":\"string\",\"minLength\":1}," ++
        "\"steps\":{\"type\":\"array\",\"items\":{" ++
          "\"type\":\"object\",\"additionalProperties\":false," ++
          "\"required\":[\"recurrence_depth\",\"n_plus\",\"n_minus\"," ++
            "\"effective_evidence\",\"decay_retention\"," ++
            "\"derived_decay_default\",\"natural_parameter\"," ++
            "\"precision\",\"strength\",\"confidence\",\"mean\",\"gain\"]," ++
          "\"properties\":{" ++
            "\"recurrence_depth\":{\"type\":\"integer\",\"minimum\":0}," ++
            "\"n_plus\":{\"type\":\"number\",\"minimum\":0}," ++
            "\"n_minus\":{\"type\":\"number\",\"minimum\":0}," ++
            "\"effective_evidence\":{\"type\":\"number\",\"minimum\":0}," ++
            "\"decay_retention\":{\"type\":\"number\",\"minimum\":0," ++
              "\"maximum\":1}," ++
            "\"derived_decay_default\":{\"type\":\"number\",\"minimum\":0," ++
              "\"maximum\":1}," ++
            "\"natural_parameter\":{\"type\":\"number\"}," ++
            "\"precision\":{\"type\":\"number\",\"minimum\":0}," ++
            "\"strength\":{\"type\":\"number\",\"minimum\":0,\"maximum\":1}," ++
            "\"confidence\":{\"type\":\"number\",\"minimum\":0,\"maximum\":1}," ++
            "\"mean\":{\"type\":\"number\"}," ++
            "\"gain\":{\"type\":\"number\"}" ++
          "}}" ++
      "}}}}" ++
  "}," ++
  "\"formal_scope\":{" ++
    "\"prediction_a\":\"derived_for_exact_linear_shift_mismatch\"," ++
    "\"prediction_b\":\"entropy_antitone_in_nonnegative_linear_gaussian_residual\"," ++
    "\"belief_coordinates\":\"weighted_n_plus_n_minus\"," ++
    "\"gaussian_coordinates\":\"natural_information_eta_lambda\"," ++
    "\"derived_columns\":[\"effective_evidence\",\"strength\",\"confidence\"," ++
      "\"mean\",\"gain\"]," ++
    "\"decay_columns\":[\"decay_retention\",\"derived_decay_default\"]," ++
    "\"nonlinear_trajectory\":\"registered_empirical_question\"}" ++
  "}"

/-- SHA-256 computed by the repository's Lean SHA implementation.  The literal
pin is checked below before the fixture is exported. -/
def depthProbeSchemaComputedSha256 : String :=
  sha256Hex depthProbeSchemaPayload

/-- Immutable SHA-256 pin for the canonical schema payload. -/
def depthProbeSchemaSha256 : String :=
  "324f5a67d1907420e0161d07f22b480487a94fbdd6fe33db8c78bfd0efd9b03c"

/- The build fails if the repository's Lean SHA-256 implementation does not
recompute the literal schema pin exactly. -/
#guard depthProbeSchemaComputedSha256 == depthProbeSchemaSha256

/-- Export envelope containing the pinned digest and canonical JSON Schema.
The digest covers the `schema` payload and intentionally excludes itself. -/
def renderDepthProbeSchemaFixture : String :=
  "{\"schema_sha256\":\"" ++ depthProbeSchemaSha256 ++
    "\",\"schema\":" ++ depthProbeSchemaPayload ++ "}\n"

#print axioms linearGaussianReadEntropy_antitoneOn
#print axioms linearGaussianReadEntropy_strictAntiOn
#print axioms linearWorkspaceReadEntropy_tendsto_uniform
#print axioms amplifiedResidual_lowersEntropy_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
