import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Autoencoder-mediated target propagation

Bengio, *How Auto-Encoders Could Provide Credit Assignment in Deep Networks
via Target Propagation* (arXiv:1407.7906), Section 2.2.6 and Figure 3, argues
that a better upper-layer target can be decoded into a better nearby
lower-layer target when encoder and decoder are local inverses.

The exact argument needs two differently directed reconstruction facts:

* `decode (encode current) ≈ current` keeps the propagated lower target near
  the current lower state;
* `encode (decode target) ≈ target` transfers the upper target's cost
  improvement through the encoder.

This file makes both directions explicit and replaces informal
"approximately" statements by a measurable budget.  A Lipschitz decoder and
current reconstruction error bound control lower-target displacement.  A
Lipschitz cost and target reconstruction error bound control the realized
upper cost.  Strict improvement follows exactly when the original target's
cost margin exceeds that error budget.

A coordinate-embedding fixture shows why inverse direction matters:
`decode ∘ encode = id` can hold everywhere while `encode ∘ decode` is only a
projection.  A target outside the encoder range is strictly better, yet its
decoded-and-reencoded image need not improve the current cost.

The results are finite target and finite error statements; differentiability
is not required.  They do not claim that a learned decoder satisfies the
premises or that the resulting local parameter update improves a whole
network.

Source artifact SHA-256:
`057169c28f576962098436325de05c6bdc5c296501acd846f2de63ab8be6f104`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace AutoencoderTargetPropagation

variable {Lower Upper : Type*}
  [NormedAddCommGroup Lower] [NormedAddCommGroup Upper]

/-- A global norm-Lipschitz bound stated with an ordinary nonnegative real
constant, suitable for runtime certificates. -/
def HasLipschitzBound
    (map : Lower → Upper) (constant : ℝ) : Prop :=
  0 ≤ constant ∧
    ∀ first second,
      ‖map first - map second‖ ≤
        constant * ‖first - second‖

/-- A real-valued cost has a norm-Lipschitz bound. -/
def HasCostLipschitzBound
    (cost : Upper → ℝ) (constant : ℝ) : Prop :=
  0 ≤ constant ∧
    ∀ first second,
      |cost first - cost second| ≤
        constant * ‖first - second‖

/-- The decoded upper target is the proposed lower-layer target. -/
def propagatedTarget
    (decode : Upper → Lower) (target : Upper) : Lower :=
  decode target

omit [NormedAddCommGroup Lower] [NormedAddCommGroup Upper] in
/-- An exact right-inverse reconstruction at the target transfers every strict
upper cost improvement through the encoder. -/
theorem exact_target_reconstruction_strictly_improves
    (encode : Lower → Upper)
    (decode : Upper → Lower)
    (cost : Upper → ℝ)
    (current : Lower)
    (target : Upper)
    (htarget : encode (decode target) = target)
    (himproves : cost target < cost (encode current)) :
    cost (encode (propagatedTarget decode target)) <
      cost (encode current) := by
  simpa [propagatedTarget, htarget] using himproves

omit [NormedAddCommGroup Lower] in
/-- Approximate target reconstruction increases target cost by at most the
cost-Lipschitz constant times the reconstruction error. -/
theorem approximate_target_reconstruction_cost_le
    (encode : Lower → Upper)
    (decode : Upper → Lower)
    (cost : Upper → ℝ)
    (costConstant targetError : ℝ)
    (target : Upper)
    (hcost : HasCostLipschitzBound cost costConstant)
    (htarget :
      ‖encode (decode target) - target‖ ≤ targetError) :
    cost (encode (propagatedTarget decode target)) ≤
      cost target + costConstant * targetError := by
  have habs :=
    hcost.2 (encode (decode target)) target
  have hdiff :
      cost (encode (decode target)) - cost target ≤
        costConstant * targetError := by
    calc
      cost (encode (decode target)) - cost target ≤
          |cost (encode (decode target)) - cost target| :=
        le_abs_self _
      _ ≤ costConstant * ‖encode (decode target) - target‖ :=
        habs
      _ ≤ costConstant * targetError :=
        mul_le_mul_of_nonneg_left htarget hcost.1
  dsimp [propagatedTarget]
  linarith

omit [NormedAddCommGroup Lower] in
/-- A target improvement margin larger than the approximate reconstruction
budget gives a strict realized improvement. -/
theorem approximate_target_reconstruction_strictly_improves
    (encode : Lower → Upper)
    (decode : Upper → Lower)
    (cost : Upper → ℝ)
    (costConstant targetError : ℝ)
    (current : Lower)
    (target : Upper)
    (hcost : HasCostLipschitzBound cost costConstant)
    (htarget :
      ‖encode (decode target) - target‖ ≤ targetError)
    (hmargin :
      cost target + costConstant * targetError <
        cost (encode current)) :
    cost (encode (propagatedTarget decode target)) <
      cost (encode current) :=
  lt_of_le_of_lt
    (approximate_target_reconstruction_cost_le
      encode decode cost costConstant targetError target hcost htarget)
    hmargin

/-- Decoder Lipschitzness plus a measured current reconstruction error bounds
the distance from the propagated target to the current lower state. -/
theorem propagatedTarget_distance_le
    (encode : Lower → Upper)
    (decode : Upper → Lower)
    (decoderConstant currentError : ℝ)
    (current : Lower)
    (target : Upper)
    (hdecode : HasLipschitzBound decode decoderConstant)
    (hcurrent :
      ‖decode (encode current) - current‖ ≤ currentError) :
    ‖propagatedTarget decode target - current‖ ≤
      decoderConstant * ‖target - encode current‖ + currentError := by
  calc
    ‖propagatedTarget decode target - current‖ =
        ‖(decode target - decode (encode current)) +
          (decode (encode current) - current)‖ := by
      congr 1
      simp [propagatedTarget]
    _ ≤ ‖decode target - decode (encode current)‖ +
          ‖decode (encode current) - current‖ :=
      norm_add_le _ _
    _ ≤ decoderConstant * ‖target - encode current‖ +
          currentError :=
      add_le_add (hdecode.2 target (encode current)) hcurrent

/-- Reusable finite-target crown: independently measurable reconstruction,
decoder, and cost budgets yield both a nearby lower target and strict realized
upper cost improvement. -/
theorem approximate_target_propagation_crown
    (encode : Lower → Upper)
    (decode : Upper → Lower)
    (cost : Upper → ℝ)
    (decoderConstant costConstant currentError targetError : ℝ)
    (current : Lower)
    (target : Upper)
    (hdecode : HasLipschitzBound decode decoderConstant)
    (hcost : HasCostLipschitzBound cost costConstant)
    (hcurrent :
      ‖decode (encode current) - current‖ ≤ currentError)
    (htarget :
      ‖encode (decode target) - target‖ ≤ targetError)
    (hmargin :
      cost target + costConstant * targetError <
        cost (encode current)) :
    ‖propagatedTarget decode target - current‖ ≤
        decoderConstant * ‖target - encode current‖ + currentError ∧
      cost (encode (propagatedTarget decode target)) <
        cost (encode current) :=
  ⟨propagatedTarget_distance_le
      encode decode decoderConstant currentError current target
      hdecode hcurrent,
    approximate_target_reconstruction_strictly_improves
      encode decode cost costConstant targetError current target
      hcost htarget hmargin⟩

/-! ## Inverse-direction counterexample -/

/-- Embed a scalar as the first coordinate of a plane. -/
def coordinateEncode (value : ℝ) : ℝ × ℝ :=
  (value, 0)

/-- Decode a plane by retaining only its first coordinate. -/
def coordinateDecode (value : ℝ × ℝ) : ℝ :=
  value.1

/-- Squared distance of the second coordinate from one. -/
def secondCoordinateTargetCost (value : ℝ × ℝ) : ℝ :=
  (value.2 - 1) ^ 2

/-- The decoder is a perfect left inverse of the encoder. -/
theorem coordinateDecode_leftInverse :
    Function.LeftInverse coordinateDecode coordinateEncode := by
  intro value
  rfl

/-- The opposite composition is not the identity. -/
theorem coordinateEncode_not_rightInverse :
    coordinateEncode (coordinateDecode (0, 1)) ≠
      ((0, 1) : ℝ × ℝ) := by
  norm_num [coordinateEncode, coordinateDecode]

/-- Even with perfect current reconstruction, a strictly better target outside
the encoder range can decode and re-encode to a point that is not better. -/
theorem leftInverse_alone_does_not_propagate_improvement :
    coordinateDecode (coordinateEncode 1) = 1 ∧
      secondCoordinateTargetCost (0, 1) <
        secondCoordinateTargetCost (coordinateEncode 1) ∧
      ¬ secondCoordinateTargetCost
          (coordinateEncode (coordinateDecode (0, 1))) <
        secondCoordinateTargetCost (coordinateEncode 1) := by
  norm_num
    [coordinateEncode, coordinateDecode, secondCoordinateTargetCost]

end AutoencoderTargetPropagation

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
