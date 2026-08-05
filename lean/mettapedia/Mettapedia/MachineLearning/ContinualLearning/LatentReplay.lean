import Mathlib.Tactic

/-!
# Latent replay

Pellegrini, Graffieti, Lomonaco, and Maltoni (2020), *Latent Replay
for Real-Time Continual Learning*, cache intermediate activations instead of
raw examples.  In the limiting case where every representation layer below
the replay point is frozen, the source states that latent replay is
functionally equivalent to native rehearsal.  When those layers continue to
move, cached activations age.

This file makes both claims precise:

* an externally supplied exact-cache relation makes any downstream replay
  update identical to native replay;
* the distance from a cached latent to the current latent is bounded by the
  accumulated finite representation drift, and a Lipschitz downstream map
  transports that drift to its output;
* refreshing a cache resets its pointwise age error to zero.

The word "frozen" covers all mutable representation state.  A scalar
normalization fixture keeps the encoder weight fixed while changing its
running mean; the cached latent and current latent then differ.  Thus frozen
weights with mutable batch-normalization state do not satisfy the exact-cache
premise.  Storage, wall-clock savings, and continual-learning accuracy remain
empirical.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace LatentReplay

noncomputable section

open scoped BigOperators

variable {Raw Latent Target Parameters : Type*}

/-- Encode the raw examples while retaining their targets. -/
def encodeReplayBatch
    (encoder : Raw → Latent)
    (batch : List (Raw × Target)) : List (Latent × Target) :=
  batch.map fun entry => (encoder entry.1, entry.2)

/-- The explicit external obligation connecting stored latents to a raw
replay batch under the current representation map. -/
def CacheMatches
    (encoder : Raw → Latent)
    (rawBatch : List (Raw × Target))
    (latentBatch : List (Latent × Target)) : Prop :=
  latentBatch = encodeReplayBatch encoder rawBatch

/-- A native replay step first evaluates the representation map. -/
def nativeReplayStep
    (encoder : Raw → Latent)
    (downstreamStep :
      Parameters → List (Latent × Target) → Parameters)
    (parameters : Parameters)
    (rawBatch : List (Raw × Target)) : Parameters :=
  downstreamStep parameters (encodeReplayBatch encoder rawBatch)

/-- A latent replay step consumes the stored representation directly. -/
def latentReplayStep
    (downstreamStep :
      Parameters → List (Latent × Target) → Parameters)
    (parameters : Parameters)
    (latentBatch : List (Latent × Target)) : Parameters :=
  downstreamStep parameters latentBatch

/-- **Frozen-representation equivalence.** Any downstream update agrees
exactly when the cache is authenticated against the current encoder and raw
batch. -/
theorem latentReplayStep_eq_nativeReplayStep_of_cacheMatches
    (encoder : Raw → Latent)
    (downstreamStep :
      Parameters → List (Latent × Target) → Parameters)
    (parameters : Parameters)
    (rawBatch : List (Raw × Target))
    (latentBatch : List (Latent × Target))
    (cacheMatches : CacheMatches encoder rawBatch latentBatch) :
    latentReplayStep downstreamStep parameters latentBatch =
      nativeReplayStep encoder downstreamStep parameters rawBatch := by
  rw [cacheMatches]
  rfl

/-! ## Executable exact and stale-cache fixtures -/

def sumLatentStep
    (parameters : ℝ)
    (batch : List (ℝ × Unit)) : ℝ :=
  parameters + (batch.map Prod.fst).sum

def unitRawBatch : List (ℝ × Unit) :=
  [(2, ())]

def exactUnitLatentBatch : List (ℝ × Unit) :=
  [(2, ())]

def staleUnitLatentBatch : List (ℝ × Unit) :=
  [(1, ())]

theorem exactUnitCache_matches :
    CacheMatches id unitRawBatch exactUnitLatentBatch := by
  norm_num [CacheMatches, encodeReplayBatch,
    unitRawBatch, exactUnitLatentBatch]

theorem exactUnitCache_replayStep_eq :
    latentReplayStep sumLatentStep 0 exactUnitLatentBatch =
      nativeReplayStep id sumLatentStep 0 unitRawBatch :=
  latentReplayStep_eq_nativeReplayStep_of_cacheMatches
    id sumLatentStep 0 unitRawBatch exactUnitLatentBatch
    exactUnitCache_matches

/-- An unauthenticated stale cache can change the downstream parameter update. -/
theorem staleUnitCache_changes_replayStep :
    latentReplayStep sumLatentStep 0 staleUnitLatentBatch ≠
      nativeReplayStep id sumLatentStep 0 unitRawBatch := by
  norm_num [latentReplayStep, nativeReplayStep, sumLatentStep,
    encodeReplayBatch, staleUnitLatentBatch, unitRawBatch]

/-! ## Finite latent aging -/

variable {Representation : Type*} [NormedAddCommGroup Representation]

/-- Sum of consecutive representation changes along a finite trace. -/
def latentPathVariation :
    Representation → List Representation → ℝ
  | _, [] => 0
  | current, next :: rest =>
      ‖next - current‖ + latentPathVariation next rest

/-- Final representation state of a finite trace, or the initial state for an
empty trace. -/
def finalLatent :
    Representation → List Representation → Representation
  | initial, [] => initial
  | _, next :: rest => finalLatent next rest

/-- Aging is bounded by accumulated representation drift. -/
theorem norm_finalLatent_sub_initial_le_latentPathVariation
    (initial : Representation)
    (trace : List Representation) :
    ‖finalLatent initial trace - initial‖ ≤
      latentPathVariation initial trace := by
  induction trace generalizing initial with
  | nil =>
      simp [finalLatent, latentPathVariation]
  | cons next rest inductionHypothesis =>
      simp only [finalLatent, latentPathVariation]
      calc
        ‖finalLatent next rest - initial‖ =
            ‖(finalLatent next rest - next) +
              (next - initial)‖ := by
              congr 1
              abel
        _ ≤ ‖finalLatent next rest - next‖ +
              ‖next - initial‖ :=
            norm_add_le _ _
        _ ≤ latentPathVariation next rest +
              ‖next - initial‖ :=
            add_le_add (inductionHypothesis next) (le_refl _)
        _ = ‖next - initial‖ +
              latentPathVariation next rest := by
            ring

/-- A fully frozen finite representation trace has zero variation. -/
theorem latentPathVariation_replicate
    (latent : Representation) (steps : ℕ) :
    latentPathVariation latent (List.replicate steps latent) = 0 := by
  induction steps with
  | zero =>
      simp [latentPathVariation]
  | succ steps inductionHypothesis =>
      simpa [List.replicate_succ, latentPathVariation] using inductionHypothesis

/-- Refreshing a point cache with the current latent resets its age error. -/
@[simp] theorem refresh_resets_latent_age
    (current : Representation) :
    ‖current - current‖ = 0 := by
  rw [sub_self, norm_zero]

/-! ## Downstream transport of cache age -/

variable {Output : Type*} [NormedAddCommGroup Output]

/-- A Lipschitz downstream readout transports latent aging into a declared
output-mismatch budget. -/
theorem norm_head_cached_sub_current_le
    (head : Representation → Output)
    {constant : NNReal}
    (headLipschitz : LipschitzWith constant head)
    (cached current : Representation) :
    ‖head cached - head current‖ ≤
      (constant : ℝ) * ‖cached - current‖ :=
  headLipschitz.norm_sub_le cached current

/-- Combining the path budget with downstream Lipschitzness gives an
observable finite output-aging certificate. -/
theorem norm_head_final_sub_initial_le_pathVariation
    (head : Representation → Output)
    {constant : NNReal}
    (headLipschitz : LipschitzWith constant head)
    (initial : Representation)
    (trace : List Representation) :
    ‖head (finalLatent initial trace) - head initial‖ ≤
      (constant : ℝ) * latentPathVariation initial trace := by
  calc
    ‖head (finalLatent initial trace) - head initial‖ ≤
        (constant : ℝ) *
          ‖finalLatent initial trace - initial‖ :=
      headLipschitz.norm_sub_le _ _
    _ ≤ (constant : ℝ) *
          latentPathVariation initial trace := by
      exact mul_le_mul_of_nonneg_left
        (norm_finalLatent_sub_initial_le_latentPathVariation
          initial trace)
        constant.coe_nonneg

/-! ## Mutable normalization is representation drift -/

/-- A scalar stateful encoder with one fixed weight and one mutable centering
state, modeling the relevant batch-normalization boundary. -/
def scalarStatefulEncoder
    (weight runningMean input : ℝ) : ℝ :=
  weight * (input - runningMean)

/-- Keeping the encoder weight fixed does not freeze its representation when
the normalization state moves. -/
theorem fixed_weight_mutable_normalization_ages_cache :
    scalarStatefulEncoder 1 0 2 = 2 ∧
      scalarStatefulEncoder 1 1 2 = 1 ∧
      |scalarStatefulEncoder 1 0 2 -
        scalarStatefulEncoder 1 1 2| = 1 := by
  norm_num [scalarStatefulEncoder]

/-- The identity downstream head exposes the same unit cache mismatch. -/
theorem mutable_normalization_changes_downstream_output :
    id (scalarStatefulEncoder 1 0 2) ≠
      id (scalarStatefulEncoder 1 1 2) := by
  norm_num [scalarStatefulEncoder]

#print axioms latentReplayStep_eq_nativeReplayStep_of_cacheMatches
#print axioms exactUnitCache_replayStep_eq
#print axioms staleUnitCache_changes_replayStep
#print axioms norm_finalLatent_sub_initial_le_latentPathVariation
#print axioms latentPathVariation_replicate
#print axioms norm_head_final_sub_initial_le_pathVariation
#print axioms fixed_weight_mutable_normalization_ages_cache
#print axioms mutable_normalization_changes_downstream_output

end

end LatentReplay

end Mettapedia.MachineLearning.ContinualLearning
