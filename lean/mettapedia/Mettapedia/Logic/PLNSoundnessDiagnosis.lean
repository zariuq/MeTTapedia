import Mettapedia.Logic.PLNSoundnessCounterexample

/-!
# Diagnosis: Where Does the Soundness Condition Break?

This module keeps only theorem-valid diagnostic endpoints.
It isolates the conjunction/product break for the schema
`|P - s| ≤ 1 - c` when confidence is combined by `w2c (c2w cA * c2w cB)`.
-/

namespace Mettapedia.Logic.PLNSoundnessDiagnosis

open Mettapedia.Logic.PLNWeightTV

/-- Atomic soundness schema used as a local premise. -/
def AtomicSoundness (P s c : ℝ) : Prop :=
  |P - s| ≤ 1 - c

/-- Trivial transport: an assumed atomic soundness judgment is available as-is. -/
theorem atomic_soundness_holds (P s c : ℝ)
    (hAtomic : AtomicSoundness P s c) :
    AtomicSoundness P s c :=
  hAtomic

/-- Concrete conjunction witness showing failure of the naive propagated schema.

Each premise satisfies `|Pᵢ - sᵢ| ≤ 1 - cᵢ` with `cᵢ = 0.5`, but the combined
judgment violates `|P_A*P_B - s_A*s_B| ≤ 1 - w2c (c2w c_A * c2w c_B)`.
-/
theorem conjunction_soundness_breaks :
    ∃ (P_A P_B s_A s_B c_A c_B : ℝ),
      AtomicSoundness P_A s_A c_A ∧
      AtomicSoundness P_B s_B c_B ∧
      ¬(|P_A * P_B - s_A * s_B| ≤ 1 - w2c (c2w c_A * c2w c_B)) := by
  refine ⟨1, 1, 0.5, 0.5, 0.5, 0.5, ?_, ?_, ?_⟩
  · norm_num [AtomicSoundness]
  · norm_num [AtomicSoundness]
  · unfold w2c c2w
    norm_num

/-- Worst-case budget form at `c_A = c_B = 0.5` fails.

This is the algebraic core used by the counterexample file.
-/
theorem worst_case_conjunction_fails :
    let c_A := (0.5 : ℝ)
    let c_B := (0.5 : ℝ)
    let c_out := w2c (c2w c_A * c2w c_B)
    ¬((1 - c_A) + (1 - c_B) ≤ 1 - c_out) := by
  unfold w2c c2w
  norm_num

end Mettapedia.Logic.PLNSoundnessDiagnosis
