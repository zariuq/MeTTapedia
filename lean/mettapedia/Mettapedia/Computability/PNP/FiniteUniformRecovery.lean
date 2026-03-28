import Mettapedia.Computability.PNP.FiniteConsistencyBound
import Mathlib.Data.Fintype.Card

/-!
# P vs NP background theory: finite uniform recovery

This file packages the counting bounds from `FiniteConsistencyBound.lean` into
clean existence statements.  The perspective is still fully finite and
combinatorial: if the deceptive sample set is strictly smaller than the total
sample space, then some sample escapes it; and when the target predictor is in
the encoded family, ERM recovers the target exactly on such a sample.

This is the last natural "pure counting" layer before introducing an explicit
probability interface.
-/

namespace Mettapedia.Computability.PNP

universe u v

theorem card_pointSample
    (Input : Type u) [Fintype Input] (m : ℕ) :
    Fintype.card (PointSample Input m) = Fintype.card Input ^ m := by
  simp [PointSample]

namespace EncodedFamily

section UniformRecovery

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [DecidableEq Output]
variable (H : EncodedFamily Input Output)

omit [DecidableEq Output] in
theorem exists_nondeceptiveSample_of_card_gap
    (target : Input → Output) {m : ℕ}
    (hgap : Fintype.card (H.DeceptiveSamples target m) < Fintype.card (PointSample Input m)) :
    ∃ sample : PointSample Input m, ¬ H.IsDeceptiveSample target sample := by
  by_contra hnone
  push_neg at hnone
  let s : Set (PointSample Input m) := {sample | H.IsDeceptiveSample target sample}
  let _ : Fintype s := Fintype.ofFinite s
  have hs_univ : s = Set.univ := by
    ext sample
    simp [s, hnone sample]
  have hcardEq : Fintype.card (H.DeceptiveSamples target m) = Fintype.card (PointSample Input m) := by
    simpa [DeceptiveSamples, s] using
      (set_fintype_card_eq_univ_iff s).2 hs_univ
  exact (ne_of_lt hgap) hcardEq

theorem exists_nondeceptiveSample_of_bound_lt
    (target : Input → Output) (m : ℕ)
    (hbound :
      Fintype.card H.Code * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m, ¬ H.IsDeceptiveSample target sample := by
  apply H.exists_nondeceptiveSample_of_card_gap target
  rw [card_pointSample Input m]
  exact lt_of_le_of_lt (H.card_deceptiveSamples_le target m) hbound

theorem exists_sample_empiricalRiskPredictor_eq_target_of_bound_lt
    [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target)
    (hbound :
      Fintype.card H.Code * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      H.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  rcases H.exists_nondeceptiveSample_of_bound_lt target m hbound with ⟨sample, hsample⟩
  refine ⟨sample, ?_⟩
  exact H.empiricalRiskPredictor_eq_target_of_not_deceptive target sample htarget hsample

end UniformRecovery

end EncodedFamily

end Mettapedia.Computability.PNP
