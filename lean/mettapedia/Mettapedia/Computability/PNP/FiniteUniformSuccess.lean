import Mettapedia.Computability.PNP.FiniteUniformRate

/-!
# P vs NP background theory: finite uniform success bounds

This file packages the rational rate layer into a cleaner "uniform success"
interface.  The main quantity is the one-step miss ratio

`((|X| - 1) / |X|)`,

which is strictly less than `1` on any nonempty finite input domain.  In these
terms the deceptive-sample rate decays like

`|Code(H)| * missRatio^m`,

and exact ERM recovery has the complementary lower bound.

This is still a fully finite and uniform-sampling result, not yet the full
i.i.d. or PAC-style generalization theorem.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- The uniform one-step miss ratio on a finite input domain. -/
noncomputable def uniformMissRatio (Input : Type u) [Fintype Input] : ℚ :=
  (((Fintype.card Input : ℚ) - 1) / Fintype.card Input)

theorem uniformMissRatio_lt_one (Input : Type u) [Fintype Input] [Nonempty Input] :
    uniformMissRatio Input < 1 := by
  unfold uniformMissRatio
  have hpos : (0 : ℚ) < Fintype.card Input := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Input)
  have hlt : (Fintype.card Input : ℚ) - 1 < Fintype.card Input := by
    exact sub_lt_self _ zero_lt_one
  exact (div_lt_one hpos).2 hlt

namespace EncodedFamily

section UniformSuccess

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [Nonempty Input] [DecidableEq Output]
variable (H : EncodedFamily Input Output)

theorem deceptiveRate_le_codeMul_uniformMissRatio_pow
    (target : Input → Output) (m : ℕ) :
    H.deceptiveRate target m ≤
      (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m := by
  calc
    H.deceptiveRate target m
      ≤ (((Fintype.card H.Code : ℚ) * ((Fintype.card Input : ℚ) - 1) ^ m) /
          ((Fintype.card Input : ℚ) ^ m)) :=
        H.deceptiveRate_le_bound target m
    _ = (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m := by
      unfold uniformMissRatio
      rw [mul_div_assoc, ← div_pow]

theorem exactRecoveryRate_ge_one_sub_codeMul_uniformMissRatio_pow
    [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target) :
    1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤
      H.exactRecoveryRate target m := by
  have hdeceptive :
      H.deceptiveRate target m ≤
        (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m :=
    H.deceptiveRate_le_codeMul_uniformMissRatio_pow target m
  have hone :
      1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤
        1 - H.deceptiveRate target m := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      add_le_add_left (neg_le_neg hdeceptive) 1
  exact le_trans hone (H.exactRecoveryRate_ge_one_sub_deceptiveRate target m htarget)

theorem exactRecoveryRate_ge_one_sub_of_codeMul_uniformMissRatio_pow_le
    [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target)
    {ε : ℚ}
    (hε :
      (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤ ε) :
    1 - ε ≤ H.exactRecoveryRate target m := by
  have hstep :
      1 - ε ≤ 1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      add_le_add_left (neg_le_neg hε) 1
  exact le_trans hstep <|
    H.exactRecoveryRate_ge_one_sub_codeMul_uniformMissRatio_pow target m htarget

theorem exactRecoveryRate_pos_of_codeMul_uniformMissRatio_pow_lt_one
    [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target)
    (hlt :
      (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m < 1) :
    0 < H.exactRecoveryRate target m := by
  have hpos :
      0 < 1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m := by
    have : 1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m > 0 := by
      exact sub_pos.mpr hlt
    simpa using this
  exact lt_of_lt_of_le hpos <|
    H.exactRecoveryRate_ge_one_sub_codeMul_uniformMissRatio_pow target m htarget

end UniformSuccess

end EncodedFamily

end Mettapedia.Computability.PNP
