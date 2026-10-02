import Mettapedia.Languages.VibeITP.Presentation.CompleteLists
import Mettapedia.Languages.VibeITP.Presentation.SoundTheorems

/-!
# Constructive literal inference witnesses

The number-literal witnesses use the specification's actual one-byte or
eight-byte representation.  Each primitive literal theorem is then derived
with the exact guards of its corresponding static kernel constructor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

private theorem literalRule_in {R : List FORule} (hR : kernelRules ⊆ R)
    {r : FORule} (hr : r ∈ literalRules) : r ∈ R :=
  hR (by simp [kernelRules, hr])

private theorem theoremRule_in {R : List FORule} (hR : kernelRules ⊆ R)
    {r : FORule} (hr : r ∈ theoremRules) : r ∈ R :=
  hR (by simp [kernelRules, hr])

/-- Number-literal formation computes the actual specification encoding,
including its low-eight-byte behavior on unbounded arithmetic witnesses. -/
theorem complete_natlit {R : List FORule} (hR : kernelRules ⊆ R) (n : Nat) :
    FODerivable R (jNatLit (encNat n) (encBytes (natLiteral n))) := by
  by_cases hn : n < 256
  · rw [encBytes_natLiteral_small n hn]
    have hadd := complete_nadd hR n (256 - n)
    rw [show n + (256 - n) = 256 by omega, encNat_pos (256 - n) (by omega)] at hadd
    exact intro_rNatlitSmall (literalRule_in hR (by simp [literalRules]))
      (isData_encNat n) (isData_encPos (256 - n)) hadd
  · let q1 := n / 256
    let q2 := q1 / 256
    let q3 := q2 / 256
    let q4 := q3 / 256
    let q5 := q4 / 256
    let q6 := q5 / 256
    let q7 := q6 / 256
    let q8 := q7 / 256
    rw [natLiteral, if_neg hn]
    simp only [leBytes, encBytes_cons, uint8_toNat_ofNat_mod, encBytes_nil]
    exact intro_rNatlitLarge (literalRule_in hR (by simp [literalRules]))
      (isData_encNat n) (isData_encNat q1) (isData_encNat q2) (isData_encNat q3)
      (isData_encNat q4) (isData_encNat q5) (isData_encNat q6) (isData_encNat q7)
      (isData_encNat q8) (isData_encNat (n % 256)) (isData_encNat (q1 % 256))
      (isData_encNat (q2 % 256)) (isData_encNat (q3 % 256)) (isData_encNat (q4 % 256))
      (isData_encNat (q5 % 256)) (isData_encNat (q6 % 256)) (isData_encNat (q7 % 256))
      (complete_nle hR 256 n (by omega))
      (complete_ndivmod hR n 256 (by decide)) (complete_ndivmod hR q1 256 (by decide))
      (complete_ndivmod hR q2 256 (by decide)) (complete_ndivmod hR q3 256 (by decide))
      (complete_ndivmod hR q4 256 (by decide)) (complete_ndivmod hR q5 256 (by decide))
      (complete_ndivmod hR q6 256 (by decide)) (complete_ndivmod hR q7 256 (by decide))

theorem complete_bytes_literal_wf {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (bs : List UInt8) (hwf : WellFormed sig (.lit bs) = true) :
    FODerivable R (jWf (cLit (encBytes bs))) := by
  have hlen : bs.length + 8 < wordBound := by
    simpa only [WellFormed, decide_eq_true_eq] using hwf
  exact intro_rWfLit (hR (by simp [kernelRules, termRules]))
    (isData_encBytes bs) (isData_encNat bs.length) (isData_encNat (bs.length + 8))
    (complete_bytes hR bs) (complete_len_bytes hR bs) (complete_nadd hR bs.length 8)
    (complete_nword hR (bs.length + 8) hlen)

theorem natLiteral_length_le8 (n : Nat) : (natLiteral n).length ≤ 8 := by
  unfold natLiteral
  split
  · simp
  · simp

theorem wellFormed_natLiteral (sig : Sig) (n : Nat) :
    WellFormed sig (.natLit n) = true := by
  unfold Term.natLit WellFormed
  apply decide_eq_true
  have hlen := natLiteral_length_le8 n
  have hbound : 16 < wordBound := by decide
  omega

theorem complete_natLiteral_wf {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (n : Nat) : FODerivable R (jWf (cLit (encBytes (natLiteral n)))) :=
  complete_bytes_literal_wf hR sig (natLiteral n) (wellFormed_natLiteral sig n)

section LiteralTheorems

variable {R : List FORule} (hR : kernelRules ⊆ R) (T : Theory)
variable (hb : BuiltinsFixed T.sig)
include hR hb

theorem complete_litIsNat (n : Nat) (hn : n < wordBound) :
    FODerivable R (jThm (encTerm T.sig (litIsNatStatement n))) := by
  unfold litIsNatStatement Term.natLit
  rw [encTerm_litStatement1 hb]
  exact intro_rLitIsnat (theoremRule_in hR (by simp [theoremRules]))
    (isData_encNat n) (isData_encBytes (natLiteral n))
    (complete_nword hR n hn) (complete_natlit hR n)

theorem complete_litLt (a b : Nat) (hab : a < b) (hbw : b < wordBound) :
    FODerivable R (jThm (encTerm T.sig (litLtStatement a b))) := by
  unfold litLtStatement Term.natLit
  rw [encTerm_litStatement2 hb]
  exact intro_rLitLt (theoremRule_in hR (by simp [theoremRules]))
    (isData_encNat a) (isData_encNat b) (isData_encBytes (natLiteral a))
    (isData_encBytes (natLiteral b)) (complete_nlt hR a b hab) (complete_nword hR b hbw)
    (complete_natlit hR a) (complete_natlit hR b)

theorem complete_litAdd (a b : Nat) (haw : a < wordBound) (hbw : b < wordBound) :
    FODerivable R (jThm (encTerm T.sig (litAddStatement a b))) := by
  unfold litAddStatement Term.natLit
  rw [encTerm_litEquation hb .litAdd _ _ (by simp [depth_lit]) (by simp [hasFvar_lit])]
  exact intro_rLitAdd (theoremRule_in hR (by simp [theoremRules]))
    (isData_encNat a) (isData_encNat b) (isData_encNat (a + b))
    (isData_encNat ((a + b) % wordBound)) (isData_encBytes (natLiteral a))
    (isData_encBytes (natLiteral b)) (isData_encBytes (natLiteral ((a + b) % wordBound)))
    (complete_nword hR a haw) (complete_nword hR b hbw) (complete_nadd hR a b)
    (complete_nmod64 hR (a + b)) (complete_natlit hR a) (complete_natlit hR b)
    (complete_natlit hR ((a + b) % wordBound))

theorem complete_litMul (a b : Nat) (haw : a < wordBound) (hbw : b < wordBound) :
    FODerivable R (jThm (encTerm T.sig (litMulStatement a b))) := by
  unfold litMulStatement Term.natLit
  rw [encTerm_litEquation hb .litMul _ _ (by simp [depth_lit]) (by simp [hasFvar_lit])]
  exact intro_rLitMul (theoremRule_in hR (by simp [theoremRules]))
    (isData_encNat a) (isData_encNat b) (isData_encNat (a * b))
    (isData_encNat ((a * b) % wordBound)) (isData_encBytes (natLiteral a))
    (isData_encBytes (natLiteral b)) (isData_encBytes (natLiteral ((a * b) % wordBound)))
    (complete_nword hR a haw) (complete_nword hR b hbw) (complete_nmul hR a b)
    (complete_nmod64 hR (a * b)) (complete_natlit hR a) (complete_natlit hR b)
    (complete_natlit hR ((a * b) % wordBound))

theorem complete_litDiv (a b : Nat) (haw : a < wordBound) (hbw : b < wordBound)
    (hb0 : b ≠ 0) : FODerivable R (jThm (encTerm T.sig (litDivStatement a b))) := by
  unfold litDivStatement Term.natLit
  rw [encTerm_litEquation hb .litDiv _ _ (by simp [depth_lit]) (by simp [hasFvar_lit])]
  exact intro_rLitDiv (theoremRule_in hR (by simp [theoremRules]))
    (isData_encNat a) (isData_encNat b) (isData_encNat (a / b)) (isData_encNat (a % b))
    (isData_encBytes (natLiteral a)) (isData_encBytes (natLiteral b))
    (isData_encBytes (natLiteral (a / b))) (complete_nword hR a haw)
    (complete_nword hR b hbw) (complete_ndivmod hR a b (by omega))
    (complete_natlit hR a) (complete_natlit hR b) (complete_natlit hR (a / b))

theorem complete_litLength (bs : List UInt8) (hwf : WellFormed T.sig (.lit bs) = true) :
    FODerivable R (jThm (encTerm T.sig (litLengthStatement bs))) := by
  unfold litLengthStatement Term.natLit
  rw [encTerm_litEquation hb .litLength _ _ (by simp [depth_lit]) (by simp [hasFvar_lit])]
  exact intro_rLitLength (theoremRule_in hR (by simp [theoremRules]))
    (isData_encBytes bs) (isData_encNat bs.length) (isData_encBytes (natLiteral bs.length))
    (complete_bytes_literal_wf hR T.sig bs hwf) (complete_len_bytes hR bs)
    (complete_natlit hR bs.length)

theorem complete_litGet (bs : List UInt8) (i : Nat)
    (hwf : WellFormed T.sig (.lit bs) = true) (hi : i < bs.length) :
    FODerivable R (jThm (encTerm T.sig (litGetStatement bs i))) := by
  let b := bs[i]
  have hget : bs[i]? = some b := List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
  have hD : bs.getD i 0 = b := by
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_some]
  unfold litGetStatement Term.natLit
  rw [hD, encTerm_litEquation hb .litGet _ _ (by simp [depth_lit]) (by simp [hasFvar_lit])]
  exact intro_rLitGet (theoremRule_in hR (by simp [theoremRules]))
    (isData_encBytes bs) (isData_encNat i) (isData_encNat b.toNat)
    (isData_encBytes (natLiteral i)) (isData_encBytes (natLiteral b.toNat))
    (complete_bytes_literal_wf hR T.sig bs hwf) (complete_nth_bytes hR bs i b hget)
    (complete_natlit hR i) (complete_natlit hR b.toNat)

end LiteralTheorems

end Mettapedia.Languages.VibeITP.Presentation
