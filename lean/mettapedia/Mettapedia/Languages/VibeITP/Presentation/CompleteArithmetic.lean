import Mettapedia.Languages.VibeITP.Presentation.RuleShapes

/-!
# Constructive arithmetic witnesses for the Vibe-ITP presentation

The first-order rules derive the canonical binary representation of every
arithmetic result.  The arithmetic witnesses are unbounded naturals; the word
bound is imposed only by the `VNWord` judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

private theorem arithmeticRule_in {R : List FORule} (hR : kernelRules ⊆ R)
    {r : FORule} (hr : r ∈ arithmeticRules) : r ∈ R :=
  hR (by simp [kernelRules, hr])

private theorem positive_mul {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  simpa using Nat.mul_le_mul ha hb

theorem complete_psucc {R : List FORule} (hR : kernelRules ⊆ R)
    (a : Nat) (ha : 1 ≤ a) :
    FODerivable R (jPSucc (encPos a) (encPos (a + 1))) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
      by_cases ha1 : a = 1
      · subst a
        exact intro_rPsucc1 (arithmeticRule_in hR (by simp [arithmeticRules, psuccRules]))
      · obtain ⟨p, hp | hp⟩ := nat_even_or_odd a
        · subst a
          have hpos : 1 ≤ p := by omega
          rw [encPos_even p hpos, encPos_odd p hpos]
          exact intro_rPsuccO (arithmeticRule_in hR (by simp [arithmeticRules, psuccRules]))
            (isData_encPos p)
        · subst a
          have hpos : 1 ≤ p := by omega
          rw [encPos_odd p hpos, show 2 * p + 1 + 1 = 2 * (p + 1) by omega,
            encPos_even (p + 1) (by omega)]
          exact intro_rPsuccI (arithmeticRule_in hR (by simp [arithmeticRules, psuccRules]))
            (isData_encPos p) (isData_encPos (p + 1)) (ih p (by omega) hpos)

private theorem complete_padd_pair {R : List FORule} (hR : kernelRules ⊆ R)
    (a : Nat) (ha : 1 ≤ a) : ∀ b : Nat, 1 ≤ b →
    FODerivable R (jPAdd (encPos a) (encPos b) (encPos (a + b))) ∧
      FODerivable R (jPAddC (encPos a) (encPos b) (encPos (a + b + 1))) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
      intro b hb
      by_cases ha1 : a = 1
      · subst a
        constructor
        · rw [encPos_one, show 1 + b = b + 1 by omega]
          exact intro_rPadd1l (arithmeticRule_in hR (by simp [arithmeticRules, paddRules]))
            (isData_encPos b) (isData_encPos (b + 1)) (complete_psucc hR b hb)
        · by_cases hb1 : b = 1
          · subst b
            exact intro_rPaddc11
              (arithmeticRule_in hR (by simp [arithmeticRules, paddcRules]))
          · obtain ⟨q, hq | hq⟩ := nat_even_or_odd b
            · subst b
              have hqpos : 1 ≤ q := by omega
              rw [encPos_one, encPos_even q hqpos,
                show 1 + 2 * q + 1 = 2 * (q + 1) by omega,
                encPos_even (q + 1) (by omega)]
              exact intro_rPaddc1o
                (arithmeticRule_in hR (by simp [arithmeticRules, paddcRules]))
                (isData_encPos q) (isData_encPos (q + 1)) (complete_psucc hR q hqpos)
            · subst b
              have hqpos : 1 ≤ q := by omega
              rw [encPos_one, encPos_odd q hqpos,
                show 1 + (2 * q + 1) + 1 = 2 * (q + 1) + 1 by omega,
                encPos_odd (q + 1) (by omega)]
              exact intro_rPaddc1i
                (arithmeticRule_in hR (by simp [arithmeticRules, paddcRules]))
                (isData_encPos q) (isData_encPos (q + 1)) (complete_psucc hR q hqpos)
      · by_cases hb1 : b = 1
        · subst b
          constructor
          · rw [encPos_one]
            exact intro_rPadd1r (arithmeticRule_in hR (by simp [arithmeticRules, paddRules]))
              (isData_encPos a) (isData_encPos (a + 1)) (complete_psucc hR a ha)
          · obtain ⟨p, hp | hp⟩ := nat_even_or_odd a
            · subst a
              have hppos : 1 ≤ p := by omega
              rw [encPos_one, encPos_even p hppos,
                show 2 * p + 1 + 1 = 2 * (p + 1) by omega,
                encPos_even (p + 1) (by omega)]
              exact intro_rPaddcO1
                (arithmeticRule_in hR (by simp [arithmeticRules, paddcRules]))
                (isData_encPos p) (isData_encPos (p + 1)) (complete_psucc hR p hppos)
            · subst a
              have hppos : 1 ≤ p := by omega
              rw [encPos_one, encPos_odd p hppos,
                show 2 * p + 1 + 1 + 1 = 2 * (p + 1) + 1 by omega,
                encPos_odd (p + 1) (by omega)]
              exact intro_rPaddcI1
                (arithmeticRule_in hR (by simp [arithmeticRules, paddcRules]))
                (isData_encPos p) (isData_encPos (p + 1)) (complete_psucc hR p hppos)
        · obtain ⟨p, hp | hp⟩ := nat_even_or_odd a <;>
            obtain ⟨q, hq | hq⟩ := nat_even_or_odd b <;> subst a <;> subst b
          · have hppos : 1 ≤ p := by omega
            have hqpos : 1 ≤ q := by omega
            obtain ⟨hadd, _⟩ := ih p (by omega) hppos q hqpos
            rw [encPos_even p hppos, encPos_even q hqpos,
              show 2 * p + 2 * q = 2 * (p + q) by omega,
              encPos_even (p + q) (by omega), encPos_odd (p + q) (by omega)]
            exact ⟨intro_rPaddOo
              (arithmeticRule_in hR (by simp [arithmeticRules, paddRules]))
              (isData_encPos p) (isData_encPos q) (isData_encPos (p + q)) hadd,
              intro_rPaddcOo
              (arithmeticRule_in hR (by simp [arithmeticRules, paddcRules]))
              (isData_encPos p) (isData_encPos q) (isData_encPos (p + q)) hadd⟩
          · have hppos : 1 ≤ p := by omega
            have hqpos : 1 ≤ q := by omega
            obtain ⟨hadd, hcarry⟩ := ih p (by omega) hppos q hqpos
            rw [encPos_even p hppos, encPos_odd q hqpos,
              show 2 * p + (2 * q + 1) = 2 * (p + q) + 1 by omega,
              show 2 * (p + q) + 1 + 1 = 2 * (p + q + 1) by omega,
              encPos_odd (p + q) (by omega), encPos_even (p + q + 1) (by omega)]
            exact ⟨intro_rPaddOi
              (arithmeticRule_in hR (by simp [arithmeticRules, paddRules]))
              (isData_encPos p) (isData_encPos q) (isData_encPos (p + q)) hadd,
              intro_rPaddcOi
              (arithmeticRule_in hR (by simp [arithmeticRules, paddcRules]))
              (isData_encPos p) (isData_encPos q) (isData_encPos (p + q + 1)) hcarry⟩
          · have hppos : 1 ≤ p := by omega
            have hqpos : 1 ≤ q := by omega
            obtain ⟨hadd, hcarry⟩ := ih p (by omega) hppos q hqpos
            rw [encPos_odd p hppos, encPos_even q hqpos,
              show (2 * p + 1) + 2 * q = 2 * (p + q) + 1 by omega,
              show 2 * (p + q) + 1 + 1 = 2 * (p + q + 1) by omega,
              encPos_odd (p + q) (by omega), encPos_even (p + q + 1) (by omega)]
            exact ⟨intro_rPaddIo
              (arithmeticRule_in hR (by simp [arithmeticRules, paddRules]))
              (isData_encPos p) (isData_encPos q) (isData_encPos (p + q)) hadd,
              intro_rPaddcIo
              (arithmeticRule_in hR (by simp [arithmeticRules, paddcRules]))
              (isData_encPos p) (isData_encPos q) (isData_encPos (p + q + 1)) hcarry⟩
          · have hppos : 1 ≤ p := by omega
            have hqpos : 1 ≤ q := by omega
            obtain ⟨_, hcarry⟩ := ih p (by omega) hppos q hqpos
            rw [encPos_odd p hppos, encPos_odd q hqpos,
              show (2 * p + 1) + (2 * q + 1) = 2 * (p + q + 1) by omega,
              encPos_even (p + q + 1) (by omega), encPos_odd (p + q + 1) (by omega)]
            exact ⟨intro_rPaddIi
              (arithmeticRule_in hR (by simp [arithmeticRules, paddRules]))
              (isData_encPos p) (isData_encPos q) (isData_encPos (p + q + 1)) hcarry,
              intro_rPaddcIi
              (arithmeticRule_in hR (by simp [arithmeticRules, paddcRules]))
              (isData_encPos p) (isData_encPos q) (isData_encPos (p + q + 1)) hcarry⟩

theorem complete_padd {R : List FORule} (hR : kernelRules ⊆ R)
    (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    FODerivable R (jPAdd (encPos a) (encPos b) (encPos (a + b))) :=
  (complete_padd_pair hR a ha b hb).1

theorem complete_paddc {R : List FORule} (hR : kernelRules ⊆ R)
    (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    FODerivable R (jPAddC (encPos a) (encPos b) (encPos (a + b + 1))) :=
  (complete_padd_pair hR a ha b hb).2

theorem complete_nadd {R : List FORule} (hR : kernelRules ⊆ R)
    (a b : Nat) : FODerivable R (jNAdd (encNat a) (encNat b) (encNat (a + b))) := by
  by_cases ha0 : a = 0
  · subst a
    simp only [encNat_zero, Nat.zero_add]
    exact intro_rNadd0l (arithmeticRule_in hR (by simp [arithmeticRules, naddRules]))
      (isData_encNat b)
  · have ha : 1 ≤ a := by omega
    by_cases hb0 : b = 0
    · subst b
      simp only [encNat_zero, Nat.add_zero, encNat_pos a ha]
      exact intro_rNadd0r (arithmeticRule_in hR (by simp [arithmeticRules, naddRules]))
        (isData_encPos a)
    · have hb : 1 ≤ b := by omega
      rw [encNat_pos a ha, encNat_pos b hb, encNat_pos (a + b) (by omega)]
      exact intro_rNaddPp (arithmeticRule_in hR (by simp [arithmeticRules, naddRules]))
        (isData_encPos a) (isData_encPos b) (isData_encPos (a + b))
        (complete_padd hR a b ha hb)

theorem complete_nlt {R : List FORule} (hR : kernelRules ⊆ R)
    (a b : Nat) (h : a < b) : FODerivable R (jNLt (encNat a) (encNat b)) := by
  have hadd := complete_nadd hR a (b - a)
  rw [show a + (b - a) = b by omega, encNat_pos (b - a) (by omega)] at hadd
  exact intro_rNlt (arithmeticRule_in hR (by simp [arithmeticRules, orderRules]))
    (isData_encNat a) (isData_encPos (b - a)) (isData_encNat b) hadd

theorem complete_nle {R : List FORule} (hR : kernelRules ⊆ R)
    (a b : Nat) (h : a ≤ b) : FODerivable R (jNLe (encNat a) (encNat b)) := by
  have hadd := complete_nadd hR a (b - a)
  rw [show a + (b - a) = b by omega] at hadd
  exact intro_rNle (arithmeticRule_in hR (by simp [arithmeticRules, orderRules]))
    (isData_encNat a) (isData_encNat (b - a)) (isData_encNat b) hadd

theorem complete_nmonus {R : List FORule} (hR : kernelRules ⊆ R)
    (a b : Nat) : FODerivable R (jNMonus (encNat a) (encNat b) (encNat (a - b))) := by
  by_cases h : a ≤ b
  · rw [show a - b = 0 by omega, encNat_zero]
    exact intro_rNmonusLe (arithmeticRule_in hR (by simp [arithmeticRules, orderRules]))
      (isData_encNat a) (isData_encNat b) (complete_nle hR a b h)
  · have hadd := complete_nadd hR b (a - b)
    rw [show b + (a - b) = a by omega, encNat_pos (a - b) (by omega)] at hadd
    rw [encNat_pos (a - b) (by omega)]
    exact intro_rNmonusGt (arithmeticRule_in hR (by simp [arithmeticRules, orderRules]))
      (isData_encNat a) (isData_encNat b) (isData_encPos (a - b)) hadd

theorem complete_nmax {R : List FORule} (hR : kernelRules ⊆ R)
    (a b : Nat) : FODerivable R (jNMax (encNat a) (encNat b) (encNat (max a b))) := by
  by_cases h : a ≤ b
  · rw [Nat.max_eq_right h]
    exact intro_rNmaxLe (arithmeticRule_in hR (by simp [arithmeticRules, orderRules]))
      (isData_encNat a) (isData_encNat b) (complete_nle hR a b h)
  · rw [Nat.max_eq_left (by omega)]
    exact intro_rNmaxGt (arithmeticRule_in hR (by simp [arithmeticRules, orderRules]))
      (isData_encNat a) (isData_encNat b) (complete_nlt hR b a (by omega))

theorem complete_bor {R : List FORule} (hR : kernelRules ⊆ R)
    (x y : Bool) : FODerivable R (jBOr (encBool x) (encBool y) (encBool (x || y))) := by
  cases x <;> cases y
  · exact intro_rBorFf (arithmeticRule_in hR (by simp [arithmeticRules, orderRules]))
  · exact intro_rBorFt (arithmeticRule_in hR (by simp [arithmeticRules, orderRules]))
  · exact intro_rBorTf (arithmeticRule_in hR (by simp [arithmeticRules, orderRules]))
  · exact intro_rBorTt (arithmeticRule_in hR (by simp [arithmeticRules, orderRules]))

theorem complete_pbits {R : List FORule} (hR : kernelRules ⊆ R)
    (n k : Nat) (hn : 1 ≤ n) (h : n < 2 ^ k) :
    FODerivable R (jPBits (encPos n) (encUnary k)) := by
  induction k generalizing n with
  | zero => simp only [Nat.pow_zero] at h; omega
  | succ k ih =>
      by_cases hn1 : n = 1
      · subst n
        exact intro_rPbits1 (arithmeticRule_in hR (by simp [arithmeticRules, wordRules]))
          (isData_encUnary k)
      · rw [Nat.pow_succ] at h
        obtain ⟨p, hp | hp⟩ := nat_even_or_odd n
        · subst n
          have hppos : 1 ≤ p := by omega
          rw [encPos_even p hppos]
          exact intro_rPbitsO (arithmeticRule_in hR (by simp [arithmeticRules, wordRules]))
            (isData_encPos p) (isData_encUnary k) (ih p hppos (by omega))
        · subst n
          have hppos : 1 ≤ p := by omega
          rw [encPos_odd p hppos]
          exact intro_rPbitsI (arithmeticRule_in hR (by simp [arithmeticRules, wordRules]))
            (isData_encPos p) (isData_encUnary k) (ih p hppos (by omega))

theorem complete_nword {R : List FORule} (hR : kernelRules ⊆ R)
    (a : Nat) (h : a < wordBound) : FODerivable R (jNWord (encNat a)) := by
  by_cases ha0 : a = 0
  · subst a
    exact intro_rNword0 (arithmeticRule_in hR (by simp [arithmeticRules, wordRules]))
  · have ha : 1 ≤ a := by omega
    rw [encNat_pos a ha]
    exact intro_rNwordP (arithmeticRule_in hR (by simp [arithmeticRules, wordRules]))
      (isData_encPos a) (complete_pbits hR a 64 ha h)

theorem complete_pmul {R : List FORule} (hR : kernelRules ⊆ R)
    (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    FODerivable R (jPMul (encPos a) (encPos b) (encPos (a * b))) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
      by_cases ha1 : a = 1
      · subst a
        simp only [encPos_one, Nat.one_mul]
        exact intro_rPmul1 (arithmeticRule_in hR (by simp [arithmeticRules, mulRules]))
          (isData_encPos b)
      · obtain ⟨p, hp | hp⟩ := nat_even_or_odd a
        · subst a
          have hppos : 1 ≤ p := by omega
          have hpmul : 1 ≤ p * b := positive_mul hppos hb
          rw [encPos_even p hppos, Nat.mul_assoc, encPos_even (p * b) hpmul]
          exact intro_rPmulO (arithmeticRule_in hR (by simp [arithmeticRules, mulRules]))
            (isData_encPos p) (isData_encPos b) (isData_encPos (p * b))
            (ih p (by omega) hppos)
        · subst a
          have hppos : 1 ≤ p := by omega
          have hp2 : 1 ≤ 2 * (p * b) := positive_mul (by omega) (positive_mul hppos hb)
          have hadd := complete_padd hR (2 * (p * b)) b hp2 hb
          rw [encPos_even (p * b) (positive_mul hppos hb)] at hadd
          rw [encPos_odd p hppos, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
          exact intro_rPmulI (arithmeticRule_in hR (by simp [arithmeticRules, mulRules]))
            (isData_encPos p) (isData_encPos b) (isData_encPos (p * b))
            (isData_encPos (2 * (p * b) + b)) (ih p (by omega) hppos) hadd

theorem complete_nmul {R : List FORule} (hR : kernelRules ⊆ R)
    (a b : Nat) : FODerivable R (jNMul (encNat a) (encNat b) (encNat (a * b))) := by
  by_cases ha0 : a = 0
  · subst a
    simp only [encNat_zero, Nat.zero_mul]
    exact intro_rNmul0l (arithmeticRule_in hR (by simp [arithmeticRules, mulRules]))
      (isData_encNat b)
  · have ha : 1 ≤ a := by omega
    by_cases hb0 : b = 0
    · subst b
      simp only [encNat_zero, Nat.mul_zero, encNat_pos a ha]
      exact intro_rNmul0r (arithmeticRule_in hR (by simp [arithmeticRules, mulRules]))
        (isData_encPos a)
    · have hb : 1 ≤ b := by omega
      rw [encNat_pos a ha, encNat_pos b hb, encNat_pos (a * b) (positive_mul ha hb)]
      exact intro_rNmulPp (arithmeticRule_in hR (by simp [arithmeticRules, mulRules]))
        (isData_encPos a) (isData_encPos b) (isData_encPos (a * b))
        (complete_pmul hR a b ha hb)

theorem complete_ndivmod {R : List FORule} (hR : kernelRules ⊆ R)
    (a b : Nat) (hb : 0 < b) :
    FODerivable R (jNDivMod (encNat a) (encNat b) (encNat (a / b)) (encNat (a % b))) := by
  have hadd := complete_nadd hR (b * (a / b)) (a % b)
  rw [show b * (a / b) + a % b = a by
    have h := Nat.mod_add_div a b
    omega] at hadd
  exact intro_rNdivmod (arithmeticRule_in hR (by simp [arithmeticRules, mulRules]))
    (isData_encNat a) (isData_encNat b) (isData_encNat (a / b)) (isData_encNat (a % b))
    (isData_encNat (b * (a / b))) (complete_nmul hR b (a / b)) hadd
    (complete_nlt hR (a % b) b (Nat.mod_lt a hb))

theorem complete_nmod64 {R : List FORule} (hR : kernelRules ⊆ R)
    (a : Nat) : FODerivable R (jNMod64 (encNat a) (encNat (a % wordBound))) := by
  exact intro_rNmod64 (arithmeticRule_in hR (by simp [arithmeticRules, mulRules]))
    (isData_encNat a) (isData_encNat (a / wordBound)) (isData_encNat (a % wordBound))
    (complete_ndivmod hR a wordBound (by simp [wordBound]))

end Mettapedia.Languages.VibeITP.Presentation
