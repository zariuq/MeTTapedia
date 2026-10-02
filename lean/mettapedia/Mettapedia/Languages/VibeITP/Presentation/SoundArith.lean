import Mettapedia.Languages.VibeITP.Presentation.Meaning
import Mettapedia.Languages.VibeITP.Presentation.RuleShapes

/-!
# Vibe-ITP presentation: soundness of the arithmetic and list rules

Each lemma states that one rule preserves `Meaning`: if its premises hold,
so does its conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

variable (T : Theory)

/-! ## Successor -/

theorem ms_rPsucc1 : Meaning T (jPSucc cP1 (cPO cP1)) := by
  simp only [M_psucc, PSuccM, decPos_PO, decPos_P1, Option.map_some, Option.some.injEq]
  exact ⟨fun x hx => by subst hx; rfl, fun y hy => ⟨1, rfl, by omega⟩⟩

theorem ms_rPsuccO : ∀ p : Pattern, Meaning T (jPSucc (cPO p) (cPI p)) := by
  intro p
  simp only [M_psucc, PSuccM, decPos_PO, decPos_PI, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩; exact ⟨y, hy, by omega⟩
  · rintro z ⟨y, hy, rfl⟩; exact ⟨2 * y, ⟨y, hy, rfl⟩, by omega⟩

theorem ms_rPsuccI : ∀ p q : Pattern,
    Meaning T (jPSucc p q) → Meaning T (jPSucc (cPI p) (cPO q)) := by
  intro p q h
  simp only [M_psucc, PSuccM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_psucc, PSuccM, decPos_PO, decPos_PI, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩; exact ⟨y + 1, hf y hy, by omega⟩
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hb w hw
    exact ⟨2 * y + 1, ⟨y, hy, rfl⟩, by omega⟩

/-! ## Addition of positive numerals -/

theorem ms_rPadd1l : ∀ q r : Pattern, Meaning T (jPSucc q r) → Meaning T (jPAdd cP1 q r) := by
  intro q r h
  simp only [M_psucc, PSuccM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_padd, PAddM, decPos_P1, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rintro x y rfl hy; rw [hf y hy]; congr 1; omega
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hb z hz
    exact ⟨1, y, rfl, hy, by omega⟩

theorem ms_rPadd1r : ∀ p r : Pattern, Meaning T (jPSucc p r) → Meaning T (jPAdd p cP1 r) := by
  intro p r h
  simp only [M_psucc, PSuccM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_padd, PAddM, decPos_P1, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rintro x y hx rfl; exact hf x hx
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hb z hz
    exact ⟨x, 1, hx, rfl, rfl⟩

theorem ms_rPaddOo : ∀ p q r : Pattern,
    Meaning T (jPAdd p q r) → Meaning T (jPAdd (cPO p) (cPO q) (cPO r)) := by
  intro p q r h
  simp only [M_padd, PAddM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_padd, PAddM, decPos_PO, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ ⟨b, hb', rfl⟩; exact ⟨a + b, hf a b ha hb', by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨a, b, ha, hb', rfl⟩ := hb c hc
    exact ⟨2 * a, 2 * b, ⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, by omega⟩

theorem ms_rPaddOi : ∀ p q r : Pattern,
    Meaning T (jPAdd p q r) → Meaning T (jPAdd (cPO p) (cPI q) (cPI r)) := by
  intro p q r h
  simp only [M_padd, PAddM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_padd, PAddM, decPos_PO, decPos_PI, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ ⟨b, hb', rfl⟩; exact ⟨a + b, hf a b ha hb', by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨a, b, ha, hb', rfl⟩ := hb c hc
    exact ⟨2 * a, 2 * b + 1, ⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, by omega⟩

theorem ms_rPaddIo : ∀ p q r : Pattern,
    Meaning T (jPAdd p q r) → Meaning T (jPAdd (cPI p) (cPO q) (cPI r)) := by
  intro p q r h
  simp only [M_padd, PAddM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_padd, PAddM, decPos_PO, decPos_PI, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ ⟨b, hb', rfl⟩; exact ⟨a + b, hf a b ha hb', by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨a, b, ha, hb', rfl⟩ := hb c hc
    exact ⟨2 * a + 1, 2 * b, ⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, by omega⟩

theorem ms_rPaddIi : ∀ p q r : Pattern,
    Meaning T (jPAddC p q r) → Meaning T (jPAdd (cPI p) (cPI q) (cPO r)) := by
  intro p q r h
  simp only [M_paddc, PAddCM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_padd, PAddM, decPos_PO, decPos_PI, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ ⟨b, hb', rfl⟩; exact ⟨a + b + 1, hf a b ha hb', by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨a, b, ha, hb', rfl⟩ := hb c hc
    exact ⟨2 * a + 1, 2 * b + 1, ⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, by omega⟩

/-! ## Addition with carry -/

theorem ms_rPaddc11 : Meaning T (jPAddC cP1 cP1 (cPI cP1)) := by
  simp only [M_paddc, PAddCM, decPos_PI, decPos_P1, Option.map_some, Option.some.injEq]
  exact ⟨fun x y hx hy => by subst hx hy; rfl, fun z hz => ⟨1, 1, rfl, rfl, by omega⟩⟩

theorem ms_rPaddc1o : ∀ q r : Pattern,
    Meaning T (jPSucc q r) → Meaning T (jPAddC cP1 (cPO q) (cPO r)) := by
  intro q r h
  simp only [M_psucc, PSuccM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_paddc, PAddCM, decPos_PO, decPos_P1, Option.map_eq_some_iff, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rintro x y rfl ⟨b, hb', rfl⟩; exact ⟨b + 1, hf b hb', by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨b, hb', rfl⟩ := hb c hc
    exact ⟨1, 2 * b, rfl, ⟨b, hb', rfl⟩, by omega⟩

theorem ms_rPaddc1i : ∀ q r : Pattern,
    Meaning T (jPSucc q r) → Meaning T (jPAddC cP1 (cPI q) (cPI r)) := by
  intro q r h
  simp only [M_psucc, PSuccM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_paddc, PAddCM, decPos_PI, decPos_P1, Option.map_eq_some_iff, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rintro x y rfl ⟨b, hb', rfl⟩; exact ⟨b + 1, hf b hb', by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨b, hb', rfl⟩ := hb c hc
    exact ⟨1, 2 * b + 1, rfl, ⟨b, hb', rfl⟩, by omega⟩

theorem ms_rPaddcO1 : ∀ p r : Pattern,
    Meaning T (jPSucc p r) → Meaning T (jPAddC (cPO p) cP1 (cPO r)) := by
  intro p r h
  simp only [M_psucc, PSuccM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_paddc, PAddCM, decPos_PO, decPos_P1, Option.map_eq_some_iff, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ rfl; exact ⟨a + 1, hf a ha, by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hb c hc
    exact ⟨2 * a, 1, ⟨a, ha, rfl⟩, rfl, by omega⟩

theorem ms_rPaddcI1 : ∀ p r : Pattern,
    Meaning T (jPSucc p r) → Meaning T (jPAddC (cPI p) cP1 (cPI r)) := by
  intro p r h
  simp only [M_psucc, PSuccM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_paddc, PAddCM, decPos_PI, decPos_P1, Option.map_eq_some_iff, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ rfl; exact ⟨a + 1, hf a ha, by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hb c hc
    exact ⟨2 * a + 1, 1, ⟨a, ha, rfl⟩, rfl, by omega⟩

theorem ms_rPaddcOo : ∀ p q r : Pattern,
    Meaning T (jPAdd p q r) → Meaning T (jPAddC (cPO p) (cPO q) (cPI r)) := by
  intro p q r h
  simp only [M_padd, PAddM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_paddc, PAddCM, decPos_PO, decPos_PI, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ ⟨b, hb', rfl⟩; exact ⟨a + b, hf a b ha hb', by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨a, b, ha, hb', rfl⟩ := hb c hc
    exact ⟨2 * a, 2 * b, ⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, by omega⟩

theorem ms_rPaddcOi : ∀ p q r : Pattern,
    Meaning T (jPAddC p q r) → Meaning T (jPAddC (cPO p) (cPI q) (cPO r)) := by
  intro p q r h
  simp only [M_paddc, PAddCM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_paddc, PAddCM, decPos_PO, decPos_PI, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ ⟨b, hb', rfl⟩; exact ⟨a + b + 1, hf a b ha hb', by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨a, b, ha, hb', rfl⟩ := hb c hc
    exact ⟨2 * a, 2 * b + 1, ⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, by omega⟩

theorem ms_rPaddcIo : ∀ p q r : Pattern,
    Meaning T (jPAddC p q r) → Meaning T (jPAddC (cPI p) (cPO q) (cPO r)) := by
  intro p q r h
  simp only [M_paddc, PAddCM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_paddc, PAddCM, decPos_PO, decPos_PI, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ ⟨b, hb', rfl⟩; exact ⟨a + b + 1, hf a b ha hb', by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨a, b, ha, hb', rfl⟩ := hb c hc
    exact ⟨2 * a + 1, 2 * b, ⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, by omega⟩

theorem ms_rPaddcIi : ∀ p q r : Pattern,
    Meaning T (jPAddC p q r) → Meaning T (jPAddC (cPI p) (cPI q) (cPI r)) := by
  intro p q r h
  simp only [M_paddc, PAddCM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_paddc, PAddCM, decPos_PI, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ ⟨b, hb', rfl⟩; exact ⟨a + b + 1, hf a b ha hb', by omega⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨a, b, ha, hb', rfl⟩ := hb c hc
    exact ⟨2 * a + 1, 2 * b + 1, ⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, by omega⟩

/-! ## Addition of natural numerals -/

theorem ms_rNadd0l : ∀ b : Pattern, Meaning T (jNAdd cN0 b b) := by
  intro b
  simp only [M_nadd, NAddM, decNat_N0, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rintro x y rfl hy; rw [hy]; simp
  · intro z hz; exact ⟨0, z, rfl, hz, by omega⟩

theorem ms_rNadd0r : ∀ p : Pattern, Meaning T (jNAdd (cNPos p) cN0 (cNPos p)) := by
  intro p
  simp only [M_nadd, NAddM, decNat_N0, decNat_NPos, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rintro x y hx rfl; simp [hx]
  · intro z hz; exact ⟨z, 0, hz, rfl, by omega⟩

theorem ms_rNaddPp : ∀ p q r : Pattern,
    Meaning T (jPAdd p q r) → Meaning T (jNAdd (cNPos p) (cNPos q) (cNPos r)) := by
  intro p q r h
  simp only [M_padd, PAddM] at h
  simpa only [M_nadd, NAddM, decNat_NPos] using h

/-! ## Order, truncated subtraction, maximum, disjunction -/

theorem ms_rNlt : ∀ a p b : Pattern, Meaning T (jNAdd a (cNPos p) b) → Meaning T (jNLt a b) := by
  intro a p b h
  simp only [M_nadd, NAddM] at h
  simp only [M_nlt, NLtM]
  intro y hy
  obtain ⟨x, w, hx, hw, rfl⟩ := h.2 y hy
  have := decPos_pos p w (by simpa using hw)
  exact ⟨x, hx, by omega⟩

theorem ms_rNle : ∀ a c b : Pattern, Meaning T (jNAdd a c b) → Meaning T (jNLe a b) := by
  intro a c b h
  simp only [M_nadd, NAddM] at h
  simp only [M_nle, NLeM]
  intro y hy
  obtain ⟨x, w, hx, _, rfl⟩ := h.2 y hy
  exact ⟨x, hx, by omega⟩

theorem ms_rNmonusLe : ∀ a b : Pattern, Meaning T (jNLe a b) → Meaning T (jNMonus a b cN0) := by
  intro a b h
  simp only [M_nle, NLeM] at h
  simp only [M_nmonus, NMonusM, decNat_N0, Option.some.injEq]
  intro x y hx hy
  obtain ⟨x', hx', hle⟩ := h y hy
  rw [hx] at hx'
  cases hx'
  omega

theorem ms_rNmonusGt : ∀ a b p : Pattern,
    Meaning T (jNAdd b (cNPos p) a) → Meaning T (jNMonus a b (cNPos p)) := by
  intro a b p h
  simp only [M_nadd, NAddM] at h
  simp only [M_nmonus, NMonusM, decNat_NPos]
  intro x y hx hy
  obtain ⟨y', w, hy', hw, rfl⟩ := h.2 x hx
  rw [hy] at hy'
  cases hy'
  simp only [decNat_NPos] at hw
  rw [hw]; congr 1; omega

theorem ms_rNmaxLe : ∀ a b : Pattern, Meaning T (jNLe a b) → Meaning T (jNMax a b b) := by
  intro a b h
  simp only [M_nle, NLeM] at h
  simp only [M_nmax, NMaxM]
  intro x y hx hy
  obtain ⟨x', hx', hle⟩ := h y hy
  rw [hx] at hx'
  cases hx'
  rw [hy]; congr 1; omega

theorem ms_rNmaxGt : ∀ a b : Pattern, Meaning T (jNLt b a) → Meaning T (jNMax a b a) := by
  intro a b h
  simp only [M_nlt, NLtM] at h
  simp only [M_nmax, NMaxM]
  intro x y hx hy
  obtain ⟨y', hy', hlt⟩ := h x hx
  rw [hy] at hy'
  cases hy'
  rw [hx]; congr 1; omega

theorem ms_rBorFf : Meaning T (jBOr cFalse cFalse cFalse) :=
  ⟨false, false, rfl, rfl, rfl⟩
theorem ms_rBorFt : Meaning T (jBOr cFalse cTrue cTrue) :=
  ⟨false, true, rfl, rfl, rfl⟩
theorem ms_rBorTf : Meaning T (jBOr cTrue cFalse cTrue) :=
  ⟨true, false, rfl, rfl, rfl⟩
theorem ms_rBorTt : Meaning T (jBOr cTrue cTrue cTrue) :=
  ⟨true, true, rfl, rfl, rfl⟩

/-! ## Bit length and machine words -/

theorem ms_rPbits1 : ∀ u : Pattern, Meaning T (jPBits cP1 (cUS u)) := by
  intro u
  simp only [M_pbits, PBitsM, decPos_P1, decUnary_US, Option.map_eq_some_iff]
  refine ⟨1, rfl, ?_⟩
  rintro k ⟨j, _, rfl⟩
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [Nat.pow_succ]; omega

theorem ms_rPbitsO : ∀ p u : Pattern, Meaning T (jPBits p u) → Meaning T (jPBits (cPO p) (cUS u)) := by
  intro p u h
  simp only [M_pbits, PBitsM] at h
  obtain ⟨x, hx, hlt⟩ := h
  simp only [M_pbits, PBitsM, decPos_PO, decUnary_US, Option.map_eq_some_iff]
  refine ⟨2 * x, ⟨x, hx, rfl⟩, ?_⟩
  rintro k ⟨j, hj, rfl⟩
  have := hlt j hj
  rw [Nat.pow_succ]; omega

theorem ms_rPbitsI : ∀ p u : Pattern, Meaning T (jPBits p u) → Meaning T (jPBits (cPI p) (cUS u)) := by
  intro p u h
  simp only [M_pbits, PBitsM] at h
  obtain ⟨x, hx, hlt⟩ := h
  simp only [M_pbits, PBitsM, decPos_PI, decUnary_US, Option.map_eq_some_iff]
  refine ⟨2 * x + 1, ⟨x, hx, rfl⟩, ?_⟩
  rintro k ⟨j, hj, rfl⟩
  have := hlt j hj
  rw [Nat.pow_succ]; omega

theorem ms_rNword0 : Meaning T (jNWord cN0) :=
  ⟨0, rfl, by simp [wordBound]⟩

theorem ms_rNwordP : ∀ p : Pattern, Meaning T (jPBits p patWordBits) → Meaning T (jNWord (cNPos p)) := by
  intro p h
  simp only [M_pbits, PBitsM] at h
  obtain ⟨x, hx, hlt⟩ := h
  exact ⟨x, by simpa using hx, by simpa [wordBound] using hlt 64 (decUnary_encUnary 64)⟩

/-! ## Multiplication, division, reduction modulo the word -/

theorem ms_rPmul1 : ∀ q : Pattern, Meaning T (jPMul cP1 q q) := by
  intro q
  simp only [M_pmul, PMulM, decPos_P1, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rintro x y rfl hy; rw [hy]; simp
  · intro z hz; exact ⟨1, z, rfl, hz, by omega⟩

theorem ms_rPmulO : ∀ p q r : Pattern,
    Meaning T (jPMul p q r) → Meaning T (jPMul (cPO p) q (cPO r)) := by
  intro p q r h
  simp only [M_pmul, PMulM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_pmul, PMulM, decPos_PO, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ hy
    exact ⟨a * y, hf a y ha hy, by rw [Nat.mul_assoc]⟩
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨a, b, ha, hb', rfl⟩ := hb c hc
    exact ⟨2 * a, b, ⟨a, ha, rfl⟩, hb', by rw [Nat.mul_assoc]⟩

theorem ms_rPmulI : ∀ p q r s : Pattern,
    Meaning T (jPMul p q r) → Meaning T (jPAdd (cPO r) q s) →
      Meaning T (jPMul (cPI p) q s) := by
  intro p q r s h1 h2
  simp only [M_pmul, PMulM] at h1
  simp only [M_padd, PAddM] at h2
  obtain ⟨hf1, hb1⟩ := h1
  obtain ⟨hf2, hb2⟩ := h2
  simp only [M_pmul, PMulM, decPos_PI, Option.map_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, ha, rfl⟩ hy
    have hr := hf1 a y ha hy
    have hs := hf2 (2 * (a * y)) y (by simp [hr]) hy
    rw [hs]; congr 1; rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  · intro z hz
    obtain ⟨w, y, hw, hy, rfl⟩ := hb2 z hz
    simp only [decPos_PO, Option.map_eq_some_iff] at hw
    obtain ⟨c, hc, rfl⟩ := hw
    obtain ⟨a, y', ha, hy', rfl⟩ := hb1 c hc
    rw [hy] at hy'
    cases hy'
    exact ⟨2 * a + 1, y, ⟨a, ha, rfl⟩, hy, by rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]⟩

theorem ms_rNmul0l : ∀ b : Pattern, Meaning T (jNMul cN0 b cN0) := by
  intro b
  simp only [M_nmul, NMulM, decNat_N0, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rintro x y rfl _; simp
  · rintro z x _ rfl; exact Or.inl rfl

theorem ms_rNmul0r : ∀ p : Pattern, Meaning T (jNMul (cNPos p) cN0 cN0) := by
  intro p
  simp only [M_nmul, NMulM, decNat_N0, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rintro x y _ rfl; simp
  · rintro z x rfl _; exact Or.inr ⟨0, rfl, by simp⟩

theorem ms_rNmulPp : ∀ p q r : Pattern,
    Meaning T (jPMul p q r) → Meaning T (jNMul (cNPos p) (cNPos q) (cNPos r)) := by
  intro p q r h
  simp only [M_pmul, PMulM] at h
  obtain ⟨hf, hb⟩ := h
  simp only [M_nmul, NMulM, decNat_NPos]
  refine ⟨hf, ?_⟩
  intro z x hz hx
  obtain ⟨a, b, ha, hb', rfl⟩ := hb z hz
  rw [hx] at ha
  cases ha
  exact Or.inr ⟨b, hb', rfl⟩

theorem ms_rNdivmod : ∀ a b q r m : Pattern,
    Meaning T (jNMul b q m) → Meaning T (jNAdd m r a) → Meaning T (jNLt r b) →
      Meaning T (jNDivMod a b q r) := by
  intro a b q r m h1 h2 h3
  simp only [M_nmul, NMulM] at h1
  simp only [M_nadd, NAddM] at h2
  simp only [M_nlt, NLtM] at h3
  simp only [M_ndivmod, NDivModM]
  intro x y hx hy
  obtain ⟨w, v, hw, hv, rfl⟩ := h2.2 x hx
  obtain ⟨v', hv', hlt⟩ := h3 y hy
  rw [hv] at hv'
  cases hv'
  rcases h1.2 w y hw hy with hy0 | ⟨u, hu, rfl⟩
  · omega
  · exact ⟨u, v, hu, hv, rfl, hlt⟩

theorem ms_rNmod64 : ∀ a q c : Pattern,
    Meaning T (jNDivMod a patTwo64 q c) → Meaning T (jNMod64 a c) := by
  intro a q c h
  simp only [M_ndivmod, NDivModM] at h
  simp only [M_nmod64, NMod64M]
  intro x hx
  obtain ⟨u, v, _, hv, rfl, hlt⟩ := h x wordBound hx (decNat_encNat _)
  rw [hv]
  congr 1
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ## Lists -/

theorem ms_rLenNil : Meaning T (jLen cNil cN0) := by
  simp only [M_len, LenM, decList_nil, Option.some.injEq]
  rintro l rfl; rfl

theorem ms_rLenCons : ∀ xx xs n k : Pattern,
    Meaning T (jLen xs n) → Meaning T (jNAdd n patOne k) → Meaning T (jLen (cCons xx xs) k) := by
  intro xx xs n k h1 h2
  simp only [M_len, LenM] at h1
  simp only [M_nadd, NAddM] at h2
  simp only [M_len, LenM, decList_cons, Option.map_eq_some_iff]
  rintro l ⟨l', hl', rfl⟩
  exact h2.1 _ 1 (h1 l' hl') decNat_patOne

theorem ms_rNth0 : ∀ xx xs : Pattern, Meaning T (jNth (cCons xx xs) cN0 xx) := by
  intro xx xs
  simp only [M_nth, NthM, decList_cons, Option.map_eq_some_iff]
  rintro l ⟨l', _, rfl⟩
  exact ⟨0, decNat_N0, rfl⟩

theorem ms_rNthS : ∀ xx xs i j y : Pattern,
    Meaning T (jNAdd j patOne i) → Meaning T (jNth xs j y) →
      Meaning T (jNth (cCons xx xs) i y) := by
  intro xx xs i j y h1 h2
  simp only [M_nadd, NAddM] at h1
  simp only [M_nth, NthM] at h2
  simp only [M_nth, NthM, decList_cons, Option.map_eq_some_iff]
  rintro l ⟨l', hl', rfl⟩
  obtain ⟨k, hk, hy⟩ := h2 l' hl'
  exact ⟨k + 1, h1.1 k 1 hk decNat_patOne, by simpa using hy⟩

theorem ms_rBytesNil : Meaning T (jBytes cNil) := ⟨[], rfl⟩

theorem ms_rBytesCons : ∀ xx xs : Pattern,
    Meaning T (jNLt xx patByteBound) → Meaning T (jBytes xs) → Meaning T (jBytes (cCons xx xs)) := by
  intro xx xs h1 h2
  simp only [M_nlt, NLtM] at h1
  obtain ⟨bytes, rfl⟩ := h2
  obtain ⟨v, hv, hlt⟩ := h1 256 (decNat_encNat 256)
  refine ⟨UInt8.ofNat v :: bytes, ?_⟩
  rw [encBytes_cons, decNat_unique xx v hv]
  congr 2
  have : (UInt8.ofNat v).toNat = v := by simp; omega
  rw [this]

end Mettapedia.Languages.VibeITP.Presentation
