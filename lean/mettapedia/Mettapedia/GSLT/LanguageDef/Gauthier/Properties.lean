/-
# Verified property analysis for the Gauthier E1 org evaluator

This file lifts the WM-PLN property-analysis lane into Lean for the scalar E1 `org` evaluator.
The first certified layer is deliberately conservative: every positive claim is proved against the
real `eval` relation from `E1.lean`, and unknown cases stay unknown rather than becoming hypotheses.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.Gauthier.E1

namespace Mettapedia.GSLT.LanguageDef.GauthierProperties

open Mettapedia.GSLT.LanguageDef.GauthierE1

/-! ## Lattices -/

/-- Sign lattice as subsets of `{negative, zero, positive}`. -/
inductive SignInfo where
  | bot | neg | zero | pos | nonpos | nonneg | nonzero | top
  deriving DecidableEq, Repr

/-- Parity lattice `bot < even/odd < top`. -/
inductive ParityInfo where
  | bot | even | odd | top
  deriving DecidableEq, Repr

structure AbsVal where
  sign : SignInfo
  parity : ParityInfo
  total : Bool
  deriving Repr

def SignInfo.denote (s : SignInfo) (v : Int) : Prop :=
  match s with
  | .bot => False
  | .neg => v < 0
  | .zero => v = 0
  | .pos => 0 < v
  | .nonpos => v <= 0
  | .nonneg => 0 <= v
  | .nonzero => v ≠ 0
  | .top => True

def SignInfo.provesNonneg : SignInfo -> Bool
  | .zero | .pos | .nonneg => true
  | _ => false

def SignInfo.provesNonpos : SignInfo -> Bool
  | .zero | .neg | .nonpos => true
  | _ => false

def SignInfo.provesPos : SignInfo -> Bool
  | .pos => true
  | _ => false

def SignInfo.provesNeg : SignInfo -> Bool
  | .neg => true
  | _ => false

def SignInfo.provesNonzero : SignInfo -> Bool
  | .neg | .pos | .nonzero => true
  | _ => false

def SignInfo.join : SignInfo -> SignInfo -> SignInfo
  | .bot, b => b
  | a, .bot => a
  | .neg, .neg => .neg
  | .zero, .zero => .zero
  | .pos, .pos => .pos
  | .neg, .zero => .nonpos
  | .zero, .neg => .nonpos
  | .zero, .pos => .nonneg
  | .pos, .zero => .nonneg
  | .neg, .nonpos => .nonpos
  | .nonpos, .neg => .nonpos
  | .zero, .nonpos => .nonpos
  | .nonpos, .zero => .nonpos
  | .nonpos, .nonpos => .nonpos
  | .pos, .nonneg => .nonneg
  | .nonneg, .pos => .nonneg
  | .zero, .nonneg => .nonneg
  | .nonneg, .zero => .nonneg
  | .nonneg, .nonneg => .nonneg
  | .neg, .pos => .nonzero
  | .pos, .neg => .nonzero
  | .neg, .nonzero => .nonzero
  | .nonzero, .neg => .nonzero
  | .pos, .nonzero => .nonzero
  | .nonzero, .pos => .nonzero
  | .nonzero, .nonzero => .nonzero
  | _, _ => .top

def ParityInfo.join : ParityInfo -> ParityInfo -> ParityInfo
  | .bot, b => b
  | a, .bot => a
  | .even, .even => .even
  | .odd, .odd => .odd
  | .top, _ => .top
  | _, .top => .top
  | _, _ => .top

def EvenInt (v : Int) : Prop := ∃ k : Int, v = 2 * k
def OddInt (v : Int) : Prop := ∃ k : Int, v = 2 * k + 1

def ParityInfo.denote (p : ParityInfo) (v : Int) : Prop :=
  match p with
  | .bot => False
  | .even => EvenInt v
  | .odd => OddInt v
  | .top => True

def ParityInfo.provesEven : ParityInfo -> Bool
  | .even => true
  | _ => false

def ParityInfo.provesOdd : ParityInfo -> Bool
  | .odd => true
  | _ => false

def SignInfo.rank : SignInfo -> Nat
  | .bot => 0
  | .neg | .zero | .pos => 1
  | .nonpos | .nonneg | .nonzero => 2
  | .top => 3

def ParityInfo.rank : ParityInfo -> Nat
  | .bot => 0
  | .even | .odd => 1
  | .top => 2

theorem SignInfo.rank_le_three (s : SignInfo) : s.rank <= 3 := by
  cases s <;> simp [SignInfo.rank]

theorem ParityInfo.rank_le_two (p : ParityInfo) : p.rank <= 2 := by
  cases p <;> simp [ParityInfo.rank]

theorem SignInfo.rank_join_left {a b : SignInfo} : a.rank <= (a.join b).rank := by
  cases a <;> cases b <;> simp [SignInfo.rank, SignInfo.join]

theorem ParityInfo.rank_join_left {a b : ParityInfo} : a.rank <= (a.join b).rank := by
  cases a <;> cases b <;> simp [ParityInfo.rank, ParityInfo.join]

theorem SignInfo.rank_lt_join_of_ne {a b : SignInfo} (h : a.join b ≠ a) :
    a.rank < (a.join b).rank := by
  cases a <;> cases b <;> simp [SignInfo.rank, SignInfo.join] at h ⊢

theorem ParityInfo.rank_lt_join_of_ne {a b : ParityInfo} (h : a.join b ≠ a) :
    a.rank < (a.join b).rank := by
  cases a <;> cases b <;> simp [ParityInfo.rank, ParityInfo.join] at h ⊢

theorem SignInfo.join_join_right_of_eq_left {a b : SignInfo} (h : a.join b = a) :
    (a.join b).join b = a.join b := by
  cases a <;> cases b <;> simp [SignInfo.join] at h ⊢

theorem ParityInfo.join_join_right_of_eq_left {a b : ParityInfo} (h : a.join b = a) :
    (a.join b).join b = a.join b := by
  cases a <;> cases b <;> simp [ParityInfo.join] at h ⊢

def AbsVal.widenRank (a : AbsVal) : Nat := a.sign.rank + a.parity.rank

theorem AbsVal.widenRank_le_five (a : AbsVal) : a.widenRank <= 5 := by
  unfold AbsVal.widenRank
  have hs := SignInfo.rank_le_three a.sign
  have hp := ParityInfo.rank_le_two a.parity
  omega

theorem AbsVal.widenRank_join_le (acc step : AbsVal) :
    acc.widenRank <=
      ({ sign := acc.sign.join step.sign
       , parity := acc.parity.join step.parity
       , total := true
       } : AbsVal).widenRank := by
  unfold AbsVal.widenRank
  change acc.sign.rank + acc.parity.rank <=
    (acc.sign.join step.sign).rank + (acc.parity.join step.parity).rank
  have hs := SignInfo.rank_join_left (a := acc.sign) (b := step.sign)
  have hp := ParityInfo.rank_join_left (a := acc.parity) (b := step.parity)
  omega

theorem AbsVal.widenRank_lt_of_join_changed (acc step : AbsVal)
    (h : acc.sign.join step.sign ≠ acc.sign ∨ acc.parity.join step.parity ≠ acc.parity) :
    acc.widenRank <
      ({ sign := acc.sign.join step.sign
       , parity := acc.parity.join step.parity
       , total := true
       } : AbsVal).widenRank := by
  unfold AbsVal.widenRank
  change acc.sign.rank + acc.parity.rank <
    (acc.sign.join step.sign).rank + (acc.parity.join step.parity).rank
  rcases h with hs | hp
  · have hlt := SignInfo.rank_lt_join_of_ne hs
    have hle := ParityInfo.rank_join_left (a := acc.parity) (b := step.parity)
    omega
  · have hle := SignInfo.rank_join_left (a := acc.sign) (b := step.sign)
    have hlt := ParityInfo.rank_lt_join_of_ne hp
    omega

def AbsVal.pairWidenRank (a b : AbsVal) : Nat := a.widenRank + b.widenRank

theorem AbsVal.pairWidenRank_le_ten (a b : AbsVal) : a.pairWidenRank b <= 10 := by
  unfold AbsVal.pairWidenRank
  have ha := AbsVal.widenRank_le_five a
  have hb := AbsVal.widenRank_le_five b
  omega

theorem AbsVal.pairWidenRank_lt_of_join_changed (accX accY stepX stepY : AbsVal)
    (h : accX.sign.join stepX.sign ≠ accX.sign ∨
      accX.parity.join stepX.parity ≠ accX.parity ∨
      accY.sign.join stepY.sign ≠ accY.sign ∨
      accY.parity.join stepY.parity ≠ accY.parity) :
    accX.pairWidenRank accY <
      ({ sign := accX.sign.join stepX.sign
       , parity := accX.parity.join stepX.parity
       , total := true
       } : AbsVal).pairWidenRank
      ({ sign := accY.sign.join stepY.sign
       , parity := accY.parity.join stepY.parity
       , total := true
       } : AbsVal) := by
  unfold AbsVal.pairWidenRank
  rcases h with hxS | hxP | hyS | hyP
  · have hx := AbsVal.widenRank_lt_of_join_changed accX stepX (Or.inl hxS)
    have hy := AbsVal.widenRank_join_le accY stepY
    omega
  · have hx := AbsVal.widenRank_lt_of_join_changed accX stepX (Or.inr hxP)
    have hy := AbsVal.widenRank_join_le accY stepY
    omega
  · have hx := AbsVal.widenRank_join_le accX stepX
    have hy := AbsVal.widenRank_lt_of_join_changed accY stepY (Or.inl hyS)
    omega
  · have hx := AbsVal.widenRank_join_le accX stepX
    have hy := AbsVal.widenRank_lt_of_join_changed accY stepY (Or.inr hyP)
    omega

def signAdd : SignInfo -> SignInfo -> SignInfo
  | .zero, b => b
  | a, .zero => a
  | .nonneg, .pos => .pos
  | .pos, .nonneg => .pos
  | .pos, .pos => .pos
  | .nonneg, .nonneg => .nonneg
  | .nonpos, .neg => .neg
  | .neg, .nonpos => .neg
  | .neg, .neg => .neg
  | .nonpos, .nonpos => .nonpos
  | _, _ => .top

def signNeg : SignInfo -> SignInfo
  | .bot => .bot
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg
  | .nonpos => .nonneg
  | .nonneg => .nonpos
  | .nonzero => .nonzero
  | .top => .top

def signMul : SignInfo -> SignInfo -> SignInfo
  | .zero, _ => .zero
  | _, .zero => .zero
  | .pos, .pos => .pos
  | .pos, .nonneg => .nonneg
  | .nonneg, .pos => .nonneg
  | .nonneg, .nonneg => .nonneg
  | _, _ => .top

def signDiv : SignInfo -> SignInfo -> SignInfo
  | .zero, .neg => .zero
  | .zero, .pos => .zero
  | .zero, .nonpos => .zero
  | .zero, .nonneg => .zero
  | .zero, .nonzero => .zero
  | .zero, .top => .zero
  | .neg, .neg => .nonneg
  | .neg, .pos => .neg
  | .neg, .nonpos => .nonneg
  | .neg, .nonneg => .neg
  | .pos, .neg => .neg
  | .pos, .pos => .nonneg
  | .pos, .nonpos => .neg
  | .pos, .nonneg => .nonneg
  | .nonpos, .neg => .nonneg
  | .nonpos, .pos => .nonpos
  | .nonpos, .nonpos => .nonneg
  | .nonpos, .nonneg => .nonpos
  | .nonneg, .neg => .nonpos
  | .nonneg, .pos => .nonneg
  | .nonneg, .nonpos => .nonpos
  | .nonneg, .nonneg => .nonneg
  | _, _ => .top

def signMod : SignInfo -> SignInfo -> SignInfo
  | _, .pos => .nonneg
  | _, .nonneg => .nonneg
  | _, .neg => .nonpos
  | _, .nonpos => .nonpos
  | _, _ => .top

def parityAdd : ParityInfo -> ParityInfo -> ParityInfo
  | .even, .even => .even
  | .even, .odd => .odd
  | .odd, .even => .odd
  | .odd, .odd => .even
  | .bot, _ => .bot
  | _, .bot => .bot
  | _, _ => .top

def parityMul : ParityInfo -> ParityInfo -> ParityInfo
  | .bot, _ => .bot
  | _, .bot => .bot
  | .even, _ => .even
  | _, .even => .even
  | .odd, .odd => .odd
  | _, _ => .top

def AbsVal.top : AbsVal := { sign := .top, parity := .top, total := false }
def AbsVal.zero : AbsVal := { sign := .zero, parity := .even, total := true }
def AbsVal.one : AbsVal := { sign := .pos, parity := .odd, total := true }
def AbsVal.two : AbsVal := { sign := .pos, parity := .even, total := true }
def AbsVal.nonnegUnknownParity : AbsVal := { sign := .nonneg, parity := .top, total := true }
def AbsVal.zeroReg : AbsVal := { sign := .zero, parity := .even, total := true }

def AbsVal.join (a b : AbsVal) : AbsVal :=
  { sign := a.sign.join b.sign
  , parity := a.parity.join b.parity
  , total := a.total && b.total
  }

def AbsVal.add (a b : AbsVal) : AbsVal :=
  { sign := signAdd a.sign b.sign
  , parity := parityAdd a.parity b.parity
  , total := a.total && b.total
  }

def AbsVal.diff (a b : AbsVal) : AbsVal :=
  { sign := signAdd a.sign (signNeg b.sign)
  , parity := parityAdd a.parity b.parity
  , total := a.total && b.total
  }

def AbsVal.mult (a b : AbsVal) : AbsVal :=
  { sign := signMul a.sign b.sign
  , parity := parityMul a.parity b.parity
  , total := a.total && b.total
  }

def AbsVal.divi (a b : AbsVal) : AbsVal :=
  { sign := signDiv a.sign b.sign
  , parity := .top
  , total := a.total && b.total && b.sign.provesNonzero
  }

def AbsVal.modu (a b : AbsVal) : AbsVal :=
  { sign := signMod a.sign b.sign
  , parity := .top
  , total := a.total && b.total && b.sign.provesNonzero
  }

def AbsVal.compr : AbsVal := { sign := .nonneg, parity := .top, total := false }

theorem SignInfo.join_left_sound {a b : SignInfo} {v : Int}
    (h : a.denote v) : (a.join b).denote v := by
  cases a <;> cases b <;> simp [SignInfo.denote, SignInfo.join] at h ⊢ <;> omega

theorem SignInfo.join_right_sound {a b : SignInfo} {v : Int}
    (h : b.denote v) : (a.join b).denote v := by
  cases a <;> cases b <;> simp [SignInfo.denote, SignInfo.join] at h ⊢ <;> omega

theorem SignInfo.denote_of_join_eq_left {a b : SignInfo} {v : Int}
    (hjoin : a.join b = a) (hb : b.denote v) : a.denote v := by
  rw [← hjoin]
  exact SignInfo.join_right_sound hb

theorem signAdd_sound {a b : SignInfo} {va vb : Int}
    (ha : a.denote va) (hb : b.denote vb) : (signAdd a b).denote (va + vb) := by
  cases a <;> cases b <;> simp [SignInfo.denote, signAdd] at ha hb ⊢ <;> omega

theorem signNeg_sound {a : SignInfo} {v : Int}
    (h : a.denote v) : (signNeg a).denote (-v) := by
  cases a <;> simp [SignInfo.denote, signNeg] at h ⊢ <;> omega

theorem signMul_sound {a b : SignInfo} {va vb : Int}
    (ha : a.denote va) (hb : b.denote vb) : (signMul a b).denote (va * vb) := by
  cases a <;> cases b <;> simp [SignInfo.denote, signMul] at ha hb ⊢ <;> try simp_all
  case nonneg.nonneg => exact Int.mul_nonneg ha hb

theorem Int.fdiv_zero_left (b : Int) : Int.fdiv 0 b = 0 := by
  simp [Int.fdiv_eq_ediv]

theorem Int.fdiv_neg_of_neg_of_pos_right {a b : Int} (ha : a < 0) (hb : 0 < b) :
    Int.fdiv a b < 0 := by
  rw [Int.fdiv_eq_ediv_of_nonneg a hb.le]
  exact Int.ediv_neg_of_neg_of_pos ha hb

theorem Int.fdiv_neg_of_pos_of_neg_right {a b : Int} (ha : 0 < a) (hb : b < 0) :
    Int.fdiv a b < 0 := by
  let c : Int := -b
  have hcpos : 0 < c := by dsimp [c]; omega
  have hbexpr : b = -c := by dsimp [c]; omega
  rw [hbexpr]
  have hcne : c ≠ 0 := by omega
  rw [Int.fdiv_neg (a := a) (b := c) hcne]
  by_cases hdiv : c ∣ a
  · have hqpos : 0 < Int.fdiv a c := by
      rw [Int.fdiv_eq_ediv_of_nonneg a hcpos.le]
      exact Int.ediv_pos_of_pos_of_dvd ha hcpos.le hdiv
    simp [hdiv]
    omega
  · have hqnonneg : 0 <= Int.fdiv a c := Int.fdiv_nonneg ha.le hcpos.le
    simp [hdiv]
    omega

theorem Int.fdiv_nonneg_of_neg_of_neg_right {a b : Int} (ha : a < 0) (hb : b < 0) :
    0 <= Int.fdiv a b := by
  let c : Int := -b
  have hcpos : 0 < c := by dsimp [c]; omega
  have hbexpr : b = -c := by dsimp [c]; omega
  rw [hbexpr]
  have hcne : c ≠ 0 := by omega
  rw [Int.fdiv_neg (a := a) (b := c) hcne]
  have hqneg : Int.fdiv a c < 0 := Int.fdiv_neg_of_neg_of_pos_right ha hcpos
  by_cases hdiv : c ∣ a
  · simp [hdiv]
    omega
  · simp [hdiv]
    omega

theorem Int.fdiv_nonpos_of_nonpos_of_pos_right {a b : Int} (ha : a <= 0) (hb : 0 < b) :
    Int.fdiv a b <= 0 := by
  by_cases hzero : a = 0
  · subst a
    simp
  · exact le_of_lt (Int.fdiv_neg_of_neg_of_pos_right (by omega) hb)

theorem Int.fdiv_nonpos_of_nonpos_of_nonneg_right {a b : Int}
    (ha : a <= 0) (hb : 0 <= b) (hbnz : b ≠ 0) :
    Int.fdiv a b <= 0 :=
  Int.fdiv_nonpos_of_nonpos_of_pos_right ha (by omega)

theorem Int.fdiv_nonpos_of_nonneg_of_neg_right {a b : Int} (ha : 0 <= a) (hb : b < 0) :
    Int.fdiv a b <= 0 := by
  by_cases hzero : a = 0
  · subst a
    simp
  · exact le_of_lt (Int.fdiv_neg_of_pos_of_neg_right (by omega) hb)

theorem Int.fdiv_nonpos_of_nonneg_of_nonpos_right {a b : Int}
    (ha : 0 <= a) (hb : b <= 0) (hbnz : b ≠ 0) :
    Int.fdiv a b <= 0 :=
  Int.fdiv_nonpos_of_nonneg_of_neg_right ha (by omega)

theorem Int.fdiv_nonneg_of_nonpos_of_neg_right {a b : Int} (ha : a <= 0) (hb : b < 0) :
    0 <= Int.fdiv a b := by
  by_cases hzero : a = 0
  · subst a
    simp
  · exact Int.fdiv_nonneg_of_neg_of_neg_right (by omega) hb

theorem Int.fdiv_nonneg_of_nonpos_of_nonpos_right {a b : Int}
    (ha : a <= 0) (hb : b <= 0) (hbnz : b ≠ 0) :
    0 <= Int.fdiv a b :=
  Int.fdiv_nonneg_of_nonpos_of_neg_right ha (by omega)

theorem signDiv_sound {a b : SignInfo} {va vb : Int}
    (ha : a.denote va) (hb : b.denote vb) (_hvb : vb ≠ 0) :
    (signDiv a b).denote (Int.fdiv va vb) := by
  cases a <;> cases b <;> simp [SignInfo.denote, signDiv] at ha hb ⊢
  all_goals try
    subst va
    simp
  all_goals try exact Int.fdiv_nonneg_of_neg_of_neg_right ha hb
  all_goals try exact Int.fdiv_nonneg_of_neg_of_neg_right ha (by omega)
  all_goals try exact Int.fdiv_nonneg_of_nonpos_of_neg_right ha hb
  all_goals try exact Int.fdiv_nonneg_of_nonpos_of_nonpos_right ha hb _hvb
  all_goals try exact Int.fdiv_neg_of_neg_of_pos_right ha hb
  all_goals try exact Int.fdiv_neg_of_neg_of_pos_right ha (by omega)
  all_goals try exact Int.fdiv_neg_of_pos_of_neg_right ha hb
  all_goals try exact Int.fdiv_neg_of_pos_of_neg_right ha (by omega)
  all_goals try exact Int.fdiv_nonpos_of_nonpos_of_pos_right ha hb
  all_goals try exact Int.fdiv_nonpos_of_nonpos_of_nonneg_right ha hb _hvb
  all_goals try exact Int.fdiv_nonpos_of_nonneg_of_neg_right ha hb
  all_goals try exact Int.fdiv_nonpos_of_nonneg_of_nonpos_right ha hb _hvb
  all_goals try exact Int.fdiv_nonneg (le_of_lt ha) (le_of_lt hb)
  all_goals try exact Int.fdiv_nonneg (le_of_lt ha) hb
  all_goals try exact Int.fdiv_nonneg ha (le_of_lt hb)
  all_goals try exact Int.fdiv_nonneg ha hb

theorem Int.fmod_nonneg_of_pos_right (a : Int) {b : Int} (hb : 0 < b) :
    0 <= Int.fmod a b := by
  rw [Int.fmod_eq_emod_of_nonneg a hb.le]
  exact Int.emod_nonneg a (ne_of_gt hb)

theorem Int.fmod_nonpos_of_neg_right (a : Int) {b : Int} (hb : b < 0) :
    Int.fmod a b <= 0 := by
  rw [Int.fmod_eq_emod]
  have hnb0 : ¬ 0 <= b := by omega
  by_cases hdiv : b ∣ a
  · have hem0 : a % b = 0 := Int.emod_eq_zero_of_dvd hdiv
    simp [hnb0, hdiv, hem0]
  · have hne : b ≠ 0 := by omega
    have hlt : a % b < |b| := Int.emod_lt_abs a hne
    have habs : |b| = -b := abs_of_neg hb
    simp [hnb0, hdiv]
    rw [habs] at hlt
    omega

theorem signMod_sound {a b : SignInfo} {va vb : Int}
    (hb : b.denote vb) (hvb : vb ≠ 0) :
    (signMod a b).denote (Int.fmod va vb) := by
  cases a <;> cases b <;> simp [SignInfo.denote, signMod] at hb ⊢
  all_goals try exact Int.fmod_nonneg_of_pos_right va hb
  all_goals try
    apply Int.fmod_nonneg_of_pos_right
    omega
  all_goals try exact Int.fmod_nonpos_of_neg_right va hb
  all_goals try
    apply Int.fmod_nonpos_of_neg_right
    omega

theorem SignInfo.provesNonneg_sound {s : SignInfo} {v : Int}
    (hs : s.provesNonneg = true) (h : s.denote v) : 0 <= v := by
  cases s <;> simp [SignInfo.provesNonneg, SignInfo.denote] at hs h ⊢ <;> omega

theorem SignInfo.provesNonpos_sound {s : SignInfo} {v : Int}
    (hs : s.provesNonpos = true) (h : s.denote v) : v <= 0 := by
  cases s <;> simp [SignInfo.provesNonpos, SignInfo.denote] at hs h ⊢ <;> omega

theorem SignInfo.provesPos_sound {s : SignInfo} {v : Int}
    (hs : s.provesPos = true) (h : s.denote v) : 0 < v := by
  cases s <;> simp [SignInfo.provesPos, SignInfo.denote] at hs h ⊢; omega

theorem SignInfo.provesNeg_sound {s : SignInfo} {v : Int}
    (hs : s.provesNeg = true) (h : s.denote v) : v < 0 := by
  cases s <;> simp [SignInfo.provesNeg, SignInfo.denote] at hs h ⊢; omega

theorem SignInfo.provesNonzero_sound {s : SignInfo} {v : Int}
    (hs : s.provesNonzero = true) (h : s.denote v) : v ≠ 0 := by
  cases s <;> simp [SignInfo.provesNonzero, SignInfo.denote] at hs h ⊢ <;> omega

theorem ParityInfo.join_left_sound {a b : ParityInfo} {v : Int}
    (h : a.denote v) : (a.join b).denote v := by
  cases a <;> cases b <;> simp [ParityInfo.denote, ParityInfo.join] at h ⊢
  all_goals assumption

theorem ParityInfo.join_right_sound {a b : ParityInfo} {v : Int}
    (h : b.denote v) : (a.join b).denote v := by
  cases a <;> cases b <;> simp [ParityInfo.denote, ParityInfo.join] at h ⊢
  all_goals assumption

theorem ParityInfo.denote_of_join_eq_left {a b : ParityInfo} {v : Int}
    (hjoin : a.join b = a) (hb : b.denote v) : a.denote v := by
  rw [← hjoin]
  exact ParityInfo.join_right_sound hb

theorem parityAdd_sound {a b : ParityInfo} {va vb : Int}
    (ha : a.denote va) (hb : b.denote vb) :
    (parityAdd a b).denote (va + vb) := by
  cases a <;> cases b <;> simp [ParityInfo.denote, parityAdd, EvenInt, OddInt] at ha hb ⊢
  · rcases ha with ⟨ka, rfl⟩
    rcases hb with ⟨kb, rfl⟩
    exact ⟨ka + kb, by omega⟩
  · rcases ha with ⟨ka, rfl⟩
    rcases hb with ⟨kb, rfl⟩
    exact ⟨ka + kb, by omega⟩
  · rcases ha with ⟨ka, rfl⟩
    rcases hb with ⟨kb, rfl⟩
    exact ⟨ka + kb, by omega⟩
  · rcases ha with ⟨ka, rfl⟩
    rcases hb with ⟨kb, rfl⟩
    exact ⟨ka + kb + 1, by omega⟩

theorem paritySub_sound {a b : ParityInfo} {va vb : Int}
    (ha : a.denote va) (hb : b.denote vb) :
    (parityAdd a b).denote (va - vb) := by
  cases a <;> cases b <;> simp [ParityInfo.denote, parityAdd, EvenInt, OddInt] at ha hb ⊢
  · rcases ha with ⟨ka, rfl⟩
    rcases hb with ⟨kb, rfl⟩
    exact ⟨ka - kb, by omega⟩
  · rcases ha with ⟨ka, rfl⟩
    rcases hb with ⟨kb, rfl⟩
    exact ⟨ka - kb - 1, by omega⟩
  · rcases ha with ⟨ka, rfl⟩
    rcases hb with ⟨kb, rfl⟩
    exact ⟨ka - kb, by omega⟩
  · rcases ha with ⟨ka, rfl⟩
    rcases hb with ⟨kb, rfl⟩
    exact ⟨ka - kb, by omega⟩

theorem parityMul_sound {a b : ParityInfo} {va vb : Int}
    (ha : a.denote va) (hb : b.denote vb) :
    (parityMul a b).denote (va * vb) := by
  have even_mul_any {x y : Int} (hx : EvenInt x) : EvenInt (x * y) := by
    rcases hx with ⟨k, rfl⟩
    exact ⟨k * y, by ring⟩
  have any_mul_even {x y : Int} (hy : EvenInt y) : EvenInt (x * y) := by
    rcases hy with ⟨k, rfl⟩
    exact ⟨k * x, by ring⟩
  have odd_mul_odd {x y : Int} (hx : OddInt x) (hy : OddInt y) : OddInt (x * y) := by
    rcases hx with ⟨kx, rfl⟩
    rcases hy with ⟨ky, rfl⟩
    exact ⟨2 * kx * ky + kx + ky, by ring⟩
  cases a <;> cases b <;> simp [ParityInfo.denote, parityMul, EvenInt, OddInt] at ha hb ⊢
  all_goals first
    | exact even_mul_any ha
    | exact any_mul_even hb
    | exact odd_mul_odd ha hb

theorem ParityInfo.provesEven_sound {p : ParityInfo} {v : Int}
    (hp : p.provesEven = true) (h : p.denote v) : EvenInt v := by
  cases p <;> simp [ParityInfo.provesEven, ParityInfo.denote] at hp h ⊢
  exact h

theorem ParityInfo.provesOdd_sound {p : ParityInfo} {v : Int}
    (hp : p.provesOdd = true) (h : p.denote v) : OddInt v := by
  cases p <;> simp [ParityInfo.provesOdd, ParityInfo.denote] at hp h ⊢
  exact h

def progHeight : Prog -> Nat
  | .node _ [] => 1
  | .node _ ch => 1 + listHeight ch
where
  listHeight : List Prog -> Nat
    | [] => 0
    | p :: ps => Nat.max (progHeight p) (listHeight ps)

/-! ## Executable analysis over `Prog` -/

def analyzeFuel : Nat -> AbsVal -> AbsVal -> Prog -> AbsVal
  | 0, _, _, _ => .top
  | fuel + 1, xVal, yVal, .node id ch =>
      match id, ch with
      | 0, [] => .zero
      | 1, [] => .one
      | 2, [] => .two
      | 3, [a, b] => (analyzeFuel fuel xVal yVal a).add (analyzeFuel fuel xVal yVal b)
      | 4, [a, b] => (analyzeFuel fuel xVal yVal a).diff (analyzeFuel fuel xVal yVal b)
      | 5, [a, b] => (analyzeFuel fuel xVal yVal a).mult (analyzeFuel fuel xVal yVal b)
      | 6, [a, b] => (analyzeFuel fuel xVal yVal a).divi (analyzeFuel fuel xVal yVal b)
      | 7, [a, b] => (analyzeFuel fuel xVal yVal a).modu (analyzeFuel fuel xVal yVal b)
      | 8, [c, t, e] =>
          let cv := analyzeFuel fuel xVal yVal c
          let branches := (analyzeFuel fuel xVal yVal t).join (analyzeFuel fuel xVal yVal e)
          { branches with total := cv.total && branches.total }
      | 9, [body, count, init] =>
          let cnt := analyzeFuel fuel xVal yVal count
          let initial := analyzeFuel fuel xVal yVal init
          let loopY := AbsVal.nonnegUnknownParity
          let rec loopWiden : Nat -> AbsVal -> AbsVal
            | 0, acc => acc
            | steps + 1, acc =>
                let step := analyzeFuel fuel { acc with total := true } loopY body
                let next : AbsVal :=
                  { sign := acc.sign.join step.sign
                  , parity := acc.parity.join step.parity
                  , total := true
                  }
                if next.sign = acc.sign && next.parity = acc.parity then
                  next
                else
                  loopWiden steps next
          let acc := loopWiden 24 initial
          let bodyTotal := analyzeFuel fuel { acc with total := true } loopY body
          { sign := acc.sign
          , parity := acc.parity
          , total := cnt.total && initial.total && bodyTotal.total
          }
      | 10, [] => xVal
      | 11, [] => yVal
      | 12, [_, _] => .compr
      | 13, [f, g, count, a, b] =>
          let cnt := analyzeFuel fuel xVal yVal count
          let initialX := analyzeFuel fuel xVal yVal a
          let initialY := analyzeFuel fuel xVal yVal b
          let rec loop2Widen : Nat -> AbsVal -> AbsVal -> AbsVal × AbsVal
            | 0, accX, accY => (accX, accY)
            | steps + 1, accX, accY =>
                let envX := { accX with total := true }
                let envY := { accY with total := true }
                let stepX := analyzeFuel fuel envX envY f
                let stepY := analyzeFuel fuel envX envY g
                let nextX : AbsVal :=
                  { sign := accX.sign.join stepX.sign
                  , parity := accX.parity.join stepX.parity
                  , total := true
                  }
                let nextY : AbsVal :=
                  { sign := accY.sign.join stepY.sign
                  , parity := accY.parity.join stepY.parity
                  , total := true
                  }
                if nextX.sign = accX.sign && nextX.parity = accX.parity &&
                    nextY.sign = accY.sign && nextY.parity = accY.parity then
                  (nextX, nextY)
                else
                  loop2Widen steps nextX nextY
          let acc := loop2Widen 24 initialX initialY
          let bodyX := analyzeFuel fuel { acc.1 with total := true } { acc.2 with total := true } f
          let bodyY := analyzeFuel fuel { acc.1 with total := true } { acc.2 with total := true } g
          { sign := acc.1.sign
          , parity := acc.1.parity
          , total := cnt.total && initialX.total && initialY.total && bodyX.total && bodyY.total
          }
      | _, _ => .top

def loopWidenStep (fuel : Nat) (body : Prog) (loopY acc : AbsVal) : AbsVal :=
  let step := analyzeFuel fuel { acc with total := true } loopY body
  { sign := acc.sign.join step.sign
  , parity := acc.parity.join step.parity
  , total := true
  }

def loop2WidenStep (fuel : Nat) (f g : Prog) (accX accY : AbsVal) : AbsVal × AbsVal :=
  let envX := { accX with total := true }
  let envY := { accY with total := true }
  let stepX := analyzeFuel fuel envX envY f
  let stepY := analyzeFuel fuel envX envY g
  let nextX : AbsVal :=
    { sign := accX.sign.join stepX.sign
    , parity := accX.parity.join stepX.parity
    , total := true
    }
  let nextY : AbsVal :=
    { sign := accY.sign.join stepY.sign
    , parity := accY.parity.join stepY.parity
    , total := true
    }
  (nextX, nextY)

theorem loopWiden_zero (fuel : Nat) (body : Prog) (loopY acc : AbsVal) :
    analyzeFuel.loopWiden fuel body loopY 0 acc = acc := by
  simp [analyzeFuel.loopWiden]

theorem loopWiden_succ (fuel : Nat) (body : Prog) (loopY acc : AbsVal) (steps : Nat) :
    analyzeFuel.loopWiden fuel body loopY (steps + 1) acc =
      (let step := analyzeFuel fuel { acc with total := true } loopY body
       let next : AbsVal :=
         { sign := acc.sign.join step.sign
         , parity := acc.parity.join step.parity
         , total := true
         }
       if next.sign = acc.sign && next.parity = acc.parity then
         next
       else
         analyzeFuel.loopWiden fuel body loopY steps next) := by
  simp [analyzeFuel.loopWiden]

theorem loopWiden_succ_step (fuel : Nat) (body : Prog) (loopY acc : AbsVal) (steps : Nat) :
    analyzeFuel.loopWiden fuel body loopY (steps + 1) acc =
      (let next := loopWidenStep fuel body loopY acc
       if next.sign = acc.sign && next.parity = acc.parity then
         next
       else
         analyzeFuel.loopWiden fuel body loopY steps next) := by
  simp [loopWiden_succ, loopWidenStep]

theorem loopWidenStep_rank_le (fuel : Nat) (body : Prog) (loopY acc : AbsVal) :
    acc.widenRank <= (loopWidenStep fuel body loopY acc).widenRank := by
  simp [loopWidenStep, AbsVal.widenRank_join_le]

theorem loopWidenStep_sign_acc_denote {fuel : Nat} {body : Prog} {loopY acc : AbsVal}
    {v : Int} (hacc : acc.sign.denote v) :
    (loopWidenStep fuel body loopY acc).sign.denote v := by
  unfold loopWidenStep
  exact SignInfo.join_left_sound hacc

theorem loopWidenStep_parity_acc_denote {fuel : Nat} {body : Prog} {loopY acc : AbsVal}
    {v : Int} (hacc : acc.parity.denote v) :
    (loopWidenStep fuel body loopY acc).parity.denote v := by
  unfold loopWidenStep
  exact ParityInfo.join_left_sound hacc

theorem loopWidenStep_rank_lt_of_changed (fuel : Nat) (body : Prog) (loopY acc : AbsVal)
    (h : (loopWidenStep fuel body loopY acc).sign ≠ acc.sign ∨
      (loopWidenStep fuel body loopY acc).parity ≠ acc.parity) :
    acc.widenRank < (loopWidenStep fuel body loopY acc).widenRank := by
  simpa [loopWidenStep] using
    AbsVal.widenRank_lt_of_join_changed acc
      (analyzeFuel fuel { acc with total := true } loopY body) h

theorem loopWiden_rank_mono (fuel : Nat) (body : Prog) (loopY : AbsVal) :
    ∀ (steps : Nat) (acc : AbsVal),
      acc.widenRank <= (analyzeFuel.loopWiden fuel body loopY steps acc).widenRank
  | 0, acc => by simp [loopWiden_zero]
  | steps + 1, acc => by
      rw [loopWiden_succ_step]
      let next := loopWidenStep fuel body loopY acc
      have hnext : acc.widenRank <= next.widenRank :=
        loopWidenStep_rank_le fuel body loopY acc
      by_cases h : next.sign = acc.sign && next.parity = acc.parity
      · simp [h, next]
        exact hnext
      · simp [h, next]
        exact Nat.le_trans hnext (loopWiden_rank_mono fuel body loopY steps next)

def loopWidenStable (fuel : Nat) (body : Prog) (loopY acc : AbsVal) : Prop :=
  let next := loopWidenStep fuel body loopY acc
  next.sign = acc.sign ∧ next.parity = acc.parity

theorem loopWidenStep_stable_of_stable (fuel : Nat) (body : Prog) (loopY acc : AbsVal)
    (hstable : loopWidenStable fuel body loopY acc) :
    loopWidenStable fuel body loopY (loopWidenStep fuel body loopY acc) := by
  dsimp [loopWidenStable] at hstable ⊢
  rcases hstable with ⟨hs, hp⟩
  cases acc
  simp [loopWidenStep] at hs hp ⊢
  constructor
  · rw [hs, hp]
    exact hs
  · rw [hs, hp]
    exact hp

theorem loopWiden_stable_of_rank_budget (fuel : Nat) (body : Prog) (loopY : AbsVal) :
    ∀ (steps : Nat) (acc : AbsVal),
      6 <= acc.widenRank + steps ->
      loopWidenStable fuel body loopY (analyzeFuel.loopWiden fuel body loopY steps acc)
  | 0, acc, hbudget => by
      have hle := AbsVal.widenRank_le_five acc
      omega
  | steps + 1, acc, hbudget => by
      rw [loopWiden_succ_step]
      let next := loopWidenStep fuel body loopY acc
      by_cases h : next.sign = acc.sign && next.parity = acc.parity
      · have hstable : loopWidenStable fuel body loopY acc := by
          unfold loopWidenStable
          simpa [next] using h
        simp [h, next]
        exact loopWidenStep_stable_of_stable fuel body loopY acc hstable
      · have hchanged : next.sign ≠ acc.sign ∨ next.parity ≠ acc.parity := by
          by_cases hs : next.sign = acc.sign
          · right
            intro hp
            exact h (by simp [hs, hp])
          · exact Or.inl hs
        have hlt := loopWidenStep_rank_lt_of_changed fuel body loopY acc hchanged
        have hltNext : acc.widenRank < next.widenRank := by
          simpa [next] using hlt
        have hbudgetNext : 6 <= next.widenRank + steps := by omega
        simp [h, next]
        exact loopWiden_stable_of_rank_budget fuel body loopY steps next hbudgetNext

theorem loopWiden_stable_24 (fuel : Nat) (body : Prog) (loopY acc : AbsVal) :
    loopWidenStable fuel body loopY (analyzeFuel.loopWiden fuel body loopY 24 acc) := by
  apply loopWiden_stable_of_rank_budget
  omega

theorem loopWiden_sign_initial_denote (fuel : Nat) (body : Prog) (loopY : AbsVal) :
    ∀ (steps : Nat) (initial : AbsVal) {v : Int},
      initial.sign.denote v ->
      (analyzeFuel.loopWiden fuel body loopY steps initial).sign.denote v
  | 0, initial, v, h => by simpa [loopWiden_zero] using h
  | steps + 1, initial, v, h => by
      rw [loopWiden_succ_step]
      let next := loopWidenStep fuel body loopY initial
      have hnext : next.sign.denote v := loopWidenStep_sign_acc_denote h
      by_cases hstop : next.sign = initial.sign && next.parity = initial.parity
      · simpa [hstop, next] using hnext
      · simp [hstop, next]
        exact loopWiden_sign_initial_denote fuel body loopY steps next hnext

theorem loopWiden_parity_initial_denote (fuel : Nat) (body : Prog) (loopY : AbsVal) :
    ∀ (steps : Nat) (initial : AbsVal) {v : Int},
      initial.parity.denote v ->
      (analyzeFuel.loopWiden fuel body loopY steps initial).parity.denote v
  | 0, initial, v, h => by simpa [loopWiden_zero] using h
  | steps + 1, initial, v, h => by
      rw [loopWiden_succ_step]
      let next := loopWidenStep fuel body loopY initial
      have hnext : next.parity.denote v := loopWidenStep_parity_acc_denote h
      by_cases hstop : next.sign = initial.sign && next.parity = initial.parity
      · simpa [hstop, next] using hnext
      · simp [hstop, next]
        exact loopWiden_parity_initial_denote fuel body loopY steps next hnext

theorem loopWidenStable_sign_body_denote {fuel : Nat} {body : Prog} {loopY acc : AbsVal}
    {v : Int} (hstable : loopWidenStable fuel body loopY acc)
    (hbody : (analyzeFuel fuel { acc with total := true } loopY body).sign.denote v) :
    acc.sign.denote v := by
  unfold loopWidenStable at hstable
  unfold loopWidenStep at hstable
  exact SignInfo.denote_of_join_eq_left hstable.1 hbody

theorem loopWidenStable_parity_body_denote {fuel : Nat} {body : Prog} {loopY acc : AbsVal}
    {v : Int} (hstable : loopWidenStable fuel body loopY acc)
    (hbody : (analyzeFuel fuel { acc with total := true } loopY body).parity.denote v) :
    acc.parity.denote v := by
  unfold loopWidenStable at hstable
  unfold loopWidenStep at hstable
  exact ParityInfo.denote_of_join_eq_left hstable.2 hbody

theorem loopWiden24_sign_body_denote {fuel : Nat} {body : Prog} {loopY initial : AbsVal}
    {v : Int}
    (hbody : (analyzeFuel fuel { analyzeFuel.loopWiden fuel body loopY 24 initial with total := true }
      loopY body).sign.denote v) :
    (analyzeFuel.loopWiden fuel body loopY 24 initial).sign.denote v :=
  loopWidenStable_sign_body_denote (loopWiden_stable_24 fuel body loopY initial) hbody

theorem loopWiden24_parity_body_denote {fuel : Nat} {body : Prog} {loopY initial : AbsVal}
    {v : Int}
    (hbody : (analyzeFuel fuel { analyzeFuel.loopWiden fuel body loopY 24 initial with total := true }
      loopY body).parity.denote v) :
    (analyzeFuel.loopWiden fuel body loopY 24 initial).parity.denote v :=
  loopWidenStable_parity_body_denote (loopWiden_stable_24 fuel body loopY initial) hbody

theorem loop2Widen_zero (fuel : Nat) (f g : Prog) (accX accY : AbsVal) :
    analyzeFuel.loop2Widen fuel f g 0 accX accY = (accX, accY) := by
  simp [analyzeFuel.loop2Widen]

theorem loop2Widen_succ (fuel : Nat) (f g : Prog) (accX accY : AbsVal) (steps : Nat) :
    analyzeFuel.loop2Widen fuel f g (steps + 1) accX accY =
      (let envX := { accX with total := true }
       let envY := { accY with total := true }
       let stepX := analyzeFuel fuel envX envY f
       let stepY := analyzeFuel fuel envX envY g
       let nextX : AbsVal :=
         { sign := accX.sign.join stepX.sign
         , parity := accX.parity.join stepX.parity
         , total := true
         }
       let nextY : AbsVal :=
         { sign := accY.sign.join stepY.sign
         , parity := accY.parity.join stepY.parity
         , total := true
         }
       if nextX.sign = accX.sign && nextX.parity = accX.parity &&
           nextY.sign = accY.sign && nextY.parity = accY.parity then
         (nextX, nextY)
       else
         analyzeFuel.loop2Widen fuel f g steps nextX nextY) := by
  simp [analyzeFuel.loop2Widen]

theorem loop2Widen_succ_step (fuel : Nat) (f g : Prog) (accX accY : AbsVal) (steps : Nat) :
    analyzeFuel.loop2Widen fuel f g (steps + 1) accX accY =
      (let next := loop2WidenStep fuel f g accX accY
       if next.1.sign = accX.sign && next.1.parity = accX.parity &&
           next.2.sign = accY.sign && next.2.parity = accY.parity then
         next
       else
         analyzeFuel.loop2Widen fuel f g steps next.1 next.2) := by
  simp [loop2Widen_succ, loop2WidenStep]

theorem loop2WidenStep_pair_rank_le (fuel : Nat) (f g : Prog) (accX accY : AbsVal) :
    accX.pairWidenRank accY <=
      (loop2WidenStep fuel f g accX accY).1.pairWidenRank
        (loop2WidenStep fuel f g accX accY).2 := by
  simp [loop2WidenStep]
  unfold AbsVal.pairWidenRank
  have hx := AbsVal.widenRank_join_le accX
    (analyzeFuel fuel { accX with total := true } { accY with total := true } f)
  have hy := AbsVal.widenRank_join_le accY
    (analyzeFuel fuel { accX with total := true } { accY with total := true } g)
  omega

theorem loop2WidenStep_sign_accX_denote {fuel : Nat} {f g : Prog} {accX accY : AbsVal}
    {v : Int} (hacc : accX.sign.denote v) :
    (loop2WidenStep fuel f g accX accY).1.sign.denote v := by
  unfold loop2WidenStep
  exact SignInfo.join_left_sound hacc

theorem loop2WidenStep_parity_accX_denote {fuel : Nat} {f g : Prog} {accX accY : AbsVal}
    {v : Int} (hacc : accX.parity.denote v) :
    (loop2WidenStep fuel f g accX accY).1.parity.denote v := by
  unfold loop2WidenStep
  exact ParityInfo.join_left_sound hacc

theorem loop2WidenStep_sign_accY_denote {fuel : Nat} {f g : Prog} {accX accY : AbsVal}
    {v : Int} (hacc : accY.sign.denote v) :
    (loop2WidenStep fuel f g accX accY).2.sign.denote v := by
  unfold loop2WidenStep
  exact SignInfo.join_left_sound hacc

theorem loop2WidenStep_parity_accY_denote {fuel : Nat} {f g : Prog} {accX accY : AbsVal}
    {v : Int} (hacc : accY.parity.denote v) :
    (loop2WidenStep fuel f g accX accY).2.parity.denote v := by
  unfold loop2WidenStep
  exact ParityInfo.join_left_sound hacc

theorem loop2WidenStep_pair_rank_lt_of_changed (fuel : Nat) (f g : Prog)
    (accX accY : AbsVal)
    (h : (loop2WidenStep fuel f g accX accY).1.sign ≠ accX.sign ∨
      (loop2WidenStep fuel f g accX accY).1.parity ≠ accX.parity ∨
      (loop2WidenStep fuel f g accX accY).2.sign ≠ accY.sign ∨
      (loop2WidenStep fuel f g accX accY).2.parity ≠ accY.parity) :
    accX.pairWidenRank accY <
      (loop2WidenStep fuel f g accX accY).1.pairWidenRank
        (loop2WidenStep fuel f g accX accY).2 := by
  simpa [loop2WidenStep] using
    AbsVal.pairWidenRank_lt_of_join_changed accX accY
      (analyzeFuel fuel { accX with total := true } { accY with total := true } f)
      (analyzeFuel fuel { accX with total := true } { accY with total := true } g) h

theorem loop2Widen_rank_mono (fuel : Nat) (f g : Prog) :
    ∀ (steps : Nat) (accX accY : AbsVal),
      accX.pairWidenRank accY <=
        (analyzeFuel.loop2Widen fuel f g steps accX accY).1.pairWidenRank
          (analyzeFuel.loop2Widen fuel f g steps accX accY).2
  | 0, accX, accY => by simp [loop2Widen_zero]
  | steps + 1, accX, accY => by
      rw [loop2Widen_succ_step]
      let next := loop2WidenStep fuel f g accX accY
      have hnext : accX.pairWidenRank accY <= next.1.pairWidenRank next.2 := by
        simpa [next] using loop2WidenStep_pair_rank_le fuel f g accX accY
      by_cases h : next.1.sign = accX.sign && next.1.parity = accX.parity &&
          next.2.sign = accY.sign && next.2.parity = accY.parity
      · simp [h, next]
        exact hnext
      · simp [h, next]
        exact Nat.le_trans hnext (loop2Widen_rank_mono fuel f g steps next.1 next.2)

def loop2WidenStable (fuel : Nat) (f g : Prog) (accX accY : AbsVal) : Prop :=
  let next := loop2WidenStep fuel f g accX accY
  next.1.sign = accX.sign ∧ next.1.parity = accX.parity ∧
    next.2.sign = accY.sign ∧ next.2.parity = accY.parity

theorem loop2WidenStep_stable_of_stable (fuel : Nat) (f g : Prog) (accX accY : AbsVal)
    (hstable : loop2WidenStable fuel f g accX accY) :
    loop2WidenStable fuel f g
      (loop2WidenStep fuel f g accX accY).1
      (loop2WidenStep fuel f g accX accY).2 := by
  dsimp [loop2WidenStable] at hstable ⊢
  rcases hstable with ⟨hxs, hxp, hys, hyp⟩
  cases accX
  cases accY
  simp [loop2WidenStep] at hxs hxp hys hyp ⊢
  constructor
  · rw [hxs, hxp, hys, hyp]
    exact hxs
  · constructor
    · rw [hxs, hxp, hys, hyp]
      exact hxp
    · constructor
      · rw [hxs, hxp, hys, hyp]
        exact hys
      · rw [hxs, hxp, hys, hyp]
        exact hyp

theorem loop2Widen_stable_of_rank_budget (fuel : Nat) (f g : Prog) :
    ∀ (steps : Nat) (accX accY : AbsVal),
      11 <= accX.pairWidenRank accY + steps ->
      loop2WidenStable fuel f g
        (analyzeFuel.loop2Widen fuel f g steps accX accY).1
        (analyzeFuel.loop2Widen fuel f g steps accX accY).2
  | 0, accX, accY, hbudget => by
      have hle := AbsVal.pairWidenRank_le_ten accX accY
      omega
  | steps + 1, accX, accY, hbudget => by
      rw [loop2Widen_succ_step]
      let next := loop2WidenStep fuel f g accX accY
      by_cases h : next.1.sign = accX.sign && next.1.parity = accX.parity &&
          next.2.sign = accY.sign && next.2.parity = accY.parity
      · have hstable : loop2WidenStable fuel f g accX accY := by
          unfold loop2WidenStable
          simp at h
          exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
        simp [h, next]
        exact loop2WidenStep_stable_of_stable fuel f g accX accY hstable
      · have hchanged : next.1.sign ≠ accX.sign ∨ next.1.parity ≠ accX.parity ∨
            next.2.sign ≠ accY.sign ∨ next.2.parity ≠ accY.parity := by
          by_cases hxs : next.1.sign = accX.sign
          · by_cases hxp : next.1.parity = accX.parity
            · by_cases hys : next.2.sign = accY.sign
              · right; right; right
                intro hyp
                exact h (by simp [hxs, hxp, hys, hyp])
              · exact Or.inr (Or.inr (Or.inl hys))
            · exact Or.inr (Or.inl hxp)
          · exact Or.inl hxs
        have hlt := loop2WidenStep_pair_rank_lt_of_changed fuel f g accX accY hchanged
        have hltNext : accX.pairWidenRank accY < next.1.pairWidenRank next.2 := by
          simpa [next] using hlt
        have hbudgetNext : 11 <= next.1.pairWidenRank next.2 + steps := by omega
        simp [h, next]
        exact loop2Widen_stable_of_rank_budget fuel f g steps next.1 next.2 hbudgetNext

theorem loop2Widen_stable_24 (fuel : Nat) (f g : Prog) (accX accY : AbsVal) :
    loop2WidenStable fuel f g
      (analyzeFuel.loop2Widen fuel f g 24 accX accY).1
      (analyzeFuel.loop2Widen fuel f g 24 accX accY).2 := by
  apply loop2Widen_stable_of_rank_budget
  omega

theorem loop2Widen_sign_initialX_denote (fuel : Nat) (f g : Prog) :
    ∀ (steps : Nat) (initialX initialY : AbsVal) {v : Int},
      initialX.sign.denote v ->
      (analyzeFuel.loop2Widen fuel f g steps initialX initialY).1.sign.denote v
  | 0, initialX, _initialY, v, h => by simpa [loop2Widen_zero] using h
  | steps + 1, initialX, initialY, v, h => by
      rw [loop2Widen_succ_step]
      let next := loop2WidenStep fuel f g initialX initialY
      have hnext : next.1.sign.denote v := loop2WidenStep_sign_accX_denote h
      by_cases hstop : next.1.sign = initialX.sign && next.1.parity = initialX.parity &&
          next.2.sign = initialY.sign && next.2.parity = initialY.parity
      · simpa [hstop, next] using hnext
      · simp [hstop, next]
        exact loop2Widen_sign_initialX_denote fuel f g steps next.1 next.2 hnext

theorem loop2Widen_parity_initialX_denote (fuel : Nat) (f g : Prog) :
    ∀ (steps : Nat) (initialX initialY : AbsVal) {v : Int},
      initialX.parity.denote v ->
      (analyzeFuel.loop2Widen fuel f g steps initialX initialY).1.parity.denote v
  | 0, initialX, _initialY, v, h => by simpa [loop2Widen_zero] using h
  | steps + 1, initialX, initialY, v, h => by
      rw [loop2Widen_succ_step]
      let next := loop2WidenStep fuel f g initialX initialY
      have hnext : next.1.parity.denote v := loop2WidenStep_parity_accX_denote h
      by_cases hstop : next.1.sign = initialX.sign && next.1.parity = initialX.parity &&
          next.2.sign = initialY.sign && next.2.parity = initialY.parity
      · simpa [hstop, next] using hnext
      · simp [hstop, next]
        exact loop2Widen_parity_initialX_denote fuel f g steps next.1 next.2 hnext

theorem loop2Widen_sign_initialY_denote (fuel : Nat) (f g : Prog) :
    ∀ (steps : Nat) (initialX initialY : AbsVal) {v : Int},
      initialY.sign.denote v ->
      (analyzeFuel.loop2Widen fuel f g steps initialX initialY).2.sign.denote v
  | 0, _initialX, initialY, v, h => by simpa [loop2Widen_zero] using h
  | steps + 1, initialX, initialY, v, h => by
      rw [loop2Widen_succ_step]
      let next := loop2WidenStep fuel f g initialX initialY
      have hnext : next.2.sign.denote v := loop2WidenStep_sign_accY_denote h
      by_cases hstop : next.1.sign = initialX.sign && next.1.parity = initialX.parity &&
          next.2.sign = initialY.sign && next.2.parity = initialY.parity
      · simpa [hstop, next] using hnext
      · simp [hstop, next]
        exact loop2Widen_sign_initialY_denote fuel f g steps next.1 next.2 hnext

theorem loop2Widen_parity_initialY_denote (fuel : Nat) (f g : Prog) :
    ∀ (steps : Nat) (initialX initialY : AbsVal) {v : Int},
      initialY.parity.denote v ->
      (analyzeFuel.loop2Widen fuel f g steps initialX initialY).2.parity.denote v
  | 0, _initialX, initialY, v, h => by simpa [loop2Widen_zero] using h
  | steps + 1, initialX, initialY, v, h => by
      rw [loop2Widen_succ_step]
      let next := loop2WidenStep fuel f g initialX initialY
      have hnext : next.2.parity.denote v := loop2WidenStep_parity_accY_denote h
      by_cases hstop : next.1.sign = initialX.sign && next.1.parity = initialX.parity &&
          next.2.sign = initialY.sign && next.2.parity = initialY.parity
      · simpa [hstop, next] using hnext
      · simp [hstop, next]
        exact loop2Widen_parity_initialY_denote fuel f g steps next.1 next.2 hnext

theorem loop2WidenStable_sign_f_denote {fuel : Nat} {f g : Prog} {accX accY : AbsVal}
    {v : Int} (hstable : loop2WidenStable fuel f g accX accY)
    (hbody : (analyzeFuel fuel { accX with total := true } { accY with total := true } f).sign.denote v) :
    accX.sign.denote v := by
  unfold loop2WidenStable at hstable
  unfold loop2WidenStep at hstable
  exact SignInfo.denote_of_join_eq_left hstable.1 hbody

theorem loop2WidenStable_parity_f_denote {fuel : Nat} {f g : Prog} {accX accY : AbsVal}
    {v : Int} (hstable : loop2WidenStable fuel f g accX accY)
    (hbody : (analyzeFuel fuel { accX with total := true } { accY with total := true } f).parity.denote v) :
    accX.parity.denote v := by
  unfold loop2WidenStable at hstable
  unfold loop2WidenStep at hstable
  exact ParityInfo.denote_of_join_eq_left hstable.2.1 hbody

theorem loop2WidenStable_sign_g_denote {fuel : Nat} {f g : Prog} {accX accY : AbsVal}
    {v : Int} (hstable : loop2WidenStable fuel f g accX accY)
    (hbody : (analyzeFuel fuel { accX with total := true } { accY with total := true } g).sign.denote v) :
    accY.sign.denote v := by
  unfold loop2WidenStable at hstable
  unfold loop2WidenStep at hstable
  exact SignInfo.denote_of_join_eq_left hstable.2.2.1 hbody

theorem loop2WidenStable_parity_g_denote {fuel : Nat} {f g : Prog} {accX accY : AbsVal}
    {v : Int} (hstable : loop2WidenStable fuel f g accX accY)
    (hbody : (analyzeFuel fuel { accX with total := true } { accY with total := true } g).parity.denote v) :
    accY.parity.denote v := by
  unfold loop2WidenStable at hstable
  unfold loop2WidenStep at hstable
  exact ParityInfo.denote_of_join_eq_left hstable.2.2.2 hbody

theorem loop2Widen24_sign_f_denote {fuel : Nat} {f g : Prog} {initialX initialY : AbsVal}
    {v : Int}
    (hbody : (analyzeFuel fuel
      { (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).1 with total := true }
      { (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).2 with total := true } f).sign.denote v) :
    (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).1.sign.denote v :=
  loop2WidenStable_sign_f_denote (loop2Widen_stable_24 fuel f g initialX initialY) hbody

theorem loop2Widen24_parity_f_denote {fuel : Nat} {f g : Prog} {initialX initialY : AbsVal}
    {v : Int}
    (hbody : (analyzeFuel fuel
      { (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).1 with total := true }
      { (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).2 with total := true } f).parity.denote v) :
    (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).1.parity.denote v :=
  loop2WidenStable_parity_f_denote (loop2Widen_stable_24 fuel f g initialX initialY) hbody

theorem loop2Widen24_sign_g_denote {fuel : Nat} {f g : Prog} {initialX initialY : AbsVal}
    {v : Int}
    (hbody : (analyzeFuel fuel
      { (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).1 with total := true }
      { (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).2 with total := true } g).sign.denote v) :
    (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).2.sign.denote v :=
  loop2WidenStable_sign_g_denote (loop2Widen_stable_24 fuel f g initialX initialY) hbody

theorem loop2Widen24_parity_g_denote {fuel : Nat} {f g : Prog} {initialX initialY : AbsVal}
    {v : Int}
    (hbody : (analyzeFuel fuel
      { (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).1 with total := true }
      { (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).2 with total := true } g).parity.denote v) :
    (analyzeFuel.loop2Widen fuel f g 24 initialX initialY).2.parity.denote v :=
  loop2WidenStable_parity_g_denote (loop2Widen_stable_24 fuel f g initialX initialY) hbody

def analyzeWith (xVal yVal : AbsVal) (p : Prog) : AbsVal :=
  analyzeFuel (progHeight p + 1) xVal yVal p

def analyze (p : Prog) : AbsVal := analyzeWith AbsVal.nonnegUnknownParity AbsVal.zeroReg p

def signAnalysis (p : Prog) : SignInfo := (analyze p).sign
def parityAnalysis (p : Prog) : ParityInfo := (analyze p).parity
def totalAnalysis (p : Prog) : Bool := (analyze p).total

def coreOnly : Prog -> Bool
  | .node id ch =>
      match id, ch with
      | 0, [] => true
      | 1, [] => true
      | 2, [] => true
      | 3, [a, b] => coreOnly a && coreOnly b
      | 4, [a, b] => coreOnly a && coreOnly b
      | 5, [a, b] => coreOnly a && coreOnly b
      | 8, [c, t, e] => coreOnly c && coreOnly t && coreOnly e
      | 10, [] => true
      | 11, [] => true
      | _, _ => false

def CfgSignSound (xVal yVal : AbsVal) (cfg : Config) : Prop :=
  xVal.sign.denote cfg.x ∧ yVal.sign.denote cfg.y

def CfgParitySound (xVal yVal : AbsVal) (cfg : Config) : Prop :=
  xVal.parity.denote cfg.x ∧ yVal.parity.denote cfg.y

inductive CoreProg : Prog -> Prop where
  | zero : CoreProg (.node 0 [])
  | one : CoreProg (.node 1 [])
  | two : CoreProg (.node 2 [])
  | add {a b : Prog} : CoreProg a -> CoreProg b -> CoreProg (.node 3 [a, b])
  | diff {a b : Prog} : CoreProg a -> CoreProg b -> CoreProg (.node 4 [a, b])
  | mult {a b : Prog} : CoreProg a -> CoreProg b -> CoreProg (.node 5 [a, b])
  | cond {c t e : Prog} : CoreProg c -> CoreProg t -> CoreProg e -> CoreProg (.node 8 [c, t, e])
  | x : CoreProg (.node 10 [])
  | y : CoreProg (.node 11 [])

namespace CoreProg

theorem to_coreOnly : ∀ {p : Prog}, CoreProg p -> coreOnly p = true
  | _, zero => rfl
  | _, one => rfl
  | _, two => rfl
  | _, add ha hb => by simp [coreOnly, to_coreOnly ha, to_coreOnly hb]
  | _, diff ha hb => by simp [coreOnly, to_coreOnly ha, to_coreOnly hb]
  | _, mult ha hb => by simp [coreOnly, to_coreOnly ha, to_coreOnly hb]
  | _, cond hc ht he => by simp [coreOnly, to_coreOnly hc, to_coreOnly ht, to_coreOnly he]
  | _, x => rfl
  | _, y => rfl

theorem of_coreOnly : ∀ {p : Prog}, coreOnly p = true -> CoreProg p
  | .node 0 [], _ => CoreProg.zero
  | .node 1 [], _ => CoreProg.one
  | .node 2 [], _ => CoreProg.two
  | .node 3 [a, b], h => by
      simp [coreOnly] at h
      exact CoreProg.add (of_coreOnly h.1) (of_coreOnly h.2)
  | .node 4 [a, b], h => by
      simp [coreOnly] at h
      exact CoreProg.diff (of_coreOnly h.1) (of_coreOnly h.2)
  | .node 5 [a, b], h => by
      simp [coreOnly] at h
      exact CoreProg.mult (of_coreOnly h.1) (of_coreOnly h.2)
  | .node 8 [c, t, e], h => by
      simp [coreOnly] at h
      exact CoreProg.cond (of_coreOnly h.1.1) (of_coreOnly h.1.2) (of_coreOnly h.2)
  | .node 10 [], _ => CoreProg.x
  | .node 11 [], _ => CoreProg.y
  | .node id ch, h => by
      cases id with
      | zero =>
          cases ch with
          | nil => exact CoreProg.zero
          | cons _ _ => simp [coreOnly] at h
      | succ id =>
          cases id with
          | zero =>
              cases ch with
              | nil => exact CoreProg.one
              | cons _ _ => simp [coreOnly] at h
          | succ id =>
              cases id with
              | zero =>
                  cases ch with
                  | nil => exact CoreProg.two
                  | cons _ _ => simp [coreOnly] at h
              | succ id =>
                  cases id with
                  | zero =>
                      cases ch with
                      | nil => simp [coreOnly] at h
                      | cons a rest =>
                          cases rest with
                          | nil => simp [coreOnly] at h
                          | cons b rest =>
                              cases rest with
                              | nil =>
                                  simp [coreOnly] at h
                                  exact CoreProg.add (of_coreOnly h.1) (of_coreOnly h.2)
                              | cons _ _ => simp [coreOnly] at h
                  | succ id =>
                      cases id with
                      | zero =>
                          cases ch with
                          | nil => simp [coreOnly] at h
                          | cons a rest =>
                              cases rest with
                              | nil => simp [coreOnly] at h
                              | cons b rest =>
                                  cases rest with
                                  | nil =>
                                      simp [coreOnly] at h
                                      exact CoreProg.diff (of_coreOnly h.1) (of_coreOnly h.2)
                                  | cons _ _ => simp [coreOnly] at h
                      | succ id =>
                          cases id with
                          | zero =>
                              cases ch with
                              | nil => simp [coreOnly] at h
                              | cons a rest =>
                                  cases rest with
                                  | nil => simp [coreOnly] at h
                                  | cons b rest =>
                                      cases rest with
                                      | nil =>
                                          simp [coreOnly] at h
                                          exact CoreProg.mult (of_coreOnly h.1) (of_coreOnly h.2)
                                      | cons _ _ => simp [coreOnly] at h
                          | succ id =>
                              cases id with
                              | zero => simp [coreOnly] at h
                              | succ id =>
                                  cases id with
                                  | zero => simp [coreOnly] at h
                                  | succ id =>
                                      cases id with
                                      | zero =>
                                          cases ch with
                                          | nil => simp [coreOnly] at h
                                          | cons c rest =>
                                              cases rest with
                                              | nil => simp [coreOnly] at h
                                              | cons t rest =>
                                                  cases rest with
                                                  | nil => simp [coreOnly] at h
                                                  | cons e rest =>
                                                      cases rest with
                                                      | nil =>
                                                          simp [coreOnly] at h
                                                          exact CoreProg.cond
                                                            (of_coreOnly h.1.1)
                                                            (of_coreOnly h.1.2)
                                                            (of_coreOnly h.2)
                                                      | cons _ _ => simp [coreOnly] at h
                                      | succ id =>
                                          cases id with
                                          | zero => simp [coreOnly] at h
                                          | succ id =>
                                              cases id with
                                              | zero =>
                                                  cases ch with
                                                  | nil => exact CoreProg.x
                                                  | cons _ _ => simp [coreOnly] at h
                                              | succ id =>
                                                  cases id with
                                                  | zero =>
                                                      cases ch with
                                                      | nil => exact CoreProg.y
                                                      | cons _ _ => simp [coreOnly] at h
                                                  | succ _ => simp [coreOnly] at h

theorem coreOnly_iff {p : Prog} : coreOnly p = true ↔ CoreProg p :=
  ⟨of_coreOnly, to_coreOnly⟩

theorem sign_sound : ∀ {p : Prog}, CoreProg p ->
    ∀ (fuelA evalFuel : Nat) (xVal yVal : AbsVal) (cfg : Config)
      (st st' : Store) (v : Int),
      CfgSignSound xVal yVal cfg ->
      eval evalFuel orgE1Signature p cfg st = some (v, st') ->
      (analyzeFuel fuelA xVal yVal p).sign.denote v
  | _, zero, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, _hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp [eval, orgE1Signature, entryAt, listGet?, entry] at heval
              rcases heval with ⟨hv, _hst⟩
              subst v
              simp [analyzeFuel, SignInfo.denote, AbsVal.zero]
  | _, one, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, _hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp [eval, orgE1Signature, entryAt, listGet?, entry] at heval
              rcases heval with ⟨hv, _hst⟩
              subst v
              simp [analyzeFuel, SignInfo.denote, AbsVal.one]
  | _, two, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, _hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp [eval, orgE1Signature, entryAt, listGet?, entry] at heval
              rcases heval with ⟨hv, _hst⟩
              subst v
              simp [analyzeFuel, SignInfo.denote, AbsVal.two]
  | _, add ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature _ cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature _ cfg ra.2).bind
                    fun rb => some (ra.1 + rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature _ cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature _ cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.add]
                      exact signAdd_sound
                        (sign_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                        (sign_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb)
  | _, diff ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature _ cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature _ cfg ra.2).bind
                    fun rb => some (ra.1 - rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature _ cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature _ cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.diff]
                      simpa [sub_eq_add_neg] using
                        signAdd_sound
                          (sign_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                          (signNeg_sound
                            (sign_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb))
  | _, mult ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature _ cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature _ cfg ra.2).bind
                    fun rb => some (ra.1 * rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature _ cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature _ cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.mult]
                      exact signMul_sound
                        (sign_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                        (sign_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb)
  | _, cond hc ht he, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature _ cfg st).bind fun rc =>
                  if rc.1 ≤ 0 then eval evalFuel orgE1Signature _ cfg rc.2
                  else eval evalFuel orgE1Signature _ cfg rc.2) = some (v, st') at heval
              cases hrc : eval evalFuel orgE1Signature _ cfg st with
              | none =>
                  rw [hrc] at heval
                  simp at heval
              | some rc =>
                  rw [hrc] at heval
                  simp at heval
                  by_cases hle : rc.1 ≤ 0
                  · rw [if_pos hle] at heval
                    simp [analyzeFuel, AbsVal.join]
                    exact SignInfo.join_left_sound
                      (sign_sound ht fuelA evalFuel xVal yVal cfg rc.2 st' v hcfg heval)
                  · rw [if_neg hle] at heval
                    simp [analyzeFuel, AbsVal.join]
                    exact SignInfo.join_right_sound
                      (sign_sound he fuelA evalFuel xVal yVal cfg rc.2 st' v hcfg heval)
  | _, x, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp [eval, orgE1Signature, entryAt, listGet?, entry] at heval
              rcases heval with ⟨hv, _hst⟩
              subst v
              simpa [analyzeFuel] using hcfg.1
  | _, y, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp [eval, orgE1Signature, entryAt, listGet?, entry] at heval
              rcases heval with ⟨hv, _hst⟩
              subst v
              simpa [analyzeFuel] using hcfg.2

theorem parity_sound : ∀ {p : Prog}, CoreProg p ->
    ∀ (fuelA evalFuel : Nat) (xVal yVal : AbsVal) (cfg : Config)
      (st st' : Store) (v : Int),
      CfgParitySound xVal yVal cfg ->
      eval evalFuel orgE1Signature p cfg st = some (v, st') ->
      (analyzeFuel fuelA xVal yVal p).parity.denote v
  | _, zero, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, _hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp [eval, orgE1Signature, entryAt, listGet?, entry] at heval
              rcases heval with ⟨hv, _hst⟩
              subst v
              simp [analyzeFuel, AbsVal.zero, ParityInfo.denote, EvenInt]
  | _, one, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, _hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp [eval, orgE1Signature, entryAt, listGet?, entry] at heval
              rcases heval with ⟨hv, _hst⟩
              subst v
              simp [analyzeFuel, AbsVal.one, ParityInfo.denote, OddInt]
  | _, two, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, _hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp [eval, orgE1Signature, entryAt, listGet?, entry] at heval
              rcases heval with ⟨hv, _hst⟩
              subst v
              simp [analyzeFuel, AbsVal.two, ParityInfo.denote, EvenInt]
  | _, add ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature _ cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature _ cfg ra.2).bind
                    fun rb => some (ra.1 + rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature _ cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature _ cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.add]
                      exact parityAdd_sound
                        (parity_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                        (parity_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb)
  | _, diff ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature _ cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature _ cfg ra.2).bind
                    fun rb => some (ra.1 - rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature _ cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature _ cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.diff]
                      exact paritySub_sound
                        (parity_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                        (parity_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb)
  | _, mult ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature _ cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature _ cfg ra.2).bind
                    fun rb => some (ra.1 * rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature _ cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature _ cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.mult]
                      exact parityMul_sound
                        (parity_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                        (parity_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb)
  | _, cond hc ht he, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature _ cfg st).bind fun rc =>
                  if rc.1 ≤ 0 then eval evalFuel orgE1Signature _ cfg rc.2
                  else eval evalFuel orgE1Signature _ cfg rc.2) = some (v, st') at heval
              cases hrc : eval evalFuel orgE1Signature _ cfg st with
              | none =>
                  rw [hrc] at heval
                  simp at heval
              | some rc =>
                  rw [hrc] at heval
                  simp at heval
                  by_cases hle : rc.1 ≤ 0
                  · rw [if_pos hle] at heval
                    simp [analyzeFuel, AbsVal.join]
                    exact ParityInfo.join_left_sound
                      (parity_sound ht fuelA evalFuel xVal yVal cfg rc.2 st' v hcfg heval)
                  · rw [if_neg hle] at heval
                    simp [analyzeFuel, AbsVal.join]
                    exact ParityInfo.join_right_sound
                      (parity_sound he fuelA evalFuel xVal yVal cfg rc.2 st' v hcfg heval)
  | _, x, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp [eval, orgE1Signature, entryAt, listGet?, entry] at heval
              rcases heval with ⟨hv, _hst⟩
              subst v
              simpa [analyzeFuel] using hcfg.1
  | _, y, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp [eval, orgE1Signature, entryAt, listGet?, entry] at heval
              rcases heval with ⟨hv, _hst⟩
              subst v
              simpa [analyzeFuel] using hcfg.2

theorem signAnalysis_nonneg_sound_seed {p : Prog} (hp : CoreProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNonneg = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : 0 <= v := by
  apply SignInfo.provesNonneg_sound hs
  exact sign_sound hp (progHeight p + 1) fuel AbsVal.nonnegUnknownParity AbsVal.zeroReg
    (seed n) Store.zero st' v (by
      simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, SignInfo.denote, seed]
      exact hn) heval

theorem signAnalysis_pos_sound_seed {p : Prog} (hp : CoreProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesPos = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : 0 < v := by
  apply SignInfo.provesPos_sound hs
  exact sign_sound hp (progHeight p + 1) fuel AbsVal.nonnegUnknownParity AbsVal.zeroReg
    (seed n) Store.zero st' v (by
      simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, SignInfo.denote, seed]
      exact hn) heval

theorem parityAnalysis_even_sound_seed {p : Prog} (hp : CoreProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hs : (parityAnalysis p).provesEven = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : EvenInt v := by
  apply ParityInfo.provesEven_sound hs
  exact parity_sound hp (progHeight p + 1) fuel AbsVal.nonnegUnknownParity AbsVal.zeroReg
    (seed n) Store.zero st' v (by
      simp [CfgParitySound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, ParityInfo.denote, EvenInt,
        seed]) heval

theorem analyzeFuel_total_of_core : ∀ {p : Prog}, CoreProg p ->
    ∀ {fuel : Nat} {xVal yVal : AbsVal},
      progHeight p < fuel -> xVal.total = true -> yVal.total = true ->
      (analyzeFuel fuel xVal yVal p).total = true
  | .node 0 [], zero, fuel, xVal, yVal, hfuel, _hx, _hy => by
      cases fuel with
      | zero => omega
      | succ fuel => simp [analyzeFuel, AbsVal.zero]
  | .node 1 [], one, fuel, xVal, yVal, hfuel, _hx, _hy => by
      cases fuel with
      | zero => omega
      | succ fuel => simp [analyzeFuel, AbsVal.one]
  | .node 2 [], two, fuel, xVal, yVal, hfuel, _hx, _hy => by
      cases fuel with
      | zero => omega
      | succ fuel => simp [analyzeFuel, AbsVal.two]
  | .node 3 [a, b], add ha hb, fuel, xVal, yVal, hfuel, hx, hy => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfa : progHeight a < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight a <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_left _ _
            omega
          have hfb : progHeight b < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight b <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_right _ _
            omega
          simp [analyzeFuel, AbsVal.add, analyzeFuel_total_of_core ha hfa hx hy,
            analyzeFuel_total_of_core hb hfb hx hy]
  | .node 4 [a, b], diff ha hb, fuel, xVal, yVal, hfuel, hx, hy => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfa : progHeight a < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight a <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_left _ _
            omega
          have hfb : progHeight b < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight b <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_right _ _
            omega
          simp [analyzeFuel, AbsVal.diff, analyzeFuel_total_of_core ha hfa hx hy,
            analyzeFuel_total_of_core hb hfb hx hy]
  | .node 5 [a, b], mult ha hb, fuel, xVal, yVal, hfuel, hx, hy => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfa : progHeight a < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight a <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_left _ _
            omega
          have hfb : progHeight b < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight b <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_right _ _
            omega
          simp [analyzeFuel, AbsVal.mult, analyzeFuel_total_of_core ha hfa hx hy,
            analyzeFuel_total_of_core hb hfb hx hy]
  | .node 8 [c, t, e], cond hc ht he, fuel, xVal, yVal, hfuel, hx, hy => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfc : progHeight c < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle :
                progHeight c <= Nat.max (progHeight c) (Nat.max (progHeight t) (progHeight e)) :=
              Nat.le_max_left _ _
            omega
          have hft : progHeight t < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle₁ : progHeight t <= Nat.max (progHeight t) (progHeight e) :=
              Nat.le_max_left _ _
            have hle₂ : Nat.max (progHeight t) (progHeight e) <=
                Nat.max (progHeight c) (Nat.max (progHeight t) (progHeight e)) :=
              Nat.le_max_right _ _
            omega
          have hfe : progHeight e < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle₁ : progHeight e <= Nat.max (progHeight t) (progHeight e) :=
              Nat.le_max_right _ _
            have hle₂ : Nat.max (progHeight t) (progHeight e) <=
                Nat.max (progHeight c) (Nat.max (progHeight t) (progHeight e)) :=
              Nat.le_max_right _ _
            omega
          simp [analyzeFuel, AbsVal.join, analyzeFuel_total_of_core hc hfc hx hy,
            analyzeFuel_total_of_core ht hft hx hy,
            analyzeFuel_total_of_core he hfe hx hy]
  | .node 10 [], x, fuel, xVal, yVal, hfuel, hx, _hy => by
      cases fuel with
      | zero => omega
      | succ fuel => simp [analyzeFuel, hx]
  | .node 11 [], y, fuel, xVal, yVal, hfuel, _hx, hy => by
      cases fuel with
      | zero => omega
      | succ fuel => simp [analyzeFuel, hy]

theorem totalAnalysis_true {p : Prog} (hp : CoreProg p) : totalAnalysis p = true := by
  exact analyzeFuel_total_of_core hp (by omega)
    (by simp [AbsVal.nonnegUnknownParity])
    (by simp [AbsVal.zeroReg])

theorem eval_defined_of_fuel : ∀ {p : Prog}, CoreProg p ->
    ∀ {fuel : Nat} (cfg : Config) (st : Store),
      progHeight p < fuel -> ∃ v st', eval fuel orgE1Signature p cfg st = some (v, st')
  | .node 0 [], zero, fuel, cfg, st, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨0, st, by simp [eval, orgE1Signature, entryAt, listGet?, entry]⟩
  | .node 1 [], one, fuel, cfg, st, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨1, st, by simp [eval, orgE1Signature, entryAt, listGet?, entry]⟩
  | .node 2 [], two, fuel, cfg, st, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨2, st, by simp [eval, orgE1Signature, entryAt, listGet?, entry]⟩
  | .node 3 [a, b], add ha hb, fuel, cfg, st, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfa : progHeight a < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight a <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_left _ _
            omega
          have hfb : progHeight b < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight b <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_right _ _
            omega
          rcases eval_defined_of_fuel ha cfg st hfa with ⟨va, sta, hra⟩
          rcases eval_defined_of_fuel hb cfg sta hfb with ⟨vb, stb, hrb⟩
          refine ⟨va + vb, stb, ?_⟩
          simp only [eval]
          simp only [orgE1Signature, entryAt, listGet?, entry]
          change ((eval fuel orgE1Signature a cfg st).bind fun ra =>
              (eval fuel orgE1Signature b cfg ra.2).bind
                fun rb => some (ra.1 + rb.1, rb.2)) = some (va + vb, stb)
          rw [hra]
          simp
          rw [hrb]
          simp
  | .node 4 [a, b], diff ha hb, fuel, cfg, st, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfa : progHeight a < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight a <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_left _ _
            omega
          have hfb : progHeight b < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight b <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_right _ _
            omega
          rcases eval_defined_of_fuel ha cfg st hfa with ⟨va, sta, hra⟩
          rcases eval_defined_of_fuel hb cfg sta hfb with ⟨vb, stb, hrb⟩
          refine ⟨va - vb, stb, ?_⟩
          simp only [eval]
          simp only [orgE1Signature, entryAt, listGet?, entry]
          change ((eval fuel orgE1Signature a cfg st).bind fun ra =>
              (eval fuel orgE1Signature b cfg ra.2).bind
                fun rb => some (ra.1 - rb.1, rb.2)) = some (va - vb, stb)
          rw [hra]
          simp
          rw [hrb]
          simp
  | .node 5 [a, b], mult ha hb, fuel, cfg, st, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfa : progHeight a < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight a <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_left _ _
            omega
          have hfb : progHeight b < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight b <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_right _ _
            omega
          rcases eval_defined_of_fuel ha cfg st hfa with ⟨va, sta, hra⟩
          rcases eval_defined_of_fuel hb cfg sta hfb with ⟨vb, stb, hrb⟩
          refine ⟨va * vb, stb, ?_⟩
          simp only [eval]
          simp only [orgE1Signature, entryAt, listGet?, entry]
          change ((eval fuel orgE1Signature a cfg st).bind fun ra =>
              (eval fuel orgE1Signature b cfg ra.2).bind
                fun rb => some (ra.1 * rb.1, rb.2)) = some (va * vb, stb)
          rw [hra]
          simp
          rw [hrb]
          simp
  | .node 8 [c, t, e], cond hc ht he, fuel, cfg, st, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfc : progHeight c < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle :
                progHeight c <= Nat.max (progHeight c) (Nat.max (progHeight t) (progHeight e)) :=
              Nat.le_max_left _ _
            omega
          have hft : progHeight t < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle₁ : progHeight t <= Nat.max (progHeight t) (progHeight e) :=
              Nat.le_max_left _ _
            have hle₂ : Nat.max (progHeight t) (progHeight e) <=
                Nat.max (progHeight c) (Nat.max (progHeight t) (progHeight e)) :=
              Nat.le_max_right _ _
            omega
          have hfe : progHeight e < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle₁ : progHeight e <= Nat.max (progHeight t) (progHeight e) :=
              Nat.le_max_right _ _
            have hle₂ : Nat.max (progHeight t) (progHeight e) <=
                Nat.max (progHeight c) (Nat.max (progHeight t) (progHeight e)) :=
              Nat.le_max_right _ _
            omega
          rcases eval_defined_of_fuel hc cfg st hfc with ⟨vc, stc, hrc⟩
          by_cases hle : vc <= 0
          · rcases eval_defined_of_fuel ht cfg stc hft with ⟨vt, stt, hrt⟩
            refine ⟨vt, stt, ?_⟩
            simp only [eval]
            simp only [orgE1Signature, entryAt, listGet?, entry]
            change ((eval fuel orgE1Signature c cfg st).bind fun rc =>
                if rc.1 <= 0 then eval fuel orgE1Signature t cfg rc.2
                else eval fuel orgE1Signature e cfg rc.2) = some (vt, stt)
            rw [hrc]
            simp [hle, hrt]
          · rcases eval_defined_of_fuel he cfg stc hfe with ⟨ve, ste, hre⟩
            refine ⟨ve, ste, ?_⟩
            simp only [eval]
            simp only [orgE1Signature, entryAt, listGet?, entry]
            change ((eval fuel orgE1Signature c cfg st).bind fun rc =>
                if rc.1 <= 0 then eval fuel orgE1Signature t cfg rc.2
                else eval fuel orgE1Signature e cfg rc.2) = some (ve, ste)
            rw [hrc]
            simp [hle, hre]
  | .node 10 [], x, fuel, cfg, st, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨cfg.x, st, by simp [eval, orgE1Signature, entryAt, listGet?, entry]⟩
  | .node 11 [], y, fuel, cfg, st, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨cfg.y, st, by simp [eval, orgE1Signature, entryAt, listGet?, entry]⟩

theorem eval_defined_at_analysis_fuel {p : Prog} (hp : CoreProg p)
    (cfg : Config) (st : Store) :
    ∃ v st', eval (progHeight p + 1) orgE1Signature p cfg st = some (v, st') :=
  eval_defined_of_fuel hp cfg st (by omega)

theorem totalAnalysis_sound {p : Prog} (hp : CoreProg p)
    (cfg : Config) (st : Store) :
    totalAnalysis p = true ∧
      ∃ v st', eval (progHeight p + 1) orgE1Signature p cfg st = some (v, st') :=
  ⟨totalAnalysis_true hp, eval_defined_at_analysis_fuel hp cfg st⟩

theorem signAnalysis_nonneg_sound_seed_of_coreOnly {p : Prog}
    (hcore : coreOnly p = true) {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNonneg = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : 0 <= v :=
  signAnalysis_nonneg_sound_seed (of_coreOnly hcore) hn hs heval

theorem signAnalysis_pos_sound_seed_of_coreOnly {p : Prog}
    (hcore : coreOnly p = true) {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesPos = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : 0 < v :=
  signAnalysis_pos_sound_seed (of_coreOnly hcore) hn hs heval

theorem parityAnalysis_even_sound_seed_of_coreOnly {p : Prog}
    (hcore : coreOnly p = true) {fuel : Nat} {n v : Int} {st' : Store}
    (hs : (parityAnalysis p).provesEven = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : EvenInt v :=
  parityAnalysis_even_sound_seed (of_coreOnly hcore) hs heval

theorem totalAnalysis_sound_of_coreOnly {p : Prog}
    (hcore : coreOnly p = true) (cfg : Config) (st : Store) :
    totalAnalysis p = true ∧
      ∃ v st', eval (progHeight p + 1) orgE1Signature p cfg st = some (v, st') :=
  totalAnalysis_sound (of_coreOnly hcore) cfg st

theorem loopIter_defined_of_core {body : Prog} (hbody : CoreProg body) :
    ∀ {fuel k : Nat} (x1 x2 x3 : Int) (st : Store),
      progHeight body + k + 1 <= fuel ->
      ∃ v st', loopIter fuel orgE1Signature body k x1 x2 x3 st = some (v, st')
  | 0, _k, _x1, _x2, _x3, _st, hfuel => by omega
  | fuel + 1, 0, x1, _x2, _x3, st, _hfuel => by
      exact ⟨x1, st, by simp [loopIter]⟩
  | fuel + 1, k + 1, x1, x2, x3, st, hfuel => by
      have hbodyFuel : progHeight body < fuel := by omega
      rcases eval_defined_of_fuel hbody { x := x1, y := x2, z := x3 } st hbodyFuel with
        ⟨vf, stf, hf⟩
      have hrecFuel : progHeight body + k + 1 <= fuel := by omega
      rcases loopIter_defined_of_core hbody vf (x2 + 1) x3 stf hrecFuel with
        ⟨v, st', hloop⟩
      refine ⟨v, st', ?_⟩
      simp only [loopIter]
      rw [hf]
      simp
      exact hloop

theorem eval_loop_defined_of_core_parts {fuel : Nat} {body count init : Prog}
    (hbody : CoreProg body) {cfg : Config} {st stCount stInit : Store} {cnt initVal : Int}
    (hcount : eval fuel orgE1Signature count cfg st = some (cnt, stCount))
    (hinit : eval fuel orgE1Signature init cfg stCount = some (initVal, stInit))
    (hfuel : progHeight body + cnt.toNat + 1 <= fuel) :
    ∃ v st', eval (fuel + 1) orgE1Signature (.node 9 [body, count, init]) cfg st =
      some (v, st') := by
  rcases loopIter_defined_of_core hbody initVal 1 initVal stInit hfuel with ⟨v, st', hloop⟩
  refine ⟨v, st', ?_⟩
  simp only [eval]
  simp only [orgE1Signature, entryAt, listGet?, entry]
  change ((eval fuel orgE1Signature count cfg st).bind fun rn =>
      (eval fuel orgE1Signature init cfg rn.2).bind fun rx0 =>
        loopIter fuel orgE1Signature body rn.1.toNat rx0.1 1 rx0.1 rx0.2) =
      some (v, st')
  rw [hcount]
  simp
  rw [hinit]
  simp
  exact hloop

theorem loop2Iter_defined_of_core {f g : Prog} (hf : CoreProg f) (hg : CoreProg g) :
    ∀ {fuel k : Nat} (x1 x2 x3 : Int) (st : Store),
      progHeight f + k + 1 <= fuel ->
      progHeight g + k + 1 <= fuel ->
      ∃ v st', loop2Iter fuel orgE1Signature f g k x1 x2 x3 st = some (v, st')
  | 0, _k, _x1, _x2, _x3, _st, hfuel, _gfuel => by omega
  | fuel + 1, 0, x1, _x2, _x3, st, _hfuel, _hgfuel => by
      exact ⟨x1, st, by simp [loop2Iter]⟩
  | fuel + 1, k + 1, x1, x2, x3, st, hfuel, hgfuel => by
      have hfFuel : progHeight f < fuel := by omega
      have hgFuel : progHeight g < fuel := by omega
      rcases eval_defined_of_fuel hf { x := x1, y := x2, z := x3 } st hfFuel with
        ⟨vf, stf, hrf⟩
      rcases eval_defined_of_fuel hg { x := x1, y := x2, z := x3 } stf hgFuel with
        ⟨vg, stg, hrg⟩
      have hrecF : progHeight f + k + 1 <= fuel := by omega
      have hrecG : progHeight g + k + 1 <= fuel := by omega
      rcases loop2Iter_defined_of_core hf hg vf vg (x3 + 1) stg hrecF hrecG with
        ⟨v, st', hloop⟩
      refine ⟨v, st', ?_⟩
      simp only [loop2Iter]
      rw [hrf]
      simp
      rw [hrg]
      simp
      exact hloop

theorem eval_loop2_defined_of_core_parts {fuel : Nat} {f g count a b : Prog}
    (hf : CoreProg f) (hg : CoreProg g) {cfg : Config} {st stCount stA stB : Store}
    {cnt aVal bVal : Int}
    (hcount : eval fuel orgE1Signature count cfg st = some (cnt, stCount))
    (haEval : eval fuel orgE1Signature a cfg stCount = some (aVal, stA))
    (hbEval : eval fuel orgE1Signature b cfg stA = some (bVal, stB))
    (hfFuel : progHeight f + cnt.toNat + 1 <= fuel)
    (hgFuel : progHeight g + cnt.toNat + 1 <= fuel) :
    ∃ v st', eval (fuel + 1) orgE1Signature (.node 13 [f, g, count, a, b]) cfg st =
      some (v, st') := by
  rcases loop2Iter_defined_of_core hf hg aVal bVal 1 stB hfFuel hgFuel with
    ⟨v, st', hloop⟩
  refine ⟨v, st', ?_⟩
  simp only [eval]
  simp only [orgE1Signature, entryAt, listGet?, entry]
  change ((eval fuel orgE1Signature count cfg st).bind fun rn =>
      (eval fuel orgE1Signature a cfg rn.2).bind fun ra =>
        (eval fuel orgE1Signature b cfg ra.2).bind fun rb =>
          loop2Iter fuel orgE1Signature f g rn.1.toNat ra.1 rb.1 1 rb.2) =
      some (v, st')
  rw [hcount]
  simp
  rw [haEval]
  simp
  rw [hbEval]
  simp
  exact hloop

end CoreProg

/-! ## Loop evaluator transfer -/

theorem loopIter_sign_denote_of_stable {fuelA : Nat} {body : Prog} {acc : AbsVal}
    (hbody : CoreProg body)
    (hstable : loopWidenStable fuelA body AbsVal.nonnegUnknownParity acc) :
    ∀ (evalFuel k : Nat) (x1 x2 x3 : Int) (st st' : Store) (v : Int),
      acc.sign.denote x1 ->
      0 <= x2 ->
      loopIter evalFuel orgE1Signature body k x1 x2 x3 st = some (v, st') ->
      acc.sign.denote v
  | 0, _k, _x1, _x2, _x3, _st, _st', _v, _hacc, _hx2, hloop => by
      simp [loopIter] at hloop
  | fuel + 1, 0, x1, _x2, _x3, _st, _st', v, hacc, _hx2, hloop => by
      simp [loopIter] at hloop
      rcases hloop with ⟨hv, _hst⟩
      subst v
      exact hacc
  | fuel + 1, k + 1, x1, x2, x3, st, st', v, hacc, hx2, hloop => by
      simp only [loopIter] at hloop
      change ((eval fuel orgE1Signature body { x := x1, y := x2, z := x3 } st).bind fun rf =>
          loopIter fuel orgE1Signature body k rf.1 (x2 + 1) x3 rf.2) = some (v, st') at hloop
      cases hrf : eval fuel orgE1Signature body { x := x1, y := x2, z := x3 } st with
      | none =>
          rw [hrf] at hloop
          simp at hloop
      | some rf =>
          rw [hrf] at hloop
          simp at hloop
          have hbodyDenote :
              (analyzeFuel fuelA { acc with total := true } AbsVal.nonnegUnknownParity body).sign.denote
                rf.1 := by
            exact CoreProg.sign_sound hbody fuelA fuel { acc with total := true }
              AbsVal.nonnegUnknownParity { x := x1, y := x2, z := x3 } st rf.2 rf.1
              (by
                simp [CfgSignSound, AbsVal.nonnegUnknownParity, SignInfo.denote]
                exact ⟨hacc, hx2⟩)
              hrf
          have hnext : acc.sign.denote rf.1 :=
            loopWidenStable_sign_body_denote hstable hbodyDenote
          exact loopIter_sign_denote_of_stable hbody hstable fuel k rf.1 (x2 + 1) x3
            rf.2 st' v hnext (by omega) hloop

theorem loopIter_parity_denote_of_stable {fuelA : Nat} {body : Prog} {acc : AbsVal}
    (hbody : CoreProg body)
    (hstable : loopWidenStable fuelA body AbsVal.nonnegUnknownParity acc) :
    ∀ (evalFuel k : Nat) (x1 x2 x3 : Int) (st st' : Store) (v : Int),
      acc.parity.denote x1 ->
      loopIter evalFuel orgE1Signature body k x1 x2 x3 st = some (v, st') ->
      acc.parity.denote v
  | 0, _k, _x1, _x2, _x3, _st, _st', _v, _hacc, hloop => by
      simp [loopIter] at hloop
  | fuel + 1, 0, x1, _x2, _x3, _st, _st', v, hacc, hloop => by
      simp [loopIter] at hloop
      rcases hloop with ⟨hv, _hst⟩
      subst v
      exact hacc
  | fuel + 1, k + 1, x1, x2, x3, st, st', v, hacc, hloop => by
      simp only [loopIter] at hloop
      change ((eval fuel orgE1Signature body { x := x1, y := x2, z := x3 } st).bind fun rf =>
          loopIter fuel orgE1Signature body k rf.1 (x2 + 1) x3 rf.2) = some (v, st') at hloop
      cases hrf : eval fuel orgE1Signature body { x := x1, y := x2, z := x3 } st with
      | none =>
          rw [hrf] at hloop
          simp at hloop
      | some rf =>
          rw [hrf] at hloop
          simp at hloop
          have hbodyDenote :
              (analyzeFuel fuelA { acc with total := true } AbsVal.nonnegUnknownParity body).parity.denote
                rf.1 := by
            exact CoreProg.parity_sound hbody fuelA fuel { acc with total := true }
              AbsVal.nonnegUnknownParity { x := x1, y := x2, z := x3 } st rf.2 rf.1
              (by
                simp [CfgParitySound, AbsVal.nonnegUnknownParity, ParityInfo.denote]
                exact hacc)
              hrf
          have hnext : acc.parity.denote rf.1 :=
            loopWidenStable_parity_body_denote hstable hbodyDenote
          exact loopIter_parity_denote_of_stable hbody hstable fuel k rf.1 (x2 + 1) x3
            rf.2 st' v hnext hloop

theorem loop_sign_sound_core_body_init {body count init : Prog}
    (hbody : CoreProg body) (hinit : CoreProg init) :
    ∀ (fuelA evalFuel : Nat) (xVal yVal : AbsVal) (cfg : Config)
      (st st' : Store) (v : Int),
      CfgSignSound xVal yVal cfg ->
      eval evalFuel orgE1Signature (.node 9 [body, count, init]) cfg st = some (v, st') ->
      (analyzeFuel fuelA xVal yVal (.node 9 [body, count, init])).sign.denote v
  | 0, _evalFuel, _xVal, _yVal, _cfg, _st, _st', _v, _hcfg, _heval => by
      simp [analyzeFuel, AbsVal.top, SignInfo.denote]
  | fuelA + 1, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases evalFuel with
      | zero => simp [eval] at heval
      | succ evalFuel =>
          simp only [eval] at heval
          simp only [orgE1Signature, entryAt, listGet?, entry] at heval
          change ((eval evalFuel orgE1Signature count cfg st).bind fun rn =>
              (eval evalFuel orgE1Signature init cfg rn.2).bind fun rx0 =>
                loopIter evalFuel orgE1Signature body rn.1.toNat rx0.1 1 rx0.1 rx0.2) =
              some (v, st') at heval
          cases hrn : eval evalFuel orgE1Signature count cfg st with
          | none =>
              rw [hrn] at heval
              simp at heval
          | some rn =>
              rw [hrn] at heval
              simp at heval
              cases hrx0 : eval evalFuel orgE1Signature init cfg rn.2 with
              | none =>
                  rw [hrx0] at heval
                  simp at heval
              | some rx0 =>
                  rw [hrx0] at heval
                  simp at heval
                  let initial := analyzeFuel fuelA xVal yVal init
                  let acc := analyzeFuel.loopWiden fuelA body AbsVal.nonnegUnknownParity 24 initial
                  have hinitDenote : initial.sign.denote rx0.1 := by
                    exact CoreProg.sign_sound hinit fuelA evalFuel xVal yVal cfg rn.2 rx0.2
                      rx0.1 hcfg hrx0
                  have haccInitial : acc.sign.denote rx0.1 := by
                    exact loopWiden_sign_initial_denote fuelA body AbsVal.nonnegUnknownParity 24
                      initial hinitDenote
                  have hloopDenote : acc.sign.denote v := by
                    exact loopIter_sign_denote_of_stable hbody
                      (loopWiden_stable_24 fuelA body AbsVal.nonnegUnknownParity initial)
                      evalFuel rn.1.toNat rx0.1 1 rx0.1 rx0.2 st' v
                      haccInitial (by omega) heval
                  simpa [analyzeFuel, initial, acc] using hloopDenote

theorem loop_parity_sound_core_body_init {body count init : Prog}
    (hbody : CoreProg body) (hinit : CoreProg init) :
    ∀ (fuelA evalFuel : Nat) (xVal yVal : AbsVal) (cfg : Config)
      (st st' : Store) (v : Int),
      CfgParitySound xVal yVal cfg ->
      eval evalFuel orgE1Signature (.node 9 [body, count, init]) cfg st = some (v, st') ->
      (analyzeFuel fuelA xVal yVal (.node 9 [body, count, init])).parity.denote v
  | 0, _evalFuel, _xVal, _yVal, _cfg, _st, _st', _v, _hcfg, _heval => by
      simp [analyzeFuel, AbsVal.top, ParityInfo.denote]
  | fuelA + 1, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases evalFuel with
      | zero => simp [eval] at heval
      | succ evalFuel =>
          simp only [eval] at heval
          simp only [orgE1Signature, entryAt, listGet?, entry] at heval
          change ((eval evalFuel orgE1Signature count cfg st).bind fun rn =>
              (eval evalFuel orgE1Signature init cfg rn.2).bind fun rx0 =>
                loopIter evalFuel orgE1Signature body rn.1.toNat rx0.1 1 rx0.1 rx0.2) =
              some (v, st') at heval
          cases hrn : eval evalFuel orgE1Signature count cfg st with
          | none =>
              rw [hrn] at heval
              simp at heval
          | some rn =>
              rw [hrn] at heval
              simp at heval
              cases hrx0 : eval evalFuel orgE1Signature init cfg rn.2 with
              | none =>
                  rw [hrx0] at heval
                  simp at heval
              | some rx0 =>
                  rw [hrx0] at heval
                  simp at heval
                  let initial := analyzeFuel fuelA xVal yVal init
                  let acc := analyzeFuel.loopWiden fuelA body AbsVal.nonnegUnknownParity 24 initial
                  have hinitDenote : initial.parity.denote rx0.1 := by
                    exact CoreProg.parity_sound hinit fuelA evalFuel xVal yVal cfg rn.2 rx0.2
                      rx0.1 hcfg hrx0
                  have haccInitial : acc.parity.denote rx0.1 := by
                    exact loopWiden_parity_initial_denote fuelA body AbsVal.nonnegUnknownParity 24
                      initial hinitDenote
                  have hloopDenote : acc.parity.denote v := by
                    exact loopIter_parity_denote_of_stable hbody
                      (loopWiden_stable_24 fuelA body AbsVal.nonnegUnknownParity initial)
                      evalFuel rn.1.toNat rx0.1 1 rx0.1 rx0.2 st' v
                      haccInitial heval
                  simpa [analyzeFuel, initial, acc] using hloopDenote

theorem loop2Iter_sign_denote_of_stable {fuelA : Nat} {f g : Prog} {accX accY : AbsVal}
    (hf : CoreProg f) (hg : CoreProg g)
    (hstable : loop2WidenStable fuelA f g accX accY) :
    ∀ (evalFuel k : Nat) (x1 x2 x3 : Int) (st st' : Store) (v : Int),
      accX.sign.denote x1 ->
      accY.sign.denote x2 ->
      loop2Iter evalFuel orgE1Signature f g k x1 x2 x3 st = some (v, st') ->
      accX.sign.denote v
  | 0, _k, _x1, _x2, _x3, _st, _st', _v, _hx, _hy, hloop => by
      simp [loop2Iter] at hloop
  | fuel + 1, 0, x1, _x2, _x3, _st, _st', v, hx, _hy, hloop => by
      simp [loop2Iter] at hloop
      rcases hloop with ⟨hv, _hst⟩
      subst v
      exact hx
  | fuel + 1, k + 1, x1, x2, x3, st, st', v, hx, hy, hloop => by
      simp only [loop2Iter] at hloop
      change ((eval fuel orgE1Signature f { x := x1, y := x2, z := x3 } st).bind fun rf =>
          (eval fuel orgE1Signature g { x := x1, y := x2, z := x3 } rf.2).bind fun rg =>
            loop2Iter fuel orgE1Signature f g k rf.1 rg.1 (x3 + 1) rg.2) =
          some (v, st') at hloop
      cases hrf : eval fuel orgE1Signature f { x := x1, y := x2, z := x3 } st with
      | none =>
          rw [hrf] at hloop
          simp at hloop
      | some rf =>
          rw [hrf] at hloop
          simp at hloop
          cases hrg : eval fuel orgE1Signature g { x := x1, y := x2, z := x3 } rf.2 with
          | none =>
              rw [hrg] at hloop
              simp at hloop
          | some rg =>
              rw [hrg] at hloop
              simp at hloop
              have hfx :
                  (analyzeFuel fuelA { accX with total := true }
                    { accY with total := true } f).sign.denote rf.1 := by
                exact CoreProg.sign_sound hf fuelA fuel { accX with total := true }
                  { accY with total := true } { x := x1, y := x2, z := x3 }
                  st rf.2 rf.1
                  (by
                    simp [CfgSignSound]
                    exact ⟨hx, hy⟩)
                  hrf
              have hgy :
                  (analyzeFuel fuelA { accX with total := true }
                    { accY with total := true } g).sign.denote rg.1 := by
                exact CoreProg.sign_sound hg fuelA fuel { accX with total := true }
                  { accY with total := true } { x := x1, y := x2, z := x3 }
                  rf.2 rg.2 rg.1
                  (by
                    simp [CfgSignSound]
                    exact ⟨hx, hy⟩)
                  hrg
              have hnextX : accX.sign.denote rf.1 :=
                loop2WidenStable_sign_f_denote hstable hfx
              have hnextY : accY.sign.denote rg.1 :=
                loop2WidenStable_sign_g_denote hstable hgy
              exact loop2Iter_sign_denote_of_stable hf hg hstable fuel k rf.1 rg.1
                (x3 + 1) rg.2 st' v hnextX hnextY hloop

theorem loop2Iter_parity_denote_of_stable {fuelA : Nat} {f g : Prog} {accX accY : AbsVal}
    (hf : CoreProg f) (hg : CoreProg g)
    (hstable : loop2WidenStable fuelA f g accX accY) :
    ∀ (evalFuel k : Nat) (x1 x2 x3 : Int) (st st' : Store) (v : Int),
      accX.parity.denote x1 ->
      accY.parity.denote x2 ->
      loop2Iter evalFuel orgE1Signature f g k x1 x2 x3 st = some (v, st') ->
      accX.parity.denote v
  | 0, _k, _x1, _x2, _x3, _st, _st', _v, _hx, _hy, hloop => by
      simp [loop2Iter] at hloop
  | fuel + 1, 0, x1, _x2, _x3, _st, _st', v, hx, _hy, hloop => by
      simp [loop2Iter] at hloop
      rcases hloop with ⟨hv, _hst⟩
      subst v
      exact hx
  | fuel + 1, k + 1, x1, x2, x3, st, st', v, hx, hy, hloop => by
      simp only [loop2Iter] at hloop
      change ((eval fuel orgE1Signature f { x := x1, y := x2, z := x3 } st).bind fun rf =>
          (eval fuel orgE1Signature g { x := x1, y := x2, z := x3 } rf.2).bind fun rg =>
            loop2Iter fuel orgE1Signature f g k rf.1 rg.1 (x3 + 1) rg.2) =
          some (v, st') at hloop
      cases hrf : eval fuel orgE1Signature f { x := x1, y := x2, z := x3 } st with
      | none =>
          rw [hrf] at hloop
          simp at hloop
      | some rf =>
          rw [hrf] at hloop
          simp at hloop
          cases hrg : eval fuel orgE1Signature g { x := x1, y := x2, z := x3 } rf.2 with
          | none =>
              rw [hrg] at hloop
              simp at hloop
          | some rg =>
              rw [hrg] at hloop
              simp at hloop
              have hfx :
                  (analyzeFuel fuelA { accX with total := true }
                    { accY with total := true } f).parity.denote rf.1 := by
                exact CoreProg.parity_sound hf fuelA fuel { accX with total := true }
                  { accY with total := true } { x := x1, y := x2, z := x3 }
                  st rf.2 rf.1
                  (by
                    simp [CfgParitySound]
                    exact ⟨hx, hy⟩)
                  hrf
              have hgy :
                  (analyzeFuel fuelA { accX with total := true }
                    { accY with total := true } g).parity.denote rg.1 := by
                exact CoreProg.parity_sound hg fuelA fuel { accX with total := true }
                  { accY with total := true } { x := x1, y := x2, z := x3 }
                  rf.2 rg.2 rg.1
                  (by
                    simp [CfgParitySound]
                    exact ⟨hx, hy⟩)
                  hrg
              have hnextX : accX.parity.denote rf.1 :=
                loop2WidenStable_parity_f_denote hstable hfx
              have hnextY : accY.parity.denote rg.1 :=
                loop2WidenStable_parity_g_denote hstable hgy
              exact loop2Iter_parity_denote_of_stable hf hg hstable fuel k rf.1 rg.1
                (x3 + 1) rg.2 st' v hnextX hnextY hloop

theorem loop2_sign_sound_core_body_init {f g count a b : Prog}
    (hf : CoreProg f) (hg : CoreProg g) (ha : CoreProg a) (hb : CoreProg b) :
    ∀ (fuelA evalFuel : Nat) (xVal yVal : AbsVal) (cfg : Config)
      (st st' : Store) (v : Int),
      CfgSignSound xVal yVal cfg ->
      eval evalFuel orgE1Signature (.node 13 [f, g, count, a, b]) cfg st = some (v, st') ->
      (analyzeFuel fuelA xVal yVal (.node 13 [f, g, count, a, b])).sign.denote v
  | 0, _evalFuel, _xVal, _yVal, _cfg, _st, _st', _v, _hcfg, _heval => by
      simp [analyzeFuel, AbsVal.top, SignInfo.denote]
  | fuelA + 1, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases evalFuel with
      | zero => simp [eval] at heval
      | succ evalFuel =>
          simp only [eval] at heval
          simp only [orgE1Signature, entryAt, listGet?, entry] at heval
          change ((eval evalFuel orgE1Signature count cfg st).bind fun rn =>
              (eval evalFuel orgE1Signature a cfg rn.2).bind fun ra =>
                (eval evalFuel orgE1Signature b cfg ra.2).bind fun rb =>
                  loop2Iter evalFuel orgE1Signature f g rn.1.toNat ra.1 rb.1 1 rb.2) =
              some (v, st') at heval
          cases hrn : eval evalFuel orgE1Signature count cfg st with
          | none =>
              rw [hrn] at heval
              simp at heval
          | some rn =>
              rw [hrn] at heval
              simp at heval
              cases hra : eval evalFuel orgE1Signature a cfg rn.2 with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature b cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      let initialX := analyzeFuel fuelA xVal yVal a
                      let initialY := analyzeFuel fuelA xVal yVal b
                      let acc := analyzeFuel.loop2Widen fuelA f g 24 initialX initialY
                      have hinitX : initialX.sign.denote ra.1 := by
                        exact CoreProg.sign_sound ha fuelA evalFuel xVal yVal cfg rn.2
                          ra.2 ra.1 hcfg hra
                      have hinitY : initialY.sign.denote rb.1 := by
                        exact CoreProg.sign_sound hb fuelA evalFuel xVal yVal cfg ra.2
                          rb.2 rb.1 hcfg hrb
                      have haccX : acc.1.sign.denote ra.1 := by
                        exact loop2Widen_sign_initialX_denote fuelA f g 24 initialX
                          initialY hinitX
                      have haccY : acc.2.sign.denote rb.1 := by
                        exact loop2Widen_sign_initialY_denote fuelA f g 24 initialX
                          initialY hinitY
                      have hloopDenote : acc.1.sign.denote v := by
                        exact loop2Iter_sign_denote_of_stable hf hg
                          (loop2Widen_stable_24 fuelA f g initialX initialY)
                          evalFuel rn.1.toNat ra.1 rb.1 1 rb.2 st' v
                          haccX haccY heval
                      simpa [analyzeFuel, initialX, initialY, acc] using hloopDenote

theorem loop2_parity_sound_core_body_init {f g count a b : Prog}
    (hf : CoreProg f) (hg : CoreProg g) (ha : CoreProg a) (hb : CoreProg b) :
    ∀ (fuelA evalFuel : Nat) (xVal yVal : AbsVal) (cfg : Config)
      (st st' : Store) (v : Int),
      CfgParitySound xVal yVal cfg ->
      eval evalFuel orgE1Signature (.node 13 [f, g, count, a, b]) cfg st = some (v, st') ->
      (analyzeFuel fuelA xVal yVal (.node 13 [f, g, count, a, b])).parity.denote v
  | 0, _evalFuel, _xVal, _yVal, _cfg, _st, _st', _v, _hcfg, _heval => by
      simp [analyzeFuel, AbsVal.top, ParityInfo.denote]
  | fuelA + 1, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval => by
      cases evalFuel with
      | zero => simp [eval] at heval
      | succ evalFuel =>
          simp only [eval] at heval
          simp only [orgE1Signature, entryAt, listGet?, entry] at heval
          change ((eval evalFuel orgE1Signature count cfg st).bind fun rn =>
              (eval evalFuel orgE1Signature a cfg rn.2).bind fun ra =>
                (eval evalFuel orgE1Signature b cfg ra.2).bind fun rb =>
                  loop2Iter evalFuel orgE1Signature f g rn.1.toNat ra.1 rb.1 1 rb.2) =
              some (v, st') at heval
          cases hrn : eval evalFuel orgE1Signature count cfg st with
          | none =>
              rw [hrn] at heval
              simp at heval
          | some rn =>
              rw [hrn] at heval
              simp at heval
              cases hra : eval evalFuel orgE1Signature a cfg rn.2 with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature b cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      let initialX := analyzeFuel fuelA xVal yVal a
                      let initialY := analyzeFuel fuelA xVal yVal b
                      let acc := analyzeFuel.loop2Widen fuelA f g 24 initialX initialY
                      have hinitX : initialX.parity.denote ra.1 := by
                        exact CoreProg.parity_sound ha fuelA evalFuel xVal yVal cfg rn.2
                          ra.2 ra.1 hcfg hra
                      have hinitY : initialY.parity.denote rb.1 := by
                        exact CoreProg.parity_sound hb fuelA evalFuel xVal yVal cfg ra.2
                          rb.2 rb.1 hcfg hrb
                      have haccX : acc.1.parity.denote ra.1 := by
                        exact loop2Widen_parity_initialX_denote fuelA f g 24 initialX
                          initialY hinitX
                      have haccY : acc.2.parity.denote rb.1 := by
                        exact loop2Widen_parity_initialY_denote fuelA f g 24 initialX
                          initialY hinitY
                      have hloopDenote : acc.1.parity.denote v := by
                        exact loop2Iter_parity_denote_of_stable hf hg
                          (loop2Widen_stable_24 fuelA f g initialX initialY)
                          evalFuel rn.1.toNat ra.1 rb.1 1 rb.2 st' v
                          haccX haccY heval
                      simpa [analyzeFuel, initialX, initialY, acc] using hloopDenote

theorem comprSearch_result_nonneg :
    ∀ {fuel target seen : Nat} {cand : Int} {f : Prog} {st st' : Store} {v : Int},
      0 <= cand ->
      comprSearch fuel orgE1Signature f target seen cand st = some (v, st') ->
      0 <= v
  | 0, _target, _seen, _cand, _f, _st, _st', _v, _hcand, h => by
      simp [comprSearch] at h
  | fuel + 1, target, seen, cand, f, st, st', v, hcand, h => by
      simp only [comprSearch] at h
      change ((eval fuel orgE1Signature f { x := cand, y := 0, z := 0 } st).bind fun r =>
          if r.1 <= 0 then
            if seen >= target then some (cand, r.2)
            else comprSearch fuel orgE1Signature f target (seen + 1) (cand + 1) r.2
          else comprSearch fuel orgE1Signature f target seen (cand + 1) r.2) =
        some (v, st') at h
      cases hEval : eval fuel orgE1Signature f { x := cand, y := 0, z := 0 } st with
      | none =>
          rw [hEval] at h
          simp at h
      | some r =>
          rw [hEval] at h
          simp at h
          by_cases hle : r.1 <= 0
          · rw [if_pos hle] at h
            by_cases hseen : seen >= target
            · rw [if_pos hseen] at h
              cases h
              exact hcand
            · rw [if_neg hseen] at h
              exact comprSearch_result_nonneg (cand := cand + 1) (by omega) h
          · rw [if_neg hle] at h
            exact comprSearch_result_nonneg (cand := cand + 1) (by omega) h

/-! ## Public sign/parity certificate layer -/

inductive AnalysisSoundProg : Prog -> Prop where
  | core {p : Prog} : CoreProg p -> AnalysisSoundProg p
  | add {a b : Prog} :
      AnalysisSoundProg a -> AnalysisSoundProg b -> AnalysisSoundProg (.node 3 [a, b])
  | diff {a b : Prog} :
      AnalysisSoundProg a -> AnalysisSoundProg b -> AnalysisSoundProg (.node 4 [a, b])
  | mult {a b : Prog} :
      AnalysisSoundProg a -> AnalysisSoundProg b -> AnalysisSoundProg (.node 5 [a, b])
  | cond {c t e : Prog} :
      AnalysisSoundProg c -> AnalysisSoundProg t -> AnalysisSoundProg e ->
      AnalysisSoundProg (.node 8 [c, t, e])
  | divi {a b : Prog} :
      AnalysisSoundProg a -> AnalysisSoundProg b -> AnalysisSoundProg (.node 6 [a, b])
  | modu {a b : Prog} :
      AnalysisSoundProg a -> AnalysisSoundProg b -> AnalysisSoundProg (.node 7 [a, b])
  | loop {body count init : Prog} :
      CoreProg body -> CoreProg init -> AnalysisSoundProg (.node 9 [body, count, init])
  | compr {f n : Prog} :
      AnalysisSoundProg (.node 12 [f, n])
  | loop2 {f g count a b : Prog} :
      CoreProg f -> CoreProg g -> CoreProg a -> CoreProg b ->
      AnalysisSoundProg (.node 13 [f, g, count, a, b])

def analysisCertFuel? : Nat -> (p : Prog) -> Option (PLift (AnalysisSoundProg p))
  | 0, _ => none
  | fuel + 1, .node id ch =>
      if hcore : coreOnly (.node id ch) = true then
        some ⟨AnalysisSoundProg.core (CoreProg.of_coreOnly hcore)⟩
      else
        match id, ch with
        | 3, [a, b] =>
            match analysisCertFuel? fuel a, analysisCertFuel? fuel b with
            | some ha, some hb => some ⟨AnalysisSoundProg.add ha.down hb.down⟩
            | _, _ => none
        | 4, [a, b] =>
            match analysisCertFuel? fuel a, analysisCertFuel? fuel b with
            | some ha, some hb => some ⟨AnalysisSoundProg.diff ha.down hb.down⟩
            | _, _ => none
        | 5, [a, b] =>
            match analysisCertFuel? fuel a, analysisCertFuel? fuel b with
            | some ha, some hb => some ⟨AnalysisSoundProg.mult ha.down hb.down⟩
            | _, _ => none
        | 6, [a, b] =>
            match analysisCertFuel? fuel a, analysisCertFuel? fuel b with
            | some ha, some hb => some ⟨AnalysisSoundProg.divi ha.down hb.down⟩
            | _, _ => none
        | 7, [a, b] =>
            match analysisCertFuel? fuel a, analysisCertFuel? fuel b with
            | some ha, some hb => some ⟨AnalysisSoundProg.modu ha.down hb.down⟩
            | _, _ => none
        | 8, [c, t, e] =>
            match analysisCertFuel? fuel c, analysisCertFuel? fuel t, analysisCertFuel? fuel e with
            | some hc, some ht, some he =>
                some ⟨AnalysisSoundProg.cond hc.down ht.down he.down⟩
            | _, _, _ => none
        | 9, [body, count, init] =>
            if hbody : coreOnly body = true then
              if hinit : coreOnly init = true then
                some ⟨AnalysisSoundProg.loop (count := count)
                  (CoreProg.of_coreOnly hbody) (CoreProg.of_coreOnly hinit)⟩
              else
                none
            else
              none
        | 12, [f, n] => some ⟨AnalysisSoundProg.compr (f := f) (n := n)⟩
        | 13, [f, g, count, a, b] =>
            if hf : coreOnly f = true then
              if hg : coreOnly g = true then
                if ha : coreOnly a = true then
                  if hb : coreOnly b = true then
                    some ⟨AnalysisSoundProg.loop2 (count := count)
                      (CoreProg.of_coreOnly hf) (CoreProg.of_coreOnly hg)
                      (CoreProg.of_coreOnly ha) (CoreProg.of_coreOnly hb)⟩
                  else
                    none
                else
                  none
              else
                none
            else
              none
        | _, _ => none

def analysisCert? (p : Prog) : Option (PLift (AnalysisSoundProg p)) :=
  analysisCertFuel? (progHeight p + 1) p

def analysisSupported (p : Prog) : Bool := (analysisCert? p).isSome

theorem analysisSupported_sound {p : Prog} (h : analysisSupported p = true) :
    AnalysisSoundProg p := by
  unfold analysisSupported at h
  cases hcert : analysisCert? p with
  | none =>
      rw [hcert] at h
      simp at h
  | some hp =>
      exact hp.down

def certifiedAnalyze (p : Prog) : AbsVal :=
  if analysisSupported p then analyze p else AbsVal.top

def certifiedSignAnalysis (p : Prog) : SignInfo := (certifiedAnalyze p).sign
def certifiedParityAnalysis (p : Prog) : ParityInfo := (certifiedAnalyze p).parity

namespace AnalysisSoundProg

theorem sign_sound : ∀ {p : Prog}, AnalysisSoundProg p ->
    ∀ (fuelA evalFuel : Nat) (xVal yVal : AbsVal) (cfg : Config)
      (st st' : Store) (v : Int),
      CfgSignSound xVal yVal cfg ->
      eval evalFuel orgE1Signature p cfg st = some (v, st') ->
      (analyzeFuel fuelA xVal yVal p).sign.denote v
  | _, core hp, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval =>
      CoreProg.sign_sound hp fuelA evalFuel xVal yVal cfg st st' v hcfg heval
  | _, add (a := a) (b := b) ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v,
      hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature a cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature b cfg ra.2).bind
                    fun rb => some (ra.1 + rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature a cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature b cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.add]
                      exact signAdd_sound
                        (sign_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                        (sign_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb)
  | _, diff (a := a) (b := b) ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v,
      hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature a cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature b cfg ra.2).bind
                    fun rb => some (ra.1 - rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature a cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature b cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.diff]
                      simpa [sub_eq_add_neg] using
                        signAdd_sound
                          (sign_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                          (signNeg_sound
                            (sign_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb))
  | _, mult (a := a) (b := b) ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v,
      hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature a cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature b cfg ra.2).bind
                    fun rb => some (ra.1 * rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature a cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature b cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.mult]
                      exact signMul_sound
                        (sign_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                        (sign_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb)
  | _, cond (c := c) (t := t) (e := e) hc ht he, fuelA, evalFuel, xVal, yVal, cfg, st,
      st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, SignInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature c cfg st).bind fun rc =>
                  if rc.1 ≤ 0 then eval evalFuel orgE1Signature t cfg rc.2
                  else eval evalFuel orgE1Signature e cfg rc.2) = some (v, st') at heval
              cases hrc : eval evalFuel orgE1Signature c cfg st with
              | none =>
                  rw [hrc] at heval
                  simp at heval
              | some rc =>
                  rw [hrc] at heval
                  simp at heval
                  by_cases hle : rc.1 ≤ 0
                  · rw [if_pos hle] at heval
                    have hden :=
                      sign_sound ht fuelA evalFuel xVal yVal cfg rc.2 st' v hcfg heval
                    simpa [analyzeFuel, AbsVal.join] using
                      (SignInfo.join_left_sound
                        (a := (analyzeFuel fuelA xVal yVal t).sign)
                        (b := (analyzeFuel fuelA xVal yVal e).sign) hden)
                  · rw [if_neg hle] at heval
                    have hden :=
                      sign_sound he fuelA evalFuel xVal yVal cfg rc.2 st' v hcfg heval
                    simpa [analyzeFuel, AbsVal.join] using
                      (SignInfo.join_right_sound
                        (a := (analyzeFuel fuelA xVal yVal t).sign)
                        (b := (analyzeFuel fuelA xVal yVal e).sign) hden)
  | _, divi (a := a) (b := b) haCert hbCert, fuelA, evalFuel, xVal, yVal, cfg, st, st', v,
      hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, AbsVal.top, SignInfo.denote]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature a cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature b cfg ra.2).bind fun rb =>
                    (sdiv ra.1 rb.1).bind fun q => some (q, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature a cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature b cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      cases hdiv : sdiv ra.1 rb.1 with
                      | none =>
                          rw [hdiv] at heval
                          simp at heval
                      | some q =>
                          rw [hdiv] at heval
                          simp at heval
                          have hsa :
                              (analyzeFuel fuelA xVal yVal a).sign.denote ra.1 :=
                            sign_sound haCert fuelA evalFuel xVal yVal cfg st ra.2 ra.1
                              hcfg hra
                          have hsb :
                              (analyzeFuel fuelA xVal yVal b).sign.denote rb.1 :=
                            sign_sound hbCert fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1
                              hcfg hrb
                          have hvb : rb.1 ≠ 0 := by
                            unfold sdiv at hdiv
                            by_cases hz : rb.1 = 0
                            · simp [hz] at hdiv
                            · exact hz
                          have hdivSome :
                              sdiv ra.1 rb.1 = some (Int.fdiv ra.1 rb.1) := by
                            simp [sdiv, hvb]
                          rw [hdivSome] at hdiv
                          cases hdiv
                          rcases heval with ⟨hv, _hst⟩
                          subst v
                          have hden := signDiv_sound hsa hsb hvb
                          simpa [analyzeFuel, AbsVal.divi] using hden
  | _, modu (a := a) (b := b) _haCert hbCert, fuelA, evalFuel, xVal, yVal, cfg, st, st',
      v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, AbsVal.top, SignInfo.denote]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature a cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature b cfg ra.2).bind fun rb =>
                    (smod ra.1 rb.1).bind fun r => some (r, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature a cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature b cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      cases hmod : smod ra.1 rb.1 with
                      | none =>
                          rw [hmod] at heval
                          simp at heval
                      | some r =>
                          rw [hmod] at heval
                          simp at heval
                          have hsb :
                              (analyzeFuel fuelA xVal yVal b).sign.denote rb.1 :=
                            sign_sound hbCert fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1
                              hcfg hrb
                          have hvb : rb.1 ≠ 0 := by
                            unfold smod at hmod
                            by_cases hz : rb.1 = 0
                            · simp [hz] at hmod
                            · exact hz
                          have hmodSome :
                              smod ra.1 rb.1 = some (Int.fmod ra.1 rb.1) := by
                            simp [smod, hvb]
                          rw [hmodSome] at hmod
                          cases hmod
                          rcases heval with ⟨hv, _hst⟩
                          subst v
                          have hden :=
                            signMod_sound
                              (a := (analyzeFuel fuelA xVal yVal a).sign)
                              (b := (analyzeFuel fuelA xVal yVal b).sign)
                              (va := ra.1) (vb := rb.1) hsb hvb
                          simpa [analyzeFuel, AbsVal.modu] using hden
  | _, compr (f := f) (n := n), fuelA, evalFuel, xVal, yVal, cfg, st, st', v, _hcfg,
      heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, AbsVal.top, SignInfo.denote]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature n cfg st).bind fun rn =>
                  comprSearch evalFuel orgE1Signature f rn.1.toNat 0 0 rn.2) =
                some (v, st') at heval
              cases hrn : eval evalFuel orgE1Signature n cfg st with
              | none =>
                  rw [hrn] at heval
                  simp at heval
              | some rn =>
                  rw [hrn] at heval
                  simp at heval
                  have hv := comprSearch_result_nonneg
                    (fuel := evalFuel) (target := rn.1.toNat) (seen := 0)
                    (cand := 0) (f := f) (st := rn.2) (st' := st') (v := v)
                    (by omega) heval
                  simpa [analyzeFuel, AbsVal.compr, SignInfo.denote] using hv
  | _, loop hbody hinit, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval =>
      loop_sign_sound_core_body_init hbody hinit fuelA evalFuel xVal yVal cfg st st' v
        hcfg heval
  | _, loop2 hf hg ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval =>
      loop2_sign_sound_core_body_init hf hg ha hb fuelA evalFuel xVal yVal cfg st st' v
        hcfg heval

theorem parity_sound : ∀ {p : Prog}, AnalysisSoundProg p ->
    ∀ (fuelA evalFuel : Nat) (xVal yVal : AbsVal) (cfg : Config)
      (st st' : Store) (v : Int),
      CfgParitySound xVal yVal cfg ->
      eval evalFuel orgE1Signature p cfg st = some (v, st') ->
      (analyzeFuel fuelA xVal yVal p).parity.denote v
  | _, core hp, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval =>
      CoreProg.parity_sound hp fuelA evalFuel xVal yVal cfg st st' v hcfg heval
  | _, add (a := a) (b := b) ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v,
      hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature a cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature b cfg ra.2).bind
                    fun rb => some (ra.1 + rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature a cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature b cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.add]
                      exact parityAdd_sound
                        (parity_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                        (parity_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb)
  | _, diff (a := a) (b := b) ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v,
      hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature a cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature b cfg ra.2).bind
                    fun rb => some (ra.1 - rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature a cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature b cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.diff]
                      exact paritySub_sound
                        (parity_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                        (parity_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb)
  | _, mult (a := a) (b := b) ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v,
      hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature a cfg st).bind fun ra =>
                  (eval evalFuel orgE1Signature b cfg ra.2).bind
                    fun rb => some (ra.1 * rb.1, rb.2)) = some (v, st') at heval
              cases hra : eval evalFuel orgE1Signature a cfg st with
              | none =>
                  rw [hra] at heval
                  simp at heval
              | some ra =>
                  rw [hra] at heval
                  simp at heval
                  cases hrb : eval evalFuel orgE1Signature b cfg ra.2 with
                  | none =>
                      rw [hrb] at heval
                      simp at heval
                  | some rb =>
                      rw [hrb] at heval
                      simp at heval
                      rcases heval with ⟨hv, _hst⟩
                      subst v
                      simp [analyzeFuel, AbsVal.mult]
                      exact parityMul_sound
                        (parity_sound ha fuelA evalFuel xVal yVal cfg st ra.2 ra.1 hcfg hra)
                        (parity_sound hb fuelA evalFuel xVal yVal cfg ra.2 rb.2 rb.1 hcfg hrb)
  | _, cond (c := c) (t := t) (e := e) hc ht he, fuelA, evalFuel, xVal, yVal, cfg, st,
      st', v, hcfg, heval => by
      cases fuelA with
      | zero => simp [analyzeFuel, ParityInfo.denote, AbsVal.top]
      | succ fuelA =>
          cases evalFuel with
          | zero => simp [eval] at heval
          | succ evalFuel =>
              simp only [eval] at heval
              simp only [orgE1Signature, entryAt, listGet?, entry] at heval
              change ((eval evalFuel orgE1Signature c cfg st).bind fun rc =>
                  if rc.1 ≤ 0 then eval evalFuel orgE1Signature t cfg rc.2
                  else eval evalFuel orgE1Signature e cfg rc.2) = some (v, st') at heval
              cases hrc : eval evalFuel orgE1Signature c cfg st with
              | none =>
                  rw [hrc] at heval
                  simp at heval
              | some rc =>
                  rw [hrc] at heval
                  simp at heval
                  by_cases hle : rc.1 ≤ 0
                  · rw [if_pos hle] at heval
                    have hden :=
                      parity_sound ht fuelA evalFuel xVal yVal cfg rc.2 st' v hcfg heval
                    simpa [analyzeFuel, AbsVal.join] using
                      (ParityInfo.join_left_sound
                        (a := (analyzeFuel fuelA xVal yVal t).parity)
                        (b := (analyzeFuel fuelA xVal yVal e).parity) hden)
                  · rw [if_neg hle] at heval
                    have hden :=
                      parity_sound he fuelA evalFuel xVal yVal cfg rc.2 st' v hcfg heval
                    simpa [analyzeFuel, AbsVal.join] using
                      (ParityInfo.join_right_sound
                        (a := (analyzeFuel fuelA xVal yVal t).parity)
                        (b := (analyzeFuel fuelA xVal yVal e).parity) hden)
  | _, divi _haCert _hbCert, fuelA, _evalFuel, xVal, yVal, _cfg, _st, _st', _v, _hcfg,
      _heval => by
      cases fuelA <;> simp [analyzeFuel, AbsVal.top, AbsVal.divi, ParityInfo.denote]
  | _, modu _haCert _hbCert, fuelA, _evalFuel, xVal, yVal, _cfg, _st, _st', _v, _hcfg,
      _heval => by
      cases fuelA <;> simp [analyzeFuel, AbsVal.top, AbsVal.modu, ParityInfo.denote]
  | _, compr, fuelA, _evalFuel, xVal, yVal, _cfg, _st, _st', _v, _hcfg, _heval => by
      cases fuelA <;> simp [analyzeFuel, AbsVal.top, AbsVal.compr, ParityInfo.denote]
  | _, loop hbody hinit, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval =>
      loop_parity_sound_core_body_init hbody hinit fuelA evalFuel xVal yVal cfg st st' v
        hcfg heval
  | _, loop2 hf hg ha hb, fuelA, evalFuel, xVal, yVal, cfg, st, st', v, hcfg, heval =>
      loop2_parity_sound_core_body_init hf hg ha hb fuelA evalFuel xVal yVal cfg st st' v
        hcfg heval

theorem sign_nonzero_sound {p : Prog} (hp : AnalysisSoundProg p)
    {fuelA evalFuel : Nat} {xVal yVal : AbsVal} {cfg : Config}
    {st st' : Store} {v : Int}
    (hcfg : CfgSignSound xVal yVal cfg)
    (hs : ((analyzeFuel fuelA xVal yVal p).sign).provesNonzero = true)
    (heval : eval evalFuel orgE1Signature p cfg st = some (v, st')) : v ≠ 0 := by
  apply SignInfo.provesNonzero_sound hs
  exact sign_sound hp fuelA evalFuel xVal yVal cfg st st' v hcfg heval

theorem signAnalysis_nonneg_sound_seed {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNonneg = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : 0 <= v := by
  apply SignInfo.provesNonneg_sound hs
  exact sign_sound hp (progHeight p + 1) fuel AbsVal.nonnegUnknownParity AbsVal.zeroReg
    (seed n) Store.zero st' v (by
      simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, SignInfo.denote, seed]
      exact hn) heval

theorem signAnalysis_nonpos_sound_seed {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNonpos = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : v <= 0 := by
  apply SignInfo.provesNonpos_sound hs
  exact sign_sound hp (progHeight p + 1) fuel AbsVal.nonnegUnknownParity AbsVal.zeroReg
    (seed n) Store.zero st' v (by
      simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, SignInfo.denote, seed]
      exact hn) heval

theorem signAnalysis_pos_sound_seed {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesPos = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : 0 < v := by
  apply SignInfo.provesPos_sound hs
  exact sign_sound hp (progHeight p + 1) fuel AbsVal.nonnegUnknownParity AbsVal.zeroReg
    (seed n) Store.zero st' v (by
      simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, SignInfo.denote, seed]
      exact hn) heval

theorem signAnalysis_neg_sound_seed {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNeg = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : v < 0 := by
  apply SignInfo.provesNeg_sound hs
  exact sign_sound hp (progHeight p + 1) fuel AbsVal.nonnegUnknownParity AbsVal.zeroReg
    (seed n) Store.zero st' v (by
      simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, SignInfo.denote, seed]
      exact hn) heval

theorem signAnalysis_nonzero_sound_seed {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNonzero = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : v ≠ 0 := by
  exact sign_nonzero_sound hp
    (fuelA := progHeight p + 1) (evalFuel := fuel)
    (xVal := AbsVal.nonnegUnknownParity) (yVal := AbsVal.zeroReg)
    (cfg := seed n) (st := Store.zero) (st' := st') (v := v)
    (by
      simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, SignInfo.denote, seed]
      exact hn)
    hs heval

theorem parityAnalysis_even_sound_seed {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hs : (parityAnalysis p).provesEven = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : EvenInt v := by
  apply ParityInfo.provesEven_sound hs
  exact parity_sound hp (progHeight p + 1) fuel AbsVal.nonnegUnknownParity AbsVal.zeroReg
    (seed n) Store.zero st' v (by
      simp [CfgParitySound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, ParityInfo.denote,
        EvenInt, seed]) heval

theorem parityAnalysis_odd_sound_seed {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hs : (parityAnalysis p).provesOdd = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) : OddInt v := by
  apply ParityInfo.provesOdd_sound hs
  exact parity_sound hp (progHeight p + 1) fuel AbsVal.nonnegUnknownParity AbsVal.zeroReg
    (seed n) Store.zero st' v (by
      simp [CfgParitySound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, ParityInfo.denote,
        EvenInt, seed]) heval

end AnalysisSoundProg

theorem sdiv_eq_some_of_ne_zero {a b : Int} (hb : b ≠ 0) :
    sdiv a b = some (Int.fdiv a b) := by
  simp [sdiv, hb]

theorem smod_eq_some_of_ne_zero {a b : Int} (hb : b ≠ 0) :
    smod a b = some (Int.fmod a b) := by
  simp [smod, hb]

theorem eval_divi_defined_of_analysis_parts {a b : Prog} (hbCert : AnalysisSoundProg b)
    {fuelA evalFuel : Nat} {xVal yVal : AbsVal} {cfg : Config}
    {st sta stb : Store} {va vb : Int}
    (hcfg : CfgSignSound xVal yVal cfg)
    (hsafe : ((analyzeFuel fuelA xVal yVal b).sign).provesNonzero = true)
    (ha : eval evalFuel orgE1Signature a cfg st = some (va, sta))
    (hb : eval evalFuel orgE1Signature b cfg sta = some (vb, stb)) :
    eval (evalFuel + 1) orgE1Signature (.node 6 [a, b]) cfg st =
      some (Int.fdiv va vb, stb) := by
  have hvb : vb ≠ 0 :=
    AnalysisSoundProg.sign_nonzero_sound hbCert
      (fuelA := fuelA) (evalFuel := evalFuel) (xVal := xVal) (yVal := yVal)
      (cfg := cfg) (st := sta) (st' := stb) (v := vb) hcfg hsafe hb
  simp only [eval]
  simp only [orgE1Signature, entryAt, listGet?, entry]
  change ((eval evalFuel orgE1Signature a cfg st).bind fun ra =>
      (eval evalFuel orgE1Signature b cfg ra.2).bind fun rb =>
        (sdiv ra.1 rb.1).bind fun q => some (q, rb.2)) =
      some (Int.fdiv va vb, stb)
  rw [ha]
  simp
  rw [hb]
  simp [sdiv_eq_some_of_ne_zero hvb]

theorem eval_modu_defined_of_analysis_parts {a b : Prog} (hbCert : AnalysisSoundProg b)
    {fuelA evalFuel : Nat} {xVal yVal : AbsVal} {cfg : Config}
    {st sta stb : Store} {va vb : Int}
    (hcfg : CfgSignSound xVal yVal cfg)
    (hsafe : ((analyzeFuel fuelA xVal yVal b).sign).provesNonzero = true)
    (ha : eval evalFuel orgE1Signature a cfg st = some (va, sta))
    (hb : eval evalFuel orgE1Signature b cfg sta = some (vb, stb)) :
    eval (evalFuel + 1) orgE1Signature (.node 7 [a, b]) cfg st =
      some (Int.fmod va vb, stb) := by
  have hvb : vb ≠ 0 :=
    AnalysisSoundProg.sign_nonzero_sound hbCert
      (fuelA := fuelA) (evalFuel := evalFuel) (xVal := xVal) (yVal := yVal)
      (cfg := cfg) (st := sta) (st' := stb) (v := vb) hcfg hsafe hb
  simp only [eval]
  simp only [orgE1Signature, entryAt, listGet?, entry]
  change ((eval evalFuel orgE1Signature a cfg st).bind fun ra =>
      (eval evalFuel orgE1Signature b cfg ra.2).bind fun rb =>
        (smod ra.1 rb.1).bind fun r => some (r, rb.2)) =
      some (Int.fmod va vb, stb)
  rw [ha]
  simp
  rw [hb]
  simp [smod_eq_some_of_ne_zero hvb]

/-! ## Public totality certificate layer for the loop-free conditional/div/mod fragment -/

inductive TotalSoundProg : Prog -> Prop where
  | core {p : Prog} : CoreProg p -> TotalSoundProg p
  | add {a b : Prog} :
      TotalSoundProg a -> TotalSoundProg b -> TotalSoundProg (.node 3 [a, b])
  | diff {a b : Prog} :
      TotalSoundProg a -> TotalSoundProg b -> TotalSoundProg (.node 4 [a, b])
  | mult {a b : Prog} :
      TotalSoundProg a -> TotalSoundProg b -> TotalSoundProg (.node 5 [a, b])
  | cond {c t e : Prog} :
      TotalSoundProg c -> TotalSoundProg t -> TotalSoundProg e ->
      TotalSoundProg (.node 8 [c, t, e])
  | divi {a b : Prog} :
      TotalSoundProg a -> TotalSoundProg b ->
      (signAnalysis b).provesNonzero = true -> TotalSoundProg (.node 6 [a, b])
  | modu {a b : Prog} :
      TotalSoundProg a -> TotalSoundProg b ->
      (signAnalysis b).provesNonzero = true -> TotalSoundProg (.node 7 [a, b])

def totalCertFuel? : Nat -> (p : Prog) -> Option (PLift (TotalSoundProg p))
  | 0, _ => none
  | fuel + 1, .node id ch =>
      if hcore : coreOnly (.node id ch) = true then
        some ⟨TotalSoundProg.core (CoreProg.of_coreOnly hcore)⟩
      else
        match id, ch with
        | 3, [a, b] =>
            match totalCertFuel? fuel a, totalCertFuel? fuel b with
            | some ha, some hb => some ⟨TotalSoundProg.add ha.down hb.down⟩
            | _, _ => none
        | 4, [a, b] =>
            match totalCertFuel? fuel a, totalCertFuel? fuel b with
            | some ha, some hb => some ⟨TotalSoundProg.diff ha.down hb.down⟩
            | _, _ => none
        | 5, [a, b] =>
            match totalCertFuel? fuel a, totalCertFuel? fuel b with
            | some ha, some hb => some ⟨TotalSoundProg.mult ha.down hb.down⟩
            | _, _ => none
        | 6, [a, b] =>
            match totalCertFuel? fuel a, totalCertFuel? fuel b with
            | some ha, some hb =>
                if hsafe : (signAnalysis b).provesNonzero = true then
                  some ⟨TotalSoundProg.divi ha.down hb.down hsafe⟩
                else
                  none
            | _, _ => none
        | 7, [a, b] =>
            match totalCertFuel? fuel a, totalCertFuel? fuel b with
            | some ha, some hb =>
                if hsafe : (signAnalysis b).provesNonzero = true then
                  some ⟨TotalSoundProg.modu ha.down hb.down hsafe⟩
                else
                  none
            | _, _ => none
        | 8, [c, t, e] =>
            match totalCertFuel? fuel c, totalCertFuel? fuel t, totalCertFuel? fuel e with
            | some hc, some ht, some he => some ⟨TotalSoundProg.cond hc.down ht.down he.down⟩
            | _, _, _ => none
        | _, _ => none

def totalCert? (p : Prog) : Option (PLift (TotalSoundProg p)) :=
  totalCertFuel? (progHeight p + 1) p

def totalSupported (p : Prog) : Bool := (totalCert? p).isSome

theorem totalSupported_sound {p : Prog} (h : totalSupported p = true) :
    TotalSoundProg p := by
  unfold totalSupported at h
  cases hcert : totalCert? p with
  | none =>
      rw [hcert] at h
      simp at h
  | some hp =>
      exact hp.down

def certifiedTotalAnalysis (p : Prog) : Bool :=
  totalSupported p && totalAnalysis p

namespace TotalSoundProg

theorem analysisSound : ∀ {p : Prog}, TotalSoundProg p -> AnalysisSoundProg p
  | _, core hp => AnalysisSoundProg.core hp
  | _, add ha hb => AnalysisSoundProg.add (analysisSound ha) (analysisSound hb)
  | _, diff ha hb => AnalysisSoundProg.diff (analysisSound ha) (analysisSound hb)
  | _, mult ha hb => AnalysisSoundProg.mult (analysisSound ha) (analysisSound hb)
  | _, cond hc ht he =>
      AnalysisSoundProg.cond (analysisSound hc) (analysisSound ht) (analysisSound he)
  | _, divi ha hb _hsafe => AnalysisSoundProg.divi (analysisSound ha) (analysisSound hb)
  | _, modu ha hb _hsafe => AnalysisSoundProg.modu (analysisSound ha) (analysisSound hb)

theorem eval_defined_of_fuel : ∀ {p : Prog}, TotalSoundProg p ->
    ∀ {fuel : Nat} {n : Int} (st : Store),
      0 <= n -> progHeight p < fuel ->
      ∃ v st', eval fuel orgE1Signature p (seed n) st = some (v, st')
  | _, core hp, fuel, n, st, _hn, hfuel =>
      CoreProg.eval_defined_of_fuel hp (seed n) st hfuel
  | _, add (a := a) (b := b) ha hb, fuel, n, st, hn, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfa : progHeight a < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight a <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_left _ _
            omega
          have hfb : progHeight b < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight b <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_right _ _
            omega
          rcases eval_defined_of_fuel ha st hn hfa with ⟨va, sta, hra⟩
          rcases eval_defined_of_fuel hb sta hn hfb with ⟨vb, stb, hrb⟩
          refine ⟨va + vb, stb, ?_⟩
          simp only [eval]
          simp only [orgE1Signature, entryAt, listGet?, entry]
          change ((eval fuel orgE1Signature a (seed n) st).bind fun ra =>
              (eval fuel orgE1Signature b (seed n) ra.2).bind
                fun rb => some (ra.1 + rb.1, rb.2)) = some (va + vb, stb)
          rw [hra]
          simp
          rw [hrb]
          simp
  | _, diff (a := a) (b := b) ha hb, fuel, n, st, hn, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfa : progHeight a < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight a <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_left _ _
            omega
          have hfb : progHeight b < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight b <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_right _ _
            omega
          rcases eval_defined_of_fuel ha st hn hfa with ⟨va, sta, hra⟩
          rcases eval_defined_of_fuel hb sta hn hfb with ⟨vb, stb, hrb⟩
          refine ⟨va - vb, stb, ?_⟩
          simp only [eval]
          simp only [orgE1Signature, entryAt, listGet?, entry]
          change ((eval fuel orgE1Signature a (seed n) st).bind fun ra =>
              (eval fuel orgE1Signature b (seed n) ra.2).bind
                fun rb => some (ra.1 - rb.1, rb.2)) = some (va - vb, stb)
          rw [hra]
          simp
          rw [hrb]
          simp
  | _, mult (a := a) (b := b) ha hb, fuel, n, st, hn, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfa : progHeight a < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight a <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_left _ _
            omega
          have hfb : progHeight b < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight b <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_right _ _
            omega
          rcases eval_defined_of_fuel ha st hn hfa with ⟨va, sta, hra⟩
          rcases eval_defined_of_fuel hb sta hn hfb with ⟨vb, stb, hrb⟩
          refine ⟨va * vb, stb, ?_⟩
          simp only [eval]
          simp only [orgE1Signature, entryAt, listGet?, entry]
          change ((eval fuel orgE1Signature a (seed n) st).bind fun ra =>
              (eval fuel orgE1Signature b (seed n) ra.2).bind
                fun rb => some (ra.1 * rb.1, rb.2)) = some (va * vb, stb)
          rw [hra]
          simp
          rw [hrb]
          simp
  | _, cond (c := c) (t := t) (e := e) hc ht he, fuel, n, st, hn, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfc : progHeight c < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle :
                progHeight c <= Nat.max (progHeight c) (Nat.max (progHeight t) (progHeight e)) :=
              Nat.le_max_left _ _
            omega
          have hft : progHeight t < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle₁ : progHeight t <= Nat.max (progHeight t) (progHeight e) :=
              Nat.le_max_left _ _
            have hle₂ : Nat.max (progHeight t) (progHeight e) <=
                Nat.max (progHeight c) (Nat.max (progHeight t) (progHeight e)) :=
              Nat.le_max_right _ _
            omega
          have hfe : progHeight e < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle₁ : progHeight e <= Nat.max (progHeight t) (progHeight e) :=
              Nat.le_max_right _ _
            have hle₂ : Nat.max (progHeight t) (progHeight e) <=
                Nat.max (progHeight c) (Nat.max (progHeight t) (progHeight e)) :=
              Nat.le_max_right _ _
            omega
          rcases eval_defined_of_fuel hc st hn hfc with ⟨vc, stc, hrc⟩
          by_cases hle : vc <= 0
          · rcases eval_defined_of_fuel ht stc hn hft with ⟨vt, stt, hrt⟩
            refine ⟨vt, stt, ?_⟩
            simp only [eval]
            simp only [orgE1Signature, entryAt, listGet?, entry]
            change ((eval fuel orgE1Signature c (seed n) st).bind fun rc =>
                if rc.1 <= 0 then eval fuel orgE1Signature t (seed n) rc.2
                else eval fuel orgE1Signature e (seed n) rc.2) = some (vt, stt)
            rw [hrc]
            simp [hle, hrt]
          · rcases eval_defined_of_fuel he stc hn hfe with ⟨ve, ste, hre⟩
            refine ⟨ve, ste, ?_⟩
            simp only [eval]
            simp only [orgE1Signature, entryAt, listGet?, entry]
            change ((eval fuel orgE1Signature c (seed n) st).bind fun rc =>
                if rc.1 <= 0 then eval fuel orgE1Signature t (seed n) rc.2
                else eval fuel orgE1Signature e (seed n) rc.2) = some (ve, ste)
            rw [hrc]
            simp [hle, hre]
  | _, divi (a := a) (b := b) ha hb hsafe, fuel, n, st, hn, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfa : progHeight a < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight a <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_left _ _
            omega
          have hfb : progHeight b < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight b <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_right _ _
            omega
          rcases eval_defined_of_fuel ha st hn hfa with ⟨va, sta, hra⟩
          rcases eval_defined_of_fuel hb sta hn hfb with ⟨vb, stb, hrb⟩
          have hcfg : CfgSignSound AbsVal.nonnegUnknownParity AbsVal.zeroReg (seed n) := by
            simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, SignInfo.denote,
              seed]
            exact hn
          have hsafe' :
              ((analyzeFuel (progHeight b + 1) AbsVal.nonnegUnknownParity
                AbsVal.zeroReg b).sign).provesNonzero = true := by
            simpa [signAnalysis, analyze, analyzeWith] using hsafe
          refine ⟨Int.fdiv va vb, stb, ?_⟩
          simpa [Nat.succ_eq_add_one] using
            eval_divi_defined_of_analysis_parts (a := a) (b := b)
              (hbCert := analysisSound hb)
              (fuelA := progHeight b + 1) (evalFuel := fuel)
              (xVal := AbsVal.nonnegUnknownParity) (yVal := AbsVal.zeroReg)
              (cfg := seed n) (st := st) (sta := sta) (stb := stb)
              (va := va) (vb := vb) hcfg hsafe' hra hrb
  | _, modu (a := a) (b := b) ha hb hsafe, fuel, n, st, hn, hfuel => by
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfa : progHeight a < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight a <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_left _ _
            omega
          have hfb : progHeight b < fuel := by
            simp [progHeight, progHeight.listHeight] at hfuel
            have hle : progHeight b <= Nat.max (progHeight a) (progHeight b) :=
              Nat.le_max_right _ _
            omega
          rcases eval_defined_of_fuel ha st hn hfa with ⟨va, sta, hra⟩
          rcases eval_defined_of_fuel hb sta hn hfb with ⟨vb, stb, hrb⟩
          have hcfg : CfgSignSound AbsVal.nonnegUnknownParity AbsVal.zeroReg (seed n) := by
            simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, SignInfo.denote,
              seed]
            exact hn
          have hsafe' :
              ((analyzeFuel (progHeight b + 1) AbsVal.nonnegUnknownParity
                AbsVal.zeroReg b).sign).provesNonzero = true := by
            simpa [signAnalysis, analyze, analyzeWith] using hsafe
          refine ⟨Int.fmod va vb, stb, ?_⟩
          simpa [Nat.succ_eq_add_one] using
            eval_modu_defined_of_analysis_parts (a := a) (b := b)
              (hbCert := analysisSound hb)
              (fuelA := progHeight b + 1) (evalFuel := fuel)
              (xVal := AbsVal.nonnegUnknownParity) (yVal := AbsVal.zeroReg)
              (cfg := seed n) (st := st) (sta := sta) (stb := stb)
              (va := va) (vb := vb) hcfg hsafe' hra hrb

theorem eval_defined_at_analysis_fuel {p : Prog} (hp : TotalSoundProg p)
    {n : Int} (st : Store) (hn : 0 <= n) :
    ∃ v st', eval (progHeight p + 1) orgE1Signature p (seed n) st = some (v, st') :=
  eval_defined_of_fuel hp st hn (by omega)

theorem totalAnalysis_sound {p : Prog} (hp : TotalSoundProg p)
    (htotal : totalAnalysis p = true) {n : Int} (st : Store) (hn : 0 <= n) :
    totalAnalysis p = true ∧
      ∃ v st', eval (progHeight p + 1) orgE1Signature p (seed n) st = some (v, st') :=
  ⟨htotal, eval_defined_at_analysis_fuel hp st hn⟩

theorem eval_loop_defined_of_total_parts {body count init : Prog}
    (hbody : CoreProg body) (hcount : TotalSoundProg count) (hinit : TotalSoundProg init)
    {fuel : Nat} {n : Int} (st : Store) (hn : 0 <= n)
    (hcountFuel : progHeight count < fuel)
    (hinitFuel : progHeight init < fuel)
    (hbodyFuel : ∀ {cnt : Int} {stCount : Store},
      eval fuel orgE1Signature count (seed n) st = some (cnt, stCount) ->
      progHeight body + cnt.toNat + 1 <= fuel) :
    ∃ v st',
      eval (fuel + 1) orgE1Signature (.node 9 [body, count, init]) (seed n) st =
        some (v, st') := by
  rcases eval_defined_of_fuel hcount st hn hcountFuel with ⟨cnt, stCount, hcountEval⟩
  rcases eval_defined_of_fuel hinit stCount hn hinitFuel with
    ⟨initVal, stInit, hinitEval⟩
  exact CoreProg.eval_loop_defined_of_core_parts hbody hcountEval hinitEval
    (hbodyFuel hcountEval)

theorem eval_loop2_defined_of_total_parts {f g count a b : Prog}
    (hf : CoreProg f) (hg : CoreProg g)
    (hcount : TotalSoundProg count) (ha : TotalSoundProg a) (hb : TotalSoundProg b)
    {fuel : Nat} {n : Int} (st : Store) (hn : 0 <= n)
    (hcountFuel : progHeight count < fuel)
    (haFuel : progHeight a < fuel)
    (hbFuel : progHeight b < fuel)
    (hfFuel : ∀ {cnt : Int} {stCount : Store},
      eval fuel orgE1Signature count (seed n) st = some (cnt, stCount) ->
      progHeight f + cnt.toNat + 1 <= fuel)
    (hgFuel : ∀ {cnt : Int} {stCount : Store},
      eval fuel orgE1Signature count (seed n) st = some (cnt, stCount) ->
      progHeight g + cnt.toNat + 1 <= fuel) :
    ∃ v st',
      eval (fuel + 1) orgE1Signature (.node 13 [f, g, count, a, b]) (seed n) st =
        some (v, st') := by
  rcases eval_defined_of_fuel hcount st hn hcountFuel with ⟨cnt, stCount, hcountEval⟩
  rcases eval_defined_of_fuel ha stCount hn haFuel with ⟨aVal, stA, haEval⟩
  rcases eval_defined_of_fuel hb stA hn hbFuel with ⟨bVal, stB, hbEval⟩
  exact CoreProg.eval_loop2_defined_of_core_parts hf hg hcountEval haEval hbEval
    (hfFuel hcountEval) (hgFuel hcountEval)

end TotalSoundProg

/-! ## Examples and canaries -/

def addiXOne : Prog := .node 3 [.node 10 [], .node 1 []]
def diffXOne : Prog := .node 4 [.node 10 [], .node 1 []]
def diffZeroOne : Prog := .node 4 [.node 0 [], .node 1 []]
def addiOneOne : Prog := .node 3 [.node 1 [], .node 1 []]
def multTwoX : Prog := .node 5 [.node 2 [], .node 10 []]
def multXX : Prog := .node 5 [.node 10 [], .node 10 []]
def diviAddiXOneOne : Prog := .node 6 [addiXOne, .node 1 []]
def diviDiffZeroOneOne : Prog := .node 6 [diffZeroOne, .node 1 []]
def diviOneDiffZeroOne : Prog := .node 6 [.node 1 [], diffZeroOne]
def diviAddiXOneDiffXOne : Prog := .node 6 [addiXOne, diffXOne]
def diviOneX : Prog := .node 6 [.node 1 [], .node 10 []]
def diviXTwo : Prog := .node 6 [.node 10 [], .node 2 []]
def moduAddiXOneOne : Prog := .node 7 [addiXOne, .node 1 []]
def moduXTwo : Prog := .node 7 [.node 10 [], .node 2 []]
def comprXOne : Prog := .node 12 [.node 10 [], .node 1 []]
def condDiffXOneDiviXTwoModuXTwo : Prog := .node 8 [diffXOne, diviXTwo, moduXTwo]
def condZeroOneDiviOneX : Prog := .node 8 [.node 0 [], .node 1 [], diviOneX]
def condDiviOneXOneOne : Prog := .node 8 [diviOneX, .node 1 [], .node 1 []]
def loopAddiXOne : Prog := .node 9 [addiXOne, .node 10 [], .node 1 []]
def loop2AddiXOneKeepY : Prog :=
  .node 13 [addiXOne, .node 11 [], .node 10 [], .node 1 [], .node 0 []]
def loop2DiffXOneKeepY : Prog :=
  .node 13 [diffXOne, .node 11 [], .node 10 [], .node 1 [], .node 0 []]

theorem addiXOne_core : CoreProg addiXOne := by
  simp [addiXOne]
  exact CoreProg.add CoreProg.x CoreProg.one

theorem diffXOne_core : CoreProg diffXOne := by
  simp [diffXOne]
  exact CoreProg.diff CoreProg.x CoreProg.one

theorem diffZeroOne_core : CoreProg diffZeroOne := by
  simp [diffZeroOne]
  exact CoreProg.diff CoreProg.zero CoreProg.one

theorem multTwoX_core : CoreProg multTwoX := by
  simp [multTwoX]
  exact CoreProg.mult CoreProg.two CoreProg.x

theorem multXX_core : CoreProg multXX := by
  simp [multXX]
  exact CoreProg.mult CoreProg.x CoreProg.x

theorem addiXOne_analysisSound : AnalysisSoundProg addiXOne :=
  AnalysisSoundProg.core addiXOne_core

theorem diffXOne_analysisSound : AnalysisSoundProg diffXOne :=
  AnalysisSoundProg.core diffXOne_core

theorem diviAddiXOneOne_analysisSound : AnalysisSoundProg diviAddiXOneOne :=
  AnalysisSoundProg.divi addiXOne_analysisSound (AnalysisSoundProg.core CoreProg.one)

theorem diviDiffZeroOneOne_analysisSound : AnalysisSoundProg diviDiffZeroOneOne :=
  AnalysisSoundProg.divi (AnalysisSoundProg.core diffZeroOne_core)
    (AnalysisSoundProg.core CoreProg.one)

theorem diviOneDiffZeroOne_analysisSound : AnalysisSoundProg diviOneDiffZeroOne :=
  AnalysisSoundProg.divi (AnalysisSoundProg.core CoreProg.one)
    (AnalysisSoundProg.core diffZeroOne_core)

theorem moduAddiXOneOne_analysisSound : AnalysisSoundProg moduAddiXOneOne :=
  AnalysisSoundProg.modu addiXOne_analysisSound (AnalysisSoundProg.core CoreProg.one)

theorem comprXOne_analysisSound : AnalysisSoundProg comprXOne := by
  simpa [comprXOne] using
    (AnalysisSoundProg.compr (f := .node 10 []) (n := .node 1 []))

theorem loopAddiXOne_analysisSound : AnalysisSoundProg loopAddiXOne :=
  AnalysisSoundProg.loop addiXOne_core CoreProg.one

theorem loop2AddiXOneKeepY_analysisSound : AnalysisSoundProg loop2AddiXOneKeepY :=
  AnalysisSoundProg.loop2 addiXOne_core CoreProg.y CoreProg.one CoreProg.zero

theorem loop2DiffXOneKeepY_analysisSound : AnalysisSoundProg loop2DiffXOneKeepY :=
  AnalysisSoundProg.loop2 diffXOne_core CoreProg.y CoreProg.one CoreProg.zero

theorem coreOnly_addiXOne : coreOnly addiXOne = true := by
  simp [addiXOne, coreOnly]

theorem coreOnly_diffXOne : coreOnly diffXOne = true := by
  simp [diffXOne, coreOnly]

theorem signAnalysis_addiXOne_pos : signAnalysis addiXOne = .pos := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    addiXOne, AbsVal.add, signAdd, AbsVal.nonnegUnknownParity, AbsVal.one]

theorem signAnalysis_diffXOne_not_nonneg : signAnalysis diffXOne ≠ .nonneg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diffXOne, AbsVal.diff, signAdd, signNeg, AbsVal.nonnegUnknownParity, AbsVal.one]

theorem signAnalysis_addiXOne_nonzero : (signAnalysis addiXOne).provesNonzero = true := by
  simp [signAnalysis_addiXOne_pos, SignInfo.provesNonzero]

theorem signAnalysis_one_nonzero : (signAnalysis (.node 1 [])).provesNonzero = true := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, AbsVal.one,
    SignInfo.provesNonzero]

theorem signAnalysis_two_nonzero : (signAnalysis (.node 2 [])).provesNonzero = true := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, AbsVal.two,
    SignInfo.provesNonzero]

theorem signAnalysis_diffXOne_top : signAnalysis diffXOne = .top := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diffXOne, AbsVal.diff, signAdd, signNeg, AbsVal.nonnegUnknownParity, AbsVal.one]

theorem signAnalysis_diffXOne_not_nonzero :
    (signAnalysis diffXOne).provesNonzero = false := by
  simp [signAnalysis_diffXOne_top, SignInfo.provesNonzero]

theorem signAnalysis_diffZeroOne_neg : signAnalysis diffZeroOne = .neg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diffZeroOne, AbsVal.diff, signAdd, signNeg, AbsVal.zero, AbsVal.one]

theorem signAnalysis_diffZeroOne_nonzero :
    (signAnalysis diffZeroOne).provesNonzero = true := by
  simp [signAnalysis_diffZeroOne_neg, SignInfo.provesNonzero]

theorem parityAnalysis_multTwoX_even : parityAnalysis multTwoX = .even := by
  simp [parityAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    multTwoX, AbsVal.mult, parityMul, AbsVal.two, AbsVal.nonnegUnknownParity]

theorem signAnalysis_multTwoX_nonneg : signAnalysis multTwoX = .nonneg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    multTwoX, AbsVal.mult, signMul, AbsVal.two, AbsVal.nonnegUnknownParity]

theorem signAnalysis_multXX_nonneg : signAnalysis multXX = .nonneg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    multXX, AbsVal.mult, signMul, AbsVal.nonnegUnknownParity]

theorem signAnalysis_diviAddiXOneOne_nonneg :
    signAnalysis diviAddiXOneOne = .nonneg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diviAddiXOneOne, addiXOne, AbsVal.divi, AbsVal.add, signDiv, signAdd, parityAdd,
    AbsVal.nonnegUnknownParity, AbsVal.one]

theorem signAnalysis_diviDiffZeroOneOne_neg :
    signAnalysis diviDiffZeroOneOne = .neg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diviDiffZeroOneOne, diffZeroOne, AbsVal.divi, AbsVal.diff, signDiv, signAdd,
    signNeg, parityAdd, AbsVal.zero, AbsVal.one]

theorem signAnalysis_diviOneDiffZeroOne_neg :
    signAnalysis diviOneDiffZeroOne = .neg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diviOneDiffZeroOne, diffZeroOne, AbsVal.divi, AbsVal.diff, signDiv, signAdd,
    signNeg, parityAdd, AbsVal.zero, AbsVal.one]

theorem signAnalysis_diviXTwo_nonneg : signAnalysis diviXTwo = .nonneg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diviXTwo, AbsVal.divi, signDiv, AbsVal.nonnegUnknownParity, AbsVal.two]

theorem signAnalysis_moduAddiXOneOne_nonneg :
    signAnalysis moduAddiXOneOne = .nonneg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    moduAddiXOneOne, addiXOne, AbsVal.modu, AbsVal.add, signMod, signAdd, parityAdd,
    AbsVal.nonnegUnknownParity, AbsVal.one]

theorem signAnalysis_moduXTwo_nonneg : signAnalysis moduXTwo = .nonneg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    moduXTwo, AbsVal.modu, signMod, AbsVal.nonnegUnknownParity, AbsVal.two]

theorem signAnalysis_compr_nonneg (f n : Prog) :
    signAnalysis (.node 12 [f, n]) = .nonneg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    AbsVal.compr]

theorem signAnalysis_comprXOne_nonneg : signAnalysis comprXOne = .nonneg := by
  simpa [comprXOne] using signAnalysis_compr_nonneg (.node 10 []) (.node 1 [])

theorem signAnalysis_condDiffXOneDiviXTwoModuXTwo_nonneg :
    signAnalysis condDiffXOneDiviXTwoModuXTwo = .nonneg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    condDiffXOneDiviXTwoModuXTwo, diffXOne, diviXTwo, moduXTwo, AbsVal.join,
    AbsVal.divi, AbsVal.modu, signDiv, signMod, SignInfo.join, ParityInfo.join,
    AbsVal.nonnegUnknownParity, AbsVal.two]

theorem addiXOne_totalSound : TotalSoundProg addiXOne :=
  TotalSoundProg.core addiXOne_core

theorem diffZeroOne_totalSound : TotalSoundProg diffZeroOne :=
  TotalSoundProg.core diffZeroOne_core

theorem diffXOne_totalSound : TotalSoundProg diffXOne :=
  TotalSoundProg.core diffXOne_core

theorem diviAddiXOneOne_totalSound : TotalSoundProg diviAddiXOneOne := by
  simpa [diviAddiXOneOne] using
    TotalSoundProg.divi addiXOne_totalSound (TotalSoundProg.core CoreProg.one)
      signAnalysis_one_nonzero

theorem diviDiffZeroOneOne_totalSound : TotalSoundProg diviDiffZeroOneOne := by
  simpa [diviDiffZeroOneOne] using
    TotalSoundProg.divi diffZeroOne_totalSound (TotalSoundProg.core CoreProg.one)
      signAnalysis_one_nonzero

theorem diviOneDiffZeroOne_totalSound : TotalSoundProg diviOneDiffZeroOne := by
  simpa [diviOneDiffZeroOne] using
    TotalSoundProg.divi (TotalSoundProg.core CoreProg.one) diffZeroOne_totalSound
      signAnalysis_diffZeroOne_nonzero

theorem diviXTwo_totalSound : TotalSoundProg diviXTwo := by
  simpa [diviXTwo] using
    TotalSoundProg.divi (TotalSoundProg.core CoreProg.x) (TotalSoundProg.core CoreProg.two)
      signAnalysis_two_nonzero

theorem moduAddiXOneOne_totalSound : TotalSoundProg moduAddiXOneOne := by
  simpa [moduAddiXOneOne] using
    TotalSoundProg.modu addiXOne_totalSound (TotalSoundProg.core CoreProg.one)
      signAnalysis_one_nonzero

theorem moduXTwo_totalSound : TotalSoundProg moduXTwo := by
  simpa [moduXTwo] using
    TotalSoundProg.modu (TotalSoundProg.core CoreProg.x) (TotalSoundProg.core CoreProg.two)
      signAnalysis_two_nonzero

theorem condDiffXOneDiviXTwoModuXTwo_totalSound :
    TotalSoundProg condDiffXOneDiviXTwoModuXTwo := by
  simpa [condDiffXOneDiviXTwoModuXTwo] using
    TotalSoundProg.cond diffXOne_totalSound diviXTwo_totalSound moduXTwo_totalSound

theorem signAnalysis_loopAddiXOne_pos : signAnalysis loopAddiXOne = .pos := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    loopAddiXOne, addiXOne, AbsVal.add, signAdd, parityAdd,
    AbsVal.nonnegUnknownParity, AbsVal.one]
  change (analyzeFuel.loopWiden 3 addiXOne AbsVal.nonnegUnknownParity 24 AbsVal.one).sign =
    SignInfo.pos
  rw [show 24 = 23 + 1 by norm_num]
  simp [analyzeFuel.loopWiden, analyzeFuel, addiXOne, AbsVal.add, signAdd, parityAdd,
    SignInfo.join, ParityInfo.join, AbsVal.nonnegUnknownParity, AbsVal.one]

theorem signAnalysis_loop2AddiXOneKeepY_pos : signAnalysis loop2AddiXOneKeepY = .pos := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    loop2AddiXOneKeepY, addiXOne, AbsVal.add, signAdd, parityAdd,
    AbsVal.nonnegUnknownParity, AbsVal.one, AbsVal.zero]
  change (analyzeFuel.loop2Widen 3 addiXOne (.node 11 []) 24 AbsVal.one AbsVal.zero).1.sign =
    SignInfo.pos
  rw [show 24 = 23 + 1 by norm_num]
  simp [analyzeFuel.loop2Widen, analyzeFuel, addiXOne, AbsVal.add, signAdd, parityAdd,
    SignInfo.join, ParityInfo.join, AbsVal.one, AbsVal.zero]

theorem signAnalysis_loop2DiffXOneKeepY_not_nonneg :
    signAnalysis loop2DiffXOneKeepY ≠ .nonneg := by
  simp [signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    loop2DiffXOneKeepY, diffXOne, AbsVal.diff, signAdd, signNeg, parityAdd,
    AbsVal.nonnegUnknownParity, AbsVal.one, AbsVal.zero]
  change (analyzeFuel.loop2Widen 3 diffXOne (.node 11 []) 24 AbsVal.one AbsVal.zero).1.sign ≠
    SignInfo.nonneg
  rw [show 24 = 23 + 1 by norm_num]
  simp [analyzeFuel.loop2Widen, analyzeFuel, diffXOne, AbsVal.diff, signAdd, signNeg, parityAdd,
    SignInfo.join, ParityInfo.join, AbsVal.one, AbsVal.zero]

example : signAnalysis addiXOne = .pos := signAnalysis_addiXOne_pos

example : signAnalysis diffXOne ≠ .nonneg := signAnalysis_diffXOne_not_nonneg

example : (signAnalysis addiXOne).provesNonzero = true := signAnalysis_addiXOne_nonzero

example : (signAnalysis diffXOne).provesNonzero = false :=
  signAnalysis_diffXOne_not_nonzero

example : (signAnalysis diffZeroOne).provesNonzero = true :=
  signAnalysis_diffZeroOne_nonzero

example : parityAnalysis multTwoX = .even :=
  parityAnalysis_multTwoX_even

example : signAnalysis multXX = .nonneg :=
  signAnalysis_multXX_nonneg

example : signAnalysis diviAddiXOneOne = .nonneg :=
  signAnalysis_diviAddiXOneOne_nonneg

example : signAnalysis diviDiffZeroOneOne = .neg :=
  signAnalysis_diviDiffZeroOneOne_neg

example : signAnalysis diviOneDiffZeroOne = .neg :=
  signAnalysis_diviOneDiffZeroOne_neg

example : signAnalysis diviXTwo = .nonneg :=
  signAnalysis_diviXTwo_nonneg

example : signAnalysis moduAddiXOneOne = .nonneg :=
  signAnalysis_moduAddiXOneOne_nonneg

example : signAnalysis moduXTwo = .nonneg :=
  signAnalysis_moduXTwo_nonneg

example : signAnalysis comprXOne = .nonneg :=
  signAnalysis_comprXOne_nonneg

example : signAnalysis condDiffXOneDiviXTwoModuXTwo = .nonneg :=
  signAnalysis_condDiffXOneDiviXTwoModuXTwo_nonneg

example : TotalSoundProg diviAddiXOneOne :=
  diviAddiXOneOne_totalSound

example : TotalSoundProg diviOneDiffZeroOne :=
  diviOneDiffZeroOne_totalSound

example : TotalSoundProg moduAddiXOneOne :=
  moduAddiXOneOne_totalSound

example : TotalSoundProg diviXTwo :=
  diviXTwo_totalSound

example : TotalSoundProg moduXTwo :=
  moduXTwo_totalSound

example : TotalSoundProg condDiffXOneDiviXTwoModuXTwo :=
  condDiffXOneDiviXTwoModuXTwo_totalSound

example : signAnalysis loop2AddiXOneKeepY = .pos := signAnalysis_loop2AddiXOneKeepY_pos

example : signAnalysis loop2DiffXOneKeepY ≠ .nonneg :=
  signAnalysis_loop2DiffXOneKeepY_not_nonneg

example : parityAnalysis (.node 2 []) = .even := by
  simp [parityAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, AbsVal.two]

example : parityAnalysis addiXOne ≠ .even := by
  simp [parityAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    addiXOne, AbsVal.add, parityAdd, AbsVal.nonnegUnknownParity, AbsVal.one]

theorem parityAnalysis_two_even : parityAnalysis (.node 2 []) = .even := by
  simp [parityAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, AbsVal.two]

theorem parityAnalysis_one_odd : parityAnalysis (.node 1 []) = .odd := by
  simp [parityAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, AbsVal.one]

theorem parityAnalysis_two_sound {fuel : Nat} {cfg : Config} {st st' : Store} {v : Int}
    (h : eval (fuel + 1) orgE1Signature (.node 2 []) cfg st = some (v, st')) :
    (parityAnalysis (.node 2 [])).denote v := by
  simp [eval, orgE1Signature, entryAt, listGet?, entry] at h
  simp [parityAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, AbsVal.two,
    ParityInfo.denote, EvenInt]
  exact ⟨1, by omega⟩

theorem parityAnalysis_one_sound {fuel : Nat} {cfg : Config} {st st' : Store} {v : Int}
    (h : eval (fuel + 1) orgE1Signature (.node 1 []) cfg st = some (v, st')) :
    (parityAnalysis (.node 1 [])).denote v := by
  simp [eval, orgE1Signature, entryAt, listGet?, entry] at h
  simp [parityAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, AbsVal.one,
    ParityInfo.denote, OddInt]
  exact ⟨0, by omega⟩

theorem eval_addiXOne_defined (fuel : Nat) (n : Int) :
    eval (fuel + 2) orgE1Signature addiXOne (seed n) Store.zero =
      some (n + 1, Store.zero) := by
  simp [addiXOne, eval, orgE1Signature, entryAt, listGet?, entry, seed]

theorem eval_addiXOne_config (fuel : Nat) (cfg : Config) (st : Store) :
    eval (fuel + 2) orgE1Signature addiXOne cfg st = some (cfg.x + 1, st) := by
  simp [addiXOne, eval, orgE1Signature, entryAt, listGet?, entry]

theorem loopIter_addiXOne_defined (k : Nat) (acc counter input : Int) (st : Store) :
    loopIter (k + 2) orgE1Signature addiXOne k acc counter input st =
      some (acc + (k : Int), st) := by
  induction k generalizing acc counter with
  | zero =>
      simp [loopIter]
  | succ k ih =>
      rw [show k.succ + 2 = (k + 2) + 1 by omega]
      simp [loopIter, eval_addiXOne_config, ih]
      omega

theorem eval_loopAddiXOne_defined (n : Int) (hn : 0 <= n) :
    eval (n.toNat + 3) orgE1Signature loopAddiXOne (seed n) Store.zero =
      some (n + 1, Store.zero) := by
  have hnat : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg hn
  simp [loopAddiXOne, eval, orgE1Signature, entryAt, listGet?, entry, seed]
  change loopIter (n.toNat + 2) orgE1Signature addiXOne n.toNat 1 1 1 Store.zero =
    some (n + 1, Store.zero)
  rw [loopIter_addiXOne_defined]
  rw [hnat]
  ring_nf

theorem addiXOne_pos_sound {fuel : Nat} {n v : Int} {st' : Store}
    (h : eval (fuel + 2) orgE1Signature addiXOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : 0 < v := by
  simp [addiXOne, eval, orgE1Signature, entryAt, listGet?, entry, seed] at h
  omega

theorem addiXOne_pos_sound_from_analysis {fuel : Nat} {n v : Int} {st' : Store}
    (h : eval fuel orgE1Signature addiXOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : 0 < v := by
  apply CoreProg.signAnalysis_pos_sound_seed addiXOne_core hn
  · simp [signAnalysis_addiXOne_pos, SignInfo.provesPos]
  · exact h

theorem addiXOne_pos_sound_from_coreOnly {fuel : Nat} {n v : Int} {st' : Store}
    (h : eval fuel orgE1Signature addiXOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : 0 < v := by
  apply CoreProg.signAnalysis_pos_sound_seed_of_coreOnly coreOnly_addiXOne hn
  · simp [signAnalysis_addiXOne_pos, SignInfo.provesPos]
  · exact h

theorem addiXOne_pos_sound_from_public_analysis {fuel : Nat} {n v : Int} {st' : Store}
    (h : eval fuel orgE1Signature addiXOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : 0 < v := by
  exact AnalysisSoundProg.signAnalysis_pos_sound_seed addiXOne_analysisSound hn
    (by simp [signAnalysis_addiXOne_pos, SignInfo.provesPos]) h

theorem addiXOne_nonzero_sound_from_public_analysis {fuel : Nat} {n v : Int}
    {st' : Store}
    (h : eval fuel orgE1Signature addiXOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : v ≠ 0 := by
  exact AnalysisSoundProg.signAnalysis_nonzero_sound_seed addiXOne_analysisSound hn
    signAnalysis_addiXOne_nonzero h

theorem diviAddiXOneOne_nonneg_sound_from_public_analysis {fuel : Nat} {n v : Int}
    {st' : Store}
    (h : eval fuel orgE1Signature diviAddiXOneOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : 0 <= v := by
  exact AnalysisSoundProg.signAnalysis_nonneg_sound_seed diviAddiXOneOne_analysisSound hn
    (by simp [signAnalysis_diviAddiXOneOne_nonneg, SignInfo.provesNonneg]) h

theorem diviDiffZeroOneOne_neg_sound_from_public_analysis {fuel : Nat} {n v : Int}
    {st' : Store}
    (h : eval fuel orgE1Signature diviDiffZeroOneOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : v < 0 := by
  exact AnalysisSoundProg.signAnalysis_neg_sound_seed diviDiffZeroOneOne_analysisSound hn
    (by simp [signAnalysis_diviDiffZeroOneOne_neg, SignInfo.provesNeg]) h

theorem diffZeroOne_nonpos_sound_from_public_analysis {fuel : Nat} {n v : Int}
    {st' : Store}
    (h : eval fuel orgE1Signature diffZeroOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : v <= 0 := by
  exact AnalysisSoundProg.signAnalysis_nonpos_sound_seed
    (AnalysisSoundProg.core diffZeroOne_core) hn
    (by simp [signAnalysis_diffZeroOne_neg, SignInfo.provesNonpos]) h

theorem diviOneDiffZeroOne_neg_sound_from_public_analysis {fuel : Nat} {n v : Int}
    {st' : Store}
    (h : eval fuel orgE1Signature diviOneDiffZeroOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : v < 0 := by
  exact AnalysisSoundProg.signAnalysis_neg_sound_seed diviOneDiffZeroOne_analysisSound hn
    (by simp [signAnalysis_diviOneDiffZeroOne_neg, SignInfo.provesNeg]) h

theorem moduAddiXOneOne_nonneg_sound_from_public_analysis {fuel : Nat} {n v : Int}
    {st' : Store}
    (h : eval fuel orgE1Signature moduAddiXOneOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : 0 <= v := by
  exact AnalysisSoundProg.signAnalysis_nonneg_sound_seed moduAddiXOneOne_analysisSound hn
    (by simp [signAnalysis_moduAddiXOneOne_nonneg, SignInfo.provesNonneg]) h

theorem compr_nonneg_sound_from_public_analysis {f count : Prog} {fuel : Nat} {n v : Int}
    {st' : Store}
    (h : eval fuel orgE1Signature (.node 12 [f, count]) (seed n) Store.zero =
      some (v, st'))
    (hn : 0 <= n) : 0 <= v := by
  exact AnalysisSoundProg.signAnalysis_nonneg_sound_seed
    (AnalysisSoundProg.compr (f := f) (n := count)) hn
    (by simp [signAnalysis_compr_nonneg, SignInfo.provesNonneg]) h

theorem comprXOne_nonneg_sound_from_public_analysis {fuel : Nat} {n v : Int}
    {st' : Store}
    (h : eval fuel orgE1Signature comprXOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : 0 <= v := by
  simpa [comprXOne] using
    compr_nonneg_sound_from_public_analysis (f := .node 10 []) (count := .node 1 [])
      h hn

theorem multTwoX_even_sound_from_analysis {fuel : Nat} {n v : Int} {st' : Store}
    (h : eval fuel orgE1Signature multTwoX (seed n) Store.zero = some (v, st')) :
    EvenInt v := by
  exact CoreProg.parityAnalysis_even_sound_seed multTwoX_core
    (by simp [parityAnalysis_multTwoX_even, ParityInfo.provesEven]) h

theorem multXX_nonneg_sound_from_analysis {fuel : Nat} {n v : Int} {st' : Store}
    (h : eval fuel orgE1Signature multXX (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : 0 <= v := by
  exact CoreProg.signAnalysis_nonneg_sound_seed multXX_core hn
    (by simp [signAnalysis_multXX_nonneg, SignInfo.provesNonneg]) h

theorem condDiffXOneDiviXTwoModuXTwo_nonneg_sound_from_public_analysis {fuel : Nat}
    {n v : Int} {st' : Store}
    (h : eval fuel orgE1Signature condDiffXOneDiviXTwoModuXTwo (seed n) Store.zero =
      some (v, st'))
    (hn : 0 <= n) : 0 <= v := by
  exact AnalysisSoundProg.signAnalysis_nonneg_sound_seed
    (TotalSoundProg.analysisSound condDiffXOneDiviXTwoModuXTwo_totalSound) hn
    (by simp [signAnalysis_condDiffXOneDiviXTwoModuXTwo_nonneg, SignInfo.provesNonneg]) h

theorem totalAnalysis_addiXOne : totalAnalysis addiXOne = true :=
  CoreProg.totalAnalysis_true addiXOne_core

theorem totalAnalysis_diffXOne : totalAnalysis diffXOne = true :=
  CoreProg.totalAnalysis_true diffXOne_core

theorem totalAnalysis_diviAddiXOneOne : totalAnalysis diviAddiXOneOne = true := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diviAddiXOneOne, addiXOne, AbsVal.divi, AbsVal.add, signAdd, parityAdd,
    AbsVal.nonnegUnknownParity, AbsVal.one, SignInfo.provesNonzero]

theorem totalAnalysis_moduAddiXOneOne : totalAnalysis moduAddiXOneOne = true := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    moduAddiXOneOne, addiXOne, AbsVal.modu, AbsVal.add, signAdd, parityAdd, signMod,
    AbsVal.nonnegUnknownParity, AbsVal.one, SignInfo.provesNonzero]

theorem totalAnalysis_diviDiffZeroOneOne : totalAnalysis diviDiffZeroOneOne = true := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diviDiffZeroOneOne, diffZeroOne, AbsVal.divi, AbsVal.diff, signDiv, signAdd, signNeg,
    parityAdd, AbsVal.zero, AbsVal.one, SignInfo.provesNonzero]

theorem totalAnalysis_diviOneDiffZeroOne : totalAnalysis diviOneDiffZeroOne = true := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diviOneDiffZeroOne, diffZeroOne, AbsVal.divi, AbsVal.diff, signDiv, signAdd, signNeg,
    parityAdd, AbsVal.zero, AbsVal.one, SignInfo.provesNonzero]

theorem totalAnalysis_diviOneX_false : totalAnalysis diviOneX = false := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diviOneX, AbsVal.divi, signDiv, AbsVal.one, AbsVal.nonnegUnknownParity,
    SignInfo.provesNonzero]

theorem totalAnalysis_diviXTwo : totalAnalysis diviXTwo = true := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diviXTwo, AbsVal.divi, signDiv, AbsVal.nonnegUnknownParity, AbsVal.two,
    SignInfo.provesNonzero]

theorem totalAnalysis_moduXTwo : totalAnalysis moduXTwo = true := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    moduXTwo, AbsVal.modu, signMod, AbsVal.nonnegUnknownParity, AbsVal.two,
    SignInfo.provesNonzero]

theorem totalAnalysis_compr_false (f n : Prog) :
    totalAnalysis (.node 12 [f, n]) = false := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    AbsVal.compr]

theorem totalAnalysis_comprXOne_false : totalAnalysis comprXOne = false := by
  simpa [comprXOne] using totalAnalysis_compr_false (.node 10 []) (.node 1 [])

theorem analysisSupported_comprXOne : analysisSupported comprXOne = true := by
  rfl

theorem analysisSupported_addiXOne : analysisSupported addiXOne = true := by
  rfl

theorem analysisSupported_diffZeroOne : analysisSupported diffZeroOne = true := by
  rfl

theorem totalSupported_diviAddiXOneOne : totalSupported diviAddiXOneOne = true := by
  simp [totalSupported, totalCert?, totalCertFuel?, diviAddiXOneOne, addiXOne,
    coreOnly, progHeight, progHeight.listHeight, signAnalysis_one_nonzero]

theorem totalSupported_diviOneX_false : totalSupported diviOneX = false := by
  simp [totalSupported, totalCert?, totalCertFuel?, diviOneX, coreOnly,
    signAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    AbsVal.nonnegUnknownParity, SignInfo.provesNonzero]

theorem totalSupported_comprXOne_false : totalSupported comprXOne = false := by
  rfl

theorem not_core_compr (f n : Prog) : ¬ CoreProg (.node 12 [f, n]) := by
  intro h
  cases h

theorem no_totalSound_compr (f n : Prog) :
    ¬ TotalSoundProg (.node 12 [f, n]) := by
  intro h
  cases h with
  | core hp => exact not_core_compr f n hp

theorem totalAnalysis_condDiffXOneDiviXTwoModuXTwo :
    totalAnalysis condDiffXOneDiviXTwoModuXTwo = true := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    condDiffXOneDiviXTwoModuXTwo, diffXOne, diviXTwo, moduXTwo, AbsVal.join,
    AbsVal.divi, AbsVal.modu, AbsVal.diff, signDiv, signMod, signAdd, signNeg, parityAdd,
    AbsVal.nonnegUnknownParity, AbsVal.one, AbsVal.two, SignInfo.provesNonzero]

theorem totalAnalysis_condZeroOneDiviOneX_false :
    totalAnalysis condZeroOneDiviOneX = false := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    condZeroOneDiviOneX, diviOneX, AbsVal.join, AbsVal.divi, signDiv,
    AbsVal.one, AbsVal.nonnegUnknownParity, SignInfo.provesNonzero]

theorem totalAnalysis_condDiviOneXOneOne_false :
    totalAnalysis condDiviOneXOneOne = false := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    condDiviOneXOneOne, diviOneX, AbsVal.join, AbsVal.divi, signDiv,
    AbsVal.one, AbsVal.nonnegUnknownParity, SignInfo.provesNonzero]

theorem totalAnalysis_diviAddiXOneDiffXOne_false :
    totalAnalysis diviAddiXOneDiffXOne = false := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    diviAddiXOneDiffXOne, addiXOne, diffXOne, AbsVal.divi, AbsVal.add, AbsVal.diff,
    signDiv, signAdd, signNeg, parityAdd, AbsVal.nonnegUnknownParity, AbsVal.one,
    SignInfo.provesNonzero]

theorem eval_diviOneX_fails_at_zero :
    eval 3 orgE1Signature diviOneX (seed 0) Store.zero = none := by
  simp [diviOneX, eval, orgE1Signature, entryAt, listGet?, entry, seed, sdiv]

theorem eval_diviAddiXOneDiffXOne_fails_at_one :
    eval 3 orgE1Signature diviAddiXOneDiffXOne (seed 1) Store.zero = none := by
  simp [diviAddiXOneDiffXOne, addiXOne, diffXOne, eval, orgE1Signature, entryAt,
    listGet?, entry, seed, sdiv]

theorem eval_condZeroOneDiviOneX_defined_at_zero :
    eval 3 orgE1Signature condZeroOneDiviOneX (seed 0) Store.zero = some (1, Store.zero) := by
  simp [condZeroOneDiviOneX, diviOneX, eval, orgE1Signature, entryAt, listGet?, entry, seed]

theorem eval_condDiviOneXOneOne_fails_at_zero :
    eval 3 orgE1Signature condDiviOneXOneOne (seed 0) Store.zero = none := by
  simp [condDiviOneXOneOne, diviOneX, eval, orgE1Signature, entryAt, listGet?, entry, seed,
    sdiv]

theorem eval_comprXOne_fuel_four_none :
    eval 4 orgE1Signature comprXOne (seed 0) Store.zero = none := by
  simp [comprXOne, eval, comprSearch, orgE1Signature, entryAt, listGet?, entry, seed]

theorem comprSearch_x_one_seen_one_positive_none :
    ∀ (fuel : Nat) {cand : Int} (st : Store),
      0 < cand ->
      comprSearch fuel orgE1Signature (.node 10 []) 1 1 cand st = none
  | 0, _cand, _st, _hpos => by
      simp [comprSearch]
  | fuel + 1, cand, st, hpos => by
      cases fuel with
      | zero =>
          simp [comprSearch, eval]
      | succ fuel =>
          have hEval :
              eval (fuel + 1) orgE1Signature (.node 10 []) { x := cand, y := 0, z := 0 } st =
                some (cand, st) := by
            simp [eval, orgE1Signature, entryAt, listGet?, entry]
          have hnot : ¬ cand <= 0 := by omega
          have hstep :
              comprSearch (fuel + 1 + 1) orgE1Signature (.node 10 []) 1 1 cand st =
                ((eval (fuel + 1) orgE1Signature (.node 10 [])
                    { x := cand, y := 0, z := 0 } st).bind fun r =>
                  if r.1 <= 0 then
                    if 1 >= 1 then some (cand, r.2)
                    else comprSearch (fuel + 1) orgE1Signature (.node 10 []) 1 (1 + 1)
                      (cand + 1) r.2
                  else
                    comprSearch (fuel + 1) orgE1Signature (.node 10 []) 1 1
                      (cand + 1) r.2) := by
            simp [comprSearch]
          rw [hstep, hEval]
          simp [hnot]
          exact comprSearch_x_one_seen_one_positive_none (fuel + 1) (cand := cand + 1) st
            (by omega)

theorem comprSearch_x_one_zero_zero_none (fuel : Nat) (st : Store) :
    comprSearch fuel orgE1Signature (.node 10 []) 1 0 0 st = none := by
  cases fuel with
  | zero =>
      simp [comprSearch]
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [comprSearch, eval]
      | succ fuel =>
          have hEval :
              eval (fuel + 1) orgE1Signature (.node 10 []) { x := 0, y := 0, z := 0 } st =
                some (0, st) := by
            simp [eval, orgE1Signature, entryAt, listGet?, entry]
          have hseen : ¬ (0 : Nat) >= 1 := by omega
          have hstep :
              comprSearch (fuel + 1 + 1) orgE1Signature (.node 10 []) 1 0 0 st =
                ((eval (fuel + 1) orgE1Signature (.node 10 []) { x := 0, y := 0, z := 0 }
                    st).bind fun r =>
                  if r.1 <= 0 then
                    if 0 >= 1 then some (0, r.2)
                    else comprSearch (fuel + 1) orgE1Signature (.node 10 []) 1 (0 + 1)
                      (0 + 1) r.2
                  else
                    comprSearch (fuel + 1) orgE1Signature (.node 10 []) 1 0 (0 + 1) r.2) := by
            simp [comprSearch]
          rw [hstep, hEval]
          simp [hseen]
          exact comprSearch_x_one_seen_one_positive_none (fuel + 1) (cand := 1) st
            (by norm_num)

theorem eval_comprXOne_none (fuel : Nat) :
    eval fuel orgE1Signature comprXOne (seed 0) Store.zero = none := by
  cases fuel with
  | zero =>
      simp [eval]
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [comprXOne, eval, orgE1Signature, entryAt, listGet?, entry, seed]
      | succ fuel =>
          simp [comprXOne, eval, orgE1Signature, entryAt, listGet?, entry, seed]
          exact comprSearch_x_one_zero_zero_none (fuel + 1) Store.zero

theorem totalAnalysis_addiXOne_defined (fuel : Nat) (n : Int) :
    (eval (fuel + 2) orgE1Signature addiXOne (seed n) Store.zero).isSome = true := by
  rw [eval_addiXOne_defined]
  rfl

theorem eval_diviAddiXOneOne_defined (fuel : Nat) (n : Int) :
    eval (fuel + 3) orgE1Signature diviAddiXOneOne (seed n) Store.zero =
      some (Int.fdiv (n + 1) 1, Store.zero) := by
  have ha : eval (fuel + 2) orgE1Signature addiXOne (seed n) Store.zero =
      some (n + 1, Store.zero) :=
    eval_addiXOne_defined fuel n
  have hb : eval (fuel + 2) orgE1Signature (.node 1 []) (seed n) Store.zero =
      some (1, Store.zero) := by
    simp [eval, orgE1Signature, entryAt, listGet?, entry]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  simpa [diviAddiXOneOne] using
    eval_divi_defined_of_analysis_parts (a := addiXOne) (b := .node 1 [])
      (hbCert := AnalysisSoundProg.core CoreProg.one)
      (fuelA := 1) (evalFuel := fuel + 2)
      (xVal := AbsVal.top) (yVal := AbsVal.zeroReg)
      (cfg := seed n) (st := Store.zero) (sta := Store.zero) (stb := Store.zero)
      (va := n + 1) (vb := 1)
      (by
        simp [CfgSignSound, AbsVal.top, AbsVal.zeroReg, SignInfo.denote, seed])
      (by simp [analyzeFuel, AbsVal.one, SignInfo.provesNonzero])
      ha hb

theorem eval_moduAddiXOneOne_defined (fuel : Nat) (n : Int) :
    eval (fuel + 3) orgE1Signature moduAddiXOneOne (seed n) Store.zero =
      some (Int.fmod (n + 1) 1, Store.zero) := by
  have ha : eval (fuel + 2) orgE1Signature addiXOne (seed n) Store.zero =
      some (n + 1, Store.zero) :=
    eval_addiXOne_defined fuel n
  have hb : eval (fuel + 2) orgE1Signature (.node 1 []) (seed n) Store.zero =
      some (1, Store.zero) := by
    simp [eval, orgE1Signature, entryAt, listGet?, entry]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  simpa [moduAddiXOneOne] using
    eval_modu_defined_of_analysis_parts (a := addiXOne) (b := .node 1 [])
      (hbCert := AnalysisSoundProg.core CoreProg.one)
      (fuelA := 1) (evalFuel := fuel + 2)
      (xVal := AbsVal.top) (yVal := AbsVal.zeroReg)
      (cfg := seed n) (st := Store.zero) (sta := Store.zero) (stb := Store.zero)
      (va := n + 1) (vb := 1)
      (by
        simp [CfgSignSound, AbsVal.top, AbsVal.zeroReg, SignInfo.denote, seed])
      (by simp [analyzeFuel, AbsVal.one, SignInfo.provesNonzero])
      ha hb

theorem totalAnalysis_addiXOne_sound (n : Int) :
    totalAnalysis addiXOne = true ∧
      ∃ v st', eval (progHeight addiXOne + 1) orgE1Signature addiXOne
        (seed n) Store.zero = some (v, st') :=
  CoreProg.totalAnalysis_sound addiXOne_core (seed n) Store.zero

theorem totalAnalysis_diviAddiXOneOne_sound_from_totalSound (n : Int) (hn : 0 <= n) :
    totalAnalysis diviAddiXOneOne = true ∧
      ∃ v st', eval (progHeight diviAddiXOneOne + 1) orgE1Signature diviAddiXOneOne
        (seed n) Store.zero = some (v, st') :=
  TotalSoundProg.totalAnalysis_sound diviAddiXOneOne_totalSound
    totalAnalysis_diviAddiXOneOne Store.zero hn

theorem totalAnalysis_diviOneDiffZeroOne_sound_from_totalSound (n : Int) (hn : 0 <= n) :
    totalAnalysis diviOneDiffZeroOne = true ∧
      ∃ v st', eval (progHeight diviOneDiffZeroOne + 1) orgE1Signature diviOneDiffZeroOne
        (seed n) Store.zero = some (v, st') :=
  TotalSoundProg.totalAnalysis_sound diviOneDiffZeroOne_totalSound
    totalAnalysis_diviOneDiffZeroOne Store.zero hn

theorem totalAnalysis_moduAddiXOneOne_sound_from_totalSound (n : Int) (hn : 0 <= n) :
    totalAnalysis moduAddiXOneOne = true ∧
      ∃ v st', eval (progHeight moduAddiXOneOne + 1) orgE1Signature moduAddiXOneOne
        (seed n) Store.zero = some (v, st') :=
  TotalSoundProg.totalAnalysis_sound moduAddiXOneOne_totalSound
    totalAnalysis_moduAddiXOneOne Store.zero hn

theorem totalAnalysis_diviXTwo_sound_from_totalSound (n : Int) (hn : 0 <= n) :
    totalAnalysis diviXTwo = true ∧
      ∃ v st', eval (progHeight diviXTwo + 1) orgE1Signature diviXTwo
        (seed n) Store.zero = some (v, st') :=
  TotalSoundProg.totalAnalysis_sound diviXTwo_totalSound
    totalAnalysis_diviXTwo Store.zero hn

theorem totalAnalysis_moduXTwo_sound_from_totalSound (n : Int) (hn : 0 <= n) :
    totalAnalysis moduXTwo = true ∧
      ∃ v st', eval (progHeight moduXTwo + 1) orgE1Signature moduXTwo
        (seed n) Store.zero = some (v, st') :=
  TotalSoundProg.totalAnalysis_sound moduXTwo_totalSound
    totalAnalysis_moduXTwo Store.zero hn

theorem totalAnalysis_condDiffXOneDiviXTwoModuXTwo_sound_from_totalSound
    (n : Int) (hn : 0 <= n) :
    totalAnalysis condDiffXOneDiviXTwoModuXTwo = true ∧
      ∃ v st',
        eval (progHeight condDiffXOneDiviXTwoModuXTwo + 1) orgE1Signature
          condDiffXOneDiviXTwoModuXTwo (seed n) Store.zero = some (v, st') :=
  TotalSoundProg.totalAnalysis_sound condDiffXOneDiviXTwoModuXTwo_totalSound
    totalAnalysis_condDiffXOneDiviXTwoModuXTwo Store.zero hn

theorem totalAnalysis_loopAddiXOne : totalAnalysis loopAddiXOne = true := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    loopAddiXOne, addiXOne, AbsVal.add, signAdd, parityAdd,
    AbsVal.nonnegUnknownParity, AbsVal.one]

theorem loopAddiXOne_defined_from_total_parts (n : Int) (hn : 0 <= n) :
    ∃ v st', eval (n.toNat + 4) orgE1Signature loopAddiXOne (seed n) Store.zero =
      some (v, st') := by
  have hcountFuel : progHeight (.node 10 []) < n.toNat + 3 := by
    simp [progHeight]
  have hinitFuel : progHeight (.node 1 []) < n.toNat + 3 := by
    simp [progHeight]
  have hbodyFuel : ∀ {cnt : Int} {stCount : Store},
      eval (n.toNat + 3) orgE1Signature (.node 10 []) (seed n) Store.zero =
        some (cnt, stCount) ->
      progHeight addiXOne + cnt.toNat + 1 <= n.toNat + 3 := by
    intro cnt stCount hcnt
    simp [eval, orgE1Signature, entryAt, listGet?, entry, seed] at hcnt
    rcases hcnt with ⟨rfl, rfl⟩
    simp [addiXOne, progHeight, progHeight.listHeight]
    omega
  simpa [loopAddiXOne] using
    TotalSoundProg.eval_loop_defined_of_total_parts
      (body := addiXOne) (count := .node 10 []) (init := .node 1 [])
      addiXOne_core (TotalSoundProg.core CoreProg.x) (TotalSoundProg.core CoreProg.one)
      (fuel := n.toNat + 3) (n := n) Store.zero hn hcountFuel hinitFuel hbodyFuel

theorem totalAnalysis_loopAddiXOne_sound_from_total_parts (n : Int) (hn : 0 <= n) :
    totalAnalysis loopAddiXOne = true ∧
      ∃ v st', eval (n.toNat + 4) orgE1Signature loopAddiXOne (seed n) Store.zero =
        some (v, st') :=
  ⟨totalAnalysis_loopAddiXOne, loopAddiXOne_defined_from_total_parts n hn⟩

theorem totalAnalysis_loop2AddiXOneKeepY : totalAnalysis loop2AddiXOneKeepY = true := by
  simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
    loop2AddiXOneKeepY, addiXOne, AbsVal.add, signAdd, parityAdd,
    AbsVal.nonnegUnknownParity, AbsVal.one, AbsVal.zero]

theorem loop2AddiXOneKeepY_defined_from_total_parts (n : Int) (hn : 0 <= n) :
    ∃ v st', eval (n.toNat + 4) orgE1Signature loop2AddiXOneKeepY (seed n) Store.zero =
      some (v, st') := by
  have hcountFuel : progHeight (.node 10 []) < n.toNat + 3 := by
    simp [progHeight]
  have haFuel : progHeight (.node 1 []) < n.toNat + 3 := by
    simp [progHeight]
  have hbFuel : progHeight (.node 0 []) < n.toNat + 3 := by
    simp [progHeight]
  have hfFuel : ∀ {cnt : Int} {stCount : Store},
      eval (n.toNat + 3) orgE1Signature (.node 10 []) (seed n) Store.zero =
        some (cnt, stCount) ->
      progHeight addiXOne + cnt.toNat + 1 <= n.toNat + 3 := by
    intro cnt stCount hcnt
    simp [eval, orgE1Signature, entryAt, listGet?, entry, seed] at hcnt
    rcases hcnt with ⟨rfl, rfl⟩
    simp [addiXOne, progHeight, progHeight.listHeight]
    omega
  have hgFuel : ∀ {cnt : Int} {stCount : Store},
      eval (n.toNat + 3) orgE1Signature (.node 10 []) (seed n) Store.zero =
        some (cnt, stCount) ->
      progHeight (.node 11 []) + cnt.toNat + 1 <= n.toNat + 3 := by
    intro cnt stCount hcnt
    simp [eval, orgE1Signature, entryAt, listGet?, entry, seed] at hcnt
    rcases hcnt with ⟨rfl, rfl⟩
    simp [progHeight]
    omega
  simpa [loop2AddiXOneKeepY] using
    TotalSoundProg.eval_loop2_defined_of_total_parts
      (f := addiXOne) (g := .node 11 []) (count := .node 10 [])
      (a := .node 1 []) (b := .node 0 [])
      addiXOne_core CoreProg.y (TotalSoundProg.core CoreProg.x)
      (TotalSoundProg.core CoreProg.one) (TotalSoundProg.core CoreProg.zero)
      (fuel := n.toNat + 3) (n := n) Store.zero hn hcountFuel haFuel hbFuel hfFuel hgFuel

theorem totalAnalysis_loop2AddiXOneKeepY_sound_from_total_parts (n : Int) (hn : 0 <= n) :
    totalAnalysis loop2AddiXOneKeepY = true ∧
      ∃ v st', eval (n.toNat + 4) orgE1Signature loop2AddiXOneKeepY (seed n) Store.zero =
        some (v, st') :=
  ⟨totalAnalysis_loop2AddiXOneKeepY, loop2AddiXOneKeepY_defined_from_total_parts n hn⟩

theorem loopAddiXOne_defined_from_core_totality (n : Int) :
    ∃ v st', eval (n.toNat + 4) orgE1Signature loopAddiXOne (seed n) Store.zero =
      some (v, st') := by
  have hcount : eval (n.toNat + 3) orgE1Signature (.node 10 []) (seed n) Store.zero =
      some (n, Store.zero) := by
    simp [eval, orgE1Signature, entryAt, listGet?, entry, seed]
  have hinit : eval (n.toNat + 3) orgE1Signature (.node 1 []) (seed n) Store.zero =
      some (1, Store.zero) := by
    simp [eval, orgE1Signature, entryAt, listGet?, entry, seed]
  have hfuel : progHeight addiXOne + n.toNat + 1 <= n.toNat + 3 := by
    simp [addiXOne, progHeight, progHeight.listHeight]
    omega
  simpa [loopAddiXOne] using
    CoreProg.eval_loop_defined_of_core_parts (fuel := n.toNat + 3) (body := addiXOne)
      (count := .node 10 []) (init := .node 1 []) addiXOne_core hcount hinit hfuel

theorem loop2AddiXOneKeepY_defined_from_core_totality (n : Int) :
    ∃ v st', eval (n.toNat + 4) orgE1Signature loop2AddiXOneKeepY (seed n) Store.zero =
      some (v, st') := by
  have hcount : eval (n.toNat + 3) orgE1Signature (.node 10 []) (seed n) Store.zero =
      some (n, Store.zero) := by
    simp [eval, orgE1Signature, entryAt, listGet?, entry, seed]
  have ha : eval (n.toNat + 3) orgE1Signature (.node 1 []) (seed n) Store.zero =
      some (1, Store.zero) := by
    simp [eval, orgE1Signature, entryAt, listGet?, entry, seed]
  have hb : eval (n.toNat + 3) orgE1Signature (.node 0 []) (seed n) Store.zero =
      some (0, Store.zero) := by
    simp [eval, orgE1Signature, entryAt, listGet?, entry, seed]
  have hfuel : progHeight addiXOne + n.toNat + 1 <= n.toNat + 3 := by
    simp [addiXOne, progHeight, progHeight.listHeight]
    omega
  have hgfuel : progHeight (.node 11 []) + n.toNat + 1 <= n.toNat + 3 := by
    simp [progHeight]
    omega
  simpa [loop2AddiXOneKeepY] using
    CoreProg.eval_loop2_defined_of_core_parts (fuel := n.toNat + 3) (f := addiXOne)
      (g := .node 11 []) (count := .node 10 []) (a := .node 1 []) (b := .node 0 [])
      addiXOne_core CoreProg.y hcount ha hb hfuel hgfuel

theorem loopAddiXOne_pos_sound (n : Int) (hn : 0 <= n) :
    eval (n.toNat + 3) orgE1Signature loopAddiXOne (seed n) Store.zero =
      some (n + 1, Store.zero) ∧ 0 < n + 1 := by
  exact ⟨eval_loopAddiXOne_defined n hn, by omega⟩

theorem loopAddiXOne_pos_sound_from_analysis (n : Int) (hn : 0 <= n) :
    (signAnalysis loopAddiXOne).provesPos = true ∧
      eval (n.toNat + 3) orgE1Signature loopAddiXOne (seed n) Store.zero =
        some (n + 1, Store.zero) ∧ 0 < n + 1 := by
  exact ⟨by simp [signAnalysis_loopAddiXOne_pos, SignInfo.provesPos],
    loopAddiXOne_pos_sound n hn⟩

theorem loopAddiXOne_pos_sound_from_loop_transfer {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (heval : eval fuel orgE1Signature loopAddiXOne (seed n) Store.zero = some (v, st')) :
    0 < v := by
  have hden : (signAnalysis loopAddiXOne).denote v := by
    simpa [signAnalysis, analyze, analyzeWith, loopAddiXOne] using
      loop_sign_sound_core_body_init (body := addiXOne) (count := .node 10 [])
        (init := .node 1 []) addiXOne_core CoreProg.one
        (progHeight loopAddiXOne + 1) fuel AbsVal.nonnegUnknownParity AbsVal.zeroReg
        (seed n) Store.zero st' v
        (by
          simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, SignInfo.denote, seed]
          exact hn)
        heval
  exact SignInfo.provesPos_sound
    (by simp [signAnalysis_loopAddiXOne_pos, SignInfo.provesPos]) hden

theorem loopAddiXOne_pos_sound_from_public_analysis {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (heval : eval fuel orgE1Signature loopAddiXOne (seed n) Store.zero = some (v, st')) :
    0 < v := by
  exact AnalysisSoundProg.signAnalysis_pos_sound_seed loopAddiXOne_analysisSound hn
    (by simp [signAnalysis_loopAddiXOne_pos, SignInfo.provesPos]) heval

theorem loop2AddiXOneKeepY_pos_sound_from_loop2_transfer {fuel : Nat} {n v : Int}
    {st' : Store}
    (hn : 0 <= n)
    (heval : eval fuel orgE1Signature loop2AddiXOneKeepY (seed n) Store.zero = some (v, st')) :
    0 < v := by
  have hden : (signAnalysis loop2AddiXOneKeepY).denote v := by
    simpa [signAnalysis, analyze, analyzeWith, loop2AddiXOneKeepY] using
      loop2_sign_sound_core_body_init (f := addiXOne) (g := .node 11 [])
        (count := .node 10 []) (a := .node 1 []) (b := .node 0 [])
        addiXOne_core CoreProg.y CoreProg.one CoreProg.zero
        (progHeight loop2AddiXOneKeepY + 1) fuel
        AbsVal.nonnegUnknownParity AbsVal.zeroReg (seed n) Store.zero st' v
        (by
          simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg, SignInfo.denote, seed]
          exact hn)
        heval
  exact SignInfo.provesPos_sound
    (by simp [signAnalysis_loop2AddiXOneKeepY_pos, SignInfo.provesPos]) hden

theorem loop2AddiXOneKeepY_pos_sound_from_public_analysis {fuel : Nat} {n v : Int}
    {st' : Store}
    (hn : 0 <= n)
    (heval : eval fuel orgE1Signature loop2AddiXOneKeepY (seed n) Store.zero = some (v, st')) :
    0 < v := by
  exact AnalysisSoundProg.signAnalysis_pos_sound_seed loop2AddiXOneKeepY_analysisSound hn
    (by simp [signAnalysis_loop2AddiXOneKeepY_pos, SignInfo.provesPos]) heval

namespace Seal

theorem sign_nonneg {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNonneg = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    0 <= v :=
  AnalysisSoundProg.signAnalysis_nonneg_sound_seed hp hn hs heval

theorem sign_nonpos {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNonpos = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    v <= 0 :=
  AnalysisSoundProg.signAnalysis_nonpos_sound_seed hp hn hs heval

theorem sign_pos {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesPos = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    0 < v :=
  AnalysisSoundProg.signAnalysis_pos_sound_seed hp hn hs heval

theorem sign_neg {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNeg = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    v < 0 :=
  AnalysisSoundProg.signAnalysis_neg_sound_seed hp hn hs heval

theorem sign_nonzero {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNonzero = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    v ≠ 0 :=
  AnalysisSoundProg.signAnalysis_nonzero_sound_seed hp hn hs heval

theorem parity_even {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hs : (parityAnalysis p).provesEven = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    EvenInt v :=
  AnalysisSoundProg.parityAnalysis_even_sound_seed hp hs heval

theorem parity_odd {p : Prog} (hp : AnalysisSoundProg p)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hs : (parityAnalysis p).provesOdd = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    OddInt v :=
  AnalysisSoundProg.parityAnalysis_odd_sound_seed hp hs heval

theorem analysis_supported_certifies {p : Prog} (hsupp : analysisSupported p = true) :
    AnalysisSoundProg p :=
  analysisSupported_sound hsupp

theorem certified_sign_sound {p : Prog} {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    (certifiedSignAnalysis p).denote v := by
  by_cases hsupp : analysisSupported p = true
  · have hp := analysisSupported_sound hsupp
    have hden : (signAnalysis p).denote v := by
      exact AnalysisSoundProg.sign_sound hp (progHeight p + 1) fuel
        AbsVal.nonnegUnknownParity AbsVal.zeroReg
        (seed n) Store.zero st' v
        (by
          simp [CfgSignSound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg,
            SignInfo.denote, seed]
          exact hn)
        heval
    simpa [certifiedSignAnalysis, certifiedAnalyze, signAnalysis, hsupp] using hden
  · have hfalse : analysisSupported p = false := by
      cases h : analysisSupported p
      · rfl
      · simp [h] at hsupp
    simp [certifiedSignAnalysis, certifiedAnalyze, hfalse, AbsVal.top, SignInfo.denote]

theorem certified_sign_nonneg {p : Prog} {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (certifiedSignAnalysis p).provesNonneg = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    0 <= v :=
  SignInfo.provesNonneg_sound hs (certified_sign_sound hn heval)

theorem certified_parity_sound {p : Prog} {fuel : Nat} {n v : Int} {st' : Store}
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    (certifiedParityAnalysis p).denote v := by
  by_cases hsupp : analysisSupported p = true
  · have hp := analysisSupported_sound hsupp
    have hden : (parityAnalysis p).denote v := by
      exact AnalysisSoundProg.parity_sound hp (progHeight p + 1) fuel
        AbsVal.nonnegUnknownParity AbsVal.zeroReg
        (seed n) Store.zero st' v
        (by
          simp [CfgParitySound, AbsVal.nonnegUnknownParity, AbsVal.zeroReg,
            ParityInfo.denote, EvenInt, seed])
        heval
    simpa [certifiedParityAnalysis, certifiedAnalyze, parityAnalysis, hsupp] using hden
  · have hfalse : analysisSupported p = false := by
      cases h : analysisSupported p
      · rfl
      · simp [h] at hsupp
    simp [certifiedParityAnalysis, certifiedAnalyze, hfalse, AbsVal.top, ParityInfo.denote]

theorem certified_parity_even {p : Prog} {fuel : Nat} {n v : Int} {st' : Store}
    (hs : (certifiedParityAnalysis p).provesEven = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    EvenInt v :=
  ParityInfo.provesEven_sound hs (certified_parity_sound heval)

theorem sign_nonneg_checked {p : Prog} (hsupp : analysisSupported p = true)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNonneg = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    0 <= v :=
  sign_nonneg (analysisSupported_sound hsupp) hn hs heval

theorem sign_nonpos_checked {p : Prog} (hsupp : analysisSupported p = true)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNonpos = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    v <= 0 :=
  sign_nonpos (analysisSupported_sound hsupp) hn hs heval

theorem sign_nonzero_checked {p : Prog} (hsupp : analysisSupported p = true)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (hs : (signAnalysis p).provesNonzero = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    v ≠ 0 :=
  sign_nonzero (analysisSupported_sound hsupp) hn hs heval

theorem parity_even_checked {p : Prog} (hsupp : analysisSupported p = true)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hs : (parityAnalysis p).provesEven = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    EvenInt v :=
  parity_even (analysisSupported_sound hsupp) hs heval

theorem parity_odd_checked {p : Prog} (hsupp : analysisSupported p = true)
    {fuel : Nat} {n v : Int} {st' : Store}
    (hs : (parityAnalysis p).provesOdd = true)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    OddInt v :=
  parity_odd (analysisSupported_sound hsupp) hs heval

theorem total_fixed_fuel {p : Prog} (hp : TotalSoundProg p)
    (htotal : totalAnalysis p = true) {n : Int} (st : Store) (hn : 0 <= n) :
    totalAnalysis p = true ∧
      ∃ v st', eval (progHeight p + 1) orgE1Signature p (seed n) st = some (v, st') :=
  TotalSoundProg.totalAnalysis_sound hp htotal st hn

theorem total_supported_certifies {p : Prog} (hsupp : totalSupported p = true) :
    TotalSoundProg p :=
  totalSupported_sound hsupp

theorem certified_total_sound {p : Prog}
    (htotal : certifiedTotalAnalysis p = true) {n : Int} (st : Store) (hn : 0 <= n) :
    totalAnalysis p = true ∧
      ∃ v st', eval (progHeight p + 1) orgE1Signature p (seed n) st = some (v, st') := by
  simp [certifiedTotalAnalysis] at htotal
  exact TotalSoundProg.totalAnalysis_sound (totalSupported_sound htotal.1) htotal.2 st hn

theorem total_checked {p : Prog} (hsupp : totalSupported p = true)
    (htotal : totalAnalysis p = true) {n : Int} (st : Store) (hn : 0 <= n) :
    totalAnalysis p = true ∧
      ∃ v st', eval (progHeight p + 1) orgE1Signature p (seed n) st = some (v, st') :=
  total_fixed_fuel (totalSupported_sound hsupp) htotal st hn

theorem total_loopAddiXOne_seed_fuel (n : Int) (hn : 0 <= n) :
    totalAnalysis loopAddiXOne = true ∧
      ∃ v st', eval (n.toNat + 4) orgE1Signature loopAddiXOne (seed n) Store.zero =
        some (v, st') :=
  totalAnalysis_loopAddiXOne_sound_from_total_parts n hn

theorem total_loop2AddiXOneKeepY_seed_fuel (n : Int) (hn : 0 <= n) :
    totalAnalysis loop2AddiXOneKeepY = true ∧
      ∃ v st', eval (n.toNat + 4) orgE1Signature loop2AddiXOneKeepY (seed n) Store.zero =
        some (v, st') :=
  totalAnalysis_loop2AddiXOneKeepY_sound_from_total_parts n hn

theorem positive_example_addiXOne : signAnalysis addiXOne = .pos :=
  signAnalysis_addiXOne_pos

theorem nonpositive_example_diffZeroOne : signAnalysis diffZeroOne = .neg :=
  signAnalysis_diffZeroOne_neg

theorem negative_example_diffXOne_not_nonneg : signAnalysis diffXOne ≠ .nonneg :=
  signAnalysis_diffXOne_not_nonneg

theorem odd_example_one : parityAnalysis (.node 1 []) = .odd :=
  parityAnalysis_one_odd

theorem comprehension_is_not_total (f n : Prog) :
    totalAnalysis (.node 12 [f, n]) = false :=
  totalAnalysis_compr_false f n

theorem comprehension_is_analysis_supported : analysisSupported comprXOne = true :=
  analysisSupported_comprXOne

theorem comprehension_is_not_total_supported : totalSupported comprXOne = false :=
  totalSupported_comprXOne_false

theorem unsafe_division_is_not_total_supported : totalSupported diviOneX = false :=
  totalSupported_diviOneX_false

theorem safe_division_is_total_supported : totalSupported diviAddiXOneOne = true :=
  totalSupported_diviAddiXOneOne

theorem comprehension_has_no_fixed_fuel_certificate (f n : Prog) :
    ¬ TotalSoundProg (.node 12 [f, n]) :=
  no_totalSound_compr f n

theorem scalar_org_signature_length : orgE1Signature.length = 14 := by
  simp [orgE1Signature]

theorem scalar_org_has_no_id14 : entryAt orgE1Signature 14 = none := by
  simp [orgE1Signature, entryAt, listGet?]

theorem scalar_org_has_no_id15 : entryAt orgE1Signature 15 = none := by
  simp [orgE1Signature, entryAt, listGet?]

theorem scalar_org_eval_id14_none (fuel : Nat) (ch : List Prog) (cfg : Config) (st : Store) :
    eval (fuel + 1) orgE1Signature (.node 14 ch) cfg st = none := by
  simp [eval, orgE1Signature, entryAt, listGet?]

theorem scalar_org_eval_id15_none (fuel : Nat) (ch : List Prog) (cfg : Config) (st : Store) :
    eval (fuel + 1) orgE1Signature (.node 15 ch) cfg st = none := by
  simp [eval, orgE1Signature, entryAt, listGet?]

theorem scalar_org_id14_not_total (ch : List Prog) :
    totalAnalysis (.node 14 ch) = false := by
  cases ch <;>
    simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
      AbsVal.top]

theorem scalar_org_id15_not_total (ch : List Prog) :
    totalAnalysis (.node 15 ch) = false := by
  cases ch <;>
    simp [totalAnalysis, analyze, analyzeWith, analyzeFuel, progHeight, progHeight.listHeight,
      AbsVal.top]

theorem scalar_org_id14_not_analysis_supported (ch : List Prog) :
    analysisSupported (.node 14 ch) = false := by
  cases ch <;>
    simp [analysisSupported, analysisCert?, analysisCertFuel?, coreOnly]

theorem scalar_org_id15_not_analysis_supported (ch : List Prog) :
    analysisSupported (.node 15 ch) = false := by
  cases ch <;>
    simp [analysisSupported, analysisCert?, analysisCertFuel?, coreOnly]

end Seal

example {fuel : Nat} {n v : Int} {st' : Store}
    (h : eval (fuel + 2) orgE1Signature addiXOne (seed n) Store.zero = some (v, st'))
    (hn : 0 <= n) : 0 < v := by
  fail_if_success
    rfl
  exact addiXOne_pos_sound h hn

end Mettapedia.GSLT.LanguageDef.GauthierProperties
