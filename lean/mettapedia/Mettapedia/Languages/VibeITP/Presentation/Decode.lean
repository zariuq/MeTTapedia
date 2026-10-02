import Mettapedia.Languages.VibeITP.Presentation.Package

/-!
# Vibe-ITP presentation: decoding data patterns

Numerals have exactly one representation, so decoding a numeral determines the
pattern (`decNat_unique`).  Data patterns (applications only) are valid rule
arguments at depth zero.  This module also proves that the encoding of kernel
terms is injective and can be inverted constructor by constructor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.VibeITP.Spec

/-! ## Data patterns -/

/-- Patterns built from applications only. -/
inductive IsData : Pattern → Prop where
  | apply (c : String) (args : List Pattern) (h : ∀ a ∈ args, IsData a) :
      IsData (.apply c args)

theorem IsData.app0 (c : String) : IsData (.apply c []) := .apply c [] (by simp)

theorem IsData.app1 (c : String) {a : Pattern} (ha : IsData a) : IsData (.apply c [a]) :=
  .apply c [a] (by simp [ha])

theorem IsData.app2 (c : String) {a b : Pattern} (ha : IsData a) (hb : IsData b) :
    IsData (.apply c [a, b]) :=
  .apply c [a, b] (by simp [ha, hb])

theorem IsData.app3 (c : String) {a b d : Pattern} (ha : IsData a) (hb : IsData b)
    (hd : IsData d) : IsData (.apply c [a, b, d]) :=
  .apply c [a, b, d] (by simp [ha, hb, hd])

mutual
theorem isData_ground : (p : Pattern) → IsData p → p.isGroundAt 0 = true
  | .apply _ args, .apply _ _ h => by
      simp only [Pattern.isGroundAt]
      exact isData_groundList args h
theorem isData_groundList : (ps : List Pattern) → (∀ a ∈ ps, IsData a) →
    Pattern.isGroundListAt 0 ps = true
  | [], _ => rfl
  | a :: as, h => by
      simp only [Pattern.isGroundListAt, Bool.and_eq_true]
      exact ⟨isData_ground a (h a (by simp)), isData_groundList as (fun x hx => h x (by simp [hx]))⟩
end

mutual
theorem isData_canonical : (p : Pattern) → IsData p → p.hasCanonicalBinderMetadata = true
  | .apply _ args, .apply _ _ h => by
      simp only [Pattern.hasCanonicalBinderMetadata]
      exact isData_canonicalList args h
theorem isData_canonicalList : (ps : List Pattern) → (∀ a ∈ ps, IsData a) →
    Pattern.hasCanonicalBinderMetadataList ps = true
  | [], _ => rfl
  | a :: as, h => by
      simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
      exact ⟨isData_canonical a (h a (by simp)),
        isData_canonicalList as (fun x hx => h x (by simp [hx]))⟩
end

theorem isData_valid {p : Pattern} (h : IsData p) : argumentValidAt 0 p = true := by
  simp [argumentValidAt, isData_ground p h, isData_canonical p h]

/-! ## Decoders -/

def decPos : Pattern → Option Nat
  | .apply "VP1" [] => some 1
  | .apply "VPO" [p] => (decPos p).map (2 * ·)
  | .apply "VPI" [p] => (decPos p).map (2 * · + 1)
  | _ => none

def decNat : Pattern → Option Nat
  | .apply "VN0" [] => some 0
  | .apply "VNPos" [p] => decPos p
  | _ => none

def decUnary : Pattern → Option Nat
  | .apply "VU0" [] => some 0
  | .apply "VUS" [u] => (decUnary u).map (· + 1)
  | _ => none

def decBool : Pattern → Option Bool
  | .apply "VTrue" [] => some true
  | .apply "VFalse" [] => some false
  | _ => none

def decList : Pattern → Option (List Pattern)
  | .apply "VNil" [] => some []
  | .apply "VCons" [x, xs] => (decList xs).map (x :: ·)
  | _ => none

@[simp] theorem decPos_P1 : decPos cP1 = some 1 := rfl
@[simp] theorem decPos_PO (p : Pattern) : decPos (cPO p) = (decPos p).map (2 * ·) := rfl
@[simp] theorem decPos_PI (p : Pattern) : decPos (cPI p) = (decPos p).map (2 * · + 1) := rfl
@[simp] theorem decNat_N0 : decNat cN0 = some 0 := rfl
@[simp] theorem decNat_NPos (p : Pattern) : decNat (cNPos p) = decPos p := rfl
@[simp] theorem decUnary_U0 : decUnary cU0 = some 0 := rfl
@[simp] theorem decUnary_US (u : Pattern) : decUnary (cUS u) = (decUnary u).map (· + 1) := rfl
@[simp] theorem decBool_true : decBool cTrue = some true := rfl
@[simp] theorem decBool_false : decBool cFalse = some false := rfl
@[simp] theorem decList_nil : decList cNil = some [] := rfl
@[simp] theorem decList_cons (x xs : Pattern) : decList (cCons x xs) = (decList xs).map (x :: ·) := rfl

/-! ## Positive numerals -/

theorem decPos_pos (p : Pattern) : ∀ x, decPos p = some x → 1 ≤ x := by
  fun_induction decPos p with
  | case1 => intro x h; simp at h; omega
  | case2 p ih =>
      intro x h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      have := ih y hy; omega
  | case3 p ih =>
      intro x h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      omega
  | case4 => intro x h; simp at h

theorem encPosFuel_stable : ∀ (n fuel fuel' : Nat), n ≤ fuel → n ≤ fuel' →
    encPosFuel fuel n = encPosFuel fuel' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro fuel fuel' hf hf'
      cases fuel with
      | zero =>
          cases fuel' with
          | zero => rfl
          | succ f' =>
              have : n = 0 := by omega
              subst this; simp [encPosFuel]
      | succ f =>
          cases fuel' with
          | zero =>
              have : n = 0 := by omega
              subst this; simp [encPosFuel]
          | succ f' =>
              simp only [encPosFuel]
              split
              · rfl
              · have hlt : n / 2 < n := by omega
                rw [ih (n / 2) hlt f f' (by omega) (by omega)]

theorem encPos_one : encPos 1 = cP1 := rfl

theorem encPos_even (n : Nat) (h : 1 ≤ n) : encPos (2 * n) = cPO (encPos n) := by
  unfold encPos
  obtain ⟨f, hf⟩ : ∃ f, 2 * n = f + 1 := ⟨2 * n - 1, by omega⟩
  rw [hf]
  simp only [encPosFuel]
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  rw [show (f + 1) / 2 = n by omega]
  exact encPosFuel_stable n f n (by omega) (Nat.le_refl _)

theorem encPos_odd (n : Nat) (h : 1 ≤ n) : encPos (2 * n + 1) = cPI (encPos n) := by
  unfold encPos
  simp only [encPosFuel]
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  rw [show (2 * n + 1) / 2 = n by omega]
  exact encPosFuel_stable n (2 * n) n (by omega) (Nat.le_refl _)

theorem nat_even_or_odd (n : Nat) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 :=
  ⟨n / 2, by omega⟩

theorem decPos_encPos : ∀ (n : Nat), 1 ≤ n → decPos (encPos n) = some n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn
      obtain ⟨k, hk | hk⟩ := nat_even_or_odd n
      · subst hk
        have hk1 : 1 ≤ k := by omega
        rw [encPos_even k hk1, decPos_PO, ih k (by omega) hk1]
        rfl
      · subst hk
        by_cases hk0 : k = 0
        · subst hk0; rfl
        · have hk1 : 1 ≤ k := by omega
          rw [encPos_odd k hk1, decPos_PI, ih k (by omega) hk1]
          rfl

theorem decPos_unique (p : Pattern) : ∀ x, decPos p = some x → p = encPos x := by
  fun_induction decPos p with
  | case1 => intro x h; simp at h; subst h; rfl
  | case2 p ih =>
      intro x h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      rw [encPos_even y (decPos_pos p y hy), ← ih y hy]
      rfl
  | case3 p ih =>
      intro x h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      rw [encPos_odd y (decPos_pos p y hy), ← ih y hy]
      rfl
  | case4 => intro x h; simp at h

theorem decPos_eq_iff (p : Pattern) (x : Nat) :
    decPos p = some x ↔ 1 ≤ x ∧ p = encPos x :=
  ⟨fun h => ⟨decPos_pos p x h, decPos_unique p x h⟩,
    fun ⟨hx, hp⟩ => hp ▸ decPos_encPos x hx⟩

/-! ## Natural numerals -/

@[simp] theorem decNat_encNat (n : Nat) : decNat (encNat n) = some n := by
  unfold encNat
  split
  · subst_vars; rfl
  · simp only [decNat_NPos]; exact decPos_encPos n (by omega)

theorem encNat_pos (n : Nat) (h : 1 ≤ n) : encNat n = cNPos (encPos n) := by
  simp [encNat, show n ≠ 0 by omega]

theorem decNat_unique (p : Pattern) (x : Nat) (h : decNat p = some x) : p = encNat x := by
  unfold decNat at h
  split at h
  · simp at h; subst h; rfl
  · rename_i q
    have hx := decPos_pos q x h
    rw [decPos_unique q x h, encNat_pos x hx]
    rfl
  · simp at h

theorem decNat_eq_iff (p : Pattern) (x : Nat) : decNat p = some x ↔ p = encNat x :=
  ⟨decNat_unique p x, fun h => h ▸ decNat_encNat x⟩

theorem encNat_inj {a b : Nat} (h : encNat a = encNat b) : a = b := by
  have := decNat_encNat a
  rw [h, decNat_encNat] at this
  exact (Option.some.inj this).symm

theorem encNat_zero : encNat 0 = cN0 := rfl

theorem isData_encPos : ∀ n : Nat, IsData (encPos n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      obtain ⟨k, hk | hk⟩ := nat_even_or_odd n
      · subst hk
        by_cases hk0 : k = 0
        · subst hk0; exact IsData.app0 _
        · rw [encPos_even k (by omega)]; exact IsData.app1 _ (ih k (by omega))
      · subst hk
        by_cases hk0 : k = 0
        · subst hk0; exact IsData.app0 _
        · rw [encPos_odd k (by omega)]; exact IsData.app1 _ (ih k (by omega))

@[simp] theorem decNat_patOne : decNat patOne = some 1 := decNat_encNat 1
@[simp] theorem decNat_patEight : decNat patEight = some 8 := decNat_encNat 8
@[simp] theorem decNat_patByteBound : decNat patByteBound = some 256 := decNat_encNat 256
@[simp] theorem decNat_patTwo64 : decNat patTwo64 = some wordBound := decNat_encNat _
@[simp] theorem decNat_patMaxWord : decNat patMaxWord = some (wordBound - 1) := decNat_encNat _

theorem isData_encNat (n : Nat) : IsData (encNat n) := by
  unfold encNat
  split
  · exact IsData.app0 _
  · exact IsData.app1 _ (isData_encPos n)

/-! ## Unary numerals, booleans, lists -/

theorem decUnary_encUnary : ∀ n : Nat, decUnary (encUnary n) = some n
  | 0 => rfl
  | n + 1 => by simp [encUnary, decUnary_encUnary n]

@[simp] theorem decUnary_patWordBits : decUnary patWordBits = some 64 := decUnary_encUnary 64

theorem decBool_encBool (b : Bool) : decBool (encBool b) = some b := by
  cases b <;> rfl

theorem decBool_unique (p : Pattern) (b : Bool) (h : decBool p = some b) : p = encBool b := by
  unfold decBool at h
  split at h <;> simp at h <;> subst h <;> rfl

theorem encBool_inj {a b : Bool} (h : encBool a = encBool b) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [encBool, cTrue, cFalse] at h)

theorem isData_encBool (b : Bool) : IsData (encBool b) := by
  cases b <;> exact IsData.app0 _

theorem decList_encList : ∀ l : List Pattern, decList (encList l) = some l
  | [] => rfl
  | x :: xs => by simp [encList, decList_encList xs]

theorem decList_unique (p : Pattern) : ∀ l, decList p = some l → p = encList l := by
  fun_induction decList p with
  | case1 => intro l h; simp at h; subst h; rfl
  | case2 x xs ih =>
      intro l h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨l', hl', rfl⟩ := h
      rw [ih l' hl']
      rfl
  | case3 => intro l h; simp at h

theorem encList_inj : ∀ {l₁ l₂ : List Pattern}, encList l₁ = encList l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encList, cNil, cCons] at h
  | _ :: _, [], h => by simp [encList, cNil, cCons] at h
  | x :: xs, y :: ys, h => by
      simp only [encList, cCons, Pattern.apply.injEq, List.cons.injEq, true_and] at h
      rw [h.1, encList_inj h.2.1]

theorem isData_encList : ∀ (l : List Pattern), (∀ x ∈ l, IsData x) → IsData (encList l)
  | [], _ => IsData.app0 _
  | x :: xs, h => IsData.app2 _ (h x (by simp)) (isData_encList xs (fun y hy => h y (by simp [hy])))

theorem encNatList_inj : ∀ {l₁ l₂ : List Nat}, encNatList l₁ = encNatList l₂ → l₁ = l₂ := by
  intro l₁ l₂ h
  have h' := encList_inj h
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a as ih =>
      cases l₂ with
      | nil => simp at h'
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at h'
          rw [encNat_inj h'.1, ih (by simp [encNatList, h'.2]) h'.2]

theorem isData_encNatList (l : List Nat) : IsData (encNatList l) :=
  isData_encList _ (by simp [isData_encNat])

theorem encBytes_inj {b₁ b₂ : List UInt8} (h : encBytes b₁ = encBytes b₂) : b₁ = b₂ := by
  have h' := encList_inj h
  induction b₁ generalizing b₂ with
  | nil => cases b₂ <;> simp_all
  | cons a as ih =>
      cases b₂ with
      | nil => simp at h'
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at h'
          have hab : a = b := UInt8.toNat_inj.mp (encNat_inj h'.1)
          rw [hab, ih (by simp [encBytes, h'.2]) h'.2]

theorem isData_encBytes (bytes : List UInt8) : IsData (encBytes bytes) :=
  isData_encList _ (by simp [isData_encNat])

end Mettapedia.Languages.VibeITP.Presentation
