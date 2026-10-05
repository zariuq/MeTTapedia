import Mettapedia.Languages.VibeITP.Presentation.CompleteArithmetic

/-!
# Constructive list witnesses for the Vibe-ITP presentation

List length and indexing are derived for arbitrary lists of data patterns.
Byte-list formation is derived from the bounds of the actual `UInt8` entries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.GSLT.LanguageDef.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

private theorem listRule_in {R : List FORule} (hR : kernelRules ⊆ R)
    {r : FORule} (hr : r ∈ listRules) : r ∈ R :=
  hR (by simp [kernelRules, hr])

theorem complete_len {R : List FORule} (hR : kernelRules ⊆ R)
    (xs : List Pattern) (hdata : ∀ x ∈ xs, IsData x) :
    FODerivable R (jLen (encList xs) (encNat xs.length)) := by
  induction xs with
  | nil => exact intro_rLenNil (listRule_in hR (by simp [listRules]))
  | cons x xs ih =>
      have hdx : IsData x := hdata x (by simp)
      have hdxs : ∀ y ∈ xs, IsData y := fun y hy => hdata y (by simp [hy])
      exact intro_rLenCons (listRule_in hR (by simp [listRules]))
        hdx (isData_encList xs hdxs) (isData_encNat xs.length)
        (isData_encNat (xs.length + 1)) (ih hdxs) (complete_nadd hR xs.length 1)

theorem complete_nth {R : List FORule} (hR : kernelRules ⊆ R)
    (xs : List Pattern) (i : Nat) (x : Pattern)
    (hdata : ∀ y ∈ xs, IsData y) (hget : xs[i]? = some x) :
    FODerivable R (jNth (encList xs) (encNat i) x) := by
  induction xs generalizing i with
  | nil => simp at hget
  | cons y ys ih =>
      have hdy : IsData y := hdata y (by simp)
      have hdys : ∀ z ∈ ys, IsData z := fun z hz => hdata z (by simp [hz])
      cases i with
      | zero =>
          have hyx : y = x := by simpa using hget
          subst x
          exact intro_rNth0 (listRule_in hR (by simp [listRules])) hdy
            (isData_encList ys hdys)
      | succ i =>
          have hget' : ys[i]? = some x := by simpa using hget
          exact intro_rNthS (listRule_in hR (by simp [listRules]))
            hdy (isData_encList ys hdys) (isData_encNat (i + 1)) (isData_encNat i)
            (hdys x (List.mem_of_getElem? hget')) (complete_nadd hR i 1)
            (ih i hdys hget')

theorem complete_bytes {R : List FORule} (hR : kernelRules ⊆ R)
    (bs : List UInt8) : FODerivable R (jBytes (encBytes bs)) := by
  induction bs with
  | nil => exact intro_rBytesNil (listRule_in hR (by simp [listRules]))
  | cons b bs ih =>
      exact intro_rBytesCons (listRule_in hR (by simp [listRules]))
        (isData_encNat b.toNat) (isData_encBytes bs)
        (complete_nlt hR b.toNat 256 (by exact b.toNat_lt)) ih

theorem complete_len_bytes {R : List FORule} (hR : kernelRules ⊆ R)
    (bs : List UInt8) : FODerivable R (jLen (encBytes bs) (encNat bs.length)) := by
  have h := complete_len hR (bs.map fun b => encNat b.toNat)
    (by simp [isData_encNat])
  simpa only [encBytes, List.length_map] using h

theorem complete_nth_bytes {R : List FORule} (hR : kernelRules ⊆ R)
    (bs : List UInt8) (i : Nat) (b : UInt8) (hget : bs[i]? = some b) :
    FODerivable R (jNth (encBytes bs) (encNat i) (encNat b.toNat)) := by
  apply complete_nth hR (bs.map fun b => encNat b.toNat) i (encNat b.toNat)
  · simp [isData_encNat]
  · simp [List.getElem?_map, hget]

end Mettapedia.Languages.VibeITP.Presentation
