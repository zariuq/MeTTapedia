import Mathlib.Data.List.Basic
import Mettapedia.Languages.MeTTa.Pure.Core
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# MeTTa-Pure: Binder Operations

Locally nameless helper operations and lemmas for the Pure fragment.
This file stays below typing/conversion so higher metatheory can share
the same binder interface without introducing import cycles.
-/

namespace Mettapedia.Languages.MeTTa.Pure.BinderOps

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core

/-- Helper: convert list to finset for cofinite freshness sets. -/
def listToFinset (l : List String) : Finset String := l.toFinset

/-- Freshness from finite exclusion on free variables. -/
theorem isFresh_of_not_in_freeVars_finset {x : String} {p : Pattern}
    (h : x ∉ listToFinset (freeVars p)) : isFresh x p = true := by
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hmem
  exact h (List.mem_toFinset.mpr (List.contains_iff_mem.mp hmem))

/-- Helper: if `f a = a` for all `a ∈ l`, then `l.map f = l`. -/
theorem list_map_eq_self {f : Pattern → Pattern} {l : List Pattern}
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons]
    congr 1
    · exact h a List.mem_cons_self
    · exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem isFresh_of_apply_mem {x c : String} {ps : List Pattern} {p : Pattern}
    (hfresh : isFresh x (.apply c ps) = true) (hp : p ∈ ps) :
    isFresh x p = true := by
  simp only [isFresh, freeVars, Bool.not_eq_true'] at hfresh ⊢
  rw [Bool.eq_false_iff] at hfresh ⊢
  exact fun h => hfresh (List.contains_iff_mem.mpr
    (List.mem_flatMap.mpr ⟨p, hp, List.contains_iff_mem.mp h⟩))

theorem isFresh_of_collection_mem {x : String} {ct : CollType}
    {ps : List Pattern} {rest : Option String} {p : Pattern}
    (hfresh : isFresh x (.collection ct ps rest) = true) (hp : p ∈ ps) :
    isFresh x p = true := by
  simp only [isFresh, freeVars, Bool.not_eq_true'] at hfresh ⊢
  rw [Bool.eq_false_iff] at hfresh ⊢
  exact fun h => hfresh (List.contains_iff_mem.mpr
    (List.mem_flatMap.mpr ⟨p, hp, List.contains_iff_mem.mp h⟩))

theorem isFresh_of_lambda {x : String} {body : Pattern}
    (hfresh : isFresh x (.lambda body) = true) : isFresh x body = true := by
  simpa only [isFresh, freeVars] using hfresh

theorem isFresh_of_multiLambda {x : String} {n : Nat} {body : Pattern}
    (hfresh : isFresh x (.multiLambda n body) = true) : isFresh x body = true := by
  simpa only [isFresh, freeVars] using hfresh

theorem isFresh_of_subst_body {x : String} {body repl : Pattern}
    (hfresh : isFresh x (.subst body repl) = true) : isFresh x body = true := by
  simp only [isFresh, freeVars, List.contains_append, Bool.not_eq_true',
             Bool.or_eq_false_iff] at hfresh ⊢
  exact hfresh.1

theorem isFresh_of_subst_repl {x : String} {body repl : Pattern}
    (hfresh : isFresh x (.subst body repl) = true) : isFresh x repl = true := by
  simp only [isFresh, freeVars, List.contains_append, Bool.not_eq_true',
             Bool.or_eq_false_iff] at hfresh ⊢
  exact hfresh.2

@[simp] theorem openBVar_u0 (k : Nat) (u : Pattern) :
    openBVar k u u0 = u0 := by
  simp [u0, openBVar]

@[simp] theorem openBVar_u1 (k : Nat) (u : Pattern) :
    openBVar k u u1 = u1 := by
  simp [u1, openBVar]

@[simp] theorem openBVar_mkPi (k : Nat) (u A B : Pattern) :
    openBVar k u (mkPi A B) = mkPi (openBVar k u A) (openBVar (k + 1) u B) := by
  simp [mkPi, openBVar]

@[simp] theorem openBVar_mkSigma (k : Nat) (u A B : Pattern) :
    openBVar k u (mkSigma A B) = mkSigma (openBVar k u A) (openBVar (k + 1) u B) := by
  simp [mkSigma, openBVar]

@[simp] theorem openBVar_mkId (k : Nat) (u A a b : Pattern) :
    openBVar k u (mkId A a b) =
      mkId (openBVar k u A) (openBVar k u a) (openBVar k u b) := by
  simp [mkId, openBVar]

@[simp] theorem openBVar_mkLam (k : Nat) (u body : Pattern) :
    openBVar k u (mkLam body) = mkLam (openBVar (k + 1) u body) := by
  simp [mkLam, openBVar]

@[simp] theorem openBVar_mkApp (k : Nat) (u f a : Pattern) :
    openBVar k u (mkApp f a) = mkApp (openBVar k u f) (openBVar k u a) := by
  simp [mkApp, openBVar]

@[simp] theorem openBVar_mkPair (k : Nat) (u a b : Pattern) :
    openBVar k u (mkPair a b) = mkPair (openBVar k u a) (openBVar k u b) := by
  simp [mkPair, openBVar]

@[simp] theorem openBVar_mkFst (k : Nat) (u p : Pattern) :
    openBVar k u (mkFst p) = mkFst (openBVar k u p) := by
  simp [mkFst, openBVar]

@[simp] theorem openBVar_mkSnd (k : Nat) (u p : Pattern) :
    openBVar k u (mkSnd p) = mkSnd (openBVar k u p) := by
  simp [mkSnd, openBVar]

@[simp] theorem openBVar_mkRefl (k : Nat) (u a : Pattern) :
    openBVar k u (mkRefl a) = mkRefl (openBVar k u a) := by
  simp [mkRefl, openBVar]

/-- Replace all occurrences of `.fvar x` with `.bvar k` in a pattern,
    incrementing `k` under binders. -/
abbrev closeBVar (k : Nat) (x : String) : Pattern → Pattern := closeFVar k x

/-- `closeBVar` removes `x` from free variables. -/
theorem isFresh_closeBVar (k : Nat) (x : String) (p : Pattern) :
    isFresh x (closeBVar k x p) = true := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar _ => simp [closeBVar, isFresh, freeVars, closeFVar]
  | hfvar y =>
    by_cases h : y = x
    · subst h
      simp [closeBVar, closeFVar, isFresh, freeVars]
    · have h' : x ≠ y := fun hxy => h (Eq.symm hxy)
      simp [closeBVar, closeFVar, isFresh, freeVars, h, h']
  | happly c args ih =>
    simp only [closeBVar, closeFVar, isFresh, freeVars, Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro hmem
    rw [List.contains_iff_mem] at hmem
    obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.mp hmem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    have := ih p hp k
    simp only [isFresh, Bool.not_eq_true'] at this
    rw [Bool.eq_false_iff] at this
    exact this (List.contains_iff_mem.mpr hxq)
  | hlambda body ih =>
    simpa only [closeBVar, closeFVar, isFresh, freeVars] using ih (k + 1)
  | hmultiLambda n body ih =>
    simpa only [closeBVar, closeFVar, isFresh, freeVars] using ih (k + n)
  | hsubst body repl ihb ihr =>
    unfold closeBVar closeFVar
    have h1 := ihb (k + 1)
    have h2 := ihr k
    simp only [isFresh, freeVars, Bool.not_eq_true'] at h1 h2 ⊢
    rw [Bool.eq_false_iff]
    intro hmem
    rw [List.contains_iff_mem, List.mem_append] at hmem
    cases hmem with
    | inl h => rw [Bool.eq_false_iff] at h1; exact h1 (List.contains_iff_mem.mpr h)
    | inr h => rw [Bool.eq_false_iff] at h2; exact h2 (List.contains_iff_mem.mpr h)
  | hcollection ct elems rest ih =>
    simp only [closeBVar, closeFVar, isFresh, freeVars, Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro hmem
    rw [List.contains_iff_mem] at hmem
    obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.mp hmem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    have := ih p hp k
    simp only [isFresh, Bool.not_eq_true'] at this
    rw [Bool.eq_false_iff] at this
    exact this (List.contains_iff_mem.mpr hxq)

/-- Open-close roundtrip when the term is locally closed at level `k`. -/
theorem openBVar_closeBVar_cancel {k : Nat} {x : String} {p : Pattern}
    (hlc : lc_at k p = true) :
    openBVar k (.fvar x) (closeBVar k x p) = p := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [closeBVar, closeFVar, openBVar]
    have hlt : n < k := by simpa [lc_at] using hlc
    split
    · next h => simp [beq_iff_eq] at h; omega
    · rfl
  | hfvar y =>
    by_cases h : y = x
    · subst h
      simp [closeBVar, closeFVar, openBVar]
    · simp [closeBVar, closeFVar, openBVar, h]
  | happly c args ih =>
    simp only [closeBVar, closeFVar, openBVar, List.map_map]
    congr 1
    exact list_map_eq_self (fun a ha =>
      ih a ha (lc_at_list_mem (by simpa [lc_at] using hlc) ha))
  | hlambda body ih =>
    simp only [closeBVar, closeFVar, openBVar]
    congr 1
    exact ih (by simpa [lc_at] using hlc)
  | hmultiLambda n body ih =>
    simp only [closeBVar, closeFVar, openBVar]
    congr 1
    exact ih (by simpa [lc_at] using hlc)
  | hsubst body repl ihb ihr =>
    simp only [closeBVar, closeFVar, openBVar]
    congr 1
    · have hlc' : lc_at (k + 1) body = true ∧ lc_at k repl = true := by
        simpa [lc_at, Bool.and_eq_true] using hlc
      exact ihb hlc'.1
    · have hlc' : lc_at (k + 1) body = true ∧ lc_at k repl = true := by
        simpa [lc_at, Bool.and_eq_true] using hlc
      exact ihr hlc'.2
  | hcollection ct elems rest ih =>
    simp only [closeBVar, closeFVar, openBVar, List.map_map]
    congr 1
    exact list_map_eq_self (fun a ha =>
      ih a ha (lc_at_list_mem (by simpa [lc_at] using hlc) ha))

/-- Reverse roundtrip when `x` is fresh in the original term. -/
theorem closeBVar_openBVar_cancel {k : Nat} {x : String} {p : Pattern}
    (hf : isFresh x p = true) :
    closeBVar k x (openBVar k (.fvar x) p) = p := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [openBVar]
    split
    · next h => simp [beq_iff_eq] at h; subst h; simp [closeBVar, closeFVar]
    · simp [closeBVar, closeFVar]
  | hfvar y =>
    have hne : y ≠ x := by
      simp only [isFresh, freeVars, Bool.not_eq_true'] at hf
      intro h
      subst h
      simp at hf
    simp [openBVar, closeBVar, closeFVar, hne]
  | happly c args ih =>
    simp only [openBVar, closeBVar, closeFVar, List.map_map]
    congr 1
    exact list_map_eq_self (fun a ha => ih a ha (isFresh_of_apply_mem hf ha))
  | hlambda body ih =>
    simp only [openBVar, closeBVar, closeFVar]
    congr 1
    exact ih (isFresh_of_lambda hf)
  | hmultiLambda n body ih =>
    simp only [openBVar, closeBVar, closeFVar]
    congr 1
    exact ih (isFresh_of_multiLambda hf)
  | hsubst body repl ihb ihr =>
    simp only [openBVar, closeBVar, closeFVar]
    congr 1
    · exact ihb (isFresh_of_subst_body hf)
    · exact ihr (isFresh_of_subst_repl hf)
  | hcollection ct elems rest ih =>
    simp only [openBVar, closeBVar, closeFVar, List.map_map]
    congr 1
    exact list_map_eq_self (fun a ha => ih a ha (isFresh_of_collection_mem hf ha))

end Mettapedia.Languages.MeTTa.Pure.BinderOps
