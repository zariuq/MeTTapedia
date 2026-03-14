import Mettapedia.Languages.MeTTa.Pure.Reduction
import Mettapedia.Languages.MeTTa.Pure.Confluence
import Mettapedia.Languages.MeTTa.Pure.FVarSubst
import Mettapedia.Languages.MeTTa.Pure.Fragment

/-!
# MeTTa-Pure: Subject Reduction (Type Preservation)

The crown theorem of MeTTa-Pure: if a well-typed term reduces, the result
is well-typed at the same type.

```
PureHasType Γ t A → PureReduces t t' → PureHasType Γ t' A
```

## Proof Architecture

The proof follows the standard locally nameless approach (Aydemir et al. 2008):

1. **FVar substitution** (`substFVar`): replace `.fvar x` with a term `u`
2. **substFVar_intro**: `[x↦u](open_0(x, p)) = open_0(u, p)` for fresh `x`
3. **Typing substitution lemma**: if `Γ, x:A ⊢ t : B` and `Γ ⊢ u : A`
   then `Γ ⊢ [x↦u]t : [x↦u]B`
4. **Subject reduction**: by induction on typing; β-cases use (2)+(3)

## References

- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
- Adjedj et al., "Martin-Löf à la Coq" (2023)
-/

namespace Mettapedia.Languages.MeTTa.Pure.SubjectReduction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.Typing
open Mettapedia.Languages.MeTTa.Pure.Reduction
open Mettapedia.Languages.MeTTa.Pure.FVarSubst
open Mettapedia.Languages.MeTTa.Pure.Fragment

/-! ## FVar Substitution

Replace `.fvar x` with `u` throughout a pattern. This is simpler than the
full `applySubst` (which handles environments and explicit `.subst` nodes). -/

/-- Replace all occurrences of `.fvar x` with `u` in a pattern. -/
def substFVar (x : String) (u : Pattern) : Pattern → Pattern
  | .bvar n => .bvar n
  | .fvar y => if y = x then u else .fvar y
  | .apply c args => .apply c (args.map (substFVar x u))
  | .lambda body => .lambda (substFVar x u body)
  | .multiLambda n body => .multiLambda n (substFVar x u body)
  | .subst body repl => .subst (substFVar x u body) (substFVar x u repl)
  | .collection ct elems rest => .collection ct (elems.map (substFVar x u)) rest
termination_by p => sizeOf p

/-- Local `substFVar` is definitionally aligned with the shared FVarSubst version. -/
private theorem substFVar_eq_shared (x : String) (u : Pattern) (p : Pattern) :
    substFVar x u p = Mettapedia.Languages.MeTTa.Pure.FVarSubst.substFVar x u p := by
  induction p using Pattern.inductionOn with
  | hbvar n =>
      simp [substFVar]
  | hfvar y =>
      simp [substFVar, Mettapedia.Languages.MeTTa.Pure.FVarSubst.substFVar]
  | happly c args ih =>
      simp [substFVar, Mettapedia.Languages.MeTTa.Pure.FVarSubst.substFVar]
      exact ih
  | hlambda body ih =>
      simp [substFVar, Mettapedia.Languages.MeTTa.Pure.FVarSubst.substFVar, ih]
  | hmultiLambda n body ih =>
      simp [substFVar, Mettapedia.Languages.MeTTa.Pure.FVarSubst.substFVar, ih]
  | hsubst body repl ihb ihr =>
      simp [substFVar, Mettapedia.Languages.MeTTa.Pure.FVarSubst.substFVar, ihb, ihr]
  | hcollection ct elems rest ih =>
      simp [substFVar, Mettapedia.Languages.MeTTa.Pure.FVarSubst.substFVar]
      exact ih

/-- `lc_at` preservation for the local `substFVar` wrapper. -/
private theorem lc_at_substFVar_local {k : Nat} {x : String} {u p : Pattern}
    (hp : lc_at k p = true) (hu : lc_at k u = true) :
    lc_at k (substFVar x u p) = true := by
  simpa [substFVar_eq_shared] using
    (Mettapedia.Languages.MeTTa.Pure.FVarSubst.lc_at_substFVar (k := k) (x := x) (u := u) (p := p) hp hu)

/-! ## List helper -/

private theorem list_map_eq_self {f : Pattern → Pattern} {l : List Pattern}
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons]; congr 1
    · exact h a List.mem_cons_self
    · exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-! ## Freshness propagation helpers -/

private theorem isFresh_of_apply_mem {x c : String} {ps : List Pattern} {p : Pattern}
    (hfresh : isFresh x (.apply c ps) = true) (hp : p ∈ ps) :
    isFresh x p = true := by
  simp only [isFresh, freeVars, Bool.not_eq_true'] at hfresh ⊢
  rw [Bool.eq_false_iff] at hfresh ⊢
  exact fun h => hfresh (List.contains_iff_mem.mpr
    (List.mem_flatMap.mpr ⟨p, hp, List.contains_iff_mem.mp h⟩))

private theorem isFresh_of_collection_mem {x : String} {ct : CollType}
    {ps : List Pattern} {rest : Option String} {p : Pattern}
    (hfresh : isFresh x (.collection ct ps rest) = true) (hp : p ∈ ps) :
    isFresh x p = true := by
  simp only [isFresh, freeVars, Bool.not_eq_true'] at hfresh ⊢
  rw [Bool.eq_false_iff] at hfresh ⊢
  exact fun h => hfresh (List.contains_iff_mem.mpr
    (List.mem_flatMap.mpr ⟨p, hp, List.contains_iff_mem.mp h⟩))

private theorem isFresh_of_lambda {x : String} {body : Pattern}
    (hfresh : isFresh x (.lambda body) = true) : isFresh x body = true := by
  simp only [isFresh, freeVars] at hfresh ⊢; exact hfresh

private theorem isFresh_of_multiLambda {x : String} {n : Nat} {body : Pattern}
    (hfresh : isFresh x (.multiLambda n body) = true) : isFresh x body = true := by
  simp only [isFresh, freeVars] at hfresh ⊢; exact hfresh

private theorem isFresh_of_subst_body {x : String} {body repl : Pattern}
    (hfresh : isFresh x (.subst body repl) = true) : isFresh x body = true := by
  simp only [isFresh, freeVars, List.contains_append, Bool.not_eq_true',
             Bool.or_eq_false_iff] at hfresh ⊢; exact hfresh.1

private theorem isFresh_of_subst_repl {x : String} {body repl : Pattern}
    (hfresh : isFresh x (.subst body repl) = true) : isFresh x repl = true := by
  simp only [isFresh, freeVars, List.contains_append, Bool.not_eq_true',
             Bool.or_eq_false_iff] at hfresh ⊢; exact hfresh.2

/-! ## substFVar interaction with constructors -/

@[simp] theorem substFVar_u0 (x : String) (u : Pattern) :
    substFVar x u u0 = u0 := by simp [u0, substFVar]

@[simp] theorem substFVar_u1 (x : String) (u : Pattern) :
    substFVar x u u1 = u1 := by simp [u1, substFVar]

@[simp] theorem substFVar_mkPi (x : String) (u A B : Pattern) :
    substFVar x u (mkPi A B) = mkPi (substFVar x u A) (substFVar x u B) := by
  simp [mkPi, substFVar]

@[simp] theorem substFVar_mkSigma (x : String) (u A B : Pattern) :
    substFVar x u (mkSigma A B) = mkSigma (substFVar x u A) (substFVar x u B) := by
  simp [mkSigma, substFVar]

@[simp] theorem substFVar_mkId (x : String) (u A a b : Pattern) :
    substFVar x u (mkId A a b) =
      mkId (substFVar x u A) (substFVar x u a) (substFVar x u b) := by
  simp [mkId, substFVar]

@[simp] theorem substFVar_mkLam (x : String) (u body : Pattern) :
    substFVar x u (mkLam body) = mkLam (substFVar x u body) := by
  simp [mkLam, substFVar]

@[simp] theorem substFVar_mkApp (x : String) (u f a : Pattern) :
    substFVar x u (mkApp f a) = mkApp (substFVar x u f) (substFVar x u a) := by
  simp [mkApp, substFVar]

@[simp] theorem substFVar_mkPair (x : String) (u a b : Pattern) :
    substFVar x u (mkPair a b) = mkPair (substFVar x u a) (substFVar x u b) := by
  simp [mkPair, substFVar]

@[simp] theorem substFVar_mkFst (x : String) (u p : Pattern) :
    substFVar x u (mkFst p) = mkFst (substFVar x u p) := by
  simp [mkFst, substFVar]

@[simp] theorem substFVar_mkSnd (x : String) (u p : Pattern) :
    substFVar x u (mkSnd p) = mkSnd (substFVar x u p) := by
  simp [mkSnd, substFVar]

@[simp] theorem substFVar_mkRefl (x : String) (u a : Pattern) :
    substFVar x u (mkRefl a) = mkRefl (substFVar x u a) := by
  simp [mkRefl, substFVar]

@[simp] theorem substFVar_fvar_eq (x : String) (u : Pattern) :
    substFVar x u (.fvar x) = u := by simp [substFVar]

@[simp] theorem substFVar_fvar_ne {x y : String} (u : Pattern) (hne : y ≠ x) :
    substFVar x u (.fvar y) = .fvar y := by simp [substFVar, hne]

@[simp] theorem substFVar_bvar (x : String) (u : Pattern) (n : Nat) :
    substFVar x u (.bvar n) = .bvar n := by unfold substFVar; rfl

/-! ## substFVar with fresh variable is identity -/

/-- If `x` is fresh in `p`, then `substFVar x u p = p`. -/
theorem substFVar_fresh {x : String} {u : Pattern} {p : Pattern}
    (hfresh : isFresh x p = true) :
    substFVar x u p = p := by
  induction p using Pattern.inductionOn with
  | hbvar _ => unfold substFVar; rfl
  | hfvar y =>
    unfold substFVar
    have hne : y ≠ x := by
      simp only [isFresh, freeVars, Bool.not_eq_true'] at hfresh
      intro h; subst h; simp at hfresh
    simp [hne]
  | happly c args ih =>
    unfold substFVar; congr 1
    exact list_map_eq_self fun a ha => ih a ha (isFresh_of_apply_mem hfresh ha)
  | hlambda body ih =>
    unfold substFVar; congr 1; exact ih (isFresh_of_lambda hfresh)
  | hmultiLambda n body ih =>
    unfold substFVar; congr 1; exact ih (isFresh_of_multiLambda hfresh)
  | hsubst body repl ihb ihr =>
    unfold substFVar; congr 1
    · exact ihb (isFresh_of_subst_body hfresh)
    · exact ihr (isFresh_of_subst_repl hfresh)
  | hcollection ct elems rest ih =>
    unfold substFVar; congr 1
    exact list_map_eq_self fun a ha => ih a ha (isFresh_of_collection_mem hfresh ha)

/-! ## openBVar interaction with MeTTa-Pure constructors -/

@[simp] theorem openBVar_u0 (k : Nat) (u : Pattern) :
    openBVar k u u0 = u0 := by simp [u0, openBVar]

@[simp] theorem openBVar_u1 (k : Nat) (u : Pattern) :
    openBVar k u u1 = u1 := by simp [u1, openBVar]

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

/-! ## substFVar_intro — The Key Connecting Lemma -/

/-- `substFVar_intro`: substituting after opening with a fresh fvar
    equals direct opening. -/
theorem substFVar_intro {x : String} {u : Pattern} (p : Pattern)
    (hfresh : isFresh x p = true) (k : Nat) :
    substFVar x u (openBVar k (.fvar x) p) = openBVar k u p := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    unfold openBVar; split
    · unfold substFVar; simp
    · unfold substFVar; rfl
  | hfvar y =>
    unfold openBVar substFVar
    have hne : y ≠ x := by
      simp only [isFresh, freeVars, Bool.not_eq_true'] at hfresh
      intro h; subst h; simp at hfresh
    simp [hne]
  | happly c args ih =>
    simp only [openBVar, substFVar, List.map_map]
    congr 1; apply List.map_congr_left; intro a ha
    simp only [Function.comp]
    exact ih a ha (isFresh_of_apply_mem hfresh ha) k
  | hlambda body ih =>
    simp only [openBVar, substFVar]; congr 1
    exact ih (isFresh_of_lambda hfresh) (k + 1)
  | hmultiLambda n body ih =>
    simp only [openBVar, substFVar]; congr 1
    exact ih (isFresh_of_multiLambda hfresh) (k + n)
  | hsubst body repl ihb ihr =>
    simp only [openBVar, substFVar]; congr 1
    · exact ihb (isFresh_of_subst_body hfresh) (k + 1)
    · exact ihr (isFresh_of_subst_repl hfresh) k
  | hcollection ct elems rest ih =>
    simp only [openBVar, substFVar, List.map_map]; congr 1
    apply List.map_congr_left; intro a ha
    simp only [Function.comp]
    exact ih a ha (isFresh_of_collection_mem hfresh ha) k

/-! ## Commutation and Conversion Transport -/

/-- Free-variable substitution commutes with opening when the replacement
    term is locally closed at the opening depth. -/
theorem substFVar_openBVar_comm {x : String} {u a p : Pattern} {k : Nat}
    (hlc : lc_at k u = true) :
    substFVar x u (openBVar k a p) =
      openBVar k (substFVar x u a) (substFVar x u p) := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
      by_cases hnk : n == k
      · simp [openBVar, hnk]
      · simp [openBVar, hnk]
  | hfvar y =>
      by_cases hyx : y = x
      · simp [openBVar, hyx]
        exact (openBVar_lc_at k (substFVar x u a) u hlc).symm
      · simp [openBVar, hyx]
  | happly c args ih =>
      simp only [openBVar, substFVar, List.map_map]
      congr 1
      exact List.map_congr_left (fun q hq => ih q hq (k := k) hlc)
  | hlambda body ih =>
      simp only [openBVar, substFVar]
      congr 1
      exact ih (k := k + 1) (lc_at_mono hlc (Nat.le_add_right k 1))
  | hmultiLambda n body ih =>
      simp only [openBVar, substFVar]
      congr 1
      exact ih (k := k + n) (lc_at_mono hlc (Nat.le_add_right k n))
  | hsubst body repl ihb ihr =>
      simp only [openBVar, substFVar]
      congr 1
      · exact ihb (k := k + 1) (lc_at_mono hlc (Nat.le_add_right k 1))
      · exact ihr (k := k) hlc
  | hcollection ct elems rest ih =>
      simp only [openBVar, substFVar, List.map_map]
      congr 1
      exact List.map_congr_left (fun q hq => ih q hq (k := k) hlc)

/-- Substitution preserves definitional equality for locally closed
    replacement terms. -/
private theorem pureTm_substFVar {x : String} {u p : Pattern}
    (hu : PureTmPattern u) (hp : PureTmPattern p) :
    PureTmPattern (substFVar x u p) := by
  induction hp with
  | bvar n =>
      simp
      exact .bvar n
  | fvar y =>
      by_cases hyx : y = x
      · subst hyx
        simpa [substFVar]
      · simpa [substFVar, hyx] using PureTmPattern.fvar y
  | u0 =>
      simpa [substFVar, u0] using PureTmPattern.u0
  | u1 =>
      simpa [substFVar, u1] using PureTmPattern.u1
  | pi hA hB ihA ihB =>
      simpa [substFVar_mkPi] using PureTmPattern.pi ihA ihB
  | sigma hA hB ihA ihB =>
      simpa [substFVar_mkSigma] using PureTmPattern.sigma ihA ihB
  | id hA ha hb ihA iha ihb =>
      simpa [substFVar_mkId] using PureTmPattern.id ihA iha ihb
  | lam hBody ihBody =>
      simpa [substFVar_mkLam] using PureTmPattern.lam ihBody
  | app hf ha ihf iha =>
      simpa [substFVar_mkApp] using PureTmPattern.app ihf iha
  | pair ha hb iha ihb =>
      simpa [substFVar_mkPair] using PureTmPattern.pair iha ihb
  | fst hp ihp =>
      simpa [substFVar_mkFst] using PureTmPattern.fst ihp
  | snd hp ihp =>
      simpa [substFVar_mkSnd] using PureTmPattern.snd ihp
  | refl ha iha =>
      simpa [substFVar_mkRefl] using PureTmPattern.refl iha

theorem pureConv_substFVar {x : String} {u : Pattern}
    (hlc : lc_at 0 u = true) (huPure : PureTmPattern u)
    {t₁ t₂ : Pattern} (hconv : PureConv t₁ t₂) :
    PureConv (substFVar x u t₁) (substFVar x u t₂) := by
  induction hconv with
  | refl t htPure =>
      simpa using PureConv.refl (substFVar x u t) (pureTm_substFVar huPure htPure)
  | symm _ ih => exact PureConv.symm ih
  | trans _ _ ih₁ ih₂ => exact PureConv.trans ih₁ ih₂
  | betaPi body a hbodyPure haPure hlcBody hlcA =>
      refine PureConv.trans (t₂ := openBVar 0 (substFVar x u a) (substFVar x u body)) ?_ ?_
      · simpa [mkApp, mkLam, substFVar] using
          (PureConv.betaPi (substFVar x u body) (substFVar x u a)
            (pureTm_substFVar huPure hbodyPure)
            (pureTm_substFVar huPure haPure)
            (lc_at_substFVar_local hlcBody (lc_at_mono hlc (Nat.le_add_right 0 1)))
            (lc_at_substFVar_local hlcA hlc))
      · rw [(substFVar_openBVar_comm (x := x) (u := u) (a := a) (p := body) (k := 0) hlc).symm]
        exact PureConv.refl _ (pureTm_substFVar huPure (pureTm_openBVar haPure hbodyPure))
  | betaSigmaFst a b haPure hbPure hlcA hlcB =>
      simpa [mkFst, mkPair, substFVar] using
        (PureConv.betaSigmaFst (substFVar x u a) (substFVar x u b)
          (pureTm_substFVar huPure haPure)
          (pureTm_substFVar huPure hbPure)
          (lc_at_substFVar_local hlcA hlc) (lc_at_substFVar_local hlcB hlc))
  | betaSigmaSnd a b haPure hbPure hlcA hlcB =>
      simpa [mkSnd, mkPair, substFVar] using
        (PureConv.betaSigmaSnd (substFVar x u a) (substFVar x u b)
          (pureTm_substFVar huPure haPure)
          (pureTm_substFVar huPure hbPure)
          (lc_at_substFVar_local hlcA hlc) (lc_at_substFVar_local hlcB hlc))
  | congPi L hA hB ihA ihB =>
      simp only [substFVar_mkPi]
      refine .congPi (L ∪ {x}) ihA (fun y hy => ?_)
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ihB y hyL
      rwa [substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx] at key
  | congSigma L hA hB ihA ihB =>
      simp only [substFVar_mkSigma]
      refine .congSigma (L ∪ {x}) ihA (fun y hy => ?_)
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ihB y hyL
      rwa [substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx] at key
  | congId _ _ _ ihA iha ihb =>
      simpa using PureConv.congId ihA iha ihb
  | congLam L h ih =>
      simp only [substFVar_mkLam]
      refine .congLam (L ∪ {x}) (fun y hy => ?_)
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ih y hyL
      rwa [substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx] at key
  | congApp _ _ ihf iha => simpa using PureConv.congApp ihf iha
  | congPair _ _ iha ihb => simpa using PureConv.congPair iha ihb
  | congFst _ ih => simpa using PureConv.congFst ih
  | congSnd _ ih => simpa using PureConv.congSnd ih
  | congRefl _ ih => simpa using PureConv.congRefl ih

/-! ## Context helpers for substitution -/

def ctxNames (Γ : PureCtx) : List String := Γ.map Prod.fst

@[simp] theorem ctxNames_append (Γ Δ : PureCtx) :
    ctxNames (Γ ++ Δ) = ctxNames Γ ++ ctxNames Δ := by simp [ctxNames]

@[simp] theorem ctxNames_cons (x : String) (A : Pattern) (Γ : PureCtx) :
    ctxNames ((x, A) :: Γ) = x :: ctxNames Γ := by simp [ctxNames]

theorem mem_ctxNames_of_mem {x : String} {A : Pattern} {Γ : PureCtx}
    (hmem : (x, A) ∈ Γ) : x ∈ ctxNames Γ := by
  exact List.mem_map.mpr ⟨(x, A), hmem, rfl⟩

def ctxFresh (x : String) (Γ : PureCtx) : Prop :=
  ∀ y T, (y, T) ∈ Γ → isFresh x T = true

def substCtx (x : String) (u : Pattern) (Γ : PureCtx) : PureCtx :=
  Γ.filterMap fun (y, A) =>
    if y = x then none else some (y, substFVar x u A)

@[simp] theorem substCtx_nil (x : String) (u : Pattern) :
    substCtx x u [] = [] := rfl

@[simp] theorem substCtx_cons_eq (x : String) (u : Pattern) (A : Pattern) (Γ : PureCtx) :
    substCtx x u ((x, A) :: Γ) = substCtx x u Γ := by simp [substCtx]

@[simp] theorem substCtx_cons_ne {x y : String} (u : Pattern) (A : Pattern) (Γ : PureCtx)
    (hne : y ≠ x) :
    substCtx x u ((y, A) :: Γ) = (y, substFVar x u A) :: substCtx x u Γ := by
  simp [substCtx, hne]

@[simp] theorem substCtx_append (x : String) (u : Pattern) (Γ Δ : PureCtx) :
    substCtx x u (Γ ++ Δ) = substCtx x u Γ ++ substCtx x u Δ := by
  induction Γ with
  | nil => simp [substCtx]
  | cons b Γ ih =>
      rcases b with ⟨y, A⟩
      by_cases h : y = x
      · simp [substCtx, h]
      · simp [substCtx, h]

theorem mem_substCtx {x y : String} {A u : Pattern} {Γ : PureCtx}
    (hmem : (y, A) ∈ Γ) (hne : y ≠ x) :
    (y, substFVar x u A) ∈ substCtx x u Γ := by
  rw [substCtx, List.mem_filterMap]
  refine ⟨(y, A), hmem, ?_⟩; simp [hne]

/-! ## Context monotonicity -/

theorem context_monotone {Γ Γ' : PureCtx} {t A : Pattern}
    (hsub : ∀ x T, (x, T) ∈ Γ → (x, T) ∈ Γ')
    (ht : PureHasType Γ t A) :
    PureHasType Γ' t A := by
  induction ht generalizing Γ' with
  | u0_type Γ => exact .u0_type Γ'
  | fvar Γ x A hmem hA_pure hA_lc =>
      exact .fvar Γ' x A (hsub x A hmem) hA_pure hA_lc
  | pi_form Γ L A B U hA hB ihA ihB =>
      refine .pi_form Γ' L A B U (ihA hsub) ?_
      intro z hz
      exact ihB z hz (fun y T hy => by
        rcases List.mem_cons.mp hy with hyz | hyΓ
        · exact List.mem_cons.mpr (Or.inl hyz)
        · exact List.mem_cons.mpr (Or.inr (hsub y T hyΓ)))
  | lam_intro Γ L A body B U hA hBody ihA ihBody =>
      refine .lam_intro Γ' L A body B U (ihA hsub) ?_
      intro z hz
      exact ihBody z hz (fun y T hy => by
        rcases List.mem_cons.mp hy with hyz | hyΓ
        · exact List.mem_cons.mpr (Or.inl hyz)
        · exact List.mem_cons.mpr (Or.inr (hsub y T hyΓ)))
  | app Γ L f a A B U hf ha hB ihf iha ihB =>
      refine .app Γ' L f a A B U (ihf hsub) (iha hsub) ?_
      intro z hz
      exact ihB z hz (fun y T hy => by
        rcases List.mem_cons.mp hy with hyz | hyΓ
        · exact List.mem_cons.mpr (Or.inl hyz)
        · exact List.mem_cons.mpr (Or.inr (hsub y T hyΓ)))
  | sigma_form Γ L A B U hA hB ihA ihB =>
      refine .sigma_form Γ' L A B U (ihA hsub) ?_
      intro z hz
      exact ihB z hz (fun y T hy => by
        rcases List.mem_cons.mp hy with hyz | hyΓ
        · exact List.mem_cons.mpr (Or.inl hyz)
        · exact List.mem_cons.mpr (Or.inr (hsub y T hyΓ)))
  | pair_intro Γ L a b A B U ha hb hB iha ihb ihB =>
      refine .pair_intro Γ' L a b A B U (iha hsub) (ihb hsub) ?_
      intro z hz
      exact ihB z hz (fun y T hy => by
        rcases List.mem_cons.mp hy with hyz | hyΓ
        · exact List.mem_cons.mpr (Or.inl hyz)
        · exact List.mem_cons.mpr (Or.inr (hsub y T hyΓ)))
  | fst_elim Γ L p A B U hp hB ihp ihB =>
      refine .fst_elim Γ' L p A B U (ihp hsub) ?_
      intro z hz
      exact ihB z hz (fun y T hy => by
        rcases List.mem_cons.mp hy with hyz | hyΓ
        · exact List.mem_cons.mpr (Or.inl hyz)
        · exact List.mem_cons.mpr (Or.inr (hsub y T hyΓ)))
  | snd_elim Γ L p A B U hp hB ihp ihB =>
      refine .snd_elim Γ' L p A B U (ihp hsub) ?_
      intro z hz
      exact ihB z hz (fun y T hy => by
        rcases List.mem_cons.mp hy with hyz | hyΓ
        · exact List.mem_cons.mpr (Or.inl hyz)
        · exact List.mem_cons.mpr (Or.inr (hsub y T hyΓ)))
  | id_form Γ A a b U hA ha hb ihA iha ihb =>
      exact .id_form Γ' A a b U (ihA hsub) (iha hsub) (ihb hsub)
  | refl_intro Γ a A ha iha =>
      exact .refl_intro Γ' a A (iha hsub)
  | conv Γ t A B ht hconv iht =>
      exact .conv Γ' t A B (iht hsub) hconv

theorem weakening {Γ : PureCtx} {t A : Pattern} {x : String} {U : Pattern}
    (ht : PureHasType Γ t A) :
    PureHasType ((x, U) :: Γ) t A := by
  exact context_monotone (fun y T hy => List.mem_cons_of_mem _ hy) ht

/-! ## Typing Substitution Lemma -/

theorem typing_subst {x : String} {A u : Pattern} {Γ : PureCtx}
    (hu : PureHasType Γ u A)
    (hlc_u : lc_at 0 u = true)
    (hxΓ : x ∉ ctxNames Γ)
    (hfreshA : isFresh x A = true)
    (hfreshΓ : ctxFresh x Γ) :
    ∀ {Γ₀ t B}, PureHasType Γ₀ t B →
      ∀ {Δ}, Γ₀ = Δ ++ (x, A) :: Γ → x ∉ ctxNames Δ →
        PureHasType (substCtx x u Δ ++ Γ) (substFVar x u t) (substFVar x u B) := by
  intro Γ₀ t B ht
  induction ht with
  | u0_type _ =>
      intro Δ _ _; simp; exact .u0_type _
  | fvar _ y T hmem hA_pure hA_lc =>
      intro Δ hΓ hxΔ; subst hΓ
      by_cases hyx : y = x
      · subst hyx; simp only [substFVar_fvar_eq]
        rcases List.mem_append.mp hmem with hΔ | hxA
        · exact absurd (mem_ctxNames_of_mem hΔ) hxΔ
        · rcases List.mem_cons.mp hxA with heq | hΓmem
          · obtain ⟨_, hTA⟩ := Prod.mk.inj heq; subst hTA
            rw [substFVar_fresh hfreshA]
            exact context_monotone (fun y T hy => List.mem_append_right _ hy) hu
          · exact absurd (mem_ctxNames_of_mem hΓmem) hxΓ
      · simp only [substFVar_fvar_ne _ hyx]
        rcases List.mem_append.mp hmem with hΔ | hrest
        · exact .fvar _ y _ (List.mem_append_left _ (mem_substCtx hΔ hyx))
            (pureTm_substFVar (typing_term_pure hu) hA_pure)
            (lc_at_substFVar_local hA_lc hlc_u)
        · rcases List.mem_cons.mp hrest with heq | hΓmem
          · exact absurd (Prod.mk.inj heq).1 hyx
          · rw [substFVar_fresh (hfreshΓ y T hΓmem)]
            exact .fvar _ y T (List.mem_append_right _ hΓmem) hA_pure hA_lc
  | pi_form _ L A' B' U _ _ ihA ihB =>
      intro Δ hΓ hxΔ; subst hΓ; simp only [substFVar_mkPi]
      refine .pi_form _ (L ∪ {x}) (substFVar x u A') (substFVar x u B')
        (substFVar x u U) (ihA rfl hxΔ) ?_
      intro z hz
      have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
      have hzx : z ≠ x := fun h => hz (Finset.mem_union_right _
        (Finset.mem_singleton.mpr h))
      have hxΔz : x ∉ ctxNames ((z, A') :: Δ) := by
        simp only [ctxNames_cons, List.mem_cons, not_or]; exact ⟨Ne.symm hzx, hxΔ⟩
      have h := ihB z hzL rfl hxΔz
      rw [substCtx_cons_ne u A' Δ hzx] at h
      rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hzx] at h
      exact h
  | lam_intro _ L A' body B' U _ _ ihA ihBody =>
      intro Δ hΓ hxΔ; subst hΓ; simp only [substFVar_mkLam, substFVar_mkPi]
      refine .lam_intro _ (L ∪ {x}) (substFVar x u A') (substFVar x u body)
        (substFVar x u B') (substFVar x u U) (ihA rfl hxΔ) ?_
      intro z hz
      have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
      have hzx : z ≠ x := fun h => hz (Finset.mem_union_right _
        (Finset.mem_singleton.mpr h))
      have hxΔz : x ∉ ctxNames ((z, A') :: Δ) := by
        simp only [ctxNames_cons, List.mem_cons, not_or]; exact ⟨Ne.symm hzx, hxΔ⟩
      have h := ihBody z hzL rfl hxΔz
      rw [substCtx_cons_ne u A' Δ hzx] at h
      have hsoc : ∀ p, substFVar x u (openBVar 0 (.fvar z) p) =
          openBVar 0 (.fvar z) (substFVar x u p) := fun p => by
        rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hzx]
      rw [hsoc body, hsoc B'] at h; exact h
  | app _ L' f a A' B' U _ _ _ ihf iha ihB =>
      intro Δ hΓ hxΔ; subst hΓ; simp only [substFVar_mkApp]
      rw [substFVar_openBVar_comm hlc_u]
      have hf := ihf rfl hxΔ; simp only [substFVar_mkPi] at hf
      refine .app _ (L' ∪ {x}) _ _ _ _ (substFVar x u U) hf (iha rfl hxΔ) ?_
      intro z hz
      have hzL : z ∉ L' := fun h => hz (Finset.mem_union_left _ h)
      have hzx : z ≠ x := fun h => hz (Finset.mem_union_right _
        (Finset.mem_singleton.mpr h))
      have hxΔz : x ∉ ctxNames ((z, A') :: Δ) := by
        simp only [ctxNames_cons, List.mem_cons, not_or]; exact ⟨Ne.symm hzx, hxΔ⟩
      have h := ihB z hzL rfl hxΔz
      rw [substCtx_cons_ne u A' Δ hzx] at h
      rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hzx] at h
      exact h
  | sigma_form _ L A' B' U _ _ ihA ihB =>
      intro Δ hΓ hxΔ; subst hΓ; simp only [substFVar_mkSigma]
      refine .sigma_form _ (L ∪ {x}) (substFVar x u A') (substFVar x u B')
        (substFVar x u U) (ihA rfl hxΔ) ?_
      intro z hz
      have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
      have hzx : z ≠ x := fun h => hz (Finset.mem_union_right _
        (Finset.mem_singleton.mpr h))
      have hxΔz : x ∉ ctxNames ((z, A') :: Δ) := by
        simp only [ctxNames_cons, List.mem_cons, not_or]; exact ⟨Ne.symm hzx, hxΔ⟩
      have h := ihB z hzL rfl hxΔz
      rw [substCtx_cons_ne u A' Δ hzx] at h
      rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hzx] at h
      exact h
  | pair_intro _ L' a' b' A' B' U' _ _ _ iha ihb ihB =>
      intro Δ hΓ hxΔ; subst hΓ; simp only [substFVar_mkPair, substFVar_mkSigma]
      have hb := ihb rfl hxΔ; rw [substFVar_openBVar_comm hlc_u] at hb
      refine .pair_intro _ (L' ∪ {x}) _ _ _ _ (substFVar x u U') (iha rfl hxΔ) hb ?_
      intro z hz
      have hzL : z ∉ L' := fun h => hz (Finset.mem_union_left _ h)
      have hzx : z ≠ x := fun h => hz (Finset.mem_union_right _
        (Finset.mem_singleton.mpr h))
      have hxΔz : x ∉ ctxNames ((z, A') :: Δ) := by
        simp only [ctxNames_cons, List.mem_cons, not_or]; exact ⟨Ne.symm hzx, hxΔ⟩
      have h := ihB z hzL rfl hxΔz
      rw [substCtx_cons_ne u A' Δ hzx] at h
      rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hzx] at h
      exact h
  | fst_elim _ L' p' A' B' U _ _ ihp ihB =>
      intro Δ hΓ hxΔ; subst hΓ; simp only [substFVar_mkFst]
      have hp := ihp rfl hxΔ; simp only [substFVar_mkSigma] at hp
      refine .fst_elim _ (L' ∪ {x}) _ _ _ (substFVar x u U) hp ?_
      intro z hz
      have hzL : z ∉ L' := fun h => hz (Finset.mem_union_left _ h)
      have hzx : z ≠ x := fun h => hz (Finset.mem_union_right _
        (Finset.mem_singleton.mpr h))
      have hxΔz : x ∉ ctxNames ((z, A') :: Δ) := by
        simp only [ctxNames_cons, List.mem_cons, not_or]; exact ⟨Ne.symm hzx, hxΔ⟩
      have h := ihB z hzL rfl hxΔz
      rw [substCtx_cons_ne u A' Δ hzx] at h
      rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hzx] at h
      exact h
  | snd_elim _ L' p' A' B' U _ _ ihp ihB =>
      intro Δ hΓ hxΔ; subst hΓ; simp only [substFVar_mkSnd]
      rw [substFVar_openBVar_comm hlc_u, substFVar_mkFst]
      have hp := ihp rfl hxΔ; simp only [substFVar_mkSigma] at hp
      refine .snd_elim _ (L' ∪ {x}) _ _ _ (substFVar x u U) hp ?_
      intro z hz
      have hzL : z ∉ L' := fun h => hz (Finset.mem_union_left _ h)
      have hzx : z ≠ x := fun h => hz (Finset.mem_union_right _
        (Finset.mem_singleton.mpr h))
      have hxΔz : x ∉ ctxNames ((z, A') :: Δ) := by
        simp only [ctxNames_cons, List.mem_cons, not_or]; exact ⟨Ne.symm hzx, hxΔ⟩
      have h := ihB z hzL rfl hxΔz
      rw [substCtx_cons_ne u A' Δ hzx] at h
      rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hzx] at h
      exact h
  | id_form _ A' a' b' U _ _ _ ihA iha ihb =>
      intro Δ hΓ hxΔ; subst hΓ; simp only [substFVar_mkId]
      exact .id_form _ _ _ _ _ (ihA rfl hxΔ) (iha rfl hxΔ) (ihb rfl hxΔ)
  | refl_intro _ a' A' _ iha =>
      intro Δ hΓ hxΔ; subst hΓ; simp only [substFVar_mkRefl, substFVar_mkId]
      exact .refl_intro _ _ _ (iha rfl hxΔ)
  | conv _ t' A' B' _ hconv iht =>
      intro Δ hΓ hxΔ; subst hΓ
      exact .conv _ _ _ _ (iht rfl hxΔ) (pureConv_substFVar hlc_u (typing_term_pure hu) hconv)

/-! ## Pattern Discrimination -/

private theorem apply_label_inj {c₁ c₂ : String} {args₁ args₂ : List Pattern}
    (h : Pattern.apply c₁ args₁ = Pattern.apply c₂ args₂) : c₁ = c₂ ∧ args₁ = args₂ :=
  ⟨Pattern.apply.inj h |>.1, Pattern.apply.inj h |>.2⟩

/-! ## Generation Lemmas -/

/-- App generation (auxiliary). -/
private theorem app_generation_aux {Γ : PureCtx} {p C : Pattern}
    (ht : PureHasType Γ p C) :
    ∀ f a, p = mkApp f a →
    ∃ A B U, ∃ L : Finset String,
      PureHasType Γ f (mkPi A B) ∧ PureHasType Γ a A ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv (openBVar 0 a B) C := by
  induction ht with
  | app _ L _ _ A' B' U hf ha hB _ _ _ =>
      intro f a heq
      simp only [mkApp] at heq
      have hinj := apply_label_inj heq
      have hargs := hinj.2; simp at hargs
      obtain ⟨hf_eq, ha_eq⟩ := hargs; subst hf_eq; subst ha_eq
      exact ⟨A', B', U, L, hf, ha, hB,
        .refl _ (typing_type_pure (.app _ L _ _ A' B' U hf ha hB))⟩
  | conv _ _ A' B' _ hconv ih =>
      intro f a heq
      obtain ⟨A₀, B₀, U₀, L₀, hf₀, ha₀, hB₀, hconv₀⟩ := ih f a heq
      exact ⟨A₀, B₀, U₀, L₀, hf₀, ha₀, hB₀, .trans hconv₀ hconv⟩
  | u0_type _ => intro _ _ h; exact absurd h (by simp [mkApp, u0])
  | fvar _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkApp])
  | pi_form _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkApp, mkPi])
  | lam_intro _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkApp, mkLam])
  | sigma_form _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkApp, mkSigma])
  | pair_intro _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkApp, mkPair])
  | fst_elim _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkApp, mkFst])
  | snd_elim _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkApp, mkSnd])
  | id_form _ _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkApp, mkId])
  | refl_intro _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkApp, mkRefl])

/-- App generation: if `Γ ⊢ mkApp f a : C`, then there exist `A`, `B`, `U`, `L`
    with f, a, B typing and `PureConv (openBVar 0 a B) C`. -/
theorem app_generation {Γ : PureCtx} {f a C : Pattern}
    (ht : PureHasType Γ (mkApp f a) C) :
    ∃ A B U, ∃ L : Finset String,
      PureHasType Γ f (mkPi A B) ∧ PureHasType Γ a A ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv (openBVar 0 a B) C :=
  app_generation_aux ht f a rfl

/-- Lam generation (auxiliary). -/
private theorem lam_generation_aux {Γ : PureCtx} {p C : Pattern}
    (ht : PureHasType Γ p C) :
    ∀ body, p = mkLam body →
    ∃ A B U, ∃ L : Finset String,
      PureHasType Γ A U ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ)
        (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) B)) ∧
      PureConv (mkPi A B) C := by
  induction ht with
  | lam_intro _ L A' body' B' U' hA hBody _ _ =>
      intro body heq
      simp only [mkLam] at heq
      have hinj := apply_label_inj heq
      have hargs := hinj.2; simp at hargs; subst hargs
      exact ⟨A', B', U', L, hA, hBody,
        .refl _ (typing_type_pure (.lam_intro _ L A' body' B' U' hA hBody))⟩
  | conv _ _ A' B' _ hconv ih =>
      intro body heq
      obtain ⟨A₀, B₀, U₀, L₀, hA₀, hBody₀, hconv₀⟩ := ih body heq
      exact ⟨A₀, B₀, U₀, L₀, hA₀, hBody₀, .trans hconv₀ hconv⟩
  | u0_type _ => intro _ h; exact absurd h (by simp [mkLam, u0])
  | fvar _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkLam])
  | pi_form _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkLam, mkPi])
  | app _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkLam, mkApp])
  | sigma_form _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkLam, mkSigma])
  | pair_intro _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkLam, mkPair])
  | fst_elim _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkLam, mkFst])
  | snd_elim _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkLam, mkSnd])
  | id_form _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkLam, mkId])
  | refl_intro _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkLam, mkRefl])

/-- Lam generation. -/
theorem lam_generation {Γ : PureCtx} {body C : Pattern}
    (ht : PureHasType Γ (mkLam body) C) :
    ∃ A B U, ∃ L : Finset String,
      PureHasType Γ A U ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ)
        (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) B)) ∧
      PureConv (mkPi A B) C :=
  lam_generation_aux ht body rfl

/-- Pair generation (auxiliary with explicit equality hypothesis). -/
private theorem pair_generation_aux {Γ : PureCtx} {p C : Pattern}
    (ht : PureHasType Γ p C) :
    ∀ a b, p = mkPair a b →
    ∃ A B U, ∃ L : Finset String,
      PureHasType Γ a A ∧ PureHasType Γ b (openBVar 0 a B) ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv (mkSigma A B) C := by
  induction ht with
  | pair_intro _ L' a' b' A' B' U' ha hb hB _ _ _ =>
      intro a b heq
      simp only [mkPair] at heq
      have hinj := apply_label_inj heq
      have hargs := hinj.2
      simp at hargs
      obtain ⟨ha_eq, hb_eq⟩ := hargs
      subst ha_eq; subst hb_eq
      exact ⟨A', B', U', L', ha, hb, hB,
        .refl _ (typing_type_pure (.pair_intro _ L' a' b' A' B' U' ha hb hB))⟩
  | conv _ _ A' B' _ hconv ih =>
      intro a b heq
      obtain ⟨A₀, B₀, U₀, L₀, ha₀, hb₀, hB₀, hconv₀⟩ := ih a b heq
      exact ⟨A₀, B₀, U₀, L₀, ha₀, hb₀, hB₀, .trans hconv₀ hconv⟩
  | u0_type _ => intro a b h; exact absurd h (by simp [mkPair, u0])
  | fvar _ _ _ _ _ => intro a b h; exact absurd h (by simp [mkPair])
  | pi_form _ _ _ _ _ _ _ _ _ => intro a b h; exact absurd h (by simp [mkPair, mkPi])
  | lam_intro _ _ _ _ _ _ _ _ _ _ => intro a b h; exact absurd h (by simp [mkPair, mkLam])
  | app _ _ _ _ _ _ _ _ _ _ _ _ _ => intro a b h; exact absurd h (by simp [mkPair, mkApp])
  | sigma_form _ _ _ _ _ _ _ _ _ => intro a b h; exact absurd h (by simp [mkPair, mkSigma])
  | fst_elim _ _ _ _ _ _ _ _ _ _ => intro a b h; exact absurd h (by simp [mkPair, mkFst])
  | snd_elim _ _ _ _ _ _ _ _ _ _ => intro a b h; exact absurd h (by simp [mkPair, mkSnd])
  | id_form _ _ _ _ _ _ _ _ _ _ _ => intro a b h; exact absurd h (by simp [mkPair, mkId])
  | refl_intro _ _ _ _ _ => intro a b h; exact absurd h (by simp [mkPair, mkRefl])

/-- Pair generation. -/
theorem pair_generation {Γ : PureCtx} {a b C : Pattern}
    (ht : PureHasType Γ (mkPair a b) C) :
    ∃ A B U, ∃ L : Finset String,
      PureHasType Γ a A ∧ PureHasType Γ b (openBVar 0 a B) ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv (mkSigma A B) C :=
  pair_generation_aux ht a b rfl

/-! ## Pi/Sigma Injectivity under Conversion

Delegated to Confluence.lean which proves these via Church-Rosser +
head-preservation + decomposition. -/

theorem pi_injectivity {A₁ B₁ A₂ B₂ : Pattern}
    (h : PureConv (mkPi A₁ B₁) (mkPi A₂ B₂))
    (hlc : lc_at 0 (mkPi A₁ B₁) = true) :
    PureConv A₁ A₂ ∧
      (∃ L : Finset String, ∀ x, x ∉ L →
        PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) :=
  Mettapedia.Languages.MeTTa.Pure.Confluence.pi_injectivity h hlc

theorem sigma_injectivity {A₁ B₁ A₂ B₂ : Pattern}
    (h : PureConv (mkSigma A₁ B₁) (mkSigma A₂ B₂))
    (hlc : lc_at 0 (mkSigma A₁ B₁) = true) :
    PureConv A₁ A₂ ∧
      (∃ L : Finset String, ∀ x, x ∉ L →
        PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) :=
  Mettapedia.Languages.MeTTa.Pure.Confluence.sigma_injectivity h hlc

/-! ## Freshness: picking fresh strings -/

/-- There exists a string not in any given finite set (String is infinite). -/
theorem exists_fresh (S : Finset String) : ∃ x : String, x ∉ S :=
  Infinite.exists_notMem_finset S

/-- Convert freeVars list to a Finset for freshness arguments. -/
noncomputable def freeVarsFinset (p : Pattern) : Finset String :=
  (freeVars p).toFinset

theorem isFresh_of_not_mem_freeVarsFinset {x : String} {p : Pattern}
    (h : x ∉ freeVarsFinset p) : isFresh x p = true := by
  simp only [freeVarsFinset, List.mem_toFinset] at h
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]; intro hc
  exact h (List.contains_iff_mem.mp hc)

/-- Convert context names to a Finset. -/
noncomputable def ctxNamesFinset (Γ : PureCtx) : Finset String :=
  (ctxNames Γ).toFinset

theorem not_mem_ctxNames_of_not_mem_finset {x : String} {Γ : PureCtx}
    (h : x ∉ ctxNamesFinset Γ) : x ∉ ctxNames Γ := by
  simp only [ctxNamesFinset, List.mem_toFinset] at h; exact h

/-- All free variables in all types of a context. Recursive for easy induction. -/
noncomputable def ctxTypeFVFinset : PureCtx → Finset String
  | [] => ∅
  | (_, T) :: Γ => (freeVars T).toFinset ∪ ctxTypeFVFinset Γ

theorem mem_ctxTypeFVFinset_of_mem {x : String} {y : String} {T : Pattern} {Γ : PureCtx}
    (hmem : (y, T) ∈ Γ) (hfv : x ∈ (freeVars T).toFinset) :
    x ∈ ctxTypeFVFinset Γ := by
  induction Γ with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.mem_cons] at hmem
    simp only [ctxTypeFVFinset]
    rcases hmem with ⟨rfl, rfl⟩ | htail
    · exact Finset.mem_union_left _ hfv
    · exact Finset.mem_union_right _ (ih htail)

theorem ctxFresh_of_not_mem_ctxTypeFVFinset {x : String} {Γ : PureCtx}
    (h : x ∉ ctxTypeFVFinset Γ) : ctxFresh x Γ := by
  intro y T hmem
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]; intro hc
  have hfv : x ∈ (freeVars T).toFinset :=
    List.mem_toFinset.mpr (List.contains_iff_mem.mp hc)
  exact h (mem_ctxTypeFVFinset_of_mem hmem hfv)

/-- Legacy alias for backward compat. -/
noncomputable def ctxTypesFinset (Γ : PureCtx) : Finset String := ctxTypeFVFinset Γ

theorem ctxFresh_of_not_mem {x : String} {Γ : PureCtx}
    (h : ∀ y T, (y, T) ∈ Γ → x ∉ (freeVars T).toFinset) : ctxFresh x Γ := by
  exact ctxFresh_of_not_mem_ctxTypeFVFinset (by
    intro hmem
    induction Γ with
    | nil => simp [ctxTypeFVFinset] at hmem
    | cons hd tl ih =>
      simp only [ctxTypeFVFinset, Finset.mem_union] at hmem
      rcases hmem with hfv | htl
      · exact h hd.1 hd.2 (List.mem_cons_self) hfv
      · exact ih (fun y T hy hfv => h y T (List.mem_cons_of_mem _ hy) hfv) htl)

/-! ## Replacement Congruence (typed patterns)

The key lemma for the congAppArg case of SR: if `PureConv u u'` and `q`
is well-typed, then `PureConv (substFVar x u q) (substFVar x u' q)`.

Proved by induction on the typing derivation for `q`. The binder cases
use the cofinite body typing + substFVar_openBVar_comm. -/

theorem pureConv_substFVar_repl {x : String} {u u' : Pattern}
    (hconv : PureConv u u') (hlc : lc_at 0 u = true) (hlc' : lc_at 0 u' = true)
    {Γ : PureCtx} {q A : Pattern}
    (hq : PureHasType Γ q A) :
    PureConv (substFVar x u q) (substFVar x u' q) := by
  induction hq with
  | u0_type _ => simp; exact .refl _ PureTmPattern.u0
  | fvar _ y _ _ _ _ =>
      by_cases hyx : y = x
      · simp [hyx]; exact hconv
      · simp [hyx]; exact .refl _ (PureTmPattern.fvar y)
  | pi_form _ L A' B' U _ _ ihA ihB =>
      simp only [substFVar_mkPi]
      refine .congPi (L ∪ {x}) ihA (fun y hy => ?_)
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ihB y hyL
      rwa [substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc', substFVar_fvar_ne u' hyx] at key
  | lam_intro _ L A' body B' U _ _ ihA ihBody =>
      simp only [substFVar_mkLam]
      refine .congLam (L ∪ {x}) (fun y hy => ?_)
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ihBody y hyL
      rwa [substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc', substFVar_fvar_ne u' hyx] at key
  | app _ _ _ _ _ _ _ _ _ _ ihf iha _ =>
      simp only [substFVar_mkApp]; exact .congApp ihf iha
  | sigma_form _ L A' B' U _ _ ihA ihB =>
      simp only [substFVar_mkSigma]
      refine .congSigma (L ∪ {x}) ihA (fun y hy => ?_)
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ihB y hyL
      rwa [substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc', substFVar_fvar_ne u' hyx] at key
  | pair_intro _ _ _ _ _ _ _ _ _ _ iha ihb _ =>
      simp only [substFVar_mkPair]; exact .congPair iha ihb
  | fst_elim _ _ _ _ _ _ _ _ ihp _ =>
      simp only [substFVar_mkFst]; exact .congFst ihp
  | snd_elim _ _ _ _ _ _ _ _ ihp _ =>
      simp only [substFVar_mkSnd]; exact .congSnd ihp
  | id_form _ _ _ _ _ _ _ _ ihA iha ihb =>
      simp only [substFVar_mkId]; exact .congId ihA iha ihb
  | refl_intro _ _ _ _ iha =>
      simp only [substFVar_mkRefl]; exact .congRefl iha
  | conv _ _ _ _ _ _ ih => exact ih

/-! ## Typed terms are locally closed -/

/-- Well-typed terms are locally closed at level 0. -/
theorem typing_lc {Γ : PureCtx} {t A : Pattern}
    (ht : PureHasType Γ t A) : lc_at 0 t = true := by
  induction ht with
  | u0_type _ => simp [u0, lc_at, lc_at_list]
  | fvar _ _ _ _ _ => simp [lc_at]
  | pi_form _ L A B U hA hB ihA ihB =>
      simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true]
      refine ⟨ihA, ?_, trivial⟩
      obtain ⟨x, hx⟩ := exists_fresh L
      exact lc_at_of_openBVar (ihB x hx)
  | lam_intro _ L A body B U hA hBody ihA ihBody =>
      simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true]
      refine ⟨?_, trivial⟩
      obtain ⟨x, hx⟩ := exists_fresh L
      exact lc_at_of_openBVar (ihBody x hx)
  | app _ _ _ _ _ _ _ _ _ _ ihf iha _ =>
      simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true]
      exact ⟨ihf, iha, trivial⟩
  | sigma_form _ L A B U hA hB ihA ihB =>
      simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true]
      refine ⟨ihA, ?_, trivial⟩
      obtain ⟨x, hx⟩ := exists_fresh L
      exact lc_at_of_openBVar (ihB x hx)
  | pair_intro _ _ _ _ _ _ _ _ _ _ iha ihb _ =>
      simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true]
      exact ⟨iha, ihb, trivial⟩
  | fst_elim _ _ _ _ _ _ _ _ ihp _ =>
      simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true]
      exact ⟨ihp, trivial⟩
  | snd_elim _ _ _ _ _ _ _ _ ihp _ =>
      simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true]
      exact ⟨ihp, trivial⟩
  | id_form _ _ _ _ _ _ _ _ ihA iha ihb =>
      simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true]
      exact ⟨ihA, iha, ihb, trivial⟩
  | refl_intro _ _ _ _ iha =>
      simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true]
      exact ⟨iha, trivial⟩
  | conv _ _ _ _ _ _ ih => exact ih

/-- The type of a well-typed term is locally closed. -/
theorem typing_type_lc {Γ : PureCtx} {t A : Pattern}
    (ht : PureHasType Γ t A) : lc_at 0 A = true := by
  induction ht with
  | u0_type _ => simp [u1, lc_at, lc_at_list]
  | fvar _ _ _ _ _ hA_lc => exact hA_lc
  | pi_form _ L A B U hA hB ihA ihB =>
      -- Type is U; ihA : lc_at 0 U = true
      exact ihA
  | lam_intro _ L A body B U hA hBody ihA ihBody =>
      -- Type is mkPi A B
      simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true]
      refine ⟨typing_lc hA, ?_, trivial⟩
      obtain ⟨x, hx⟩ := exists_fresh L
      -- ihBody x hx : lc_at 0 (openBVar 0 (.fvar x) B) = true
      exact lc_at_of_openBVar (ihBody x hx)
  | app _ _ _ _ _ B _ hf ha hB ihf iha ihB =>
      -- Type is openBVar 0 a B; ihf : lc_at 0 (mkPi A B) = true
      have hlcB : lc_at 1 B = true := by
        simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true] at ihf; exact ihf.2.1
      exact lc_at_openBVar_result hlcB (typing_lc ha)
  | sigma_form _ L A B U hA hB ihA ihB => exact ihA
  | pair_intro _ L a b A B U ha hb hB iha ihb ihB =>
      -- Type is mkSigma A B
      simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true]
      constructor
      · -- lc_at 0 A: iha gives lc_at 0 A (the type of a is A, not the result type)
        -- Actually iha : lc_at 0 (type of a) where the type of a in ha is A
        -- Since ha : PureHasType Γ a A, typing_lc ha gives lc_at 0 a
        -- We need lc_at 0 A. From typing_type_lc ha = iha? No.
        -- iha is the IH for ha, which gives typing_type_lc of ha = lc_at 0 A. ✓
        exact iha
      constructor
      · obtain ⟨x, hx⟩ := exists_fresh L
        exact lc_at_of_openBVar (typing_lc (hB x hx))
      · trivial
  | fst_elim _ _ _ _ _ _ hp hB ihp ihB =>
      -- Type is A; ihp : lc_at 0 (mkSigma A B) = true
      simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true] at ihp
      exact ihp.1
  | snd_elim _ L p _ B _ hp hB ihp ihB =>
      -- Type is openBVar 0 (mkFst p) B; ihp : lc_at 0 (mkSigma _ B) = true
      have hlcB : lc_at 1 B = true := by
        simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true] at ihp; exact ihp.2.1
      have hlcFstP : lc_at 0 (mkFst p) = true := by
        simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true]
        exact ⟨typing_lc hp, trivial⟩
      exact lc_at_openBVar_result hlcB hlcFstP
  | id_form _ _ _ _ _ _ _ _ ihA _ _ => exact ihA
  | refl_intro _ a A ha iha =>
      -- Type is mkId A a a; iha : lc_at 0 A = true
      simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true]
      exact ⟨iha, typing_lc ha, typing_lc ha, trivial⟩
  | conv _ _ _ _ _ hconv ih =>
      -- ih : lc_at 0 A; hconv : PureConv A B; need lc_at 0 B
      exact (Mettapedia.Languages.MeTTa.Pure.Confluence.PureConv_preserves_lc_both hconv).1 ih

/-! ## Context conversion -/

/-- Helper: extend a context conversion proof under a binder with same type. -/
private theorem ctxConv_cons_same
    {Γ₁ Γ₂ : PureCtx} {z : String} {C : Pattern}
    (hctx : ∀ y B, (y, B) ∈ Γ₁ → PureTmPattern B →
      ∃ B', (y, B') ∈ Γ₂ ∧ PureConv B' B) :
    ∀ y B, (y, B) ∈ (z, C) :: Γ₁ → PureTmPattern B →
      ∃ B', (y, B') ∈ (z, C) :: Γ₂ ∧ PureConv B' B := by
  intro y B hmem hBpure
  simp only [List.mem_cons] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | htail
  · exact ⟨C, List.mem_cons_self, .refl _ hBpure⟩
  · obtain ⟨B', hmem', hconv⟩ := hctx y B htail hBpure
    exact ⟨B', List.mem_cons_of_mem _ hmem', hconv⟩

/-- General context conversion: if every binding in Γ₁ has a convertible
    counterpart in Γ₂, typing transfers. -/
private theorem context_conv_any {Γ₁ Γ₂ : PureCtx} {t T : Pattern}
    (ht : PureHasType Γ₁ t T)
    (hctx : ∀ y B, (y, B) ∈ Γ₁ → PureTmPattern B →
      ∃ B', (y, B') ∈ Γ₂ ∧ PureConv B' B) :
    PureHasType Γ₂ t T := by
  induction ht generalizing Γ₂ with
  | u0_type _ => exact .u0_type _
  | fvar _ y B hmem hA_pure hA_lc =>
      obtain ⟨B', hmem', hconv⟩ := hctx y B hmem hA_pure
      have hB'_lc := (Mettapedia.Languages.MeTTa.Pure.Confluence.PureConv_preserves_lc_both hconv).2 hA_lc
      exact .conv _ _ _ _ (.fvar _ y B' hmem' (PureConv_leftPure hconv) hB'_lc) hconv
  | pi_form _ L A B U hA hB ihA ihB =>
      exact .pi_form _ L _ _ _ (ihA hctx) (fun z hz =>
        ihB z hz (ctxConv_cons_same hctx) )
  | lam_intro _ L A body B U hA hBody ihA ihBody =>
      exact .lam_intro _ L _ _ _ _ (ihA hctx) (fun z hz =>
        ihBody z hz (ctxConv_cons_same hctx))
  | app _ L f a A B U hf ha hB ihf iha ihB =>
      exact .app _ L _ _ _ _ _ (ihf hctx) (iha hctx) (fun z hz =>
        ihB z hz (ctxConv_cons_same hctx))
  | sigma_form _ L A B U hA hB ihA ihB =>
      exact .sigma_form _ L _ _ _ (ihA hctx) (fun z hz =>
        ihB z hz (ctxConv_cons_same hctx))
  | pair_intro _ L a b A B U ha hb hB iha ihb ihB =>
      exact .pair_intro _ L _ _ _ _ _ (iha hctx) (ihb hctx)
        (fun z hz => ihB z hz (ctxConv_cons_same hctx))
  | fst_elim _ L p A B U hp hB ihp ihB =>
      exact .fst_elim _ L _ _ _ _ (ihp hctx) (fun z hz =>
        ihB z hz (ctxConv_cons_same hctx))
  | snd_elim _ L p A B U hp hB ihp ihB =>
      exact .snd_elim _ L _ _ _ _ (ihp hctx) (fun z hz =>
        ihB z hz (ctxConv_cons_same hctx))
  | id_form _ _ _ _ _ _ _ _ ihA iha ihb =>
      exact .id_form _ _ _ _ _ (ihA hctx) (iha hctx) (ihb hctx)
  | refl_intro _ _ _ _ iha =>
      exact .refl_intro _ _ _ (iha hctx)
  | conv _ _ _ _ _ hBC ih => exact .conv _ _ _ _ (ih hctx) hBC

/-- If `PureConv A A'`, then typing in context `(x, A) :: Γ` implies
    typing in context `(x, A') :: Γ`. -/
theorem context_conv_head
    {Γ : PureCtx} {x : String} {A A' t T : Pattern}
    (hAA' : PureConv A A')
    (ht : PureHasType ((x, A) :: Γ) t T) :
    PureHasType ((x, A') :: Γ) t T :=
  context_conv_any ht (fun y B hmem hBpure => by
    simp only [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | htail
    · exact ⟨A', List.mem_cons_self, .symm hAA'⟩
    · exact ⟨B, List.mem_cons_of_mem _ htail, .refl _ hBpure⟩)

/-! ## Additional Generation Lemmas

Invert typing for Pi, Sigma, Id, Fst, Snd, Refl by induction on PureHasType,
matching the relevant constructor and threading through conv. -/

-- Absurdity macro: each non-matching constructor is dismissed by simp
-- on the equality between distinct mk-constructors.

private theorem pi_generation_aux {Γ : PureCtx} {p C : Pattern}
    (ht : PureHasType Γ p C) :
    ∀ A B, p = mkPi A B →
    ∃ U, ∃ L : Finset String,
      PureHasType Γ A U ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv U C := by
  induction ht with
  | pi_form _ L' A' B' U' hA hB _ _ =>
      intro A B heq; simp only [mkPi] at heq
      have hinj := apply_label_inj heq
      have hargs := hinj.2; simp at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      exact ⟨U', L', hA, hB, .refl _ (typing_type_pure hA)⟩
  | conv _ _ _ _ _ hconv ih =>
      intro A B heq
      obtain ⟨U₀, L₀, hA₀, hB₀, hconv₀⟩ := ih A B heq
      exact ⟨U₀, L₀, hA₀, hB₀, .trans hconv₀ hconv⟩
  | u0_type _ => intro _ _ h; exact absurd h (by simp [mkPi, u0])
  | fvar _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkPi])
  | lam_intro _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkPi, mkLam])
  | app _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkPi, mkApp])
  | sigma_form _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkPi, mkSigma])
  | pair_intro _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkPi, mkPair])
  | fst_elim _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkPi, mkFst])
  | snd_elim _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkPi, mkSnd])
  | id_form _ _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkPi, mkId])
  | refl_intro _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkPi, mkRefl])

theorem pi_generation {Γ : PureCtx} {A B C : Pattern}
    (ht : PureHasType Γ (mkPi A B) C) :
    ∃ U, ∃ L : Finset String,
      PureHasType Γ A U ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv U C :=
  pi_generation_aux ht A B rfl

private theorem sigma_generation_aux {Γ : PureCtx} {p C : Pattern}
    (ht : PureHasType Γ p C) :
    ∀ A B, p = mkSigma A B →
    ∃ U, ∃ L : Finset String,
      PureHasType Γ A U ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv U C := by
  induction ht with
  | sigma_form _ L' A' B' U' hA hB _ _ =>
      intro A B heq; simp only [mkSigma] at heq
      have hinj := apply_label_inj heq
      have hargs := hinj.2; simp at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      exact ⟨U', L', hA, hB, .refl _ (typing_type_pure hA)⟩
  | conv _ _ _ _ _ hconv ih =>
      intro A B heq
      obtain ⟨U₀, L₀, hA₀, hB₀, hconv₀⟩ := ih A B heq
      exact ⟨U₀, L₀, hA₀, hB₀, .trans hconv₀ hconv⟩
  | u0_type _ => intro _ _ h; exact absurd h (by simp [mkSigma, u0])
  | fvar _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkSigma])
  | pi_form _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkSigma, mkPi])
  | lam_intro _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkSigma, mkLam])
  | app _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkSigma, mkApp])
  | pair_intro _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkSigma, mkPair])
  | fst_elim _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkSigma, mkFst])
  | snd_elim _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkSigma, mkSnd])
  | id_form _ _ _ _ _ _ _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkSigma, mkId])
  | refl_intro _ _ _ _ _ => intro _ _ h; exact absurd h (by simp [mkSigma, mkRefl])

theorem sigma_generation {Γ : PureCtx} {A B C : Pattern}
    (ht : PureHasType Γ (mkSigma A B) C) :
    ∃ U, ∃ L : Finset String,
      PureHasType Γ A U ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv U C :=
  sigma_generation_aux ht A B rfl

private theorem id_generation_aux {Γ : PureCtx} {p C : Pattern}
    (ht : PureHasType Γ p C) :
    ∀ A a b, p = mkId A a b →
    ∃ U, PureHasType Γ A U ∧ PureHasType Γ a A ∧ PureHasType Γ b A ∧
      PureConv U C := by
  induction ht with
  | id_form _ A' a' b' U' hA ha hb _ _ _ =>
      intro A a b heq; simp only [mkId] at heq
      have hinj := apply_label_inj heq
      have hargs := hinj.2; simp at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      exact ⟨U', hA, ha, hb, .refl _ (typing_type_pure hA)⟩
  | conv _ _ _ _ _ hconv ih =>
      intro A a b heq
      obtain ⟨U₀, hA₀, ha₀, hb₀, hconv₀⟩ := ih A a b heq
      exact ⟨U₀, hA₀, ha₀, hb₀, .trans hconv₀ hconv⟩
  | u0_type _ => intro _ _ _ h; exact absurd h (by simp [mkId, u0])
  | fvar _ _ _ _ _ => intro _ _ _ h; exact absurd h (by simp [mkId])
  | pi_form _ _ _ _ _ _ _ _ _ => intro _ _ _ h; exact absurd h (by simp [mkId, mkPi])
  | lam_intro _ _ _ _ _ _ _ _ _ _ => intro _ _ _ h; exact absurd h (by simp [mkId, mkLam])
  | app _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ _ _ h; exact absurd h (by simp [mkId, mkApp])
  | sigma_form _ _ _ _ _ _ _ _ _ => intro _ _ _ h; exact absurd h (by simp [mkId, mkSigma])
  | pair_intro _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ _ _ h; exact absurd h (by simp [mkId, mkPair])
  | fst_elim _ _ _ _ _ _ _ _ _ _ => intro _ _ _ h; exact absurd h (by simp [mkId, mkFst])
  | snd_elim _ _ _ _ _ _ _ _ _ _ => intro _ _ _ h; exact absurd h (by simp [mkId, mkSnd])
  | refl_intro _ _ _ _ _ => intro _ _ _ h; exact absurd h (by simp [mkId, mkRefl])

theorem id_generation {Γ : PureCtx} {A a b C : Pattern}
    (ht : PureHasType Γ (mkId A a b) C) :
    ∃ U, PureHasType Γ A U ∧ PureHasType Γ a A ∧ PureHasType Γ b A ∧
      PureConv U C :=
  id_generation_aux ht A a b rfl

private theorem fst_generation_aux {Γ : PureCtx} {p C : Pattern}
    (ht : PureHasType Γ p C) :
    ∀ q, p = mkFst q →
    ∃ A B U, ∃ L : Finset String,
      PureHasType Γ q (mkSigma A B) ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv A C := by
  induction ht with
  | fst_elim _ L' p' A' B' U' hp hB _ _ =>
      intro q heq; simp only [mkFst] at heq
      have hinj := apply_label_inj heq
      have hargs := hinj.2; simp at hargs; subst hargs
      have hSigmaPure : PureTmPattern (mkSigma A' B') := typing_type_pure hp
      exact ⟨A', B', U', L', hp, hB, .refl _ (pure_sigma_inv hSigmaPure).1⟩
  | conv _ _ _ _ _ hconv ih =>
      intro q heq
      obtain ⟨A₀, B₀, U₀, L₀, hp₀, hB₀, hconv₀⟩ := ih q heq
      exact ⟨A₀, B₀, U₀, L₀, hp₀, hB₀, .trans hconv₀ hconv⟩
  | u0_type _ => intro _ h; exact absurd h (by simp [mkFst, u0])
  | fvar _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkFst])
  | pi_form _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkFst, mkPi])
  | lam_intro _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkFst, mkLam])
  | app _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkFst, mkApp])
  | sigma_form _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkFst, mkSigma])
  | pair_intro _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkFst, mkPair])
  | snd_elim _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkFst, mkSnd])
  | id_form _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkFst, mkId])
  | refl_intro _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkFst, mkRefl])

theorem fst_generation {Γ : PureCtx} {p C : Pattern}
    (ht : PureHasType Γ (mkFst p) C) :
    ∃ A B U, ∃ L : Finset String,
      PureHasType Γ p (mkSigma A B) ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv A C :=
  fst_generation_aux ht p rfl

private theorem snd_generation_aux {Γ : PureCtx} {p C : Pattern}
    (ht : PureHasType Γ p C) :
    ∀ q, p = mkSnd q →
    ∃ A B U, ∃ L : Finset String,
      PureHasType Γ q (mkSigma A B) ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv (openBVar 0 (mkFst q) B) C := by
  induction ht with
  | snd_elim _ L' p' A' B' U' hp hB _ _ =>
      intro q heq; simp only [mkSnd] at heq
      have hinj := apply_label_inj heq
      have hargs := hinj.2; simp at hargs; subst hargs
      exact ⟨A', B', U', L', hp, hB,
        .refl _ (typing_type_pure (.snd_elim _ L' p' A' B' U' hp hB))⟩
  | conv _ _ _ _ _ hconv ih =>
      intro q heq
      obtain ⟨A₀, B₀, U₀, L₀, hp₀, hB₀, hconv₀⟩ := ih q heq
      exact ⟨A₀, B₀, U₀, L₀, hp₀, hB₀, .trans hconv₀ hconv⟩
  | u0_type _ => intro _ h; exact absurd h (by simp [mkSnd, u0])
  | fvar _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkSnd])
  | pi_form _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkSnd, mkPi])
  | lam_intro _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkSnd, mkLam])
  | app _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkSnd, mkApp])
  | sigma_form _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkSnd, mkSigma])
  | pair_intro _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkSnd, mkPair])
  | fst_elim _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkSnd, mkFst])
  | id_form _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkSnd, mkId])
  | refl_intro _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkSnd, mkRefl])

theorem snd_generation {Γ : PureCtx} {p C : Pattern}
    (ht : PureHasType Γ (mkSnd p) C) :
    ∃ A B U, ∃ L : Finset String,
      PureHasType Γ p (mkSigma A B) ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv (openBVar 0 (mkFst p) B) C :=
  snd_generation_aux ht p rfl

private theorem refl_generation_aux {Γ : PureCtx} {p C : Pattern}
    (ht : PureHasType Γ p C) :
    ∀ a, p = mkRefl a →
    ∃ A, PureHasType Γ a A ∧ PureConv (mkId A a a) C := by
  induction ht with
  | refl_intro _ a' A' ha _ =>
      intro a heq; simp only [mkRefl] at heq
      have hinj := apply_label_inj heq
      have hargs := hinj.2; simp at hargs; subst hargs
      exact ⟨A', ha, .refl _ (typing_type_pure (.refl_intro _ a' A' ha))⟩
  | conv _ _ _ _ _ hconv ih =>
      intro a heq
      obtain ⟨A₀, ha₀, hconv₀⟩ := ih a heq
      exact ⟨A₀, ha₀, .trans hconv₀ hconv⟩
  | u0_type _ => intro _ h; exact absurd h (by simp [mkRefl, u0])
  | fvar _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkRefl])
  | pi_form _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkRefl, mkPi])
  | lam_intro _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkRefl, mkLam])
  | app _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkRefl, mkApp])
  | sigma_form _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkRefl, mkSigma])
  | pair_intro _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkRefl, mkPair])
  | fst_elim _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkRefl, mkFst])
  | snd_elim _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkRefl, mkSnd])
  | id_form _ _ _ _ _ _ _ _ _ _ _ => intro _ h; exact absurd h (by simp [mkRefl, mkId])

theorem refl_generation {Γ : PureCtx} {a C : Pattern}
    (ht : PureHasType Γ (mkRefl a) C) :
    ∃ A, PureHasType Γ a A ∧ PureConv (mkId A a a) C :=
  refl_generation_aux ht a rfl

/-! ## Conversion Helpers for Open -/

/-- If `PureConv a₁ a₂` and `B` has a cofinite typing witness under a binder,
    then `PureConv (openBVar 0 a₁ B) (openBVar 0 a₂ B)`. -/
theorem conv_openBVar_of_conv {Γ : PureCtx} {a₁ a₂ B A : Pattern}
    {L : Finset String} {U : Pattern}
    (hconv : PureConv a₁ a₂)
    (hlc₁ : lc_at 0 a₁ = true) (hlc₂ : lc_at 0 a₂ = true)
    (hB : ∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
    PureConv (openBVar 0 a₁ B) (openBVar 0 a₂ B) := by
  obtain ⟨z, hz⟩ := exists_fresh (L ∪ freeVarsFinset B)
  have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
  have hzB : z ∉ freeVarsFinset B := fun h => hz (Finset.mem_union_right _ h)
  have hfreshB := isFresh_of_not_mem_freeVarsFinset hzB
  have hrepl := pureConv_substFVar_repl (x := z) hconv hlc₁ hlc₂ (hB z hzL)
  rw [substFVar_intro B hfreshB 0, substFVar_intro B hfreshB 0] at hrepl
  exact hrepl

/-- If for all fresh `x ∉ L`, `PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)`,
    then `PureConv (openBVar 0 a B₁) (openBVar 0 a B₂)` for locally closed `a`. -/
theorem conv_openBVar_body {a B₁ B₂ : Pattern} {L : Finset String}
    (hlc : lc_at 0 a = true)
    (haPure : PureTmPattern a)
    (hBconv : ∀ x, x ∉ L → PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) :
    PureConv (openBVar 0 a B₁) (openBVar 0 a B₂) := by
  obtain ⟨z, hz⟩ := exists_fresh (L ∪ freeVarsFinset B₁ ∪ freeVarsFinset B₂)
  have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _
    (Finset.mem_union_left _ h))
  have hzB₁ : z ∉ freeVarsFinset B₁ := fun h => hz (Finset.mem_union_left _
    (Finset.mem_union_right _ h))
  have hzB₂ : z ∉ freeVarsFinset B₂ := fun h => hz (Finset.mem_union_right _ h)
  have hfreshB₁ := isFresh_of_not_mem_freeVarsFinset hzB₁
  have hfreshB₂ := isFresh_of_not_mem_freeVarsFinset hzB₂
  have hsubst := pureConv_substFVar (x := z) hlc haPure (hBconv z hzL)
  rw [substFVar_intro B₁ hfreshB₁ 0, substFVar_intro B₂ hfreshB₂ 0] at hsubst
  exact hsubst

/-! ## Subject Reduction -/

/-- **Subject Reduction** (Type Preservation) for MeTTa-Pure.

By induction on `PureReduces t t'`, using generation lemmas to decompose
the typing hypothesis. β-cases use generation + typing_subst + substFVar_intro.
Congruence cases use the IH plus conversion helpers. -/
theorem mettaPure_subject_reduction
    {Γ : PureCtx} {t t' A : Pattern}
    (ht : PureHasType Γ t A) (hr : PureReduces t t') :
    PureHasType Γ t' A := by
  induction hr generalizing Γ A with
  -- β-Pi: (λ.body) a ⟶ openBVar 0 a body
  | betaPi body a =>
      obtain ⟨A₀, B₀, U₀, L₀, hf, ha₀, hB₀, hConvType⟩ := app_generation ht
      obtain ⟨A₁, B₁, U₁, L₁, hA₁, hBody₁, hConvPi⟩ := lam_generation hf
      have hlcPi₀ := typing_type_lc hf  -- lc_at 0 (mkPi A₀ B₀)
      have hlcPi₁ :=
        (Mettapedia.Languages.MeTTa.Pure.Confluence.PureConv_preserves_lc_both hConvPi).2 hlcPi₀
      obtain ⟨hAconv, L₂, hBconv⟩ := pi_injectivity hConvPi hlcPi₁
      -- Transport argument to domain A₁
      have ha₁ : PureHasType Γ a A₁ := .conv _ _ _ _ ha₀ (.symm hAconv)
      -- Pick fresh z for substitution
      obtain ⟨z, hz⟩ := exists_fresh
        (L₁ ∪ L₂ ∪ freeVarsFinset body ∪ freeVarsFinset B₁ ∪
         ctxNamesFinset Γ ∪ freeVarsFinset A₁ ∪ ctxTypesFinset Γ)
      have hzL₁ : z ∉ L₁ := fun h => hz (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ h))))))
      have hzL₂ : z ∉ L₂ := fun h => hz (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ h))))))
      have hzBody : z ∉ freeVarsFinset body := fun h => hz (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_right _ h)))))
      have hzB₁ : z ∉ freeVarsFinset B₁ := fun h => hz (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ h))))
      have hzΓ : z ∉ ctxNamesFinset Γ := fun h => hz (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hzA₁ : z ∉ freeVarsFinset A₁ := fun h => hz (Finset.mem_union_left _
        (Finset.mem_union_right _ h))
      have hzΓT : z ∉ ctxTypesFinset Γ := fun h => hz (Finset.mem_union_right _ h)
      -- Body typing at fresh z
      have hBody_z := hBody₁ z hzL₁
      -- Substitution lemma
      have hlc_a := typing_lc ha₁
      have hsub := typing_subst ha₁ hlc_a
        (not_mem_ctxNames_of_not_mem_finset hzΓ)
        (isFresh_of_not_mem_freeVarsFinset hzA₁)
        (ctxFresh_of_not_mem_ctxTypeFVFinset hzΓT)
        hBody_z (Δ := []) rfl (by simp [ctxNames])
      -- Rewrite using substFVar_intro
      have hfreshBody := isFresh_of_not_mem_freeVarsFinset hzBody
      have hfreshB₁ := isFresh_of_not_mem_freeVarsFinset hzB₁
      rw [substFVar_intro body hfreshBody 0] at hsub
      rw [substFVar_intro B₁ hfreshB₁ 0] at hsub
      -- hsub : PureHasType Γ (openBVar 0 a body) (openBVar 0 a B₁)
      -- Transport type: openBVar 0 a B₁ ≡ openBVar 0 a B₀ (via hBconv)
      have hconvB : PureConv (openBVar 0 a B₁) (openBVar 0 a B₀) :=
        conv_openBVar_body hlc_a (typing_term_pure ha₁) hBconv
      exact .conv _ _ _ _ (.conv _ _ _ _ hsub hconvB) hConvType

  -- β-Σ-fst: fst (a, b) ⟶ a
  | betaSigmaFst a b =>
      obtain ⟨A₀, B₀, U₀, L₀, hp₀, hB₀, hConvA⟩ := fst_generation ht
      have hlcSigma₀ := typing_type_lc hp₀  -- lc_at 0 (mkSigma A₀ B₀)
      obtain ⟨A₁, B₁, U₁, L₁, ha₁, _, _, hConvSigma⟩ := pair_generation hp₀
      have hlcSigma₁ :=
        (Mettapedia.Languages.MeTTa.Pure.Confluence.PureConv_preserves_lc_both hConvSigma).2 hlcSigma₀
      obtain ⟨hAconv₁₀, _⟩ := sigma_injectivity hConvSigma hlcSigma₁
      exact .conv _ _ _ _ ha₁ (.trans hAconv₁₀ hConvA)

  -- β-Σ-snd: snd (a, b) ⟶ b
  | betaSigmaSnd a b =>
      obtain ⟨A₀, B₀, U₀, L₀, hp₀, hB₀, hConvSnd⟩ := snd_generation ht
      have hlcSigma₀ := typing_type_lc hp₀  -- lc_at 0 (mkSigma A₀ B₀)
      obtain ⟨A₁, B₁, U₁, L₁, ha₁, hb₁, hB₁, hConvSigma⟩ := pair_generation hp₀
      have hlcSigma₁ :=
        (Mettapedia.Languages.MeTTa.Pure.Confluence.PureConv_preserves_lc_both hConvSigma).2 hlcSigma₀
      obtain ⟨hAconv, L₂, hBconv⟩ := sigma_injectivity hConvSigma hlcSigma₁
      -- hb₁ : Γ ⊢ b : openBVar 0 a B₁
      -- Need: Γ ⊢ b : A  (where A is the overall type)
      -- Chain: openBVar 0 a B₁ ≡ openBVar 0 a B₀ ≡ openBVar 0 (mkFst (mkPair a b)) B₀ ≡ A
      have hlc_a := typing_lc ha₁
      have hconv₁ : PureConv (openBVar 0 a B₁) (openBVar 0 a B₀) :=
        conv_openBVar_body hlc_a (typing_term_pure ha₁) hBconv
      have hlc_b := typing_lc hb₁
      have hlc_fstpair : lc_at 0 (mkFst (mkPair a b)) = true := by
        simp [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true]
        exact ⟨hlc_a, hlc_b⟩
      have hconv₂ : PureConv (openBVar 0 a B₀) (openBVar 0 (mkFst (mkPair a b)) B₀) :=
        conv_openBVar_of_conv
          (.symm (.betaSigmaFst a b (typing_term_pure ha₁) (typing_term_pure hb₁) hlc_a hlc_b))
          hlc_a hlc_fstpair hB₀
      exact .conv _ _ _ _ hb₁ (.trans hconv₁ (.trans hconv₂ hConvSnd))

  -- Congruence: Pi domain
  | congPiDom hred ih =>
      obtain ⟨U, L, hA, hB, hConvU⟩ := pi_generation ht
      have hA' := ih hA
      have hconvA : PureConv _ _ := PureReduces_implies_PureConv hred (typing_lc hA) (typing_term_pure hA)
      exact .conv _ _ _ _ (.pi_form _ L _ _ U hA'
        (fun z hz => context_conv_head hconvA (hB z hz))) hConvU

  -- Congruence: Pi codomain (under binder)
  | congPiCod L' A₀ B₀ B₀' hred ih =>
      obtain ⟨U, L, hA, hB, hConvU⟩ := pi_generation ht
      exact .conv _ _ _ _ (.pi_form _ (L ∪ L') A₀ _ U hA (fun z hz => by
        have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
        have hzL' : z ∉ L' := fun h => hz (Finset.mem_union_right _ h)
        exact ih z hzL' (hB z hzL))) hConvU

  -- Congruence: Sigma domain
  | congSigmaDom hred ih =>
      obtain ⟨U, L, hA, hB, hConvU⟩ := sigma_generation ht
      have hA' := ih hA
      have hconvA : PureConv _ _ := PureReduces_implies_PureConv hred (typing_lc hA) (typing_term_pure hA)
      exact .conv _ _ _ _ (.sigma_form _ L _ _ U hA'
        (fun z hz => context_conv_head hconvA (hB z hz))) hConvU

  -- Congruence: Sigma codomain (under binder)
  | congSigmaCod L' A₀ B₀ B₀' hred ih =>
      obtain ⟨U, L, hA, hB, hConvU⟩ := sigma_generation ht
      exact .conv _ _ _ _ (.sigma_form _ (L ∪ L') A₀ _ U hA (fun z hz => by
        have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
        have hzL' : z ∉ L' := fun h => hz (Finset.mem_union_right _ h)
        exact ih z hzL' (hB z hzL))) hConvU

  -- Congruence: Id type
  | congIdType hred ih =>
      obtain ⟨U, hA, ha, hb, hConvU⟩ := id_generation ht
      have hA' := ih hA
      have hconv_aa : PureConv _ _ := PureReduces_implies_PureConv hred (typing_lc hA) (typing_term_pure hA)
      exact .conv _ _ _ _ (.id_form _ _ _ _ U hA'
        (.conv _ _ _ _ ha hconv_aa)
        (.conv _ _ _ _ hb hconv_aa)) hConvU

  -- Congruence: Id left
  | congIdLeft hred ih =>
      obtain ⟨U, hA, ha, hb, hConvU⟩ := id_generation ht
      exact .conv _ _ _ _ (.id_form _ _ _ _ U hA (ih ha) hb) hConvU

  -- Congruence: Id right
  | congIdRight hred ih =>
      obtain ⟨U, hA, ha, hb, hConvU⟩ := id_generation ht
      exact .conv _ _ _ _ (.id_form _ _ _ _ U hA ha (ih hb)) hConvU

  -- Congruence: Lam (under binder)
  | congLam L' body body' hred ih =>
      obtain ⟨A₀, B₀, U₀, L₀, hA₀, hBody₀, hConvPi⟩ := lam_generation ht
      exact .conv _ _ _ _ (.lam_intro _ (L₀ ∪ L') A₀ _ B₀ U₀ hA₀ (fun z hz => by
        have hzL₀ : z ∉ L₀ := fun h => hz (Finset.mem_union_left _ h)
        have hzL' : z ∉ L' := fun h => hz (Finset.mem_union_right _ h)
        exact ih z hzL' (hBody₀ z hzL₀))) hConvPi

  -- Congruence: App function
  | congAppFun hred ih =>
      obtain ⟨A₀, B₀, U₀, L₀, hf, ha, hB, hConvType⟩ := app_generation ht
      exact .conv _ _ _ _ (.app _ L₀ _ _ A₀ B₀ U₀ (ih hf) ha hB) hConvType

  -- Congruence: App argument
  | congAppArg hred ih =>
      obtain ⟨A₀, B₀, U₀, L₀, hf, ha, hB, hConvType⟩ := app_generation ht
      have ha' := ih ha
      have hconv_aa : PureConv _ _ := PureReduces_implies_PureConv hred (typing_lc ha) (typing_term_pure ha)
      have hlc_a := typing_lc ha
      have hlc_a' := typing_lc ha'
      -- openBVar 0 a' B₀ ≡ openBVar 0 a B₀ via conv_openBVar_of_conv
      have hconvOpen := conv_openBVar_of_conv (.symm hconv_aa) hlc_a' hlc_a hB
      exact .conv _ _ _ _
        (.conv _ _ _ _ (.app _ L₀ _ _ A₀ B₀ U₀ hf ha' hB) hconvOpen)
        hConvType

  -- Congruence: Pair first
  | congPairFst hred ih =>
      obtain ⟨A₀, B₀, U₀, L₀, ha, hb, hB₀, hConvSigma⟩ := pair_generation ht
      have ha' := ih ha
      have hconv_aa : PureConv _ _ := PureReduces_implies_PureConv hred (typing_lc ha) (typing_term_pure ha)
      have hlc_a := typing_lc ha
      have hlc_a' := typing_lc ha'
      -- hconvOpen : PureConv (openBVar 0 a' B₀) (openBVar 0 a B₀)
      have hconvOpen := conv_openBVar_of_conv (.symm hconv_aa) hlc_a' hlc_a hB₀
      -- hb : Γ ⊢ b : openBVar 0 a B₀, need openBVar 0 a' B₀
      -- hconvOpen goes a'→a, so .symm goes a→a'
      exact .conv _ _ _ _
        (.pair_intro _ L₀ _ _ A₀ B₀ U₀ ha' (.conv _ _ _ _ hb (.symm hconvOpen)) hB₀)
        hConvSigma

  -- Congruence: Pair second
  | congPairSnd hred ih =>
      obtain ⟨A₀, B₀, U₀, L₀, ha, hb, hB₀, hConvSigma⟩ := pair_generation ht
      exact .conv _ _ _ _ (.pair_intro _ L₀ _ _ A₀ B₀ U₀ ha (ih hb) hB₀) hConvSigma

  -- Congruence: Fst
  | congFst hred ih =>
      obtain ⟨A₀, B₀, U₀, L₀, hp, hB₀, hConvA⟩ := fst_generation ht
      exact .conv _ _ _ _ (.fst_elim _ L₀ _ A₀ B₀ U₀ (ih hp) hB₀) hConvA

  -- Congruence: Snd
  | congSnd hred ih =>
      obtain ⟨A₀, B₀, U₀, L₀, hp, hB₀, hConvSnd⟩ := snd_generation ht
      have hp' := ih hp
      have hconv_pp : PureConv _ _ := PureReduces_implies_PureConv hred (typing_lc hp) (typing_term_pure hp)
      have hlc_fp := typing_lc (.fst_elim _ L₀ _ A₀ B₀ U₀ hp hB₀)
      have hlc_fp' := typing_lc (.fst_elim _ L₀ _ A₀ B₀ U₀ hp' hB₀)
      have hconvFst : PureConv (mkFst _) (mkFst _) := .congFst hconv_pp
      have hconvOpen := conv_openBVar_of_conv (.symm hconvFst) hlc_fp' hlc_fp hB₀
      exact .conv _ _ _ _
        (.conv _ _ _ _ (.snd_elim _ L₀ _ A₀ B₀ U₀ hp' hB₀) hconvOpen)
        hConvSnd

  -- Congruence: Refl
  | congRefl hred ih =>
      obtain ⟨A₀, ha, hConvId⟩ := refl_generation ht
      have ha' := ih ha
      have hconv_aa : PureConv _ _ := PureReduces_implies_PureConv hred (typing_lc ha) (typing_term_pure ha)
      exact .conv _ _ _ _
        (.refl_intro _ _ A₀ ha')
        (.trans (.congId (.refl _ (typing_type_pure ha)) (.symm hconv_aa) (.symm hconv_aa)) hConvId)

/-! ## TypedLangDef Assembly -/

structure TypedLangDef where
  lang : LanguageDef
  Ctx : Type
  hasType : Ctx → Pattern → Pattern → Prop
  reduces : Pattern → Pattern → Prop
  subject_reduction : ∀ {Γ t t' A},
    hasType Γ t A → reduces t t' → hasType Γ t' A

end Mettapedia.Languages.MeTTa.Pure.SubjectReduction
