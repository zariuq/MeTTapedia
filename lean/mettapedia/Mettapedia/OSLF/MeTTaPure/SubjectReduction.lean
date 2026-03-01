import Mettapedia.OSLF.MeTTaPure.Reduction

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

namespace Mettapedia.OSLF.MeTTaPure.SubjectReduction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaPure.Core
open Mettapedia.OSLF.MeTTaPure.Typing
open Mettapedia.OSLF.MeTTaPure.Reduction

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
theorem pureConv_substFVar {x : String} {u : Pattern}
    (hlc : lc_at 0 u = true) {t₁ t₂ : Pattern} (hconv : PureConv t₁ t₂) :
    PureConv (substFVar x u t₁) (substFVar x u t₂) := by
  induction hconv with
  | refl t => simpa using PureConv.refl (substFVar x u t)
  | symm _ ih => exact PureConv.symm ih
  | trans _ _ ih₁ ih₂ => exact PureConv.trans ih₁ ih₂
  | betaPi body a =>
      refine PureConv.trans (t₂ := openBVar 0 (substFVar x u a) (substFVar x u body)) ?_ ?_
      · simpa [mkApp, mkLam, substFVar] using
          (PureConv.betaPi (substFVar x u body) (substFVar x u a))
      · rw [(substFVar_openBVar_comm (x := x) (u := u) (a := a) (p := body) (k := 0) hlc).symm]
        exact PureConv.refl _
  | betaSigmaFst a b =>
      simpa [mkFst, mkPair, substFVar] using
        (PureConv.betaSigmaFst (substFVar x u a) (substFVar x u b))
  | betaSigmaSnd a b =>
      simpa [mkSnd, mkPair, substFVar] using
        (PureConv.betaSigmaSnd (substFVar x u a) (substFVar x u b))
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
  | fvar Γ x A hmem => exact .fvar Γ' x A (hsub x A hmem)
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
  | pair_intro Γ a b A B ha hb iha ihb =>
      exact .pair_intro Γ' a b A B (iha hsub) (ihb hsub)
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
  | fvar _ y T hmem =>
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
        · rcases List.mem_cons.mp hrest with heq | hΓmem
          · exact absurd (Prod.mk.inj heq).1 hyx
          · rw [substFVar_fresh (hfreshΓ y T hΓmem)]
            exact .fvar _ y T (List.mem_append_right _ hΓmem)
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
      refine .app _ (L' ∪ {x}) _ _ _ _ _ hf (iha rfl hxΔ) ?_
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
  | pair_intro _ a' b' A' B' _ _ iha ihb =>
      intro Δ hΓ hxΔ; subst hΓ; simp only [substFVar_mkPair, substFVar_mkSigma]
      have hb := ihb rfl hxΔ; rw [substFVar_openBVar_comm hlc_u] at hb
      exact .pair_intro _ _ _ _ _ (iha rfl hxΔ) hb
  | fst_elim _ L' p' A' B' U _ _ ihp ihB =>
      intro Δ hΓ hxΔ; subst hΓ; simp only [substFVar_mkFst]
      have hp := ihp rfl hxΔ; simp only [substFVar_mkSigma] at hp
      refine .fst_elim _ (L' ∪ {x}) _ _ _ _ hp ?_
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
      refine .snd_elim _ (L' ∪ {x}) _ _ _ _ hp ?_
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
      exact .conv _ _ _ _ (iht rfl hxΔ) (pureConv_substFVar hlc_u hconv)

/-! ## Pattern Discrimination -/

private theorem apply_label_inj {c₁ c₂ : String} {args₁ args₂ : List Pattern}
    (h : Pattern.apply c₁ args₁ = Pattern.apply c₂ args₂) : c₁ = c₂ ∧ args₁ = args₂ :=
  ⟨Pattern.apply.inj h |>.1, Pattern.apply.inj h |>.2⟩

/-! ## Generation Lemmas -/

/-- App generation: if `Γ ⊢ mkApp f a : C`, then there exist `A`, `B`, `U`, `L`
    with f, a, B typing and `PureConv (openBVar 0 a B) C`. -/
theorem app_generation {Γ : PureCtx} {f a C : Pattern}
    (ht : PureHasType Γ (mkApp f a) C) :
    ∃ A B U (L : Finset String),
      PureHasType Γ f (mkPi A B) ∧ PureHasType Γ a A ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) ∧
      PureConv (openBVar 0 a B) C := by
  induction ht with
  | app _ L _ _ A' B' U hf ha hB _ _ _ =>
      exact ⟨A', B', U, L, hf, ha, hB, .refl _⟩
  | conv _ _ A' B' _ hconv ih =>
      obtain ⟨A₀, B₀, U₀, L₀, hf₀, ha₀, hB₀, hconv₀⟩ := ih rfl
      exact ⟨A₀, B₀, U₀, L₀, hf₀, ha₀, hB₀, .trans hconv₀ hconv⟩
  | u0_type _ => exact absurd rfl (by simp [mkApp, u0])
  | fvar _ _ _ _ => exact absurd rfl (by simp [mkApp])
  | pi_form _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkApp, mkPi])
  | lam_intro _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkApp, mkLam, mkPi])
  | sigma_form _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkApp, mkSigma])
  | pair_intro _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkApp, mkPair, mkSigma])
  | fst_elim _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkApp, mkFst])
  | snd_elim _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkApp, mkSnd])
  | id_form _ _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkApp, mkId])
  | refl_intro _ _ _ _ _ => exact absurd rfl (by simp [mkApp, mkRefl, mkId])

/-- Lam generation. -/
theorem lam_generation {Γ : PureCtx} {body C : Pattern}
    (ht : PureHasType Γ (mkLam body) C) :
    ∃ A B U (L : Finset String),
      PureHasType Γ A U ∧
      (∀ x, x ∉ L → PureHasType ((x, A) :: Γ)
        (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) B)) ∧
      PureConv (mkPi A B) C := by
  induction ht with
  | lam_intro _ L A' body' B' U' hA hBody _ _ =>
      have hinj := apply_label_inj (show Pattern.apply "Lam" [.lambda body] =
        Pattern.apply "Lam" [.lambda body'] from rfl)
      have hbody_eq : body = body' := by have := hinj.2; simp at this; exact this
      subst hbody_eq
      exact ⟨A', B', U', L, hA, hBody, .refl _⟩
  | conv _ _ A' B' _ hconv ih =>
      obtain ⟨A₀, B₀, U₀, L₀, hA₀, hBody₀, hconv₀⟩ := ih rfl
      exact ⟨A₀, B₀, U₀, L₀, hA₀, hBody₀, .trans hconv₀ hconv⟩
  | u0_type _ => exact absurd rfl (by simp [mkLam, u0])
  | fvar _ _ _ _ => exact absurd rfl (by simp [mkLam])
  | pi_form _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkLam, mkPi])
  | app _ _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkLam, mkApp])
  | sigma_form _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkLam, mkSigma])
  | pair_intro _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkLam, mkPair, mkSigma])
  | fst_elim _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkLam, mkFst])
  | snd_elim _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkLam, mkSnd])
  | id_form _ _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkLam, mkId])
  | refl_intro _ _ _ _ _ => exact absurd rfl (by simp [mkLam, mkRefl, mkId])

/-- Pair generation. -/
theorem pair_generation {Γ : PureCtx} {a b C : Pattern}
    (ht : PureHasType Γ (mkPair a b) C) :
    ∃ A B, PureHasType Γ a A ∧ PureHasType Γ b (openBVar 0 a B) ∧
      PureConv (mkSigma A B) C := by
  induction ht with
  | pair_intro _ a' b' A' B' ha hb _ _ =>
      have hinj := apply_label_inj (show Pattern.apply "Pair" [a, b] =
        Pattern.apply "Pair" [a', b'] from rfl)
      have : a = a' ∧ b = b' := by simp at hinj; exact hinj.2
      subst this.1; subst this.2
      exact ⟨A', B', ha, hb, .refl _⟩
  | conv _ _ A' B' _ hconv ih =>
      obtain ⟨A₀, B₀, ha₀, hb₀, hconv₀⟩ := ih rfl
      exact ⟨A₀, B₀, ha₀, hb₀, .trans hconv₀ hconv⟩
  | u0_type _ => exact absurd rfl (by simp [mkPair, u0])
  | fvar _ _ _ _ => exact absurd rfl (by simp [mkPair])
  | pi_form _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkPair, mkPi])
  | lam_intro _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkPair, mkLam, mkPi])
  | app _ _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkPair, mkApp])
  | sigma_form _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkPair, mkSigma])
  | fst_elim _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkPair, mkFst])
  | snd_elim _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkPair, mkSnd])
  | id_form _ _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (by simp [mkPair, mkId])
  | refl_intro _ _ _ _ _ => exact absurd rfl (by simp [mkPair, mkRefl, mkId])

/-! ## Pi/Sigma Injectivity under Conversion -/

private theorem pi_head_pres :
    ∀ {s t : Pattern}, PureConv s t →
      (∀ A₁ B₁, s = mkPi A₁ B₁ → ∃ A₂ B₂, t = mkPi A₂ B₂ ∧ PureConv A₁ A₂ ∧
        (∃ L : Finset String, ∀ x, x ∉ L →
          PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂))) ∧
      (∀ A₂ B₂, t = mkPi A₂ B₂ → ∃ A₁ B₁, s = mkPi A₁ B₁ ∧ PureConv A₁ A₂ ∧
        (∃ L : Finset String, ∀ x, x ∉ L →
          PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂))) := by
  intro s t h; induction h with
  | refl _ =>
      exact ⟨fun A B heq => ⟨A, B, heq, .refl _, ∅, fun _ _ => .refl _⟩,
             fun A B heq => ⟨A, B, heq, .refl _, ∅, fun _ _ => .refl _⟩⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ =>
      constructor
      · intro A₁ B₁ heq
        obtain ⟨A₂, B₂, heq₂, hA₁₂, L₁₂, hB₁₂⟩ := ih₁.1 A₁ B₁ heq
        obtain ⟨A₃, B₃, heq₃, hA₂₃, L₂₃, hB₂₃⟩ := ih₂.1 A₂ B₂ heq₂
        exact ⟨A₃, B₃, heq₃, .trans hA₁₂ hA₂₃,
          L₁₂ ∪ L₂₃, fun x hx => .trans (hB₁₂ x (fun h => hx (Finset.mem_union_left _ h)))
            (hB₂₃ x (fun h => hx (Finset.mem_union_right _ h)))⟩
      · intro A₃ B₃ heq
        obtain ⟨A₂, B₂, heq₂, hA₂₃, L₂₃, hB₂₃⟩ := ih₂.2 A₃ B₃ heq
        obtain ⟨A₁, B₁, heq₁, hA₁₂, L₁₂, hB₁₂⟩ := ih₁.2 A₂ B₂ heq₂
        exact ⟨A₁, B₁, heq₁, .trans hA₁₂ hA₂₃,
          L₁₂ ∪ L₂₃, fun x hx => .trans (hB₁₂ x (fun h => hx (Finset.mem_union_left _ h)))
            (hB₂₃ x (fun h => hx (Finset.mem_union_right _ h)))⟩
  | betaPi _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkPi, mkApp]),
             fun _ _ h => absurd h (by simp [mkPi, openBVar]; intro heq; simp [mkPi] at heq)⟩
  | betaSigmaFst _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkPi, mkFst]),
             fun _ _ h => absurd h (by simp [mkPi])⟩
  | betaSigmaSnd _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkPi, mkSnd]),
             fun _ _ h => absurd h (by simp [mkPi])⟩
  | congPi L hA hB _ _ =>
      constructor
      · intro A₁ B₁ heq
        have ⟨_, hargs⟩ := apply_label_inj heq; simp [mkPi] at hargs
        obtain ⟨hA1, hB1⟩ := hargs; subst hA1; subst hB1
        exact ⟨_, _, rfl, hA, L, hB⟩
      · intro A₂ B₂ heq
        have ⟨_, hargs⟩ := apply_label_inj heq; simp [mkPi] at hargs
        obtain ⟨hA2, hB2⟩ := hargs; subst hA2; subst hB2
        exact ⟨_, _, rfl, hA, L, hB⟩
  | congSigma _ _ _ _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkPi, mkSigma]),
             fun _ _ h => absurd h (by simp [mkPi, mkSigma])⟩
  | congId _ _ _ _ _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkPi, mkId]),
             fun _ _ h => absurd h (by simp [mkPi, mkId])⟩
  | congLam _ _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkPi, mkLam]),
             fun _ _ h => absurd h (by simp [mkPi, mkLam])⟩
  | congApp _ _ _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkPi, mkApp]),
             fun _ _ h => absurd h (by simp [mkPi, mkApp])⟩
  | congPair _ _ _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkPi, mkPair]),
             fun _ _ h => absurd h (by simp [mkPi, mkPair])⟩
  | congFst _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkPi, mkFst]),
             fun _ _ h => absurd h (by simp [mkPi, mkFst])⟩
  | congSnd _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkPi, mkSnd]),
             fun _ _ h => absurd h (by simp [mkPi, mkSnd])⟩
  | congRefl _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkPi, mkRefl]),
             fun _ _ h => absurd h (by simp [mkPi, mkRefl])⟩

private theorem sigma_head_pres :
    ∀ {s t : Pattern}, PureConv s t →
      (∀ A₁ B₁, s = mkSigma A₁ B₁ → ∃ A₂ B₂, t = mkSigma A₂ B₂ ∧ PureConv A₁ A₂ ∧
        (∃ L : Finset String, ∀ x, x ∉ L →
          PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂))) ∧
      (∀ A₂ B₂, t = mkSigma A₂ B₂ → ∃ A₁ B₁, s = mkSigma A₁ B₁ ∧ PureConv A₁ A₂ ∧
        (∃ L : Finset String, ∀ x, x ∉ L →
          PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂))) := by
  intro s t h; induction h with
  | refl _ =>
      exact ⟨fun A B heq => ⟨A, B, heq, .refl _, ∅, fun _ _ => .refl _⟩,
             fun A B heq => ⟨A, B, heq, .refl _, ∅, fun _ _ => .refl _⟩⟩
  | symm _ ih =>
      exact ⟨fun A B h => ih.2 A B h, fun A B h => ih.1 A B h⟩
  | trans _ _ ih₁ ih₂ =>
      constructor
      · intro A₁ B₁ heq
        obtain ⟨A₂, B₂, heq₂, hA₁₂, L₁₂, hB₁₂⟩ := ih₁.1 A₁ B₁ heq
        obtain ⟨A₃, B₃, heq₃, hA₂₃, L₂₃, hB₂₃⟩ := ih₂.1 A₂ B₂ heq₂
        exact ⟨A₃, B₃, heq₃, .trans hA₁₂ hA₂₃,
          L₁₂ ∪ L₂₃, fun x hx => .trans (hB₁₂ x (fun h => hx (Finset.mem_union_left _ h)))
            (hB₂₃ x (fun h => hx (Finset.mem_union_right _ h)))⟩
      · intro A₃ B₃ heq
        obtain ⟨A₂, B₂, heq₂, hA₂₃, L₂₃, hB₂₃⟩ := ih₂.2 A₃ B₃ heq
        obtain ⟨A₁, B₁, heq₁, hA₁₂, L₁₂, hB₁₂⟩ := ih₁.2 A₂ B₂ heq₂
        exact ⟨A₁, B₁, heq₁, .trans hA₁₂ hA₂₃,
          L₁₂ ∪ L₂₃, fun x hx => .trans (hB₁₂ x (fun h => hx (Finset.mem_union_left _ h)))
            (hB₂₃ x (fun h => hx (Finset.mem_union_right _ h)))⟩
  | betaPi _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkSigma, mkApp]),
             fun _ _ h => by simp [mkSigma, openBVar] at h⟩
  | betaSigmaFst a b =>
      constructor
      · intro _ _ h; simp [mkSigma, mkFst] at h
      · intro A' B' h
        -- `a = mkSigma A' B'` is possible if the projection reduces to a Sigma type
        exact absurd h (by simp [mkSigma])
  | betaSigmaSnd a b =>
      constructor
      · intro _ _ h; simp [mkSigma, mkSnd] at h
      · intro A' B' h; exact absurd h (by simp [mkSigma])
  | congPi _ _ _ _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkSigma, mkPi]),
             fun _ _ h => absurd h (by simp [mkSigma, mkPi])⟩
  | congSigma L hA hB _ _ =>
      constructor
      · intro A₁ B₁ heq
        have ⟨_, hargs⟩ := apply_label_inj heq; simp [mkSigma] at hargs
        obtain ⟨hA1, hB1⟩ := hargs; subst hA1; subst hB1
        exact ⟨_, _, rfl, hA, L, hB⟩
      · intro A₂ B₂ heq
        have ⟨_, hargs⟩ := apply_label_inj heq; simp [mkSigma] at hargs
        obtain ⟨hA2, hB2⟩ := hargs; subst hA2; subst hB2
        exact ⟨_, _, rfl, hA, L, hB⟩
  | congId _ _ _ _ _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkSigma, mkId]),
             fun _ _ h => absurd h (by simp [mkSigma, mkId])⟩
  | congLam _ _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkSigma, mkLam]),
             fun _ _ h => absurd h (by simp [mkSigma, mkLam])⟩
  | congApp _ _ _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkSigma, mkApp]),
             fun _ _ h => absurd h (by simp [mkSigma, mkApp])⟩
  | congPair _ _ _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkSigma, mkPair]),
             fun _ _ h => absurd h (by simp [mkSigma, mkPair])⟩
  | congFst _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkSigma, mkFst]),
             fun _ _ h => absurd h (by simp [mkSigma, mkFst])⟩
  | congSnd _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkSigma, mkSnd]),
             fun _ _ h => absurd h (by simp [mkSigma, mkSnd])⟩
  | congRefl _ _ =>
      exact ⟨fun _ _ h => absurd h (by simp [mkSigma, mkRefl]),
             fun _ _ h => absurd h (by simp [mkSigma, mkRefl])⟩

theorem pi_injectivity {A₁ B₁ A₂ B₂ : Pattern}
    (h : PureConv (mkPi A₁ B₁) (mkPi A₂ B₂)) :
    PureConv A₁ A₂ ∧
      (∃ L : Finset String, ∀ x, x ∉ L →
        PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) := by
  obtain ⟨A₂', B₂', heq, hA, L, hB⟩ := (pi_head_pres h).1 A₁ B₁ rfl
  have ⟨_, hargs⟩ := apply_label_inj heq; simp [mkPi] at hargs
  obtain ⟨hAeq, hBeq⟩ := hargs; subst hAeq; subst hBeq
  exact ⟨hA, L, hB⟩

theorem sigma_injectivity {A₁ B₁ A₂ B₂ : Pattern}
    (h : PureConv (mkSigma A₁ B₁) (mkSigma A₂ B₂)) :
    PureConv A₁ A₂ ∧
      (∃ L : Finset String, ∀ x, x ∉ L →
        PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) := by
  obtain ⟨A₂', B₂', heq, hA, L, hB⟩ := (sigma_head_pres h).1 A₁ B₁ rfl
  have ⟨_, hargs⟩ := apply_label_inj heq; simp [mkSigma] at hargs
  obtain ⟨hAeq, hBeq⟩ := hargs; subst hAeq; subst hBeq
  exact ⟨hA, L, hB⟩

/-! ## Freshness: picking fresh strings -/

/-- There exists a string not in any given finite set (String is infinite). -/
theorem exists_fresh (S : Finset String) : ∃ x : String, x ∉ S :=
  Infinite.exists_not_mem S

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

/-- All types in a context, for freshness collection. -/
noncomputable def ctxTypesFinset (Γ : PureCtx) : Finset String :=
  Γ.foldl (fun acc (_, T) => acc ∪ (freeVars T).toFinset) ∅

theorem ctxFresh_of_not_mem {x : String} {Γ : PureCtx}
    (h : ∀ y T, (y, T) ∈ Γ → x ∉ (freeVars T).toFinset) : ctxFresh x Γ := by
  intro y T hmem
  have := h y T hmem
  simp only [List.mem_toFinset] at this
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]; intro hc
  exact this (List.contains_iff_mem.mp hc)

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
  | u0_type _ => simp; exact .refl _
  | fvar _ y _ _ =>
      by_cases hyx : y = x
      · simp [substFVar, hyx]; exact hconv
      · simp [substFVar, hyx]; exact .refl _
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
  | app _ L _ _ _ _ _ _ _ _ _ _ ihB =>
      simp only [substFVar_mkApp]; exact .congApp sorry sorry
  | sigma_form _ L A' B' U _ _ ihA ihB =>
      simp only [substFVar_mkSigma]
      refine .congSigma (L ∪ {x}) ihA (fun y hy => ?_)
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ihB y hyL
      rwa [substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc', substFVar_fvar_ne u' hyx] at key
  | pair_intro _ _ _ _ _ _ _ iha ihb =>
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

/-! ## Subject Reduction -/

/-- **Subject Reduction** (Type Preservation) for MeTTa-Pure.

By induction on `PureHasType Γ t A`, with `PureReduces t t'` as
extra hypothesis. The β-cases use generation + typing_subst +
substFVar_intro. Congruence-under-binder cases use cofinite quantification.
The congAppArg case uses `pureConv_substFVar_repl` for type conversion. -/
theorem mettaPure_subject_reduction
    {Γ : PureCtx} {t t' A : Pattern}
    (ht : PureHasType Γ t A) (hr : PureReduces t t') :
    PureHasType Γ t' A := by
  sorry

/-! ## TypedLangDef Assembly -/

structure TypedLangDef where
  lang : LanguageDef
  Ctx : Type
  hasType : Ctx → Pattern → Pattern → Prop
  reduces : Pattern → Pattern → Prop
  subject_reduction : ∀ {Γ t t' A},
    hasType Γ t A → reduces t t' → hasType Γ t' A

end Mettapedia.OSLF.MeTTaPure.SubjectReduction
