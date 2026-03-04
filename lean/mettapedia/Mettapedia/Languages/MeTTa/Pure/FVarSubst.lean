import Mettapedia.Languages.MeTTa.Pure.Reduction

/-!
# Free Variable Substitution Infrastructure

Defines `substFVar` (replace `.fvar x` with a term `u`) and proves its key
properties:
- Interaction with `mk*` constructors (`@[simp]` lemmas)
- Identity on fresh variables (`substFVar_fresh`)
- Interaction with `openBVar` (`substFVar_intro`, `substFVar_openBVar_comm`)
- Equivariance of `PureReduces` / `PureReducesStar` under `substFVar`

These are shared between `Confluence.lean` and `SubjectReduction.lean`.
-/

namespace Mettapedia.Languages.MeTTa.Pure.FVarSubst

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType)
open Mettapedia.OSLF.MeTTaIL.Substitution (openBVar lc_at lc_at_list openBVar_lc_at lc_at_mono lc_at_list_mem freeVars isFresh lc_at_openBVar_result)
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.Typing (PureConv)
open Mettapedia.Languages.MeTTa.Pure.Reduction

/-! ## FVar Substitution

Replace `.fvar x` with `u` throughout a pattern. -/

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

theorem list_map_eq_self {f : Pattern → Pattern} {l : List Pattern}
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons]; congr 1
    · exact h a List.mem_cons_self
    · exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-! ## Freshness propagation helpers -/

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
  simp only [isFresh, freeVars] at hfresh ⊢; exact hfresh

theorem isFresh_of_multiLambda {x : String} {n : Nat} {body : Pattern}
    (hfresh : isFresh x (.multiLambda n body) = true) : isFresh x body = true := by
  simp only [isFresh, freeVars] at hfresh ⊢; exact hfresh

theorem isFresh_of_subst_body {x : String} {body repl : Pattern}
    (hfresh : isFresh x (.subst body repl) = true) : isFresh x body = true := by
  simp only [isFresh, freeVars, List.contains_append, Bool.not_eq_true',
             Bool.or_eq_false_iff] at hfresh ⊢; exact hfresh.1

theorem isFresh_of_subst_repl {x : String} {body repl : Pattern}
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

/-! ## Commutation -/

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

/-! ## PureReduces equivariance under substFVar

The key lemma: single-step reduction is preserved by free variable
substitution (with a locally-closed replacement term). -/

/-- `PureReduces` is equivariant under `substFVar`. -/
theorem pureReduces_substFVar {x : String} {u : Pattern}
    (hlc : lc_at 0 u = true) {p q : Pattern} (h : PureReduces p q) :
    PureReduces (substFVar x u p) (substFVar x u q) := by
  induction h with
  | betaPi body a =>
      simp only [substFVar_mkApp, substFVar_mkLam]
      rw [substFVar_openBVar_comm hlc]
      exact .betaPi (substFVar x u body) (substFVar x u a)
  | betaSigmaFst a b =>
      simp only [substFVar_mkFst, substFVar_mkPair]
      exact .betaSigmaFst (substFVar x u a) (substFVar x u b)
  | betaSigmaSnd a b =>
      simp only [substFVar_mkSnd, substFVar_mkPair]
      exact .betaSigmaSnd (substFVar x u a) (substFVar x u b)
  | congPiDom hA ih =>
      simp only [substFVar_mkPi]
      exact .congPiDom ih
  | congPiCod L A Bc Bc' hBc ih =>
      simp only [substFVar_mkPi]
      refine .congPiCod (L ∪ {x}) (substFVar x u A) (substFVar x u Bc) (substFVar x u Bc')
        (fun y hy => ?_)
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ih y hyL
      rwa [substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx] at key
  | congSigmaDom hA ih =>
      simp only [substFVar_mkSigma]
      exact .congSigmaDom ih
  | congSigmaCod L A Bc Bc' hBc ih =>
      simp only [substFVar_mkSigma]
      refine .congSigmaCod (L ∪ {x}) (substFVar x u A) (substFVar x u Bc) (substFVar x u Bc')
        (fun y hy => ?_)
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ih y hyL
      rwa [substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx] at key
  | congIdType hA ih =>
      simp only [substFVar_mkId]; exact .congIdType ih
  | congIdLeft ha ih =>
      simp only [substFVar_mkId]; exact .congIdLeft ih
  | congIdRight hb ih =>
      simp only [substFVar_mkId]; exact .congIdRight ih
  | congLam L body body' hB ih =>
      simp only [substFVar_mkLam]
      refine .congLam (L ∪ {x}) (substFVar x u body) (substFVar x u body') (fun y hy => ?_)
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ih y hyL
      rwa [substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc, substFVar_fvar_ne u hyx] at key
  | congAppFun hf ih =>
      simp only [substFVar_mkApp]; exact .congAppFun ih
  | congAppArg ha ih =>
      simp only [substFVar_mkApp]; exact .congAppArg ih
  | congPairFst ha ih =>
      simp only [substFVar_mkPair]; exact .congPairFst ih
  | congPairSnd hb ih =>
      simp only [substFVar_mkPair]; exact .congPairSnd ih
  | congFst hp ih =>
      simp only [substFVar_mkFst]; exact .congFst ih
  | congSnd hp ih =>
      simp only [substFVar_mkSnd]; exact .congSnd ih
  | congRefl ha ih =>
      simp only [substFVar_mkRefl]; exact .congRefl ih

/-- `PureReducesStar` is equivariant under `substFVar`. -/
theorem pureReducesStar_substFVar {x : String} {u : Pattern}
    (hlc : lc_at 0 u = true) {p q : Pattern} (h : PureReducesStar p q) :
    PureReducesStar (substFVar x u p) (substFVar x u q) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (pureReduces_substFVar hlc hs) ih

/-! ## closeBVar — Abstract a free variable back to a bound variable

The dual of `openBVar`: replace `.fvar x` with `.bvar k`, incrementing k
under binders. Needed for the open-close roundtrip. -/

/-- Replace all occurrences of `.fvar x` with `.bvar k` in a pattern,
    incrementing k under binders. -/
def closeBVar (k : Nat) (x : String) : Pattern → Pattern
  | .bvar n => .bvar n
  | .fvar y => if y = x then .bvar k else .fvar y
  | .apply c args => .apply c (args.map (closeBVar k x))
  | .lambda body => .lambda (closeBVar (k + 1) x body)
  | .multiLambda n body => .multiLambda n (closeBVar (k + n) x body)
  | .subst body repl => .subst (closeBVar (k + 1) x body) (closeBVar k x repl)
  | .collection ct elems rest => .collection ct (elems.map (closeBVar k x)) rest
termination_by p => sizeOf p

/-- `closeBVar` removes `x` from free variables. -/
theorem isFresh_closeBVar (k : Nat) (x : String) (p : Pattern) :
    isFresh x (closeBVar k x p) = true := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar _ => simp [closeBVar, isFresh, freeVars]
  | hfvar y =>
    unfold closeBVar; split
    · simp [isFresh, freeVars]
    · next hne => simp [isFresh, freeVars]; exact Ne.symm hne
  | happly c args ih =>
    simp only [closeBVar, isFresh, freeVars, Bool.not_eq_true']
    rw [Bool.eq_false_iff]; intro hmem
    rw [List.contains_iff_mem] at hmem
    obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.mp hmem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    have := ih p hp k
    simp only [isFresh, Bool.not_eq_true'] at this
    rw [Bool.eq_false_iff] at this
    exact this (List.contains_iff_mem.mpr hxq)
  | hlambda body ih =>
    simp only [closeBVar, isFresh, freeVars]; exact ih (k + 1)
  | hmultiLambda n body ih =>
    simp only [closeBVar, isFresh, freeVars]; exact ih (k + n)
  | hsubst body repl ihb ihr =>
    unfold closeBVar
    have h1 := ihb (k + 1)
    have h2 := ihr k
    simp only [isFresh, freeVars, Bool.not_eq_true'] at h1 h2 ⊢
    rw [Bool.eq_false_iff]; intro hmem
    rw [List.contains_iff_mem, List.mem_append] at hmem
    cases hmem with
    | inl h => rw [Bool.eq_false_iff] at h1; exact h1 (List.contains_iff_mem.mpr h)
    | inr h => rw [Bool.eq_false_iff] at h2; exact h2 (List.contains_iff_mem.mpr h)
  | hcollection ct elems rest ih =>
    simp only [closeBVar, isFresh, freeVars, Bool.not_eq_true']
    rw [Bool.eq_false_iff]; intro hmem
    rw [List.contains_iff_mem] at hmem
    obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.mp hmem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    have := ih p hp k
    simp only [isFresh, Bool.not_eq_true'] at this
    rw [Bool.eq_false_iff] at this
    exact this (List.contains_iff_mem.mpr hxq)

/-- Open-close roundtrip: `openBVar k (fvar x) (closeBVar k x p) = p` when
    `p` is locally closed at level `k` (no free bvars at level ≥ k). -/
theorem openBVar_closeBVar_cancel {k : Nat} {x : String} {p : Pattern}
    (hlc : lc_at k p = true) :
    openBVar k (.fvar x) (closeBVar k x p) = p := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [closeBVar, openBVar]
    have hlt : n < k := by simpa [lc_at] using hlc
    split
    · next h => simp [beq_iff_eq] at h; omega
    · rfl
  | hfvar y =>
    unfold closeBVar; split
    · next h => subst h; simp [openBVar]
    · simp [openBVar]
  | happly c args ih =>
    simp only [closeBVar, openBVar, List.map_map]
    congr 1; exact list_map_eq_self fun a ha =>
      ih a ha (lc_at_list_mem (by simpa [lc_at] using hlc) ha)
  | hlambda body ih =>
    simp only [closeBVar, openBVar]; congr 1
    exact ih (by simpa [lc_at] using hlc)
  | hmultiLambda n body ih =>
    simp only [closeBVar, openBVar]; congr 1
    exact ih (by simpa [lc_at] using hlc)
  | hsubst body repl ihb ihr =>
    simp only [closeBVar, openBVar]; congr 1
    · exact ihb (by simp [lc_at, Bool.and_eq_true] at hlc; exact hlc.1)
    · exact ihr (by simp [lc_at, Bool.and_eq_true] at hlc; exact hlc.2)
  | hcollection ct elems rest ih =>
    simp only [closeBVar, openBVar, List.map_map]
    congr 1; exact list_map_eq_self fun a ha =>
      ih a ha (lc_at_list_mem (by simpa [lc_at] using hlc) ha)

/-- `substFVar` preserves `lc_at`: substituting an lc term for a free variable
    in an lc pattern yields an lc pattern. -/
theorem lc_at_substFVar {k : Nat} {x : String} {u p : Pattern}
    (hp : lc_at k p = true) (hu : lc_at k u = true) :
    lc_at k (substFVar x u p) = true := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n => simp [substFVar]; exact hp
  | hfvar y => simp [substFVar]; split <;> simp [lc_at, *]
  | happly c args ih =>
    simp only [substFVar, lc_at] at hp ⊢
    induction args with
    | nil => simp [lc_at_list]
    | cons a as ihas =>
      simp only [List.map_cons, lc_at_list, Bool.and_eq_true] at hp ⊢
      exact ⟨ih a List.mem_cons_self hp.1 hu,
             ihas (fun q hq => ih q (List.mem_cons_of_mem _ hq)) hp.2⟩
  | hlambda body ih =>
    simp only [substFVar, lc_at] at hp ⊢
    exact ih hp (lc_at_mono hu (Nat.le_add_right k 1))
  | hmultiLambda n body ih =>
    simp only [substFVar, lc_at] at hp ⊢
    exact ih hp (lc_at_mono hu (Nat.le_add_right k n))
  | hsubst body repl ihb ihr =>
    simp only [substFVar, lc_at, Bool.and_eq_true] at hp ⊢
    exact ⟨ihb hp.1 (lc_at_mono hu (Nat.le_add_right k 1)), ihr hp.2 hu⟩
  | hcollection ct elems rest ih =>
    simp only [substFVar, lc_at] at hp ⊢
    induction elems with
    | nil => simp [lc_at_list]
    | cons a as ihas =>
      simp only [List.map_cons, lc_at_list, Bool.and_eq_true] at hp ⊢
      exact ⟨ih a List.mem_cons_self hp.1 hu,
             ihas (fun q hq => ih q (List.mem_cons_of_mem _ hq)) hp.2⟩

/-! ## lc_at preservation infrastructure -/

/-- Reverse of `lc_at_openBVar_result`: if `lc_at k (openBVar k u p)`, then `lc_at (k+1) p`.
    The key: opening at level k absorbs the bvar at level k, so the original had
    at most bvars < k+1. -/
theorem lc_at_of_openBVar {k : Nat} {u : Pattern} {p : Pattern}
    (h : lc_at k (openBVar k u p) = true) : lc_at (k + 1) p = true := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [openBVar] at h; split at h
    · next heq =>
      simp [beq_iff_eq] at heq
      simp [lc_at, decide_eq_true_eq]
      omega
    · next hne =>
      simp [lc_at, decide_eq_true_eq] at h ⊢
      omega
  | hfvar _ => simp [lc_at]
  | happly c args ih =>
    simp only [openBVar, lc_at] at h ⊢
    induction args with
    | nil => simp [lc_at_list]
    | cons a as ihas =>
      simp only [List.map_cons, lc_at_list, Bool.and_eq_true] at h ⊢
      exact ⟨ih a List.mem_cons_self h.1,
             ihas (fun p hp => ih p (List.mem_cons_of_mem _ hp)) h.2⟩
  | hlambda body ih =>
    simp only [openBVar, lc_at] at h ⊢
    exact ih h
  | hmultiLambda n body ih =>
    simp only [openBVar, lc_at] at h ⊢
    have step := ih h
    rwa [Nat.add_right_comm] at step
  | hsubst body repl ihb ihr =>
    simp only [openBVar, lc_at, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    exact ⟨ihb h1, ihr h2⟩
  | hcollection ct elems rest ih =>
    simp only [openBVar, lc_at] at h ⊢
    induction elems with
    | nil => simp [lc_at_list]
    | cons a as ihas =>
      simp only [List.map_cons, lc_at_list, Bool.and_eq_true] at h ⊢
      exact ⟨ih a List.mem_cons_self h.1,
             ihas (fun p hp => ih p (List.mem_cons_of_mem _ hp)) h.2⟩

/-- `closeBVar` at level k on a term lc_at k produces a term lc_at (k+1). -/
theorem lc_at_closeBVar {k : Nat} {x : String} {p : Pattern}
    (hlc : lc_at k p = true) : lc_at (k + 1) (closeBVar k x p) = true := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [closeBVar, lc_at, decide_eq_true_eq] at hlc ⊢; omega
  | hfvar y =>
    unfold closeBVar; split <;> simp [lc_at]
  | happly c args ih =>
    simp only [closeBVar, lc_at] at hlc ⊢
    induction args with
    | nil => simp [lc_at_list]
    | cons a as ihas =>
      simp only [List.map_cons, lc_at_list, Bool.and_eq_true] at hlc ⊢
      exact ⟨ih a List.mem_cons_self hlc.1,
             ihas (fun p hp => ih p (List.mem_cons_of_mem _ hp)) hlc.2⟩
  | hlambda body ih =>
    simp only [closeBVar, lc_at] at hlc ⊢
    exact ih hlc
  | hmultiLambda n body ih =>
    simp only [closeBVar, lc_at] at hlc ⊢
    have step := ih hlc
    rwa [Nat.add_right_comm] at step
  | hsubst body repl ihb ihr =>
    simp only [closeBVar, lc_at, Bool.and_eq_true] at hlc ⊢
    obtain ⟨hlc1, hlc2⟩ := hlc
    exact ⟨ihb hlc1, ihr hlc2⟩
  | hcollection ct elems rest ih =>
    simp only [closeBVar, lc_at] at hlc ⊢
    induction elems with
    | nil => simp [lc_at_list]
    | cons a as ihas =>
      simp only [List.map_cons, lc_at_list, Bool.and_eq_true] at hlc ⊢
      exact ⟨ih a List.mem_cons_self hlc.1,
             ihas (fun p hp => ih p (List.mem_cons_of_mem _ hp)) hlc.2⟩

/-- Substituting `fvar x` for itself is identity. -/
theorem substFVar_self (x : String) (p : Pattern) :
    substFVar x (.fvar x) p = p := by
  induction p using Pattern.inductionOn with
  | hbvar _ => unfold substFVar; rfl
  | hfvar y =>
    simp only [substFVar]
    split_ifs with h
    · exact congrArg Pattern.fvar h.symm
    · rfl
  | happly c args ih =>
    unfold substFVar; congr 1
    exact list_map_eq_self fun a ha => ih a ha
  | hlambda body ih =>
    simp only [substFVar, ih]
  | hmultiLambda n body ih =>
    simp only [substFVar, ih]
  | hsubst body repl ihb ihr =>
    unfold substFVar; congr 1 <;> assumption
  | hcollection ct elems rest ih =>
    unfold substFVar; congr 1
    exact list_map_eq_self fun a ha => ih a ha

/-- Fresh name existence for Finsets of strings. -/
theorem exists_fresh (S : Finset String) : ∃ x : String, x ∉ S :=
  Infinite.exists_notMem_finset S

private theorem lc_at_list_cons_iff {k : Nat} {a : Pattern} {as : List Pattern} :
    lc_at_list k (a :: as) = true ↔ lc_at k a = true ∧ lc_at_list k as = true := by
  simp [lc_at_list, Bool.and_eq_true]

/-! ## PureReduces preserves local closure -/

/-- Single-step reduction preserves `lc_at 0`. -/
theorem pureReduces_preserves_lc {p q : Pattern}
    (h : PureReduces p q) (hlc : lc_at 0 p = true) :
    lc_at 0 q = true := by
  induction h with
  | betaPi body a =>
    simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact lc_at_openBVar_result hlc.1 hlc.2
  | betaSigmaFst a b =>
    simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact hlc.1
  | betaSigmaSnd a b =>
    simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact hlc.2
  | congPiDom _ ih =>
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨ih hlc.1, hlc.2⟩
  | congPiCod L A Bc Bc' hBc ih =>
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    refine ⟨hlc.1, ?_⟩
    obtain ⟨y, hy⟩ := exists_fresh L
    have hlcOpen := lc_at_openBVar_result hlc.2 (by simp [lc_at] : lc_at 0 (.fvar y) = true)
    have := ih y hy hlcOpen
    exact lc_at_of_openBVar this
  | congSigmaDom _ ih =>
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨ih hlc.1, hlc.2⟩
  | congSigmaCod L A Bc Bc' hBc ih =>
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    refine ⟨hlc.1, ?_⟩
    obtain ⟨y, hy⟩ := exists_fresh L
    have hlcOpen := lc_at_openBVar_result hlc.2 (by simp [lc_at] : lc_at 0 (.fvar y) = true)
    have := ih y hy hlcOpen
    exact lc_at_of_openBVar this
  | congIdType _ ih =>
    simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨ih hlc.1, hlc.2⟩
  | congIdLeft _ ih =>
    simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨hlc.1, ih hlc.2.1, hlc.2.2⟩
  | congIdRight _ ih =>
    simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨hlc.1, hlc.2.1, ih hlc.2.2⟩
  | congLam L body body' _ ih =>
    simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    obtain ⟨y, hy⟩ := exists_fresh L
    have hlcOpen := lc_at_openBVar_result hlc (by simp [lc_at] : lc_at 0 (.fvar y) = true)
    have := ih y hy hlcOpen
    exact lc_at_of_openBVar this
  | congAppFun _ ih =>
    simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨ih hlc.1, hlc.2⟩
  | congAppArg _ ih =>
    simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨hlc.1, ih hlc.2⟩
  | congPairFst _ ih =>
    simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨ih hlc.1, hlc.2⟩
  | congPairSnd _ ih =>
    simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨hlc.1, ih hlc.2⟩
  | congFst _ ih =>
    simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ih hlc
  | congSnd _ ih =>
    simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ih hlc
  | congRefl _ ih =>
    simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ih hlc

/-- Multi-step reduction preserves `lc_at 0`. -/
theorem pureReducesStar_preserves_lc {p q : Pattern}
    (h : PureReducesStar p q) (hlc : lc_at 0 p = true) :
    lc_at 0 q = true := by
  induction h with
  | refl => exact hlc
  | step hs _ ih => exact ih (pureReduces_preserves_lc hs hlc)

/-! ## Multi-step binder congruence

Strategy: pick a fresh variable x₀, get the reduction chain on opened terms,
then lift each single step through mkLam/mkPi/mkSigma using the
PureReduces.congLam/congPiCod/congSigmaCod constructors.

For each intermediate term `mid` in the chain, define `mid' := closeBVar 0 x₀ mid`
and use openBVar_closeBVar_cancel + pureReducesStar_substFVar for renaming. -/

/-- Helper: convert List to Finset for use in cofinite sets. -/
private def listToFinset (l : List String) : Finset String :=
  l.toFinset

/-- Reverse roundtrip: `closeBVar k x (openBVar k (fvar x) p) = p` when `isFresh x p`.
    This is the dual of `openBVar_closeBVar_cancel` (which requires `lc_at k p`). -/
theorem closeBVar_openBVar_cancel {k : Nat} {x : String} {p : Pattern}
    (hf : isFresh x p = true) :
    closeBVar k x (openBVar k (.fvar x) p) = p := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [openBVar]; split
    · next h => simp [beq_iff_eq] at h; subst h; simp [closeBVar]
    · simp [closeBVar]
  | hfvar y =>
    have hne : y ≠ x := by
      simp only [isFresh, freeVars, Bool.not_eq_true'] at hf
      intro h; subst h; simp at hf
    simp [openBVar, closeBVar, hne]
  | happly c args ih =>
    simp only [openBVar, closeBVar, List.map_map]
    congr 1; exact list_map_eq_self fun a ha =>
      ih a ha (isFresh_of_apply_mem hf ha)
  | hlambda body ih =>
    simp only [openBVar, closeBVar]; congr 1
    exact ih (isFresh_of_lambda hf)
  | hmultiLambda n body ih =>
    simp only [openBVar, closeBVar]; congr 1
    exact ih (isFresh_of_multiLambda hf)
  | hsubst body repl ihb ihr =>
    simp only [openBVar, closeBVar]; congr 1
    · exact ihb (isFresh_of_subst_body hf)
    · exact ihr (isFresh_of_subst_repl hf)
  | hcollection ct elems rest ih =>
    simp only [openBVar, closeBVar, List.map_map]
    congr 1; exact list_map_eq_self fun a ha =>
      ih a ha (isFresh_of_collection_mem hf ha)

/-- Helper: pick a fresh x₀, establish freshness for two bodies. -/
private theorem isFresh_of_not_in_freeVars_finset {x : String} {p : Pattern}
    (h : x ∉ listToFinset (freeVars p)) : isFresh x p = true := by
  simp only [isFresh, Bool.not_eq_true']; rw [Bool.eq_false_iff]
  intro hmem; exact h (List.mem_toFinset.mpr (List.contains_iff_mem.mp hmem))

/-- Core induction for multi-step binder congruence.
    Tracks both endpoints via equality hypotheses to avoid non-variable index issues. -/
private theorem binderCongruenceAux
    (wrap : Pattern → Pattern)
    (wrapStep : ∀ b b', (∀ y, y ∉ (∅ : Finset String) →
        PureReduces (openBVar 0 (.fvar y) b) (openBVar 0 (.fvar y) b')) →
      PureReduces (wrap b) (wrap b'))
    (x₀ : String) {b' : Pattern}
    (hlcB' : lc_at 1 b' = true) (hfreshB' : isFresh x₀ b' = true)
    {p q : Pattern} (hpq : PureReducesStar p q)
    {b : Pattern} (hlcb : lc_at 1 b = true) (hfreshb : isFresh x₀ b = true)
    (hpb : p = openBVar 0 (.fvar x₀) b) (hqb' : q = openBVar 0 (.fvar x₀) b') :
    PureReducesStar (wrap b) (wrap b') := by
  induction hpq generalizing b with
  | refl =>
    have heq : b = b' := by
      have h1 : openBVar 0 (.fvar x₀) b = openBVar 0 (.fvar x₀) b' := by
        rw [← hpb]; exact hqb'
      calc b = closeBVar 0 x₀ (openBVar 0 (.fvar x₀) b) := (closeBVar_openBVar_cancel hfreshb).symm
        _ = closeBVar 0 x₀ (openBVar 0 (.fvar x₀) b') := by rw [h1]
        _ = b' := closeBVar_openBVar_cancel hfreshB'
    subst heq; exact .refl _
  | @step _ mid _ hstep htail ih =>
    rw [hpb] at hstep
    set mid' := closeBVar 0 x₀ mid
    have hlcMid : lc_at 0 mid = true :=
      pureReduces_preserves_lc hstep (lc_at_openBVar_result hlcb (by simp [lc_at]))
    have hopen_mid' : openBVar 0 (.fvar x₀) mid' = mid := openBVar_closeBVar_cancel hlcMid
    have hx₀mid' : isFresh x₀ mid' = true := isFresh_closeBVar 0 x₀ mid
    have hlcMid' : lc_at 1 mid' = true := lc_at_closeBVar hlcMid
    -- Step 1: wrap b → wrap mid'
    have step1 : PureReduces (wrap b) (wrap mid') := by
      apply wrapStep b mid'
      intro y _
      have key := pureReduces_substFVar (x := x₀) (u := .fvar y)
        (by simp [lc_at] : lc_at 0 (.fvar y) = true) hstep
      rw [substFVar_intro b hfreshb 0] at key
      rw [show substFVar x₀ (.fvar y) mid = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) mid')
        from by rw [hopen_mid']] at key
      rw [substFVar_intro mid' hx₀mid' 0] at key
      exact key
    -- Step 2: wrap mid' →* wrap b' (by IH)
    have step2 : PureReducesStar (wrap mid') (wrap b') :=
      ih hlcMid' hx₀mid' hopen_mid'.symm hqb'
    exact .step step1 step2

/-- Multi-step Lam congruence from cofinite body reduction.
    Requires locally-closed bodies for the closeBVar roundtrip. -/
theorem PureReducesStar.congLamLC (L : Finset String) {body body' : Pattern}
    (hlcB : lc_at 1 body = true) (hlcB' : lc_at 1 body' = true)
    (h : ∀ x, x ∉ L → PureReducesStar (openBVar 0 (.fvar x) body)
                                         (openBVar 0 (.fvar x) body')) :
    PureReducesStar (mkLam body) (mkLam body') := by
  set L' := L ∪ listToFinset (freeVars body) ∪ listToFinset (freeVars body')
  obtain ⟨x₀, hx₀⟩ := exists_fresh L'
  have hx₀L : x₀ ∉ L := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hx₀B := isFresh_of_not_in_freeVars_finset (show x₀ ∉ listToFinset (freeVars body) from
    fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have hx₀B' := isFresh_of_not_in_freeVars_finset (show x₀ ∉ listToFinset (freeVars body') from
    fun h => hx₀ (Finset.mem_union_right _ h))
  exact binderCongruenceAux mkLam
    (fun b b' hred => .congLam ∅ b b' hred)
    x₀ hlcB' hx₀B' (h x₀ hx₀L) hlcB hx₀B rfl rfl

/-- Multi-step Pi codomain congruence from cofinite body reduction. -/
theorem PureReducesStar.congPiCodLC (L : Finset String) {A B B' : Pattern}
    (hlcB : lc_at 1 B = true) (hlcB' : lc_at 1 B' = true)
    (h : ∀ x, x ∉ L → PureReducesStar (openBVar 0 (.fvar x) B)
                                         (openBVar 0 (.fvar x) B')) :
    PureReducesStar (mkPi A B) (mkPi A B') := by
  set L' := L ∪ listToFinset (freeVars B) ∪ listToFinset (freeVars B')
  obtain ⟨x₀, hx₀⟩ := exists_fresh L'
  have hx₀L : x₀ ∉ L := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hx₀B := isFresh_of_not_in_freeVars_finset (show x₀ ∉ listToFinset (freeVars B) from
    fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have hx₀B' := isFresh_of_not_in_freeVars_finset (show x₀ ∉ listToFinset (freeVars B') from
    fun h => hx₀ (Finset.mem_union_right _ h))
  exact binderCongruenceAux (mkPi A)
    (fun b b' hred => .congPiCod ∅ A b b' hred)
    x₀ hlcB' hx₀B' (h x₀ hx₀L) hlcB hx₀B rfl rfl

/-- Multi-step Sigma codomain congruence from cofinite body reduction. -/
theorem PureReducesStar.congSigmaCodLC (L : Finset String) {A B B' : Pattern}
    (hlcB : lc_at 1 B = true) (hlcB' : lc_at 1 B' = true)
    (h : ∀ x, x ∉ L → PureReducesStar (openBVar 0 (.fvar x) B)
                                         (openBVar 0 (.fvar x) B')) :
    PureReducesStar (mkSigma A B) (mkSigma A B') := by
  set L' := L ∪ listToFinset (freeVars B) ∪ listToFinset (freeVars B')
  obtain ⟨x₀, hx₀⟩ := exists_fresh L'
  have hx₀L : x₀ ∉ L := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hx₀B := isFresh_of_not_in_freeVars_finset (show x₀ ∉ listToFinset (freeVars B) from
    fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have hx₀B' := isFresh_of_not_in_freeVars_finset (show x₀ ∉ listToFinset (freeVars B') from
    fun h => hx₀ (Finset.mem_union_right _ h))
  exact binderCongruenceAux (mkSigma A)
    (fun b b' hred => .congSigmaCod ∅ A b b' hred)
    x₀ hlcB' hx₀B' (h x₀ hx₀L) hlcB hx₀B rfl rfl

/-! ## Multi-step reduction implies conversion (lc version)

Moved here from Reduction.lean because it needs `pureReduces_preserves_lc`. -/

/-- Multi-step reduction of a locally closed term implies conversion. -/
theorem PureReducesStar_implies_PureConv {t₁ t₂ : Pattern}
    (h : PureReducesStar t₁ t₂) (hlc : lc_at 0 t₁ = true) :
    PureConv t₁ t₂ := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
      exact .trans (PureReduces_implies_PureConv hs hlc)
                   (ih (pureReduces_preserves_lc hs hlc))

end Mettapedia.Languages.MeTTa.Pure.FVarSubst
