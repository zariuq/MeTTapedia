import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Free-name substitution and locally nameless binders

Closing a name removes its free occurrences. Substitution by a free name
commutes with disjoint binders; freshening a binder protects a colliding
replacement. These laws apply to raw patterns without explicit substitutions,
whose execution would otherwise change the constructor structure.
-/

namespace Mettapedia.OSLF.MeTTaIL.Substitution

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Helper: pointwise equal functions produce equal maps. -/
private theorem list_map_eq_map {α β : Type*} {f g : α → β} {l : List α}
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, List.map_cons]; congr 1
    · exact h a (List.mem_cons.mpr (Or.inl rfl))
    · exact ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))

/-- Helper: allNoExplicitSubst for a mapped list from pointwise proof. -/
private theorem allNoExplicitSubst_map {f : Pattern → Pattern} {ps : List Pattern}
    (hall : allNoExplicitSubst ps = true)
    (hf : ∀ q ∈ ps, noExplicitSubst q = true → noExplicitSubst (f q) = true) :
    allNoExplicitSubst (ps.map f) = true := by
  induction ps with
  | nil => rfl
  | cons a as ih =>
    simp only [allNoExplicitSubst, Bool.and_eq_true] at hall ⊢
    simp only [List.map_cons, allNoExplicitSubst, Bool.and_eq_true]
    exact ⟨hf a (List.mem_cons.mpr (Or.inl rfl)) hall.1,
           ih hall.2 (fun q hq => hf q (List.mem_cons.mpr (Or.inr hq)))⟩

/-- closeFVar preserves noExplicitSubst. -/
theorem noExplicitSubst_closeFVar {k : Nat} {x : String} {p : Pattern}
    (h : noExplicitSubst p = true) : noExplicitSubst (closeFVar k x p) = true := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar _ => simp only [closeFVar, noExplicitSubst]
  | hfvar y =>
    simp only [closeFVar]; split
    · simp only [noExplicitSubst]
    · simp only [noExplicitSubst]
  | happly c args ih =>
    simp only [closeFVar, noExplicitSubst]
    exact allNoExplicitSubst_map h fun q hq hnes => ih q hq (k := k) hnes
  | hlambda _ body ih => simp only [closeFVar, noExplicitSubst]; exact ih h
  | hmultiLambda _ _ body ih => simp only [closeFVar, noExplicitSubst]; exact ih h
  | hsubst _ _ _ _ => exact absurd h Bool.false_ne_true
  | hcollection ct elems rest ih =>
    simp only [closeFVar, noExplicitSubst]
    exact allNoExplicitSubst_map h fun q hq hnes => ih q hq (k := k) hnes

/-- Closing removes exactly the free occurrences of its binder name. -/
theorem freeVars_closeFVar_iff (p : Pattern) (k : Nat) (binder name : String) :
    name ∈ freeVars (closeFVar k binder p) ↔ name ≠ binder ∧ name ∈ freeVars p := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar _ => simp [closeFVar, freeVars]
  | hfvar x =>
      by_cases hx : x = binder
      · subst x; simp [closeFVar, freeVars]
      · simp [closeFVar, freeVars, beq_eq_false_iff_ne.mpr hx]
        intro same; exact same ▸ hx
  | happly c args ih | hcollection c args _ ih =>
      simp only [closeFVar, freeVars, List.flatMap_map,
        List.mem_flatMap]
      constructor
      · rintro ⟨q, member, free⟩
        have h := (ih q member k).mp free
        exact ⟨h.1, q, member, h.2⟩
      · rintro ⟨different, q, member, free⟩
        exact ⟨q, member, (ih q member k).mpr ⟨different, free⟩⟩
  | hlambda _ body ih => simpa only [closeFVar, freeVars] using ih (k + 1)
  | hmultiLambda n _ body ih => simpa only [closeFVar, freeVars] using ih (k + n)
  | hsubst body replacement ihBody ihReplacement =>
      simp only [closeFVar, freeVars, List.mem_append, ihBody (k + 1), ihReplacement k]
      tauto

/-- Singleton substitution replaces one free name. -/
theorem applySubst_fvar_single (old new name : String) :
    applySubst [(old, .fvar new)] (.fvar name) = .fvar (if name = old then new else name) := by
  change applySubst (SubstEnv.extend SubstEnv.empty old (.fvar new)) (.fvar name) = _
  by_cases same : name = old
  · subst name; simp only [applySubst, SubstEnv.find_extend_empty_eq, ite_true]
  · simp only [applySubst, SubstEnv.find_extend_empty_ne (Ne.symm same), if_neg same]

/-- Closing a free name selects the corresponding de Bruijn level. -/
theorem closeFVar_fvar (k : Nat) (binder name : String) :
    closeFVar k binder (.fvar name) = if name = binder then .bvar k else .fvar name := by
  simp only [closeFVar, beq_iff_eq]

/-- Freshen the binder before substitution, then close it: even a colliding
replacement remains free. -/
theorem closeFVar_applySubst_freshen {p : Pattern} {old new bound fresh : String} (k : Nat)
    (distinct : old ≠ bound) (oldFresh : old ≠ fresh) (newFresh : new ≠ fresh)
    (absent : fresh ∉ freeVars p) (normal : noExplicitSubst p = true) :
    closeFVar k fresh
      (applySubst [(old, .fvar new)] (applySubst [(bound, .fvar fresh)] p)) =
      applySubst [(old, .fvar new)] (closeFVar k bound p) := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar _ => simp [closeFVar, applySubst]
  | hfvar name =>
      have nameFresh : name ≠ fresh := by
        simpa only [freeVars, List.mem_singleton, ne_eq, eq_comm] using absent
      by_cases nameBound : name = bound
      · subst name
        simp only [applySubst_fvar_single, ite_true, if_neg (Ne.symm oldFresh),
          closeFVar_fvar, applySubst]
      · by_cases nameOld : name = old
        · subst name
          simp only [applySubst_fvar_single, if_neg distinct, ite_true,
            closeFVar_fvar, if_neg newFresh]
        · simp only [applySubst_fvar_single, if_neg nameBound, if_neg nameOld,
            closeFVar_fvar, if_neg nameFresh]
  | happly c args ih | hcollection c args _ ih =>
      simp only [freeVars] at absent
      simp only [applySubst, closeFVar, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      exact ih q member k
        (fun free => absent (List.mem_flatMap.mpr ⟨q, member, free⟩))
        (allNoExplicitSubst_mem normal member)
  | hlambda _ body ih =>
      simp only [applySubst, closeFVar]
      exact congrArg (Pattern.lambda _) (ih (k + 1)
        (by simpa only [freeVars] using absent) normal)
  | hmultiLambda n names body ih =>
      simp only [applySubst, closeFVar]
      exact congrArg (Pattern.multiLambda n names) (ih (k + n)
        (by simpa only [freeVars] using absent) normal)
  | hsubst _ _ _ _ => exact absurd normal Bool.false_ne_true


/-- Freshness as a Boolean agrees with non-membership in the free-name list. -/
theorem isFresh_iff_not_mem (name : String) (p : Pattern) :
    isFresh name p = true ↔ name ∉ freeVars p := by
  simp [isFresh]

/-- After closeFVar k y p, y is fresh in the result. -/
theorem isFresh_closeFVar_self (k : Nat) (y : String) (p : Pattern) :
    isFresh y (closeFVar k y p) = true := by
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]; intro h
  have hmem : y ∈ freeVars (closeFVar k y p) := by
    simp only [List.contains_iff_exists_mem_beq] at h
    obtain ⟨w, hw, hwy⟩ := h
    rwa [show w = y from (beq_iff_eq.mp hwy).symm] at hw
  exact ((freeVars_closeFVar_iff p k y y).mp hmem).1 rfl

/-- Singleton fvar substitution commutes with closeFVar when names are disjoint.

    Preconditions (Barendregt convention):
    - `hyw : y ≠ w`: the substituted variable differs from the abstracted one
    - `hzw : z ≠ w`: the replacement doesn't clash with the abstracted variable -/
theorem applySubst_closeFVar_comm_single
    {y z w : String} {p : Pattern} {k : Nat}
    (hyw : y ≠ w) (hzw : z ≠ w) (hnes : noExplicitSubst p = true) :
    applySubst (SubstEnv.extend SubstEnv.empty y (.fvar z)) (closeFVar k w p) =
      closeFVar k w (applySubst (SubstEnv.extend SubstEnv.empty y (.fvar z)) p) := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n => simp [closeFVar, applySubst]
  | hfvar x =>
    show applySubst _ (closeFVar k w (.fvar x)) = closeFVar k w (applySubst _ (.fvar x))
    by_cases hxw : x = w
    · -- x = w: LHS: closeFVar gives .bvar k, applySubst leaves it
      --        RHS: applySubst misses (y ≠ w), then closeFVar gives .bvar k
      subst hxw
      simp only [closeFVar, beq_self_eq_true, ite_true, applySubst,
                 SubstEnv.find_extend_empty_ne hyw]
    · -- x ≠ w: closeFVar leaves .fvar x
      have hxw_beq : (x == w) = false := beq_eq_false_iff_ne.mpr hxw
      have hclose_x : closeFVar k w (.fvar x) = .fvar x := by
        simp only [closeFVar, hxw_beq, Bool.false_eq_true, ↓reduceIte]
      rw [hclose_x]
      by_cases hxy : y = x
      · -- y = x: substitution fires to .fvar z; closeFVar leaves it since z ≠ w
        subst hxy
        -- now x is gone, the var is y; hyw : y ≠ w, hxw_beq : (y == w) = false
        have hsubst_y : applySubst (SubstEnv.extend SubstEnv.empty y (.fvar z)) (.fvar y) = .fvar z := by
          simp only [applySubst, SubstEnv.find_extend_empty_eq]
        rw [hsubst_y]
        have hclose_z : closeFVar k w (.fvar z) = .fvar z := by
          simp only [closeFVar, beq_eq_false_iff_ne.mpr hzw, Bool.false_eq_true, ↓reduceIte]
        rw [hclose_z]
      · -- y ≠ x: substitution misses, closeFVar leaves .fvar x
        have hsubst_x : applySubst (SubstEnv.extend SubstEnv.empty y (.fvar z)) (.fvar x) = .fvar x := by
          simp only [applySubst, SubstEnv.find_extend_empty_ne hxy]
        rw [hsubst_x, hclose_x]
  | happly c args ih =>
    simp only [closeFVar, applySubst, List.map_map]; congr 1
    exact list_map_eq_map fun a ha => ih a ha (allNoExplicitSubst_mem hnes ha)
  | hlambda _ body ih =>
    simp only [closeFVar, applySubst]; congr 1; exact ih hnes
  | hmultiLambda _ _ body ih =>
    simp only [closeFVar, applySubst]; congr 1; exact ih hnes
  | hsubst _ _ _ _ => exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
    simp only [closeFVar, applySubst, List.map_map]; congr 1
    exact list_map_eq_map fun a ha => ih a ha (allNoExplicitSubst_mem hnes ha)

/-- closeFVar k x maps lc_at k terms to lc_at (k+1) terms. -/
theorem lc_at_closeFVar {k : Nat} {x : String} {p : Pattern}
    (hlc : lc_at k p = true) : lc_at (k + 1) (closeFVar k x p) = true := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [closeFVar, lc_at]
    simp only [lc_at] at hlc
    exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true hlc) (Nat.le_succ k))
  | hfvar y =>
    simp only [closeFVar]
    split
    · simp only [lc_at]; exact decide_eq_true (Nat.lt_succ_of_le (Nat.le_refl k))
    · simp only [lc_at]
  | happly c args ih =>
    simp only [closeFVar, lc_at] at hlc ⊢
    exact lc_at_list_of_forall fun q hq => by
      rw [List.mem_map] at hq
      obtain ⟨a, ha, rfl⟩ := hq
      exact ih a ha (lc_at_list_mem hlc ha)
  | hlambda _ body ih =>
    simp only [closeFVar, lc_at] at hlc ⊢
    have : k + 1 + 1 = (k + 1) + 1 := by omega
    rw [this]
    exact ih hlc
  | hmultiLambda n _ body ih =>
    simp only [closeFVar, lc_at] at hlc ⊢
    have : k + 1 + n = (k + n) + 1 := by omega
    rw [this]
    exact ih hlc
  | hsubst body repl ihb ihr =>
    simp only [closeFVar, lc_at, Bool.and_eq_true] at hlc ⊢
    constructor
    · have : k + 1 + 1 = (k + 1) + 1 := by omega
      rw [this]; exact ihb hlc.1
    · exact ihr hlc.2
  | hcollection ct elems rest ih =>
    simp only [closeFVar, lc_at] at hlc ⊢
    exact lc_at_list_of_forall fun q hq => by
      rw [List.mem_map] at hq
      obtain ⟨a, ha, rfl⟩ := hq
      exact ih a ha (lc_at_list_mem hlc ha)


end Mettapedia.OSLF.MeTTaIL.Substitution
