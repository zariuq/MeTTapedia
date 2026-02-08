import Mettapedia.OSLF.PiCalculus.RhoEncoding
import Mettapedia.OSLF.PiCalculus.MultiStep
import Mettapedia.OSLF.RhoCalculus.MultiStep
import Mettapedia.OSLF.PiCalculus.WeakBisim

/-!
# Sorry-Free Forward Simulation for Restriction-Free π→ρ Encoding

Proves the forward direction of operational correspondence (Prop 4) for the
restriction-free fragment of the π-calculus: processes built from nil, par,
input, and output (no ν, no replication).

## Key Results

- `forward_single_step_rf`: single-step forward simulation (sorry-free)
- `forward_multi_step_rf`: multi-step forward simulation (sorry-free)

## Structure

1. `RestrictionFree` predicate + preservation lemmas
2. `encode_rf_ns_independent`: namespace parameter doesn't matter for RF
3. Metatheory: closeFVar/applySubst commutation, openBVar SC replacement
4. `encode_rf_applySubst`: encoding commutes with substitution
5. Assembly: forward simulation from ρ-COMM + congruence

## References

- Lybech (2022), Section 6, pages 104-107
-/

namespace Mettapedia.OSLF.PiCalculus.ForwardSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.PiCalculus
open Mettapedia.OSLF.RhoCalculus hiding StructuralCongruence NameEquiv
open Mettapedia.OSLF.RhoCalculus.Reduction
-- Import SC constructors (not the type name, to avoid clash with π-calc SC)
open Mettapedia.OSLF.RhoCalculus.StructuralCongruence
  (refl symm trans alpha apply_cong lambda_cong multiLambda_cong subst_cong
   collection_general_cong par_singleton par_comm par_perm par_cong
   par_nil_left par_nil_right par_assoc par_flatten quote_drop)

/-- Abbreviation to disambiguate ρ-calculus SC from π-calculus SC. -/
local notation:50 p " ≡ᵨ " q => Mettapedia.OSLF.RhoCalculus.StructuralCongruence p q

/-! ## Restriction-Free Processes -/

/-- A π-calculus process is restriction-free: no ν or replication. -/
def RestrictionFree : Process → Prop
  | .nil => True
  | .par P Q => RestrictionFree P ∧ RestrictionFree Q
  | .input _ _ P => RestrictionFree P
  | .output _ _ => True
  | .nu _ _ => False
  | .replicate _ _ _ => False

/-- RF is preserved by π-substitution. -/
theorem rf_substitute {P : Process} (hrf : RestrictionFree P) (y z : Name) :
    RestrictionFree (P.substitute y z) := by
  induction P with
  | nil => trivial
  | par P Q ihP ihQ =>
    simp only [Process.substitute]
    exact ⟨ihP hrf.1, ihQ hrf.2⟩
  | input x w P ihP =>
    simp only [Process.substitute]
    split_ifs <;> (try exact ihP hrf) <;> exact hrf
  | output _ _ => trivial
  | nu _ _ => exact absurd hrf id
  | replicate _ _ _ => exact absurd hrf id

/-! ## Namespace Independence for RF Processes -/

/-- For RF processes, the encoding is independent of the namespace parameter. -/
theorem encode_rf_ns_independent {P : Process} (hrf : RestrictionFree P)
    (n₁ n₂ v : String) :
    encode P n₁ v = encode P n₂ v := by
  induction P generalizing n₁ n₂ with
  | nil => rfl
  | par P Q ihP ihQ =>
    show rhoPar (encode P (n₁ ++ "_L") v) (encode Q (n₁ ++ "_R") v) =
         rhoPar (encode P (n₂ ++ "_L") v) (encode Q (n₂ ++ "_R") v)
    rw [ihP hrf.1, ihQ hrf.2]
  | input x y P ihP =>
    show rhoInput (piNameToRhoName x) y (encode P n₁ v) =
         rhoInput (piNameToRhoName x) y (encode P n₂ v)
    rw [ihP hrf]
  | output _ _ => rfl
  | nu _ _ => exact absurd hrf id
  | replicate _ _ _ => exact absurd hrf id

/-! ## Locally Nameless Metatheory -/

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
  | hlambda body ih => simp only [closeFVar, noExplicitSubst]; exact ih h
  | hmultiLambda _ body ih => simp only [closeFVar, noExplicitSubst]; exact ih h
  | hsubst _ _ _ _ => exact absurd h Bool.false_ne_true
  | hcollection ct elems rest ih =>
    simp only [closeFVar, noExplicitSubst]
    exact allNoExplicitSubst_map h fun q hq hnes => ih q hq (k := k) hnes

/-- y cannot appear in freeVars (closeFVar k y p). -/
private theorem not_mem_freeVars_closeFVar_self (k : Nat) (y : String) (p : Pattern) :
    y ∉ freeVars (closeFVar k y p) := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar _ => simp [closeFVar, freeVars]
  | hfvar x =>
    simp only [closeFVar]
    split
    · simp [freeVars]
    · next hne =>
      simp only [freeVars, List.mem_singleton]
      intro heq
      rw [heq] at hne
      exact hne (beq_self_eq_true x)
  | happly c args ih =>
    simp only [closeFVar, freeVars, List.mem_flatMap]; push_neg
    intro sub hsub_mem
    rw [List.mem_map] at hsub_mem
    obtain ⟨a, ha, rfl⟩ := hsub_mem
    exact ih a ha k
  | hlambda body ih => simp only [closeFVar, freeVars]; exact ih (k + 1)
  | hmultiLambda n body ih => simp only [closeFVar, freeVars]; exact ih (k + n)
  | hsubst body repl ihb ihr =>
    simp only [closeFVar, freeVars, List.mem_append]; push_neg
    exact ⟨ihb (k + 1), ihr k⟩
  | hcollection ct elems rest ih =>
    simp only [closeFVar, freeVars, List.mem_flatMap]; push_neg
    intro sub hsub_mem
    rw [List.mem_map] at hsub_mem
    obtain ⟨a, ha, rfl⟩ := hsub_mem
    exact ih a ha k

/-- After closeFVar k y p, y is fresh in the result. -/
theorem isFresh_closeFVar_self (k : Nat) (y : String) (p : Pattern) :
    isFresh y (closeFVar k y p) = true := by
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]; intro h
  have hmem : y ∈ freeVars (closeFVar k y p) := by
    simp only [List.contains_iff_exists_mem_beq] at h
    obtain ⟨w, hw, hwy⟩ := h
    rwa [show w = y from (beq_iff_eq.mp hwy).symm] at hw
  exact not_mem_freeVars_closeFVar_self k y p hmem

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
  | hlambda body ih =>
    simp only [closeFVar, applySubst]; congr 1; exact ih hnes
  | hmultiLambda _ body ih =>
    simp only [closeFVar, applySubst]; congr 1; exact ih hnes
  | hsubst _ _ _ _ => exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
    simp only [closeFVar, applySubst, List.map_map]; congr 1
    exact list_map_eq_map fun a ha => ih a ha (allNoExplicitSubst_mem hnes ha)

/-! ## SC Propagation Through openBVar -/

/-- If SC u u', then SC (openBVar k u body) (openBVar k u' body).
    SC on the substituted term propagates through openBVar. -/
theorem openBVar_SC_replacement {u u' : Pattern}
    (hsc : u ≡ᵨ u') (body : Pattern) (k : Nat) :
    openBVar k u body ≡ᵨ openBVar k u' body := by
  induction body using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [openBVar]; split
    · exact hsc
    · exact refl _
  | hfvar _ => simp only [openBVar]; exact refl _
  | happly c args ih =>
    simp only [openBVar]
    apply apply_cong c _ _ (by simp [List.length_map])
    intro i h₁ h₂
    simp only [List.length_map] at h₁ h₂
    simp only [List.get_eq_getElem, List.getElem_map]
    exact ih _ (List.getElem_mem h₁) k
  | hlambda body ih =>
    simp only [openBVar]; exact lambda_cong _ _ (ih (k + 1))
  | hmultiLambda n body ih =>
    simp only [openBVar]; exact multiLambda_cong n _ _ (ih (k + n))
  | hsubst body repl ihb ihr =>
    simp only [openBVar]; exact subst_cong _ _ _ _ (ihb (k + 1)) (ihr k)
  | hcollection ct elems rest ih =>
    simp only [openBVar]
    apply collection_general_cong ct _ _ rest (by simp [List.length_map])
    intro i h₁ h₂
    simp only [List.length_map] at h₁ h₂
    simp only [List.get_eq_getElem, List.getElem_map]
    exact ih _ (List.getElem_mem h₁) k

/-! ## Encoding Preserves noExplicitSubst -/

/-- Helper: allNoExplicitSubst distributes over append. -/
private theorem allNoExplicitSubst_append {ps qs : List Pattern}
    (hp : allNoExplicitSubst ps = true) (hq : allNoExplicitSubst qs = true) :
    allNoExplicitSubst (ps ++ qs) = true := by
  induction ps with
  | nil => exact hq
  | cons a as ih =>
    simp only [List.cons_append, allNoExplicitSubst, Bool.and_eq_true] at hp ⊢
    exact ⟨hp.1, ih hp.2⟩

/-- rhoPar preserves noExplicitSubst. -/
private theorem noExplicitSubst_rhoPar {P Q : Pattern}
    (hp : noExplicitSubst P = true) (hq : noExplicitSubst Q = true) :
    noExplicitSubst (rhoPar P Q) = true := by
  unfold rhoPar
  split
  · -- Both hashBag
    simp only [noExplicitSubst]
    simp only [noExplicitSubst] at hp hq
    exact allNoExplicitSubst_append hp hq
  · -- Left hashBag, right not
    simp only [noExplicitSubst]
    simp only [noExplicitSubst] at hp
    exact allNoExplicitSubst_append hp (by simp [allNoExplicitSubst, hq])
  · -- Left not, right hashBag
    simp only [noExplicitSubst]
    simp only [noExplicitSubst] at hq
    simp only [allNoExplicitSubst, hp, Bool.true_and]; exact hq
  · -- Neither hashBag
    simp only [noExplicitSubst, allNoExplicitSubst, hp, hq, Bool.and_true]

/-- The encoding of any process is subst-free. -/
theorem encode_noExplicitSubst (P : Process) (n v : String) :
    noExplicitSubst (encode P n v) = true := by
  induction P generalizing n with
  | nil => rfl
  | par P Q ihP ihQ =>
    exact noExplicitSubst_rhoPar (ihP (n ++ "_L")) (ihQ (n ++ "_R"))
  | input x y Q ih =>
    show noExplicitSubst (.apply "PInput" [piNameToRhoName x,
           .lambda (closeFVar 0 y (encode Q n v))]) = true
    simp only [noExplicitSubst, allNoExplicitSubst, piNameToRhoName, Bool.true_and,
               Bool.and_eq_true]
    exact ⟨noExplicitSubst_closeFVar (ih n), trivial⟩
  | output x z =>
    simp only [encode, rhoOutput, rhoDrop, piNameToRhoName, noExplicitSubst,
               allNoExplicitSubst, Bool.true_and]
  | nu x Q ih =>
    exact noExplicitSubst_rhoPar
      (by simp [rhoOutput, noExplicitSubst, allNoExplicitSubst])
      (by simp only [rhoInput, noExplicitSubst, allNoExplicitSubst, Bool.true_and, Bool.and_eq_true]
          exact ⟨noExplicitSubst_closeFVar (ih (n ++ "_" ++ n)), trivial⟩)
  | replicate x y Q ih =>
    simp only [encode, rhoReplicate, rhoInput, piNameToRhoName, noExplicitSubst,
               allNoExplicitSubst, Bool.true_and, Bool.and_eq_true]
    exact ⟨⟨noExplicitSubst_closeFVar (ih (n ++ "_rep")), trivial⟩, trivial⟩

/-! ## Local Closure for closeFVar and Encoding -/

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
  | hlambda body ih =>
    simp only [closeFVar, lc_at] at hlc ⊢
    have : k + 1 + 1 = (k + 1) + 1 := by omega
    rw [this]
    exact ih hlc
  | hmultiLambda n body ih =>
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

/-- Helper: lc_at_list distributes over append. -/
private theorem lc_at_list_append {k : Nat} {ps qs : List Pattern}
    (hp : lc_at_list k ps = true) (hq : lc_at_list k qs = true) :
    lc_at_list k (ps ++ qs) = true := by
  induction ps with
  | nil => exact hq
  | cons a as ih =>
    simp only [List.cons_append, lc_at_list, Bool.and_eq_true] at hp ⊢
    exact ⟨hp.1, ih hp.2⟩

/-- rhoPar preserves lc_at. -/
private theorem lc_at_rhoPar {k : Nat} {P Q : Pattern}
    (hp : lc_at k P = true) (hq : lc_at k Q = true) :
    lc_at k (rhoPar P Q) = true := by
  unfold rhoPar
  split
  · simp only [lc_at]; simp only [lc_at] at hp hq; exact lc_at_list_append hp hq
  · simp only [lc_at]; simp only [lc_at] at hp
    exact lc_at_list_append hp (by simp [lc_at_list, hq])
  · simp only [lc_at]; simp only [lc_at] at hq
    simp only [lc_at_list, hp, Bool.true_and]; exact hq
  · simp only [lc_at, lc_at_list, hp, hq, Bool.true_and, Bool.and_true]

/-- The encoding of an RF process is locally closed. -/
theorem encode_rf_lc {P : Process} (hrf : RestrictionFree P) (n v : String) :
    lc_at 0 (encode P n v) = true := by
  induction P generalizing n with
  | nil => rfl
  | par P Q ihP ihQ =>
    exact lc_at_rhoPar (ihP hrf.1 (n ++ "_L")) (ihQ hrf.2 (n ++ "_R"))
  | input x y Q ih =>
    show lc_at 0 (.apply "PInput" [piNameToRhoName x,
           .lambda (closeFVar 0 y (encode Q n v))]) = true
    simp only [lc_at, lc_at_list, piNameToRhoName, Bool.true_and, Bool.and_true]
    exact lc_at_closeFVar (ih hrf n)
  | output x z =>
    simp only [encode, rhoOutput, rhoDrop, piNameToRhoName, lc_at, lc_at_list, Bool.true_and]
  | nu _ _ => exact absurd hrf id
  | replicate _ _ _ => exact absurd hrf id

/-! ## Barendregt Convention -/

/-- Barendregt condition for substitution y → z in Q:
    neither y nor z equals any binding variable in Q. -/
def BarendregtFor (y z : Name) : Process → Prop
  | .nil => True
  | .par P Q => BarendregtFor y z P ∧ BarendregtFor y z Q
  | .input _ w P => y ≠ w ∧ z ≠ w ∧ BarendregtFor y z P
  | .output _ _ => True
  | .nu _ _ => True   -- RF processes don't have nu
  | .replicate _ _ _ => True

/-- BarendregtFor is preserved by π-substitution. -/
theorem barendregt_substitute {P : Process} {y z : Name}
    (hb : BarendregtFor y z P) (hrf : RestrictionFree P) :
    BarendregtFor y z (P.substitute y z) := by
  induction P with
  | nil => trivial
  | par P Q ihP ihQ =>
    exact ⟨ihP hb.1 hrf.1, ihQ hb.2 hrf.2⟩
  | input x w R ih =>
    have ⟨hyw, hzw, hbR⟩ := hb
    simp only [Process.substitute]
    split_ifs with hxy hwy
    · exact ⟨hyw, hzw, ih hbR hrf⟩
    · exact absurd hwy.symm hyw  -- w = y contradicts y ≠ w
    · exact ⟨hyw, hzw, ih hbR hrf⟩
  | output _ _ => trivial
  | nu _ _ => exact absurd hrf id
  | replicate _ _ _ => exact absurd hrf id

/-! ## rhoPar case lemmas -/

/-- Predicate: P is a hashBag-none collection. -/
private def IsHashBagNone (P : Pattern) : Prop :=
  ∃ ps, P = .collection .hashBag ps none

private instance : DecidablePred IsHashBagNone := by
  intro p
  cases p with
  | collection ct elems rest =>
    cases ct with
    | hashBag => cases rest with
      | none => exact isTrue ⟨elems, rfl⟩
      | some _ => exact isFalse (fun ⟨_, h⟩ => by cases h)
    | vec | hashSet => exact isFalse (fun ⟨_, h⟩ => by cases h)
  | bvar _ | fvar _ | apply _ _ | lambda _ | multiLambda _ _ | subst _ _ =>
    exact isFalse (fun ⟨_, h⟩ => by cases h)

private theorem not_isHashBagNone_iff {P : Pattern} :
    ¬IsHashBagNone P ↔ (∀ ps, P ≠ .collection .hashBag ps none) := by
  simp only [IsHashBagNone, not_exists]

/-- If Q is not a hashBag-none collection, rhoPar with hashBag-none LHS appends [Q]. -/
private theorem rhoPar_hashBag_left {ps : List Pattern} {Q : Pattern}
    (hQ : ∀ qs, Q ≠ .collection .hashBag qs none) :
    rhoPar (.collection .hashBag ps none) Q = .collection .hashBag (ps ++ [Q]) none := by
  cases Q with
  | collection ct elems rest =>
    cases ct with
    | hashBag => cases rest with
      | none => exact absurd rfl (hQ elems)
      | some _ => rfl
    | vec | hashSet => rfl
  | bvar _ | fvar _ | apply _ _ | lambda _ | multiLambda _ _ | subst _ _ => rfl

/-- If P is not a hashBag-none collection, rhoPar with hashBag-none RHS prepends P. -/
private theorem rhoPar_hashBag_right {P : Pattern} {qs : List Pattern}
    (hP : ∀ ps, P ≠ .collection .hashBag ps none) :
    rhoPar P (.collection .hashBag qs none) = .collection .hashBag (P :: qs) none := by
  cases P with
  | collection ct elems rest =>
    cases ct with
    | hashBag => cases rest with
      | none => exact absurd rfl (hP elems)
      | some _ => rfl
    | vec | hashSet => rfl
  | bvar _ | fvar _ | apply _ _ | lambda _ | multiLambda _ _ | subst _ _ => rfl

/-- If neither is a hashBag-none collection, rhoPar creates a pair list. -/
private theorem rhoPar_neither {P Q : Pattern}
    (hP : ∀ ps, P ≠ .collection .hashBag ps none)
    (hQ : ∀ qs, Q ≠ .collection .hashBag qs none) :
    rhoPar P Q = .collection .hashBag [P, Q] none := by
  cases P with
  | collection ct elems rest =>
    cases ct with
    | hashBag => cases rest with
      | none => exact absurd rfl (hP elems)
      | some _ =>
        cases Q with
        | collection ct₂ elems₂ rest₂ => cases ct₂ with
          | hashBag => cases rest₂ with
            | none => exact absurd rfl (hQ elems₂)
            | some _ => rfl
          | vec | hashSet => rfl
        | bvar _ | fvar _ | apply _ _ | lambda _ | multiLambda _ _ | subst _ _ => rfl
    | vec | hashSet =>
      cases Q with
      | collection ct₂ elems₂ rest₂ => cases ct₂ with
        | hashBag => cases rest₂ with
          | none => exact absurd rfl (hQ elems₂)
          | some _ => rfl
        | vec | hashSet => rfl
      | bvar _ | fvar _ | apply _ _ | lambda _ | multiLambda _ _ | subst _ _ => rfl
  | bvar _ | fvar _ | apply _ _ | lambda _ | multiLambda _ _ | subst _ _ =>
    cases Q with
    | collection ct₂ elems₂ rest₂ => cases ct₂ with
      | hashBag => cases rest₂ with
        | none => exact absurd rfl (hQ elems₂)
        | some _ => rfl
      | vec | hashSet => rfl
    | bvar _ | fvar _ | apply _ _ | lambda _ | multiLambda _ _ | subst _ _ => rfl

/-- For noExplicitSubst patterns with fvar→fvar substitution:
    if P is not hashBag-none, then applySubst P is also not hashBag-none. -/
private theorem applySubst_fvar_preserves_non_hashBag {y z : String} {P : Pattern}
    (hnes : noExplicitSubst P = true)
    (hP : ∀ ps, P ≠ .collection .hashBag ps none) :
    ∀ ps', applySubst (SubstEnv.extend SubstEnv.empty y (.fvar z)) P ≠
      .collection .hashBag ps' none := by
  intro ps' heq
  cases P with
  | bvar n => simp [applySubst] at heq
  | fvar x =>
    by_cases hxy : x = y
    · subst hxy
      simp only [applySubst, SubstEnv.find_extend_empty_eq] at heq
      exact nomatch heq
    · simp only [applySubst, SubstEnv.find_extend_empty_ne (Ne.symm hxy)] at heq
      exact nomatch heq
  | apply c args => simp only [applySubst] at heq; cases heq
  | lambda body => simp only [applySubst] at heq; cases heq
  | multiLambda n body => simp only [applySubst] at heq; cases heq
  | subst body repl => exact absurd hnes Bool.false_ne_true
  | collection ct elems rest =>
    simp only [applySubst] at heq; cases heq
    exact hP elems rfl

/-- applySubst with fvar→fvar env distributes through rhoPar for noExplicitSubst patterns. -/
theorem applySubst_fvar_rhoPar_comm (y z : String) (P Q : Pattern)
    (hnesP : noExplicitSubst P = true) (hnesQ : noExplicitSubst Q = true) :
    applySubst (SubstEnv.extend SubstEnv.empty y (.fvar z)) (rhoPar P Q) =
      rhoPar (applySubst (SubstEnv.extend SubstEnv.empty y (.fvar z)) P)
             (applySubst (SubstEnv.extend SubstEnv.empty y (.fvar z)) Q) := by
  set env := SubstEnv.extend SubstEnv.empty y (.fvar z) with henv
  by_cases hPb : IsHashBagNone P <;> by_cases hQb : IsHashBagNone Q
  · -- Case 1: Both hashBag-none
    obtain ⟨ps, rfl⟩ := hPb; obtain ⟨qs, rfl⟩ := hQb
    simp [rhoPar, applySubst, List.map_append]
  · -- Case 2: P hashBag-none, Q not
    obtain ⟨ps, rfl⟩ := hPb
    have hQb' := not_isHashBagNone_iff.mp hQb
    rw [rhoPar_hashBag_left hQb']
    simp only [applySubst, List.map_append, List.map_cons, List.map_nil]
    exact (rhoPar_hashBag_left (applySubst_fvar_preserves_non_hashBag hnesQ hQb')).symm
  · -- Case 3: P not hashBag-none, Q hashBag-none
    obtain ⟨qs, rfl⟩ := hQb
    have hPb' := not_isHashBagNone_iff.mp hPb
    rw [rhoPar_hashBag_right hPb']
    simp only [applySubst, List.map_cons]
    exact (rhoPar_hashBag_right (applySubst_fvar_preserves_non_hashBag hnesP hPb')).symm
  · -- Case 4: Neither hashBag-none
    have hPb' := not_isHashBagNone_iff.mp hPb
    have hQb' := not_isHashBagNone_iff.mp hQb
    rw [rhoPar_neither hPb' hQb']
    simp only [applySubst, List.map_cons, List.map_nil]
    exact (rhoPar_neither (applySubst_fvar_preserves_non_hashBag hnesP hPb')
                          (applySubst_fvar_preserves_non_hashBag hnesQ hQb')).symm

/-! ## Encoding commutes with free-variable substitution -/

/-- Core lemma: fvar→fvar substitution on encoding equals encoding of π-substituted process.

    `applySubst [(y, .fvar z)] (encode Q n v) = encode (Q.substitute y z) n v`

    Requires Barendregt: y and z are distinct from all binding variables in Q. -/
theorem encode_rf_subst_fvar {Q : Process} (hrf : RestrictionFree Q)
    (y z : Name) (n v : String) (hyz : y ≠ z) (hb : BarendregtFor y z Q) :
    applySubst (SubstEnv.extend SubstEnv.empty y (.fvar z)) (encode Q n v) =
      encode (Q.substitute y z) n v := by
  induction Q generalizing n with
  | nil => simp [encode, rhoNil, applySubst, Process.substitute]
  | par P R ihP ihR =>
    simp only [encode, Process.substitute]
    conv_rhs => rw [← ihP hrf.1 (n ++ "_L") hb.1, ← ihR hrf.2 (n ++ "_R") hb.2]
    exact applySubst_fvar_rhoPar_comm y z _ _
      (encode_noExplicitSubst P (n ++ "_L") v) (encode_noExplicitSubst R (n ++ "_R") v)
  | input x w R ih =>
    have ⟨hyw, hzw, hbR⟩ := hb
    show applySubst _ (.apply "PInput" [piNameToRhoName x,
           .lambda (closeFVar 0 w (encode R n v))]) = _
    simp only [applySubst, List.map_cons, List.map_nil, piNameToRhoName]
    -- Body: applySubst commutes with closeFVar 0 w (since y ≠ w and z ≠ w)
    have hbody : applySubst (SubstEnv.extend SubstEnv.empty y (.fvar z))
        (closeFVar 0 w (encode R n v)) =
        closeFVar 0 w (applySubst (SubstEnv.extend SubstEnv.empty y (.fvar z))
          (encode R n v)) :=
      applySubst_closeFVar_comm_single hyw hzw (encode_noExplicitSubst R n v)
    rw [hbody, ih hrf n hbR]
    -- Match π-substitute structure
    simp only [Process.substitute]
    have hwy : w ≠ y := Ne.symm hyw
    simp only [hwy, ↓reduceIte]
    by_cases hxy : x = y
    · subst hxy
      simp only [↓reduceIte, encode, rhoInput, piNameToRhoName,
                 SubstEnv.find_extend_empty_eq]
    · simp only [hxy, ↓reduceIte, encode, rhoInput, piNameToRhoName,
                 SubstEnv.find_extend_empty_ne (Ne.symm hxy)]
  | output x w =>
    simp only [encode, rhoOutput, rhoDrop, piNameToRhoName, Process.substitute,
               applySubst, List.map_cons, List.map_nil]
    congr 1; congr 1
    · -- Channel: .fvar x through substitution
      by_cases hxy : x = y
      · rw [hxy, SubstEnv.find_extend_empty_eq]; simp
      · rw [SubstEnv.find_extend_empty_ne (Ne.symm hxy)]; simp [hxy]
    · -- Payload: PDrop(.fvar w) through substitution
      congr 1; congr 1; congr 1
      by_cases hyw : w = y
      · rw [hyw, SubstEnv.find_extend_empty_eq]; simp
      · rw [SubstEnv.find_extend_empty_ne (Ne.symm hyw)]; simp [hyw]
  | nu _ _ => exact absurd hrf id
  | replicate _ _ _ => exact absurd hrf id

/-! ## Open-Close-Subst: the key encoding-substitution commutation -/

/-- Encoding commutes with open/close substitution (Barendregt).

    Derived cleanly from:
    1. `open_close_id`: openBVar k (.fvar y) (closeFVar k y p) = p  (when lc_at k)
    2. `subst_intro`: applySubst [(y, u)] (openBVar 0 (.fvar y) p) = openBVar 0 u p  (when y fresh)
    3. `encode_rf_subst_fvar`: applySubst [(y, .fvar z)] (encode Q) = encode (Q.subst y z) -/
theorem encode_rf_open_close_subst {Q : Process} (hrf : RestrictionFree Q)
    (y z : Name) (n v : String) (hyz : y ≠ z) (hb : BarendregtFor y z Q) :
    openBVar 0 (.fvar z) (closeFVar 0 y (encode Q n v)) =
      encode (Q.substitute y z) n v := by
  -- Step 1: y is fresh in closeFVar 0 y (encode Q n v)
  have hfresh := isFresh_closeFVar_self 0 y (encode Q n v)
  -- Step 2: closeFVar 0 y (encode Q n v) has no explicit subst
  have hnes := noExplicitSubst_closeFVar (k := 0) (x := y) (encode_noExplicitSubst Q n v)
  -- Step 3: By subst_intro, applySubst [(y, .fvar z)] (openBVar 0 (.fvar y) p) = openBVar 0 (.fvar z) p
  -- where p = closeFVar 0 y (encode Q n v)
  have h1 := subst_intro (z := y) (u := .fvar z)
    (p := closeFVar 0 y (encode Q n v)) hfresh hnes
  -- h1 : applySubst [(y, .fvar z)] (openBVar 0 (.fvar y) (closeFVar 0 y (encode Q n v)))
  --     = openBVar 0 (.fvar z) (closeFVar 0 y (encode Q n v))
  -- Step 4: open_close_id: openBVar 0 (.fvar y) (closeFVar 0 y (encode Q n v)) = encode Q n v
  have h2 := open_close_id 0 y (encode Q n v) (encode_rf_lc hrf n v)
  -- Step 5: Combine: LHS = applySubst [(y, .fvar z)] (encode Q n v)
  rw [← h1, h2]
  -- Step 6: By encode_rf_subst_fvar
  exact encode_rf_subst_fvar hrf y z n v hyz hb

/-! ## Forward COMM Case -/

open Mettapedia.OSLF.RhoCalculus (ReducesStar)

/-- The encoding of `par (input x y P) (output x z)` is a 2-element hashBag. -/
private theorem encode_par_io (x y : Name) (P : Process) (z : Name) (n v : String) :
    encode (.par (.input x y P) (.output x z)) n v =
      .collection .hashBag
        [rhoInput (.fvar x) y (encode P (n ++ "_L") v),
         rhoOutput (.fvar x) (rhoDrop (.fvar z))] none := by
  show rhoPar (rhoInput (piNameToRhoName x) y (encode P (n ++ "_L") v))
              (rhoOutput (piNameToRhoName x) (rhoDrop (piNameToRhoName z))) = _
  rfl

/-- COMM case of forward simulation for RF processes.

    π-COMM: `(input x y P) | (output x z) ⇝ P.substitute y z`
    ρ-encoding: reduces in one step (via equiv + COMM + SC) to encode of result.

    The proof chain:
    1. par_comm swaps PInput/POutput to match ρ-COMM order
    2. ρ-COMM fires, producing commSubst body (PDrop(.fvar z))
    3. quote_drop: NQuote(PDrop(.fvar z)) ≡ .fvar z
    4. openBVar_SC_replacement bridges to openBVar 0 (.fvar z) body
    5. encode_rf_open_close_subst gives encode(P.substitute y z)
    6. encode_rf_ns_independent removes namespace dependency
    7. par_singleton unwraps the singleton bag -/
theorem forward_comm_rf {P : Process} (hrf : RestrictionFree P)
    (x y z : Name) (n v : String)
    (hyz : y ≠ z) (hb : BarendregtFor y z P) :
    ∃ T, Nonempty (ReducesStar (encode (.par (.input x y P) (.output x z)) n v) T) ∧
         (T ≡ᵨ encode (P.substitute y z) n v) := by
  set nL := n ++ "_L"
  set body := closeFVar 0 y (encode P nL v)
  -- The encoding unfolds to a 2-element hashBag [PInput, POutput]
  rw [encode_par_io]
  refine ⟨encode (P.substitute y z) n v, ?_, refl _⟩
  constructor
  apply ReducesStar.single
  apply Mettapedia.OSLF.RhoCalculus.Reduction.Reduces.equiv
  -- Pre-SC: swap PInput/POutput to match ρ-COMM order
  · exact par_comm _ _
  -- ρ-COMM fires (rest = [])
  · exact Mettapedia.OSLF.RhoCalculus.Reduction.Reduces.comm
  -- Post-SC: {commSubst body (PDrop(.fvar z))} ≡ᵨ encode(P.subst y z) n v
  · -- Key intermediate facts
    have h_open_sc : openBVar 0 (.apply "NQuote" [.apply "PDrop" [.fvar z]]) body ≡ᵨ
                     openBVar 0 (.fvar z) body :=
      openBVar_SC_replacement (quote_drop (.fvar z)) body 0
    have h_target : openBVar 0 (.fvar z) body = encode (P.substitute y z) n v :=
      (encode_rf_open_close_subst hrf y z nL v hyz hb).trans
        (encode_rf_ns_independent (rf_substitute hrf y z) nL n v)
    -- Element-wise SC: commSubst body q ≡ᵨ encode(P.subst y z) n v
    have h_elt : commSubst body (.apply "PDrop" [.fvar z]) ≡ᵨ
                 encode (P.substitute y z) n v := by
      show openBVar 0 (.apply "NQuote" [.apply "PDrop" [.fvar z]]) body ≡ᵨ _
      rw [← h_target]
      exact h_open_sc
    -- Lift to singleton bag, then unwrap via par_singleton
    set target := encode (P.substitute y z) n v
    exact trans _ (.collection .hashBag [target] none) _
      (par_cong _ _ (by simp) (fun i h₁ h₂ => by
        have h₁' : i < 1 := h₁
        have : i = 0 := by omega
        subst this; exact h_elt))
      (par_singleton _)

/-! ## Lifting Reductions Through rhoPar -/

/-- rhoPar A B is SC-equivalent to the "two-element" collection {[A, B]}.
    This lets us lift component-wise reductions uniformly. -/
private theorem rhoPar_to_two (A B : Pattern) :
    rhoPar A B ≡ᵨ .collection .hashBag [A, B] none := by
  by_cases hA : IsHashBagNone A <;> by_cases hB : IsHashBagNone B
  · -- Both hashBag: {as ++ bs} ≡ {[{as}, {bs}]}
    obtain ⟨as, rfl⟩ := hA; obtain ⟨bs, rfl⟩ := hB
    show .collection .hashBag (as ++ bs) none ≡ᵨ _
    -- Chain: {as ++ bs} ≡ {bs ++ as} ≡ {bs ++ [{as}]} ≡ {{as} :: bs} ≡ {[{as}, {bs}]}
    exact trans _ _ _ (par_perm _ _ List.perm_append_comm)
      (trans _ _ _ (symm _ _ (par_flatten bs as))
        (trans _ _ _ (par_perm _ _ List.perm_append_comm)
          (symm _ _ (par_flatten [.collection .hashBag as none] bs))))
  · -- A hashBag, B not: {as ++ [B]} ≡ {[{as}, B]}
    obtain ⟨as, rfl⟩ := hA
    rw [rhoPar_hashBag_left (not_isHashBagNone_iff.mp hB)]
    -- Chain: {as ++ [B]} ≡ {B :: as} ≡ {[B, {as}]} ≡ {[{as}, B]}
    exact trans _ _ _ (par_perm _ _ List.perm_append_comm)
      (trans _ _ _ (symm _ _ (par_flatten [B] as))
        (par_comm _ _))
  · -- A not, B hashBag: {A :: bs} ≡ {[A, {bs}]}
    obtain ⟨bs, rfl⟩ := hB
    rw [rhoPar_hashBag_right (not_isHashBagNone_iff.mp hA)]
    exact symm _ _ (par_flatten [A] bs)
  · -- Neither: {[A, B]} = {[A, B]}
    rw [rhoPar_neither (not_isHashBagNone_iff.mp hA) (not_isHashBagNone_iff.mp hB)]
    exact refl _

/-- Lifting ReducesStar to the head of a 2-element collection. -/
private noncomputable def ReducesStar_two_left {A T B : Pattern}
    (h : ReducesStar A T) :
    ReducesStar (.collection .hashBag [A, B] none) (.collection .hashBag [T, B] none) := by
  induction h with
  | refl => exact ReducesStar.refl _
  | step h_red _ ih =>
    exact ReducesStar.step
      (Mettapedia.OSLF.RhoCalculus.Reduction.Reduces.par h_red) ih

/-- Lifting ReducesStar to the second element of a 2-element collection. -/
private noncomputable def ReducesStar_two_right {A B T : Pattern}
    (h : ReducesStar B T) :
    ReducesStar (.collection .hashBag [A, B] none) (.collection .hashBag [A, T] none) := by
  induction h with
  | refl => exact ReducesStar.refl _
  | step h_red _ ih =>
    exact ReducesStar.step
      (Mettapedia.OSLF.RhoCalculus.Reduction.Reduces.par_any
        (before := [A]) (after := []) h_red) ih

/-- SC on the source can be folded into the first reduction step. -/
private theorem ReducesStar_equiv_pre {p p' q : Pattern}
    (hsc : p ≡ᵨ p') (h : Nonempty (ReducesStar p' q)) :
    ∃ T, Nonempty (ReducesStar p T) ∧ (T ≡ᵨ q) := by
  obtain ⟨h⟩ := h
  match h with
  | .refl _ => exact ⟨p, ⟨ReducesStar.refl p⟩, hsc⟩
  | .step h_first h_rest =>
    exact ⟨q, ⟨ReducesStar.step
      (Mettapedia.OSLF.RhoCalculus.Reduction.Reduces.equiv hsc h_first (refl _))
      h_rest⟩, refl _⟩

/-! ## PAR Congruence: Lifting through rhoPar -/

/-- SC on the left component propagates through rhoPar. -/
private theorem rhoPar_SC_left {A A' B : Pattern} (h : A ≡ᵨ A') :
    rhoPar A B ≡ᵨ rhoPar A' B :=
  trans _ (.collection .hashBag [A, B] none) _
    (rhoPar_to_two A B)
    (trans _ (.collection .hashBag [A', B] none) _
      (par_cong [A, B] [A', B] rfl (fun i h₁ h₂ => by
        have h₁' : i < 2 := h₁
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl
        · exact h
        · exact refl _))
      (symm _ _ (rhoPar_to_two A' B)))

/-- SC on the right component propagates through rhoPar. -/
private theorem rhoPar_SC_right {A B B' : Pattern} (h : B ≡ᵨ B') :
    rhoPar A B ≡ᵨ rhoPar A B' :=
  trans _ (.collection .hashBag [A, B] none) _
    (rhoPar_to_two A B)
    (trans _ (.collection .hashBag [A, B'] none) _
      (par_cong [A, B] [A, B'] rfl (fun i h₁ h₂ => by
        have h₁' : i < 2 := h₁
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl
        · exact refl _
        · exact h))
      (symm _ _ (rhoPar_to_two A B')))

/-- Forward simulation lifts through left component of par.

    Given IH: encode(P₁) ⇝* T₁ ≡ᵨ encode(P₁'),
    Show: encode(P₁ ||| Q) ⇝* T ≡ᵨ encode(P₁' ||| Q). -/
theorem forward_par_left_rf (P₁' : Process) {Q : Process}
    (hrfQ : RestrictionFree Q) (n v : String)
    (ih : ∃ T, Nonempty (ReducesStar (encode P₁ (n ++ "_L") v) T) ∧
               (T ≡ᵨ encode P₁' (n ++ "_L") v)) :
    ∃ T, Nonempty (ReducesStar (encode (.par P₁ Q) n v) T) ∧
         (T ≡ᵨ encode (.par P₁' Q) n v) := by
  obtain ⟨T₁, ⟨hT₁⟩, hsc₁⟩ := ih
  set eQ := encode Q (n ++ "_R") v
  -- Lift ReducesStar through {[_, eQ]} form
  have h_two : Nonempty (ReducesStar
      (.collection .hashBag [encode P₁ (n ++ "_L") v, eQ] none)
      (.collection .hashBag [T₁, eQ] none)) := ⟨ReducesStar_two_left hT₁⟩
  -- Bridge from rhoPar form to {[_, eQ]} form
  obtain ⟨T, ⟨hT⟩, hsc⟩ := ReducesStar_equiv_pre
    (rhoPar_to_two (encode P₁ (n ++ "_L") v) eQ) h_two
  refine ⟨T, ⟨hT⟩, ?_⟩
  -- SC chain: T ≡ᵨ {[T₁, eQ]} ≡ᵨ {[encode P₁' nL v, eQ]} ≡ᵨ rhoPar (encode P₁' nL v) eQ
  exact trans _ (.collection .hashBag [T₁, eQ] none) _
    hsc
    (trans _ (.collection .hashBag [encode P₁' (n ++ "_L") v, eQ] none) _
      (par_cong [T₁, eQ] [encode P₁' (n ++ "_L") v, eQ] rfl (fun i h₁ h₂ => by
        have h₁' : i < 2 := h₁
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl
        · exact hsc₁
        · exact refl _))
      (symm _ _ (rhoPar_to_two (encode P₁' (n ++ "_L") v) eQ)))

/-- Forward simulation lifts through right component of par. -/
theorem forward_par_right_rf {P₁ : Process} (Q' : Process)
    (hrf₁ : RestrictionFree P₁) (n v : String)
    (ih : ∃ T, Nonempty (ReducesStar (encode Q (n ++ "_R") v) T) ∧
               (T ≡ᵨ encode Q' (n ++ "_R") v)) :
    ∃ T, Nonempty (ReducesStar (encode (.par P₁ Q) n v) T) ∧
         (T ≡ᵨ encode (.par P₁ Q') n v) := by
  obtain ⟨T₁, ⟨hT₁⟩, hsc₁⟩ := ih
  set eP := encode P₁ (n ++ "_L") v
  -- Lift ReducesStar through {[eP, _]} form
  have h_two : Nonempty (ReducesStar
      (.collection .hashBag [eP, encode Q (n ++ "_R") v] none)
      (.collection .hashBag [eP, T₁] none)) := ⟨ReducesStar_two_right hT₁⟩
  -- Bridge from rhoPar form to {[eP, _]} form
  obtain ⟨T, ⟨hT⟩, hsc⟩ := ReducesStar_equiv_pre
    (rhoPar_to_two eP (encode Q (n ++ "_R") v)) h_two
  refine ⟨T, ⟨hT⟩, ?_⟩
  -- SC chain: T ≡ᵨ {[eP, T₁]} ≡ᵨ {[eP, encode Q' nR v]} ≡ᵨ rhoPar eP (encode Q' nR v)
  exact trans _ (.collection .hashBag [eP, T₁] none) _
    hsc
    (trans _ (.collection .hashBag [eP, encode Q' (n ++ "_R") v] none) _
      (par_cong [eP, T₁] [eP, encode Q' (n ++ "_R") v] rfl (fun i h₁ h₂ => by
        have h₁' : i < 2 := h₁
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl
        · exact refl _
        · exact hsc₁))
      (symm _ _ (rhoPar_to_two eP (encode Q' (n ++ "_R") v))))

/-! ## Restriction-Free Structural Congruence and Reduction -/

/-- Structural congruence restricted to the RF fragment.
    Excludes: input_cong, nu_cong, replicate_cong, nu_nil, nu_par,
    nu_swap, alpha_input, alpha_nu, alpha_replicate, replicate_unfold.
    This ensures `rfsc_preserves_rf` holds as an iff. -/
inductive StructuralCongruenceRF : Process → Process → Type where
  | refl (P : Process) :
      StructuralCongruenceRF P P
  | symm (P Q : Process) :
      StructuralCongruenceRF P Q →
      StructuralCongruenceRF Q P
  | trans (P Q R : Process) :
      StructuralCongruenceRF P Q →
      StructuralCongruenceRF Q R →
      StructuralCongruenceRF P R
  | par_cong (P P' Q Q' : Process) :
      StructuralCongruenceRF P P' →
      StructuralCongruenceRF Q Q' →
      StructuralCongruenceRF (P ||| Q) (P' ||| Q')
  | par_comm (P Q : Process) :
      StructuralCongruenceRF (P ||| Q) (Q ||| P)
  | par_assoc (P Q R : Process) :
      StructuralCongruenceRF ((P ||| Q) ||| R) (P ||| (Q ||| R))
  | par_nil_left (P : Process) :
      StructuralCongruenceRF (Process.nil ||| P) P
  | par_nil_right (P : Process) :
      StructuralCongruenceRF (P ||| Process.nil) P

local notation:50 P " ≡ᵣ " Q => StructuralCongruenceRF P Q

/-- RFSC preserves the RestrictionFree predicate (iff). -/
theorem rfsc_preserves_rf : (P ≡ᵣ Q) → (RestrictionFree P ↔ RestrictionFree Q) := by
  intro h
  induction h with
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | par_cong _ _ _ _ _ _ ih₁ ih₂ =>
    show RestrictionFree _ ∧ RestrictionFree _ ↔ RestrictionFree _ ∧ RestrictionFree _
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨ih₁.mp h₁, ih₂.mp h₂⟩,
           fun ⟨h₁, h₂⟩ => ⟨ih₁.mpr h₁, ih₂.mpr h₂⟩⟩
  | par_comm P Q =>
    show RestrictionFree P ∧ RestrictionFree Q ↔ RestrictionFree Q ∧ RestrictionFree P
    exact And.comm
  | par_assoc P Q R =>
    show (RestrictionFree P ∧ RestrictionFree Q) ∧ RestrictionFree R ↔
         RestrictionFree P ∧ (RestrictionFree Q ∧ RestrictionFree R)
    exact and_assoc
  | par_nil_left P =>
    show True ∧ RestrictionFree P ↔ RestrictionFree P
    simp
  | par_nil_right P =>
    show RestrictionFree P ∧ True ↔ RestrictionFree P
    simp

/-- Reduction restricted to the RF fragment. Uses RFSC instead of full SC,
    and drops the `res` rule. -/
inductive ReducesRF : Process → Process → Type where
  | comm (x : Name) (y z : Name) (P : Process) :
      ReducesRF
        (Process.par (Process.input x y P) (Process.output x z))
        (P.substitute y z)
  | par_left (P P' Q : Process) :
      ReducesRF P P' →
      ReducesRF (P ||| Q) (P' ||| Q)
  | par_right (P Q Q' : Process) :
      ReducesRF Q Q' →
      ReducesRF (P ||| Q) (P ||| Q')
  | struct (P P' Q Q' : Process) :
      StructuralCongruenceRF P P' →
      ReducesRF P' Q' →
      StructuralCongruenceRF Q' Q →
      ReducesRF P Q

notation:50 P " ⇝ᵣ " Q => ReducesRF P Q

/-- RF is preserved by RF-reduction. -/
theorem reducesRF_preserves_rf : (P ⇝ᵣ Q) → RestrictionFree P → RestrictionFree Q := by
  intro h hrf
  induction h with
  | comm _ y z P => exact rf_substitute (P := P) hrf.1 y z
  | par_left _ _ Q _ ih => exact ⟨ih hrf.1, hrf.2⟩
  | par_right P _ _ _ ih => exact ⟨hrf.1, ih hrf.2⟩
  | struct _ P' _ _ hsc₁ _ hsc₂ ih =>
    exact (rfsc_preserves_rf hsc₂).mp (ih ((rfsc_preserves_rf hsc₁).mp hrf))

/-! ## rhoPar SC Lemmas -/

/-- Commutativity of rhoPar under ρ-SC. -/
private theorem rhoPar_comm_sc (A B : Pattern) : rhoPar A B ≡ᵨ rhoPar B A :=
  trans _ (.collection .hashBag [A, B] none) _
    (rhoPar_to_two A B)
    (trans _ (.collection .hashBag [B, A] none) _
      (par_comm _ _)
      (symm _ _ (rhoPar_to_two B A)))

/-- rhoPar with rhoNil on the left is SC to P. -/
private theorem rhoPar_nil_left_sc (P : Pattern) : rhoPar rhoNil P ≡ᵨ P := by
  by_cases hP : IsHashBagNone P
  · obtain ⟨ps, rfl⟩ := hP
    -- rhoPar {[]} {ps} = {[] ++ ps} = {ps}
    show .collection .hashBag ([] ++ ps) none ≡ᵨ .collection .hashBag ps none
    exact refl _
  · -- rhoPar {[]} P = {[P]} (since P is not hashBag)
    rw [show rhoNil = .collection .hashBag [] none from rfl,
        rhoPar_hashBag_left (not_isHashBagNone_iff.mp hP)]
    -- {[] ++ [P]} = {[P]} ≡ P
    exact par_singleton _

/-- rhoPar with rhoNil on the right is SC to P. -/
private theorem rhoPar_nil_right_sc (P : Pattern) : rhoPar P rhoNil ≡ᵨ P :=
  trans _ (rhoPar rhoNil P) _
    (rhoPar_comm_sc P rhoNil)
    (rhoPar_nil_left_sc P)

/-- Associativity of rhoPar under ρ-SC. -/
private theorem rhoPar_assoc_sc (A B C : Pattern) :
    rhoPar (rhoPar A B) C ≡ᵨ rhoPar A (rhoPar B C) := by
  -- LHS chain: rhoPar(rhoPar A B, C) ≡ {[A,B,C]} via comm + flatten
  have lhs_s1 : rhoPar (rhoPar A B) C ≡ᵨ
      .collection .hashBag [rhoPar A B, C] none :=
    rhoPar_to_two (rhoPar A B) C
  have lhs_s2 : .collection .hashBag [rhoPar A B, C] none ≡ᵨ
      .collection .hashBag [C, rhoPar A B] none :=
    par_comm _ _
  have lhs_s3 : .collection .hashBag [C, rhoPar A B] none ≡ᵨ
      .collection .hashBag [C, .collection .hashBag [A, B] none] none :=
    par_cong [C, rhoPar A B] [C, .collection .hashBag [A, B] none] rfl
      (fun i h₁ h₂ => by
        have h₁' : i < 2 := h₁
        rcases show i = 0 ∨ i = 1 by omega with rfl | rfl
        · exact refl _
        · exact rhoPar_to_two A B)
  have lhs_s4 : .collection .hashBag [C, .collection .hashBag [A, B] none] none ≡ᵨ
      .collection .hashBag [C, A, B] none :=
    par_flatten_two C A B
  have lhs_s5 : .collection .hashBag [C, A, B] none ≡ᵨ
      .collection .hashBag [A, B, C] none :=
    par_perm _ _ (@List.perm_append_comm Pattern [C] [A, B])
  have lhs : rhoPar (rhoPar A B) C ≡ᵨ .collection .hashBag [A, B, C] none :=
    let t1 := trans _ _ _ lhs_s1 lhs_s2
    let t2 := trans _ _ _ t1 lhs_s3
    let t3 := trans _ _ _ t2 lhs_s4
    trans _ _ _ t3 lhs_s5
  -- RHS chain: rhoPar(A, rhoPar B C) ≡ {[A,B,C]} via par_flatten_two
  have rhs_s1 : rhoPar A (rhoPar B C) ≡ᵨ
      .collection .hashBag [A, rhoPar B C] none :=
    rhoPar_to_two A (rhoPar B C)
  have rhs_s2 : .collection .hashBag [A, rhoPar B C] none ≡ᵨ
      .collection .hashBag [A, .collection .hashBag [B, C] none] none :=
    par_cong [A, rhoPar B C] [A, .collection .hashBag [B, C] none] rfl
      (fun i h₁ h₂ => by
        have h₁' : i < 2 := h₁
        rcases show i = 0 ∨ i = 1 by omega with rfl | rfl
        · exact refl _
        · exact rhoPar_to_two B C)
  have rhs_s3 : .collection .hashBag [A, .collection .hashBag [B, C] none] none ≡ᵨ
      .collection .hashBag [A, B, C] none :=
    par_flatten_two A B C
  have rhs : rhoPar A (rhoPar B C) ≡ᵨ .collection .hashBag [A, B, C] none :=
    let t1 := trans _ _ _ rhs_s1 rhs_s2
    trans _ _ _ t1 rhs_s3
  exact trans _ (.collection .hashBag [A, B, C] none) _ lhs (symm _ _ rhs)

/-! ## Encoding Preserves RFSC -/

/-- The encoding preserves restriction-free structural congruence. -/
theorem encode_preserves_rfsc (h : P ≡ᵣ Q) (hrf : RestrictionFree P)
    (n v : String) : encode P n v ≡ᵨ encode Q n v := by
  induction h generalizing n v with
  | refl _ => exact refl _
  | symm P Q hPQ ih =>
    exact symm _ _ (ih ((rfsc_preserves_rf hPQ).mpr hrf) n v)
  | trans P Q R hPQ hQR ihPQ ihQR =>
    exact trans _ (encode Q n v) _
      (ihPQ hrf n v)
      (ihQR ((rfsc_preserves_rf hPQ).mp hrf) n v)
  | par_cong P P' Q Q' _ _ ihP ihQ =>
    show rhoPar (encode P (n ++ "_L") v) (encode Q (n ++ "_R") v) ≡ᵨ
         rhoPar (encode P' (n ++ "_L") v) (encode Q' (n ++ "_R") v)
    exact trans _ (rhoPar (encode P' (n ++ "_L") v) (encode Q (n ++ "_R") v)) _
      (rhoPar_SC_left (ihP hrf.1 (n ++ "_L") v))
      (rhoPar_SC_right (ihQ hrf.2 (n ++ "_R") v))
  | par_comm P Q =>
    show rhoPar (encode P (n ++ "_L") v) (encode Q (n ++ "_R") v) ≡ᵨ
         rhoPar (encode Q (n ++ "_L") v) (encode P (n ++ "_R") v)
    rw [encode_rf_ns_independent hrf.1 (n ++ "_L") (n ++ "_R") v,
        encode_rf_ns_independent hrf.2 (n ++ "_R") (n ++ "_L") v]
    exact rhoPar_comm_sc _ _
  | par_assoc P Q R =>
    have hrfP := hrf.1.1; have hrfQ := hrf.1.2; have hrfR := hrf.2
    show rhoPar (rhoPar (encode P ((n ++ "_L") ++ "_L") v)
                        (encode Q ((n ++ "_L") ++ "_R") v))
               (encode R (n ++ "_R") v) ≡ᵨ
         rhoPar (encode P (n ++ "_L") v)
               (rhoPar (encode Q ((n ++ "_R") ++ "_L") v)
                       (encode R ((n ++ "_R") ++ "_R") v))
    rw [encode_rf_ns_independent hrfP ((n ++ "_L") ++ "_L") n v,
        encode_rf_ns_independent hrfQ ((n ++ "_L") ++ "_R") n v,
        encode_rf_ns_independent hrfR (n ++ "_R") n v,
        encode_rf_ns_independent hrfP (n ++ "_L") n v,
        encode_rf_ns_independent hrfQ ((n ++ "_R") ++ "_L") n v,
        encode_rf_ns_independent hrfR ((n ++ "_R") ++ "_R") n v]
    exact rhoPar_assoc_sc _ _ _
  | par_nil_left P =>
    show rhoPar rhoNil (encode P (n ++ "_R") v) ≡ᵨ encode P n v
    rw [encode_rf_ns_independent hrf.2 (n ++ "_R") n v]
    exact rhoPar_nil_left_sc _
  | par_nil_right P =>
    show rhoPar (encode P (n ++ "_L") v) rhoNil ≡ᵨ encode P n v
    rw [encode_rf_ns_independent hrf.1 (n ++ "_L") n v]
    exact rhoPar_nil_right_sc _

/-! ## Barendregt Condition for RF Reductions -/

/-- Barendregt condition on an RF reduction derivation: every COMM step has
    `y ≠ z` and `BarendregtFor y z P`. -/
def CommSafe : ReducesRF P Q → Prop
  | .comm _ y z P => y ≠ z ∧ BarendregtFor y z P
  | .par_left _ _ _ h => CommSafe h
  | .par_right _ _ _ h => CommSafe h
  | .struct _ _ _ _ _ h _ => CommSafe h

/-! ## Forward Simulation Theorems -/

/-- Single-step forward simulation for the RF fragment.
    If `P ⇝ᵣ Q` (via ReducesRF), RF P holds, and every COMM is safe,
    then the ρ-encoding simulates the step. -/
theorem forward_single_step_rf {P Q : Process}
    (h : P ⇝ᵣ Q) (hrf : RestrictionFree P) (hsafe : CommSafe h)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧
         (T ≡ᵨ encode Q n v) := by
  induction h generalizing n v with
  | comm x y z R =>
    exact forward_comm_rf (P := R) hrf.1 x y z n v hsafe.1 hsafe.2
  | par_left P P' Q h ih =>
    exact forward_par_left_rf P' (hrf.2) n v (ih hrf.1 hsafe (n ++ "_L") v)
  | par_right P Q Q' h ih =>
    exact forward_par_right_rf Q' (hrf.1) n v (ih hrf.2 hsafe (n ++ "_R") v)
  | struct P₀ P₀' Q₀ Q₀' hsc₁ hred hsc₂ ih =>
    have hrf' := (rfsc_preserves_rf hsc₁).mp hrf
    obtain ⟨T, ⟨hT⟩, hscT⟩ := ih hrf' hsafe n v
    have henc₁ := encode_preserves_rfsc hsc₁ hrf n v
    have hrfQ₀' := reducesRF_preserves_rf hred hrf'
    have henc₂ := encode_preserves_rfsc hsc₂ hrfQ₀' n v
    obtain ⟨T', ⟨hT'⟩, hscT'⟩ := ReducesStar_equiv_pre henc₁ ⟨hT⟩
    have s1 : T' ≡ᵨ encode Q₀ n v :=
      let a := trans _ T _ hscT' hscT
      trans _ (encode Q₀' n v) _ a henc₂
    exact ⟨T', ⟨hT'⟩, s1⟩

/-- Multi-step RF reduction -/
inductive MultiStepRF : Process → Process → Type where
  | refl (P : Process) : MultiStepRF P P
  | step {P Q R : Process} : ReducesRF P Q → MultiStepRF Q R → MultiStepRF P R

/-- CommSafe for multi-step: every step is safe. -/
def MultiCommSafe : MultiStepRF P Q → Prop
  | .refl _ => True
  | .step h rest => CommSafe h ∧ MultiCommSafe rest

/-- Multi-step forward simulation for the RF fragment. -/
theorem forward_multi_step_rf {P Q : Process}
    (h : MultiStepRF P Q) (hrf : RestrictionFree P) (hsafe : MultiCommSafe h)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧
         (T ≡ᵨ encode Q n v) := by
  induction h generalizing n v with
  | refl P => exact ⟨encode P n v, ⟨ReducesStar.refl _⟩, refl _⟩
  | step h rest ih =>
    obtain ⟨T₁, ⟨hT₁⟩, hsc₁⟩ :=
      forward_single_step_rf h hrf hsafe.1 n v
    have hrfQ := reducesRF_preserves_rf h hrf
    obtain ⟨T₂, ⟨hT₂⟩, hsc₂⟩ := ih hrfQ hsafe.2 n v
    obtain ⟨T', ⟨hT'⟩, hsc'⟩ := ReducesStar_equiv_pre hsc₁ ⟨hT₂⟩
    exact ⟨T', ⟨hT₁.trans hT'⟩, trans _ T₂ _ hsc' hsc₂⟩

end Mettapedia.OSLF.PiCalculus.ForwardSimulation
