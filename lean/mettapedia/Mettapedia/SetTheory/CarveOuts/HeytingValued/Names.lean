import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Heyting-valued sets over a frame: names, equality, membership

A **frame** `H` (a complete Heyting algebra) is a frame of perspectives: its elements are
truth values. The Heyting-valued universe `V^(H)` (Scott–Solovay for Boolean `H`; Fourman,
Scott, Grayson and Bell for Heyting `H`) has as its sets the **names**: a name is a family of
names, each carrying the truth value of its own membership (`Name.mk ι child weight`).

Equality and membership are valued in `H`, by recursion on names:

* `⟦x = y⟧ = (⨅ i, x_i ⇨ ⟦x.child i ∈ y⟧) ⊓ (⨅ j, y_j ⇨ ⟦y.child j ∈ x⟧)`,
  where `x_i` is the weight of the `i`-th child (`eq_eq_bounded`);
* `⟦x ∈ y⟧ = ⨆ j, y_j ⊓ ⟦x = y.child j⟧` (`mem_eq_iSup`).

**The equality laws** hold in every frame: reflexivity (`eq_self`), symmetry (`eq_comm`),
transitivity (`eq_inf_eq_le`), and substitution of equals in membership on both sides
(`eq_inf_mem_le_left`, `eq_inf_mem_le_right`). A child is a member to at least its weight
(`weight_le_mem`).

**Bounded formulas** (`BFormula n`, with `n` free variables) have atoms `∈` and `=`, the
connectives `⊥ ∧ ∨ →`, and the bounded quantifiers `∀ z ∈ v` and `∃ z ∈ v`. Their value at
an assignment of names (`eval`) is computed in `H`: a bounded universal is an infimum of
implications over the children of the bound, a bounded existential a supremum of
conjunctions. **Substitution of equals** holds for every bounded formula (`eval_subst`):
the value of a formula at one assignment, met with the equality of that assignment and
another, is at most its value at the other. The one-variable form is `eval_subst_cons`.

Every truth value is the value of an atomic sentence: `⟦∅ ∈ {∅ ↦ h}⟧ = h`
(`mem_empty_truthName`).

The well-founded part of the `H`-valued top is built here. The `H`-valued hyperset top, the
final coalgebra of the `H`-weighted power functor, would attach in place of the inductive
type `Name`: its equality is the greatest fixed point of the same equations, and these
laws are the ones it must satisfy.

Nothing in this module uses a choice principle.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.HeytingValued

universe u

/-- A name of the Heyting-valued universe: a family of names, each with the truth value of
its membership. -/
inductive Name (H : Type u) : Type (u + 1) where
  | mk (Index : Type u) (child : Index → Name H) (weight : Index → H) : Name H

namespace Name

variable {H : Type u}

/-- The index type of the children of a name. -/
def Index : Name H → Type u
  | mk ι _ _ => ι

/-- The children of a name. -/
def child : (x : Name H) → x.Index → Name H
  | mk _ A _ => A

/-- The truth value of the membership of each child. -/
def weight : (x : Name H) → x.Index → H
  | mk _ _ B => B

/-- The empty name. -/
def empty : Name H :=
  mk PEmpty PEmpty.elim PEmpty.elim

/-- The name `{∅ ↦ h}`: the empty name is a member to the extent `h`. -/
def truthName (h : H) : Name H :=
  mk PUnit (fun _ => empty) (fun _ => h)

variable [Order.Frame H]

/-- The truth value of `x = y`. -/
def eq : Name H → Name H → H
  | mk _ A B, mk _ A' B' =>
    (⨅ i, B i ⇨ ⨆ j, B' j ⊓ eq (A i) (A' j)) ⊓ (⨅ j, B' j ⇨ ⨆ i, B i ⊓ eq (A i) (A' j))

/-- The truth value of `x ∈ y`. -/
def mem (x : Name H) : Name H → H
  | mk _ A B => ⨆ j, B j ⊓ eq x (A j)

theorem eq_mk {ι κ : Type u} (A : ι → Name H) (B : ι → H) (A' : κ → Name H) (B' : κ → H) :
    eq (mk ι A B) (mk κ A' B') =
      (⨅ i, B i ⇨ ⨆ j, B' j ⊓ eq (A i) (A' j)) ⊓ (⨅ j, B' j ⇨ ⨆ i, B i ⊓ eq (A i) (A' j)) :=
  rfl

theorem mem_mk (x : Name H) {κ : Type u} (A : κ → Name H) (B : κ → H) :
    mem x (mk κ A B) = ⨆ j, B j ⊓ eq x (A j) :=
  rfl

/-- Membership is a supremum over the children of the bound. -/
theorem mem_eq_iSup (x y : Name H) : mem x y = ⨆ j, y.weight j ⊓ eq x (y.child j) := by
  cases y
  rfl

/-! ## The equality laws -/

/-- **Reflexivity.** -/
theorem eq_self (x : Name H) : eq x x = ⊤ := by
  induction x with
  | mk ι A B ih =>
    rw [eq_mk]
    refine top_unique (le_inf (le_iInf fun i => ?_) (le_iInf fun j => ?_))
    · rw [le_himp_iff, top_inf_eq]
      exact le_iSup_of_le i (by rw [ih i, inf_top_eq])
    · rw [le_himp_iff, top_inf_eq]
      exact le_iSup_of_le j (by rw [ih j, inf_top_eq])

/-- **Symmetry.** -/
theorem eq_comm (x y : Name H) : eq x y = eq y x := by
  induction x generalizing y with
  | mk ι A B ih =>
    cases y with
    | mk κ A' B' =>
      have e : ∀ i j, eq (A i) (A' j) = eq (A' j) (A i) := fun i j => ih i (A' j)
      rw [eq_mk, eq_mk]
      simp only [e]
      rw [inf_comm]

/-- The left half of equality: a child of `x`, met with `⟦x = y⟧`, is a member of `y`. -/
theorem eq_mk_inf_weight_le {ι κ : Type u} (A : ι → Name H) (B : ι → H) (A' : κ → Name H)
    (B' : κ → H) (i : ι) :
    eq (mk ι A B) (mk κ A' B') ⊓ B i ≤ ⨆ j, B' j ⊓ eq (A i) (A' j) :=
  le_trans (inf_le_inf_right _ (le_trans inf_le_left (iInf_le _ i))) himp_inf_le

/-- The right half of equality: a child of `y`, met with `⟦x = y⟧`, is a member of `x`. -/
theorem eq_mk_inf_weight_le' {ι κ : Type u} (A : ι → Name H) (B : ι → H) (A' : κ → Name H)
    (B' : κ → H) (j : κ) :
    eq (mk ι A B) (mk κ A' B') ⊓ B' j ≤ ⨆ i, B i ⊓ eq (A i) (A' j) :=
  le_trans (inf_le_inf_right _ (le_trans inf_le_right (iInf_le _ j))) himp_inf_le

theorem eq_inf_weight_le (x y : Name H) (i : x.Index) :
    eq x y ⊓ x.weight i ≤ ⨆ j, y.weight j ⊓ eq (x.child i) (y.child j) := by
  cases x
  cases y
  exact eq_mk_inf_weight_le _ _ _ _ i

theorem eq_inf_weight_le' (x y : Name H) (j : y.Index) :
    eq x y ⊓ y.weight j ≤ ⨆ i, x.weight i ⊓ eq (x.child i) (y.child j) := by
  cases x
  cases y
  exact eq_mk_inf_weight_le' _ _ _ _ j

/-- **Transitivity.** -/
theorem eq_inf_eq_le (x y z : Name H) : eq x y ⊓ eq y z ≤ eq x z := by
  induction x generalizing y z with
  | mk ι A B ih =>
    cases y with
    | mk κ C D =>
      cases z with
      | mk μ E F =>
        rw [eq_mk A B E F]
        refine le_inf (le_iInf fun i => le_himp_iff.mpr ?_) (le_iInf fun k => le_himp_iff.mpr ?_)
        · -- a child of `x` is matched in `z` through `y`
          have step : ∀ j, eq (mk κ C D) (mk μ E F) ⊓ (D j ⊓ eq (A i) (C j)) ≤
              ⨆ k, F k ⊓ eq (A i) (E k) := by
            intro j
            calc eq (mk κ C D) (mk μ E F) ⊓ (D j ⊓ eq (A i) (C j))
                = (eq (mk κ C D) (mk μ E F) ⊓ D j) ⊓ eq (A i) (C j) := (inf_assoc _ _ _).symm
              _ ≤ (⨆ k, F k ⊓ eq (C j) (E k)) ⊓ eq (A i) (C j) :=
                inf_le_inf_right _ (eq_mk_inf_weight_le C D E F j)
              _ = ⨆ k, F k ⊓ eq (C j) (E k) ⊓ eq (A i) (C j) := iSup_inf_eq _ _
              _ ≤ ⨆ k, F k ⊓ eq (A i) (E k) := iSup_mono fun k => by
                rw [inf_assoc]
                exact inf_le_inf_left _ (by rw [inf_comm]; exact ih i (C j) (E k))
          calc eq (mk ι A B) (mk κ C D) ⊓ eq (mk κ C D) (mk μ E F) ⊓ B i
              = eq (mk κ C D) (mk μ E F) ⊓ (eq (mk ι A B) (mk κ C D) ⊓ B i) := by
                rw [inf_comm (eq (mk ι A B) (mk κ C D)), inf_assoc]
            _ ≤ eq (mk κ C D) (mk μ E F) ⊓ ⨆ j, D j ⊓ eq (A i) (C j) :=
              inf_le_inf_left _ (eq_mk_inf_weight_le A B C D i)
            _ = ⨆ j, eq (mk κ C D) (mk μ E F) ⊓ (D j ⊓ eq (A i) (C j)) := inf_iSup_eq _ _
            _ ≤ ⨆ k, F k ⊓ eq (A i) (E k) := iSup_le step
        · -- a child of `z` is matched in `x` through `y`
          have step : ∀ j, eq (mk ι A B) (mk κ C D) ⊓ (D j ⊓ eq (C j) (E k)) ≤
              ⨆ i, B i ⊓ eq (A i) (E k) := by
            intro j
            calc eq (mk ι A B) (mk κ C D) ⊓ (D j ⊓ eq (C j) (E k))
                = (eq (mk ι A B) (mk κ C D) ⊓ D j) ⊓ eq (C j) (E k) := (inf_assoc _ _ _).symm
              _ ≤ (⨆ i, B i ⊓ eq (A i) (C j)) ⊓ eq (C j) (E k) :=
                inf_le_inf_right _ (eq_mk_inf_weight_le' A B C D j)
              _ = ⨆ i, B i ⊓ eq (A i) (C j) ⊓ eq (C j) (E k) := iSup_inf_eq _ _
              _ ≤ ⨆ i, B i ⊓ eq (A i) (E k) := iSup_mono fun i => by
                rw [inf_assoc]
                exact inf_le_inf_left _ (ih i (C j) (E k))
          calc eq (mk ι A B) (mk κ C D) ⊓ eq (mk κ C D) (mk μ E F) ⊓ F k
              = eq (mk ι A B) (mk κ C D) ⊓ (eq (mk κ C D) (mk μ E F) ⊓ F k) := inf_assoc _ _ _
            _ ≤ eq (mk ι A B) (mk κ C D) ⊓ ⨆ j, D j ⊓ eq (C j) (E k) :=
              inf_le_inf_left _ (eq_mk_inf_weight_le' C D E F k)
            _ = ⨆ j, eq (mk ι A B) (mk κ C D) ⊓ (D j ⊓ eq (C j) (E k)) := inf_iSup_eq _ _
            _ ≤ ⨆ i, B i ⊓ eq (A i) (E k) := iSup_le step

/-! ## Membership -/

/-- A child is a member of its parent to at least its weight. -/
theorem weight_le_mem (x : Name H) (i : x.Index) : x.weight i ≤ mem (x.child i) x := by
  rw [mem_eq_iSup]
  exact le_iSup_of_le i (by rw [eq_self, inf_top_eq])

/-- **Substitution on the left of membership.** -/
theorem eq_inf_mem_le_left (x x' y : Name H) : eq x x' ⊓ mem x y ≤ mem x' y := by
  rw [mem_eq_iSup, mem_eq_iSup, inf_iSup_eq]
  refine iSup_mono fun j => ?_
  calc eq x x' ⊓ (y.weight j ⊓ eq x (y.child j))
      = y.weight j ⊓ (eq x' x ⊓ eq x (y.child j)) := by
        rw [eq_comm x x', inf_left_comm]
    _ ≤ y.weight j ⊓ eq x' (y.child j) := inf_le_inf_left _ (eq_inf_eq_le _ _ _)

/-- **Substitution on the right of membership.** -/
theorem eq_inf_mem_le_right (x y y' : Name H) : eq y y' ⊓ mem x y ≤ mem x y' := by
  rw [mem_eq_iSup, inf_iSup_eq]
  refine iSup_le fun j => ?_
  calc eq y y' ⊓ (y.weight j ⊓ eq x (y.child j))
      = (eq y y' ⊓ y.weight j) ⊓ eq x (y.child j) := (inf_assoc _ _ _).symm
    _ ≤ (⨆ k, y'.weight k ⊓ eq (y.child j) (y'.child k)) ⊓ eq x (y.child j) :=
      inf_le_inf_right _ (eq_inf_weight_le y y' j)
    _ = ⨆ k, y'.weight k ⊓ eq (y.child j) (y'.child k) ⊓ eq x (y.child j) := iSup_inf_eq _ _
    _ ≤ mem x y' := by
      rw [mem_eq_iSup]
      refine iSup_mono fun k => ?_
      rw [inf_assoc]
      exact inf_le_inf_left _ (by rw [inf_comm]; exact eq_inf_eq_le _ _ _)

/-- **Equality is bounded extensionality.** -/
theorem eq_eq_bounded (x y : Name H) :
    eq x y = (⨅ i, x.weight i ⇨ mem (x.child i) y) ⊓ (⨅ j, y.weight j ⇨ mem (y.child j) x) := by
  cases x with
  | mk ι A B =>
    cases y with
    | mk κ A' B' =>
      rw [eq_mk]
      congr 1
      refine iInf_congr fun j => ?_
      show B' j ⇨ ⨆ i, B i ⊓ eq (A i) (A' j) = B' j ⇨ ⨆ i, B i ⊓ eq (A' j) (A i)
      simp only [eq_comm (A _) (A' j)]

/-- The empty name has no members. -/
theorem mem_empty (x : Name H) : mem x empty = ⊥ := by
  rw [empty, mem_mk]
  exact iSup_eq_bot.mpr fun i => i.elim

/-- **Every truth value is the value of an atomic sentence.** -/
theorem mem_empty_truthName (h : H) : mem empty (truthName h) = h := by
  rw [truthName, mem_mk, eq_self, inf_top_eq]
  exact iSup_const

/-! ## Bounded formulas -/

end Name

/-- Bounded formulas with `n` free variables. `ball b φ` is `∀ z ∈ v_b, φ` and `bex b φ` is
`∃ z ∈ v_b, φ`; the bound variable `z` is variable `0` of the body. -/
inductive BFormula : ℕ → Type where
  | falsum {n : ℕ} : BFormula n
  | mem {n : ℕ} (a b : Fin n) : BFormula n
  | eq {n : ℕ} (a b : Fin n) : BFormula n
  | and {n : ℕ} (φ ψ : BFormula n) : BFormula n
  | or {n : ℕ} (φ ψ : BFormula n) : BFormula n
  | imp {n : ℕ} (φ ψ : BFormula n) : BFormula n
  | ball {n : ℕ} (b : Fin n) (φ : BFormula (n + 1)) : BFormula n
  | bex {n : ℕ} (b : Fin n) (φ : BFormula (n + 1)) : BFormula n

namespace BFormula

/-- Negation, as implication of falsity. -/
def not {n : ℕ} (φ : BFormula n) : BFormula n :=
  imp φ falsum

/-- The excluded-middle instance of a formula. -/
def lem {n : ℕ} (φ : BFormula n) : BFormula n :=
  or φ φ.not

end BFormula

namespace Name

variable {H : Type u} [Order.Frame H]

/-- Distributivity of a meet over a binary join, from the Heyting implication alone. -/
theorem inf_sup_le_sup_inf (a b c : H) : a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c := by
  rw [inf_comm, ← le_himp_iff]
  exact sup_le (le_himp_iff.mpr (by rw [inf_comm]; exact le_sup_left))
    (le_himp_iff.mpr (by rw [inf_comm]; exact le_sup_right))

/-- The truth value of a bounded formula at an assignment of names. -/
def eval : {n : ℕ} → BFormula n → (Fin n → Name H) → H
  | _, .falsum, _ => ⊥
  | _, .mem a b, v => mem (v a) (v b)
  | _, .eq a b, v => eq (v a) (v b)
  | _, .and φ ψ, v => eval φ v ⊓ eval ψ v
  | _, .or φ ψ, v => eval φ v ⊔ eval ψ v
  | _, .imp φ ψ, v => eval φ v ⇨ eval ψ v
  | _, .ball b φ, v =>
    ⨅ i : (v b).Index, (v b).weight i ⇨ eval φ (Fin.cons ((v b).child i) v : Fin _ → Name H)
  | _, .bex b φ, v =>
    ⨆ i : (v b).Index, (v b).weight i ⊓ eval φ (Fin.cons ((v b).child i) v : Fin _ → Name H)

/-- The equality of two assignments. -/
def eqAssign {n : ℕ} (v w : Fin n → Name H) : H :=
  ⨅ i, eq (v i) (w i)

theorem eqAssign_comm {n : ℕ} (v w : Fin n → Name H) : eqAssign v w = eqAssign w v := by
  simp only [eqAssign, eq_comm (v _)]

theorem eqAssign_le {n : ℕ} (v w : Fin n → Name H) (i : Fin n) :
    eqAssign v w ≤ eq (v i) (w i) :=
  iInf_le _ i

theorem eq_inf_eqAssign_le_cons {n : ℕ} (v w : Fin n → Name H) (x y : Name H) :
    eq x y ⊓ eqAssign v w ≤
      eqAssign (Fin.cons x v : Fin (n + 1) → Name H) (Fin.cons y w : Fin (n + 1) → Name H) := by
  refine le_iInf fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
    exact inf_le_left
  · simp only [Fin.cons_succ]
    exact le_trans inf_le_right (eqAssign_le v w i)

theorem eqAssign_self {n : ℕ} (v : Fin n → Name H) : eqAssign v v = ⊤ := by
  simp only [eqAssign, eq_self, iInf_top]

/-- **Substitution of equals in every bounded formula.** -/
theorem eval_subst : ∀ {n : ℕ} (φ : BFormula n) (v w : Fin n → Name H),
    eqAssign v w ⊓ eval φ v ≤ eval φ w
  | _, .falsum, _, _ => inf_le_right
  | _, .mem a b, v, w => by
    show eqAssign v w ⊓ mem (v a) (v b) ≤ mem (w a) (w b)
    calc eqAssign v w ⊓ mem (v a) (v b)
        ≤ eq (v b) (w b) ⊓ (eq (v a) (w a) ⊓ mem (v a) (v b)) :=
          le_inf (le_trans inf_le_left (eqAssign_le v w b))
            (inf_le_inf_right _ (eqAssign_le v w a))
      _ ≤ eq (v b) (w b) ⊓ mem (w a) (v b) := inf_le_inf_left _ (eq_inf_mem_le_left _ _ _)
      _ ≤ mem (w a) (w b) := eq_inf_mem_le_right _ _ _
  | _, .eq a b, v, w => by
    show eqAssign v w ⊓ eq (v a) (v b) ≤ eq (w a) (w b)
    calc eqAssign v w ⊓ eq (v a) (v b)
        ≤ (eq (w a) (v a) ⊓ eq (v a) (v b)) ⊓ eq (v b) (w b) :=
          le_inf (inf_le_inf_right _ (by rw [eq_comm]; exact eqAssign_le v w a))
            (le_trans inf_le_left (eqAssign_le v w b))
      _ ≤ eq (w a) (v b) ⊓ eq (v b) (w b) := inf_le_inf_right _ (eq_inf_eq_le _ _ _)
      _ ≤ eq (w a) (w b) := eq_inf_eq_le _ _ _
  | _, .and φ ψ, v, w => by
    show eqAssign v w ⊓ (eval φ v ⊓ eval ψ v) ≤ eval φ w ⊓ eval ψ w
    exact le_inf (le_trans (inf_le_inf_left _ inf_le_left) (eval_subst φ v w))
      (le_trans (inf_le_inf_left _ inf_le_right) (eval_subst ψ v w))
  | _, .or φ ψ, v, w => by
    show eqAssign v w ⊓ (eval φ v ⊔ eval ψ v) ≤ eval φ w ⊔ eval ψ w
    exact le_trans (inf_sup_le_sup_inf _ _ _) (sup_le_sup (eval_subst φ v w) (eval_subst ψ v w))
  | _, .imp φ ψ, v, w => by
    show eqAssign v w ⊓ (eval φ v ⇨ eval ψ v) ≤ eval φ w ⇨ eval ψ w
    rw [le_himp_iff]
    calc eqAssign v w ⊓ (eval φ v ⇨ eval ψ v) ⊓ eval φ w
        ≤ eqAssign v w ⊓ ((eval φ v ⇨ eval ψ v) ⊓ (eqAssign w v ⊓ eval φ w)) :=
          le_inf (le_trans inf_le_left inf_le_left)
            (le_inf (le_trans inf_le_left inf_le_right)
              (le_inf (le_trans (le_trans inf_le_left inf_le_left)
                (le_of_eq (eqAssign_comm v w))) inf_le_right))
      _ ≤ eqAssign v w ⊓ ((eval φ v ⇨ eval ψ v) ⊓ eval φ v) :=
          inf_le_inf_left _ (inf_le_inf_left _ (eval_subst φ w v))
      _ ≤ eqAssign v w ⊓ eval ψ v := inf_le_inf_left _ himp_inf_le
      _ ≤ eval ψ w := eval_subst ψ v w
  | _, .ball b φ, v, w => by
    show eqAssign v w ⊓ (⨅ i, (v b).weight i ⇨ eval φ (Fin.cons ((v b).child i) v)) ≤
      ⨅ k, (w b).weight k ⇨ eval φ (Fin.cons ((w b).child k) w)
    refine le_iInf fun k => le_himp_iff.mpr ?_
    have hk : eqAssign v w ⊓ (w b).weight k ≤
        ⨆ i, (v b).weight i ⊓ eq ((v b).child i) ((w b).child k) :=
      le_trans (inf_le_inf_right _ (eqAssign_le v w b)) (eq_inf_weight_le' _ _ k)
    calc eqAssign v w ⊓ (⨅ i, (v b).weight i ⇨ eval φ (Fin.cons ((v b).child i) v)) ⊓
          (w b).weight k
        ≤ (eqAssign v w ⊓ (w b).weight k) ⊓
            (eqAssign v w ⊓ ⨅ i, (v b).weight i ⇨ eval φ (Fin.cons ((v b).child i) v)) :=
          le_inf (le_inf (le_trans inf_le_left inf_le_left) inf_le_right) inf_le_left
      _ ≤ (⨆ i, (v b).weight i ⊓ eq ((v b).child i) ((w b).child k)) ⊓
            (eqAssign v w ⊓ ⨅ i, (v b).weight i ⇨ eval φ (Fin.cons ((v b).child i) v)) :=
          inf_le_inf_right _ hk
      _ = ⨆ i, (v b).weight i ⊓ eq ((v b).child i) ((w b).child k) ⊓
            (eqAssign v w ⊓ ⨅ i, (v b).weight i ⇨ eval φ (Fin.cons ((v b).child i) v)) :=
          iSup_inf_eq _ _
      _ ≤ eval φ (Fin.cons ((w b).child k) w) := iSup_le fun i => by
          have hi : (⨅ i, (v b).weight i ⇨ eval φ (Fin.cons ((v b).child i) v)) ⊓
              (v b).weight i ≤ eval φ (Fin.cons ((v b).child i) v) :=
            le_trans (inf_le_inf_right _ (iInf_le _ i)) himp_inf_le
          calc (v b).weight i ⊓ eq ((v b).child i) ((w b).child k) ⊓
                (eqAssign v w ⊓ ⨅ i, (v b).weight i ⇨ eval φ (Fin.cons ((v b).child i) v))
              = (eq ((v b).child i) ((w b).child k) ⊓ eqAssign v w) ⊓
                  ((⨅ i, (v b).weight i ⇨ eval φ (Fin.cons ((v b).child i) v)) ⊓
                    (v b).weight i) := by ac_rfl
            _ ≤ eqAssign (Fin.cons ((v b).child i) v : Fin _ → Name H)
                  (Fin.cons ((w b).child k) w : Fin _ → Name H) ⊓
                  eval φ (Fin.cons ((v b).child i) v) :=
                inf_le_inf (eq_inf_eqAssign_le_cons v w _ _) hi
            _ ≤ eval φ (Fin.cons ((w b).child k) w) := eval_subst φ _ _
  | _, .bex b φ, v, w => by
    show eqAssign v w ⊓ (⨆ i, (v b).weight i ⊓ eval φ (Fin.cons ((v b).child i) v)) ≤
      ⨆ k, (w b).weight k ⊓ eval φ (Fin.cons ((w b).child k) w)
    rw [inf_iSup_eq]
    refine iSup_le fun i => ?_
    have hi : eqAssign v w ⊓ (v b).weight i ≤
        ⨆ k, (w b).weight k ⊓ eq ((v b).child i) ((w b).child k) :=
      le_trans (inf_le_inf_right _ (eqAssign_le v w b)) (eq_inf_weight_le _ _ i)
    calc eqAssign v w ⊓ ((v b).weight i ⊓ eval φ (Fin.cons ((v b).child i) v))
        = (eqAssign v w ⊓ (v b).weight i) ⊓
            (eqAssign v w ⊓ eval φ (Fin.cons ((v b).child i) v)) := by
          rw [inf_inf_distrib_left]
      _ ≤ (⨆ k, (w b).weight k ⊓ eq ((v b).child i) ((w b).child k)) ⊓
            (eqAssign v w ⊓ eval φ (Fin.cons ((v b).child i) v)) := inf_le_inf_right _ hi
      _ = ⨆ k, (w b).weight k ⊓ eq ((v b).child i) ((w b).child k) ⊓
            (eqAssign v w ⊓ eval φ (Fin.cons ((v b).child i) v)) := iSup_inf_eq _ _
      _ ≤ ⨆ k, (w b).weight k ⊓ eval φ (Fin.cons ((w b).child k) w) := iSup_mono fun k => by
          calc (w b).weight k ⊓ eq ((v b).child i) ((w b).child k) ⊓
                (eqAssign v w ⊓ eval φ (Fin.cons ((v b).child i) v))
              = (w b).weight k ⊓ ((eq ((v b).child i) ((w b).child k) ⊓ eqAssign v w) ⊓
                  eval φ (Fin.cons ((v b).child i) v)) := by ac_rfl
            _ ≤ (w b).weight k ⊓ eval φ (Fin.cons ((w b).child k) w) :=
                inf_le_inf_left _ (le_trans
                  (inf_le_inf_right _ (eq_inf_eqAssign_le_cons v w _ _)) (eval_subst φ _ _))

/-- Substitution of equals for the newest variable. -/
theorem eval_subst_cons {n : ℕ} (φ : BFormula (n + 1)) (v : Fin n → Name H) (x y : Name H) :
    eq x y ⊓ eval φ (Fin.cons x v : Fin (n + 1) → Name H) ≤
      eval φ (Fin.cons y v : Fin (n + 1) → Name H) := by
  refine le_trans (inf_le_inf_right _ ?_) (eval_subst φ _ _)
  calc eq x y = eq x y ⊓ eqAssign v v := by rw [eqAssign_self, inf_top_eq]
    _ ≤ _ := eq_inf_eqAssign_le_cons v v x y

end Name

end Mettapedia.SetTheory.CarveOuts.HeytingValued
