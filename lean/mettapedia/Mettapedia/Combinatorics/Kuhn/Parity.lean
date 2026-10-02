import Mettapedia.Combinatorics.Kuhn.GridSimplex
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Fin

/-!
# Kuhn's lemma: an odd number of completely labelled simplices

Label the points of the grid `{0, …, p}^n` with `{0, …, n}` so that

* a point with coordinate `i` equal to `0` does not carry the label `i + 1`,
* a point with coordinate `i` equal to `p` carries a label of at least `i + 1`.

Then the number of simplices of Kuhn's triangulation whose vertices carry all
`n + 1` labels is odd (`odd_card_complete`). In particular there is one.

The proof counts the pairs of a simplex and a vertex of it such that the other
vertices carry exactly the labels `1, …, n` ("doors").

* Simplex by simplex: one door if the simplex is complete, none or two
  otherwise (`Combinatorics/Kuhn/LabelSequences.lean`).
* Vertex position by vertex position: at an inner position the doors pair up
  by exchanging the two neighbouring steps; the doors at the first position
  that can be rotated up pair with the doors at the last position; a door at
  the last position can always be rotated down; and a door at the first
  position that cannot be rotated up lies in the face where coordinate `0`
  equals `p`, where it is a complete simplex of dimension `n - 1`.

So the parity is that of dimension `n - 1`, and in dimension `0` there is one
simplex.

The consequence used for Brouwer's theorem is `exists_cell_with_both_labels`:
for labels `false`/`true` on every coordinate, forced to `false` where the
coordinate is `0` and to `true` where it is `p`, some cell of the grid has,
for each coordinate, a corner with each of the two labels.

## References

* Kuhn (1960). "Some combinatorial lemmas in topology", IBM Journal 4.
-/

set_option autoImplicit false

namespace Mettapedia.Combinatorics.Kuhn

open Finset

/-! ## Parity tools -/

/-- A finite set with an involution without fixed points has an even number of
elements. -/
theorem even_card_of_involution {α : Type*} [DecidableEq α] (s : Finset α) (f : α → α)
    (maps : ∀ a ∈ s, f a ∈ s) (involutive : ∀ a ∈ s, f (f a) = a)
    (moves : ∀ a ∈ s, f a ≠ a) : Even s.card := by
  have sum : ∑ _a ∈ s, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun a _ => f a) (fun _ _ => by decide)
      (fun a member _ => moves a member) maps involutive
  rw [← ZMod.natCast_eq_zero_iff_even]
  simpa using sum

/-- Modulo two, the number of doors is the indicator of "every label occurs". -/
theorem natCast_card_doors {n : ℕ} (labels : Fin (n + 1) → Fin (n + 1)) (top : Fin (n + 1)) :
    ((doors labels top).card : ZMod 2) = if Function.Surjective labels then 1 else 0 := by
  split_ifs with surjective
  · rw [doors_of_surjective top surjective, Nat.cast_one]
  · exact ZMod.natCast_eq_zero_iff_even.mpr (even_card_doors_of_not_surjective top surjective)

/-! ## Doors at the first and at the last position -/

section Positions

variable {m : ℕ}

theorem isDoor_zero_iff (labels : Fin (m + 2) → Fin (m + 2)) (top : Fin (m + 2)) :
    IsDoor labels top 0 ↔ (univ.image fun j : Fin (m + 1) => labels j.succ) = univ.erase top := by
  have facet : univ.erase (0 : Fin (m + 2)) = univ.image Fin.succ := by
    ext k
    simp only [mem_erase, mem_univ, and_true, mem_image, true_and]
    exact Fin.exists_succ_eq.symm
  unfold IsDoor
  rw [facet, image_image]
  rfl

theorem isDoor_last_iff (labels : Fin (m + 2) → Fin (m + 2)) (top : Fin (m + 2)) :
    IsDoor labels top (Fin.last (m + 1)) ↔
      (univ.image fun j : Fin (m + 1) => labels j.castSucc) = univ.erase top := by
  have facet : univ.erase (Fin.last (m + 1)) = univ.image Fin.castSucc := by
    ext k
    simp only [mem_erase, mem_univ, and_true, mem_image, true_and]
    exact Fin.exists_castSucc_eq.symm
  unfold IsDoor
  rw [facet, image_image]
  rfl

end Positions

/-! ## Labellings -/

/-- The boundary conditions on a labelling of the grid `{0, …, p}^n`. -/
structure Proper (p : ℕ) {n : ℕ} (label : (Fin n → ℕ) → Fin (n + 1)) : Prop where
  /-- Where coordinate `i` is `0`, the label is not `i + 1`. -/
  ne_succ_of_eq_zero : ∀ x i, x i = 0 → label x ≠ i.succ
  /-- Where coordinate `i` is `p`, the label is at least `i + 1`. -/
  succ_le_of_eq_top : ∀ x i, x i = p → i.succ ≤ label x

namespace GridSimplex

variable {q m : ℕ}

/-- The simplices for which position `k` is a door. -/
def doorsAt (label : (Fin (m + 1) → ℕ) → Fin (m + 2)) (k : Fin (m + 2)) :
    Finset (GridSimplex (q + 1) (m + 1)) :=
  univ.filter fun σ => IsDoor (σ.labels label) 0 k

theorem mem_doorsAt {label : (Fin (m + 1) → ℕ) → Fin (m + 2)} {k : Fin (m + 2)}
    {σ : GridSimplex (q + 1) (m + 1)} :
    σ ∈ doorsAt label k ↔ IsDoor (σ.labels label) 0 k := by
  simp [doorsAt]

/-- At an inner position the doors pair up by exchanging the two neighbouring
steps. -/
theorem even_card_doorsAt_inner (label : (Fin (m + 1) → ℕ) → Fin (m + 2)) (j : Fin m) :
    Even (doorsAt (q := q) label j.castSucc.succ).card := by
  apply even_card_of_involution _ fun σ => σ.swapStep j
  · intro σ member
    rw [mem_doorsAt] at member ⊢
    refine (IsDoor.congr fun vertex other => ?_).mpr member
    show label ((σ.swapStep j).vertex vertex) = label (σ.vertex vertex)
    rw [σ.swapStep_vertex j vertex fun same => other (Fin.ext (by simpa using same))]
  · intro σ _
    exact σ.swapStep_swapStep j
  · intro σ _
    exact σ.swapStep_ne j

/-- The doors at the first position that can be rotated up correspond to the
doors at the last position that can be rotated down. -/
theorem card_doorsAt_zero_canRaise (label : (Fin (m + 1) → ℕ) → Fin (m + 2)) :
    ((doorsAt (q := q) label 0).filter fun σ => σ.CanRaise).card =
      ((doorsAt (q := q) label (Fin.last (m + 1))).filter fun σ => σ.CanLower).card := by
  apply card_nbij' (fun σ => σ.rotateUp) fun σ => σ.rotateDown
  · intro σ member
    obtain ⟨door, raise⟩ := mem_filter.mp (mem_coe.mp member)
    rw [mem_doorsAt, isDoor_zero_iff] at door
    refine mem_coe.mpr (mem_filter.mpr ⟨?_, σ.canLower_rotateUp raise⟩)
    rw [mem_doorsAt, isDoor_last_iff, ← door]
    congr 1
    funext j
    show label (σ.rotateUp.vertex j.castSucc) = label (σ.vertex j.succ)
    rw [σ.rotateUp_vertex raise]
  · intro σ member
    obtain ⟨door, lower⟩ := mem_filter.mp (mem_coe.mp member)
    rw [mem_doorsAt, isDoor_last_iff] at door
    refine mem_coe.mpr (mem_filter.mpr ⟨?_, σ.canRaise_rotateDown lower⟩)
    rw [mem_doorsAt, isDoor_zero_iff, ← door]
    congr 1
    funext j
    show label (σ.rotateDown.vertex j.succ) = label (σ.vertex j.castSucc)
    rw [σ.rotateDown_vertex lower]
  · intro σ member
    exact σ.rotateDown_rotateUp (mem_filter.mp (mem_coe.mp member)).2
  · intro σ member
    exact σ.rotateUp_rotateDown (mem_filter.mp (mem_coe.mp member)).2

variable {label : (Fin (m + 1) → ℕ) → Fin (m + 2)}

/-- A door at the last position can be rotated down: otherwise its facet lies
where a coordinate is `0`, and misses a label. -/
theorem canLower_of_mem_doorsAt_last (proper : Proper (q + 1) label)
    {σ : GridSimplex (q + 1) (m + 1)} (member : σ ∈ doorsAt label (Fin.last (m + 1))) :
    σ.CanLower := by
  by_contra notLower
  rw [mem_doorsAt, isDoor_last_iff] at member
  have zero : (σ.base (σ.order (Fin.last m)) : ℕ) = 0 := by
    unfold CanLower at notLower
    omega
  have needed : (σ.order (Fin.last m)).succ ∈ univ.erase (0 : Fin (m + 2)) :=
    mem_erase.mpr ⟨Fin.succ_ne_zero _, mem_univ _⟩
  rw [← member] at needed
  obtain ⟨j, _, same⟩ := mem_image.mp needed
  have coordinate : σ.vertex j.castSucc (σ.order (Fin.last m)) = 0 := by
    have step : (σ.order.symm (σ.order (Fin.last m)) : ℕ) = m := (σ.last_iff _).mp rfl
    have upper := j.2
    simp only [vertex, step, zero, Fin.val_castSucc]
    rw [if_neg (by omega)]
  exact proper.ne_succ_of_eq_zero _ _ coordinate same

/-- A door at the first position that cannot be rotated up lies where
coordinate `0` equals `p`. -/
theorem order_zero_of_mem_doorsAt_zero (proper : Proper (q + 1) label)
    {σ : GridSimplex (q + 1) (m + 1)} (member : σ ∈ doorsAt label 0)
    (notRaise : ¬σ.CanRaise) : σ.order 0 = 0 := by
  rw [mem_doorsAt, isDoor_zero_iff] at member
  have top : (σ.base (σ.order 0) : ℕ) + 1 = q + 1 := by
    have bound := (σ.base (σ.order 0)).2
    unfold CanRaise at notRaise
    omega
  have needed : (0 : Fin (m + 1)).succ ∈ univ.erase (0 : Fin (m + 2)) :=
    mem_erase.mpr ⟨Fin.succ_ne_zero _, mem_univ _⟩
  rw [← member] at needed
  obtain ⟨j, _, same⟩ := mem_image.mp needed
  have coordinate : σ.vertex j.succ (σ.order 0) = q + 1 := by
    have step : (σ.order.symm (σ.order 0) : ℕ) = 0 := (σ.first_iff _).mp rfl
    simp only [vertex, step, Fin.val_succ]
    rw [if_pos (by omega)]
    exact top
  have bound := proper.succ_le_of_eq_top _ _ coordinate
  have labelled : label (σ.vertex j.succ) = (0 : Fin (m + 1)).succ := same
  rw [labelled] at bound
  exact nonpos_iff_eq_zero.mp (Fin.succ_le_succ_iff.mp bound)

/-! ## The face where coordinate `0` equals `p` -/

/-- The simplex of the next dimension that has `τ`, placed in the face where
coordinate `0` equals `q + 1`, as its facet opposite the first vertex. -/
def lift (τ : GridSimplex (q + 1) m) : GridSimplex (q + 1) (m + 1) :=
  ⟨Fin.cons (Fin.last q) τ.base, Equiv.Perm.decomposeFin.symm (0, τ.order)⟩

theorem lift_base_zero (τ : GridSimplex (q + 1) m) : τ.lift.base 0 = Fin.last q := rfl

theorem lift_base_succ (τ : GridSimplex (q + 1) m) (i : Fin m) :
    τ.lift.base i.succ = τ.base i := rfl

theorem lift_order_zero (τ : GridSimplex (q + 1) m) : τ.lift.order 0 = 0 :=
  Equiv.Perm.decomposeFin_symm_apply_zero 0 τ.order

theorem lift_order_succ (τ : GridSimplex (q + 1) m) (j : Fin m) :
    τ.lift.order j.succ = (τ.order j).succ := by
  show Equiv.Perm.decomposeFin.symm (0, τ.order) j.succ = _
  rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
  rfl

theorem lift_order_symm_zero (τ : GridSimplex (q + 1) m) : τ.lift.order.symm 0 = 0 := by
  rw [Equiv.symm_apply_eq, lift_order_zero]

theorem lift_order_symm_succ (τ : GridSimplex (q + 1) m) (i : Fin m) :
    τ.lift.order.symm i.succ = (τ.order.symm i).succ := by
  rw [Equiv.symm_apply_eq, lift_order_succ, Equiv.apply_symm_apply]

/-- The vertices of the lifted simplex after the first are those of `τ`, with
coordinate `0` equal to `q + 1`. -/
theorem lift_vertex_succ (τ : GridSimplex (q + 1) m) (j : Fin (m + 1)) :
    τ.lift.vertex j.succ = Fin.cons (q + 1) (τ.vertex j) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [vertex, lift_order_symm_zero, lift_base_zero, Fin.cons_zero, Fin.val_succ,
      Fin.val_zero, Fin.val_last]
    rw [if_pos (Nat.succ_pos _)]
  · simp only [vertex, lift_order_symm_succ, lift_base_succ, Fin.cons_succ, Fin.val_succ]
    by_cases before : (τ.order.symm i : ℕ) < (j : ℕ)
    · rw [if_pos (by omega), if_pos before]
    · rw [if_neg (by omega), if_neg before]

theorem lift_not_canRaise (τ : GridSimplex (q + 1) m) : ¬τ.lift.CanRaise := by
  unfold CanRaise
  rw [lift_order_zero, lift_base_zero, Fin.val_last]
  omega

theorem lift_injective :
    Function.Injective (lift : GridSimplex (q + 1) m → GridSimplex (q + 1) (m + 1)) := by
  intro τ τ' same
  apply GridSimplex.ext
  · funext i
    have at_i := congrFun (congrArg GridSimplex.base same) i.succ
    rwa [lift_base_succ, lift_base_succ] at at_i
  · have orders : Equiv.Perm.decomposeFin.symm ((0 : Fin (m + 1)), τ.order) =
        Equiv.Perm.decomposeFin.symm (0, τ'.order) := congrArg GridSimplex.order same
    exact (Prod.mk.inj (Equiv.Perm.decomposeFin.symm.injective orders)).2

/-- Every simplex whose first step raises coordinate `0` from the top cell is
a lift. -/
theorem exists_lift_eq (σ : GridSimplex (q + 1) (m + 1)) (first : σ.order 0 = 0)
    (notRaise : ¬σ.CanRaise) : ∃ τ : GridSimplex (q + 1) m, τ.lift = σ := by
  have baseTop : σ.base 0 = Fin.last q := by
    apply Fin.ext
    have bound := (σ.base 0).2
    unfold CanRaise at notRaise
    rw [first] at notRaise
    rw [Fin.val_last]
    omega
  have firstComponent : (Equiv.Perm.decomposeFin σ.order).1 = 0 := by
    have applied := Equiv.Perm.decomposeFin_symm_apply_zero
      (Equiv.Perm.decomposeFin σ.order).1 (Equiv.Perm.decomposeFin σ.order).2
    rw [Prod.mk.eta, Equiv.symm_apply_apply, first] at applied
    exact applied.symm
  refine ⟨⟨Fin.tail σ.base, (Equiv.Perm.decomposeFin σ.order).2⟩, ?_⟩
  apply GridSimplex.ext
  · show Fin.cons (Fin.last q) (Fin.tail σ.base) = σ.base
    rw [← baseTop]
    exact Fin.cons_self_tail _
  · show Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin σ.order).2) = σ.order
    rw [← firstComponent, Prod.mk.eta, Equiv.symm_apply_apply]

end GridSimplex

/-- The labelling induced on the face where coordinate `0` equals `p`. -/
def faceLabel {m : ℕ} (p : ℕ) (label : (Fin (m + 1) → ℕ) → Fin (m + 2)) :
    (Fin m → ℕ) → Fin (m + 1) :=
  fun y => Fin.predAbove 0 (label (Fin.cons p y))

theorem succ_faceLabel {m p : ℕ} {label : (Fin (m + 1) → ℕ) → Fin (m + 2)}
    (proper : Proper p label) (y : Fin m → ℕ) :
    (faceLabel p label y).succ = label (Fin.cons p y) := by
  have positive := proper.succ_le_of_eq_top (Fin.cons p y) 0 (Fin.cons_zero _ _)
  have nonzero : label (Fin.cons p y) ≠ 0 := by
    intro zero
    rw [zero] at positive
    exact absurd positive (by simp)
  exact Fin.succ_predAbove_zero nonzero

theorem Proper.faceLabel {m p : ℕ} {label : (Fin (m + 1) → ℕ) → Fin (m + 2)}
    (proper : Proper p label) : Proper p (faceLabel p label) where
  ne_succ_of_eq_zero y i zero same := by
    have lifted := succ_faceLabel proper y
    rw [same] at lifted
    exact proper.ne_succ_of_eq_zero (Fin.cons p y) i.succ (by rwa [Fin.cons_succ]) lifted.symm
  succ_le_of_eq_top y i top := by
    have bound := proper.succ_le_of_eq_top (Fin.cons p y) i.succ (by rwa [Fin.cons_succ])
    rw [← succ_faceLabel proper y] at bound
    exact Fin.succ_le_succ_iff.mp bound

namespace GridSimplex

variable {q m : ℕ} {label : (Fin (m + 1) → ℕ) → Fin (m + 2)}

/-- The lifted simplex has a door at its first position exactly when `τ` is
complete for the labelling of the face. -/
theorem lift_mem_doorsAt_zero_iff (proper : Proper (q + 1) label) (τ : GridSimplex (q + 1) m) :
    τ.lift ∈ doorsAt label 0 ↔ τ.Complete (faceLabel (q + 1) label) := by
  rw [mem_doorsAt, isDoor_zero_iff]
  have labels : (fun j : Fin (m + 1) => τ.lift.labels label j.succ) =
      fun j => (τ.labels (faceLabel (q + 1) label) j).succ := by
    funext j
    show label (τ.lift.vertex j.succ) = (faceLabel (q + 1) label (τ.vertex j)).succ
    rw [lift_vertex_succ, succ_faceLabel proper]
  rw [labels]
  constructor
  · intro facet wanted
    have needed : wanted.succ ∈ univ.erase (0 : Fin (m + 2)) :=
      mem_erase.mpr ⟨Fin.succ_ne_zero _, mem_univ _⟩
    rw [← facet] at needed
    obtain ⟨j, _, same⟩ := mem_image.mp needed
    exact ⟨j, Fin.succ_injective _ same⟩
  · intro complete
    ext k
    simp only [mem_image, mem_univ, true_and, mem_erase, and_true]
    constructor
    · rintro ⟨j, rfl⟩
      exact Fin.succ_ne_zero _
    · intro nonzero
      obtain ⟨wanted, rfl⟩ := Fin.exists_succ_eq.mpr nonzero
      obtain ⟨j, same⟩ := complete wanted
      exact ⟨j, congrArg Fin.succ same⟩

/-- The doors at the first position that cannot be rotated up are the lifts
of the complete simplices of the face. -/
theorem doorsAt_zero_not_canRaise (proper : Proper (q + 1) label) :
    ((doorsAt (q := q) label 0).filter fun σ => ¬σ.CanRaise) =
      (univ.filter fun τ : GridSimplex (q + 1) m =>
        τ.Complete (faceLabel (q + 1) label)).image lift := by
  ext σ
  simp only [mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨door, notRaise⟩
    obtain ⟨τ, rfl⟩ :=
      exists_lift_eq σ (order_zero_of_mem_doorsAt_zero proper door notRaise) notRaise
    exact ⟨τ, (lift_mem_doorsAt_zero_iff proper τ).mp door, rfl⟩
  · rintro ⟨τ, complete, rfl⟩
    exact ⟨(lift_mem_doorsAt_zero_iff proper τ).mpr complete, τ.lift_not_canRaise⟩

/-- **Kuhn's lemma.** For a labelling with the boundary conditions, the number
of completely labelled simplices is odd. -/
theorem odd_card_complete (q : ℕ) :
    ∀ (n : ℕ) (label : (Fin n → ℕ) → Fin (n + 1)), Proper (q + 1) label →
      Odd (univ.filter fun σ : GridSimplex (q + 1) n => σ.Complete label).card
  | 0, label, _ => by
    have every : ∀ σ : GridSimplex (q + 1) 0, σ.Complete label := fun σ wanted =>
      ⟨0, Fin.ext (by
        have bound := wanted.2
        have other := (σ.labels label 0).2
        omega)⟩
    have one : Fintype.card (GridSimplex (q + 1) 0) = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨⟨Fin.elim0, 1⟩, fun σ =>
        GridSimplex.ext (funext fun i => i.elim0) (Subsingleton.elim _ _)⟩
    rw [filter_true_of_mem fun σ _ => every σ, card_univ, one]
    exact odd_one
  | m + 1, label, proper => by
    have previous := odd_card_complete q m (faceLabel (q + 1) label) proper.faceLabel
    rw [← ZMod.natCast_eq_one_iff_odd] at previous ⊢
    -- simplex by simplex
    have bySimplex : ((univ.filter fun σ : GridSimplex (q + 1) (m + 1) =>
        σ.Complete label).card : ZMod 2) =
        ((∑ σ : GridSimplex (q + 1) (m + 1), (doors (σ.labels label) 0).card : ℕ) : ZMod 2) := by
      rw [card_filter, Nat.cast_sum, Nat.cast_sum]
      refine sum_congr rfl fun σ _ => ?_
      rw [natCast_card_doors]
      by_cases complete : σ.Complete label
      · have surjective : Function.Surjective (σ.labels label) := complete
        rw [if_pos complete, if_pos surjective, Nat.cast_one]
      · have notSurjective : ¬Function.Surjective (σ.labels label) := complete
        rw [if_neg complete, if_neg notSurjective, Nat.cast_zero]
    -- position by position
    have byPosition : ∑ σ : GridSimplex (q + 1) (m + 1), (doors (σ.labels label) 0).card =
        ∑ k : Fin (m + 2), (doorsAt (q := q) label k).card := by
      simp only [doors, doorsAt, card_filter]
      exact sum_comm
    have split : ∑ k : Fin (m + 2), (doorsAt (q := q) label k).card =
        (doorsAt (q := q) label 0).card +
          (∑ j : Fin m, (doorsAt (q := q) label j.castSucc.succ).card +
            (doorsAt (q := q) label (Fin.last (m + 1))).card) := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last]
    have inner : ∑ j : Fin m, ((doorsAt (q := q) label j.castSucc.succ).card : ZMod 2) = 0 :=
      sum_eq_zero fun j _ =>
        ZMod.natCast_eq_zero_iff_even.mpr (even_card_doorsAt_inner label j)
    have first : (doorsAt (q := q) label 0).card =
        ((doorsAt (q := q) label 0).filter fun σ => σ.CanRaise).card +
          ((doorsAt (q := q) label 0).filter fun σ => ¬σ.CanRaise).card :=
      (card_filter_add_card_filter_not _).symm
    have last : (doorsAt (q := q) label (Fin.last (m + 1))).card =
        ((doorsAt (q := q) label 0).filter fun σ => σ.CanRaise).card := by
      rw [card_doorsAt_zero_canRaise,
        filter_true_of_mem fun σ member => canLower_of_mem_doorsAt_last proper member]
    have boundary : ((doorsAt (q := q) label 0).filter fun σ => ¬σ.CanRaise).card =
        (univ.filter fun τ : GridSimplex (q + 1) m =>
          τ.Complete (faceLabel (q + 1) label)).card := by
      rw [doorsAt_zero_not_canRaise proper, card_image_of_injective _ lift_injective]
    rw [bySimplex, byPosition, split, first, last, boundary]
    push_cast
    rw [inner, previous]
    have twice : ∀ r : ZMod 2, r + 1 + (0 + r) = 1 := by decide
    exact twice _

/-- So there is a completely labelled simplex. -/
theorem exists_complete (q n : ℕ) (label : (Fin n → ℕ) → Fin (n + 1))
    (proper : Proper (q + 1) label) : ∃ σ : GridSimplex (q + 1) n, σ.Complete label := by
  have odd := odd_card_complete q n label proper
  have positive : 0 < (univ.filter fun σ : GridSimplex (q + 1) n => σ.Complete label).card :=
    odd.pos
  obtain ⟨σ, member⟩ := card_pos.mp positive
  exact ⟨σ, (mem_filter.mp member).2⟩

end GridSimplex

/-! ## Labels `false`/`true` on every coordinate -/

section Flags

variable {n : ℕ}

/-- One more than the largest coordinate whose flag is `true`, and `0` when no
flag is `true`. -/
def topLabel (flags : Fin n → Bool) : Fin (n + 1) :=
  if nonempty : (univ.filter fun i => flags i = true).Nonempty then
    ((univ.filter fun i => flags i = true).max' nonempty).succ
  else 0

theorem flag_of_topLabel_eq_succ {flags : Fin n → Bool} {i : Fin n}
    (same : topLabel flags = i.succ) : flags i = true := by
  unfold topLabel at same
  split_ifs at same with nonempty
  · have member := max'_mem _ nonempty
    rw [Fin.succ_injective _ same] at member
    exact (mem_filter.mp member).2
  · exact absurd same.symm (Fin.succ_ne_zero i)

theorem succ_le_topLabel {flags : Fin n → Bool} {i : Fin n} (set : flags i = true) :
    i.succ ≤ topLabel flags := by
  have member : i ∈ univ.filter fun i => flags i = true := mem_filter.mpr ⟨mem_univ _, set⟩
  unfold topLabel
  rw [dif_pos ⟨i, member⟩]
  exact Fin.succ_le_succ_iff.mpr (le_max' _ _ member)

theorem flag_of_topLabel_eq_zero {flags : Fin n → Bool} (zero : topLabel flags = 0)
    (i : Fin n) : flags i = false := by
  by_contra set
  have bound := succ_le_topLabel (Bool.eq_true_of_not_eq_false set)
  rw [zero] at bound
  exact Fin.succ_ne_zero i (nonpos_iff_eq_zero.mp bound)

/-- **A cell with both labels on every coordinate.** Give every point of the
grid `{0, …, q + 1}^n` a flag for each coordinate, `false` where the
coordinate is `0` and `true` where it is `q + 1`. Then some cell has, for
every coordinate, a corner flagged `false` and a corner flagged `true`. -/
theorem exists_cell_with_both_labels (q n : ℕ) (flag : (Fin n → ℕ) → Fin n → Bool)
    (zero : ∀ x i, x i = 0 → flag x i = false)
    (top : ∀ x i, x i = q + 1 → flag x i = true) :
    ∃ base : Fin n → Fin (q + 1), ∀ i, ∃ r s : Fin n → ℕ,
      (∀ j, (base j : ℕ) ≤ r j ∧ r j ≤ base j + 1) ∧
        (∀ j, (base j : ℕ) ≤ s j ∧ s j ≤ base j + 1) ∧
          flag r i = false ∧ flag s i = true := by
  have proper : Proper (q + 1) fun x => topLabel (flag x) :=
    { ne_succ_of_eq_zero := fun x i isZero same => by
        have set := flag_of_topLabel_eq_succ same
        rw [zero x i isZero] at set
        exact Bool.false_ne_true set
      succ_le_of_eq_top := fun x i isTop => succ_le_topLabel (top x i isTop) }
  obtain ⟨σ, complete⟩ := GridSimplex.exists_complete q n _ proper
  refine ⟨σ.base, fun i => ?_⟩
  obtain ⟨low, lowLabel⟩ := complete 0
  obtain ⟨high, highLabel⟩ := complete i.succ
  exact ⟨σ.vertex low, σ.vertex high,
    fun j => ⟨σ.base_le_vertex low j, σ.vertex_le_base_add_one low j⟩,
    fun j => ⟨σ.base_le_vertex high j, σ.vertex_le_base_add_one high j⟩,
    flag_of_topLabel_eq_zero lowLabel i, flag_of_topLabel_eq_succ highLabel⟩

end Flags

/-! ## The boundary conditions are needed -/

/-- A labelling that uses one label only has no completely labelled simplex
in positive dimension: Kuhn's lemma does not hold without the boundary
conditions. -/
theorem not_exists_complete_of_constant (q m : ℕ) :
    ¬∃ σ : GridSimplex (q + 1) (m + 1), σ.Complete fun _ => 0 := by
  rintro ⟨σ, complete⟩
  obtain ⟨k, same⟩ := complete 1
  have zero : (0 : Fin (m + 2)) = 1 := same
  exact absurd zero (by simp)

/-- The constant labelling violates the condition at the top face. -/
theorem constant_not_proper (q m : ℕ) :
    ¬Proper (q + 1) fun _ : Fin (m + 1) → ℕ => (0 : Fin (m + 2)) := by
  intro proper
  have bound := proper.succ_le_of_eq_top (fun _ => q + 1) 0 rfl
  exact Fin.succ_ne_zero 0 (nonpos_iff_eq_zero.mp bound)

end Mettapedia.Combinatorics.Kuhn
