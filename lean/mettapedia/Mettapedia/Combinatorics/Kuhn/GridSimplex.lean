import Mettapedia.Combinatorics.Kuhn.LabelSequences
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype

/-!
# Simplices of Kuhn's triangulation of a grid

The grid `{0, …, p}^n` is cut into the `p^n` unit cells, and each cell into
`n!` simplices: one for each order in which the `n` coordinates can take a unit
step from the lower corner of the cell to its upper corner. A simplex is thus a
cell together with a schedule of `n` independent steps; its vertices are the
`n + 1` points visited.

Three operations move between simplices that share a facet:

* `swapStep j`: exchange two consecutive steps. All vertices but one stay.
* `rotateUp`: start one step later and take the skipped step last. The cell
  moves up along that coordinate.
* `rotateDown`: the inverse.

These are all the neighbours of a simplex across a facet (Kuhn 1960). Only the
vertex identities below are needed for the parity argument in
`Combinatorics/Kuhn/Parity.lean`; that every facet has at most two simplices
is not used.
-/

set_option autoImplicit false

namespace Mettapedia.Combinatorics.Kuhn

/-- A simplex of the triangulation: the lower corner of a cell of the grid
`{0, …, p}^n`, and the order in which the coordinates take their unit step. -/
@[ext]
structure GridSimplex (p n : ℕ) where
  /-- The lower corner of the cell. -/
  base : Fin n → Fin p
  /-- Step `j` raises the coordinate `order j`. -/
  order : Equiv.Perm (Fin n)
  deriving DecidableEq, Fintype

namespace GridSimplex

variable {p n m : ℕ}

/-- The vertex reached after the first `k` steps. -/
def vertex (σ : GridSimplex p n) (k : Fin (n + 1)) : Fin n → ℕ :=
  fun i => (σ.base i : ℕ) + if (σ.order.symm i : ℕ) < (k : ℕ) then 1 else 0

/-- Every vertex lies in the cell of the simplex. -/
theorem base_le_vertex (σ : GridSimplex p n) (k : Fin (n + 1)) (i : Fin n) :
    (σ.base i : ℕ) ≤ σ.vertex k i := by
  unfold vertex
  split_ifs <;> omega

theorem vertex_le_base_add_one (σ : GridSimplex p n) (k : Fin (n + 1)) (i : Fin n) :
    σ.vertex k i ≤ (σ.base i : ℕ) + 1 := by
  unfold vertex
  split_ifs <;> omega

/-- The labels of the vertices, in the order of the schedule. -/
def labels (σ : GridSimplex p n) (label : (Fin n → ℕ) → Fin (n + 1)) :
    Fin (n + 1) → Fin (n + 1) :=
  fun k => label (σ.vertex k)

/-- Every label occurs at a vertex. -/
def Complete (σ : GridSimplex p n) (label : (Fin n → ℕ) → Fin (n + 1)) : Prop :=
  Function.Surjective (σ.labels label)

instance (label : (Fin n → ℕ) → Fin (n + 1)) :
    DecidablePred fun σ : GridSimplex p n => σ.Complete label := fun σ => by
  unfold Complete
  infer_instance

/-! ## Exchanging two consecutive steps -/

/-- Exchange the steps `j` and `j + 1`. -/
def swapStep (σ : GridSimplex p (m + 1)) (j : Fin m) : GridSimplex p (m + 1) :=
  ⟨σ.base, σ.order * Equiv.swap j.castSucc j.succ⟩

theorem swapStep_swapStep (σ : GridSimplex p (m + 1)) (j : Fin m) :
    (σ.swapStep j).swapStep j = σ := by
  simp [swapStep, mul_assoc]

theorem swapStep_ne (σ : GridSimplex p (m + 1)) (j : Fin m) : σ.swapStep j ≠ σ := by
  intro same
  have orders : σ.order * Equiv.swap j.castSucc j.succ = σ.order * 1 := by
    rw [mul_one]
    exact congrArg GridSimplex.order same
  have trivial := mul_left_cancel orders
  have moved := congrArg (fun e : Equiv.Perm (Fin (m + 1)) => e j.castSucc) trivial
  simp only [Equiv.swap_apply_left, Equiv.Perm.coe_one, id_eq] at moved
  exact (Fin.castSucc_lt_succ (i := j)).ne' moved

/-- All vertices other than the one between the two steps stay. -/
theorem swapStep_vertex (σ : GridSimplex p (m + 1)) (j : Fin m) (k : Fin (m + 2))
    (other : (k : ℕ) ≠ j + 1) : (σ.swapStep j).vertex k = σ.vertex k := by
  funext i
  have applied : (σ.order * Equiv.swap j.castSucc j.succ).symm i =
      Equiv.swap j.castSucc j.succ (σ.order.symm i) := rfl
  have same : ((Equiv.swap j.castSucc j.succ (σ.order.symm i) : Fin (m + 1)) : ℕ) < (k : ℕ) ↔
      (σ.order.symm i : ℕ) < (k : ℕ) := by
    rw [Equiv.swap_apply_def]
    split_ifs with first second
    · rw [first]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    · rw [second]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    · rfl
  simp only [vertex, swapStep, applied, same]

/-! ## Rotating the schedule -/

/-- The first step can be postponed to the end: the cell above along that
coordinate exists. -/
def CanRaise (σ : GridSimplex p (m + 1)) : Prop :=
  (σ.base (σ.order 0) : ℕ) + 1 < p

/-- The last step can be taken first: the cell below along that coordinate
exists. -/
def CanLower (σ : GridSimplex p (m + 1)) : Prop :=
  0 < (σ.base (σ.order (Fin.last m)) : ℕ)

instance (σ : GridSimplex p (m + 1)) : Decidable σ.CanRaise := by
  unfold CanRaise
  infer_instance

instance (σ : GridSimplex p (m + 1)) : Decidable σ.CanLower := by
  unfold CanLower
  infer_instance

/-- Start one step later and take the skipped step last. -/
def rotateUp (σ : GridSimplex p (m + 1)) : GridSimplex p (m + 1) :=
  if raise : σ.CanRaise then
    ⟨Function.update σ.base (σ.order 0) ⟨σ.base (σ.order 0) + 1, raise⟩,
      σ.order * finRotate (m + 1)⟩
  else σ

/-- Take the last step first, from one cell below. -/
def rotateDown (σ : GridSimplex p (m + 1)) : GridSimplex p (m + 1) :=
  if _lower : σ.CanLower then
    ⟨Function.update σ.base (σ.order (Fin.last m))
        ⟨σ.base (σ.order (Fin.last m)) - 1,
          lt_of_le_of_lt (Nat.sub_le _ _) (σ.base (σ.order (Fin.last m))).2⟩,
      σ.order * (finRotate (m + 1))⁻¹⟩
  else σ

theorem rotate_symm_zero : (finRotate (m + 1)).symm 0 = Fin.last m := by
  rw [Equiv.symm_apply_eq, finRotate_last]

theorem first_iff (σ : GridSimplex p (m + 1)) (i : Fin (m + 1)) :
    i = σ.order 0 ↔ (σ.order.symm i : ℕ) = 0 := by
  rw [← Equiv.symm_apply_eq, Fin.ext_iff]
  rfl

theorem last_iff (σ : GridSimplex p (m + 1)) (i : Fin (m + 1)) :
    i = σ.order (Fin.last m) ↔ (σ.order.symm i : ℕ) = m := by
  rw [← Equiv.symm_apply_eq, Fin.ext_iff]
  rfl

theorem rotateUp_order (σ : GridSimplex p (m + 1)) (raise : σ.CanRaise) :
    σ.rotateUp.order = σ.order * finRotate (m + 1) := by
  simp [rotateUp, dif_pos raise]

theorem rotateDown_order (σ : GridSimplex p (m + 1)) (lower : σ.CanLower) :
    σ.rotateDown.order = σ.order * (finRotate (m + 1))⁻¹ := by
  simp [rotateDown, dif_pos lower]

/-- Rotating up raises the cell along the coordinate of the first step. -/
theorem rotateUp_base (σ : GridSimplex p (m + 1)) (raise : σ.CanRaise) (i : Fin (m + 1)) :
    (σ.rotateUp.base i : ℕ) = (σ.base i : ℕ) + if (σ.order.symm i : ℕ) = 0 then 1 else 0 := by
  simp only [rotateUp, dif_pos raise, Function.update_apply]
  by_cases coordinate : i = σ.order 0
  · rw [if_pos coordinate, if_pos ((σ.first_iff i).mp coordinate), coordinate]
  · rw [if_neg coordinate, if_neg fun zero => coordinate ((σ.first_iff i).mpr zero)]
    rfl

/-- Rotating down lowers the cell along the coordinate of the last step. -/
theorem rotateDown_base (σ : GridSimplex p (m + 1)) (lower : σ.CanLower) (i : Fin (m + 1)) :
    (σ.rotateDown.base i : ℕ) = (σ.base i : ℕ) - if (σ.order.symm i : ℕ) = m then 1 else 0 := by
  simp only [rotateDown, dif_pos lower, Function.update_apply]
  by_cases coordinate : i = σ.order (Fin.last m)
  · rw [if_pos coordinate, if_pos ((σ.last_iff i).mp coordinate), coordinate]
  · rw [if_neg coordinate, if_neg fun last => coordinate ((σ.last_iff i).mpr last)]
    rfl

/-- After rotating up, every step is taken one position earlier, and the first
step is taken last. -/
theorem rotateUp_order_symm (σ : GridSimplex p (m + 1)) (raise : σ.CanRaise)
    (i : Fin (m + 1)) :
    (σ.rotateUp.order.symm i : ℕ) =
      if (σ.order.symm i : ℕ) = 0 then m else (σ.order.symm i : ℕ) - 1 := by
  have applied : σ.rotateUp.order.symm i = (finRotate (m + 1)).symm (σ.order.symm i) := by
    rw [σ.rotateUp_order raise]
    rfl
  rw [applied]
  by_cases first : σ.order.symm i = 0
  · rw [first, rotate_symm_zero]
    simp
  · have nonzero : ¬(σ.order.symm i : ℕ) = 0 := fun zero => first (Fin.ext zero)
    rw [if_neg nonzero, coe_finRotate_symm_of_ne_zero first]

/-- After rotating down, every step is taken one position later, and the last
step is taken first. -/
theorem rotateDown_order_symm (σ : GridSimplex p (m + 1)) (lower : σ.CanLower)
    (i : Fin (m + 1)) :
    (σ.rotateDown.order.symm i : ℕ) =
      if (σ.order.symm i : ℕ) = m then 0 else (σ.order.symm i : ℕ) + 1 := by
  have applied : σ.rotateDown.order.symm i = finRotate (m + 1) (σ.order.symm i) := by
    rw [σ.rotateDown_order lower]
    rfl
  rw [applied]
  by_cases last : σ.order.symm i = Fin.last m
  · rw [last, finRotate_last]
    simp
  · have notLast : ¬(σ.order.symm i : ℕ) = m := fun top => last (Fin.ext top)
    rw [if_neg notLast, coe_finRotate_of_ne_last last]

/-- After rotating up, vertex `j` is the old vertex `j + 1`. -/
theorem rotateUp_vertex (σ : GridSimplex p (m + 1)) (raise : σ.CanRaise) (j : Fin (m + 1)) :
    σ.rotateUp.vertex j.castSucc = σ.vertex j.succ := by
  funext i
  have bound := (σ.order.symm i).2
  have upper := j.2
  simp only [vertex, σ.rotateUp_base raise, σ.rotateUp_order_symm raise, Fin.val_castSucc,
    Fin.val_succ]
  split_ifs <;> omega

/-- After rotating down, vertex `j + 1` is the old vertex `j`. -/
theorem rotateDown_vertex (σ : GridSimplex p (m + 1)) (lower : σ.CanLower) (j : Fin (m + 1)) :
    σ.rotateDown.vertex j.succ = σ.vertex j.castSucc := by
  funext i
  have bound := (σ.order.symm i).2
  have upper := j.2
  have positive : (σ.order.symm i : ℕ) = m → 0 < (σ.base i : ℕ) := by
    intro last
    rw [(σ.last_iff i).mpr last]
    exact lower
  simp only [vertex, σ.rotateDown_base lower, σ.rotateDown_order_symm lower, Fin.val_castSucc,
    Fin.val_succ]
  split_ifs <;> omega

theorem canLower_rotateUp (σ : GridSimplex p (m + 1)) (raise : σ.CanRaise) :
    σ.rotateUp.CanLower := by
  unfold CanLower
  have coordinate : σ.rotateUp.order (Fin.last m) = σ.order 0 := by
    rw [σ.rotateUp_order raise, Equiv.Perm.mul_apply, finRotate_last]
  rw [coordinate, σ.rotateUp_base raise, if_pos ((σ.first_iff _).mp rfl)]
  omega

theorem canRaise_rotateDown (σ : GridSimplex p (m + 1)) (lower : σ.CanLower) :
    σ.rotateDown.CanRaise := by
  unfold CanRaise
  have positive : 0 < (σ.base (σ.order (Fin.last m)) : ℕ) := lower
  have bound := (σ.base (σ.order (Fin.last m))).2
  have coordinate : σ.rotateDown.order 0 = σ.order (Fin.last m) := by
    rw [σ.rotateDown_order lower, Equiv.Perm.mul_apply]
    exact congrArg σ.order rotate_symm_zero
  rw [coordinate, σ.rotateDown_base lower, if_pos ((σ.last_iff _).mp rfl)]
  omega

theorem rotateDown_rotateUp (σ : GridSimplex p (m + 1)) (raise : σ.CanRaise) :
    σ.rotateUp.rotateDown = σ := by
  have lower := σ.canLower_rotateUp raise
  apply GridSimplex.ext
  · funext i
    apply Fin.ext
    have bound := (σ.order.symm i).2
    rw [σ.rotateUp.rotateDown_base lower, σ.rotateUp_base raise, σ.rotateUp_order_symm raise]
    by_cases first : (σ.order.symm i : ℕ) = 0
    · simp only [first, if_true]
      omega
    · simp only [first, if_false]
      have : ¬(σ.order.symm i : ℕ) - 1 = m := by omega
      simp only [this, if_false]
      omega
  · rw [σ.rotateUp.rotateDown_order lower, σ.rotateUp_order raise, mul_inv_cancel_right]

theorem rotateUp_rotateDown (σ : GridSimplex p (m + 1)) (lower : σ.CanLower) :
    σ.rotateDown.rotateUp = σ := by
  have raise := σ.canRaise_rotateDown lower
  apply GridSimplex.ext
  · funext i
    apply Fin.ext
    have bound := (σ.order.symm i).2
    have positive : (σ.order.symm i : ℕ) = m → 0 < (σ.base i : ℕ) := by
      intro last
      rw [(σ.last_iff i).mpr last]
      exact lower
    rw [σ.rotateDown.rotateUp_base raise, σ.rotateDown_base lower, σ.rotateDown_order_symm lower]
    by_cases last : (σ.order.symm i : ℕ) = m
    · have := positive last
      simp only [last, if_true]
      omega
    · simp only [last, if_false]
      have : ¬(σ.order.symm i : ℕ) + 1 = 0 := by omega
      simp only [this, if_false]
      omega
  · rw [σ.rotateDown.rotateUp_order raise, σ.rotateDown_order lower, inv_mul_cancel_right]

end GridSimplex

end Mettapedia.Combinatorics.Kuhn
