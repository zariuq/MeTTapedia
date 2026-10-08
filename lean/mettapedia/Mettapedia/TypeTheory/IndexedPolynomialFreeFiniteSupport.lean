import Mettapedia.TypeTheory.IndexedPolynomialFree
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite occurrence bounds and support of free indexed trees

A polynomial with finite recursive positions has a finite number of leaf
occurrences in each free tree. Relabeling preserves that occurrence count,
while a finite support records the independently supplied reading of its
leaves. Agreement on that support suffices for equality of relabeled trees.
The bound counts occurrences rather than distinct variable values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.IndexedPolynomial.Free

open Classical
open scoped BigOperators

universe b i s p h k n

variable {Base : Type b} {Index : Base → Type i}
variable (P : IndexedPolynomial.{b, i, s, p} Base Index)
variable (finite : ∀ {base index} (shape : P.Shape base index), Finite (P.Position shape))
variable {H : (base : Base) → Index base → Type h}
variable {K : (base : Base) → Index base → Type k}

def leafCount : ∀ base index, P.Free H base index → Nat :=
  fold P (fun _ _ _ => 1) ⟨fun _ _ layer =>
    let _ : Fintype (P.Position layer.1) := @Fintype.ofFinite _ (finite layer.1)
    ∑ position, layer.2 position⟩

@[simp]
theorem leafCount_pure {base : Base} {index : Index base} (value : H base index) :
    leafCount P finite base index (pure P value) = 1 := rfl

theorem leafCount_node {base : Base} {index : Index base}
    (shape : P.Shape base index) (children : ∀ position, P.Free H base (P.next shape position)) :
    leafCount P finite base index (node P shape children) =
      let _ : Fintype (P.Position shape) := @Fintype.ofFinite _ (finite shape)
      ∑ position, leafCount P finite base _ (children position) := rfl

def support {Names : Type n} (read : ∀ base index, H base index → Names) :
    ∀ base index, P.Free H base index → Finset Names :=
  fold P (fun base index value => {read base index value}) ⟨fun _ _ layer =>
    let _ : Fintype (P.Position layer.1) := @Fintype.ofFinite _ (finite layer.1)
    Finset.univ.biUnion layer.2⟩

@[simp]
theorem support_pure {Names : Type n} (read : ∀ base index, H base index → Names)
    {base : Base} {index : Index base} (value : H base index) :
    support P finite read base index (pure P value) = {read base index value} := rfl

theorem support_node {Names : Type n} (read : ∀ base index, H base index → Names)
    {base : Base} {index : Index base} (shape : P.Shape base index)
    (children : ∀ position, P.Free H base (P.next shape position)) :
    support P finite read base index (node P shape children) =
      let _ : Fintype (P.Position shape) := @Fintype.ofFinite _ (finite shape)
      Finset.univ.biUnion (fun position => support P finite read base _ (children position)) := rfl

theorem support_card_le {Names : Type n} (read : ∀ base index, H base index → Names)
    (base : Base) (index : Index base) (term : P.Free H base index) :
    (support P finite read base index term).card ≤ leafCount P finite base index term := by
  induction term with
  | roll shape children ih =>
      cases shape with
      | inl value =>
          have empty : children = fun position => position.elim := by
            funext position
            exact position.elim
          subst children
          change (support P finite read base _ (pure P value)).card ≤ leafCount P finite base _ (pure P value)
          simp only [support_pure, leafCount_pure, Finset.card_singleton, le_refl]
      | inr shape =>
          dsimp only [withHoles] at children ih
          let _ : Fintype (P.Position shape) := @Fintype.ofFinite _ (finite shape)
          change (Finset.univ.biUnion
            (fun position => support P finite read base _ (children position))).card ≤
              ∑ position, leafCount P finite base _ (children position)
          exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun position _ => ih position))

/-- The complete leaf occurrence count is independent of variable identification. -/
theorem leafCount_map (mapping : ∀ base index, H base index → K base index)
    (base : Base) (index : Index base) (term : P.Free H base index) :
    leafCount P finite base index (map P mapping base index term) =
      leafCount P finite base index term := by
  unfold leafCount map
  rw [fold_bind]
  rfl

theorem support_map {Names : Type n} (read : ∀ base index, K base index → Names)
    (mapping : ∀ base index, H base index → K base index)
    (base : Base) (index : Index base) (term : P.Free H base index) :
    support P finite read base index (map P mapping base index term) =
      support P finite (fun base index value => read base index (mapping base index value))
        base index term := by
  unfold support map
  rw [fold_bind]
  rfl

/-- Only the supplied finite support matters when relabeling the complete tree. -/
theorem map_eq_of_support {Names : Type n} (read : ∀ base index, H base index → Names)
    (first second : ∀ base index, H base index → K base index)
    (base : Base) (index : Index base) (term : P.Free H base index)
    (agrees : ∀ index (value : H base index),
      read base index value ∈ support P finite read base _ term →
        first base index value = second base index value) :
    map P first base index term = map P second base index term := by
  induction term with
  | roll shape children ih =>
      cases shape with
      | inl value =>
          have empty : children = fun position => position.elim := by
            funext position
            exact position.elim
          subst children
          change ∀ index (value_1 : H base index),
            read base index value_1 ∈ support P finite read base _ (pure P value) →
              first base index value_1 = second base index value_1 at agrees
          change pure P (first base _ value) = pure P (second base _ value)
          exact congrArg (pure P) (agrees _ value (by simp [support_pure]))
      | inr shape =>
          dsimp only [withHoles] at children ih
          let _ : Fintype (P.Position shape) := @Fintype.ofFinite _ (finite shape)
          change map P first base _ (node P shape children) = map P second base _ (node P shape children)
          rw [map_node, map_node]
          congr 1
          funext position
          apply ih position
          intro index value member
          apply agrees index value
          change read base index value ∈ Finset.univ.biUnion
            (fun position => support P finite read base _ (children position))
          exact Finset.mem_biUnion.mpr ⟨position, Finset.mem_univ position, member⟩

end Mettapedia.TypeTheory.IndexedPolynomial.Free
