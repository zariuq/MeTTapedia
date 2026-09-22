import Mettapedia.Logic.Relation.PathConfluence

/-!
# Nondegenerate computed path joins and a divergent fork

Two independently incremented counters have a concrete diamond operation.
The joining algorithm computes a rectangle while retaining distinct orders of
increment. A terminal fork has no such operation, so the construction's input
cannot be replaced by arbitrary local transitions.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Relation.PathConfluence.Examples

open Quiver

structure Counter where
  left : Nat
  right : Nat
  deriving DecidableEq

inductive Increment : Counter → Counter → Type where
  | left (a b : Nat) : Increment ⟨a, b⟩ ⟨a + 1, b⟩
  | right (a b : Nat) : Increment ⟨a, b⟩ ⟨a, b + 1⟩

instance : Quiver Counter := ⟨Increment⟩

def counterDiamond : DiamondOperation Counter := by
  intro source left right first second
  cases first with
  | left a b =>
      cases second with
      | left => exact ⟨⟨a + 2, b⟩, .left _ _, .left _ _⟩
      | right => exact ⟨⟨a + 1, b + 1⟩, .right _ _, .left _ _⟩
  | right a b =>
      cases second with
      | left => exact ⟨⟨a + 1, b + 1⟩, .left _ _, .right _ _⟩
      | right => exact ⟨⟨a, b + 2⟩, .right _ _, .right _ _⟩

def horizontal : Path (⟨0, 0⟩ : Counter) ⟨2, 0⟩ :=
  .cons (.cons .nil (Increment.left 0 0)) (Increment.left 1 0)

def vertical : Path (⟨0, 0⟩ : Counter) ⟨0, 2⟩ :=
  .cons (.cons .nil (Increment.right 0 0)) (Increment.right 0 1)

theorem rectangle_computes :
    (join counterDiamond horizontal vertical).common = ⟨2, 2⟩ ∧
      (join counterDiamond horizontal vertical).fromLeft.length = 2 ∧
      (join counterDiamond horizontal vertical).fromRight.length = 2 := ⟨rfl, rfl, rfl⟩

def leftThenRight : Path (⟨0, 0⟩ : Counter) ⟨1, 1⟩ :=
  .cons (.cons .nil (Increment.left 0 0)) (Increment.right 1 0)

def rightThenLeft : Path (⟨0, 0⟩ : Counter) ⟨1, 1⟩ :=
  .cons (.cons .nil (Increment.right 0 0)) (Increment.left 0 1)

theorem order_is_retained : leftThenRight ≠ rightThenLeft := by
  intro equal
  have middle := Path.obj_eq_of_cons_eq_cons (show leftThenRight = rightThenLeft from equal)
  have impossible := congrArg Counter.left middle
  cases impossible

def counterZigzag : @Path (Symmetrify Counter) _ ⟨2, 0⟩ ⟨0, 2⟩ :=
  .cons (.cons (.cons (.cons .nil (.inr (Increment.left 1 0)))
    (.inr (Increment.left 0 0))) (.inl (Increment.right 0 0))) (.inl (Increment.right 0 1))

theorem zigzag_computes :
    (joinZigzag counterDiamond counterZigzag).common = ⟨2, 2⟩ ∧
      (joinZigzag counterDiamond counterZigzag).fromLeft.length = 2 ∧
      (joinZigzag counterDiamond counterZigzag).fromRight.length = 2 := ⟨rfl, rfl, rfl⟩

inductive Fork where
  | source | left | right

inductive ForkEdge : Fork → Fork → Type where
  | left : ForkEdge .source .left
  | right : ForkEdge .source .right

instance : Quiver Fork := ⟨ForkEdge⟩

theorem fork_has_no_diamond : ¬ Nonempty (DiamondOperation Fork) := by
  rintro ⟨diamond⟩
  have edge := (diamond ForkEdge.left ForkEdge.right).fromLeft
  cases edge

private theorem left_path_target {target : Fork} (path : Path Fork.left target) : target = .left := by
  induction path with
  | nil => rfl
  | cons path edge ih => subst ih; cases edge

private theorem right_path_target {target : Fork} (path : Path Fork.right target) : target = .right := by
  induction path with
  | nil => rfl
  | cons path edge ih => subst ih; cases edge

theorem fork_has_no_join : ¬ Nonempty (Join (V := Fork) .left .right) := by
  rintro ⟨joined⟩
  have incompatible := (left_path_target joined.fromLeft).symm.trans (right_path_target joined.fromRight)
  cases incompatible

#print axioms counterDiamond
#print axioms rectangle_computes
#print axioms order_is_retained
#print axioms zigzag_computes
#print axioms fork_has_no_diamond
#print axioms fork_has_no_join

#eval ((joinZigzag counterDiamond counterZigzag).common.left,
  (joinZigzag counterDiamond counterZigzag).common.right,
  (joinZigzag counterDiamond counterZigzag).fromLeft.length,
  (joinZigzag counterDiamond counterZigzag).fromRight.length)

end Mettapedia.Logic.Relation.PathConfluence.Examples
