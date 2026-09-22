import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.Logic.Relation

/-!
# Computed confluence of proof-retaining paths

A supplied one-step diamond operation computes joins of directed paths and of
finite zigzags. The output retains its endpoint and both directed paths in
`Type`; no existential witness is selected from a proposition. Paths and
symmetrization are Mathlib's quiver constructions.

The one-step diamond is executable input, not a consequence of merely
propositional confluence. No normalization, termination, or unique choice of
joining path is assumed. Each finite construction recurses on its input path.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Relation.PathConfluence

open Quiver

universe u v
variable {V : Type u} [Quiver.{v} V]

/-- Mapping an edge-valued path retains every edge position. -/
theorem mapPath_length {W : Type*} [Quiver W] (map : V ⥤q W)
    {source target : V} (path : Path source target) :
    (map.mapPath path).length = path.length := by
  induction path with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem reverse_length [HasReverse V] {source target : V} (path : Path source target) :
    path.reverse.length = path.length := by
  induction path with
  | nil => rfl
  | cons path edge ih =>
      exact (Path.length_comp (Quiver.reverse edge).toPath path.reverse).trans
        ((congrArg (1 + ·) ih).trans (Nat.add_comm _ _))

structure Diamond (left right : V) where
  common : V
  fromLeft : left ⟶ common
  fromRight : right ⟶ common

/-- Exchange the two input branches without changing their common endpoint. -/
def Diamond.symm {left right : V} (diamond : Diamond left right) : Diamond right left :=
  ⟨diamond.common, diamond.fromRight, diamond.fromLeft⟩

abbrev DiamondOperation (V : Type u) [Quiver.{v} V] :=
  {source left right : V} → (source ⟶ left) → (source ⟶ right) → Diamond left right

structure Strip (left right : V) where
  common : V
  fromLeft : left ⟶ common
  fromRight : Path right common

structure Join (left right : V) where
  common : V
  fromLeft : Path left common
  fromRight : Path right common

/-- Push an edge across a path by computing one diamond per path edge. -/
def strip (diamond : DiamondOperation V) {source left : V} (path : Path source left) :
    {right : V} → (source ⟶ right) → Strip left right := by
  induction path with
  | nil => intro right edge; exact ⟨right, edge, .nil⟩
  | cons path last ih =>
      intro right edge
      let earlier := ih edge
      let square := diamond last earlier.fromLeft
      exact ⟨square.common, square.fromLeft, earlier.fromRight.cons square.fromRight⟩

/-- The path produced on the other side has exactly the input's length. -/
theorem strip_length (diamond : DiamondOperation V) {source left right : V}
    (path : Path source left) (edge : source ⟶ right) :
    (strip diamond path edge).fromRight.length = path.length := by
  induction path with
  | nil => rfl
  | cons path last ih => exact congrArg Nat.succ ih

/-- Complete the finite rectangle between two directed paths. -/
def join (diamond : DiamondOperation V) {source left right : V}
    (first : Path source left) (second : Path source right) : Join left right := by
  induction second with
  | nil => exact ⟨left, .nil, first⟩
  | cons path last ih =>
      let next := strip diamond ih.fromRight last
      exact ⟨next.common, ih.fromLeft.cons next.fromLeft, next.fromRight⟩

theorem join_lengths (diamond : DiamondOperation V) {source left right : V}
    (first : Path source left) (second : Path source right) :
    (join diamond first second).fromLeft.length = second.length ∧
      (join diamond first second).fromRight.length = first.length := by
  induction second with
  | nil => exact ⟨rfl, rfl⟩
  | cons path last ih =>
      exact ⟨congrArg Nat.succ ih.1,
        (strip_length diamond (join diamond first path).fromRight last).trans ih.2⟩

/-- Count forward and backward edges without identifying different paths. -/
def directions {source : Symmetrify V} : {target : Symmetrify V} → Path source target → Nat × Nat
  | _, .nil => (0, 0)
  | _, .cons path (.inl _) => (directions path).map (· + 1) id
  | _, .cons path (.inr _) => (directions path).map id (· + 1)

/-- Symmetrifying an edge map retains the orientation of each selected edge. -/
theorem directions_map {W : Type*} [Quiver W] (map : V ⥤q W)
    {source target : Symmetrify V} (path : Path source target) :
    directions (V := W) (map.symmetrify.mapPath path) = directions path := by
  induction path with
  | nil => rfl
  | cons earlier last ih =>
      cases last with
      | inl edge => exact congrArg (fun counts : Nat × Nat => counts.map (· + 1) id) ih
      | inr edge => exact congrArg (fun counts : Nat × Nat => counts.map id (· + 1)) ih

/-- Convert a finite symmetric path to two directed paths with a common
endpoint. Every diamond is calculated from already supplied edge evidence. -/
def joinZigzag (diamond : DiamondOperation V) {source : Symmetrify V} :
    {target : Symmetrify V} → Path source target → Join (V := V) source target := by
  intro target path
  induction path with
  | nil => exact ⟨source, .nil, .nil⟩
  | cons path last ih =>
      cases last with
      | inl forward =>
          let next := strip diamond ih.fromRight forward
          exact ⟨next.common, ih.fromLeft.cons next.fromLeft, next.fromRight⟩
      | inr backward =>
          exact ⟨ih.common, ih.fromLeft, backward.toPath.comp ih.fromRight⟩

theorem joinZigzag_lengths (diamond : DiamondOperation V) {source target : Symmetrify V}
    (path : Path source target) :
    (joinZigzag diamond path).fromLeft.length = (directions path).1 ∧
      (joinZigzag diamond path).fromRight.length = (directions path).2 := by
  induction path with
  | nil => exact ⟨rfl, rfl⟩
  | cons path last ih =>
      cases last with
      | inl forward =>
          exact ⟨congrArg Nat.succ ih.1,
            (strip_length diamond (joinZigzag diamond path).fromRight forward).trans ih.2⟩
      | inr backward =>
          refine ⟨ih.1, ?_⟩
          change (backward.toPath.comp (joinZigzag diamond path).fromRight).length =
            (directions path).2 + 1
          exact (Path.length_comp (V := V) backward.toPath
            (joinZigzag diamond path).fromRight).trans
              ((congrArg (1 + ·) ih.2).trans (Nat.add_comm _ _))

/-- Forget only the retained edge identity when comparing with ordinary
relational reachability. The computed paths remain available independently. -/
theorem path_support {source target : V} (path : Path source target) :
    _root_.Relation.ReflTransGen (fun a b : V => Nonempty (a ⟶ b)) source target := by
  induction path with
  | nil => exact .refl
  | cons path edge ih => exact ih.tail ⟨edge⟩

theorem joinZigzag_support (diamond : DiamondOperation V) {source target : Symmetrify V}
    (path : Path source target) :
    _root_.Relation.Join (_root_.Relation.ReflTransGen (fun a b : V => Nonempty (a ⟶ b)))
      source target :=
  ⟨(joinZigzag diamond path).common, path_support (joinZigzag diamond path).fromLeft,
    path_support (joinZigzag diamond path).fromRight⟩

#print axioms mapPath_length
#print axioms directions_map
#print axioms strip_length
#print axioms join_lengths
#print axioms joinZigzag_lengths
#print axioms joinZigzag_support

end Mettapedia.Logic.Relation.PathConfluence
