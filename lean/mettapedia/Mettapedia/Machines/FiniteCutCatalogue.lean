import Mettapedia.Machines.ShapeCutComposition
import Mathlib.Data.List.MinMax

/-!
# A complete finite catalogue of bounded structural cuts

A mask retains a subtree, replaces it by one hole, or recursively cuts the
two children. The bounded catalogue enumerates every mask of that depth.
Canonicalization removes a branch that retains both complete children;
it preserves the actual skeleton and ordered hole payloads for every term.

This is completeness within bounded structural masks, not completeness for
all payload-dependent policies or unrestricted globally optimal storage.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.FiniteCutCatalogue

open ShapeStore

inductive Mask
  | keep
  | hole
  | branch (left right : Mask)
  deriving DecidableEq, Repr

def Mask.depth : Mask → Nat
  | .keep | .hole => 0
  | .branch left right => max left.depth right.depth + 1

def Mask.cutAt : Mask → Pos → Bool
  | .keep, _ => false
  | .hole, [] => true
  | .hole, _ :: _ => false
  | .branch _ _, [] => false
  | .branch left _, false :: rest => left.cutAt rest
  | .branch _ right, true :: rest => right.cutAt rest

def Mask.cut {Atom : Type} (mask : Mask) : Cut Atom := Cut.ofPolicy fun position _ => mask.cutAt position

theorem keep_cut {Atom : Type} (term : Tm Atom) : Mask.keep.cut.d term = (term.toSkel, []) := noCut_d term

theorem hole_cut {Atom : Type} (term : Tm Atom) : Mask.hole.cut.d term = (.hole, [term]) := by
  cases term <;> rfl

theorem branch_atom {Atom : Type} (left right : Mask) (atom : Atom) :
    (Mask.branch left right).cut.d (.atom atom) = (.atom atom, []) := rfl

theorem branch_node {Atom : Type} (left right : Mask) (a b : Tm Atom) :
    (Mask.branch left right).cut.d (.node a b) =
      (.node (left.cut.d a).1 (right.cut.d b).1, (left.cut.d a).2 ++ (right.cut.d b).2) := rfl

def combine (left right : Mask) : Mask :=
  if left = .keep ∧ right = .keep then .keep else .branch left right

def normalize : Mask → Mask
  | .keep => .keep
  | .hole => .hole
  | .branch left right => combine (normalize left) (normalize right)

theorem combine_cut {Atom : Type} (left right : Mask) (term : Tm Atom) :
    (combine left right).cut.d term = (Mask.branch left right).cut.d term := by
  unfold combine
  split
  next same =>
    obtain ⟨rfl, rfl⟩ := same
    cases term with
    | atom atom => simp [keep_cut, branch_atom, Tm.toSkel]
    | node left right => simp [keep_cut, branch_node, Tm.toSkel]
  next => rfl

theorem normalize_cut {Atom : Type} (mask : Mask) (term : Tm Atom) :
    (normalize mask).cut.d term = mask.cut.d term := by
  induction mask generalizing term with
  | keep | hole => rfl
  | branch left right ihl ihr =>
      rw [normalize, combine_cut]
      cases term with
      | atom atom => rfl
      | node a b => simp only [branch_node, ihl, ihr]

theorem normalize_combine (left right : Mask) :
    normalize (combine left right) = combine (normalize left) (normalize right) := by
  unfold combine
  split
  next same => obtain ⟨rfl, rfl⟩ := same; rfl
  next => rfl

theorem normalize_idempotent (mask : Mask) : normalize (normalize mask) = normalize mask := by
  induction mask with
  | keep | hole => rfl
  | branch left right ihl ihr => simp only [normalize, normalize_combine, ihl, ihr]

theorem normalize_depth (mask : Mask) : (normalize mask).depth ≤ mask.depth := by
  induction mask with
  | keep | hole => rfl
  | branch left right ihl ihr =>
      simp only [normalize, combine]
      split
      · exact Nat.zero_le _
      · simp only [Mask.depth]
        omega

def catalogue : Nat → List Mask
  | 0 => [.keep, .hole]
  | depth + 1 => [.keep, .hole] ++ (catalogue depth).flatMap fun left =>
      (catalogue depth).map (Mask.branch left)

theorem mem_catalogue (depth : Nat) (mask : Mask) : mask ∈ catalogue depth ↔ mask.depth ≤ depth := by
  induction depth generalizing mask with
  | zero => cases mask <;> simp [catalogue, Mask.depth]
  | succ depth ih =>
      cases mask with
      | keep | hole => simp [catalogue, Mask.depth]
      | branch left right =>
          simp [catalogue, List.mem_flatMap, ih, Mask.depth]

def canonicalCatalogue (depth : Nat) : List Mask := (catalogue depth).map normalize

theorem canonical_complete (depth : Nat) (mask : Mask) (bounded : mask.depth ≤ depth) :
    normalize mask ∈ canonicalCatalogue depth :=
  List.mem_map.mpr ⟨mask, (mem_catalogue depth mask).mpr bounded, rfl⟩

def choose (depth : Nat) (cost : Mask → Nat) : Option Mask := (canonicalCatalogue depth).argmin cost

theorem chosen_member (depth : Nat) (cost : Mask → Nat) (mask : Mask)
    (chosen : choose depth cost = some mask) : mask ∈ canonicalCatalogue depth := List.argmin_mem chosen

theorem chosen_minimal (depth : Nat) (cost : Mask → Nat) (best other : Mask)
    (chosen : choose depth cost = some best) (bounded : other.depth ≤ depth) :
    cost best ≤ cost (normalize other) :=
  List.le_of_mem_argmin (canonical_complete depth other bounded) chosen

theorem choice_exists (depth : Nat) (cost : Mask → Nat) : ∃ mask, choose depth cost = some mask := by
  cases chosen : choose depth cost with
  | some mask => exact ⟨mask, rfl⟩
  | none =>
      have empty : canonicalCatalogue depth = [] := List.argmin_eq_none.mp chosen
      have present := canonical_complete depth .keep (by simp [Mask.depth])
      simp [empty] at present

theorem chosen_canonical (depth : Nat) (cost : Mask → Nat) (mask : Mask)
    (chosen : choose depth cost = some mask) : normalize mask = mask := by
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp (chosen_member depth cost mask chosen)
  exact normalize_idempotent source

namespace Controls

theorem catalogue_has_deeper_than_flat_cut :
    Mask.branch .keep (.branch .keep .hole) ∈ catalogue 2 := by decide

theorem redundant_retention_branches_normalize :
    normalize (.branch (.branch .keep .keep) .keep) = .keep := by decide

theorem distinct_depth_interfaces_remain_distinct :
    normalize (.branch .hole .hole) ≠ normalize .hole := by decide

theorem canonicalization_does_not_discard_hole_order :
    (normalize (Mask.branch .hole .hole)).cut.d (Tm.node (.atom (1 : Nat)) (.atom 2)) =
      (Skel.node .hole .hole, [.atom 1, .atom 2]) := by decide

end Controls

end Mettapedia.Machines.FiniteCutCatalogue
