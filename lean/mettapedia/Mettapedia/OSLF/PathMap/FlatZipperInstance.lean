import Mettapedia.OSLF.PathMap.ZipperExecution

/-!
# Flat Zipper Instance — Concrete ZipperIterationSound

A `FlatZipper α` is the simplest possible cursor model: a flat list of
values with no trie structure.  It validates that the `ZipperIterationSound`
contract is satisfiable — not vacuously true.

The cursor is just a `List α` wrapper.  Navigation is degenerate (always at
root, always at leaf, no children), and `toNextVal` simply advances the list
head.  This serves as a reference implementation for Codex's Rust PathMap
zipper.
-/

namespace Mettapedia.OSLF.PathMap.FlatZipperInstance

open Mettapedia.PathMap
open Mettapedia.OSLF.PathMap.ZipperExecution

/-- A flat (non-trie) cursor: just a list of remaining values. -/
structure FlatZipper (α : Type*) where
  /-- The remaining values to iterate.  `head` = current value. -/
  elems : List α

instance {α : Type*} : ZipperMoving (FlatZipper α) where
  descendFirstByte _ := none    -- flat: no children
  descendLastByte  _ := none
  ascend           _ := none    -- always at root
  currentPath      _ := []      -- root path is empty
  atLeaf           _ := true    -- flat: every position is a leaf
  atRoot           _ := true    -- flat: every position is the root

instance {α : Type*} : ZipperBounded (FlatZipper α) where
  ascend_none_at_root _ _ := rfl

instance {α : Type*} : ZipperValues (FlatZipper α) α where
  valueAt z := z.elems.head?

instance {α : Type*} : ZipperIteration (FlatZipper α) where
  toNextVal z := match z.elems with
    | []          => (⟨[]⟩, false)
    | [_]         => (⟨[]⟩, false)
    | _ :: rest   => (⟨rest⟩, true)
  descendLastPath z   := (z, false)
  descendFirstKPath z
    | 0     => (z, true)
    | _ + 1 => (z, false)
  toNextKPath z _ := (z, false)

instance {α : Type*} : ZipperStoreValues (FlatZipper α) α where
  allValues z := z.elems

/-! ## Soundness Proof -/

/-- Every value reachable from a `FlatZipper` is in its element list. -/
private theorem reachable_subset {α : Type*} (z : FlatZipper α) (v : α)
    (h : ZipperReachableValue z v) : v ∈ z.elems := by
  induction h with
  | here z v hv =>
    simp only [ZipperValues.valueAt] at hv
    exact List.mem_of_head? hv
  | step z v hnext _ ih =>
    match hz : z.elems with
    | [] => simp [hz, ZipperIteration.toNextVal] at hnext
    | [_] => simp [hz, ZipperIteration.toNextVal] at hnext
    | _ :: _ :: _ =>
      simp only [hz, ZipperIteration.toNextVal] at ih
      exact List.mem_cons_of_mem _ ih

/-- Every element in a `FlatZipper` is reachable by iteration. -/
private theorem elem_reachable {α : Type*} (l : List α) (v : α) (h : v ∈ l) :
    ZipperReachableValue (FlatZipper.mk l) v := by
  induction l with
  | nil => simp at h
  | cons a rest ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | hmem
    · exact .here (FlatZipper.mk (v :: rest)) v rfl
    · match hrest : rest with
      | [] => simp at hmem
      | b :: tl =>
        apply ZipperReachableValue.step (FlatZipper.mk (a :: b :: tl)) v rfl
        exact ih hmem

/-- The `FlatZipper` is iteration-sound: reachable values = stored values. -/
instance {α : Type*} : ZipperIterationSound (FlatZipper α) α where
  reachable_in_store root v _ hreach := reachable_subset root v hreach
  store_in_reachable root v _ hmem := elem_reachable root.elems v hmem

/-! ## Additional Laws -/

instance {α : Type*} : ZipperIterationRooted (FlatZipper α) where
  toNextVal_false_at_root _ _ _ _ := rfl

instance {α : Type*} : ZipperIterationZeroDepth (FlatZipper α) where
  descendFirstKPath_zero _ := ⟨rfl, rfl⟩

instance {α : Type*} : ZipperComplexity (FlatZipper α) where
  descendFirstKPath_depth_le _ k hk := by
    match k with
    | 0 => simp [ZipperMoving.currentPath]
    | _ + 1 => simp [ZipperIteration.descendFirstKPath] at hk
  toNextVal_depth_bounded _ _ := by
    simp [ZipperMoving.currentPath]

/-! ## Summary

**0 sorries. 0 axioms.**

`FlatZipper α` is a concrete, proven instance of `ZipperIterationSound`,
validating that the ZAM contract is satisfiable.  Additional law instances
(`ZipperIterationRooted`, `ZipperIterationZeroDepth`, `ZipperComplexity`)
are also proven.
-/

end Mettapedia.OSLF.PathMap.FlatZipperInstance
