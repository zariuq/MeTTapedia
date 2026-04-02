import Mettapedia.OSLF.PathMap.Trie.FiniteTrie

/-!
# Descend-Until Refinement

This file pins down the machine-level meaning of PathMap zipper
`descend_until` against the finite trie model.

The Rust behavior in `PathMap/src/zipper.rs` is:

- do nothing at a branch or leaf
- if there is exactly one child, descend
- after descending, stop as soon as a value is encountered
- otherwise keep flowing down the unique-child chain

The key point for the public `mork:` expert surface is that the stopping point
may be an **internal prefix value**, not only a leaf.
-/

namespace Mettapedia.OSLF.PathMap.Trie

open FTrie

universe u

variable {V : Type u}

namespace FTrie

/-- Root value at the current focus. -/
def rootVal? : FTrie V → Option V
  | .empty => none
  | .node val _ => val

/-- Number of child branches at the current focus. -/
def childCount : FTrie V → Nat
  | .empty => 0
  | .node _ children => children.length

/-- Pure trie model of `zipper.descend_until`.

It returns the suffix descended from the current focus:
- `[]` means no move
- otherwise it is the unique-child path until the first encountered value
  or branch/leaf. -/
def descendUntilSuffix : FTrie V → List UInt8
  | .empty => []
  | .node _ [] => []
  | .node _ [(b, child)] =>
      if (rootVal? child).isSome then
        [b]
      else
        b :: descendUntilSuffix child
  | .node _ (_ :: _ :: _) => []

/-- Descend-until from an existing cursor path in the trie. -/
def descendUntilPath (t : FTrie V) (start : List UInt8) : List UInt8 :=
  start ++ descendUntilSuffix (t.subtreeAt start)

@[simp] theorem rootVal?_empty :
    rootVal? (FTrie.empty : FTrie V) = none := rfl

@[simp] theorem rootVal?_node (val : Option V) (children : List (UInt8 × FTrie V)) :
    rootVal? (FTrie.node val children) = val := rfl

@[simp] theorem childCount_empty :
    childCount (FTrie.empty : FTrie V) = 0 := rfl

@[simp] theorem childCount_node (val : Option V) (children : List (UInt8 × FTrie V)) :
    childCount (FTrie.node val children) = children.length := rfl

@[simp] theorem descendUntilSuffix_empty :
    descendUntilSuffix (FTrie.empty : FTrie V) = [] := rfl

@[simp] theorem descendUntilSuffix_leaf (val : Option V) :
    descendUntilSuffix (FTrie.node val ([] : List (UInt8 × FTrie V))) = [] := rfl

@[simp] theorem descendUntilSuffix_branch (val : Option V)
    (c1 c2 : UInt8 × FTrie V) (rest : List (UInt8 × FTrie V)) :
    descendUntilSuffix (FTrie.node val (c1 :: c2 :: rest)) = [] := rfl

theorem descendUntilSuffix_eq_nil_of_childCount_ne_one (t : FTrie V)
    (h : childCount t ≠ 1) :
    descendUntilSuffix t = [] := by
  cases t with
  | empty =>
      rfl
  | node val children =>
      cases children with
      | nil =>
          rfl
      | cons hd tl =>
          cases tl with
          | nil =>
              simp [childCount] at h
          | cons hd2 tl2 =>
              rfl

theorem descendUntilSuffix_unary_child_value (val : Option V)
    (b : UInt8) (child : FTrie V)
    (hval : (rootVal? child).isSome = true) :
    descendUntilSuffix (FTrie.node val [(b, child)]) = [b] := by
  simp [descendUntilSuffix, hval]

theorem descendUntilSuffix_unary_child_noval (val : Option V)
    (b : UInt8) (child : FTrie V)
    (hval : (rootVal? child).isSome = false) :
    descendUntilSuffix (FTrie.node val [(b, child)]) = b :: descendUntilSuffix child := by
  simp [descendUntilSuffix, hval]

theorem descendUntilPath_extends (t : FTrie V) (start : List UInt8) :
    start <+: descendUntilPath t start := by
  refine ⟨descendUntilSuffix (t.subtreeAt start), ?_⟩
  simp [descendUntilPath]

theorem descendUntilPath_stable_of_childCount_ne_one (t : FTrie V) (start : List UInt8)
    (h : childCount (t.subtreeAt start) ≠ 1) :
    descendUntilPath t start = start := by
  simp [descendUntilPath, descendUntilSuffix_eq_nil_of_childCount_ne_one, h]

theorem descendUntilPath_stops_at_first_internal_value
    (t : FTrie V) (start : List UInt8) (val : Option V)
    (b : UInt8) (child : FTrie V)
    (hfocus : t.subtreeAt start = FTrie.node val [(b, child)])
    (hval : (rootVal? child).isSome = true) :
    descendUntilPath t start = start ++ [b] := by
  simp [descendUntilPath, hfocus, descendUntilSuffix, hval]

theorem descendUntilSuffix_stops (t : FTrie V) :
    (rootVal? (t.subtreeAt (descendUntilSuffix t))).isSome = true ∨
      childCount (t.subtreeAt (descendUntilSuffix t)) ≠ 1 := by
  cases t with
  | empty =>
      right
      simp [descendUntilSuffix, FTrie.subtreeAt, childCount]
  | node val children =>
      cases children with
      | nil =>
          right
          simp [descendUntilSuffix, FTrie.subtreeAt, childCount]
      | cons hd tl =>
          cases tl with
          | nil =>
              obtain ⟨b, child⟩ := hd
              by_cases hval : (rootVal? child).isSome = true
              · left
                simp [descendUntilSuffix, hval, FTrie.subtreeAt, FTrie.subtreeAt_nil]
              · simpa [descendUntilSuffix, hval, FTrie.subtreeAt] using
                  descendUntilSuffix_stops child
          | cons hd2 tl2 =>
              right
              simp [descendUntilSuffix, FTrie.subtreeAt, childCount]

/-! ## Examples -/

def internalValueTrie : FTrie Unit :=
  FTrie.node none
    [(1, FTrie.node (some ()) [(2, FTrie.node (some ()) [(3, FTrie.node none
      [(4, FTrie.node (some ()) [])])])])]

def branchTrie : FTrie Unit :=
  FTrie.node none [(1, FTrie.node (some ()) []), (2, FTrie.node (some ()) [])]

/-- Positive example: from the root, descend-until stops at the first internal value. -/
example :
    descendUntilSuffix internalValueTrie = [1] := by
  rfl

/-- Positive example: starting on an internal value with one child descends to the next value. -/
example :
    descendUntilPath internalValueTrie [1] = [1, 2] := by
  rfl

/-- Negative example: at a branch, descend-until does not move. -/
example :
    descendUntilSuffix branchTrie = [] := by
  rfl

/-- Negative example: the branch root already satisfies the stopping condition. -/
example :
    childCount (branchTrie.subtreeAt (descendUntilSuffix branchTrie)) ≠ 1 := by
  decide

/-! ## Summary

**0 sorries. 0 axioms.**

This file settles the plain-trie meaning of `descend_until`:

- branches/leaves are stable (`descendUntilSuffix_eq_nil_of_childCount_ne_one`)
- unary descent stops at the first encountered internal value
- otherwise it keeps flowing down the unique-child chain
- the final focus satisfies the Rust stopping condition

This is the theorem slice needed before lifting the same machine truth to
overlay and product zippers.
-/

end FTrie

end Mettapedia.OSLF.PathMap.Trie
