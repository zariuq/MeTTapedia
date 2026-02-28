import Mettapedia.OSLF.PathMap.Core

/-!
# PathMap Zipper Interface

Lean 4 formalization of the PathMap `zipper` module trait hierarchy.

A **zipper** is a cursor into a trie that can move around and inspect or modify
the trie at its current focus.  The Rust trait hierarchy is:

```
ZipperMoving      -- navigation + path inspection
  └─ ZipperValues             -- read value at focus (known V)
       └─ ZipperReadOnlyValues      -- read-only variant
  └─ ZipperWriting            -- mutating the trie at focus
  └─ ZipperSubtries           -- subtree-level operations
  └─ ZipperIteration          -- depth-first enumeration helpers
       └─ ZipperReadOnlyIteration
  └─ ZipperProduct            -- parallel zipper products
  └─ ZipperForking            -- copy/branch the cursor
  └─ ZipperAbsolutePath       -- access full path from trie root
  └─ ZipperPathBuffer         -- buffered path accumulation
```

## Key Invariant

> "A zipper's focus may not be moved above the zipper's root."

In Lean we encode this as a `Prop` class `ZipperBounded z root` asserting that
every movement operation on a `ZipperMoving z` stays within the subtrie rooted
at `root`.  Concrete implementations carry this as a proof obligation.

## References
- PathMap crate docs: https://docs.rs/pathmap/latest/pathmap/zipper/index.html
- ZipperIteration:   https://docs.rs/pathmap/latest/pathmap/zipper/trait.ZipperIteration.html
- PathMap book:      `1.01.00_algebraic_ops.md`
-/

namespace Mettapedia.PathMap

/-! ## Path types -/

/-- A byte-sequence key — the type of paths in a PathMap trie.
    PathMap uses `[u8]` slices as keys; we model them as `List UInt8`. -/
abbrev TriePath := List UInt8

/-! ## ZipperMoving — navigation interface -/

/-- Abstract interface for moving a zipper cursor around a trie and inspecting
    the current path.

    Mirrors `pathmap::zipper::ZipperMoving`.

    Operations:
    - `descendFirstByte` / `descendLastByte`: move to first/last child
    - `ascend`: move up one byte level toward the root
    - `currentPath`: the path bytes from root to current focus
    - `atLeaf`: true when focus is a leaf (no children)
    - `atRoot`: true when focus is at the zipper's root

    **Invariant**: `ascend` must not move above the zipper's root
    (see `ZipperBounded`). -/
class ZipperMoving (Z : Type*) where
  /-- Descend into the first (lexicographically smallest) child byte. -/
  descendFirstByte : Z → Option Z
  /-- Descend into the last (lexicographically largest) child byte. -/
  descendLastByte  : Z → Option Z
  /-- Ascend one byte toward the root.  Returns `none` if already at root. -/
  ascend           : Z → Option Z
  /-- The sequence of bytes from the zipper's root to the current focus. -/
  currentPath      : Z → TriePath
  /-- True if the current focus has no children. -/
  atLeaf           : Z → Bool
  /-- True if the current focus is at the zipper's root. -/
  atRoot           : Z → Bool

/-- The fundamental zipper invariant: `ascend` never goes above the root.
    If `atRoot z = true`, then `ascend z = none`. -/
class ZipperBounded (Z : Type*) [ZipperMoving Z] : Prop where
  ascend_none_at_root : ∀ z : Z, ZipperMoving.atRoot z = true →
      ZipperMoving.ascend z = none

/-- Liveness dual of `ZipperBounded`: when the cursor is not at the root,
    ascending always succeeds.

    Together with `ZipperBounded`, this gives a bijection between
    "at root ↔ ascend fails", ensuring the root predicate is equivalent
    to the structural condition that no parent exists. -/
class ZipperLiveness (Z : Type*) [ZipperMoving Z] : Prop where
  ascend_succeeds : ∀ z : Z, ZipperMoving.atRoot z = false →
      ZipperMoving.ascend z ≠ none

/-! ## ZipperValues — value access -/

/-- Read access to the value stored at the zipper's current focus.
    `valueAt z` is `none` when the focus is an internal node with no stored value.

    Mirrors `pathmap::zipper::ZipperValues` (known value type `V`). -/
class ZipperValues (Z : Type*) (V : Type*) extends ZipperMoving Z where
  /-- The value at the current focus, if any. -/
  valueAt : Z → Option V

/-- Read-only subset: everything in `ZipperValues` but no writes. -/
class ZipperReadOnlyValues (Z : Type*) (V : Type*) extends ZipperValues Z V

/-! ## ZipperWriting — trie mutation -/

/-- Write interface: create, update, or remove entries in the trie.

    Mirrors `pathmap::zipper::ZipperWriting`. -/
class ZipperWriting (Z : Type*) (V : Type*) extends ZipperValues Z V where
  /-- Set the value at the current focus. -/
  setValue   : Z → V → Z
  /-- Remove the value (if any) at the current focus. -/
  clearValue : Z → Z
  /-- Remove the entire subtrie rooted at the current focus. -/
  pruneSubtrie : Z → Z

/-! ## ZipperIteration — depth-first traversal helpers -/

/-- Advanced navigation for systematic iteration over all values or all paths
    at a given depth.

    Mirrors `pathmap::zipper::ZipperIteration`.

    **Not dyn-compatible** (trait objects not supported for this interface). -/
class ZipperIteration (Z : Type*) [ZipperMoving Z] where
  /-- Advance to the next value in depth-first order.
      Returns `false` if no more values exist (focus restored to root). -/
  toNextVal         : Z → Z × Bool

  /-- Navigate to the terminal node of the rightmost path reachable from focus.
      Equivalent to repeatedly calling `descendLastByte`.
      Returns `false` (with `z` unchanged) if already at path's end. -/
  descendLastPath   : Z → Z × Bool

  /-- Descend exactly `k` bytes by following first children at each branch.
      Non-constant time; typically O(log n).
      Returns `false` (with `z` unchanged) if no k-depth path exists. -/
  descendFirstKPath : Z → Nat → Z × Bool

  /-- Move to the next sibling at the same path depth (k bytes from a common
      ancestor).  Returns `false` (focus restored to k-step ancestor) on
      exhaustion. -/
  toNextKPath       : Z → Nat → Z × Bool

/-! ## ZipperIteration laws -/

/-- If `toNextVal z = (z', false)`, then the focus is back at the root
    (all values have been enumerated). -/
class ZipperIterationRooted (Z : Type*) [ZipperMoving Z] [ZipperIteration Z] : Prop where
  toNextVal_false_at_root : ∀ z z' : Z,
      (ZipperIteration.toNextVal z).2 = false →
      (ZipperIteration.toNextVal z).1 = z' →
      ZipperMoving.atRoot z' = true

/-- `descendFirstKPath z 0` should succeed and leave `z` unchanged. -/
class ZipperIterationZeroDepth (Z : Type*) [ZipperMoving Z] [ZipperIteration Z] : Prop where
  descendFirstKPath_zero : ∀ z : Z,
      (ZipperIteration.descendFirstKPath z 0).2 = true ∧
      (ZipperIteration.descendFirstKPath z 0).1 = z

/-- Completeness dual of `ZipperIterationRooted`: iteration from the root
    eventually visits every position in the trie.

    Formally: for every target position `z` and root position `root`,
    there exists `n` such that iterating `toNextVal` exactly `n` times from
    `root` lands on `z`.  This ensures the depth-first enumeration is exhaustive. -/
class ZipperIterationComplete (Z : Type*) [ZipperMoving Z] [ZipperIteration Z] : Prop where
  iteration_complete : ∀ (target root : Z),
      ZipperMoving.atRoot root = true →
      ∃ n : Nat,
        (Nat.iterate (fun s => (ZipperIteration.toNextVal s).1) n root) = target

/-! ## ZipperComplexity — formal O(k) / O(depth) complexity contracts -/

/-- **Depth-bound contracts** for `descendFirstKPath` and `toNextVal`.

    These axioms constrain **path-length growth** (structural depth), not wall-clock
    time.  They are the necessary preconditions for O(k) / O(depth) time complexity,
    but an implementation must also bound the *per-step work* to achieve those
    time bounds — which is not formalised here (Lean lacks a standard cost model).

    Concretely:
    - `descendFirstKPath z k` descends **at most** `k` levels: result depth ≤ start + k.
    - `toNextVal z` advances by at most one DFS level: result depth ≤ start + 1.

    A concrete implementation satisfying these bounds can achieve O(k) and O(depth)
    time if each descent/advance step costs O(1) work. -/
class ZipperComplexity (Z : Type*) [ZipperMoving Z] [ZipperIteration Z] : Prop where
  /-- `descendFirstKPath z k` descends at most `k` levels: path length grows by at most k. -/
  descendFirstKPath_depth_le : ∀ (z : Z) (k : Nat),
    (ZipperIteration.descendFirstKPath z k).2 = true →
    (ZipperMoving.currentPath (ZipperIteration.descendFirstKPath z k).1).length ≤
    (ZipperMoving.currentPath z).length + k
  /-- `toNextVal z` stays within one DFS level of `z` (depth grows by at most 1). -/
  toNextVal_depth_bounded : ∀ (z : Z),
    (ZipperIteration.toNextVal z).2 = true →
    (ZipperMoving.currentPath (ZipperIteration.toNextVal z).1).length ≤
    (ZipperMoving.currentPath z).length + 1

/-! ## ZipperAbsolutePath — root-relative paths -/

/-- Access the full path from the trie's global root (not just the zipper root)
    to the current focus.

    Mirrors `pathmap::zipper::ZipperAbsolutePath`. -/
class ZipperAbsolutePath (Z : Type*) [ZipperMoving Z] where
  /-- Full byte-path from the trie root to current focus. -/
  absolutePath : Z → TriePath

/-- Absolute path extends relative path: `absolutePath z` ends with
    `currentPath z`. -/
class ZipperAbsolutePathSpec (Z : Type*) [ZipperMoving Z] [ZipperAbsolutePath Z] : Prop where
  absolutePath_suffix : ∀ z : Z,
      (ZipperMoving.currentPath z).IsSuffix (ZipperAbsolutePath.absolutePath z)

/-! ## ZipperForking — cursor duplication -/

/-- Duplicate the cursor so independent traversals can diverge.

    Mirrors `pathmap::zipper::ZipperForking`. -/
class ZipperForking (Z : Type*) [ZipperMoving Z] where
  /-- Clone the current cursor position for independent traversal. -/
  fork : Z → Z × Z

/-- Forking produces two cursors with identical paths. -/
class ZipperForkingSpec (Z : Type*) [ZipperMoving Z] [ZipperForking Z] : Prop where
  fork_same_path : ∀ z l r : Z,
      ZipperForking.fork z = (l, r) →
      ZipperMoving.currentPath l = ZipperMoving.currentPath r

/-! ## AlgebraicStatus — in-place operation result -/

/-- Status returned by in-place algebraic operations (e.g. `join_into`).

    Mirrors `pathmap::ring::AlgebraicStatus`.

    - `none`     : operation produced the empty/bottom result; discard
    - `identity` : output is structurally identical to one or both inputs
    - `modified` : the in-place target was modified -/
inductive AlgebraicStatus where
  | none     : AlgebraicStatus
  | identity : AlgebraicStatus
  | modified : AlgebraicStatus
  deriving Repr, DecidableEq

/-! ## Lattice extension: join_into and join_all -/

/-- In-place join (consumes `other`, mutates `self`).

    Mirrors `Lattice::join_into`. -/
class PathMapLatticeInPlace (α : Type*) extends PathMapLattice α where
  /-- In-place union: incorporate `other` into `self`. -/
  joinInto : α → α → α × AlgebraicStatus

/-- Fold-join over a non-empty list of elements.

    `join_all [x₁, x₂, …, xₙ]` = x₁ ⊔ x₂ ⊔ … ⊔ xₙ.
    Returns `none` if the list is empty. -/
def joinAll {α : Type*} [PathMapLattice α] (xs : List α) : Option (AlgebraicResult α) :=
  match xs with
  | []      => .none
  | x :: rest => some <| rest.foldl (fun acc y =>
      match acc with
      | .none         => .element y               -- lift next element cleanly
      | .identity s o => AlgebraicResult.identity s o
      | .element v    => PathMapLattice.pjoin v y) (.element x)

/-! ## None-precedence invariant (ring.rs documentation) -/

/-- When both `None` and `Identity` are conceptually valid for an operation
    result, `None` takes precedence.

    Formally: if `op a b = .none` is a valid description (inputs annihilate),
    the implementation must return `.none` rather than `.identity`.

    We encode this as a Prop on `pjoin`: if `pjoin a b = .none` then the
    resolved value is always `Option.none`. -/
class NonePrecedesIdentity (α : Type*) [PathMapLattice α] : Prop where
  none_precedes : ∀ a b : α,
      PathMapLattice.pjoin a b = .none →
      (PathMapLattice.pjoin a b).resolve a b = .none

/-! ## Non-commutativity invariant for psubtract -/

/-- `psubtract` is not commutative; its `Identity` results must only assert
    `SELF_IDENT` (the left operand).  The right operand is never declared
    identical to the result.

    Formally: `psubtract a b` never returns `.identity false true` or
    `.identity false false` in the identity arm — those would assert that the
    result equals `b` (counter), which subtraction cannot guarantee. -/
class SubtractLeftBiased (α : Type*) [PathMapDistributiveLattice α] : Prop where
  psubtract_not_counter_ident : ∀ a b : α,
      PathMapDistributiveLattice.psubtract a b ≠ .identity false true

/-- `Finset.psubtract` satisfies left-biasedness. -/
instance {α : Type*} [DecidableEq α] : SubtractLeftBiased (Finset α) where
  psubtract_not_counter_ident a b := by
    simp only [PathMapDistributiveLattice.psubtract]
    split_ifs <;> simp [AlgebraicResult.identity.injEq]

/-! ## ZipperSubtries — extract a subtrie as a new PathMap -/

/-- Extract everything below the zipper's focus as a new store.

    `makeMap z = some σ` means the subtrie at the current focus was
    materialised into a fresh `σ` value.  `none` means there is nothing
    at or below the focus.

    Mirrors `pathmap::zipper::ZipperSubtries`.

    Design note (from docs): open question whether the root value of the focus
    node should be included as the root of the returned map; implementations
    may differ. -/
class ZipperSubtries (Z : Type*) (σ : Type*) [ZipperMoving Z] [PathMapLattice σ] where
  /-- Extract the subtrie at the current focus. -/
  makeMap : Z → Option σ

/-- If `makeMap z = some m`, then `m` is non-empty (not the bottom element).
    Encodes the docs.rs invariant: `None` is returned precisely when no
    subtrie exists. -/
class ZipperSubtriesNonEmpty (Z : Type*) (σ : Type*) [ZipperMoving Z] [PathMapLattice σ]
    [ZipperSubtries Z σ] : Prop where
  makeMap_some_not_none : ∀ (z : Z) (m : σ),
      ZipperSubtries.makeMap z = some m →
      PathMapLattice.pmeet m m ≠ .none

/-! ## ZipperProduct — composite multi-zipper -/

/-- A product zipper combines several independent zippers into one structure,
    with a notion of "focus factor" (which sub-zipper currently holds focus)
    and "path indices" (split points in the shared path buffer).

    Mirrors `pathmap::zipper::ZipperProduct`.

    - `factorCount` ≥ 1 (the primary factor is always present).
    - `focusFactor` ∈ [0, factorCount).
    - `pathIndices` has length `focusFactor`. -/
class ZipperProduct (Z : Type*) extends ZipperMoving Z where
  /-- Number of component zippers (≥ 1). -/
  factorCount : Z → Nat
  /-- Which component currently holds the focus (0 = primary). -/
  focusFactor : Z → Nat
  /-- Path-buffer split indices; length equals `focusFactor`. -/
  pathIndices : Z → List Nat

/-- Invariants on `ZipperProduct` indices. -/
class ZipperProductSpec (Z : Type*) [ZipperProduct Z] : Prop where
  factorCount_pos  : ∀ z : Z, 0 < ZipperProduct.factorCount z
  focusFactor_lt   : ∀ z : Z,
      ZipperProduct.focusFactor z < ZipperProduct.factorCount z
  pathIndices_len  : ∀ z : Z,
      (ZipperProduct.pathIndices z).length = ZipperProduct.focusFactor z

/-! ## ZipperPathBuffer — low-level path buffer control -/

/-- Direct control over the zipper's internal path buffer.

    These are the low-level primitives underlying all zipper movement.
    In Rust they are partially `unsafe` (caller must avoid uninitialised reads).
    In Lean we model only the safe, high-level contracts.

    Mirrors `pathmap::zipper::ZipperPathBuffer`. -/
class ZipperPathBuffer (Z : Type*) extends ZipperMoving Z where
  /-- Return the origin path up to `len` bytes.
      Safe precondition: `len ≤ (currentPath z).length`. -/
  originPathPrefix : Z → Nat → TriePath
  /-- Ensure the path buffer is allocated (no-op if already ready). -/
  prepareBuffers   : Z → Z
  /-- Reserve at least `n` bytes in the path buffer.
      Monotone: never shrinks the buffer. -/
  reserveBuffers   : Z → Nat → Z

/-- `originPathPrefix z n` is the first `n` bytes of `currentPath z`. -/
class ZipperPathBufferSpec (Z : Type*) [ZipperPathBuffer Z] : Prop where
  originPathPrefix_take : ∀ z : Z, ∀ n : Nat,
      n ≤ (ZipperMoving.currentPath z).length →
      ZipperPathBuffer.originPathPrefix z n =
        (ZipperMoving.currentPath z).take n

/-! ## ZipperReadOnlyIteration — iteration with value read-back -/

/-- Combines `ZipperIteration` with `ZipperReadOnlyValues`: after advancing
    to the next value, immediately return a reference to it.

    Mirrors `pathmap::zipper::ZipperReadOnlyIteration`. -/
class ZipperReadOnlyIteration (Z : Type*) (V : Type*)
    [ZipperMoving Z] [ZipperIteration Z] [ZipperReadOnlyValues Z V] where
  /-- Advance to the next value and return it.
      Returns `none` when the zipper has returned to its root (enumeration
      complete). -/
  toNextGetVal : Z → Z × Option V

/-- `toNextGetVal` is consistent with `toNextVal` and `valueAt`:
    the returned value equals the value at the new position (if any). -/
class ZipperReadOnlyIterationSpec (Z : Type*) (V : Type*)
    [ZipperMoving Z] [ZipperIteration Z]
    [ZipperReadOnlyValues Z V]
    [ZipperReadOnlyIteration Z V] : Prop where
  toNextGetVal_consistent : ∀ (z z' : Z) (v : V),
      ZipperReadOnlyIteration.toNextGetVal z = (z', some v) →
      ZipperValues.valueAt z' = some v

/-! ## ZipperCreation — instantiate zippers at given paths -/

/-- Result of attempting to create a zipper: succeeds with a zipper or fails
    with a conflict (access violation in a concurrent/exclusive-access context).

    Mirrors the `Result<Zipper, Conflict>` return type of `ZipperCreation`. -/
inductive ZipperCreateResult (Z : Type*) where
  /-- Successfully created a zipper. -/
  | ok      : Z → ZipperCreateResult Z
  /-- Access conflict (e.g. exclusive path already held). -/
  | conflict : ZipperCreateResult Z
  deriving Repr

/-- Factory for creating read and write zippers from a root store.

    Mirrors `pathmap::zipper::ZipperCreation`. -/
class ZipperCreation (Root : Type*) (ReadZ WriteZ : Type*)
    [ZipperMoving ReadZ] [ZipperMoving WriteZ] where
  /-- Create a read-only zipper rooted at `path` within `root`. -/
  readZipperAtPath  : Root → TriePath → ZipperCreateResult ReadZ
  /-- Create a mutable zipper rooted at `path` within `root`.
      Exclusive access: fails if another write zipper holds an overlapping path. -/
  writeZipperAtPath : Root → TriePath → ZipperCreateResult WriteZ
  /-- Release a write zipper back to the root, pruning any dangling paths. -/
  cleanupWriteZipper : Root → WriteZ → Root

/-- Postcondition: a successfully created zipper starts at the requested path. -/
class ZipperCreationSpec (Root ReadZ WriteZ : Type*)
    [ZipperMoving ReadZ] [ZipperMoving WriteZ]
    [inst : ZipperCreation Root ReadZ WriteZ] : Prop where
  readZipper_path : ∀ (root : Root) (p : TriePath) (z : ReadZ),
      inst.readZipperAtPath root p = ZipperCreateResult.ok z →
      ZipperMoving.currentPath z = p
  writeZipper_path : ∀ (root : Root) (p : TriePath) (z : WriteZ),
      inst.writeZipperAtPath root p = ZipperCreateResult.ok z →
      ZipperMoving.currentPath z = p

/-! ## ZipperFunctorDerivative — zipper as ∂PathMap/∂V -/

/-- A zipper is the "one-hole context" or derivative of the PathMap functor
    with respect to its value type `V`.

    Concretely: given a zipper `Z` (a context with a hole) and a focus value
    `V`, we can reconstruct the full `Root`-typed trie; conversely, a trie
    with a chosen path gives a (zipper, value) pair.

    This formalizes McBride's "clowns and jokers" insight (2001):
    `Zipper V ≅ ∂PathMap/∂V`.

    Compare: `ZipperCreation` creates fresh zippers; this typeclass states the
    round-trip identity that characterises zippers as *contexts*. -/
class ZipperFunctorDerivative (Root : Type*) (Z V : Type*)
    [ZipperMoving Z] [ZipperValues Z V]
    [ZipperWriting Z V] [ZipperAbsolutePath Z] where
  /-- Fill the zipper's hole with value `v` to reconstruct the full trie. -/
  plugin  : Z → V → Root
  /-- Extract a (zipper, focus-value) pair from a trie at a given path.
      Returns `none` if the path has no associated value. -/
  unplug  : Root → TriePath → Option (Z × V)

/-- Round-trip law: `unplug` followed by `plugin` recovers the original trie.
    This is the "zipper = derivative" invariant: plugging the hole back in
    undoes the act of unplugging. -/
class ZipperFunctorDerivativeSpec (Root : Type*) (Z V : Type*)
    [ZipperMoving Z] [ZipperValues Z V]
    [ZipperWriting Z V] [ZipperAbsolutePath Z]
    [inst : ZipperFunctorDerivative Root Z V] : Prop where
  /-- `unplug r p = some (z, v)` → `plugin z v = r`. -/
  unplug_plugin : ∀ (r : Root) (p : TriePath) (z : Z) (v : V),
      inst.unplug r p = some (z, v) →
      inst.plugin z v = r
  /-- The unplugged zipper's absolute path matches the requested path. -/
  unplug_path : ∀ (r : Root) (p : TriePath) (z : Z) (v : V),
      inst.unplug r p = some (z, v) →
      ZipperAbsolutePath.absolutePath z = p

end Mettapedia.PathMap
