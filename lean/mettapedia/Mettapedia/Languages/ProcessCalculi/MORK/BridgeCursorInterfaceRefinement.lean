import Mettapedia.OSLF.PathMap.OverlayZipperRefinement
import Mettapedia.OSLF.PathMap.ProductZipperRefinement
import Mettapedia.OSLF.PathMap.Trie.SubtrieSnapshotSemantics
import Mettapedia.OSLF.PathMap.Trie.SubtreeSorted

/-!
# Bridge Cursor Interface Refinement

Connects the bridge-level cursor API used by the MORK/CeTTa integration to the
already-settled PathMap trie, overlay, and product semantics.

The bridge layer keeps explicit absolute cursor paths and rebuilds focused
zipper states from immutable snapshots. The point of this file is to say
exactly what those bridge operations mean mathematically.

## What this file covers

- plain bridge cursors over a frozen `FTrie Unit` snapshot
- overlay bridge cursors over frozen base/overlay snapshots
- product bridge cursors over frozen factor snapshots
- rooted snapshot export (`fork` / `subspace`) versus structural subtrie export

## What this file does not cover

- dependent zipper semantics
- write-side mutation semantics
- exact parser/rendering details for `path-of-atom`
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.OSLF.PathMap
open Mettapedia.OSLF.PathMap.Trie
open Mettapedia.OSLF.PathMap.Trie.FTrie
open Mettapedia.OSLF.PathMap.OverlayZipperRefinement

/-! ## Plain bridge cursor -/

/-- Bridge-level plain cursor state: a frozen snapshot plus an absolute byte path. -/
structure BridgeCursorState where
  snapshot : FTrie Unit
  path : List UInt8

namespace BridgeCursorState

/-- The focused trie seen by the bridge cursor. -/
def focusTrie (bc : BridgeCursorState) : FTrie Unit :=
  bc.snapshot.subtreeAt bc.path

/-- Structural path-existence flag exposed by the bridge cursor. -/
def pathExists (bc : BridgeCursorState) : Bool :=
  rootPathExists bc.focusTrie

/-- Root-value flag exposed by the bridge cursor. -/
def isVal (bc : BridgeCursorState) : Bool :=
  rootIsVal bc.focusTrie

/-- Child-count visible at the bridge cursor focus. -/
def childCount (bc : BridgeCursorState) : Nat :=
  FTrie.childCount bc.focusTrie

/-- Absolute descend-until target chosen by the bridge cursor. -/
def descendUntilTarget (bc : BridgeCursorState) : List UInt8 :=
  FTrie.descendUntilPath bc.snapshot bc.path

/-- Rooted snapshot exported by `fork` / `subspace`. -/
def snapshotSubspace (bc : BridgeCursorState) : FTrie Unit :=
  bc.snapshot.snapshotAt bc.path

/-- Structural subtrie export at the same focus, included to contrast the API
choice actually used by the bridge. -/
def structuralSubspace (bc : BridgeCursorState) : FTrie Unit :=
  bc.snapshot.structuralSubtrieAt bc.path

/-- `fork` rebuilds a cursor at the root of the rooted snapshot. -/
def forked (bc : BridgeCursorState) : BridgeCursorState :=
  ⟨bc.snapshotSubspace, []⟩

theorem pathExists_eq_focus_rootPathExists (bc : BridgeCursorState) :
    bc.pathExists = rootPathExists bc.focusTrie := rfl

theorem isVal_eq_focus_rootIsVal (bc : BridgeCursorState) :
    bc.isVal = rootIsVal bc.focusTrie := rfl

theorem childCount_eq_focus_childCount (bc : BridgeCursorState) :
    bc.childCount = FTrie.childCount bc.focusTrie := rfl

theorem isVal_eq_lookup (bc : BridgeCursorState) :
    bc.isVal = (bc.snapshot.lookup bc.path).isSome := by
  simp [BridgeCursorState.isVal, BridgeCursorState.focusTrie, rootIsVal,
    FTrie.rootVal?_subtreeAt_eq_lookup]

theorem snapshotSubspace_lookup (bc : BridgeCursorState) (q : List UInt8) :
    bc.snapshotSubspace.lookup q = bc.snapshot.lookup (bc.path ++ q) := by
  simpa [BridgeCursorState.snapshotSubspace, FTrie.snapshotAt] using
    FTrie.subtreeAt_lookup bc.snapshot bc.path q

theorem structuralSubspace_lookup_nil (bc : BridgeCursorState) :
    bc.structuralSubspace.lookup [] = none := by
  simpa [BridgeCursorState.structuralSubspace] using
    FTrie.structuralSubtrieAt_lookup_nil bc.snapshot bc.path

theorem structuralSubspace_lookup_cons (bc : BridgeCursorState)
    (b : UInt8) (suffix : List UInt8) :
    bc.structuralSubspace.lookup (b :: suffix) =
      bc.snapshot.lookup (bc.path ++ b :: suffix) := by
  simpa [BridgeCursorState.structuralSubspace] using
    FTrie.structuralSubtrieAt_lookup_cons bc.snapshot bc.path b suffix

theorem snapshotSubspace_lookup_nil_eq_isVal_lookup (bc : BridgeCursorState) :
    bc.snapshotSubspace.lookup [] = bc.snapshot.lookup bc.path := by
  simpa using bc.snapshotSubspace_lookup []

theorem descendUntilTarget_eq_path_append_suffix (bc : BridgeCursorState) :
    bc.descendUntilTarget =
      bc.path ++ FTrie.descendUntilSuffix bc.focusTrie := by
  simp [BridgeCursorState.descendUntilTarget, BridgeCursorState.focusTrie,
    FTrie.descendUntilPath]

theorem descendUntilTarget_stable_of_childCount_ne_one (bc : BridgeCursorState)
    (h : bc.childCount ≠ 1) :
    bc.descendUntilTarget = bc.path := by
  simpa [BridgeCursorState.childCount, BridgeCursorState.focusTrie,
    BridgeCursorState.descendUntilTarget] using
    FTrie.descendUntilPath_stable_of_childCount_ne_one bc.snapshot bc.path h

theorem forked_path_eq_nil (bc : BridgeCursorState) :
    bc.forked.path = [] := rfl

theorem forked_pathExists_eq_original (bc : BridgeCursorState) :
    bc.forked.pathExists = bc.pathExists := by
  simp [BridgeCursorState.forked, BridgeCursorState.pathExists,
    BridgeCursorState.focusTrie, BridgeCursorState.snapshotSubspace,
    FTrie.snapshotAt, rootPathExists, FTrie.subtreeAt_nil]

theorem forked_isVal_eq_original (bc : BridgeCursorState) :
    bc.forked.isVal = bc.isVal := by
  simp [BridgeCursorState.forked, BridgeCursorState.isVal,
    BridgeCursorState.focusTrie, BridgeCursorState.snapshotSubspace,
    FTrie.snapshotAt, rootIsVal, FTrie.subtreeAt_nil]

theorem forked_childCount_eq_original (bc : BridgeCursorState) :
    bc.forked.childCount = bc.childCount := by
  simp [BridgeCursorState.forked, BridgeCursorState.childCount,
    BridgeCursorState.focusTrie, BridgeCursorState.snapshotSubspace,
    FTrie.snapshotAt, FTrie.subtreeAt_nil]

theorem path_append_forked_descendUntilTarget_eq_original (bc : BridgeCursorState) :
    bc.path ++ bc.forked.descendUntilTarget = bc.descendUntilTarget := by
  rw [bc.descendUntilTarget_eq_path_append_suffix]
  simp [BridgeCursorState.forked, BridgeCursorState.descendUntilTarget,
    BridgeCursorState.snapshotSubspace, BridgeCursorState.focusTrie,
    FTrie.snapshotAt, FTrie.descendUntilPath, FTrie.subtreeAt_nil]

end BridgeCursorState

/-! ## Overlay bridge cursor -/

/-- Bridge-level overlay cursor state: frozen base/overlay tries plus an
absolute byte path. -/
structure BridgeOverlayCursorState where
  base : FTrie Unit
  overlay : FTrie Unit
  path : List UInt8

namespace BridgeOverlayCursorState

/-- Root overlay represented by the bridge cursor. -/
def rootOverlay (bc : BridgeOverlayCursorState) : OverlayTrie Unit :=
  { base := bc.base, local_ := bc.overlay }

/-- Focused overlay trie obtained by descending the absolute bridge path. -/
def focusedOverlay (bc : BridgeOverlayCursorState) : OverlayTrie Unit :=
  bc.rootOverlay.descendPath bc.path

/-- Overlay bridge path-existence flag at the current focus. -/
def pathExists (bc : BridgeOverlayCursorState) : Bool :=
  overlay_path_exists bc.focusedOverlay []

/-- Overlay bridge root-value flag at the current focus. -/
def isVal (bc : BridgeOverlayCursorState) : Bool :=
  overlay_is_val bc.focusedOverlay

/-- Overlay bridge child-count at the current focus. -/
def childCount (bc : BridgeOverlayCursorState) : Nat :=
  overlay_child_count bc.focusedOverlay

/-- Absolute descend-until target chosen from the current bridge focus. -/
def descendUntilTarget (bc : BridgeOverlayCursorState) : List UInt8 :=
  bc.path ++ overlay_descend_until_target bc.focusedOverlay

theorem focusedOverlay_eq_subtreeOverlay
    (base overlay : FTrie Unit) (path : List UInt8) :
    (BridgeOverlayCursorState.focusedOverlay ⟨base, overlay, path⟩) =
      { base := base.subtreeAt path, local_ := overlay.subtreeAt path } := by
  induction path generalizing base overlay with
  | nil =>
      simp [BridgeOverlayCursorState.focusedOverlay, BridgeOverlayCursorState.rootOverlay,
        OverlayTrie.descendPath, FTrie.subtreeAt_nil]
  | cons b rest ih =>
      simpa [BridgeOverlayCursorState.focusedOverlay, BridgeOverlayCursorState.rootOverlay,
        OverlayTrie.descendPath, OverlayTrie.descendByte, FTrie.subtreeAt_append,
        List.singleton_append] using
        ih (base.subtreeAt [b]) (overlay.subtreeAt [b])

theorem pathExists_eq_focusedOverlay (bc : BridgeOverlayCursorState) :
    bc.pathExists = overlay_path_exists bc.focusedOverlay [] := rfl

theorem isVal_eq_focusedOverlay (bc : BridgeOverlayCursorState) :
    bc.isVal = overlay_is_val bc.focusedOverlay := rfl

theorem childCount_eq_focusedOverlay (bc : BridgeOverlayCursorState) :
    bc.childCount = overlay_child_count bc.focusedOverlay := rfl

theorem descendUntilTarget_stable_of_childCount_ne_one
    (bc : BridgeOverlayCursorState) (h : bc.childCount ≠ 1) :
    bc.descendUntilTarget = bc.path := by
  simp [BridgeOverlayCursorState.descendUntilTarget]
  exact overlay_descend_until_target_stable_of_childCount_ne_one bc.focusedOverlay h

theorem descendUntilTarget_stops
    (bc : BridgeOverlayCursorState)
    (hOverlay : bc.overlay.Sorted) (hBase : bc.base.Sorted) :
    overlay_path_exists bc.focusedOverlay (overlay_descend_until_target bc.focusedOverlay) = true ∨
      OverlayTrie.childCountAt bc.focusedOverlay (overlay_descend_until_target bc.focusedOverlay) ≠ 1 := by
  have hFocusedOverlay : bc.focusedOverlay.local_.Sorted := by
    rw [focusedOverlay_eq_subtreeOverlay bc.base bc.overlay bc.path]
    simpa using
      FTrie.subtreeAt_sorted bc.overlay bc.path hOverlay
  have hFocusedBase : bc.focusedOverlay.base.Sorted := by
    rw [focusedOverlay_eq_subtreeOverlay bc.base bc.overlay bc.path]
    simpa using
      FTrie.subtreeAt_sorted bc.base bc.path hBase
  simpa using
    overlay_descend_until_target_stops bc.focusedOverlay hFocusedOverlay hFocusedBase

end BridgeOverlayCursorState

/-! ## Product bridge cursor -/

namespace ProductCursor

/-- Multi-byte descent for the stitched product cursor state. -/
def descendPath : ProductCursor → List UInt8 → ProductCursor
  | pc, [] => pc
  | pc, b :: rest => descendPath (pc.descendByte b) rest

theorem descendPath_nil (pc : ProductCursor) :
    descendPath pc [] = pc := rfl

theorem descendPath_cons (pc : ProductCursor) (b : UInt8) (rest : List UInt8) :
    descendPath pc (b :: rest) = descendPath (pc.descendByte b) rest := rfl

end ProductCursor

/-- Bridge-level product cursor state: a nonempty primary factor, remaining
factors, and an absolute byte path. -/
structure BridgeProductCursorState where
  primary : FTrie Unit
  rest : List (FTrie Unit)
  path : List UInt8

namespace BridgeProductCursorState

/-- Root stitched cursor represented by the bridge. -/
def rootCursor (bc : BridgeProductCursorState) : ProductCursor :=
  ProductCursor.ofFactors bc.primary bc.rest

/-- Focused stitched cursor obtained by descending the absolute bridge path. -/
def focusedCursor (bc : BridgeProductCursorState) : ProductCursor :=
  ProductCursor.descendPath bc.rootCursor bc.path

/-- Product bridge path-existence flag at the current focus. -/
def pathExists (bc : BridgeProductCursorState) : Bool :=
  bc.focusedCursor.pathExists

/-- Product bridge root-value flag at the current focus. -/
def isVal (bc : BridgeProductCursorState) : Bool :=
  bc.focusedCursor.isVal

/-- Product bridge child-count at the current focus. -/
def childCount (bc : BridgeProductCursorState) : Nat :=
  bc.focusedCursor.childCount

/-- Absolute descend-until target chosen from the current stitched focus. -/
noncomputable def descendUntilTarget (bc : BridgeProductCursorState) : List UInt8 :=
  bc.path ++ bc.focusedCursor.descendUntilSuffix

theorem pathExists_eq_focusedCursor (bc : BridgeProductCursorState) :
    bc.pathExists = bc.focusedCursor.pathExists := rfl

theorem isVal_eq_focusedCursor (bc : BridgeProductCursorState) :
    bc.isVal = bc.focusedCursor.isVal := rfl

theorem childCount_eq_focusedCursor (bc : BridgeProductCursorState) :
    bc.childCount = bc.focusedCursor.childCount := rfl

theorem descendUntilTarget_stable_of_childCount_ne_one
    (bc : BridgeProductCursorState) (h : bc.childCount ≠ 1) :
    bc.descendUntilTarget = bc.path := by
  simp [BridgeProductCursorState.descendUntilTarget]
  exact ProductCursor.descendUntilSuffix_eq_nil_of_childCount_ne_one bc.focusedCursor h

end BridgeProductCursorState

/-! ## Examples -/

open BridgeCursorState
open BridgeOverlayCursorState
open BridgeProductCursorState

/-- Positive example: bridge fork keeps the focused value visible at the new root. -/
example :
    (BridgeCursorState.mk
      (FTrie.node none [(1, FTrie.node (some ()) [(2, FTrie.node (some ()) [])])])
      [1]).forked.isVal = true := by
  decide

/-- Negative example: the structural export clears that root value instead. -/
example :
    (BridgeCursorState.mk
      (FTrie.node none [(1, FTrie.node (some ()) [(2, FTrie.node (some ()) [])])])
      [1]).structuralSubspace.lookup [] = none := by
  decide

/-- Positive example: overlay bridge descent can stop at an internal value in
the focused virtual overlay trie. -/
example :
    let bc : BridgeOverlayCursorState :=
      ⟨FTrie.singleton [1, 2, 3] (), FTrie.singleton [1] (), []⟩
    bc.descendUntilTarget = [1] := by
  simp [BridgeOverlayCursorState.descendUntilTarget, BridgeOverlayCursorState.focusedOverlay,
    BridgeOverlayCursorState.rootOverlay, overlay_descend_until_target,
    OverlayTrie.descendPath, OverlayTrie.descendUntilPath, OverlayTrie.virtualTrie,
    FTrie.singleton, FTrie.join, FTrie.joinChildren, FTrie.descendUntilPath,
    FTrie.descendUntilSuffix, FTrie.subtreeAt, FTrie.rootVal?]

/-- Positive example: after descending an exact singleton overlay to its target,
both structural existence and value presence remain true at the reached focus. -/
example :
    let bc : BridgeOverlayCursorState :=
      ⟨FTrie.singleton [1, 2, 3] (), FTrie.singleton [1, 2, 3] (), []⟩
    let moved : BridgeOverlayCursorState := { bc with path := bc.descendUntilTarget }
    moved.pathExists = true ∧ moved.isVal = true := by
  simp [BridgeOverlayCursorState.pathExists, BridgeOverlayCursorState.isVal,
    BridgeOverlayCursorState.focusedOverlay, BridgeOverlayCursorState.rootOverlay,
    BridgeOverlayCursorState.descendUntilTarget, overlay_path_exists,
    overlay_lookup_exists, overlay_is_val, overlay_descend_until_target,
    OverlayTrie.descendPath, OverlayTrie.descendUntilPath, OverlayTrie.descendByte,
    OverlayTrie.lookup, trie_root_path_exists, OverlayTrie.virtualTrie, FTrie.lookup,
    FTrie.singleton, FTrie.join, FTrie.joinChildren, FTrie.descendUntilPath,
    FTrie.descendUntilSuffix, FTrie.subtreeAt, FTrie.rootVal?]

/-- Negative example: product bridge descend-until does not move at a visible
branch. -/
example :
    let bc : BridgeProductCursorState :=
      ⟨FTrie.node none [(1, FTrie.node (some ()) []), (2, FTrie.node none [])], [], []⟩
    bc.descendUntilTarget = [] := by
  simp [BridgeProductCursorState.descendUntilTarget, BridgeProductCursorState.focusedCursor,
    BridgeProductCursorState.rootCursor, ProductCursor.ofFactors, ProductCursor.descendPath]
  apply ProductCursor.descendUntilSuffix_eq_nil_of_childCount_ne_one
  simp [ProductCursor.childCount]

/-! ## Summary

This file makes the bridge API mathematically explicit:

- plain cursor state is a snapshot plus an absolute path into it
- `fork` / `subspace` use rooted snapshots, not structural subtries
- overlay cursor observables are determined by the focused virtual overlay trie
- product cursor observables are determined by the focused stitched product cursor

That is the theorem layer needed so CeTTa-facing cursor operations stay aligned
with the PathMap substrate already formalized below them.
-/

end Mettapedia.Languages.ProcessCalculi.MORK
