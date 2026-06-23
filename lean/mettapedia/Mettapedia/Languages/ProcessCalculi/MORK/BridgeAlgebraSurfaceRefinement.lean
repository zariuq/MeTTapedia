import Mettapedia.Languages.ProcessCalculi.MORK.PathMapBridge
import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec
import Mettapedia.Languages.ProcessCalculi.MORK.BridgeCursorSurfaceRefinement
import Mettapedia.OSLF.PathMap.OverlayZipperRefinement
import Mettapedia.OSLF.PathMap.PathPrefixRestrictRefinement
import Mettapedia.OSLF.PathMap.Trie.RestrictSupportBridge
import Mettapedia.OSLF.PathMap.Trie.MeetSubtractSupportBridge
import Mettapedia.OSLF.PathMap.Trie.SortedPreservation
import Mettapedia.OSLF.PathMap.Trie.TrieRefinement

/-!
# Bridge Algebra Surface Refinement

This file packages the boundary between:

- **live MORK workspaces**, where stepping means scheduler execution over
  `Space = Finset Atom`
- **read-side structural exports**, where bridge operations act on frozen
  `FTrie Unit` snapshots and return ordinary structural results

The goal is not to introduce a new ontology. The goal is to state the current
design boundary explicitly so the runtime, CeTTa surface, and Lean story all
agree on the same layer split.

## Boundary summary

- stepping belongs to the live `Space`/scheduler layer
- `join` / `meet` / `subtract` / `prefix-restrict` on exported snapshots are
  structural trie operations
- rooted snapshots, structural subtries, and cursor observables are the bridge
  back from a live workspace into ordinary structural inspection
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.OSLF.PathMap
open Mettapedia.OSLF.PathMap.Trie
open Mettapedia.OSLF.PathMap.Trie.FTrie
open Mettapedia.OSLF.PathMap.OverlayZipperRefinement

namespace BridgeAlgebraSurfaceRefinement

/-! ## §1: Live workspace layer -/

/-- The live execution carrier used by the MORK scheduler. -/
abbrev LiveWorkspace := Space

/-- One live scheduler step on a workspace. -/
noncomputable abbrev liveStep : LiveWorkspace → Option LiveWorkspace :=
  workQueueStep

/-- Bounded live execution for at most `fuel` scheduler steps. -/
noncomputable abbrev liveRun : Nat → LiveWorkspace → LiveWorkspace × Nat :=
  workQueueRunN

theorem liveStep_eq_workQueueStep (s : LiveWorkspace) :
    liveStep s = workQueueStep s := rfl

theorem liveRun_eq_workQueueRunN (fuel : Nat) (s : LiveWorkspace) :
    liveRun fuel s = workQueueRunN fuel s := rfl

theorem liveRun_steps_le_fuel (fuel : Nat) (s : LiveWorkspace) :
    (liveRun fuel s).2 ≤ fuel :=
  workQueueRunN_steps_le_fuel fuel s

/-! ## §2: Read-side structural export layer -/

/-- Frozen structural carrier used by the read-side bridge surface. -/
abbrev StructuralExport := FTrie Unit

/-- Read-side join on frozen structural exports. -/
abbrev readJoin : StructuralExport → StructuralExport → StructuralExport :=
  FTrie.join

/-- Read-side meet on frozen structural exports. -/
abbrev readMeet : StructuralExport → StructuralExport → StructuralExport :=
  FTrie.meet

/-- Read-side subtract on frozen structural exports. -/
abbrev readSubtract : StructuralExport → StructuralExport → StructuralExport :=
  FTrie.subtract

/-- Read-side selector-shaped restriction on frozen structural exports. -/
abbrev readPrefixRestrict : StructuralExport → StructuralExport → StructuralExport :=
  FTrie.restrict

theorem readJoin_sorted (t₁ t₂ : StructuralExport) (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    (readJoin t₁ t₂).Sorted :=
  FTrie.join_sorted t₁ t₂ h₁ h₂

theorem readMeet_sorted (t₁ t₂ : StructuralExport) (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    (readMeet t₁ t₂).Sorted :=
  FTrie.meet_sorted t₁ t₂ h₁ h₂

theorem readSubtract_sorted (t₁ t₂ : StructuralExport) (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    (readSubtract t₁ t₂).Sorted :=
  FTrie.subtract_sorted t₁ t₂ h₁ h₂

theorem readPrefixRestrict_sorted (t₁ t₂ : StructuralExport)
    (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    (readPrefixRestrict t₁ t₂).Sorted :=
  FTrie.restrict_sorted t₁ t₂ h₁ h₂

/-- **Join support = union** for frozen structural exports.

    Positive example: a path present on either side survives.
    Negative example: only paths absent from both sides are excluded. -/
theorem pathSupport_readJoin_eq_union (t₁ t₂ : StructuralExport)
    (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    pathSupport (readJoin t₁ t₂) = pathSupport t₁ ∪ pathSupport t₂ := by
  have hj : (readJoin t₁ t₂).Sorted := readJoin_sorted t₁ t₂ h₁ h₂
  ext p
  constructor
  · intro hp
    have hlookup := lookup_of_pathSupport_mem _ p hj hp
    rw [FTrie.join_lookup t₁ t₂ p h₁ h₂] at hlookup
    rcases FTrie.lookup_unit t₁ p with h1 | h1 <;>
      rcases FTrie.lookup_unit t₂ p with h2 | h2 <;>
      simp [Finset.mem_union, h1, h2] at hlookup ⊢
    · exact Or.inr (pathSupport_mem_of_lookup _ _ h2)
    · exact Or.inl (pathSupport_mem_of_lookup _ _ h1)
    · exact Or.inl (pathSupport_mem_of_lookup _ _ h1)
  · intro hp
    rcases Finset.mem_union.mp hp with hp₁ | hp₂
    · have h1 := lookup_of_pathSupport_mem _ p h₁ hp₁
      have hjoin : (readJoin t₁ t₂).lookup p = some () := by
        rw [FTrie.join_lookup t₁ t₂ p h₁ h₂, h1]
        simp
      exact pathSupport_mem_of_lookup _ _ hjoin
    · have h2 := lookup_of_pathSupport_mem _ p h₂ hp₂
      have hjoin : (readJoin t₁ t₂).lookup p = some () := by
        rw [FTrie.join_lookup t₁ t₂ p h₁ h₂]
        rcases FTrie.lookup_unit t₁ p with h1 | h1 <;> simp [h1, h2]
      exact pathSupport_mem_of_lookup _ _ hjoin

theorem pathSupport_readMeet_eq_inter (t₁ t₂ : StructuralExport)
    (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    pathSupport (readMeet t₁ t₂) = pathSupport t₁ ∩ pathSupport t₂ :=
  pathSupport_meet_eq_inter t₁ t₂ h₁ h₂

theorem pathSupport_readSubtract_eq_sdiff (t₁ t₂ : StructuralExport)
    (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    pathSupport (readSubtract t₁ t₂) = pathSupport t₁ \ pathSupport t₂ :=
  pathSupport_subtract_eq_sdiff t₁ t₂ h₁ h₂

theorem pathSupport_readPrefixRestrict_eq_restrictPaths (t₁ t₂ : StructuralExport)
    (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    pathSupport (readPrefixRestrict t₁ t₂) =
      Mettapedia.PathMap.restrictPaths t₁.pathSupport t₂.pathSupport :=
  pathSupport_restrict_eq_restrictPaths t₁ t₂ h₁ h₂

/-! ## §3: Snapshot/subtrie/cursor bridge back to structural space -/

/-- Bridge plain cursor state is the canonical read-side bridge from a live
workspace to a frozen structural export. -/
abbrev PlainCursor := BridgeCursorState

/-- Overlay bridge cursor state over frozen structural exports. -/
abbrev OverlayCursor := BridgeOverlayCursorState

/-- Product bridge cursor state over frozen structural exports. -/
abbrev ProductCursorState := BridgeProductCursorState

/-- Rooted snapshot export used by `fork` / `subspace`. -/
abbrev rootedSnapshotExport (bc : PlainCursor) : StructuralExport :=
  bc.snapshotSubspace

/-- Structural subtrie export that clears the focus value at the root. -/
abbrev structuralSubtrieExport (bc : PlainCursor) : StructuralExport :=
  bc.structuralSubspace

theorem rootedSnapshotExport_lookup_nil (bc : PlainCursor) :
    (rootedSnapshotExport bc).lookup [] = bc.snapshot.lookup bc.path :=
  bc.snapshotSubspace_lookup_nil_eq_isVal_lookup

theorem structuralSubtrieExport_lookup_nil (bc : PlainCursor) :
    (structuralSubtrieExport bc).lookup [] = none :=
  bc.structuralSubspace_lookup_nil

theorem structuralSubtrieExport_lookup_cons (bc : PlainCursor)
    (b : UInt8) (suffix : List UInt8) :
    (structuralSubtrieExport bc).lookup (b :: suffix) =
      bc.snapshot.lookup (bc.path ++ b :: suffix) :=
  bc.structuralSubspace_lookup_cons b suffix

theorem forkedCursor_preserves_root_value_observable (bc : PlainCursor) :
    bc.forked.isVal = bc.isVal :=
  bc.forked_isVal_eq_original

theorem forkedCursor_preserves_childCount_observable (bc : PlainCursor) :
    bc.forked.childCount = bc.childCount :=
  bc.forked_childCount_eq_original

theorem overlayCursor_descendUntil_stops (bc : OverlayCursor)
    (hOverlay : bc.overlay.Sorted) (hBase : bc.base.Sorted) :
    overlay_path_exists bc.focusedOverlay (overlay_descend_until_target bc.focusedOverlay) = true ∨
      OverlayTrie.childCountAt bc.focusedOverlay (overlay_descend_until_target bc.focusedOverlay) ≠ 1 :=
  bc.descendUntilTarget_stops hOverlay hBase

theorem productCursor_descendUntil_stable_of_childCount_ne_one
    (bc : ProductCursorState) (h : bc.childCount ≠ 1) :
    bc.descendUntilTarget = bc.path :=
  bc.descendUntilTarget_stable_of_childCount_ne_one h

/-! ## §4: Examples -/

/-- Positive example: rooted snapshot export keeps the focus value visible at `[]`. -/
example :
    (rootedSnapshotExport
      ({ snapshot := (FTrie.node none
          [(1, FTrie.node (some ()) [(2, FTrie.node (some ()) [])])])
       , path := [1] } : PlainCursor)).lookup [] = some () := by
  let bc : PlainCursor :=
    { snapshot := (FTrie.node none
        [(1, FTrie.node (some ()) [(2, FTrie.node (some ()) [])])])
    , path := [1] }
  simpa [bc, rootedSnapshotExport, FTrie.lookup, FTrie.lookupChild] using
    rootedSnapshotExport_lookup_nil (bc := bc)

/-- Negative example: structural subtrie export clears that root value. -/
example :
    (structuralSubtrieExport
      ({ snapshot := (FTrie.node none
          [(1, FTrie.node (some ()) [(2, FTrie.node (some ()) [])])])
       , path := [1] } : PlainCursor)).lookup [] = none := by
  let bc : PlainCursor :=
    { snapshot := (FTrie.node none
        [(1, FTrie.node (some ()) [(2, FTrie.node (some ()) [])])])
    , path := [1] }
  simpa [bc, structuralSubtrieExport] using
    structuralSubtrieExport_lookup_nil (bc := bc)

/-- Positive example: read-side join keeps support from either side. -/
example :
    ([1] : List UInt8) ∈
      pathSupport (readJoin (FTrie.singleton [1] ()) (FTrie.singleton [2] ())) := by
  have h1 : (FTrie.singleton [1] () : StructuralExport).Sorted :=
    FTrie.singleton_sorted [1] ()
  have h2 : (FTrie.singleton [2] () : StructuralExport).Sorted :=
    FTrie.singleton_sorted [2] ()
  have hjoin :
      (readJoin (FTrie.singleton [1] ()) (FTrie.singleton [2] ())).lookup [1] = some () := by
    rw [FTrie.join_lookup _ _ [1] h1 h2]
    simp [FTrie.singleton, FTrie.lookup, FTrie.lookupChild]
  exact pathSupport_mem_of_lookup _ _ hjoin

/-- Negative example: read-side subtract removes rhs-supported paths. -/
example :
    ([1] : List UInt8) ∉
      pathSupport
        (readSubtract
          (FTrie.join (FTrie.singleton [1] ()) (FTrie.singleton [2] ()))
          (FTrie.singleton [1] ())) := by
  let t₁ : StructuralExport := FTrie.join (FTrie.singleton [1] ()) (FTrie.singleton [2] ())
  let t₂ : StructuralExport := FTrie.singleton [1] ()
  have h1 : t₁.Sorted := by
    dsimp [t₁]
    exact FTrie.join_sorted _ _ (FTrie.singleton_sorted [1] ()) (FTrie.singleton_sorted [2] ())
  have h2 : t₂.Sorted := by
    dsimp [t₂]
    exact FTrie.singleton_sorted [1] ()
  intro hp
  have hlookup := lookup_of_pathSupport_mem _ [1] (readSubtract_sorted t₁ t₂ h1 h2) hp
  rw [subtract_lookup t₁ t₂ [1] h1 h2] at hlookup
  dsimp [t₁, t₂] at hlookup
  simp [FTrie.singleton, FTrie.lookup, FTrie.lookupChild] at hlookup

/-! ## Summary

This packet makes the current bridge boundary explicit:

- **live layer**: stepping is `workQueueStep` / `workQueueRunN` on `Space`
- **read-side algebra**: exported snapshots use structural trie operators with
  extensional support laws
- **bridge back down**: rooted snapshots, structural subtries, and cursor
  observables explain how a live workspace becomes an ordinary structural
  object for inspection

This is the theorem packet that says the current CeTTa/MORK design is a
deliberate two-layer boundary, not an accident of implementation.
-/

end BridgeAlgebraSurfaceRefinement

end Mettapedia.Languages.ProcessCalculi.MORK
