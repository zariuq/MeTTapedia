import Mettapedia.Languages.ProcessCalculi.MORK.AuthoredContextBridge
import Mettapedia.Languages.ProcessCalculi.MORK.PathMapBridge
import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec

/-!
# Bridge Workspace Surface Refinement

This file packages the explicit live-workspace surface used before any read-side
structural export happens.

- live insertion and removal act on `Space = Finset Atom`
- live exact matching is `matchOneInSpace` / `matchPattern` on that same carrier
- scheduler stepping stays on the same live workspace carrier
- single-atom updates still factor through the PathMap lattice bridge underneath

Positive example: inserting a ground atom makes it immediately available to an
exact live match.
Negative example: removing that atom makes the same exact live match disappear.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

namespace BridgeWorkspaceSurfaceRefinement

/-- The live workspace carrier used by explicit MORK mutation/query operations. -/
abbrev LiveWorkspace := Space

/-- Live insertion of one atom into a workspace. -/
abbrev liveInsertAtom (s : LiveWorkspace) (a : Atom) : LiveWorkspace :=
  s ∪ {a}

/-- Live removal of one atom from a workspace. -/
abbrev liveRemoveAtom (s : LiveWorkspace) (a : Atom) : LiveWorkspace :=
  s.erase a

/-- Exact live matching of one pattern atom against a workspace. -/
noncomputable abbrev liveMatchAtom (s : LiveWorkspace) (pat : Atom) :
    List (Subst × Atom) :=
  matchOneInSpace [] pat s

/-- Exact live matching of a whole pattern against a workspace. -/
noncomputable abbrev liveMatchPattern (s : LiveWorkspace) (p : Pattern) :
    List (Subst × Finset Atom) :=
  matchPattern [] s p

/-- One live scheduler step on a workspace. -/
noncomputable abbrev liveStep : LiveWorkspace → Option LiveWorkspace :=
  workQueueStep

/-- Bounded live scheduler execution. -/
noncomputable abbrev liveRun : Nat → LiveWorkspace → LiveWorkspace × Nat :=
  workQueueRunN

private abbrev PJ := @Mettapedia.PathMap.PathMapLattice.pjoin LiveWorkspace _
private abbrev PS := @Mettapedia.PathMap.PathMapDistributiveLattice.psubtract LiveWorkspace _

theorem liveInsertAtom_eq_union_singleton (s : LiveWorkspace) (a : Atom) :
    liveInsertAtom s a = s ∪ {a} := rfl

theorem liveRemoveAtom_eq_erase (s : LiveWorkspace) (a : Atom) :
    liveRemoveAtom s a = s.erase a := rfl

theorem liveInsertAtom_contains_new (s : LiveWorkspace) (a : Atom) :
    a ∈ liveInsertAtom s a := by
  simp [liveInsertAtom]

theorem liveInsertAtom_preserves_existing (s : LiveWorkspace) (a b : Atom)
    (hb : b ∈ s) :
    b ∈ liveInsertAtom s a := by
  simp [liveInsertAtom, hb]

theorem liveRemoveAtom_absent (s : LiveWorkspace) (a : Atom) :
    a ∉ liveRemoveAtom s a := by
  simp [liveRemoveAtom]

/-- Positive example: live insertion factors through the same singleton-join law
underlying the PathMap carrier. -/
theorem liveInsertAtom_eq_pathmap_join (s : LiveWorkspace) (a : Atom) :
    ((PJ s {a}).resolve s {a}).getD s = liveInsertAtom s a := by
  rw [pjoin_singleton_resolves]
  simp [liveInsertAtom]

/-- Negative example: live removal is exactly the singleton subtract/erase law,
not some unrelated host-side effect. -/
theorem liveRemoveAtom_eq_pathmap_subtract (s : LiveWorkspace) (a : Atom) :
    ((PS s {a}).resolve s {a}).getD ∅ = liveRemoveAtom s a := by
  simpa [liveRemoveAtom] using psubtract_singleton_erase s a

theorem liveMatchAtom_ground_mem (s : LiveWorkspace) (a : Atom)
    (hg : isGroundAtom a = true) (ha : a ∈ s) :
    ([], a) ∈ liveMatchAtom s a := by
  simpa [liveMatchAtom] using groundAtom_matchOneInSpace [] a hg s ha

theorem liveMatchAtom_spec (s : LiveWorkspace) (pat : Atom) (σ' : Subst) (a : Atom)
    (h : (σ', a) ∈ liveMatchAtom s pat) :
    a ∈ s ∧ matchAtom [] pat a = some σ' := by
  simpa [liveMatchAtom] using matchOneInSpace_spec [] pat s σ' a h

/-- Positive example: after inserting a ground atom, exact matching can retrieve
it immediately from the same live workspace. -/
theorem liveInsert_then_exactMatch (s : LiveWorkspace) (a : Atom)
    (hg : isGroundAtom a = true) :
    ([], a) ∈ liveMatchAtom (liveInsertAtom s a) a := by
  apply liveMatchAtom_ground_mem
  · exact hg
  · exact liveInsertAtom_contains_new s a

/-- Negative example: after removing an atom, the same exact live match is gone. -/
theorem liveRemove_then_noExactMatch (s : LiveWorkspace) (a : Atom)
    (ha : a ∉ s) :
    ([], a) ∉ liveMatchAtom s a := by
  intro h
  exact ha (liveMatchAtom_spec s a [] a h).1

theorem liveMatchPattern_ground_singleton_mem (s : LiveWorkspace) (a : Atom)
    (hg : isGroundAtom a = true) (ha : a ∈ s) :
    ([], ({a} : Finset Atom)) ∈ liveMatchPattern s (mkPattern [a]) := by
  simp only [liveMatchPattern, matchPattern, mkPattern]
  simp only [matchPattern.go, Finset.sdiff_empty]
  rw [List.mem_flatMap]
  refine ⟨([], a), ?_, ?_⟩
  · simpa [liveMatchAtom] using groundAtom_matchOneInSpace [] a hg s ha
  · simp

theorem liveStep_eq_workQueueStep (s : LiveWorkspace) :
    liveStep s = workQueueStep s := rfl

theorem liveRun_eq_workQueueRunN (fuel : Nat) (s : LiveWorkspace) :
    liveRun fuel s = workQueueRunN fuel s := rfl

theorem liveRun_steps_le_fuel (fuel : Nat) (s : LiveWorkspace) :
    (liveRun fuel s).2 ≤ fuel :=
  workQueueRunN_steps_le_fuel fuel s

/-! ## Examples -/

/-- Positive example: inserting a concrete atom makes it exactly matchable. -/
example :
    ([], .symbol "ember") ∈
      liveMatchAtom (liveInsertAtom (∅ : LiveWorkspace) (.symbol "ember")) (.symbol "ember") := by
  exact liveInsert_then_exactMatch (s := ∅) (a := .symbol "ember") rfl

/-- Negative example: if the atom is absent, the exact live match is absent too. -/
example :
    ([], .symbol "ember") ∉ liveMatchAtom (∅ : LiveWorkspace) (.symbol "ember") := by
  exact liveRemove_then_noExactMatch (s := ∅) (a := .symbol "ember") (by simp)

end BridgeWorkspaceSurfaceRefinement

end Mettapedia.Languages.ProcessCalculi.MORK
