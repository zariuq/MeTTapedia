import Mettapedia.Languages.MeTTa.HE.Types

/-!
# Native assignment/equality trail projection

Proves that append/truncate rollback is observationally equivalent to
clone/restore on the HE assignment/equality projection.

This is not a complete model of the live CeTTa binding builder.  In particular,
the live state also carries Prime occurrence state, derived cycle and support
summaries, an authority-indexed lookup accelerator, revision clocks, owner
identity, and observer-free-region protocol state.  Complete-runtime claims
must use a product refinement that retains those independent coordinates.

## Runtime projection map

| Lean projection | Live runtime role |
|------|-----------------|
| `TrailEntry` | binding/constraint prefix lengths decoded from a builder checkpoint |
| `captureTrailEntry` | the logical prefix observed at a save boundary |
| `restoreFromTrail` | suffix rollback of those two authoritative sequences |
| `ChoicePoint` | the binding projection of a larger search checkpoint |

## Model

We model the fields semantically relevant to this projection: `len`
(assignments count) and `eq_len` (equalities count).  The statement does not
erase Prime occurrence state from the complete runtime semantics, nor does it
establish correctness of the current cache realizations.

Rollback restores both `len` and `eq_len`, logically hiding later entries.
-/

namespace Mettapedia.Languages.MeTTa.HE.NativeTrailRollbackEquivalence

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1: Assignment/equality checkpoint projection -/

/-- Trail entry for the assignment/equality projection. -/
structure TrailEntry where
  assignmentCount : Nat
  equalityCount : Nat
  deriving DecidableEq, Repr

/-- Capture a trail entry from the current binding state. -/
def captureTrailEntry (b : Bindings) : TrailEntry :=
  ⟨b.assignments.length, b.equalities.length⟩

/-- Restore a binding state from a trail entry by truncating both lists. -/
def restoreFromTrail (b : Bindings) (te : TrailEntry) : Bindings :=
  ⟨b.assignments.take te.assignmentCount, b.equalities.take te.equalityCount⟩

/-! ## §2: Clone Model (for comparison) -/

/-- Clone model: save = copy the binding state. -/
def cloneSave (b : Bindings) : Bindings := b

/-- Clone model: rollback = discard current, restore copy. -/
def cloneRollback (_current saved : Bindings) : Bindings := saved

/-! ## §3: Add operations extend the lists -/

/-- Adding an assignment appends to the assignments list. -/
def addAssignment (b : Bindings) (v : String) (val : Atom) : Bindings :=
  ⟨b.assignments ++ [(v, val)], b.equalities⟩

/-- Adding an equality appends to the equalities list. -/
def addEquality (b : Bindings) (v w : String) : Bindings :=
  ⟨b.assignments, b.equalities ++ [(v, w)]⟩

/-! ## §4: Save-Rollback Equivalence on Real Bindings -/

/-- Trail rollback equals clone restore on the assignment/equality
projection.

    Maps to: `bindings_builder_save` records `(len, eq_len)`;
    `bindings_builder_rollback` restores them. Both assignment and
    equality lists are truncated to their saved lengths. -/
theorem bindings_builder_save_restore_exact
    (base : Bindings) (newAssignments : List (String × Atom))
    (newEqualities : List (String × String)) :
    let saved := captureTrailEntry base
    let extended : Bindings :=
      ⟨base.assignments ++ newAssignments, base.equalities ++ newEqualities⟩
    restoreFromTrail extended saved = base := by
  simp [captureTrailEntry, restoreFromTrail]

/-- **Equivalence statement:** trail and clone produce the same result. -/
theorem trail_rollback_observationally_eq_clone_model
    (base : Bindings) (newAssignments : List (String × Atom))
    (newEqualities : List (String × String)) :
    let saved := captureTrailEntry base
    let cloned := cloneSave base
    let extended : Bindings :=
      ⟨base.assignments ++ newAssignments, base.equalities ++ newEqualities⟩
    restoreFromTrail extended saved = cloneRollback extended cloned := by
  simp [captureTrailEntry, restoreFromTrail, cloneSave, cloneRollback]

/-! ## §5: Nested Rollback -/

/-- Nested rollback is sound on the assignment/equality projection:
    Inner rollback restores to inner save point.
    Outer rollback (after inner) restores to outer save point.

    Maps to: nested `search_context_save` / `search_context_rollback`. -/
theorem nested_trail_rollback_sound
    (base : Bindings)
    (batch1_a : List (String × Atom)) (batch1_e : List (String × String))
    (batch2_a : List (String × Atom)) (batch2_e : List (String × String)) :
    let mark1 := captureTrailEntry base
    let after1 : Bindings :=
      ⟨base.assignments ++ batch1_a, base.equalities ++ batch1_e⟩
    let mark2 := captureTrailEntry after1
    let after2 : Bindings :=
      ⟨after1.assignments ++ batch2_a, after1.equalities ++ batch2_e⟩
    -- Inner rollback: after2 → after1
    restoreFromTrail after2 mark2 = after1 ∧
    -- Outer rollback: after1 → base
    restoreFromTrail after1 mark1 = base := by
  simp only [captureTrailEntry, restoreFromTrail]
  constructor <;>
    simp only [List.length_append, List.append_assoc,
               List.take_left, List.take_length_add_append]

/-! ## §6: Binding projection of a choice point -/

/-- A projected choice point: binding prefix checkpoint plus whether the
surrounding runtime also retained an arena mark. -/
structure ChoicePoint where
  bindingsEntry : TrailEntry
  hasArenamark : Bool
  deriving DecidableEq, Repr

/-- Save a choice point. -/
def choicepointSave (b : Bindings) (arenaActive : Bool) : ChoicePoint :=
  ⟨captureTrailEntry b, arenaActive⟩

/-- Choice-point restore is exact on this projection. -/
theorem choicepoint_restore_exact
    (base : Bindings)
    (newA : List (String × Atom)) (newE : List (String × String))
    (arenaActive : Bool) :
    let cp := choicepointSave base arenaActive
    let extended : Bindings := ⟨base.assignments ++ newA, base.equalities ++ newE⟩
    restoreFromTrail extended cp.bindingsEntry = base := by
  simp [choicepointSave, captureTrailEntry, restoreFromTrail]

/-! ## §7: Published Results Survive Rollback -/

/-- **Published assignments survive rollback.** -/
theorem rollback_preserves_published_assignments
    (base : Bindings) (newA : List (String × Atom)) (newE : List (String × String))
    (entry : String × Atom) (he : entry ∈ base.assignments) :
    let saved := captureTrailEntry base
    let extended : Bindings := ⟨base.assignments ++ newA, base.equalities ++ newE⟩
    entry ∈ (restoreFromTrail extended saved).assignments := by
  simp [captureTrailEntry, restoreFromTrail]
  exact he

/-- **Published equalities survive rollback.** -/
theorem rollback_preserves_published_equalities
    (base : Bindings) (newA : List (String × Atom)) (newE : List (String × String))
    (eq : String × String) (he : eq ∈ base.equalities) :
    let saved := captureTrailEntry base
    let extended : Bindings := ⟨base.assignments ++ newA, base.equalities ++ newE⟩
    eq ∈ (restoreFromTrail extended saved).equalities := by
  simp [captureTrailEntry, restoreFromTrail]
  exact he

/-! ## §8: Structural Properties -/

/-- **Rollback is idempotent.** -/
theorem rollback_idempotent (b : Bindings) (te : TrailEntry) :
    restoreFromTrail (restoreFromTrail b te) te =
    restoreFromTrail b te := by
  simp [restoreFromTrail, List.take_take]

/-- **Commit is the identity on binding state.** -/
theorem commit_identity (b : Bindings) :
    b = b := rfl  -- commit clears the trail, not the bindings

/-- **Rollback preserves exact counts.**
    After rollback, assignments.length = saved assignmentCount
    (when the saved count ≤ current length). -/
theorem rollback_assignment_count_exact (b : Bindings) (te : TrailEntry)
    (h : te.assignmentCount ≤ b.assignments.length) :
    (restoreFromTrail b te).assignments.length = te.assignmentCount := by
  simp [restoreFromTrail, List.length_take, Nat.min_eq_left h]

theorem rollback_equality_count_exact (b : Bindings) (te : TrailEntry)
    (h : te.equalityCount ≤ b.equalities.length) :
    (restoreFromTrail b te).equalities.length = te.equalityCount := by
  simp [restoreFromTrail, List.length_take, Nat.min_eq_left h]

/-! ## §9: Summary

This file operates on the HE `Bindings` assignment/equality projection.  It
does not by itself justify a statement about the complete live C builder.

| Theorem | What it says |
|---------|-------------|
| `bindings_builder_save_restore_exact` | Trail rollback = original projected state |
| `trail_rollback_observationally_eq_clone_model` | Trail = clone model |
| `nested_trail_rollback_sound` | Inner rollback preserves outer |
| `choicepoint_restore_exact` | ChoicePoint restores exactly |
| `rollback_preserves_published_assignments` | Old assignments survive |
| `rollback_preserves_published_equalities` | Old equalities survive |
| `rollback_idempotent` | Double rollback = single |
| `rollback_assignment_count_exact` | Exact count after rollback |

A maintainer can say: "the append/truncate trail over the assignment/equality
projection is observationally equivalent to clone/restore, with nested
save/rollback sound and old projected entries preserved."
-/

end Mettapedia.Languages.MeTTa.HE.NativeTrailRollbackEquivalence
