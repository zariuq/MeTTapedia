import Mettapedia.Machines.Cursor.PartialViewIndex

/-!
# A partial observation index retains its publication boundary

The known prefix uses its index candidates; the uninspected suffix remains
available for demand-driven observation. These regions are disjoint. Another
query may extend the index while this reader is suspended, but it may not
silently extend this reader's retained posting prefix into its own suffix.

The source list is a semantic observer. The native state can retain source
and posting end positions instead of copying that list. Capturing ends of
append-only postings removes the replay without per-row revalidation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ObservationFrontier

open SemanticTermView PartialViewIndex

def frontier (query : Focus) (paths : List Path) (cache : Cache)
    (source : List Nat) (covered : Nat) : List Nat :=
  candidates query paths cache (source.take covered) ++ source.drop covered

theorem frontier_sublist (query : Focus) (paths : List Path) (cache : Cache)
    (source : List Nat) (covered : Nat) :
    (frontier query paths cache source covered).Sublist source := by
  have selected : ((source.take covered).filter (candidate query paths cache)).Sublist
      (source.take covered) := List.filter_sublist
  have whole := selected.append (List.Sublist.refl (source.drop covered))
  simpa only [frontier, candidates, List.take_append_drop] using whole

theorem frontier_no_duplicate (query : Focus) (paths : List Path) (cache : Cache)
    (source : List Nat) (covered : Nat) (unique : source.Nodup) :
    (frontier query paths cache source covered).Nodup :=
  unique.sublist (frontier_sublist query paths cache source covered)

theorem frontier_count (query : Focus) (paths : List Path) (cache : Cache)
    (source : List Nat) (covered : Nat) :
    (frontier query paths cache source covered).length ≤ source.length :=
  (frontier_sublist query paths cache source covered).length_le

/-- Only proved nonmatches disappear from the known prefix. Every remaining
pure resolver answer, its binding payload and multiplicity are preserved. -/
theorem frontier_answers {Answer : Type} (store : Store) (cache : Cache)
    (valid : Valid store cache) (query : Focus) (paths : List Path)
    (resolve : Nat → List Answer)
    (sound : ∀ occurrence answer, answer ∈ resolve occurrence →
      Unifies query.denote (store occurrence).denote)
    (source : List Nat) (covered : Nat) :
    (frontier query paths cache source covered).flatMap resolve = source.flatMap resolve := by
  rw [frontier, List.flatMap_append,
    resolver_answers_preserved store cache valid query paths resolve sound,
    ← List.flatMap_append, List.take_append_drop]

/-- A posting may grow without changing a previously retained end. -/
theorem retained_posting_end (known appended : List Nat) :
    (known ++ appended).take known.length = known := by simp

theorem extension_keeps_cursor_frontier (known appended rest : List Nat) :
    (known ++ appended).take known.length ++ rest = known ++ rest := by simp

namespace Controls

theorem unbounded_growth_replays :
    ([0] ++ [1, 2, 3]) ++ ([0, 1, 2, 3] : List Nat).drop 1 =
      [0, 1, 2, 3, 1, 2, 3] := by decide

theorem captured_end_refutes_replay :
    (([0] ++ [1, 2, 3] : List Nat).take 1) ++ [0, 1, 2, 3].drop 1 =
      [0, 1, 2, 3] := by decide

theorem replay_changes_the_bag :
    ([0, 1, 2, 3, 1, 2, 3] : List Nat).count 2 = 2 ∧
      ([0, 1, 2, 3] : List Nat).count 2 = 1 := by decide

end Controls

end Mettapedia.Machines.Cursor.ObservationFrontier
