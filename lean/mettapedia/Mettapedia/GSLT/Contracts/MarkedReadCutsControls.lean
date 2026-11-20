import Mettapedia.GSLT.Contracts.MarkedReadCuts
import Mathlib.Tactic.FinCases

/-!
# Controls for marked read composition

All cuts below come from enabled occurrence commits. The separating
examples are about the observations of the existing adaptive interpreter,
not lookups in a table of expected answers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Dependencies.MarkedReadCuts.Controls

open Mettapedia.Machines.ReadOnlyQuery (Program run)
open Mettapedia.Machines
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Commit Enabled)

inductive Place where
  | a | b | c
  deriving DecidableEq

def label : Nat → Place
  | 1 => .b
  | 2 => .c
  | _ => .a

def inPlace (place atom : Place) : Bool := decide (atom = place)

def move (old new : Nat) : Commit Nat Place :=
  ⟨{old}, ∅, {new}, []⟩

/-- Derive a concrete read view from the executed prefix and a sorted,
duplicate-free enumeration of its present occurrence identities. -/
private theorem view_of_sorted (h : History Place) (cut : h.Cut) (ids : List Nat)
    (present : ids.toFinset = h.presentAt cut) (distinct : ids.Nodup)
    (ordered : ids.Pairwise (· ≤ ·)) :
    h.view cut = ids.map (fun o => (o, h.label o)) := by
  unfold History.view orderedRows
  rw [← present, (List.toFinset_sort (· ≤ ·) distinct).mpr ordered]

/-- A single resource migrates, with a different physical occurrence at
each place. Intermediate half-moves are not cuts of this execution. -/
def migration : History Place where
  label := label
  initial := {0}
  word := [move 0 1, move 1 2]
  executed := .cons (by decide) (.cons (by decide) (.nil _))

def noneMark (h : History Place) (place : Place) (cut : h.Cut) : Mark Place h.Cut :=
  ⟨cut, Bool, .read (inPlace place) (fun rows => .pure rows.isEmpty)⟩

private abbrev cutsFor (h : History Place) (marks : List (Mark Place h.Cut)) : Set h.Cut :=
  validatingCuts h.view (readDependencies (markedReads h.view marks))

def markA := noneMark migration .a 1
def markB := noneMark migration .b 2
def markC := noneMark migration .c 0

private theorem migrationView0 : migration.view 0 = [(0, .a)] :=
  view_of_sorted migration 0 [0] (by decide) (by decide) (by decide)

private theorem migrationView1 : migration.view 1 = [(1, .b)] :=
  view_of_sorted migration 1 [1] (by decide) (by decide) (by decide)

private theorem migrationView2 : migration.view 2 = [(2, .c)] :=
  view_of_sorted migration 2 [2] (by decide) (by decide) (by decide)

theorem each_empty_read_is_actual :
    (markA.observe migration.view markA.origin).answer = true ∧
      (markB.observe migration.view markB.origin).answer = true ∧
      (markC.observe migration.view markC.origin).answer = true := by
  simp [markA, markB, markC, Mark.observe, noneMark, run, matchingRows, inPlace,
    migrationView0, migrationView1, migrationView2]

theorem each_pair_has_a_cut :
    (cutsFor migration [markA, markB]).Nonempty ∧
      (cutsFor migration [markA, markC]).Nonempty ∧
      (cutsFor migration [markB, markC]).Nonempty :=
  ⟨⟨2, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩

theorem three_have_no_common_cut :
    ¬ (cutsFor migration [markA, markB, markC]).Nonempty := by
  change ¬ ∃ cut : migration.Cut,
    Valid (readDependencies (markedReads migration.view [markA, markB, markC]))
      (migration.view cut)
  decide +kernel

theorem no_joint_replay :
    ¬ ∃ cut : migration.Cut, ∀ mark ∈ [markA, markB, markC],
      mark.observe migration.view cut = mark.observe migration.view mark.origin := by
  rintro ⟨cut, replay⟩
  exact three_have_no_common_cut
    ⟨cut, (migration.cut_replays_iff [markA, markB, markC] cut).mpr replay⟩

/-- An exact historical read of the token is certified at its origin while
the ordinary consuming operation refuses that occurrence at the endpoint. -/
theorem historical_read_does_not_license_live_take :
    (0 : migration.Cut) ∈ cutsFor migration
        [⟨0, Bool, anyQuery (inPlace .a)⟩] ∧
      ¬ Enabled label (migration.presentAt 2) (Commit.takeOne 0) := by
  decide +kernel

/-! ## Split origins with a common witness, and the weaker any observer -/

def additions : History Place where
  label := label
  initial := {0}
  word := [Commit.makeOne 1, Commit.makeOne 3]
  executed := .cons (by decide) (.cons (by decide) (.nil _))

private def additionsRows (cut : additions.Cut) : Store Place :=
  if cut.val = 0 then [(0, .a)]
  else if cut.val = 1 then [(0, .a), (1, .b)] else [(0, .a), (1, .b), (3, .a)]

private theorem additions_view : additions.view = additionsRows := by
  funext cut
  change Fin 3 at cut
  fin_cases cut
  · exact view_of_sorted additions 0 [0] (by decide) (by decide) (by decide)
  · exact view_of_sorted additions 1 [0, 1] (by decide) (by decide) (by decide)
  · exact view_of_sorted additions 2 [0, 1, 3] (by decide) (by decide) (by decide)

def countNext (hasA : Bool) : Program (Place → Bool) (Store Place) Nat :=
  .read (if hasA then inPlace .c else inPlace .b) (fun rows => .pure rows.length)

/-- The first read decides which region to read second. Neither path is
substituted for the interpreter's actual reads in the certificate. -/
def branchCount : Program (Place → Bool) (Store Place) Nat :=
  ReadOnlyQuery.bind (anyQuery (inPlace .a)) countNext

def before : Mark Place additions.Cut := ⟨0, Nat, branchCount⟩
def after : Mark Place additions.Cut := noneMark additions .c 1

theorem distinct_marks_replay_after_irrelevant_write :
    before.observe additions.view 1 = before.observe additions.view before.origin ∧
      after.observe additions.view 1 = after.observe additions.view after.origin := by
  have valid : (1 : additions.Cut) ∈ cutsFor additions [before, after] := by
    change Valid (readDependencies (markedReads additions.view [before, after])) (additions.view 1)
    rw [additions_view]
    decide +kernel
  have replay := (additions.cut_replays_iff [before, after] 1).mp valid
  exact ⟨replay before (by simp), replay after (by simp)⟩

/-- The parent read may be captured at 0 and its answer-selected child at
1. At cut 1 these reads are the trace of one actual ordinary bind, and
the intervening write to B was not a dependency of that branch. -/
theorem split_origins_replay_one_bind :
    run (fun q => matchingRows q (additions.view 1)) branchCount =
      ⟨0, [(inPlace .a, [(0, .a)]), (inPlace .c, [])]⟩ := by
  let read (cut : additions.Cut) (q : Place → Bool) := matchingRows q (additions.view cut)
  let parent := run (read 0) (anyQuery (inPlace .a))
  let child := run (read 1) (countNext parent.answer)
  have valid : Valid (readDependencies (parent.reads ++ child.reads)) (additions.view 1) := by
    dsimp only [parent, child, read]
    rw [additions_view]
    decide +kernel
  calc
    _ = ⟨child.answer, parent.reads ++ child.reads⟩ :=
      (cut_replays_bind_iff additions.view 0 1 1 (anyQuery (inPlace .a)) countNext
        (orderedRows_consistent additions.label (additions.presentAt 1))).mp valid
    _ = _ := by
      dsimp only [parent, child, read]
      rw [additions_view]
      rfl

def childInsertion : History Place where
  label := label
  initial := {0}
  word := [Commit.makeOne 2]
  executed := .cons (by decide) (.nil _)

private def childRows (cut : childInsertion.Cut) : Store Place :=
  if cut.val = 0 then [(0, .a)] else [(0, .a), (2, .c)]

private theorem child_view : childInsertion.view = childRows := by
  funext cut
  change Fin 2 at cut
  fin_cases cut
  · exact view_of_sorted childInsertion 0 [0] (by decide) (by decide) (by decide)
  · exact view_of_sorted childInsertion 1 [0, 2] (by decide) (by decide) (by decide)

/-- The first read stays fixed, but a new matching row in the chosen
branch spoils the old trace. An empty branch still recorded a read. -/
theorem late_child_match_refuses_trace :
    matchingRows (inPlace .a) (childInsertion.view 0) =
      matchingRows (inPlace .a) (childInsertion.view 1) ∧
      (1 : childInsertion.Cut) ∉ cutsFor childInsertion [⟨0, Nat, branchCount⟩] := by
  change _ ∧ ¬ Valid
    (readDependencies (markedReads childInsertion.view [⟨0, Nat, branchCount⟩]))
      (childInsertion.view 1)
  rw [child_view]
  decide +kernel

/-- The duplicate A payload is a new occurrence. Exact replay of the any
query would see it. The captured A witness suffices for the Boolean answer,
while the separate complete C query still replays in full. -/
theorem weak_any_with_exact_other_mark :
    after.observe additions.view 2 = after.observe additions.view after.origin ∧
      (run (fun q => matchingRows q (additions.view 2)) (anyQuery (inPlace .a))).answer = true ∧
      (2 : additions.Cut) ∉ cutsFor additions [⟨0, Bool, anyQuery (inPlace .a)⟩] := by
  have saved : anyWitness (inPlace .a) (additions.view 0) = some (0, .a) := by
    rw [additions_view]
    decide +kernel
  have valid : (2 : additions.Cut) ∈ validatingCuts additions.view
      (readDependencies (markedReads additions.view [after]) ++ [.present 0 .a]) := by
    rw [additions_view]
    decide +kernel
  obtain ⟨replay, answer⟩ := cut_replays_with_any [after] (inPlace .a)
    (orderedRows_consistent additions.label (additions.presentAt 2)) saved valid
  refine ⟨replay after (by simp), answer, ?_⟩
  change ¬ Valid
    (readDependencies (markedReads additions.view [⟨0, Bool, anyQuery (inPlace .a)⟩]))
      (additions.view 2)
  rw [additions_view]
  decide +kernel

#print axioms each_pair_has_a_cut
#print axioms no_joint_replay
#print axioms historical_read_does_not_license_live_take
#print axioms distinct_marks_replay_after_irrelevant_write
#print axioms split_origins_replay_one_bind
#print axioms late_child_match_refuses_trace
#print axioms weak_any_with_exact_other_mark

end Mettapedia.GSLT.Contracts.Dependencies.MarkedReadCuts.Controls
