import Mettapedia.GSLT.Contracts.OccurrenceReadWindows
import Mettapedia.GSLT.Contracts.MarkedReadCutsControls

/-!
# Separating controls for local read windows

The occurrence examples read actual prefixes of executable commits. The
reused-stamp control deliberately violates the epoch discipline.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Dependencies.OccurrenceReadWindows.Controls

open MarkedReadCuts (History Mark markedReads orderedRows validatingCuts)
open MarkedReadCuts.Controls (Place label inPlace additions move)
open Mettapedia.GSLT.Contracts.ReadWindowCuts
open Mettapedia.Machines.ReadOnlyQuery (Agrees Observation Program run)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (regionOf)

private def footprint (q : Place → Bool) : Set Place := {place | q place = true}

private theorem covers_places : Covers inPlace footprint := by
  intro q atom emits
  exact ⟨atom, emits, by simp [inPlace]⟩

private theorem checks_place (h : History Place) (place : Place)
    {start finish : h.Cut} (same : epoch h (inPlace place) start = epoch h (inPlace place) finish) :
    Set.EqOn (epochs h inPlace start) (epochs h inPlace finish) (footprint (inPlace place)) := by
  intro other member
  have equal : other = place := of_decide_eq_true member
  subst other
  exact same

private def aWindow : Window additions.Cut := ⟨0, 0, 1, by decide, by decide⟩
private def bWindow : Window additions.Cut := ⟨1, 2, 2, by decide, by decide⟩

private def mixedReads : List ((Place → Bool) × Window additions.Cut) :=
  [(inPlace .a, aWindow), (inPlace .b, bWindow)]

private theorem mixed_checks : ∀ entry ∈ mixedReads, Set.EqOn
    (epochs additions inPlace entry.2.start) (epochs additions inPlace entry.2.finish)
    (footprint entry.1) := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | last
  · exact checks_place additions .a (by decide +kernel)
  · have equal := List.mem_singleton.mp last
    subst entry
    exact checks_place additions .b (by decide +kernel)

private theorem mixed_cross : Window.CrossOrdered (mixedReads.map Prod.snd) := by
  apply (Window.exists_joint_iff _).mp
  use 1
  intro w member
  simp only [mixedReads, List.map_cons, List.map_nil] at member
  rcases List.mem_cons.mp member with rfl | last
  · exact ⟨by decide, by decide⟩
  · have equal := List.mem_singleton.mp last
    subst w
    exact ⟨by decide, by decide⟩

private theorem mixed_joint : Window.jointStart (mixedReads.map Prod.snd) = (1 : additions.Cut) := by
  decide +kernel

private theorem observe_of_sorted (h : History Place) (cut : h.Cut) (q : Place → Bool)
    (ids : List Nat) (inventory : ids.toFinset = regionOf h.label (h.presentAt cut) q)
    (distinct : ids.Nodup) (ordered : ids.Pairwise (· ≤ ·)) :
    observe h cut q = ids.map fun identity => (identity, h.label identity) := by
  rw [observe_eq_ordered_region, ← inventory, orderedRows,
    (List.toFinset_sort (· ≤ ·) distinct).mpr ordered]

private theorem bAt0 : observe additions 0 (inPlace .b) = [] :=
  observe_of_sorted additions 0 (inPlace .b) [] (by decide +kernel) (by decide) (by decide)

private theorem bAt1 : observe additions 1 (inPlace .b) = [(1, .b)] :=
  observe_of_sorted additions 1 (inPlace .b) [1] (by decide +kernel) (by decide) (by decide)

private theorem bAt2 : observe additions 2 (inPlace .b) = [(1, .b)] :=
  observe_of_sorted additions 2 (inPlace .b) [1] (by decide +kernel) (by decide) (by decide)

private theorem aAt2 : observe additions 2 (inPlace .a) = [(0, .a), (3, .a)] :=
  observe_of_sorted additions 2 (inPlace .a) [0, 3] (by decide +kernel) (by decide) (by decide)

private def adaptive : Program (Place → Bool) (Store Place) (Nat × Nat) :=
  .read (inPlace .a) fun first =>
    .read (if first.isEmpty then inPlace .c else inPlace .b)
      fun second => .pure (first.length, second.length)

private theorem actual_capture : Captured (observe additions) adaptive mixedReads (1, 1) := by
  unfold adaptive mixedReads
  refine .read (inPlace .a) _ aWindow ?_
  have notEmpty : (observe additions aWindow.sample (inPlace .a)).isEmpty = false := by
    decide +kernel
  have aCount : (observe additions aWindow.sample (inPlace .a)).length = 1 := by
    decide +kernel
  simp only [notEmpty, Bool.false_eq_true, if_false, aCount]
  refine .read (inPlace .b) _ bWindow ?_
  have bCount : (observe additions bWindow.sample (inPlace .b)).length = 1 := by
    change (observe additions 2 (inPlace .b)).length = 1
    simp [bAt2]
  rw [bCount]
  exact .pure (1, 1)

/-- Read A before the B insertion and B after a later A insertion.
Neither read needs full-store stability, and their exact values replay at
the middle cut. The first read genuinely selects the second. -/
theorem staggered_adaptive_reads_replay :
    run (observe additions 1) adaptive =
      (⟨(1, 1), recordedReads (observe additions) mixedReads⟩ :
        Observation (Place → Bool) (Store Place) (Nat × Nat)) := by
  have replay := actual_capture.replay_at_jointStart
    (occurrence_discipline additions inPlace footprint covers_places) mixed_checks mixed_cross
  rw [mixed_joint] at replay
  exact replay

private def fixedMarks : List (Mark Place additions.Cut) :=
  [⟨0, Nat, .read (inPlace .a) fun rows => .pure rows.length⟩,
   ⟨2, Nat, .read (inPlace .b) fun rows => .pure rows.length⟩]

theorem local_epochs_validate_existing_marks :
    (1 : additions.Cut) ∈
      validatingCuts additions.view (readDependencies (markedReads additions.view fixedMarks)) ∧
    ∀ mark ∈ fixedMarks,
      mark.observe additions.view 1 = mark.observe additions.view mark.origin := by
  simpa only [mixed_joint] using marked_replay_at_jointStart additions inPlace footprint
    covers_places fixedMarks mixedReads rfl mixed_checks mixed_cross

theorem unrelated_write_preserves_narrow_epoch :
    epoch additions (inPlace .a) 0 = epoch additions (inPlace .a) 1 ∧
      epoch additions (fun _ => true) 0 ≠ epoch additions (fun _ => true) 1 := by
  decide +kernel

/-- The common historical cut does not validate the answer at the end. -/
theorem historical_result_is_not_live :
    (run (observe additions 2) adaptive).answer ≠ (1, 1) := by
  simp [adaptive, run, aAt2, bAt2]

/-- A stable stamp for the wrong region gives no evidence about a
previously empty query: this insertion is a phantom for the B read. -/
theorem checking_wrong_region_misses_insertion :
    epoch additions (inPlace .a) 0 = epoch additions (inPlace .a) 1 ∧
      observe additions 0 (inPlace .b) ≠ observe additions 1 (inPlace .b) := by
  exact ⟨by decide +kernel, by simp [bAt0, bAt1]⟩

private def transfer : History Place where
  label := label
  initial := {0}
  word := [move 0 1]
  executed := .cons (by decide) (.nil _)

private def point {C : Type} [Preorder C] (cut : C) : Window C :=
  ⟨cut, cut, cut, le_rfl, le_rfl⟩

private def separateReads : List ((Place → Bool) × Window transfer.Cut) :=
  [(inPlace .a, point 0), (inPlace .b, point 1)]

/-- Each local check passes, but the two positive observations cannot
describe one cut of the atomic transfer. -/
theorem separate_local_checks_are_not_joint :
    (∀ entry ∈ separateReads, Set.EqOn
      (epochs transfer inPlace entry.2.start) (epochs transfer inPlace entry.2.finish)
      (footprint entry.1)) ∧
    ¬ ∃ cut, Agrees (observe transfer cut) (recordedReads (observe transfer) separateReads) := by
  constructor
  · intro entry member
    rcases List.mem_cons.mp member with rfl | last
    · exact checks_place transfer .a rfl
    · have equal := List.mem_singleton.mp last
      subst entry
      exact checks_place transfer .b rfl
  · rintro ⟨cut, agrees⟩
    have a := agrees (inPlace .a, observe transfer 0 (inPlace .a))
      (by simp [separateReads, recordedReads, point])
    have b := agrees (inPlace .b, observe transfer 1 (inPlace .b))
      (by simp [separateReads, recordedReads, point])
    change Fin 2 at cut
    fin_cases cut
    · exact (by decide +kernel :
        observe transfer 0 (inPlace .b) ≠ observe transfer 1 (inPlace .b)) b
    · exact (by decide +kernel :
        observe transfer 1 (inPlace .a) ≠ observe transfer 0 (inPlace .a)) a

private def reusedStamp (cut : Cut 2) : Nat := cut.val % 2
private def reusedView (cut : Cut 2) (_ : Unit) : Bool := cut.val == 1

private def reusedReads : List (Unit × Window (Cut 2)) :=
  [((), ⟨0, 0, 2, by decide, by decide⟩), ((), ⟨0, 1, 2, by decide, by decide⟩)]

/-- Even overlapping brackets and equal endpoint stamps are insufficient
when a stamp can be reused. These two reads saw different values of one
coordinate. -/
theorem reused_stamp_does_not_certify_a_cut :
    (∀ entry ∈ reusedReads, reusedStamp entry.2.start = reusedStamp entry.2.finish) ∧
    (∃ cut, ∀ entry ∈ reusedReads, entry.2.Contains cut) ∧
    ¬ ∃ cut, Agrees (reusedView cut) (recordedReads reusedView reusedReads) := by
  constructor
  · intro entry member
    simp [reusedReads] at member
    rcases member with rfl | rfl <;> rfl
  constructor
  · use 1
    intro entry member
    simp [reusedReads] at member
    rcases member with rfl | rfl <;> exact ⟨by decide, by decide⟩
  · rintro ⟨cut, agrees⟩
    have previous := agrees ((), false) (by simp [reusedReads, recordedReads, reusedView])
    have during := agrees ((), true) (by simp [reusedReads, recordedReads, reusedView])
    exact Bool.noConfusion (previous.symm.trans during)

#print axioms staggered_adaptive_reads_replay
#print axioms local_epochs_validate_existing_marks
#print axioms unrelated_write_preserves_narrow_epoch
#print axioms historical_result_is_not_live
#print axioms checking_wrong_region_misses_insertion
#print axioms separate_local_checks_are_not_joint
#print axioms reused_stamp_does_not_certify_a_cut

end Mettapedia.GSLT.Contracts.Dependencies.OccurrenceReadWindows.Controls
