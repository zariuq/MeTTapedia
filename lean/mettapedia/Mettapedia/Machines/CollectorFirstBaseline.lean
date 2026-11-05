import Mathlib.Tactic

/-!
# A two-generation collector's first baseline

A generational collector schedules a major collection when the old
generation grows past a threshold, and sets the threshold from the live size
a full trace measured: `next live = live + max live window`.  Before any
major collection the threshold is a guess, the window.  The first minor
collection that runs while the old generation is empty traces the whole
managed heap, so its promotion is a measured live size; the collector then
sets its baseline from it, as a major collection would.

The rule as written keys on the old generation being exactly empty.  A few
bytes written into the old generation directly before that collection (a
stable export) keep the guessed threshold: a first promotion above the
window then makes a major collection due at once, which copies the whole
promotion again to reclaim at most those few bytes.  Counting old bytes
below a floor as empty keeps the baseline, and a major collection is then
due only once the old generation has grown past what the trace measured.

This file proves:
* `exact_empty_baseline`: with an empty old generation, the first minor
  collection sets the baseline and no major collection is due after it;
* `one_byte_flips`: one old byte keeps the guess, and a promotion above the
  window makes a major collection due at once;
* `wasted_major`: that major collection copies at least the whole promotion
  again and reclaims at most the `old` bytes;
* `floor_rule_no_immediate_major`: with old bytes below the floor counted as
  empty, no major collection is due after the first minor collection.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CollectorFirstBaseline

/-- The threshold set from a measured live size. -/
def next (window live : Nat) : Nat := live + max live window

/-- The threshold after the first minor collection, which found `old`
bytes already in the old generation and promoted `promoted`: the rule as
written sets the baseline only when the old generation was empty. -/
def thresholdExact (window old promoted : Nat) : Nat :=
  if old = 0 then next window (old + promoted) else window

/-- The same with old bytes below `floor` counted as empty. -/
def thresholdFloor (window floor old promoted : Nat) : Nat :=
  if old < floor then next window (old + promoted) else window

/-- A major collection is due when the old generation reaches its
threshold. -/
def majorDue (threshold live : Nat) : Prop := threshold ≤ live

theorem next_gt (window live : Nat) (h : 0 < window) : live < next window live := by
  unfold next
  have : 0 < max live window := lt_of_lt_of_le h (le_max_right _ _)
  omega

theorem exact_empty_baseline (window promoted : Nat) (h : 0 < window) :
    ¬ majorDue (thresholdExact window 0 promoted) (0 + promoted) := by
  unfold majorDue thresholdExact
  simp only [if_true]
  have := next_gt window (0 + promoted) h
  omega

theorem one_byte_flips (window promoted : Nat) (h : window < promoted) :
    majorDue (thresholdExact window 1 promoted) (1 + promoted) := by
  unfold majorDue thresholdExact
  simp only [one_ne_zero, if_false]
  omega

/-- The immediate major collection copies what is live in the old
generation and reclaims the rest.  The promotion was live when the minor
collection traced it, so the major collection copies at least the whole
promotion again and reclaims at most the `old` bytes no trace has seen. -/
theorem wasted_major (old promoted live : Nat)
    (traced : promoted ≤ live) (within : live ≤ old + promoted) :
    promoted ≤ live ∧ old + promoted - live ≤ old := by
  omega

theorem floor_rule_no_immediate_major (window floor old promoted : Nat)
    (hw : 0 < window) (hold : old < floor) :
    ¬ majorDue (thresholdFloor window floor old promoted) (old + promoted) := by
  unfold majorDue thresholdFloor
  simp only [hold, if_true]
  have := next_gt window (old + promoted) hw
  omega

end Mettapedia.Machines.CollectorFirstBaseline
