import Mathlib.Tactic

/-!
# Telegram journal retention: which received records go

The channel journal keeps the received updates in the order they were
recorded. A retention pass removes all but the newest `keep` of them, and,
while an update still waits for processing in the inbox, only those before the
oldest waiting one. The records it removes are written to an archive first.

Invariants proved here:
* a removed record is never one of the newest `keep`;
* a removed record's update is before every update still waiting;
* removing the selected records leaves the newest `keep` in place;
* with nothing waiting and more than `keep` records, the pass removes exactly
  the oldest ones.

The counterexample is the selection without the inbox bound: it removes the
record of an update that is still waiting.

This is an abstract contract, not a refinement proof of
`scripts/telegram_journal_retention.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.JournalRetention

/-- Received records, oldest first, each named by its update number. -/
abbrev Journal := List ℕ

/-- The oldest update still waiting, if any. -/
def firstWaiting (waiting : List ℕ) : Option ℕ := waiting.min?

/-- The records a pass removes. -/
def selected (journal : Journal) (keep : ℕ) (waiting : List ℕ) : List ℕ :=
  let old := journal.take (journal.length - keep)
  match firstWaiting waiting with
  | none => old
  | some first => old.filter (fun n => decide (n < first))

/-- The selection without the inbox bound. -/
def selectedUnbounded (journal : Journal) (keep : ℕ) : List ℕ :=
  journal.take (journal.length - keep)

theorem selected_sub_old (journal : Journal) (keep : ℕ) (waiting : List ℕ) :
    selected journal keep waiting ⊆ journal.take (journal.length - keep) := by
  unfold selected
  cases firstWaiting waiting with
  | none => exact fun _ h => h
  | some first => exact fun _ h => (List.mem_filter.mp h).1

/-- The newest `keep` records are the journal's last `keep`, and none of them
is selected when the update numbers are distinct. -/
theorem newest_kept (journal : Journal) (keep : ℕ) (waiting : List ℕ) (hd : journal.Nodup)
    (n : ℕ) (hn : n ∈ journal.drop (journal.length - keep)) :
    n ∉ selected journal keep waiting := by
  intro hs
  have hold := selected_sub_old journal keep waiting hs
  have hsplit : journal = journal.take (journal.length - keep) ++ journal.drop (journal.length - keep) :=
    (List.take_append_drop _ _).symm
  have hd' : (journal.take (journal.length - keep) ++ journal.drop (journal.length - keep)).Nodup := by
    rw [← hsplit]; exact hd
  exact (List.disjoint_of_nodup_append hd') hold hn

theorem selected_before_waiting (journal : Journal) (keep : ℕ) (waiting : List ℕ)
    (n : ℕ) (hn : n ∈ selected journal keep waiting) (w : ℕ) (hw : w ∈ waiting) : n < w := by
  unfold selected at hn
  cases hmin : firstWaiting waiting with
  | none =>
    have : waiting.min? = none := hmin
    simp [List.min?_eq_none_iff] at this
    simp [this] at hw
  | some first =>
    rw [hmin] at hn
    have hlt := of_decide_eq_true (List.mem_filter.mp hn).2
    have hle : first ≤ w := (List.min?_eq_some_iff.mp hmin).2 w hw
    omega

theorem nothing_waiting_takes_the_oldest (journal : Journal) (keep : ℕ) :
    selected journal keep [] = journal.take (journal.length - keep) := by
  simp [selected, firstWaiting]

/-- Without the bound, a waiting update's record is removed. -/
theorem unbounded_removes_a_waiting_update :
    ∃ (journal : Journal) (keep w : ℕ), w ∈ selectedUnbounded journal keep ∧ w ∈ [w] := by
  exact ⟨[1, 2, 3], 1, 2, by decide, by simp⟩

end Mettapedia.Protocols.Agents.JournalRetention
