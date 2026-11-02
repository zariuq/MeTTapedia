import Mettapedia.Languages.Erlang.MailboxSelection

/-!
# Computing the first accepted message of an explicitly ordered queue

The worker scans with a reversed saved prefix. Its correctness is proved
against the independently defined Erlang `Mailbox.selectFirst`, including
the residual queue. The selector supplies pure pattern and guard checking;
implementing a source language's selector is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedMailboxComputation

open Mettapedia.Languages.Erlang

variable {α β : Type*}

/-- Tail-recursive first-match search. Rejected messages are saved in reverse
order and restored exactly once when an accepted message is found. -/
def scan (select : α → Option β) (savedRev : List α) : List α → Option (β × List α)
  | [] => none
  | message :: later =>
      match select message with
      | some result => some (result, savedRev.reverse ++ later)
      | none => scan select (message :: savedRev) later

theorem scan_eq_source (select : α → Option β) (savedRev messages : List α) :
    scan select savedRev messages =
      (Mailbox.selectFirst select messages).map
        (fun pair => (pair.1, savedRev.reverse ++ pair.2)) := by
  induction messages generalizing savedRev with
  | nil => rfl
  | cons message later ih =>
      cases choice : select message with
      | none =>
          simp only [scan, Mailbox.selectFirst, choice, ih]
          cases Mailbox.selectFirst select later <;>
            simp [List.reverse_cons, List.append_assoc]
      | some result => simp [scan, Mailbox.selectFirst, choice]

/-- The prepared result retains the selected value and the complete residual
queue, so a skipped prefix is not lost at the publication boundary. -/
def compute (select : α → Option β) (messages : List α) : Option (β × List α) :=
  scan select [] messages

theorem compute_eq_selectFirst (select : α → Option β) (messages : List α) :
    compute select messages = Mailbox.selectFirst select messages := by
  simpa [compute] using scan_eq_source select [] messages

theorem compute_some_iff {select : α → Option β} {messages : List α}
    {result : β} {remaining : List α} :
    compute select messages = some (result, remaining) ↔
      ∃ before message after, messages = before ++ message :: after ∧
        select message = some result ∧
        (∀ prior ∈ before, select prior = none) ∧ remaining = before ++ after := by
  rw [compute_eq_selectFirst, Mailbox.selectFirst_some_iff]

theorem compute_none_iff (select : α → Option β) (messages : List α) :
    compute select messages = none ↔ ∀ message ∈ messages, select message = none := by
  rw [compute_eq_selectFirst, Mailbox.selectFirst_none_iff]

theorem compute_skipped_prefix {select : α → Option β} {before after : List α}
    {message : α} {result : β}
    (skipped : ∀ prior ∈ before, select prior = none)
    (selected : select message = some result) :
    compute select (before ++ message :: after) = some (result, before ++ after) := by
  rw [compute_eq_selectFirst]
  exact Mailbox.selectFirst_of_first skipped selected

theorem compute_retains_duplicate {select : α → Option β} {message : α} {result : β}
    (selected : select message = some result) (after : List α) :
    compute select (message :: message :: after) = some (result, message :: after) := by
  rw [compute_eq_selectFirst]
  exact Mailbox.selectFirst_duplicate selected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedMailboxComputation
