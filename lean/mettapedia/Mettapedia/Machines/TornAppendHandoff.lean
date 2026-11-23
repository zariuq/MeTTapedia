import Std

/-!
# Torn appends in a shared log, and when a writer must wait

Several loops take turns appending records to one append-only log. A loop
writes each record through a durable intent that names the record's offset
and payload; a crash during the write may leave any prefix of the payload in
the log. A later writer that finds a torn payload completes it in place from
the intent before it writes its own record.

The model takes the log as a list of symbols and an intent as an offset and a
payload. For each restriction such a handoff can impose it asks whether the
restriction is necessary: whether dropping it alone breaks a stated property
on a concrete case. A restriction without such a case only stalls the loops.

* Completing a torn payload before writing is necessary. A write after it
  leaves the payload's place holding other bytes, and no later write repairs
  it (`append_after_torn_loses`, `lost_stays_lost`); its written prefix stays
  in the log as a fragment.
* Waiting while an intent cannot be read is necessary for a byte log. A
  writer that cannot read the intent sees only the log, and whatever it would
  append, a recoverable torn payload consistent with that log is lost by the
  write (`unread_intent_forces_wait`).
* Waiting on an append that can never complete is not necessary once every
  new record starts on a line of its own. Its place holds other bytes, which
  no write changes (`lost_stays_lost`, `place_bytes_fixed`), so waiting for
  it waits for nothing; the same holds for a payload that cannot be known
  (one that fails its digest). What a write after it can still harm is the
  readability of the new record, when the log ends inside the abandoned
  fragment and readers find records at line starts: the write must begin
  with a line break there (`on_own_line_starts_line`, `on_own_line_keeps`,
  `no_break_joins_fragment`).
* With whole-record commits no torn state exists. An owner recovers by
  membership, appending its record once when the log lacks it, and no writer
  reads another's intent (`recover_mem`, `recover_count`, `commit_keeps`).
  This removes the one necessary wait above.

Durability is outside the model: an append here is in the log once made.
The instance is an agent runtime's shared history, written in turn by its
loops: `Whole`, `Torn` and `Lost` are the states of
`history-pending:bytes-state` (`AppendCompleteV1`, `AppendTornV1`,
`AppendForeignV1`); `complete` is its completion branch; the writers' refusal
on a record that cannot be read is `unread_intent_forces_wait`.
-/

namespace Mettapedia.Machines.TornAppendHandoff

open List

section ByteLog

variable {α : Type}

/-- The payload stands whole at its offset. -/
def Whole (log : List α) (o : Nat) (p : List α) : Prop :=
  o ≤ log.length ∧ p <+: log.drop o

/-- The bytes from the offset are a proper prefix of the payload: a crash cut
the append short, and the rest can still be written in place. -/
def Torn (log : List α) (o : Nat) (p : List α) : Prop :=
  o ≤ log.length ∧ log.drop o <+: p ∧ log.drop o ≠ p

/-- Other bytes stand at the payload's place. -/
def Lost (log : List α) (o : Nat) (p : List α) : Prop :=
  o ≤ log.length ∧ ¬ log.drop o <+: p ∧ ¬ p <+: log.drop o

/-- Completing a torn payload in place: the rest of it, appended. -/
def complete (log : List α) (o : Nat) (p : List α) : List α :=
  log ++ p.drop (log.length - o)

theorem prefix_head? {a b : List α} (h : a <+: b) (ha : a ≠ []) : a.head? = b.head? := by
  obtain ⟨u, rfl⟩ := h
  cases a with
  | nil => exact absurd rfl ha
  | cons x xs => rfl

/-- Completion writes exactly the rest: the payload then stands whole. -/
theorem torn_complete_whole {log p : List α} {o : Nat} (h : Torn log o p) :
    Whole (complete log o p) o p := by
  obtain ⟨ho, ⟨u, hu⟩, -⟩ := h
  have hlen : (log.drop o).length = log.length - o := List.length_drop
  have hrest : p.drop (log.length - o) = u := by
    rw [← hlen, ← hu, List.drop_left]
  refine ⟨?_, ?_⟩
  · simp only [complete, List.length_append]; omega
  · simp only [complete]
    rw [List.drop_append_of_le_length ho, hrest, hu]
    exact List.prefix_refl p

/-- A whole payload stays whole whatever is appended after it. -/
theorem whole_stays_whole {log p : List α} {o : Nat} (s : List α) (h : Whole log o p) :
    Whole (log ++ s) o p := by
  obtain ⟨ho, hp⟩ := h
  refine ⟨by simp only [List.length_append]; omega, ?_⟩
  rw [List.drop_append_of_le_length ho]
  exact hp.trans (List.prefix_append _ _)

/-- Other bytes at a payload's place stay there: no append makes it whole or
torn again. Waiting for such an append waits for nothing. -/
theorem lost_stays_lost {log p : List α} {o : Nat} (s : List α) (h : Lost log o p) :
    Lost (log ++ s) o p := by
  obtain ⟨ho, hnt, hnw⟩ := h
  refine ⟨by simp only [List.length_append]; omega, ?_, ?_⟩
  · rw [List.drop_append_of_le_length ho]
    intro h'
    exact hnt ((List.prefix_append _ _).trans h')
  · rw [List.drop_append_of_le_length ho]
    intro h'
    rcases List.prefix_or_prefix_of_prefix h' (List.prefix_append (log.drop o) s) with h'' | h''
    · exact hnw h''
    · exact hnt h''

/-- The bytes at a place never change: what a reader would read there now is
what it would read there after any appends. -/
theorem place_bytes_fixed {log : List α} {o : Nat} (s : List α) (ho : o ≤ log.length) :
    ((log ++ s).drop o).take (log.drop o).length = log.drop o := by
  rw [List.drop_append_of_le_length ho, List.take_left]

/-- Writing after a torn payload, with a record whose first symbol is not the
payload's next one, leaves other bytes at its place: it is lost in place. -/
theorem append_after_torn_loses {log p q : List α} {o : Nat} (h : Torn log o p)
    (hq : q ≠ []) (hdiff : q.head? ≠ (p.drop (log.drop o).length).head?) :
    Lost (log ++ q) o p := by
  obtain ⟨ho, ⟨r, hr⟩, hne⟩ := h
  have hrr : p.drop (log.drop o).length = r := by rw [← hr, List.drop_left]
  have hr0 : r ≠ [] := by
    intro h0
    apply hne
    rw [← hr, h0, List.append_nil]
  rw [hrr] at hdiff
  refine ⟨by simp only [List.length_append]; omega, ?_, ?_⟩
  · rw [List.drop_append_of_le_length ho, ← hr]
    intro h'
    rw [List.prefix_append_right_inj] at h'
    exact hdiff (prefix_head? h' hq)
  · rw [List.drop_append_of_le_length ho, ← hr]
    intro h'
    rw [List.prefix_append_right_inj] at h'
    exact hdiff (prefix_head? h' hr0).symm

/-- Necessity of the wait on an intent that cannot be read. A writer that
cannot read the intent sees only the log. For whatever record it would
append, an intent consistent with that log (written, its payload not yet
begun, starting with another symbol) is torn now and lost by the write.
So a writer that never loses a recoverable payload must wait while an
intent cannot be read. -/
theorem unread_intent_forces_wait (log q : List α) (y : α) (hq : q ≠ [])
    (hy : q.head? ≠ some y) :
    Torn log log.length [y] ∧ Lost (log ++ q) log.length [y] := by
  have ht : Torn log log.length [y] := by
    refine ⟨Nat.le_refl _, ?_, ?_⟩
    · rw [List.drop_length]; exact List.nil_prefix
    · rw [List.drop_length]; exact (List.cons_ne_nil y []).symm
  refine ⟨ht, append_after_torn_loses ht hq ?_⟩
  rw [List.drop_length]
  simpa using hy

/-- A concrete case: a payload torn after one symbol, then another record. -/
example : Torn [0, 1] 1 [1, 2] ∧ Lost ([0, 1] ++ [3]) 1 [1, 2] := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

/-- A new record on a line of its own: after a log that ends inside a line,
a line break first. -/
def onOwnLine [DecidableEq α] (nl : α) (log q : List α) : List α :=
  if log.getLast? = some nl ∨ log = [] then log ++ q else log ++ nl :: q

/-- The log before the new record is kept byte for byte, fragment included. -/
theorem on_own_line_keeps [DecidableEq α] (nl : α) (log q : List α) :
    log <+: onOwnLine nl log q := by
  unfold onOwnLine
  split
  · exact List.prefix_append _ _
  · exact List.prefix_append _ _

/-- The new record starts a line: what precedes it is empty or ends with the
line break. -/
theorem on_own_line_starts_line [DecidableEq α] (nl : α) (log q : List α) :
    ∃ pre, onOwnLine nl log q = pre ++ q ∧ (pre = [] ∨ pre.getLast? = some nl) := by
  unfold onOwnLine
  split
  · rename_i h
    exact ⟨log, rfl, h.elim Or.inr Or.inl⟩
  · exact ⟨log ++ [nl], by simp, Or.inr (by simp)⟩

/-- Without the break, a record written after a fragment that ends inside a
line does not start a line: readers that find records at line starts read it
joined to the fragment. -/
theorem no_break_joins_fragment (nl : α) (log q : List α) (hne : log ≠ [])
    (hmid : log.getLast? ≠ some nl) :
    ¬ ∃ pre, log ++ q = pre ++ q ∧ (pre = [] ∨ pre.getLast? = some nl) := by
  rintro ⟨pre, heq, hpre⟩
  have : pre = log := (List.append_cancel_right heq).symm
  subst this
  rcases hpre with h | h
  · exact hne h
  · exact hmid h

end ByteLog

section WholeRecords

variable {β : Type} [DecidableEq β]

/-- With whole-record commits a crash leaves a record wholly in the log or
wholly out of it. An owner recovers by membership. -/
def recover (log : List β) (r : β) : List β :=
  if r ∈ log then log else log ++ [r]

theorem recover_mem (log : List β) (r : β) : r ∈ recover log r := by
  unfold recover
  split
  · assumption
  · exact List.mem_append_right _ (List.mem_singleton_self r)

/-- Recovery writes a record at most once. -/
theorem recover_count (log : List β) (r : β) (h : log.count r ≤ 1) :
    (recover log r).count r = 1 := by
  unfold recover
  split
  · have := List.count_pos_iff.mpr ‹r ∈ log›
    omega
  · rw [List.count_append, List.count_eq_zero_of_not_mem ‹r ∉ log›]
    simp

omit [DecidableEq β] in
/-- Another loop's commit never removes a record: no loop needs to read
another's intent before it writes. -/
theorem commit_keeps {log : List β} {r : β} (s : List β) (h : r ∈ log) : r ∈ log ++ s :=
  List.mem_append_left s h

end WholeRecords

end Mettapedia.Machines.TornAppendHandoff
