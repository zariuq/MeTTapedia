import Mathlib.Tactic

/-!
# Receipt notices for queued operator messages: pacing and the scan

The control responder tells an operator that a message is queued when the
message has waited a while. Its memory holds, for each remembered task, when
it was first seen, whether its notice was submitted, and its lane; for each
lane, when its last notice went out. Each scan of the service's pending tasks
comes in pages; a scan is complete when its last page ends it.

A notice is due for a task when no turn failure is open, the ledger has not
processed the update, the task's notice was not submitted, the task keeps the
lane it was first seen on, the delay has passed since it was first seen, and
the lane had no notice in the last minute. A failure or a processed update
starts no delay. A complete scan forgets the remembered tasks none of its
pages showed; a lane without a remembered task forgets its last notice.

Invariants proved here:
* a failure or a processed update gives no notice and changes nothing;
* a remembered task whose notice was submitted gets no second notice;
* a lane gets at most one notice a minute;
* a due notice's key is derived from the lane and the task alone, so a restart
  that forgets everything repeats the same key;
* a page that does not end its scan forgets no task;
* a scan keeps every remembered task that one of its pages showed.

The counterexample is forgetting after each page, as if every page ended the
scan: a submitted task that the first page did not show is forgotten, with its
lane's last notice, and is noticed a second time.

This is an abstract contract, not a refinement proof of
`src/input_notice_cetta.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ReceiptNoticePacing

/-- What is remembered of one task. -/
structure Entry where
  since : ℕ
  submitted : Bool
  lane : ℕ

/-- The responder's own memory. `entry` matters for the tasks in `tasks`;
`seen` holds the tasks of the scan in progress, if `scanning`. -/
structure Memory where
  tasks : List ℕ
  entry : ℕ → Entry
  last : ℕ → Option ℕ
  seen : List ℕ
  scanning : Bool

/-- The configured delay, in seconds. -/
def delay : ℕ := 15

/-- The key under which a notice is sent: derived from the names alone. -/
def keyOf (lane task : ℕ) : ℕ × ℕ := (lane, task)

def laneRecent (m : Memory) (now lane : ℕ) : Bool :=
  match m.last lane with
  | none => false
  | some t0 => decide (now < t0 + 60)

def remember (m : Memory) (now task lane : ℕ) : Memory :=
  if task ∈ m.tasks then m
  else { m with tasks := task :: m.tasks, entry := Function.update m.entry task ⟨now, false, lane⟩ }

/-- Whether the notice of a remembered task is due at `now` on `lane`. -/
def due (m : Memory) (now task lane : ℕ) : Bool :=
  !(m.entry task).submitted && (m.entry task).lane == lane &&
    decide ((m.entry task).since + delay ≤ now) && !laneRecent m now lane

/-- One key decision: the key when a notice is due, and the memory after. -/
def key (m : Memory) (now task lane : ℕ) (failure processed : Bool) : Option (ℕ × ℕ) × Memory :=
  if (failure || processed) = true then (none, m)
  else if due (remember m now task lane) now task lane = true then
    (some (keyOf lane task), remember m now task lane)
  else (none, remember m now task lane)

/-- The notice of `task` was handed to the channel service at `now`. -/
def submitted (m : Memory) (now task : ℕ) : Memory :=
  if task ∈ m.tasks then
    { m with entry := Function.update m.entry task { m.entry task with submitted := true },
             last := Function.update m.last (m.entry task).lane (some now) }
  else m

/-- One page of a scan; `complete` when it ends the scan. -/
def beginScan (m : Memory) (page : List ℕ) (complete : Bool) : Memory :=
  let seen := (if m.scanning then m.seen else []) ++ page
  let tasks := if complete then m.tasks.filter (fun t => decide (t ∈ seen)) else m.tasks
  { m with tasks := tasks, seen := seen, scanning := !complete,
           last := fun l => if tasks.any (fun t => (m.entry t).lane == l) then m.last l else none }

theorem remember_keeps_last (m : Memory) (now task lane : ℕ) :
    (remember m now task lane).last = m.last := by
  unfold remember; split_ifs <;> rfl

theorem remember_keeps_known (m : Memory) (now task lane : ℕ) (h : task ∈ m.tasks) :
    remember m now task lane = m := by
  simp [remember, h]

theorem failure_or_processed_changes_nothing (m : Memory) (now task lane : ℕ) (f p : Bool)
    (h : f = true ∨ p = true) : key m now task lane f p = (none, m) := by
  rcases h with h | h <;> simp [key, h]

theorem submitted_task_is_silent (m : Memory) (now task lane : ℕ) (f p : Bool)
    (hm : task ∈ m.tasks) (hs : (m.entry task).submitted = true) :
    (key m now task lane f p).1 = none := by
  have hd : due (remember m now task lane) now task lane = false := by
    simp [due, remember_keeps_known m now task lane hm, hs]
  unfold key; split_ifs <;> simp_all

theorem one_notice_a_minute (m : Memory) (now t0 task lane : ℕ) (f p : Bool)
    (hl : m.last lane = some t0) (hn : now < t0 + 60) :
    (key m now task lane f p).1 = none := by
  have hd : due (remember m now task lane) now task lane = false := by
    simp [due, laneRecent, remember_keeps_last, hl, hn]
  unfold key; split_ifs <;> simp_all

theorem due_key_is_derived (m : Memory) (now task lane : ℕ) (f p : Bool) (k : ℕ × ℕ)
    (h : (key m now task lane f p).1 = some k) : k = keyOf lane task := by
  unfold key at h; split_ifs at h; simp_all

theorem unfinished_page_forgets_no_task (m : Memory) (page : List ℕ) :
    (beginScan m page false).tasks = m.tasks ∧ (beginScan m page false).entry = m.entry := by
  simp [beginScan]

theorem scan_keeps_what_it_showed (m : Memory) (page : List ℕ) (c : Bool) (t : ℕ)
    (ht : t ∈ m.tasks) (hs : t ∈ page ∨ (m.scanning = true ∧ t ∈ m.seen)) :
    t ∈ (beginScan m page c).tasks ∧ (beginScan m page c).entry t = m.entry t := by
  refine ⟨?_, rfl⟩
  cases c
  · simpa [beginScan] using ht
  · rcases hs with hp | ⟨hsc, hseen⟩
    · simp [beginScan, ht, hp]
    · simp [beginScan, ht, hsc, hseen]

/-- A submitted task that a scan showed stays silent after the scan. -/
theorem submitted_task_stays_silent_across_a_scan (m : Memory) (page : List ℕ) (c : Bool)
    (now task lane : ℕ) (f p : Bool) (ht : task ∈ m.tasks) (hs : (m.entry task).submitted = true)
    (hshown : task ∈ page ∨ (m.scanning = true ∧ task ∈ m.seen)) :
    (key (beginScan m page c) now task lane f p).1 = none := by
  obtain ⟨hk, he⟩ := scan_keeps_what_it_showed m page c task ht hshown
  exact submitted_task_is_silent _ now task lane f p hk (by rw [he]; exact hs)

/-! ## Counterexample: forgetting after each page -/

/-- Treats every page as the end of its scan. -/
def eagerScan (m : Memory) (page : List ℕ) (_complete : Bool) : Memory := beginScan m page true

def empty : Memory := ⟨[], fun _ => ⟨0, false, 0⟩, fun _ => none, [], false⟩

/-- Task 7 on lane 1, first seen at 0, is noticed at 15 and submitted. -/
def noticed : Memory := submitted (key (key empty 0 7 1 false false).2 15 7 1 false false).2 15 7

theorem noticed_at_fifteen : (key (key empty 0 7 1 false false).2 15 7 1 false false).1 = some (keyOf 1 7) := by
  decide +kernel

/-- Then one scan of two pages: the first shows task 8, the second task 7. -/
def scanned : Memory := beginScan (beginScan noticed [8] false) [7] true
def eagerScanned : Memory := eagerScan (eagerScan noticed [8] false) [7] true

theorem the_scan_keeps_the_notice_silent :
    (key scanned 75 7 1 false false).1 = none ∧
      (key (key scanned 75 7 1 false false).2 90 7 1 false false).1 = none := by
  decide +kernel

theorem forgetting_each_page_notices_twice :
    (key (key eagerScanned 75 7 1 false false).2 90 7 1 false false).1 = some (keyOf 1 7) := by
  decide +kernel

end Mettapedia.Protocols.Agents.ReceiptNoticePacing
