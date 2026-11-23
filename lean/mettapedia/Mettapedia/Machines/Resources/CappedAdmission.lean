/-!
# Admission of concurrent jobs under a memory budget

Units are memory units and seconds, all natural numbers. A job grows its
memory at `rate` while it runs, until its time limit `limit` stops it: a
computation that keeps allocating, for instance a search running past its
intended fuel. `cap` is a memory limit enforced on that job alone, as a
cgroup limit is: the job is stopped when it reaches the cap.

A time limit does not bound memory, and neither does admitting jobs by slot
count, as a pool of `k` parallel workers does (`count_admission_breaks`).
A job admitted only while the caps of the running jobs, its own included, fit
a budget `B` keeps the running jobs within `B` after any sequence of
admissions, completions and elapsed time, for jobs of any rates
(`capped_admission_never_exceeds`). A job whose cap fits the budget is
admitted once nothing else runs (`capped_admission_progress`).

The safety result needs no knowledge of the jobs' growth: the bound comes
from the caps, which the admission rule controls.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Resources.CappedAdmission

structure Job where
  rate : Nat
  limit : Nat
  cap : Nat

/-- Memory of a job `t` seconds after its start, without a cap. -/
def uncapped (j : Job) (t : Nat) : Nat := j.rate * min t j.limit

/-- Memory of a job under its enforced cap. -/
def capped (j : Job) (t : Nat) : Nat := min (uncapped j t) j.cap

/-- The running jobs, each with the seconds since it started. -/
abbrev Running := List (Job × Nat)

def total (use : Job → Nat → Nat) : Running → Nat
  | [] => 0
  | (j, t) :: rest => use j t + total use rest

def capSum : Running → Nat
  | [] => 0
  | (j, _) :: rest => j.cap + capSum rest

def removeAt : Running → Nat → Running
  | [], _ => []
  | _ :: rest, 0 => rest
  | p :: rest, n + 1 => p :: removeAt rest n

def tick : Running → Running
  | [] => []
  | (j, t) :: rest => (j, t + 1) :: tick rest

inductive Event where
  /-- A job asks to start; a refused job waits and asks again later. -/
  | admit (j : Job)
  /-- The `i`-th running job ends: completion, timeout or cap. -/
  | finish (i : Nat)
  /-- One second passes. -/
  | elapse

/-! ## Without caps -/

/-- Admission by slot count: admit while fewer than `k` jobs run. -/
def stepCount (k : Nat) (rs : Running) : Event → Running
  | .admit j => if rs.length < k then (j, 0) :: rs else rs
  | .finish i => removeAt rs i
  | .elapse => tick rs

def runCount (k : Nat) (rs : Running) : List Event → Running
  | [] => rs
  | e :: es => runCount k (stepCount k rs e) es

/-- A time limit bounds no memory: for every capacity and every positive
limit, some job exceeds the capacity before its limit stops it. -/
theorem timeout_does_not_bound_memory (C limit : Nat) (h : 0 < limit) :
    ∃ j : Job, j.limit = limit ∧ C < uncapped j limit := by
  refine ⟨⟨C + 1, limit, 0⟩, rfl, ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, limit = l + 1 := ⟨limit - 1, by omega⟩
  show C < (C + 1) * min (l + 1) (l + 1)
  rw [Nat.min_self, Nat.mul_succ]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self C) (Nat.le_add_left (C + 1) _)

/-- An example: one job growing 1000 units per second under a 300 s limit
needs 300000 units, more than five times a 59000-unit machine. -/
theorem example_fast_job : 59000 < uncapped ⟨1000, 300, 0⟩ 300 := by decide

theorem runCount_elapse (k : Nat) (j : Job) (t n : Nat) :
    runCount k [(j, t)] (List.replicate n .elapse) = [(j, t + n)] := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    show runCount k (tick [(j, t)]) (List.replicate n .elapse) = [(j, t + (n + 1))]
    rw [show tick [(j, t)] = [(j, t + 1)] from rfl, ih, Nat.add_assoc, Nat.add_comm 1 n]

/-- Count admission breaks: for every slot count `k` and every capacity,
some schedule makes the running jobs exceed the capacity. -/
theorem count_admission_breaks (k C limit : Nat) (hk : 0 < k) (hl : 0 < limit) :
    ∃ es : List Event, C < total uncapped (runCount k [] es) := by
  obtain ⟨j, hj, hC⟩ := timeout_does_not_bound_memory C limit hl
  refine ⟨.admit j :: List.replicate limit .elapse, ?_⟩
  have h0 : stepCount k [] (.admit j) = [(j, 0)] := by
    simp [stepCount, hk]
  show C < total uncapped (runCount k (stepCount k [] (.admit j)) _)
  rw [h0, runCount_elapse, Nat.zero_add]
  show C < uncapped j limit + 0
  omega

/-! ## Per-job caps and admission by a budget of caps -/

def step (B : Nat) (rs : Running) : Event → Running
  | .admit j => if capSum rs + j.cap ≤ B then (j, 0) :: rs else rs
  | .finish i => removeAt rs i
  | .elapse => tick rs

def run (B : Nat) (rs : Running) : List Event → Running
  | [] => rs
  | e :: es => run B (step B rs e) es

theorem capped_le_cap (j : Job) (t : Nat) : capped j t ≤ j.cap :=
  Nat.min_le_right _ _

/-- Under enforced caps the running jobs hold at most the sum of their caps,
whatever their rates. -/
theorem total_capped_le_capSum : ∀ rs : Running, total capped rs ≤ capSum rs
  | [] => Nat.le_refl 0
  | (j, t) :: rest =>
    Nat.add_le_add (capped_le_cap j t) (total_capped_le_capSum rest)

theorem capSum_tick : ∀ rs : Running, capSum (tick rs) = capSum rs
  | [] => rfl
  | (j, _) :: rest => by
    show j.cap + capSum (tick rest) = j.cap + capSum rest
    rw [capSum_tick rest]

theorem capSum_removeAt_le : ∀ (rs : Running) (i : Nat), capSum (removeAt rs i) ≤ capSum rs
  | [], _ => Nat.le_refl 0
  | (_, _) :: _, 0 => Nat.le_add_left _ _
  | (j, _) :: rest, n + 1 =>
    Nat.add_le_add_left (capSum_removeAt_le rest n) j.cap

/-- Each event keeps the caps of the running jobs within the budget. -/
theorem step_within (B : Nat) (rs : Running) (e : Event) (h : capSum rs ≤ B) :
    capSum (step B rs e) ≤ B := by
  cases e with
  | admit j =>
    show capSum (if capSum rs + j.cap ≤ B then (j, 0) :: rs else rs) ≤ B
    split
    · rename_i hfit
      show j.cap + capSum rs ≤ B
      omega
    · exact h
  | finish i => exact Nat.le_trans (capSum_removeAt_le rs i) h
  | elapse => show capSum (tick rs) ≤ B; rw [capSum_tick]; exact h

theorem run_within (B : Nat) :
    ∀ (rs : Running) (es : List Event), capSum rs ≤ B → capSum (run B rs es) ≤ B
  | _, [], h => h
  | rs, e :: es, h => run_within B (step B rs e) es (step_within B rs e h)

/-- Capped admission never exceeds its budget: from an empty machine, after
any sequence of admissions, completions and elapsed seconds, the running jobs
hold at most `B`, for jobs of any rates and limits. With `B` at most the
memory free for the jobs, they cannot exhaust the machine. -/
theorem capped_admission_never_exceeds (B : Nat) (es : List Event) :
    total capped (run B [] es) ≤ B :=
  Nat.le_trans (total_capped_le_capSum _) (run_within B [] es (Nat.zero_le B))

/-- And it does not starve a job that fits: once nothing runs, a job whose
cap is within the budget is admitted. -/
theorem capped_admission_progress (B : Nat) (j : Job) (h : j.cap ≤ B) :
    step B [] (.admit j) = [(j, 0)] := by
  simp [step, capSum, h]

end Mettapedia.Machines.Resources.CappedAdmission
