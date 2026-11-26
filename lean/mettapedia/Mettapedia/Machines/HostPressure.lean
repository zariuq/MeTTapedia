/-!
# Host memory pressure: caps, incident alerts, readout injection and alert delivery

A shared workstation runs many agents' jobs. This file models four pieces of the infrastructure that
keeps such a host usable, and proves the property each piece exists for.

**Memory caps.** A per-process limit bounds each process, not the job: `p` processes under a limit
`L` may use `p * L` together. A control-group scope bounds the job's total, and with swap disabled
for the scope the job's memory stays resident and counted. The kernel enforces a scope cap by
denying an allocation or killing inside the scope; from any state within its cap, every sequence of
allocations stays within it, and capped jobs whose caps fit in RAM together never need swap.
Without a scope, granted allocations accumulate without bound.

**Incident alerts.** A sampler reads available memory and 60-second stall averages every
`interval` seconds and receives kernel and userspace OOM kill notices. A reading is a pressure
symptom (severity 1) on a severe stall, on low available memory in two consecutive readings however
far apart they are, or on one low reading after a sampling gap; a kill notice has severity 2. An
alert goes out for the first symptom after a quiet period and whenever the severity rises, so a
pressure incident sends one warning and, if something is killed, one follow-up. An earlier rule
counted low memory only when two low readings were at most 45 seconds apart; a thrashing host
samples late, and that rule stays silent through exactly the storms it exists for.

**Readout injection.** A hook adds the latest reading to an agent's context at the start of each
turn, for each new kill notice, and otherwise at most once a minute. Process names in the reading
are reduced to a fixed alphabet, so the reading cannot carry other text.

**Alert delivery.** A sender whose attempt got no answer cannot tell a lost request from a lost
answer. Against a receiver that appends every message it receives, any sender that still delivers
when its first attempt is lost stores a second copy when only the answer was lost. A receiver that
stores each message id once makes retries safe: retrying with one id then delivers exactly once as
soon as any attempt arrives (`Mettapedia.Protocols.Mail.Submission.retry_once` proves this for the
mail service's ledger). Sending once and never retrying stores at most one copy against either
receiver, and loses the alert when that attempt never arrives.

Operating-system behaviour enters only through the model's inputs: the kernel's cap enforcement is
the transition `allocate`, readings arrive as `Sample`s, and readout times are the caller's clock.

Results:
- `allocate_within`, `run_within`, `capped_jobs_fit_in_ram`: caps hold under every allocation
  sequence, and capped jobs whose caps fit in RAM fit in RAM;
- `per_process_limit_allows`, `sixteen_processes_exceed_ram_and_swap`: a per-process limit permits
  `p * L`;
- `uncapped_exceeds`: without a scope, usage passes every bound;
- `kill_alerts`, `escalation_alerts`, `low_twice_level`, `low_twice_alerts`, `late_low_level`,
  `level_le_one`: when an alert fires;
- `repeat_needs_quiet`, `pressure_after_warning_is_quiet`, `kill_follows_warning`,
  `one_warning_one_follow_up`: one warning per pressure incident and one follow-up for a kill;
- `old_rule_misses_late_samples`, `storm_alerts_once`, `old_rule_silent_in_storm`: the late-sample
  failure of the 45-second rule, and a replay of a real storm's readings;
- `turn_start_injects`, `new_notice_injects`, `once_a_minute`, `minute_later_injects`: readout
  cadence;
- `sanitize_allowed`, `sanitize_length_le`: the alphabet and length of names in the reading;
- `retryFixed_nodup`, `retryFixed_delivers`, `retrying_delivers`: exactly-once delivery with one id
  and a receiver that stores each id once;
- `retry_without_dedup_duplicates`: against an appending receiver, delivering when the first attempt
  is lost forces a duplicate when only its answer is lost;
- `no_retry_at_most_once`, `stopping_loses`, `fresh_ids_duplicate`: sending once never duplicates
  but can lose the alert, and fresh ids per retry duplicate even against a deduplicating receiver.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HostPressure

/-! ## Memory caps -/

/-- One control-group scope: its cap and its current usage, in KiB. Swap is disabled for the scope,
so all of its memory is resident and counted here. -/
structure Scope where
  cap : Nat
  used : Nat
  deriving Repr

/-- The kernel's enforcement of a scope cap. An allocation of `size` KiB is granted when the scope
stays within its cap; otherwise the kernel kills inside the scope, which leaves at most what was in
use (`left` is whatever the kill leaves, clipped to the previous usage). -/
def allocate (s : Scope) (size left : Nat) : Scope :=
  if s.used + size ≤ s.cap then { s with used := s.used + size }
  else { s with used := min left s.used }

theorem allocate_cap (s : Scope) (size left : Nat) : (allocate s size left).cap = s.cap := by
  unfold allocate
  split <;> rfl

theorem allocate_within (s : Scope) (size left : Nat) (h : s.used ≤ s.cap) :
    (allocate s size left).used ≤ s.cap := by
  unfold allocate
  by_cases hfit : s.used + size ≤ s.cap
  · rw [if_pos hfit]
    exact hfit
  · rw [if_neg hfit]
    exact Nat.le_trans (Nat.min_le_right left s.used) h

/-- A sequence of allocation requests, each with the amount a kill would leave. -/
def run (s : Scope) : List (Nat × Nat) → Scope
  | [] => s
  | (size, left) :: rest => run (allocate s size left) rest

theorem run_cap (s : Scope) (steps : List (Nat × Nat)) : (run s steps).cap = s.cap := by
  induction steps generalizing s with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨size, left⟩ := step
    show (run (allocate s size left) rest).cap = s.cap
    rw [ih, allocate_cap]

theorem run_within (s : Scope) (steps : List (Nat × Nat)) (h : s.used ≤ s.cap) :
    (run s steps).used ≤ s.cap := by
  induction steps generalizing s with
  | nil => exact h
  | cons step rest ih =>
    obtain ⟨size, left⟩ := step
    show (run (allocate s size left) rest).used ≤ s.cap
    have h1 : (allocate s size left).used ≤ (allocate s size left).cap := by
      rw [allocate_cap]
      exact allocate_within s size left h
    have h2 := ih (allocate s size left) h1
    rw [allocate_cap] at h2
    exact h2

theorem runs_used_le : ∀ (jobs : List (Scope × List (Nat × Nat))),
    (∀ j ∈ jobs, j.1.used ≤ j.1.cap) →
    (jobs.map (fun j => (run j.1 j.2).used)).sum ≤ (jobs.map (fun j => j.1.cap)).sum
  | [], _ => Nat.le_refl _
  | j :: rest, h => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := run_within j.1 j.2 (h j (by simp))
    have h2 := runs_used_le rest (fun k hk => h k (by simp [hk]))
    omega

/-- Capped jobs whose caps fit in RAM together with a baseline fit in RAM after any allocation
sequences in all the scopes. -/
theorem capped_jobs_fit_in_ram (baseline ram : Nat) (jobs : List (Scope × List (Nat × Nat)))
    (start : ∀ j ∈ jobs, j.1.used ≤ j.1.cap)
    (fits : baseline + (jobs.map (fun j => j.1.cap)).sum ≤ ram) :
    baseline + (jobs.map (fun j => (run j.1 j.2).used)).sum ≤ ram := by
  have := runs_used_le jobs start
  omega

theorem sum_replicate (p L : Nat) : (List.replicate p L).sum = p * L := by
  induction p with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.sum_cons, ih, Nat.add_mul, Nat.one_mul]
    omega

/-- A per-process limit `L` bounds each of `p` processes, and their total `p * L` is attained. -/
theorem per_process_limit_allows (p L : Nat) :
    (∀ x ∈ List.replicate p L, x ≤ L) ∧ (List.replicate p L).sum = p * L := by
  refine ⟨fun x hx => ?_, sum_replicate p L⟩
  rw [List.mem_replicate] at hx
  omega

/-- In GiB: sixteen processes under a 24 GiB per-process limit may use more than a host's 59 GiB of
RAM and 60 GiB of swap together. -/
theorem sixteen_processes_exceed_ram_and_swap : 59 + 60 < 16 * 24 := by decide

/-- Without a scope, `k` granted allocations of `size` add `k * size`. -/
def grow (used size : Nat) : Nat → Nat
  | 0 => used
  | k + 1 => grow used size k + size

theorem grow_eq (used size k : Nat) : grow used size k = used + k * size := by
  induction k with
  | zero => simp [grow]
  | succ k ih =>
    rw [grow, ih, Nat.add_mul, Nat.one_mul]
    omega

/-- Without a scope, usage passes every bound. -/
theorem uncapped_exceeds (used size bound : Nat) (hsize : 0 < size) :
    bound < grow used size (bound + 1) := by
  rw [grow_eq]
  have h : (bound + 1) * 1 ≤ (bound + 1) * size := Nat.mul_le_mul_left (bound + 1) hsize
  rw [Nat.mul_one] at h
  omega

/-! ## Incident alerts -/

/-- Sampling parameters. Memory in KiB, stall averages in tenths of a percent, times in seconds. -/
structure Config where
  interval : Nat
  quiet : Nat
  lowKiB : Nat
  severe : Nat
  deriving Repr

/-- One reading: available memory, the 60-second memory and I/O stall averages, and whether a kill
notice arrived since the previous reading. -/
structure Sample where
  time : Nat
  availableKiB : Nat
  memStall : Nat
  ioStall : Nat
  killed : Bool
  deriving Repr

/-- What the sampler remembers between readings. -/
structure Incident where
  lastSample : Option Nat
  previousLow : Bool
  lastSymptom : Option Nat
  severity : Nat
  deriving Repr

def low (c : Config) (x : Sample) : Bool := decide (x.availableKiB < c.lowKiB)

def severeStall (c : Config) (x : Sample) : Bool :=
  decide (c.severe ≤ x.memStall) || decide (c.severe ≤ x.ioStall)

/-- Seconds since the previous reading (zero for the first). -/
def gap (s : Incident) (x : Sample) : Nat :=
  match s.lastSample with
  | none => 0
  | some t => x.time - t

/-- Severity of a reading: 2 for a kill notice; 1 for a severe stall, for low memory in two
consecutive readings, or for one low reading after a sampling gap of more than three intervals. -/
def level (c : Config) (s : Incident) (x : Sample) : Nat :=
  if x.killed then 2
  else if severeStall c x then 1
  else if low c x && (s.previousLow || decide (3 * c.interval < gap s x)) then 1
  else 0

/-- No symptom for at least `quiet` seconds. -/
def quietSince (c : Config) (s : Incident) (now : Nat) : Bool :=
  match s.lastSymptom with
  | none => true
  | some t => decide (t + c.quiet ≤ now)

/-- One reading under a given severity rule: the next state and whether an alert is sent. -/
def updateWith (lvl : Incident → Sample → Nat) (c : Config) (s : Incident) (x : Sample) :
    Incident × Bool :=
  let l := lvl s x
  let send := decide (0 < l) && (quietSince c s x.time || decide (s.severity < l))
  ({ lastSample := some x.time
     previousLow := low c x
     lastSymptom := if 0 < l then some x.time else s.lastSymptom
     severity := if send then l else s.severity }, send)

def update (c : Config) (s : Incident) (x : Sample) : Incident × Bool := updateWith (level c) c s x

def sends (c : Config) (s : Incident) (x : Sample) : Bool := (update c s x).2

theorem sends_eq (c : Config) (s : Incident) (x : Sample) :
    sends c s x = (decide (0 < level c s x) &&
      (quietSince c s x.time || decide (s.severity < level c s x))) := rfl

theorem kill_alerts (c : Config) (s : Incident) (x : Sample) (hk : x.killed = true)
    (h : quietSince c s x.time = true ∨ s.severity < 2) : sends c s x = true := by
  have hl : level c s x = 2 := by simp [level, hk]
  rcases h with h | h <;> simp [sends_eq, hl, h]

theorem escalation_alerts (c : Config) (s : Incident) (x : Sample)
    (h : s.severity < level c s x) : sends c s x = true := by
  have hp : 0 < level c s x := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  simp [sends_eq, hp, h]

/-- Without a kill notice a reading is at most a pressure symptom. -/
theorem level_le_one (c : Config) (s : Incident) (x : Sample) (hk : x.killed = false) :
    level c s x ≤ 1 := by
  unfold level
  rw [if_neg (by simp [hk])]
  split
  · exact Nat.le_refl 1
  · split
    · exact Nat.le_refl 1
    · exact Nat.zero_le 1

/-- Low memory in two consecutive readings has severity 1, however far apart the readings are. -/
theorem low_twice_level (c : Config) (s : Incident) (x : Sample) (hprev : s.previousLow = true)
    (hlow : low c x = true) (hk : x.killed = false) (hs : severeStall c x = false) :
    level c s x = 1 := by
  simp [level, hprev, hlow, hk, hs]

theorem low_twice_alerts (c : Config) (s : Incident) (x : Sample) (hprev : s.previousLow = true)
    (hlow : low c x = true) (hk : x.killed = false) (hs : severeStall c x = false)
    (h : quietSince c s x.time = true ∨ s.severity < 1) : sends c s x = true := by
  have hl := low_twice_level c s x hprev hlow hk hs
  rcases h with h | h <;> simp [sends_eq, hl, h]

/-- One low reading after a sampling gap of more than three intervals has severity 1. -/
theorem late_low_level (c : Config) (s : Incident) (x : Sample) (hlow : low c x = true)
    (hk : x.killed = false) (hs : severeStall c x = false) (hgap : 3 * c.interval < gap s x) :
    level c s x = 1 := by
  simp [level, hlow, hk, hs, hgap]

/-- An alert that does not raise the severity needs a quiet period since the last symptom. -/
theorem repeat_needs_quiet (c : Config) (s : Incident) (x : Sample) (hsend : sends c s x = true)
    (hle : level c s x ≤ s.severity) : quietSince c s x.time = true := by
  rw [sends_eq] at hsend
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hsend
  obtain ⟨_, h | h⟩ := hsend
  · exact h
  · exact absurd h (Nat.not_lt.2 hle)

/-- After a pressure warning, further pressure within the quiet window sends nothing. -/
theorem pressure_after_warning_is_quiet (c : Config) (s : Incident) (x : Sample) (t : Nat)
    (hsev : s.severity = 1) (hlast : s.lastSymptom = some t) (hwin : x.time < t + c.quiet)
    (hk : x.killed = false) : sends c s x = false := by
  have hl := level_le_one c s x hk
  have hq : quietSince c s x.time = false := by
    simp [quietSince, hlast]
    omega
  have hr : decide (1 < level c s x) = false := by
    simp
    omega
  rw [sends_eq, hq, hsev, hr]
  simp

/-- A kill after a pressure warning sends the follow-up. -/
theorem kill_follows_warning (c : Config) (s : Incident) (x : Sample) (hk : x.killed = true)
    (hsev : s.severity = 1) : sends c s x = true :=
  kill_alerts c s x hk (Or.inr (by omega))

/-- The earlier rule: low memory counted only when two low readings were at most 45 seconds apart. -/
def oldLevel (c : Config) (s : Incident) (x : Sample) : Nat :=
  if x.killed then 2
  else if severeStall c x then 1
  else if low c x && s.previousLow && decide (0 < gap s x) && decide (gap s x ≤ 45) then 1
  else 0

/-- Under the earlier rule, low memory read later than 45 seconds after the previous reading never
alerts, however low it is. -/
theorem old_rule_misses_late_samples (c : Config) (s : Incident) (x : Sample)
    (hk : x.killed = false) (hs : severeStall c x = false) (hgap : 45 < gap s x) :
    oldLevel c s x = 0 := by
  have h45 : ¬ gap s x ≤ 45 := by omega
  simp [oldLevel, hk, hs, h45]

/-- Alerts sent over a sequence of readings under a severity rule. -/
def countAlerts (lvl : Incident → Sample → Nat) (c : Config) : Incident → List Sample → Nat
  | _, [] => 0
  | s, x :: xs =>
    let r := updateWith lvl c s x
    (if r.2 then 1 else 0) + countAlerts lvl c r.1 xs

/-- Fifteen-second sampling, five quiet minutes, 15 GiB of available memory, 20 % stalls. -/
def defaults : Config :=
  { interval := 15, quiet := 300, lowKiB := 15 * 1024 * 1024, severe := 200 }

def quietStart : Incident :=
  { lastSample := none, previousLow := false, lastSymptom := none, severity := 0 }

/-- Low memory twice, then a severe stall, then a kill notice, fifteen seconds apart. -/
def lowStallKill : List Sample :=
  [{ time := 0, availableKiB := 10 * 1024 * 1024, memStall := 0, ioStall := 0, killed := false },
   { time := 15, availableKiB := 10 * 1024 * 1024, memStall := 0, ioStall := 0, killed := false },
   { time := 30, availableKiB := 10 * 1024 * 1024, memStall := 250, ioStall := 0, killed := false },
   { time := 45, availableKiB := 10 * 1024 * 1024, memStall := 250, ioStall := 0, killed := true }]

/-- One warning on the second low reading and one follow-up for the kill; the stall between them
sends nothing. -/
theorem one_warning_one_follow_up :
    countAlerts (level defaults) defaults quietStart lowStallKill = 2 := by
  decide

/-- After a reading at 21:40:03 (seconds since midnight) with 35.2 GB available. -/
def beforeStorm : Incident :=
  { lastSample := some 78003, previousLow := false, lastSymptom := none, severity := 0 }

/-- The next two readings a thrashing host produced, at 21:56:03 and 22:00:39: 2.9 GB and 2.5 GB
available. Stall averages are set to zero, so only the low-memory rule can fire. -/
def storm : List Sample :=
  [{ time := 78963, availableKiB := 2938932, memStall := 0, ioStall := 0, killed := false },
   { time := 79239, availableKiB := 2495388, memStall := 0, ioStall := 0, killed := false }]

/-- The current rule alerts once at 21:56 and does not repeat four minutes later. -/
theorem storm_alerts_once : countAlerts (level defaults) defaults beforeStorm storm = 1 := by
  decide

/-- The earlier rule stays silent through the same readings. -/
theorem old_rule_silent_in_storm :
    countAlerts (oldLevel defaults) defaults beforeStorm storm = 0 := by
  decide

/-! ## Readout injection -/

/-- What one agent session's hook remembers: when it last injected a reading, and the last kill
notice it showed. -/
structure Stamp where
  last : Option Nat
  seen : Option Nat
  deriving Repr

def elapsed (st : Stamp) (now : Nat) : Bool :=
  match st.last with
  | none => true
  | some t => decide (t + 60 ≤ now)

def fresh (st : Stamp) (notice : Option Nat) : Bool :=
  match notice with
  | none => false
  | some n => decide (st.seen ≠ some n)

/-- Inject at the start of a turn, for a new kill notice, or a minute after the last injection. -/
def injects (st : Stamp) (now : Nat) (turnStart : Bool) (notice : Option Nat) : Bool :=
  turnStart || elapsed st now || fresh st notice

/-- The stamp after an injection at `now`. -/
def record (st : Stamp) (now : Nat) (notice : Option Nat) : Stamp :=
  { last := some now
    seen := match notice with
      | some n => some n
      | none => st.seen }

theorem turn_start_injects (st : Stamp) (now : Nat) (notice : Option Nat) :
    injects st now true notice = true := by
  simp [injects]

theorem new_notice_injects (st : Stamp) (now : Nat) (turnStart : Bool) (n : Nat)
    (h : st.seen ≠ some n) : injects st now turnStart (some n) = true := by
  simp [injects, fresh, h]

/-- Within a minute of an injection, with no new turn and no new kill notice, nothing is injected. -/
theorem once_a_minute (st : Stamp) (t u : Nat) (notice notice' : Option Nat) (hu : u < t + 60)
    (hnew : notice' = none ∨ notice' = (record st t notice).seen) :
    injects (record st t notice) u false notice' = false := by
  have he : elapsed (record st t notice) u = false := by
    simp [elapsed, record]
    omega
  have hf : fresh (record st t notice) notice' = false := by
    rcases hnew with h | h
    · simp [h, fresh]
    · cases notice' with
      | none => rfl
      | some n =>
        show decide ((record st t notice).seen ≠ some n) = false
        rw [← h]
        simp
  simp [injects, he, hf]

theorem minute_later_injects (st : Stamp) (t u : Nat) (notice notice' : Option Nat)
    (turnStart : Bool) (hu : t + 60 ≤ u) :
    injects (record st t notice) u turnStart notice' = true := by
  simp [injects, elapsed, record, hu]

/-- Characters a process name may keep in a reading. -/
def allowed (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '+' || c == '-'

def fixChar (c : Char) : Char := if allowed c then c else '_'

/-- A process name as it appears in a reading: other characters replaced, length capped. -/
def sanitize (limit : Nat) (name : List Char) : List Char := (name.map fixChar).take limit

theorem fixChar_allowed (c : Char) : allowed (fixChar c) = true := by
  unfold fixChar
  split
  · assumption
  · decide

theorem sanitize_allowed (limit : Nat) (name : List Char) :
    ∀ c ∈ sanitize limit name, allowed c = true := by
  intro c hc
  have hm := List.mem_of_mem_take hc
  rw [List.mem_map] at hm
  obtain ⟨d, _, rfl⟩ := hm
  exact fixChar_allowed d

theorem sanitize_length_le (limit : Nat) (name : List Char) :
    (sanitize limit name).length ≤ limit :=
  List.length_take_le _ _

/-! ## Alert delivery -/

/-- What one send attempt did at the receiver. The sender sees only whether an answer came back:
`lost` and `storedUnconfirmed` look the same to it. -/
inductive Attempt where
  /-- never reached the receiver -/
  | lost
  /-- stored, but the answer was lost or timed out -/
  | storedUnconfirmed
  /-- stored and answered -/
  | confirmed
  deriving DecidableEq, Repr

/-- A receiver that stores each message id at most once. -/
def store (inbox : List Nat) (id : Nat) : List Nat :=
  if id ∈ inbox then inbox else id :: inbox

/-- Retrying with one fixed id until an attempt is answered. -/
def retryFixed (inbox : List Nat) (id : Nat) : List Attempt → List Nat
  | [] => inbox
  | .lost :: rest => retryFixed inbox id rest
  | .storedUnconfirmed :: rest => retryFixed (store inbox id) id rest
  | .confirmed :: _ => store inbox id

/-- Stopping after the first attempt, whatever it reported. -/
def stopAfterFirst (inbox : List Nat) (id : Nat) : List Attempt → List Nat
  | [] => inbox
  | .lost :: _ => inbox
  | _ :: _ => store inbox id

/-- Retrying with a fresh id on every attempt. -/
def retryFresh (inbox : List Nat) : Nat → List Attempt → List Nat
  | _, [] => inbox
  | id, .lost :: rest => retryFresh inbox (id + 1) rest
  | id, .storedUnconfirmed :: rest => retryFresh (store inbox id) (id + 1) rest
  | id, .confirmed :: _ => store inbox id

theorem store_nodup (inbox : List Nat) (id : Nat) (h : inbox.Nodup) : (store inbox id).Nodup := by
  unfold store
  split
  · exact h
  · exact List.nodup_cons.2 ⟨by assumption, h⟩

theorem mem_store (inbox : List Nat) (id : Nat) : id ∈ store inbox id := by
  unfold store
  split
  · assumption
  · simp

theorem store_keeps {inbox : List Nat} {x : Nat} (id : Nat) (h : x ∈ inbox) :
    x ∈ store inbox id := by
  unfold store
  split
  · exact h
  · simp [h]

theorem retryFixed_keeps (id x : Nat) : ∀ (inbox : List Nat) (attempts : List Attempt),
    x ∈ inbox → x ∈ retryFixed inbox id attempts
  | _, [], h => h
  | inbox, .lost :: rest, h => by
    simp only [retryFixed]
    exact retryFixed_keeps id x inbox rest h
  | inbox, .storedUnconfirmed :: rest, h => by
    simp only [retryFixed]
    exact retryFixed_keeps id x (store inbox id) rest (store_keeps id h)
  | inbox, .confirmed :: _, h => by
    simp only [retryFixed]
    exact store_keeps id h

/-- With one id and a deduplicating receiver the inbox never holds a message twice. -/
theorem retryFixed_nodup (id : Nat) : ∀ (inbox : List Nat) (attempts : List Attempt),
    inbox.Nodup → (retryFixed inbox id attempts).Nodup
  | _, [], h => h
  | inbox, .lost :: rest, h => by
    simp only [retryFixed]
    exact retryFixed_nodup id inbox rest h
  | inbox, .storedUnconfirmed :: rest, h => by
    simp only [retryFixed]
    exact retryFixed_nodup id (store inbox id) rest (store_nodup inbox id h)
  | inbox, .confirmed :: _, h => by
    simp only [retryFixed]
    exact store_nodup inbox id h

/-- With one id the alert is delivered as soon as any attempt reaches the receiver. -/
theorem retryFixed_delivers (id : Nat) : ∀ (inbox : List Nat) (attempts : List Attempt),
    (∃ a ∈ attempts, a ≠ .lost) → id ∈ retryFixed inbox id attempts
  | _, [], ⟨_, ha, _⟩ => by simp at ha
  | inbox, .lost :: rest, ⟨a, ha, hne⟩ => by
    simp only [retryFixed]
    apply retryFixed_delivers id inbox rest
    rcases List.mem_cons.1 ha with h | h
    · exact absurd h hne
    · exact ⟨a, h, hne⟩
  | inbox, .storedUnconfirmed :: rest, _ => by
    simp only [retryFixed]
    exact retryFixed_keeps id id (store inbox id) rest (mem_store inbox id)
  | inbox, .confirmed :: _, _ => by
    simp only [retryFixed]
    exact mem_store inbox id

/-- Retrying with one id after a lost first attempt delivers the alert once. -/
theorem retrying_delivers : retryFixed [] 7 [.lost, .confirmed] = [7] := by decide

/-- Stored copies of one message at a receiver that appends every message it receives, for a sender
that after `k` unanswered attempts tries again exactly when `again k` holds. The first attempt is
always made. -/
def copies (again : Nat → Bool) : Nat → List Attempt → Nat
  | _, [] => 0
  | k, .lost :: rest => if again (k + 1) then copies again (k + 1) rest else 0
  | k, .storedUnconfirmed :: rest => 1 + (if again (k + 1) then copies again (k + 1) rest else 0)
  | _, .confirmed :: _ => 1

/-- Against an appending receiver, a sender that delivers when its first attempt is lost and a retry
would be answered stores two copies when only the answer to its first attempt is lost: the two
cases look the same to it. -/
theorem retry_without_dedup_duplicates (again : Nat → Bool)
    (delivers : 1 ≤ copies again 0 [.lost, .confirmed]) :
    2 ≤ copies again 0 [.storedUnconfirmed, .confirmed] := by
  cases h : again 1 with
  | false => simp [copies, h] at delivers
  | true => simp [copies, h]

/-- Sending once and never retrying stores at most one copy, even at an appending receiver. -/
theorem no_retry_at_most_once (attempts : List Attempt) :
    copies (fun _ => false) 0 attempts ≤ 1 := by
  cases attempts with
  | nil => simp [copies]
  | cons a rest => cases a <;> simp [copies]

/-- Sending once loses the alert when that attempt never arrives. -/
theorem stopping_loses : stopAfterFirst [] 7 [.lost, .confirmed] = [] := by decide

/-- A fresh id per retry stores one alert twice when the first answer is lost, even at a receiver
that deduplicates by id. -/
theorem fresh_ids_duplicate : retryFresh [] 7 [.storedUnconfirmed, .confirmed] = [8, 7] := by
  decide

end Mettapedia.Machines.HostPressure
