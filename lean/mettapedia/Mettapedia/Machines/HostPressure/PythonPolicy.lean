import Mettapedia.Machines.HostPressure

/-!
# Correspondence of observer decisions

The first definitions represent the Python decision slice over normalized
`HostPressure` inputs. The source check extracts the deployed branches and
checks their equality to these terms. The proofs compare the extracted
severity, decision and state projection with the host-pressure transition.
The hook guard is expressed over its computed age and notice predicates.

Floating-point comparisons on the running interpreter are exercised by replay.
The operational boundary includes snapshot and stamp I/O, journal receipt,
and mail submission.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HostPressure.PythonPolicy

/-- The right operand of the Python timestamp guard, evaluated only when a
    previous symptom timestamp exists. -/
def quietWithTimestamp (c : Config) (s : Incident) (now : Nat) : Bool :=
  match s.lastSymptom with
  | none => false
  | some previous => decide (previous + c.quiet ≤ now)

def pythonLevel (c : Config) (s : Incident) (x : Sample) : Nat :=
  if x.killed then 2
  else if decide (c.severe ≤ x.memStall) || decide (c.severe ≤ x.ioStall) then 1
  else if low c x && ((s.previousLow && low c x) || decide (3 * c.interval < gap s x)) then 1
  else 0

def pythonSend (c : Config) (s : Incident) (x : Sample) (l : Nat) : Bool :=
  decide (0 < l) &&
    (s.lastSymptom.isNone || quietWithTimestamp c s x.time || decide (s.severity < l))

def pythonStep (c : Config) (s : Incident) (x : Sample) : Incident × Bool :=
  let l := pythonLevel c s x
  let send := pythonSend c s x l
  let symptom := if l = 0 then s.lastSymptom else some x.time
  let severity := if send then l else s.severity
  (⟨some x.time, low c x, symptom, severity⟩, send)

def pythonSuppress (turnStart recent hasNotice sameNotice : Bool) : Bool :=
  !turnStart && recent && (!hasNotice || sameNotice)

theorem extracted_level_agrees (c : Config) (s : Incident) (x : Sample) :
    pythonLevel c s x = level c s x := by
  unfold pythonLevel level severeStall
  cases earlier : s.previousLow <;> cases isLow : low c x <;> simp_all

theorem extracted_send_agrees (c : Config) (s : Incident) (x : Sample) :
    pythonSend c s x (pythonLevel c s x) = (update c s x).2 := by
  rw [extracted_level_agrees]
  cases h : s.lastSymptom <;>
    simp [pythonSend, update, updateWith, quietSince, quietWithTimestamp, h]

theorem extracted_step_agrees (c : Config) (s : Incident) (x : Sample) :
    pythonStep c s x = update c s x := by
  have sent := extracted_send_agrees c s x
  rw [extracted_level_agrees] at sent
  simp only [pythonStep, extracted_level_agrees, sent]
  unfold update updateWith
  dsimp
  by_cases zero : level c s x = 0
  · simp [zero]
  · simp [zero, Nat.pos_of_ne_zero zero]

theorem extracted_escalation_alerts (c : Config) (s : Incident) (x : Sample)
    (killed : x.killed = true) (beforeKill : s.severity < 2) :
    pythonSend c s x (pythonLevel c s x) = true := by
  rw [extracted_send_agrees]
  exact kill_alerts c s x killed (.inr beforeKill)

theorem extracted_hook_agrees (turnStart recent hasNotice sameNotice : Bool) :
    (!(pythonSuppress turnStart recent hasNotice sameNotice)) =
      (turnStart || !recent || (hasNotice && !sameNotice)) := by
  cases turnStart <;> cases recent <;> cases hasNotice <;> cases sameNotice <;> rfl

/-- Once the adapter has computed its normalized age and notice predicates,
    its suppression decision is the complement of the hook policy. -/
theorem extracted_hook_respects_stamp (stamp : Stamp) (now : Nat) (turnStart : Bool)
    (notice : Option Nat) :
    (!(pythonSuppress turnStart (!(elapsed stamp now)) notice.isSome (stamp.seen == notice))) =
      injects stamp now turnStart notice := by
  rw [extracted_hook_agrees]
  cases notice with
  | none => simp [fresh, injects]
  | some name =>
    cases seen : stamp.seen with
    | none => simp [fresh, injects, seen]
    | some old => simp [fresh, injects, seen, Bool.beq_eq_decide_eq]

theorem deployed_level_le (c : Config) (s : Incident) (x : Sample) :
    level c s x ≤ 2 := by
  cases killed : x.killed with
  | false => exact Nat.le_trans (level_le_one c s x killed) (by decide)
  | true => simp [level, killed]

/-- Before the quiet period reopens, an alert requires a rise in severity. -/
theorem continuing_step (c : Config) (s : Incident) (x : Sample)
    (quiet : quietSince c s x.time = false) (bound : s.severity ≤ 2) :
    let result := pythonStep c s x
    result.1.severity ≤ 2 ∧ s.severity + (if result.2 then 1 else 0) ≤ result.1.severity := by
  rw [extracted_step_agrees]
  unfold update updateWith
  dsimp
  rw [quiet]
  by_cases raised : s.severity < level c s x
  · have positive : 0 < level c s x := by omega
    simpa [positive, raised, Nat.succ_le_iff] using
      And.intro (deployed_level_le c s x) raised
  · simp [raised, bound]

/-- Each sample falls within the quiet window of the evolving incident. -/
inductive Continuing (c : Config) : Incident → List Sample → Prop where
  | finished (s : Incident) : Continuing c s []
  | sampled {s : Incident} {x : Sample} {xs : List Sample}
      (quiet : quietSince c s x.time = false)
      (rest : Continuing c (update c s x).1 xs) :
      Continuing c s (x :: xs)

theorem continuing_alert_bound (c : Config) {s : Incident} {xs : List Sample}
    (trace : Continuing c s xs) (bound : s.severity ≤ 2) :
    countAlerts (level c) c s xs + s.severity ≤ 2 := by
  induction trace with
  | finished current => simpa [countAlerts] using bound
  | @sampled current sample tail quiet rest ih =>
    have step := continuing_step c current sample quiet bound
    rw [extracted_step_agrees] at step
    have remaining := ih step.1
    simp only [countAlerts]
    unfold update at step remaining
    omega

end Mettapedia.Machines.HostPressure.PythonPolicy
