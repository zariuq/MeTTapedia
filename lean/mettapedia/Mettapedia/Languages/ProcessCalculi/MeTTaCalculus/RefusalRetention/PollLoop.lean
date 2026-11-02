import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# A refused call retained and polled: retention without progress

A reader that needs the next answer of a shared producer asks the producer to advance. When the
producer's next step is a call, the producer first checks the call against the receiving context
(its permission to run that call). Under the **native rule** examined here, a refusal leaves the
exact task pending and reports the step as *paused*; the reader treats *paused* as "resume me
later" and is resumed with the same receiving context. This module states that rule and proves
exactly what it guarantees and what it does not, then states the rule that should replace it.

## The native rule (`poll`)

`produce` runs the call when `permit ctx task` holds and pauses otherwise. `poll` applies one
producer step to a pending reader: a value is observed, or the reader is left as it was, apart
from its poll count.

## What holds

* **Retention** (`poll_refused_retains`, `iterate_poll_refused`): a refused poll changes nothing
  but the count. The task is the same task, nothing is observed, and nothing is paid. This is the
  property a retained-refusal control checks after two retries (`Controls.two_polls_retain`).
* A permitted call is observed at the next poll (`poll_permitted`).

## What fails

* **A refused call is never observed** (`refused_never_observes`): when the receiving context does
  not change between polls, every later poll pauses again, so the reader neither returns a value,
  nor a fault, nor an explicit refusal, nor a residual. Whether it is ever observed is exactly
  whether it was permitted at the first poll (`observes_iff_permitted`).
* **Environment events do not rescue an unjustified pause** (`native_never_observes`): a pause is
  *justified* when some sequence of environment events (a grant, an input) makes the call
  permitted. When it is not, no interleaving of polls and events ever lets the reader observe.
* **A retention check cannot tell a wait from a livelock** (`Controls.retention_does_not_separate`):
  two readers pass the same two-retry retention check; one completes after a grant, the other
  never completes.

## The repair

* **Counting the refusal** (`pollCounted`): a refused poll reports an explicit refusal, an
  observation distinct from every value (`refused_ne_value`); a pending reader is observed at its
  next poll (`pollCounted_observes`), and on permitted calls the rule is the native rule
  (`pollCounted_eq_poll_of_permitted`). Counting alone also refuses a call that a later grant
  would have allowed (`Controls.counted_refuses_a_justified_wait`).
* **The obligation** (`pollObliged`): pause only when the call is registered on a wake source
  (`wakeable`), and count the refusal otherwise. When registration is sound, that is, a registered
  call is justified, a reader left pending by a poll is always justified (`pollObliged_pending_justified`),
  so no reader waits on a call that nothing can enable; on permitted or registered calls the rule
  is the native rule (`pollObliged_eq_poll`), on unregistered ones it is the counted rule
  (`pollObliged_eq_counted`), and an unregistered refusal is reported at once
  (`pollObliged_refused`). With exact registration it keeps every legitimate wait and reports every
  refusal that nothing can lift (`pollObliged_exact`).

This is a model of one reader and one pending call. It is not a proof about compiled C.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RefusalRetention

universe u v w x

variable {Ctx : Type u} {Task : Type v} {Value : Type w} {E : Type x}

/-- What a reader observes of a call: its value, or an explicit refusal. -/
inductive Observation (Value : Type w)
  | value : Value → Observation Value
  | refused : Observation Value
  deriving DecidableEq

/-- What one producer step reports: a value, or a pause that leaves the task pending. -/
inductive Step (Value : Type w)
  | done : Value → Step Value
  | paused : Step Value
  deriving DecidableEq

/-- The producer's step on a pending call: it runs when the receiving context permits it, and
pauses otherwise. -/
def produce (permit : Ctx → Task → Bool) (run : Task → Value) (ctx : Ctx) (task : Task) :
    Step Value :=
  if permit ctx task then .done (run task) else .paused

/-- A reader: its receiving context, its pending task, what it has observed, and its polls. -/
structure Reader (Ctx : Type u) (Task : Type v) (Value : Type w) where
  ctx : Ctx
  task : Task
  observed : Option (Observation Value)
  polls : ℕ

/-- **The native rule.** A pause leaves the reader as it was, apart from its poll count. -/
def poll (permit : Ctx → Task → Bool) (run : Task → Value) (r : Reader Ctx Task Value) :
    Reader Ctx Task Value :=
  match r.observed with
  | some _ => r
  | none =>
    match produce permit run r.ctx r.task with
    | .done val => { r with observed := some (.value val), polls := r.polls + 1 }
    | .paused => { r with polls := r.polls + 1 }

/-- **The counted rule.** A refusal is a failed attempt, reported to the reader. -/
def pollCounted (permit : Ctx → Task → Bool) (run : Task → Value) (r : Reader Ctx Task Value) :
    Reader Ctx Task Value :=
  match r.observed with
  | some _ => r
  | none =>
    match produce permit run r.ctx r.task with
    | .done val => { r with observed := some (.value val), polls := r.polls + 1 }
    | .paused => { r with observed := some .refused, polls := r.polls + 1 }

/-- **The obligated rule.** A refused call pauses only when it is registered on a wake source
(`wakeable`); otherwise the refusal is reported. -/
def pollObliged (permit wakeable : Ctx → Task → Bool) (run : Task → Value)
    (r : Reader Ctx Task Value) : Reader Ctx Task Value :=
  match r.observed with
  | some _ => r
  | none =>
    match produce permit run r.ctx r.task with
    | .done val => { r with observed := some (.value val), polls := r.polls + 1 }
    | .paused =>
      if wakeable r.ctx r.task then { r with polls := r.polls + 1 }
      else { r with observed := some .refused, polls := r.polls + 1 }

section Native

variable (permit : Ctx → Task → Bool) (run : Task → Value)

/-- **Retention.** A refused poll changes nothing but the poll count. -/
theorem poll_refused_retains {r : Reader Ctx Task Value} (pending : r.observed = none)
    (refused : permit r.ctx r.task = false) :
    poll permit run r = { r with polls := r.polls + 1 } := by
  simp [poll, pending, produce, refused]

/-- A permitted call is observed at the next poll. -/
theorem poll_permitted {r : Reader Ctx Task Value} (pending : r.observed = none)
    (permitted : permit r.ctx r.task = true) :
    (poll permit run r).observed = some (.value (run r.task)) := by
  simp [poll, pending, produce, permitted]

/-- **Retention, iterated.** Any number of refused polls leave the same pending task. -/
theorem iterate_poll_refused (n : ℕ) {r : Reader Ctx Task Value} (pending : r.observed = none)
    (refused : permit r.ctx r.task = false) :
    (poll permit run)^[n] r = { r with polls := r.polls + n } := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, poll_refused_retains permit run pending refused,
      ih (r := { r with polls := r.polls + 1 }) pending refused]
    simp only [Nat.add_assoc, Nat.add_comm 1 n]

/-- **A refused call is never observed** under the native rule. -/
theorem refused_never_observes {r : Reader Ctx Task Value} (pending : r.observed = none)
    (refused : permit r.ctx r.task = false) (n : ℕ) :
    ((poll permit run)^[n] r).observed = none := by
  rw [iterate_poll_refused permit run n pending refused]
  exact pending

/-- **Exactly the calls permitted at the first poll are ever observed.** -/
theorem observes_iff_permitted {r : Reader Ctx Task Value} (pending : r.observed = none) :
    (∃ n, ((poll permit run)^[n] r).observed ≠ none) ↔ permit r.ctx r.task = true := by
  constructor
  · rintro ⟨n, seen⟩
    by_contra notPermitted
    exact seen (refused_never_observes permit run pending (by simpa using notPermitted) n)
  · intro permitted
    refine ⟨1, ?_⟩
    rw [Function.iterate_one, poll_permitted permit run pending permitted]
    simp

end Native

/-! ## Environment events and justified pauses -/

/-- The receiving context after a sequence of environment events. -/
def afterEvents (apply : E → Ctx → Ctx) (events : List E) (ctx : Ctx) : Ctx :=
  events.foldl (fun c e => apply e c) ctx

@[simp] theorem afterEvents_nil (apply : E → Ctx → Ctx) (ctx : Ctx) :
    afterEvents apply [] ctx = ctx := rfl

@[simp] theorem afterEvents_cons (apply : E → Ctx → Ctx) (e : E) (events : List E) (ctx : Ctx) :
    afterEvents apply (e :: events) ctx = afterEvents apply events (apply e ctx) := rfl

/-- A pause is **justified** when some sequence of environment events makes the call permitted. -/
def Justified (apply : E → Ctx → Ctx) (permit : Ctx → Task → Bool) (ctx : Ctx) (task : Task) :
    Prop :=
  ∃ events : List E, permit (afterEvents apply events ctx) task = true

/-- An unjustified pause stays unjustified after any event. -/
theorem not_justified_apply {apply : E → Ctx → Ctx} {permit : Ctx → Task → Bool} {ctx : Ctx}
    {task : Task} (unjustified : ¬ Justified apply permit ctx task) (e : E) :
    ¬ Justified apply permit (apply e ctx) task := by
  rintro ⟨events, permitted⟩
  exact unjustified ⟨e :: events, permitted⟩

/-- An unjustified call is refused in its current context. -/
theorem refused_of_not_justified {apply : E → Ctx → Ctx} {permit : Ctx → Task → Bool}
    {ctx : Ctx} {task : Task} (unjustified : ¬ Justified apply permit ctx task) :
    permit ctx task = false := by
  by_contra notRefused
  exact unjustified ⟨[], by simpa using notRefused⟩

/-- What the reader's world can do: poll the reader, or deliver an environment event. -/
inductive Action (E : Type x)
  | poll : Action E
  | event : E → Action E

/-- One action, with a given polling rule. -/
def act (apply : E → Ctx → Ctx) (rule : Reader Ctx Task Value → Reader Ctx Task Value)
    (r : Reader Ctx Task Value) : Action E → Reader Ctx Task Value
  | .poll => rule r
  | .event e => { r with ctx := apply e r.ctx }

/-- A sequence of actions. -/
def actAll (apply : E → Ctx → Ctx) (rule : Reader Ctx Task Value → Reader Ctx Task Value)
    (actions : List (Action E)) (r : Reader Ctx Task Value) : Reader Ctx Task Value :=
  actions.foldl (act apply rule) r

/-- **Events do not rescue an unjustified pause.** Under the native rule, a pending reader whose
call is unjustified is never observed, whatever polls and events follow. -/
theorem native_never_observes (apply : E → Ctx → Ctx) (permit : Ctx → Task → Bool)
    (run : Task → Value) (actions : List (Action E)) {r : Reader Ctx Task Value}
    (pending : r.observed = none) (unjustified : ¬ Justified apply permit r.ctx r.task) :
    (actAll apply (poll permit run) actions r).observed = none := by
  induction actions generalizing r with
  | nil => exact pending
  | cons a rest ih =>
    unfold actAll
    rw [List.foldl_cons]
    cases a with
    | poll =>
      have refused := refused_of_not_justified unjustified
      rw [act, poll_refused_retains permit run pending refused]
      exact ih pending unjustified
    | event e =>
      exact ih (r := { r with ctx := apply e r.ctx }) pending (not_justified_apply unjustified e)

/-- A justified pause completes under the native rule once its enabling events arrive. -/
theorem native_completes_after_events (apply : E → Ctx → Ctx) (permit : Ctx → Task → Bool)
    (run : Task → Value) (events : List E) {r : Reader Ctx Task Value}
    (pending : r.observed = none) (enabled : permit (afterEvents apply events r.ctx) r.task = true) :
    (actAll apply (poll permit run) (events.map Action.event ++ [Action.poll]) r).observed =
      some (.value (run r.task)) := by
  induction events generalizing r with
  | nil =>
    simp only [List.map_nil, List.nil_append, actAll, List.foldl_cons, List.foldl_nil, act]
    exact poll_permitted permit run pending (by simpa using enabled)
  | cons e rest ih =>
    simp only [List.map_cons, List.cons_append, actAll, List.foldl_cons, act] at ih ⊢
    exact ih (r := { r with ctx := apply e r.ctx }) pending (by simpa using enabled)

/-! ## The repair -/

section Repair

variable (permit : Ctx → Task → Bool) (run : Task → Value)

/-- An explicit refusal is distinct from every value. -/
theorem refused_ne_value (val : Value) : (Observation.refused : Observation Value) ≠ .value val := by
  intro same
  cases same

/-- **Counting the refusal: every pending reader is observed at its next poll.** -/
theorem pollCounted_observes {r : Reader Ctx Task Value} (pending : r.observed = none) :
    (pollCounted permit run r).observed ≠ none := by
  cases permitted : permit r.ctx r.task <;> simp [pollCounted, pending, produce, permitted]

/-- A refused call is reported as refused under the counted rule. -/
theorem pollCounted_refused {r : Reader Ctx Task Value} (pending : r.observed = none)
    (refused : permit r.ctx r.task = false) :
    (pollCounted permit run r).observed = some .refused := by
  simp [pollCounted, pending, produce, refused]

/-- On a permitted call the counted rule is the native rule. -/
theorem pollCounted_eq_poll_of_permitted {r : Reader Ctx Task Value}
    (permitted : permit r.ctx r.task = true) : pollCounted permit run r = poll permit run r := by
  unfold pollCounted poll
  cases r.observed <;> simp [produce, permitted]

variable (wakeable : Ctx → Task → Bool)

/-- **The obligated rule changes only unregistered refusals.** On a permitted call, or a refused
call registered on a wake source, it is the native rule. -/
theorem pollObliged_eq_poll {r : Reader Ctx Task Value}
    (permittedOrRegistered : permit r.ctx r.task = true ∨ wakeable r.ctx r.task = true) :
    pollObliged permit wakeable run r = poll permit run r := by
  unfold pollObliged poll
  cases r.observed with
  | some _ => rfl
  | none =>
    rcases permittedOrRegistered with permitted | registered
    · simp [produce, permitted]
    · cases permitted : permit r.ctx r.task <;> simp [produce, permitted, registered]

/-- An unregistered refusal is reported at once. -/
theorem pollObliged_refused {r : Reader Ctx Task Value} (pending : r.observed = none)
    (refused : permit r.ctx r.task = false) (unregistered : wakeable r.ctx r.task = false) :
    (pollObliged permit wakeable run r).observed = some .refused := by
  simp [pollObliged, pending, produce, refused, unregistered]

/-- **No reader waits on a call that nothing can enable.** When registration is sound, a reader
that a poll leaves pending has a justified call. -/
theorem pollObliged_pending_justified (apply : E → Ctx → Ctx)
    (sound : ∀ c t, wakeable c t = true → Justified apply permit c t)
    {r : Reader Ctx Task Value}
    (stillPending : (pollObliged permit wakeable run r).observed = none) :
    Justified apply permit (pollObliged permit wakeable run r).ctx
      (pollObliged permit wakeable run r).task := by
  unfold pollObliged at stillPending ⊢
  cases seen : r.observed with
  | some _ => simp [seen] at stillPending
  | none =>
    cases permitted : permit r.ctx r.task with
    | true => simp [seen, produce, permitted] at stillPending
    | false =>
      cases registered : wakeable r.ctx r.task with
      | false => simp [seen, produce, permitted, registered] at stillPending
      | true =>
        simp only [produce, permitted]
        exact sound _ _ registered

/-- Where a call is not registered, the obligated rule is the counted rule. -/
theorem pollObliged_eq_counted {r : Reader Ctx Task Value}
    (unregistered : wakeable r.ctx r.task = false) :
    pollObliged permit wakeable run r = pollCounted permit run r := by
  unfold pollObliged pollCounted
  cases r.observed with
  | some _ => rfl
  | none => cases permitted : permit r.ctx r.task <;> simp [produce, permitted, unregistered]

/-- **With exact registration the obligated rule is the native rule on justified calls and the
counted rule on unjustified ones**: it keeps every legitimate wait and reports every refusal that
nothing can lift. -/
theorem pollObliged_exact (apply : E → Ctx → Ctx)
    (exact : ∀ c t, wakeable c t = true ↔ Justified apply permit c t)
    (r : Reader Ctx Task Value) :
    (Justified apply permit r.ctx r.task → pollObliged permit wakeable run r = poll permit run r) ∧
      (¬ Justified apply permit r.ctx r.task →
        pollObliged permit wakeable run r = pollCounted permit run r) := by
  refine ⟨fun justified => ?_, fun unjustified => ?_⟩
  · exact pollObliged_eq_poll permit run wakeable (Or.inr ((exact _ _).2 justified))
  · apply pollObliged_eq_counted permit run wakeable
    cases registered : wakeable r.ctx r.task with
    | false => rfl
    | true => exact absurd ((exact _ _).1 registered) unjustified

end Repair

/-! ## A paid prefix and a context-indexed continuation

Counting a refusal is enough only while the retained task itself is the whole
unpaid computation. A source may already have emitted a visible effect and
then reach its first context-dependent read. Re-running the source in another
context duplicates that paid prefix. The transferable object at this boundary
is therefore the continuation after the prefix, indexed by the requesting
context.

`PaidPrefixContinuation` is the small observation needed here: it does not
model an evaluator or claim a C refinement. It separates resuming the retained
continuation from restarting the source, and supplies positive and negative
controls for the implementation boundary.
-/

section PaidPrefix

variable {Effect : Type u}

/-- A task continuation retained after an already-paid visible prefix. -/
structure PaidPrefixContinuation (Ctx : Type u) (Task : Type v)
    (Effect : Type w) (Value : Type x) where
  paid : List Effect
  task : Task
  resumeValue : Ctx → Task → Value

/-- Resume the retained suffix in a requesting context. The paid trace is
observed once. -/
def PaidPrefixContinuation.resume
    (continuation : PaidPrefixContinuation Ctx Task Effect Value) (ctx : Ctx) :
    List Effect × Value :=
  (continuation.paid, continuation.resumeValue ctx continuation.task)

/-- Restarting the source after the same visible prefix has already happened
duplicates that prefix before reaching the same suffix. -/
def PaidPrefixContinuation.restart
    (continuation : PaidPrefixContinuation Ctx Task Effect Value) (ctx : Ctx) :
    List Effect × Value :=
  (continuation.paid ++ continuation.paid,
    continuation.resumeValue ctx continuation.task)

@[simp] theorem PaidPrefixContinuation.resume_effects
    (continuation : PaidPrefixContinuation Ctx Task Effect Value) (ctx : Ctx) :
    (continuation.resume ctx).1 = continuation.paid := rfl

@[simp] theorem PaidPrefixContinuation.restart_effects
    (continuation : PaidPrefixContinuation Ctx Task Effect Value) (ctx : Ctx) :
    (continuation.restart ctx).1 = continuation.paid ++ continuation.paid := rfl

/-- A nonempty paid prefix makes source restart observably different from
continuation resumption, independently of the returned value. -/
theorem PaidPrefixContinuation.restart_ne_resume_of_paid
    (continuation : PaidPrefixContinuation Ctx Task Effect Value)
    (paid : continuation.paid ≠ []) (ctx : Ctx) :
    continuation.restart ctx ≠ continuation.resume ctx := by
  intro same
  have lengths := congrArg (fun result => result.1.length) same
  cases kept : continuation.paid with
  | nil => exact (paid kept).elim
  | cons effect rest =>
      simp [PaidPrefixContinuation.restart, PaidPrefixContinuation.resume, kept] at lengths

/-- Two requesting contexts select their own suffix values while sharing the
same single paid prefix. -/
theorem PaidPrefixContinuation.resumes_share_paid
    (continuation : PaidPrefixContinuation Ctx Task Effect Value)
    (left right : Ctx) :
    (continuation.resume left).1 = (continuation.resume right).1 := rfl

namespace PaidPrefixControls

inductive PrefixEffect
  | tick
  deriving DecidableEq

/-- One visible effect, followed by a context-dependent answer. -/
def contextContinuation :
    PaidPrefixContinuation Bool Unit PrefixEffect ℕ where
  paid := [.tick]
  task := ()
  resumeValue := fun right _ => if right then 2 else 1

/-- Positive: the two contexts retain one shared effect and produce distinct
answers. -/
theorem context_fork_preserves_paid_prefix :
    contextContinuation.resume false = ([.tick], 1) ∧
      contextContinuation.resume true = ([.tick], 2) := by
  simp [contextContinuation, PaidPrefixContinuation.resume]

/-- Negative: restarting for the second context repeats the visible effect. -/
theorem context_restart_duplicates_paid_prefix :
    contextContinuation.restart true = ([.tick, .tick], 2) ∧
      contextContinuation.restart true ≠ contextContinuation.resume true := by
  simp [contextContinuation, PaidPrefixContinuation.restart,
    PaidPrefixContinuation.resume]

end PaidPrefixControls

end PaidPrefix

/-! ## Controls

A receiving context is a Boolean: whether the receiver holds the grant the call needs. Two
environments: in one, the only event grants (a later grant can arrive); in the other, the only
event changes nothing (no grant can arrive). -/

namespace Controls

/-- The call needs the grant. -/
def needsGrant : Bool → Unit → Bool := fun held _ => held

/-- The call's value. -/
def answer : Unit → ℕ := fun _ => 42

/-- An environment whose event grants. -/
def grants : Unit → Bool → Bool := fun _ _ => true

/-- An environment whose event changes nothing. -/
def inert : Unit → Bool → Bool := fun _ held => held

/-- A pending reader without the grant. -/
def waiting : Reader Bool Unit ℕ := ⟨false, (), none, 0⟩

/-- The retained-refusal check: after two retries, the task is the same, nothing is observed,
and exactly the two polls were taken. -/
def RetainsAfterTwoPolls (r : Reader Bool Unit ℕ) : Prop :=
  ((poll needsGrant answer)^[2] r).task = r.task ∧
    ((poll needsGrant answer)^[2] r).observed = none ∧
    ((poll needsGrant answer)^[2] r).polls = r.polls + 2

/-- The waiting reader passes the retained-refusal check. -/
theorem two_polls_retain : RetainsAfterTwoPolls waiting := by
  refine ⟨rfl, rfl, rfl⟩

/-- Positive control: where a grant can arrive, the pause is justified and the call completes
after the grant. -/
theorem grant_completes :
    Justified grants needsGrant waiting.ctx waiting.task ∧
      (actAll grants (poll needsGrant answer) [Action.event (), Action.poll] waiting).observed =
        some (.value 42) := by
  refine ⟨⟨[()], rfl⟩, rfl⟩

/-- Negative control: where no grant can arrive, the pause is unjustified and the reader is never
observed, whatever happens. -/
theorem inert_never_completes :
    ¬ Justified inert needsGrant waiting.ctx waiting.task ∧
      ∀ actions : List (Action Unit),
        (actAll inert (poll needsGrant answer) actions waiting).observed = none := by
  have unjustified : ¬ Justified inert needsGrant waiting.ctx waiting.task := by
    rintro ⟨events, permitted⟩
    induction events with
    | nil => exact Bool.false_ne_true permitted
    | cons e rest ih => exact ih permitted
  exact ⟨unjustified, fun actions => native_never_observes inert needsGrant answer actions rfl unjustified⟩

/-- **The retained-refusal check cannot tell a wait from a livelock.** The same reader passes it
in both environments; in one it completes after a grant, in the other it is never observed. -/
theorem retention_does_not_separate :
    RetainsAfterTwoPolls waiting ∧
      (∃ actions : List (Action Unit),
        (actAll grants (poll needsGrant answer) actions waiting).observed ≠ none) ∧
      ∀ actions : List (Action Unit),
        (actAll inert (poll needsGrant answer) actions waiting).observed = none :=
  ⟨two_polls_retain, ⟨[Action.event (), Action.poll], by rw [grant_completes.2]; simp⟩,
    inert_never_completes.2⟩

/-- Counting alone is not the whole repair: it refuses a call that a later grant would allow. -/
theorem counted_refuses_a_justified_wait :
    Justified grants needsGrant waiting.ctx waiting.task ∧
      (pollCounted needsGrant answer waiting).observed = some .refused :=
  ⟨grant_completes.1, rfl⟩

/-- Registration that marks exactly the calls a grant can enable. -/
def registered : Bool → Unit → Bool := fun _ _ => true

/-- The obligated rule keeps the justified wait (it pauses, as the native rule does) and
completes after the grant. -/
theorem obliged_keeps_a_justified_wait :
    pollObliged needsGrant registered answer waiting = poll needsGrant answer waiting ∧
      (actAll grants (pollObliged needsGrant registered answer)
        [Action.event (), Action.poll] waiting).observed = some (.value 42) :=
  ⟨rfl, rfl⟩

/-- In the inert environment nothing can be registered soundly; the obligated rule with no
registration reports the refusal at the first poll. -/
theorem obliged_reports_an_unjustified_refusal :
    (pollObliged needsGrant (fun _ _ => false) answer waiting).observed = some .refused :=
  rfl

end Controls

#print axioms PaidPrefixContinuation.restart_ne_resume_of_paid
#print axioms PaidPrefixControls.context_fork_preserves_paid_prefix
#print axioms PaidPrefixControls.context_restart_duplicates_paid_prefix

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RefusalRetention
