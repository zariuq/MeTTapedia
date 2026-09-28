import Mettapedia.GSLT.LanguageDef.DestinationPassingRefinement

/-!
# Host calls in the shared-continuation machine

A compiled tier runs only the operations of its fragment.  Any other operation
(`collapse`, `superpose`, `case`, a call of a relation the tier does not admit)
becomes a *host call*: the goal, instantiated with the current frame and store,
is served by another evaluator, and its answers resume the tier's continuation
one at a time, in order.  This module adds host calls to the generic machine
`SharedContinuation.Program` without changing it.

**Hosts.**  A `Host` is an ordered answer source: `start` receives a goal and
`pull` asks for the next answer, which is `done` (the goal is exhausted),
`yield a rest` (an answer and the host after it) or `suspend rest` (no answer
yet; the host resumes from `rest` without replaying).  Nothing bounds the
number of pulls: an answer stream may be infinite, and a goal that never
answers again is an unending sequence of suspensions.

**The machine.**  `withHost P goal? H` runs `P`'s controls unchanged
(`Node.run`).  A call that `goal?` classifies as a host call has one
alternative, the host started on its goal (`Node.host`).  A host node is a last
call of its own pull (`HCall.pull`), whose alternatives are the delivered
answer (`Node.answer`) followed by the host that yields the rest.  The frontier
is the one ordered choice stack: an answer resumes the pending return frames
through `P.resume` and its continuation runs before the host is pulled again;
backtracking into the host node is the next pull; an exhausted host leaves no
alternative and the tasks below it continue.  A host call pushes its return
frame once (`expandWith_hostCall`), a host call in last position keeps the
caller's frames (`expandWith_hostTail`), and every other instruction expands as
in `P` (`expandWith_lift`).

**Simulation with stuttering.**  `simulates_step_stutter` and
`simulates_repeats_stutter` generalize `DestinationPassing.simulates_repeats`:
a related task of the first machine is matched through `ExpandsTo`, which lets
the second machine stay, take one expansion, or first pass over finitely many
steps that leave one successor and deliver nothing.  Host suspensions are such
steps.  The step bound `n' ≤ n` of the lock-step theorem is not kept.

**Collections.**  `collect` gathers a host's answers within a number of pulls
and publishes them only when the goal is exhausted; `collectRun` publishes a
run's answers only once its frontier is empty (`collectRun_eq_some`,
`collectRun_eq_none`).

**Correspondence with CeTTa.**  A host call is the tier yielding the goal to
the enclosing machine, which evaluates it as a goal of its own on the same
choice stack and resumes the tier's continuation once per answer, in order.
The host node is that goal's choice point, a pull is backtracking into it,
exhaustion fails the alternative and lets its siblings continue, and a
suspension is an interrupt after which the enclosing machine resumes where it
stopped.  A nested engine held by a host frame has the same interface.  The
model fixes this interface; the enclosing machine's own evaluation is the
host's `pull`.  It is a model, not a verified translation of the C.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostCalls

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## Hosts -/

/-- The result of asking a host for its next answer: the goal is exhausted, an
answer and the host's state after it, or no answer yet and the state from which
the host resumes. -/
inductive Pull (HState Answer : Type) where
  | done
  | yield (answer : Answer) (rest : HState)
  | suspend (rest : HState)

/-- An ordered answer source.  `start` receives a goal; each `pull` delivers the
next answer.  Nothing bounds the number of pulls, so the stream may be infinite,
and `suspend` lets a host stop between answers and resume without replaying. -/
structure Host (Goal HState Answer : Type) where
  start : Goal → HState
  pull : HState → Pull HState Answer

/-- A control of the machine with host calls: a control of the base program, an
answer a host has delivered and whose continuation has not run yet, or a host
state waiting to be pulled. -/
inductive Node (Control HState Answer : Type) where
  | run (control : Control)
  | answer (value : Answer)
  | host (state : HState)

/-- A call of the machine with host calls: a call of the base program, or a pull
of a host state. -/
inductive HCall (Call HState : Type) where
  | base (call : Call)
  | pull (state : HState)

variable {Context Control Call Frame Answer Goal HState : Type}

/-- A base instruction, with its calls as base calls. -/
def liftInstruction : Instruction Call Frame Answer → Instruction (HCall Call HState) Frame Answer
  | .ret a => .ret a
  | .fail => .fail
  | .call c f => .call (.base c) f
  | .tail c => .tail (.base c)

/-- The callee of a call or last call. -/
def calleeOf : Instruction Call Frame Answer → Option Call
  | .call c _ => some c
  | .tail c => some c
  | _ => none

/-- The alternatives a pull leaves on the frontier, in order: the delivered
answer first, then the host that yields the rest. -/
def pullBranches (context : Context) :
    Pull HState Answer → List (Context × Node Control HState Answer)
  | .done => []
  | .yield a rest => [(context, .answer a), (context, .host rest)]
  | .suspend rest => [(context, .host rest)]

/-- **The machine with host calls.**  A call that `goal?` classifies as a host
call has one alternative, the host started on its goal; every other call has the
base program's alternatives.  A host state is a last call of its own pull, whose
alternatives are the delivered answer and the host that yields the remaining
answers; an answer returns to the pending frames like any return. -/
def withHost (P : Program Context Control Call Frame Answer) (goal? : Call → Option Goal)
    (H : Host Goal HState Answer) :
    Program Context (Node Control HState Answer) (HCall Call HState) Frame Answer where
  inspect
    | .run c => liftInstruction (P.inspect c)
    | .answer a => .ret a
    | .host h => .tail (.pull h)
  branches context
    | .base c =>
        match goal? c with
        | some g => [(context, .host (H.start g))]
        | none => (P.branches context c).map fun next => (next.1, .run next.2)
    | .pull h => pullBranches context (H.pull h)
  resume context f a := ((P.resume context f a).1, .run (P.resume context f a).2)

/-- A base task, running in the machine with host calls. -/
def liftTask (t : Task Context Control Frame) : Task Context (Node Control HState Answer) Frame :=
  ⟨t.context, .run t.control, t.returns⟩

/-- A base state, running in the machine with host calls. -/
def liftState (s : State Context Control Frame Answer) :
    State Context (Node Control HState Answer) Frame Answer :=
  ⟨s.frontier.map liftTask, s.emitted⟩

/-! ## Expansion -/

section Expansion

variable (P : Program Context Control Call Frame Answer) (goal? : Call → Option Goal)
  (H : Host Goal HState Answer)

theorem expand_run (t : Task Context Control Frame) :
    expand (withHost P goal? H) (liftTask t) =
      expandWith (withHost P goal? H) t.context t.returns (liftInstruction (P.inspect t.control)) :=
  rfl

/-- An instruction that calls no host expands as in the base program. -/
theorem expandWith_lift (context : Context) (returns : List Frame)
    (i : Instruction Call Frame Answer) (base : ∀ c, calleeOf i = some c → goal? c = none) :
    expandWith (withHost P goal? H) context returns (liftInstruction i) =
      ((expandWith P context returns i).1.map (liftTask (HState := HState) (Answer := Answer)),
        (expandWith P context returns i).2) := by
  cases i with
  | ret value =>
      cases returns <;> rfl
  | fail => rfl
  | call c f =>
      have miss := base c rfl
      simp [expandWith, liftInstruction, withHost, miss, liftTask, Function.comp_def]
  | tail c =>
      have miss := base c rfl
      simp [expandWith, liftInstruction, withHost, miss, liftTask, Function.comp_def]

/-- A host call pushes its return frame once and starts the host. -/
theorem expandWith_hostCall (context : Context) (returns : List Frame) (c : Call) (f : Frame)
    {g : Goal} (hit : goal? c = some g) :
    expandWith (withHost P goal? H) context returns (liftInstruction (.call c f)) =
      ([⟨context, .host (H.start g), f :: returns⟩], []) := by
  simp [expandWith, liftInstruction, withHost, hit]

/-- A host call in last position starts the host on the caller's frames. -/
theorem expandWith_hostTail (context : Context) (returns : List Frame) (c : Call)
    {g : Goal} (hit : goal? c = some g) :
    expandWith (withHost P goal? H) context returns (liftInstruction (.tail c)) =
      ([⟨context, .host (H.start g), returns⟩], []) := by
  simp [expandWith, liftInstruction, withHost, hit]

/-- A host state expands to the alternatives of one pull, on the same frames. -/
theorem expand_host (context : Context) (returns : List Frame) (h : HState) :
    expand (withHost P goal? H) ⟨context, .host h, returns⟩ =
      ((pullBranches context (H.pull h)).map fun next => ⟨next.1, next.2, returns⟩, []) :=
  rfl

/-- A delivered answer returns to its frames as in the base program. -/
theorem expand_answer (context : Context) (returns : List Frame) (a : Answer) :
    expand (withHost P goal? H) ⟨context, .answer a, returns⟩ =
      ((expandWith P context returns (.ret a)).1.map (liftTask (HState := HState) (Answer := Answer)),
        (expandWith P context returns (.ret a)).2) :=
  expandWith_lift P goal? H context returns (.ret a) (fun _ none => by cases none)

end Expansion

/-! ## Simulation with stuttering -/

theorem Embeds.map {α β α' β' : Type} {R : α → β → Prop} {D : α → Prop}
    {R' : α' → β' → Prop} {D' : α' → Prop} (f : α → α') (g : β → β')
    (hR : ∀ a b, R a b → R' (f a) (g b)) (hD : ∀ a, D a → D' (f a)) :
    ∀ {as : List α} {bs : List β}, Embeds R D as bs → Embeds R' D' (as.map f) (bs.map g)
  | _, _, .nil => .nil
  | _, _, .keep r rest => .keep (hR _ _ r) (Embeds.map f g hR hD rest)
  | _, _, .drop d rest => .drop (hD _ d) (Embeds.map f g hR hD rest)

section Stutter

variable {C K Call' F A : Type}

/-- `ExpandsTo P t ts as`: running the task `t` at the head of the frontier for
some number of steps replaces it by `ts` and delivers `as`: no step (`stay`), one
expansion (`one`), or a step that leaves one successor and no answer before
continuing (`stutter`). -/
inductive ExpandsTo (P : Program C K Call' F A) :
    Task C K F → List (Task C K F) → List (C × A) → Prop
  | stay (t : Task C K F) : ExpandsTo P t [t] []
  | one (t : Task C K F) : ExpandsTo P t (expand P t).1 (expand P t).2
  | stutter {t t' : Task C K F} {ts : List (Task C K F)} {as : List (C × A)} :
      expand P t = ([t'], []) → ExpandsTo P t' ts as → ExpandsTo P t ts as

theorem ExpandsTo.run {P : Program C K Call' F A} {t : Task C K F} {ts : List (Task C K F)}
    {as : List (C × A)} (h : ExpandsTo P t ts as) :
    ∃ k, ∀ rest emitted, repeats (step P) k ⟨t :: rest, emitted⟩ = ⟨ts ++ rest, emitted ++ as⟩ := by
  induction h with
  | stay t => exact ⟨0, fun rest emitted => by simp [repeats]⟩
  | one t => exact ⟨1, fun rest emitted => by simp [repeats, step_cons]⟩
  | @stutter t t' ts as expanded _ ih =>
      obtain ⟨k, run⟩ := ih
      refine ⟨k + 1, fun rest emitted => ?_⟩
      simp only [repeats, step_cons, expanded, List.singleton_append, List.append_nil]
      exact run rest emitted

variable {C₁ K₁ Call₁ F₁ A₁ C₂ K₂ Call₂ F₂ A₂ : Type}

/-- One step of the first machine is matched by finitely many steps of the
second: a related task by the steps of `ExpandsTo`, a removed task by none. -/
theorem simulates_step_stutter (P₁ : Program C₁ K₁ Call₁ F₁ A₁) (P₂ : Program C₂ K₂ Call₂ F₂ A₂)
    {R : Task C₁ K₁ F₁ → Task C₂ K₂ F₂ → Prop} {D : Task C₁ K₁ F₁ → Prop}
    {Same : C₁ × A₁ → C₂ × A₂ → Prop} (M : Task C₁ K₁ F₁ → Prop)
    (related : ∀ a b, R a b → M a → ∃ ts as, ExpandsTo P₂ b ts as ∧
      Embeds R D (expand P₁ a).1 ts ∧ List.Forall₂ Same (expand P₁ a).2 as)
    (doomed : ∀ a, D a → (∀ a' ∈ (expand P₁ a).1, D a') ∧ (expand P₁ a).2 = [])
    {s₁ : State C₁ K₁ F₁ A₁} {s₂ : State C₂ K₂ F₂ A₂} (sim : Simulates R D Same s₁ s₂)
    (moded : ∀ a ∈ s₁.frontier, M a) :
    ∃ k, Simulates R D Same (step P₁ s₁) (repeats (step P₂) k s₂) := by
  obtain ⟨embeds, answers⟩ := sim
  rcases s₁ with ⟨frontier₁, emitted₁⟩
  rcases s₂ with ⟨frontier₂, emitted₂⟩
  cases embeds with
  | nil => exact ⟨0, .nil, answers⟩
  | @keep a b rest₁ rest₂ r rest =>
      obtain ⟨ts, as, expands, tasks, delivered⟩ := related a b r (moded a List.mem_cons_self)
      obtain ⟨k, run⟩ := expands.run
      refine ⟨k, ?_⟩
      rw [step_cons, run]
      exact ⟨tasks.append rest, List.rel_append answers delivered⟩
  | @drop a rest₁ _ d rest =>
      obtain ⟨all, none⟩ := doomed a d
      refine ⟨0, ?_⟩
      rw [step_cons]
      refine ⟨Embeds.prepend all rest, ?_⟩
      simpa [repeats, none] using answers

/-- **Simulation of runs with stuttering.**  After `n` steps of the first
machine, the second has taken some number of steps and the states still
correspond. -/
theorem simulates_repeats_stutter (P₁ : Program C₁ K₁ Call₁ F₁ A₁)
    (P₂ : Program C₂ K₂ Call₂ F₂ A₂)
    {R : Task C₁ K₁ F₁ → Task C₂ K₂ F₂ → Prop} {D : Task C₁ K₁ F₁ → Prop}
    {Same : C₁ × A₁ → C₂ × A₂ → Prop} (M : Task C₁ K₁ F₁ → Prop)
    (related : ∀ a b, R a b → M a → ∃ ts as, ExpandsTo P₂ b ts as ∧
      Embeds R D (expand P₁ a).1 ts ∧ List.Forall₂ Same (expand P₁ a).2 as)
    (doomed : ∀ a, D a → (∀ a' ∈ (expand P₁ a).1, D a') ∧ (expand P₁ a).2 = []) :
    ∀ (n : ℕ) (s₁ : State C₁ K₁ F₁ A₁) (s₂ : State C₂ K₂ F₂ A₂), Simulates R D Same s₁ s₂ →
      (∀ m < n, ∀ a ∈ (repeats (step P₁) m s₁).frontier, M a) →
      ∃ n', Simulates R D Same (repeats (step P₁) n s₁) (repeats (step P₂) n' s₂)
  | 0, _, _, sim, _ => ⟨0, sim⟩
  | n + 1, s₁, s₂, sim, moded => by
      have later : ∀ m < n, ∀ a ∈ (repeats (step P₁) m (step P₁ s₁)).frontier, M a :=
        fun m below => moded (m + 1) (by omega)
      obtain ⟨k, sim'⟩ := simulates_step_stutter P₁ P₂ M related doomed sim
        (moded 0 (Nat.succ_pos n))
      obtain ⟨n', sim''⟩ :=
        simulates_repeats_stutter P₁ P₂ M related doomed n _ _ sim' later
      refine ⟨k + n', ?_⟩
      rw [Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats_add (step P₂) k n' s₂]
      exact sim''

end Stutter

/-! ## Collections -/

/-- The collection of a host's answers within `fuel` pulls, in order.  It is
published only when the goal is exhausted; `none` means the fuel ran out first,
not that the goal has no answer. -/
def collect (pull : HState → Pull HState Answer) : ℕ → HState → Option (List Answer)
  | 0, _ => none
  | n + 1, h =>
      match pull h with
      | .done => some []
      | .yield a h' => (collect pull n h').map (a :: ·)
      | .suspend h' => collect pull n h'

/-- The collection of a run's answers after `n` steps, published only when its
frontier is exhausted. -/
def collectRun {C K Call' F A : Type} (P : Program C K Call' F A) (n : ℕ) (s : State C K F A) :
    Option (List (C × A)) :=
  match (repeats (step P) n s).frontier with
  | [] => some (repeats (step P) n s).emitted
  | _ :: _ => none

theorem collectRun_eq_some {C K Call' F A : Type} {P : Program C K Call' F A} {n : ℕ}
    {s : State C K F A} {as : List (C × A)} :
    collectRun P n s = some as ↔
      (repeats (step P) n s).frontier = [] ∧ (repeats (step P) n s).emitted = as := by
  unfold collectRun
  split <;> simp_all

/-- No collection is published while the run has not exhausted its frontier. -/
theorem collectRun_eq_none {C K Call' F A : Type} {P : Program C K Call' F A} {n : ℕ}
    {s : State C K F A} : collectRun P n s = none ↔ (repeats (step P) n s).frontier ≠ [] := by
  unfold collectRun
  split <;> simp_all

end Mettapedia.GSLT.LanguageDef.HostCalls
