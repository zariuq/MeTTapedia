import Mettapedia.GSLT.LanguageDef.HostGoalMachine

/-!
# Cut scopes and host goals

**The machine with cut** (`CProgram`, `cstep`).  The shared-continuation machine with a cut
instruction and cut scopes.  Every task carries its scope: the number of frontier tasks below its
activation's alternatives, or `none` outside every activation.  `call` and `tail` begin an
activation, whose alternatives are scoped at the tasks below them (`cstep_call`); `enter` runs code
of the running activation in its scope, as an expression of an equation's body does; a return frame
keeps the caller's scope (`cstep_resume`).  A cut keeps the tasks below its scope and continues.
Every frontier the machine reaches from a well-scoped one is well scoped (`WellScoped.repeats`),
and without cut the machine is the shared-continuation machine (`cstep_ofProgram`).

**(a) Cut scope** (`cstep_cut`).  A cut run inside an activation drops exactly the choices made
since the activation began and the activation's untried alternatives; the tasks below, the caller's
alternatives and everything under them, stay as they were.  Outside every activation a cut drops
every other task (`cstep_cut_outside`).

**(b) A host goal with no cut keeps to its own segment.**  In the machine with host goals
(`withHostCut`), an `enter` of a host goal starts a host node, and a pull keeps every task below the
node (`cstep_host_yield`, `cstep_host_suspend`, `cstep_host_done`).  The host `cutHost P` runs the
goal on its own frontier, where a cut would prune only that frontier.  In the inline run, where the
goal runs as code of the activation that entered it, a goal whose own code has no cut (`OwnLevel`)
leaves the enclosing activation's alternatives and everything below them as they were: step by
step (`inline_goal_step`), and until its own run delivers an answer or is exhausted
(`inline_goal_segment`).  Cuts in the relations it calls act inside its segment.

**(c) The composition** (`hosted_answers_cut`, `inline_answers_cut`, `hosted_terminates_cut`,
`inline_terminates_cut`).  Take a program whose host goals have no cut in their own code
(`GoalsOwn`), whatever cuts the rest of it makes, before a host goal, after one, or in the
relations a goal calls.  Every answer list the inline run delivers, the machine with host goals
delivers; every answer list the machine with host goals delivers, the inline run delivers within at
most as many steps; and each run is exhausted when the other is, with the same answers.  The proof
is a simulation in both directions (`FRel`): a host node stands for its host's frontier lifted onto
the inline tasks below it, with the goal's own code in the scope of the code that entered it.

**Controls** (checked by `decide`).  `cut_scope_runs`: `(outer)` calls `(cutFirst)`, whose first
equation cuts; `(cutFirst)`'s second equation goes and `(outer)`'s stays, so the run delivers `0`
and then `5`.  `plain_runs`, `cutAfter_runs`: a host goal with no cut, and a cut of the enclosing
code on the goal's first answer, give the same answers inline and hosted; `cutAfter_answers` is the
composition instantiated.  **Delegating a cut** (`delegated_cut_runs`): a goal that cuts, handed to
the host, prunes only the host's frontier, so the enclosing equation's alternative that the inline
run cuts stays, and the hosted run delivers `2`, which the inline run does not.
`withCut_not_own`: that goal is outside the hypothesis of the composition.

**The C.**  The tier declines every equation whose host goal contains a cut or a `return` anywhere
in its expression, so the enclosing machine keeps the equation and its cut acts there.  `GoalsOwn`
is that condition on the goal's own code.  The tier has no cut step: a tier that ran cuts would have
to meet `cstep_cut`.

**Not covered.**  `return` is not modelled.  The host is the machine itself, on the goal's own
frontier (`cutHost`), and the two runs deliver the same answer lists.  Neither the composition with
the enclosing machine as a host meeting `HostCorrect` nor the output-first refinement, with its
omitted answers, is extended to cut here.  The output-first extension needs a further condition:
the output-first machine meets an equation's exposed output with the destination when it activates
the equation, before the body runs.  If a cut could come before that output, an equation that would
cut and then fail at its return would never run, and its cut would never drop the alternatives the
reference drops.  The exposed output must stop at a cut.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostGoals.Scopes

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.LanguageDef.HostCalls
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## The machine with cut -/

/-- An instruction of the machine with cut.  `call` and `tail` begin a new activation, with its
own cut scope; `enter` runs code of the running activation, in its scope, as an expression of an
equation's body does; `cut` drops the choices of the running activation and continues with
`next`. -/
inductive CInstruction (Call Frame Answer Control : Type) where
  | ret (value : Answer)
  | fail
  | call (callee : Call) (frame : Frame)
  | tail (callee : Call)
  | enter (callee : Call) (frame : Frame)
  | cut (next : Control)

/-- A program of the machine with cut, as `SharedContinuation.Program` with the instructions of
`CInstruction`. -/
structure CProgram (Context Control Call Frame Answer : Type) where
  inspect : Control → CInstruction Call Frame Answer Control
  branches : Context → Call → List (Context × Control)
  resume : Context → Frame → Answer → Context × Control

/-- A task of the machine with cut.  Its `scope` is the number of frontier tasks below the
alternatives of the activation its code belongs to, or `none` for code outside every activation
(a query's own code, or a host goal's own code in its host).  A return frame keeps the scope of
the code it resumes. -/
structure CTask (Context Control Frame : Type) where
  context : Context
  control : Control
  returns : List (Frame × Option ℕ)
  scope : Option ℕ

/-- A state of the machine with cut: the ordered frontier and the answers delivered. -/
structure CState (Context Control Frame Answer : Type) where
  frontier : List (CTask Context Control Frame)
  emitted : List (Context × Answer)

/-- The tasks a cut keeps below it: those below its activation's alternatives. -/
def keepBelow {α : Type} : Option ℕ → List α → List α
  | none, _ => []
  | some n, rest => rest.drop (rest.length - n)

variable {C K Call F A : Type}

/-- One task's expansion above the tasks `rest`: the frontier it leaves and the answers it
delivers.  A call or last call scopes its callee's alternatives at `rest`; `enter` keeps the
running scope; a cut keeps only the tasks below its scope. -/
def cexpand (P : CProgram C K Call F A) (t : CTask C K F) (rest : List (CTask C K F)) :
    List (CTask C K F) × List (C × A) :=
  match P.inspect t.control with
  | .ret value =>
      match t.returns with
      | [] => (rest, [(t.context, value)])
      | (frame, scope) :: pending =>
          (⟨(P.resume t.context frame value).1, (P.resume t.context frame value).2, pending,
            scope⟩ :: rest, [])
  | .fail => (rest, [])
  | .call callee frame =>
      ((P.branches t.context callee).map (fun next =>
        ⟨next.1, next.2, (frame, t.scope) :: t.returns, some rest.length⟩) ++ rest, [])
  | .tail callee =>
      ((P.branches t.context callee).map (fun next =>
        ⟨next.1, next.2, t.returns, some rest.length⟩) ++ rest, [])
  | .enter callee frame =>
      ((P.branches t.context callee).map (fun next =>
        ⟨next.1, next.2, (frame, t.scope) :: t.returns, t.scope⟩) ++ rest, [])
  | .cut next => (⟨t.context, next, t.returns, t.scope⟩ :: keepBelow t.scope rest, [])

/-- One step of the machine with cut: the first task expands. -/
def cstep (P : CProgram C K Call F A) (s : CState C K F A) : CState C K F A :=
  match s.frontier with
  | [] => s
  | t :: rest => ⟨(cexpand P t rest).1, s.emitted ++ (cexpand P t rest).2⟩

theorem cstep_cons (P : CProgram C K Call F A) (t : CTask C K F) (rest : List (CTask C K F))
    (emitted : List (C × A)) :
    cstep P ⟨t :: rest, emitted⟩ = ⟨(cexpand P t rest).1, emitted ++ (cexpand P t rest).2⟩ :=
  rfl

theorem cstep_nil (P : CProgram C K Call F A) (emitted : List (C × A)) :
    cstep P ⟨[], emitted⟩ = ⟨[], emitted⟩ :=
  rfl

/-- A run delivers its answers after those delivered before it. -/
theorem crepeats_emitted (P : CProgram C K Call F A) :
    ∀ (k : ℕ) (frontier : List (CTask C K F)) (emitted : List (C × A)),
      repeats (cstep P) k ⟨frontier, emitted⟩ =
        ⟨(repeats (cstep P) k ⟨frontier, []⟩).frontier,
          emitted ++ (repeats (cstep P) k ⟨frontier, []⟩).emitted⟩
  | 0, _, _ => by simp [repeats]
  | k + 1, [], emitted => by
    show repeats (cstep P) k (cstep P ⟨[], emitted⟩) =
      ⟨(repeats (cstep P) k (cstep P ⟨[], []⟩)).frontier,
        emitted ++ (repeats (cstep P) k (cstep P ⟨[], []⟩)).emitted⟩
    rw [cstep_nil, cstep_nil]
    exact crepeats_emitted P k [] emitted
  | k + 1, t :: rest, emitted => by
    show repeats (cstep P) k (cstep P ⟨t :: rest, emitted⟩) =
      ⟨(repeats (cstep P) k (cstep P ⟨t :: rest, []⟩)).frontier,
        emitted ++ (repeats (cstep P) k (cstep P ⟨t :: rest, []⟩)).emitted⟩
    rw [cstep_cons, cstep_cons, crepeats_emitted P k _ (emitted ++ _),
      crepeats_emitted P k _ ([] ++ _)]
    simp

theorem keepBelow_append {α : Type} (above below : List α) :
    keepBelow (some below.length) (above ++ below) = below := by
  simp only [keepBelow, List.length_append, Nat.add_sub_cancel]
  exact List.drop_left

/-! ## Cut scope -/

/-- A call leaves its callee's alternatives above the tasks below it, scoped at those tasks: they
begin a new activation. -/
theorem cstep_call (P : CProgram C K Call F A) {t : CTask C K F} {callee : Call} {frame : F}
    (calling : P.inspect t.control = .call callee frame) (rest : List (CTask C K F))
    (emitted : List (C × A)) :
    cstep P ⟨t :: rest, emitted⟩ =
      ⟨(P.branches t.context callee).map (fun next =>
          ⟨next.1, next.2, (frame, t.scope) :: t.returns, some rest.length⟩) ++ rest, emitted⟩ := by
  simp [cstep, cexpand, calling]

/-- A return resumes the caller's code in the caller's scope, which its frame kept. -/
theorem cstep_resume (P : CProgram C K Call F A) {t : CTask C K F} {value : A} {frame : F}
    {scope : Option ℕ} {pending : List (F × Option ℕ)} (returning : P.inspect t.control = .ret value)
    (frames : t.returns = (frame, scope) :: pending) (rest : List (CTask C K F))
    (emitted : List (C × A)) :
    cstep P ⟨t :: rest, emitted⟩ =
      ⟨⟨(P.resume t.context frame value).1, (P.resume t.context frame value).2, pending, scope⟩ ::
        rest, emitted⟩ := by
  simp [cstep, cexpand, returning, frames]

/-- **A cut drops exactly the choices of its activation.**  A task whose scope counts the tasks
`below`, above the choices `made` since its activation began and the activation's untried
alternatives `untried`, cuts to its continuation directly over `below`: every task of `made` and
`untried` goes, and `below`, the caller's alternatives and everything under them, stays as it
was. -/
theorem cstep_cut (P : CProgram C K Call F A) {t : CTask C K F} {next : K}
    (cutting : P.inspect t.control = .cut next) (made untried below : List (CTask C K F))
    (wellScoped : t.scope = some below.length) (emitted : List (C × A)) :
    cstep P ⟨t :: (made ++ untried ++ below), emitted⟩ =
      ⟨⟨t.context, next, t.returns, t.scope⟩ :: below, emitted⟩ := by
  simp only [cstep, cexpand, cutting, wellScoped, List.append_nil]
  rw [keepBelow_append]

/-- A cut outside every activation, a query's own, drops every other task. -/
theorem cstep_cut_outside (P : CProgram C K Call F A) {t : CTask C K F} {next : K}
    (cutting : P.inspect t.control = .cut next) (rest : List (CTask C K F))
    (outside : t.scope = none) (emitted : List (C × A)) :
    cstep P ⟨t :: rest, emitted⟩ = ⟨[⟨t.context, next, t.returns, t.scope⟩], emitted⟩ := by
  simp [cstep, cexpand, cutting, outside, keepBelow]

/-! ## Well-scoped frontiers -/

/-- A scope fits below `n` tasks. -/
def Fits (scope : Option ℕ) (n : ℕ) : Prop := ∀ k, scope = some k → k ≤ n

/-- `outer` is the scope of an activation at or around `inner`'s. -/
def Outer (outer inner : Option ℕ) : Prop := ∀ k, outer = some k → ∃ k', inner = some k' ∧ k ≤ k'

theorem Outer.refl (scope : Option ℕ) : Outer scope scope := fun k eq => ⟨k, eq, Nat.le_refl k⟩

theorem Outer.trans {a b c : Option ℕ} (first : Outer a b) (second : Outer b c) : Outer a c := by
  intro k eq
  obtain ⟨k', eq', le⟩ := first k eq
  obtain ⟨k'', eq'', le'⟩ := second k' eq'
  exact ⟨k'', eq'', Nat.le_trans le le'⟩

theorem Fits.mono {scope : Option ℕ} {n m : ℕ} (fits : Fits scope n) (le : n ≤ m) :
    Fits scope m := fun k eq => Nat.le_trans (fits k eq) le

theorem Fits.outer {outer inner : Option ℕ} {n : ℕ} (around : Outer outer inner)
    (fits : Fits inner n) : Fits outer n := by
  intro k eq
  obtain ⟨k', eq', le⟩ := around k eq
  exact Nat.le_trans le (fits k' eq')

theorem Outer.of_fits {scope : Option ℕ} {n : ℕ} (fits : Fits scope n) :
    Outer scope (some n) := fun k eq => ⟨n, rfl, fits k eq⟩

/-- Return frames nest outward: each frame's scope is at or around the scope of the code above
it, starting from the running code's. -/
inductive Nested {F : Type} : Option ℕ → List (F × Option ℕ) → Prop
  | nil (scope : Option ℕ) : Nested scope []
  | cons {scope outer : Option ℕ} {frame : F} {rest : List (F × Option ℕ)} :
      Outer outer scope → Nested outer rest → Nested scope ((frame, outer) :: rest)

theorem Nested.widen {F : Type} {scope scope' : Option ℕ} {frames : List (F × Option ℕ)}
    (around : Outer scope scope') (nested : Nested scope frames) : Nested scope' frames := by
  cases nested with
  | nil => exact .nil _
  | cons outer rest => exact .cons (outer.trans around) rest

/-- Every task's scope fits the tasks below it, and its return frames nest outward from it. -/
inductive WellScoped {C K F : Type} : List (CTask C K F) → Prop
  | nil : WellScoped []
  | cons {t : CTask C K F} {rest : List (CTask C K F)} :
      Fits t.scope rest.length → Nested t.scope t.returns → WellScoped rest →
      WellScoped (t :: rest)

theorem WellScoped.drop {tasks : List (CTask C K F)} (wellScoped : WellScoped tasks) :
    ∀ n, WellScoped (tasks.drop n) := by
  induction wellScoped with
  | nil => intro n; simp [WellScoped.nil]
  | cons fits nested rest ih =>
    intro n
    cases n with
    | zero => exact .cons fits nested rest
    | succ n => exact ih n

theorem WellScoped.keepBelow {tasks : List (CTask C K F)} (wellScoped : WellScoped tasks)
    (scope : Option ℕ) : WellScoped (Scopes.keepBelow scope tasks) := by
  cases scope with
  | none => exact .nil
  | some n => exact wellScoped.drop _

theorem fits_keepBelow {α : Type} {scope : Option ℕ} {rest : List α} (fits : Fits scope rest.length) :
    Fits scope (keepBelow scope rest).length := by
  intro k eq
  subst eq
  have := fits k rfl
  simp only [keepBelow, List.length_drop]
  omega

/-- New tasks above `rest`, each fitting `rest` and nesting its frames. -/
theorem WellScoped.append {new rest : List (CTask C K F)}
    (each : ∀ t ∈ new, Fits t.scope rest.length ∧ Nested t.scope t.returns)
    (wellScoped : WellScoped rest) : WellScoped (new ++ rest) := by
  induction new with
  | nil => exact wellScoped
  | cons t new ih =>
    obtain ⟨fits, nested⟩ := each t List.mem_cons_self
    refine .cons (fits.mono (by simp)) nested (ih fun t' member => each t' (List.mem_cons_of_mem _ member))

/-- **Scopes stay well formed.**  A step of the machine with cut keeps every scope pointing into
the frontier below it. -/
theorem WellScoped.cexpand (P : CProgram C K Call F A) {t : CTask C K F} {rest : List (CTask C K F)}
    (wellScoped : WellScoped (t :: rest)) : WellScoped (Scopes.cexpand P t rest).1 := by
  cases wellScoped with
  | cons fits nested below =>
  unfold Scopes.cexpand
  split
  · split
    · exact below
    · rename_i frame scope pending frames
      rw [frames] at nested
      cases nested with
      | cons around rest' =>
        exact .cons (fits.outer around) rest' below
  · exact below
  · refine WellScoped.append (fun t' member => ?_) below
    simp only [List.mem_map] at member
    obtain ⟨next, _, rfl⟩ := member
    exact ⟨fun k eq => by cases eq; exact Nat.le_refl _, .cons (Outer.of_fits fits) nested⟩
  · refine WellScoped.append (fun t' member => ?_) below
    simp only [List.mem_map] at member
    obtain ⟨next, _, rfl⟩ := member
    exact ⟨fun k eq => by cases eq; exact Nat.le_refl _, nested.widen (Outer.of_fits fits)⟩
  · refine WellScoped.append (fun t' member => ?_) below
    simp only [List.mem_map] at member
    obtain ⟨next, _, rfl⟩ := member
    exact ⟨fits, .cons (Outer.refl _) nested⟩
  · exact .cons (fits_keepBelow fits) nested (below.keepBelow _)

theorem WellScoped.cstep (P : CProgram C K Call F A) {s : CState C K F A}
    (wellScoped : WellScoped s.frontier) : WellScoped (Scopes.cstep P s).frontier := by
  rcases s with ⟨frontier, emitted⟩
  cases frontier with
  | nil => exact wellScoped
  | cons t rest => exact wellScoped.cexpand P

theorem WellScoped.repeats (P : CProgram C K Call F A) :
    ∀ (n : ℕ) {s : CState C K F A}, WellScoped s.frontier →
      WellScoped (repeats (Scopes.cstep P) n s).frontier
  | 0, _, wellScoped => wellScoped
  | n + 1, _, wellScoped => WellScoped.repeats P n (wellScoped.cstep P)

/-! ## Without cut, the machine is the shared-continuation machine -/

/-- A base instruction as an instruction of the machine with cut. -/
def CInstruction.ofInstruction : Instruction Call F A → CInstruction Call F A K
  | .ret value => .ret value
  | .fail => .fail
  | .call callee frame => .call callee frame
  | .tail callee => .tail callee

/-- A program of the shared-continuation machine, run by the machine with cut. -/
def CProgram.ofProgram (P : Program C K Call F A) : CProgram C K Call F A :=
  ⟨fun control => .ofInstruction (P.inspect control), P.branches, P.resume⟩

/-- A task with its scopes forgotten. -/
def CTask.forget (t : CTask C K F) : Task C K F := ⟨t.context, t.control, t.returns.map Prod.fst⟩

/-- A state with its scopes forgotten. -/
def CState.forget (s : CState C K F A) : State C K F A := ⟨s.frontier.map CTask.forget, s.emitted⟩

/-- **A conservative extension.**  On a program with neither `enter` nor `cut`, a step of the
machine with cut is a step of the shared-continuation machine, scopes forgotten. -/
theorem cstep_ofProgram (P : Program C K Call F A) (s : CState C K F A) :
    (cstep (CProgram.ofProgram P) s).forget = step P s.forget := by
  rcases s with ⟨frontier, emitted⟩
  cases frontier with
  | nil => rfl
  | cons t rest =>
    simp only [cstep, cexpand, CState.forget, List.map_cons, step, CTask.forget]
    cases inspect : P.inspect t.control with
    | ret value =>
      simp only [CProgram.ofProgram, inspect, CInstruction.ofInstruction]
      cases t.returns with
      | nil => simp
      | cons head pending => obtain ⟨frame, scope⟩ := head; simp [CTask.forget]
    | fail => simp [CProgram.ofProgram, inspect, CInstruction.ofInstruction]
    | call callee frame =>
      simp [CProgram.ofProgram, inspect, CInstruction.ofInstruction, Function.comp_def, CTask.forget]
    | tail callee =>
      simp [CProgram.ofProgram, inspect, CInstruction.ofInstruction, Function.comp_def, CTask.forget]

/-! ## Host goals in the machine with cut -/

/-- A call of the machine with cut and host goals: a call or last call of the base program, an
`enter` of the base program, which may be a host goal, or a pull of a host state. -/
inductive SCall (Call HState : Type) where
  | base (callee : Call)
  | goal (callee : Call)
  | pull (state : HState)

/-- A base instruction, running in the machine with host goals. -/
def liftInstr {HState : Type} :
    CInstruction Call F A K → CInstruction (SCall Call HState) F A (Node K HState A)
  | .ret value => .ret value
  | .fail => .fail
  | .call callee frame => .call (.base callee) frame
  | .tail callee => .tail (.base callee)
  | .enter callee frame => .enter (.goal callee) frame
  | .cut next => .cut (.run next)

/-- The alternatives a pull leaves on the frontier: the answer, in the context of the goal's code
that delivered it, then the host that yields the rest. -/
def scopedPullBranches {HState : Type} (context : C) :
    Pull HState (C × A) → List (C × Node K HState A)
  | .done => []
  | .yield answer rest => [(answer.1, .answer answer.2), (context, .host rest)]
  | .suspend rest => [(context, .host rest)]

/-- **The machine with cut and host goals.**  An `enter` of a host goal has one alternative, the
host node started on the goal, its context and callee; any other call has the base program's
alternatives.  A host node is a last call of its own pull.  An answer returns to the frames above
the host node, in the context of the goal's code that delivered it. -/
def withHostCut (P : CProgram C K Call F A) (isHost : Call → Bool) {HState : Type}
    (H : Host (C × Call) HState (C × A)) :
    CProgram C (Node K HState A) (SCall Call HState) F A where
  inspect
    | .run control => liftInstr (P.inspect control)
    | .answer value => .ret value
    | .host state => .tail (.pull state)
  branches context
    | .base callee => (P.branches context callee).map fun next => (next.1, .run next.2)
    | .goal callee =>
        if isHost callee then [(context, .host (H.start (context, callee)))]
        else (P.branches context callee).map fun next => (next.1, .run next.2)
    | .pull state => scopedPullBranches context (H.pull state)
  resume context frame value :=
    ((P.resume context frame value).1, .run (P.resume context frame value).2)

/-- One step of a host running `P` on its own frontier: it yields the answer the step delivers,
suspends when it delivers none, and is exhausted when the frontier is. -/
def cpull (P : CProgram C K Call F A) : List (CTask C K F) → Pull (List (CTask C K F)) (C × A)
  | [] => .done
  | t :: rest =>
      match (cexpand P t rest).2 with
      | [] => .suspend (cexpand P t rest).1
      | answer :: _ => .yield answer (cexpand P t rest).1

/-- A goal's tasks in its host: its alternatives, with no return frame and outside every
activation of the host's frontier. -/
def goalTasks (P : CProgram C K Call F A) (goal : C × Call) : List (CTask C K F) :=
  (P.branches goal.1 goal.2).map fun next => ⟨next.1, next.2, [], none⟩

/-- **The host of a goal**: `P` running the goal's alternatives on the host's own frontier, one
step per pull.  A cut of the goal's own code prunes only that frontier. -/
def cutHost (P : CProgram C K Call F A) : Host (C × Call) (List (CTask C K F)) (C × A) :=
  ⟨goalTasks P, cpull P⟩

/-- The machine with cut whose host goals `cutHost P` evaluates. -/
abbrev hostedCut (P : CProgram C K Call F A) (isHost : Call → Bool) :=
  withHostCut P isHost (cutHost P)

/-- A step delivers at most one answer, and a step that delivers one leaves the tasks below. -/
theorem cexpand_delivers (P : CProgram C K Call F A) (t : CTask C K F) (rest : List (CTask C K F)) :
    (cexpand P t rest).2 = [] ∨ ∃ answer, cexpand P t rest = (rest, [answer]) := by
  unfold cexpand
  split
  · split
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl
  all_goals exact .inl rfl

/-! ## A host node keeps the tasks below it -/

section HostNode

variable (P : CProgram C K Call F A) (isHost : Call → Bool) {HState : Type}
  (H : Host (C × Call) HState (C × A))

/-- A pull that yields puts the answer, in its goal's context, above the host node, which waits
for the next pull; the tasks below are unchanged. -/
theorem cstep_host_yield (context : C) {h h' : HState} {answer : C × A}
    (returns : List (F × Option ℕ)) (scope : Option ℕ)
    (rest : List (CTask C (Node K HState A) F)) (emitted : List (C × A))
    (pulled : H.pull h = .yield answer h') :
    cstep (withHostCut P isHost H) ⟨⟨context, .host h, returns, scope⟩ :: rest, emitted⟩ =
      ⟨⟨answer.1, .answer answer.2, returns, some rest.length⟩ ::
        ⟨context, .host h', returns, some rest.length⟩ :: rest, emitted⟩ := by
  simp [cstep, cexpand, withHostCut, pulled, scopedPullBranches]

/-- A suspension leaves the host node in place; the tasks below are unchanged. -/
theorem cstep_host_suspend (context : C) {h h' : HState} (returns : List (F × Option ℕ))
    (scope : Option ℕ) (rest : List (CTask C (Node K HState A) F)) (emitted : List (C × A))
    (pulled : H.pull h = .suspend h') :
    cstep (withHostCut P isHost H) ⟨⟨context, .host h, returns, scope⟩ :: rest, emitted⟩ =
      ⟨⟨context, .host h', returns, some rest.length⟩ :: rest, emitted⟩ := by
  simp [cstep, cexpand, withHostCut, pulled, scopedPullBranches]

/-- An exhausted goal leaves nothing; the tasks below continue. -/
theorem cstep_host_done (context : C) {h : HState} (returns : List (F × Option ℕ))
    (scope : Option ℕ) (rest : List (CTask C (Node K HState A) F)) (emitted : List (C × A))
    (pulled : H.pull h = .done) :
    cstep (withHostCut P isHost H) ⟨⟨context, .host h, returns, scope⟩ :: rest, emitted⟩ =
      ⟨rest, emitted⟩ := by
  simp [cstep, cexpand, withHostCut, pulled, scopedPullBranches]

end HostNode

/-! ## The inline run and the hosted run -/

section Correspondence

/-- The tasks of the hosted run. -/
abbrev HTask (C K F A : Type) := CTask C (Node K (List (CTask C K F)) A) F

/-- How many tasks of the inline run a hosted task stands for: a host node, its host's frontier;
any other task, itself. -/
def width {H' : Type} : Node K (List H') A → ℕ
  | .host h => h.length
  | _ => 1

/-- How many tasks of the inline run a hosted frontier stands for. -/
def inlineLen : List (HTask C K F A) → ℕ
  | [] => 0
  | t :: rest => width t.control + inlineLen rest

/-- A hosted scope as an inline scope: the scope over the hosted tasks `below` counts the inline
tasks they stand for. -/
def mapScope (below : List (HTask C K F A)) : Option ℕ → Option ℕ
  | none => none
  | some n => some (inlineLen (below.drop (below.length - n)))

/-- Return frames of a hosted task, their scopes as inline scopes. -/
def mapFrames (below : List (HTask C K F A)) (frames : List (F × Option ℕ)) :
    List (F × Option ℕ) :=
  frames.map fun frame => (frame.1, mapScope below frame.2)

/-- A host's scope as an inline scope: the host's frontier lies over `base` inline tasks, and its
goal's own code (`none`) runs in the scope `encl` of the code that entered the goal. -/
def shiftScope (base : ℕ) (encl : Option ℕ) : Option ℕ → Option ℕ
  | none => encl
  | some n => some (n + base)

/-- A task of a host's frontier as a task of the inline run: its scopes shifted, and the frames
`outer` of the code that entered the goal below its own. -/
def liftHost (base : ℕ) (encl : Option ℕ) (outer : List (F × Option ℕ)) (t : CTask C K F) :
    CTask C K F :=
  ⟨t.context, t.control, t.returns.map (fun frame => (frame.1, shiftScope base encl frame.2)) ++ outer,
    shiftScope base encl t.scope⟩

/-- The own code of a goal with no cut: controls `S` that never cut, whose `enter`s stay in `S`
with frames `Fr`, whose calls push frames `Fr`, and frames `Fr` that resume into `S`. -/
structure OwnLevel (P : CProgram C K Call F A) (S : K → Prop) (Fr : F → Prop) : Prop where
  noCut : ∀ k, S k → ∀ next, P.inspect k ≠ .cut next
  enter : ∀ k callee frame, S k → P.inspect k = .enter callee frame →
    Fr frame ∧ ∀ context next, next ∈ P.branches context callee → S next.2
  call : ∀ k callee frame, S k → P.inspect k = .call callee frame → Fr frame
  resume : ∀ frame, Fr frame → ∀ context value, S (P.resume context frame value).2

/-- Every host goal's alternatives are own code of a goal with no cut. -/
def GoalsOwn (P : CProgram C K Call F A) (isHost : Call → Bool) (S : K → Prop) : Prop :=
  ∀ context callee, isHost callee = true → ∀ next ∈ P.branches context callee, S next.2

/-- A host's frontier for a goal with no cut: well scoped, its tasks outside every activation
(the goal's own code) in `S`, and their frames in `Fr`. -/
structure HostOK (S : K → Prop) (Fr : F → Prop) (h : List (CTask C K F)) : Prop where
  wellScoped : WellScoped h
  own : ∀ t ∈ h, t.scope = none → S t.control
  frames : ∀ t ∈ h, ∀ frame ∈ t.returns, frame.2 = none → Fr frame.1

/-- **The correspondence.**  A hosted frontier and an inline frontier, built from the bottom: a
base task as itself, its scopes counted in inline tasks; an answer waiting above its host node as
the continuation it resumes; a host node as its host's frontier, lifted onto the inline tasks
below it, the goal's own code in the scope of the code that entered it. -/
inductive FRel (P : CProgram C K Call F A) (S : K → Prop) (Fr : F → Prop) :
    List (HTask C K F A) → List (CTask C K F) → Prop
  | nil : FRel P S Fr [] []
  | run {below : List (HTask C K F A)} {ibelow : List (CTask C K F)} {context : C} {control : K}
      {returns : List (F × Option ℕ)} {scope : Option ℕ} :
      FRel P S Fr below ibelow →
      FRel P S Fr (⟨context, .run control, returns, scope⟩ :: below)
        (⟨context, control, mapFrames below returns, mapScope below scope⟩ :: ibelow)
  | answer {below : List (HTask C K F A)} {ibelow : List (CTask C K F)} {context : C} {value : A}
      {frame : F} {outer : Option ℕ} {returns : List (F × Option ℕ)} {scope : Option ℕ} :
      FRel P S Fr below ibelow →
      FRel P S Fr (⟨context, .answer value, (frame, outer) :: returns, scope⟩ :: below)
        (⟨(P.resume context frame value).1, (P.resume context frame value).2,
          mapFrames below returns, mapScope below outer⟩ :: ibelow)
  | host {below : List (HTask C K F A)} {ibelow : List (CTask C K F)} {context : C}
      {h : List (CTask C K F)} {frame : F} {outer : Option ℕ} {returns : List (F × Option ℕ)}
      {scope : Option ℕ} :
      FRel P S Fr below ibelow → HostOK S Fr h →
      FRel P S Fr (⟨context, .host h, (frame, outer) :: returns, scope⟩ :: below)
        (h.map (liftHost ibelow.length (mapScope below outer)
          (mapFrames below ((frame, outer) :: returns))) ++ ibelow)

variable {P : CProgram C K Call F A} {S : K → Prop} {Fr : F → Prop}

theorem FRel.length {below : List (HTask C K F A)} {ibelow : List (CTask C K F)}
    (rel : FRel P S Fr below ibelow) : ibelow.length = inlineLen below := by
  induction rel with
  | nil => rfl
  | run _ ih => simp [inlineLen, width, ih]; omega
  | answer _ ih => simp [inlineLen, width, ih]; omega
  | host _ _ ih => simp [inlineLen, width, ih]

theorem inlineLen_append (xs ys : List (HTask C K F A)) :
    inlineLen (xs ++ ys) = inlineLen xs + inlineLen ys := by
  induction xs with
  | nil => simp [inlineLen]
  | cons x xs ih => simp only [List.cons_append, inlineLen, ih]; omega

theorem drop_append_left {α : Type} (xs ys : List α) (k : ℕ) :
    (xs ++ ys).drop (xs.length + k) = ys.drop k := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
  congr 1
  omega

theorem mapScope_append (new below : List (HTask C K F A)) {scope : Option ℕ}
    (fits : Fits scope below.length) : mapScope (new ++ below) scope = mapScope below scope := by
  cases scope with
  | none => rfl
  | some n =>
    have le := fits n rfl
    simp only [mapScope, List.length_append]
    rw [show new.length + below.length - n = new.length + (below.length - n) by omega,
      drop_append_left]

theorem mapFrames_append (new below : List (HTask C K F A)) {frames : List (F × Option ℕ)}
    (fits : ∀ frame ∈ frames, Fits frame.2 below.length) :
    mapFrames (new ++ below) frames = mapFrames below frames := by
  refine List.map_congr_left fun frame member => ?_
  rw [mapScope_append new below (fits frame member)]

theorem mapScope_self (below : List (HTask C K F A)) :
    mapScope below (some below.length) = some (inlineLen below) := by
  simp [mapScope]

theorem inlineLen_take_drop (below : List (HTask C K F A)) (k : ℕ) :
    inlineLen (below.take k) + inlineLen (below.drop k) = inlineLen below := by
  rw [← inlineLen_append, List.take_append_drop]

/-- Dropping hosted tasks from the top drops the inline tasks they stand for. -/
theorem FRel.dropTop {below : List (HTask C K F A)} {ibelow : List (CTask C K F)}
    (rel : FRel P S Fr below ibelow) :
    ∀ k, FRel P S Fr (below.drop k) (ibelow.drop (inlineLen (below.take k))) := by
  induction rel with
  | nil => intro k; simpa [inlineLen] using FRel.nil
  | run rel' ih =>
    intro k
    cases k with
    | zero => simpa [inlineLen] using FRel.run rel'
    | succ k =>
      simp only [List.drop_succ_cons, List.take_succ_cons, inlineLen, width]
      rw [Nat.add_comm 1, List.drop_succ_cons]
      exact ih k
  | answer rel' ih =>
    intro k
    cases k with
    | zero => simpa [inlineLen] using FRel.answer rel'
    | succ k =>
      simp only [List.drop_succ_cons, List.take_succ_cons, inlineLen, width]
      rw [Nat.add_comm 1, List.drop_succ_cons]
      exact ih k
  | @host below' ibelow' context h frame outer returns scope rel' ok ih =>
    intro k
    cases k with
    | zero => simpa [inlineLen] using FRel.host rel' ok
    | succ k =>
      simp only [List.drop_succ_cons, List.take_succ_cons, inlineLen, width]
      have := drop_append_left (h.map (liftHost ibelow'.length (mapScope below' outer)
        (mapFrames below' ((frame, outer) :: returns)))) ibelow' (inlineLen (below'.take k))
      simp only [List.length_map] at this
      rw [this]
      exact ih k

/-- The tasks a hosted cut keeps and the inline tasks they stand for. -/
theorem FRel.keepBelow {below : List (HTask C K F A)} {ibelow : List (CTask C K F)}
    (rel : FRel P S Fr below ibelow) {scope : Option ℕ} (fits : Fits scope below.length) :
    FRel P S Fr (Scopes.keepBelow scope below)
      (Scopes.keepBelow (mapScope below scope) ibelow) := by
  cases scope with
  | none => exact .nil
  | some n =>
    have le := fits n rfl
    simp only [Scopes.keepBelow, mapScope]
    have split := inlineLen_take_drop below (below.length - n)
    rw [show ibelow.length - inlineLen (below.drop (below.length - n)) =
      inlineLen (below.take (below.length - n)) by rw [rel.length]; omega]
    exact rel.dropTop _

/-- A scope that fits a kept suffix maps the same over the suffix as over the whole. -/
theorem mapScope_keepBelow (below : List (HTask C K F A)) {scope inner : Option ℕ}
    (fitsScope : Fits scope below.length) (around : Outer inner scope) :
    mapScope (Scopes.keepBelow scope below) inner = mapScope below inner := by
  cases inner with
  | none => rfl
  | some m =>
    obtain ⟨n, rfl, le⟩ := around m rfl
    have bound := fitsScope n rfl
    simp only [Scopes.keepBelow, mapScope, List.length_drop, List.drop_drop]
    congr 3
    omega

theorem Nested.fits {scope : Option ℕ} {frames : List (F × Option ℕ)} {n : ℕ}
    (nested : Nested scope frames) (fits : Fits scope n) : ∀ frame ∈ frames, Fits frame.2 n := by
  induction nested with
  | nil => intro frame member; cases member
  | cons around rest ih =>
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · exact fits.outer around
    · exact ih (fits.outer around) frame member

theorem Nested.outer {scope : Option ℕ} {frames : List (F × Option ℕ)}
    (nested : Nested scope frames) : ∀ frame ∈ frames, Outer frame.2 scope := by
  induction nested with
  | nil => intro frame member; cases member
  | cons around rest ih =>
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · exact around
    · exact (ih frame member).trans around

/-- Pushing base tasks with common frames and scope keeps the correspondence. -/
theorem FRel.pushRuns {below : List (HTask C K F A)} {ibelow : List (CTask C K F)}
    (rel : FRel P S Fr below ibelow) (next : List (C × K)) (returns : List (F × Option ℕ))
    (scope : Option ℕ) (fitsScope : Fits scope below.length)
    (fitsFrames : ∀ frame ∈ returns, Fits frame.2 below.length) :
    FRel P S Fr ((next.map fun n => (⟨n.1, Node.run n.2, returns, scope⟩ : HTask C K F A)) ++ below)
      ((next.map fun n => (⟨n.1, n.2, mapFrames below returns, mapScope below scope⟩ :
        CTask C K F)) ++ ibelow) := by
  induction next with
  | nil => exact rel
  | cons n rest ih =>
    have := FRel.run (P := P) (S := S) (Fr := Fr) (context := n.1) (control := n.2)
      (returns := returns) (scope := scope) ih
    rw [mapFrames_append _ _ fitsFrames, mapScope_append _ _ fitsScope] at this
    exact this

/-- A base frontier corresponds to itself, its scopes unchanged. -/
def liftRun (t : CTask C K F) : HTask C K F A := ⟨t.context, .run t.control, t.returns, t.scope⟩

theorem inlineLen_liftRun (tasks : List (CTask C K F)) :
    inlineLen (tasks.map (liftRun (A := A))) = tasks.length := by
  induction tasks with
  | nil => rfl
  | cons t rest ih => simp [inlineLen, liftRun, width, ih]; omega

theorem mapScope_liftRun (tasks : List (CTask C K F)) {scope : Option ℕ}
    (fits : Fits scope tasks.length) : mapScope (tasks.map (liftRun (A := A))) scope = scope := by
  cases scope with
  | none => rfl
  | some n =>
    have le := fits n rfl
    simp only [mapScope, List.length_map, ← List.map_drop, inlineLen_liftRun, List.length_drop]
    congr 1
    omega

theorem FRel.ofWellScoped {tasks : List (CTask C K F)} (wellScoped : WellScoped tasks) :
    FRel P S Fr (tasks.map (liftRun (A := A))) tasks := by
  induction wellScoped with
  | nil => exact .nil
  | @cons t rest fits nested _ ih =>
    have := FRel.run (P := P) (S := S) (Fr := Fr) (context := t.context) (control := t.control)
      (returns := t.returns) (scope := t.scope) ih
    have frames : mapFrames (rest.map (liftRun (A := A))) t.returns = t.returns := by
      conv_rhs => rw [← List.map_id t.returns]
      refine List.map_congr_left fun frame member => ?_
      rw [mapScope_liftRun rest (nested.fits fits frame member)]
      rfl
    rw [frames, mapScope_liftRun rest fits] at this
    exact this

section Step

variable (P) (isHost : Call → Bool) (own : OwnLevel P S Fr) (goals : GoalsOwn P isHost S)
include own

/-- The own code of a goal with no cut keeps its invariants through a step of its host. -/
theorem HostOK.cexpand {ht : CTask C K F} {hrest : List (CTask C K F)}
    (ok : HostOK S Fr (ht :: hrest)) : HostOK S Fr (Scopes.cexpand P ht hrest).1 := by
  have htOwn := ok.own ht List.mem_cons_self
  have htFrames := ok.frames ht List.mem_cons_self
  have restOwn : ∀ t ∈ hrest, t.scope = none → S t.control :=
    fun t member => ok.own t (List.mem_cons_of_mem _ member)
  have restFrames : ∀ t ∈ hrest, ∀ frame ∈ t.returns, frame.2 = none → Fr frame.1 :=
    fun t member => ok.frames t (List.mem_cons_of_mem _ member)
  refine ⟨ok.wellScoped.cexpand P, ?_, ?_⟩
  · unfold Scopes.cexpand
    split
    · split
      · exact restOwn
      · rename_i frame scope pending returns
        intro t member outside
        rcases List.mem_cons.mp member with rfl | member
        · have : Fr frame := htFrames (frame, scope) (by rw [returns]; exact List.mem_cons_self)
            (by simpa using outside)
          exact own.resume frame this _ _
        · exact restOwn t member outside
    · exact restOwn
    · intro t member outside
      rcases List.mem_append.mp member with member | member
      · simp only [List.mem_map] at member
        obtain ⟨next, _, rfl⟩ := member
        cases outside
      · exact restOwn t member outside
    · intro t member outside
      rcases List.mem_append.mp member with member | member
      · simp only [List.mem_map] at member
        obtain ⟨next, _, rfl⟩ := member
        cases outside
      · exact restOwn t member outside
    · rename_i callee frame entering
      intro t member outside
      rcases List.mem_append.mp member with member | member
      · simp only [List.mem_map] at member
        obtain ⟨next, nextMember, rfl⟩ := member
        exact (own.enter _ callee frame (htOwn outside) entering).2 _ next nextMember
      · exact restOwn t member outside
    · rename_i next cutting
      intro t member outside
      rcases List.mem_cons.mp member with rfl | member
      · exact absurd cutting (own.noCut _ (htOwn outside) next)
      · cases scope : ht.scope with
        | none => rw [scope] at member; cases member
        | some n =>
          rw [scope] at member
          exact restOwn t (List.mem_of_mem_drop member) outside
  · unfold Scopes.cexpand
    split
    · split
      · exact restFrames
      · rename_i frame scope pending returns
        intro t member
        rcases List.mem_cons.mp member with rfl | member
        · intro frame' inPending outside
          exact htFrames frame' (by rw [returns]; exact List.mem_cons_of_mem _ inPending) outside
        · exact restFrames t member
    · exact restFrames
    · rename_i callee frame calling
      intro t member
      rcases List.mem_append.mp member with member | member
      · simp only [List.mem_map] at member
        obtain ⟨next, _, rfl⟩ := member
        intro frame' inFrames outside
        rcases List.mem_cons.mp inFrames with rfl | inFrames
        · exact own.call _ callee frame (htOwn outside) calling
        · exact htFrames frame' inFrames outside
      · exact restFrames t member
    · intro t member
      rcases List.mem_append.mp member with member | member
      · simp only [List.mem_map] at member
        obtain ⟨next, _, rfl⟩ := member
        exact htFrames
      · exact restFrames t member
    · rename_i callee frame entering
      intro t member
      rcases List.mem_append.mp member with member | member
      · simp only [List.mem_map] at member
        obtain ⟨next, _, rfl⟩ := member
        intro frame' inFrames outside
        rcases List.mem_cons.mp inFrames with rfl | inFrames
        · exact (own.enter _ callee frame (htOwn outside) entering).1
        · exact htFrames frame' inFrames outside
      · exact restFrames t member
    · intro t member
      rcases List.mem_cons.mp member with rfl | member
      · exact htFrames
      · cases scope : ht.scope with
        | none => rw [scope] at member; cases member
        | some n =>
          rw [scope] at member
          exact restFrames t (List.mem_of_mem_drop member)

omit own in
theorem HostOK.tail {ht : CTask C K F} {hrest : List (CTask C K F)}
    (ok : HostOK S Fr (ht :: hrest)) : HostOK S Fr hrest := by
  cases ok.wellScoped with
  | cons _ _ restScoped =>
    exact ⟨restScoped, fun t member => ok.own t (List.mem_cons_of_mem _ member),
      fun t member => ok.frames t (List.mem_cons_of_mem _ member)⟩

/-- **A host's step, lifted.**  Lifted onto the inline tasks `ibelow`, the goal's own code in the
scope `encl` of the code that entered it, a step of a goal with no cut is the host's step: a
silent step leaves the host's new frontier, lifted, over `ibelow`; a step that delivers an answer
resumes the frame that entered the goal, in the answer's context, over the rest of the host's
frontier.  `ibelow` is untouched either way. -/
theorem cexpand_liftHost {ht : CTask C K F} {hrest : List (CTask C K F)}
    (ok : HostOK S Fr (ht :: hrest)) (encl : Option ℕ) (frame : F) (outer : List (F × Option ℕ))
    (ibelow : List (CTask C K F)) :
    ((Scopes.cexpand P ht hrest).2 = [] ∧
        Scopes.cexpand P (liftHost ibelow.length encl ((frame, encl) :: outer) ht)
          (hrest.map (liftHost ibelow.length encl ((frame, encl) :: outer)) ++ ibelow) =
        ((Scopes.cexpand P ht hrest).1.map (liftHost ibelow.length encl ((frame, encl) :: outer)) ++
          ibelow, [])) ∨
      ∃ context value, Scopes.cexpand P ht hrest = (hrest, [(context, value)]) ∧
        Scopes.cexpand P (liftHost ibelow.length encl ((frame, encl) :: outer) ht)
          (hrest.map (liftHost ibelow.length encl ((frame, encl) :: outer)) ++ ibelow) =
        (⟨(P.resume context frame value).1, (P.resume context frame value).2, outer, encl⟩ ::
          (hrest.map (liftHost ibelow.length encl ((frame, encl) :: outer)) ++ ibelow), []) := by
  have htFits : Fits ht.scope hrest.length := by
    cases ok.wellScoped with
    | cons fits _ _ => exact fits
  obtain ⟨context, control, returns, scope⟩ := ht
  simp only at htFits
  cases inspect : P.inspect control with
  | ret value =>
    cases returns with
    | nil =>
      refine .inr ⟨context, value, ?_, ?_⟩
      · simp [Scopes.cexpand, inspect]
      · simp [Scopes.cexpand, liftHost, inspect]
    | cons head pending =>
      obtain ⟨frame₁, scope₁⟩ := head
      refine .inl ⟨by simp [Scopes.cexpand, inspect], ?_⟩
      simp [Scopes.cexpand, liftHost, inspect]
  | fail =>
    exact .inl ⟨by simp [Scopes.cexpand, inspect], by simp [Scopes.cexpand, liftHost, inspect]⟩
  | call callee frame₁ =>
    refine .inl ⟨by simp [Scopes.cexpand, inspect], ?_⟩
    simp only [Scopes.cexpand, liftHost, inspect, List.map_append, List.map_map, List.append_assoc,
      List.length_append, List.length_map, shiftScope]
    exact congrArg (fun tasks => (tasks ++ _, [])) (List.map_congr_left fun next _ => rfl)
  | tail callee =>
    refine .inl ⟨by simp [Scopes.cexpand, inspect], ?_⟩
    simp only [Scopes.cexpand, liftHost, inspect, List.map_append, List.map_map, List.append_assoc,
      List.length_append, List.length_map, shiftScope]
    exact congrArg (fun tasks => (tasks ++ _, [])) (List.map_congr_left fun next _ => rfl)
  | enter callee frame₁ =>
    refine .inl ⟨by simp [Scopes.cexpand, inspect], ?_⟩
    simp only [Scopes.cexpand, liftHost, inspect, List.map_append, List.map_map, List.append_assoc]
    exact congrArg (fun tasks => (tasks ++ _, [])) (List.map_congr_left fun next _ => rfl)
  | cut next =>
    cases scope with
    | none =>
      exact absurd inspect (own.noCut _ (ok.own _ List.mem_cons_self rfl) next)
    | some n =>
      have le := htFits n rfl
      refine .inl ⟨by simp [Scopes.cexpand, inspect], ?_⟩
      simp only [Scopes.cexpand, liftHost, inspect, shiftScope, Scopes.keepBelow, List.length_append,
        List.length_map, List.map_cons, Prod.mk.injEq, and_true]
      rw [show hrest.length + ibelow.length - (n + ibelow.length) = hrest.length - n by omega,
        List.drop_append_of_le_length (by simp only [List.length_map]; omega)]
      simp [List.map_drop]

/-- **A host goal with no cut touches only its own segment.**  In the inline run, a step of a
goal whose own code has no cut, its tasks lifted onto the inline tasks `ibelow` (the enclosing
activation's alternatives and everything under them), leaves `ibelow` as it was and delivers
nothing: an answer of the goal resumes the frame that entered it. -/
theorem inline_goal_step {ht : CTask C K F} {hrest : List (CTask C K F)}
    (ok : HostOK S Fr (ht :: hrest)) (encl : Option ℕ) (frame : F) (outer : List (F × Option ℕ))
    (ibelow : List (CTask C K F)) (emitted : List (C × A)) :
    ∃ top, cstep P ⟨(ht :: hrest).map (liftHost ibelow.length encl ((frame, encl) :: outer)) ++ ibelow,
      emitted⟩ = ⟨top ++ ibelow, emitted⟩ := by
  rcases cexpand_liftHost P own ok encl frame outer ibelow with ⟨_, lifted⟩ | ⟨context, value, _, lifted⟩
  · refine ⟨(Scopes.cexpand P ht hrest).1.map (liftHost ibelow.length encl ((frame, encl) :: outer)), ?_⟩
    simp only [List.map_cons, List.cons_append, cstep_cons, lifted, List.append_nil]
  · refine ⟨⟨(P.resume context frame value).1, (P.resume context frame value).2, outer, encl⟩ ::
      hrest.map (liftHost ibelow.length encl ((frame, encl) :: outer)), ?_⟩
    simp only [List.map_cons, List.cons_append, cstep_cons, lifted, List.append_nil]

/-- **A host goal with no cut runs in its own segment.**  Until its own run delivers an answer
or is exhausted, the inline run of a goal whose own code has no cut, its tasks lifted onto the
inline tasks `ibelow`, is its host's run lifted onto `ibelow`: nothing is delivered, and `ibelow`,
the enclosing activation's alternatives and everything under them, stays as it was.  Cuts of the
relations the goal calls act inside the segment. -/
theorem inline_goal_segment (encl : Option ℕ) (frame : F) (outer : List (F × Option ℕ))
    (ibelow : List (CTask C K F)) (emitted : List (C × A)) :
    ∀ (k : ℕ) (h : List (CTask C K F)), HostOK S Fr h →
      (∀ k' < k, (repeats (cstep P) k' ⟨h, []⟩).frontier ≠ []) →
      (repeats (cstep P) k ⟨h, []⟩).emitted = [] →
      repeats (cstep P) k
          ⟨h.map (liftHost ibelow.length encl ((frame, encl) :: outer)) ++ ibelow, emitted⟩ =
        ⟨(repeats (cstep P) k ⟨h, []⟩).frontier.map
            (liftHost ibelow.length encl ((frame, encl) :: outer)) ++ ibelow, emitted⟩
  | 0, _, _, _, _ => rfl
  | k + 1, h, ok, live, silent => by
    obtain ⟨ht, hrest, rfl⟩ := List.exists_cons_of_ne_nil (live 0 (Nat.succ_pos k))
    have first : ∀ k', repeats (cstep P) (k' + 1) ⟨ht :: hrest, []⟩ =
        ⟨(repeats (cstep P) k' ⟨(Scopes.cexpand P ht hrest).1, []⟩).frontier,
          (Scopes.cexpand P ht hrest).2 ++
            (repeats (cstep P) k' ⟨(Scopes.cexpand P ht hrest).1, []⟩).emitted⟩ := by
      intro k'
      show repeats (cstep P) k' (cstep P ⟨ht :: hrest, []⟩) = _
      rw [cstep_cons, crepeats_emitted P k' _ ([] ++ _), List.nil_append]
    rw [first k] at silent
    obtain ⟨quiet, silent'⟩ := List.append_eq_nil_iff.mp silent
    have later : ∀ k' < k,
        (repeats (cstep P) k' ⟨(Scopes.cexpand P ht hrest).1, []⟩).frontier ≠ [] := by
      intro k' below
      have := live (k' + 1) (by omega)
      rwa [first k'] at this
    rcases cexpand_liftHost P own ok encl frame outer ibelow with
      ⟨_, lifted⟩ | ⟨context, value, delivers, _⟩
    · show repeats (cstep P) k (cstep P ⟨liftHost ibelow.length encl ((frame, encl) :: outer) ht ::
          (hrest.map (liftHost ibelow.length encl ((frame, encl) :: outer)) ++ ibelow), emitted⟩) = _
      rw [cstep_cons, lifted, List.append_nil, first k,
        inline_goal_segment encl frame outer ibelow emitted k _ (ok.cexpand P own) later silent']
    · rw [delivers] at quiet
      cases quiet

/-- Corresponding states: corresponding frontiers and the same answers delivered. -/
def SRel (P : CProgram C K Call F A) (S : K → Prop) (Fr : F → Prop)
    (sH : CState C (Node K (List (CTask C K F)) A) F A) (sI : CState C K F A) : Prop :=
  FRel P S Fr sH.frontier sI.frontier ∧ sH.emitted = sI.emitted

include goals

omit own in
theorem step_run {below : List (HTask C K F A)} {ibelow : List (CTask C K F)}
    (rel : FRel P S Fr below ibelow) {context : C} {control : K} {returns : List (F × Option ℕ)}
    {scope : Option ℕ}
    (wellScoped : WellScoped ((⟨context, .run control, returns, scope⟩ : HTask C K F A) :: below))
    (emitted : List (C × A)) :
    SRel P S Fr (cstep (hostedCut P isHost) ⟨⟨context, .run control, returns, scope⟩ :: below, emitted⟩)
      (cstep P ⟨⟨context, control, mapFrames below returns, mapScope below scope⟩ :: ibelow, emitted⟩) := by
  cases wellScoped with
  | cons fits nested _ =>
  have framesFit := nested.fits fits
  simp only at fits nested framesFit
  have self : mapScope below (some below.length) = some ibelow.length := by
    rw [mapScope_self, rel.length]
  cases inspect : P.inspect control with
  | ret value =>
    cases returns with
    | nil =>
      refine ⟨?_, ?_⟩ <;>
        simp [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect, mapFrames, rel]
    | cons head pending =>
      obtain ⟨frame, outer⟩ := head
      refine ⟨?_, ?_⟩
      · simp only [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect, mapFrames, List.map_cons]
        exact .run rel
      · simp [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect, mapFrames]
  | fail =>
    refine ⟨?_, ?_⟩ <;> simp [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect, rel]
  | call callee frame =>
    refine ⟨?_, by simp [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect]⟩
    have := rel.pushRuns (P.branches context callee) ((frame, scope) :: returns) (some below.length)
      (fun k eq => by cases eq; exact Nat.le_refl _)
      (fun frame' member => by
        rcases List.mem_cons.mp member with rfl | member
        · exact fits
        · exact framesFit frame' member)
    simp only [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect, List.map_map]
    rw [self] at this
    simpa [mapFrames, Function.comp_def] using this
  | tail callee =>
    refine ⟨?_, by simp [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect]⟩
    have := rel.pushRuns (P.branches context callee) returns (some below.length)
      (fun k eq => by cases eq; exact Nat.le_refl _) framesFit
    simp only [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect, List.map_map]
    rw [self] at this
    simpa [mapFrames, Function.comp_def] using this
  | enter callee frame =>
    refine ⟨?_, by simp [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect]⟩
    by_cases hosting : isHost callee = true
    · simp only [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect, hosting, if_true,
        List.map_cons, List.map_nil, List.singleton_append]
      have ok : HostOK S Fr (goalTasks P (context, callee)) := by
        refine ⟨?_, ?_, ?_⟩
        · have := WellScoped.append (new := goalTasks P (context, callee)) (rest := [])
            (fun t member => by
              simp only [goalTasks, List.mem_map] at member
              obtain ⟨next, _, rfl⟩ := member
              exact ⟨(fun k eq => by cases eq), Nested.nil _⟩) .nil
          simpa using this
        · intro t member _
          simp only [goalTasks, List.mem_map] at member
          obtain ⟨next, nextMember, rfl⟩ := member
          exact goals context callee hosting next nextMember
        · intro t member frame' inFrames
          simp only [goalTasks, List.mem_map] at member
          obtain ⟨next, _, rfl⟩ := member
          cases inFrames
      have := FRel.host (context := context) (frame := frame) (outer := scope) (returns := returns)
        (scope := scope) rel ok
      convert this using 2
      all_goals first
        | rfl
        | (simp only [goalTasks, List.map_map]; exact List.map_congr_left fun next _ => rfl)
    · simp only [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect, hosting, Bool.false_eq_true,
        if_false, List.map_map]
      have := rel.pushRuns (P.branches context callee) ((frame, scope) :: returns) scope fits
        (fun frame' member => by
          rcases List.mem_cons.mp member with rfl | member
          · exact fits
          · exact framesFit frame' member)
      simpa [mapFrames, Function.comp_def] using this
  | cut next =>
    refine ⟨?_, by simp [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect]⟩
    simp only [cstep, Scopes.cexpand, withHostCut, liftInstr, inspect]
    have kept := rel.keepBelow fits
    have := FRel.run (P := P) (S := S) (Fr := Fr) (context := context) (control := next)
      (returns := returns) (scope := scope) kept
    have frames : mapFrames (Scopes.keepBelow scope below) returns = mapFrames below returns :=
      List.map_congr_left fun frame member => by
        rw [mapScope_keepBelow below fits (nested.outer frame member)]
    rw [frames, mapScope_keepBelow below fits (Outer.refl scope)] at this
    exact this

omit own goals in
theorem cstep_answer_eq {below : List (HTask C K F A)} {context : C} {value : A} {frame : F}
    {outer : Option ℕ} {returns : List (F × Option ℕ)} {scope : Option ℕ} (emitted : List (C × A)) :
    cstep (hostedCut P isHost) ⟨⟨context, .answer value, (frame, outer) :: returns, scope⟩ :: below,
      emitted⟩ =
      ⟨⟨(P.resume context frame value).1, .run (P.resume context frame value).2, returns, outer⟩ ::
        below, emitted⟩ := by
  simp [cstep, Scopes.cexpand, withHostCut]

omit own goals in
theorem step_answer {below : List (HTask C K F A)} {ibelow : List (CTask C K F)}
    (rel : FRel P S Fr below ibelow) {context : C} {value : A} {frame : F} {outer : Option ℕ}
    {returns : List (F × Option ℕ)} {scope : Option ℕ} (emitted : List (C × A)) :
    SRel P S Fr (cstep (hostedCut P isHost)
        ⟨⟨context, .answer value, (frame, outer) :: returns, scope⟩ :: below, emitted⟩)
      ⟨⟨(P.resume context frame value).1, (P.resume context frame value).2, mapFrames below returns,
        mapScope below outer⟩ :: ibelow, emitted⟩ := by
  rw [cstep_answer_eq P isHost]
  exact ⟨.run rel, rfl⟩

omit own goals in
theorem cstep_host_nil_eq {below : List (HTask C K F A)} {context : C} {returns : List (F × Option ℕ)}
    {scope : Option ℕ} (emitted : List (C × A)) :
    cstep (hostedCut P isHost) ⟨⟨context, .host [], returns, scope⟩ :: below, emitted⟩ =
      ⟨below, emitted⟩ := by
  simp [cstep, Scopes.cexpand, withHostCut, cutHost, cpull, scopedPullBranches]

omit goals in
theorem step_host_pull {below : List (HTask C K F A)} {ibelow : List (CTask C K F)}
    (rel : FRel P S Fr below ibelow) {context : C} {ht : CTask C K F} {hrest : List (CTask C K F)}
    {frame : F} {outer : Option ℕ} {returns : List (F × Option ℕ)} {scope : Option ℕ}
    (ok : HostOK S Fr (ht :: hrest))
    (wellScoped : WellScoped ((⟨context, .host (ht :: hrest), (frame, outer) :: returns, scope⟩ :
      HTask C K F A) :: below))
    (emitted : List (C × A)) :
    SRel P S Fr (cstep (hostedCut P isHost)
        ⟨⟨context, .host (ht :: hrest), (frame, outer) :: returns, scope⟩ :: below, emitted⟩)
      (cstep P ⟨(ht :: hrest).map (liftHost ibelow.length (mapScope below outer)
        (mapFrames below ((frame, outer) :: returns))) ++ ibelow, emitted⟩) := by
  cases wellScoped with
  | cons fits nested _ =>
  have framesFit := nested.fits fits
  simp only at fits nested framesFit
  have outerFits : Fits outer below.length := framesFit (frame, outer) List.mem_cons_self
  have restFit : ∀ frame' ∈ returns, Fits frame'.2 below.length :=
    fun frame' member => framesFit frame' (List.mem_cons_of_mem _ member)
  have eqFrames : mapFrames below ((frame, outer) :: returns) =
      (frame, mapScope below outer) :: mapFrames below returns := rfl
  rw [eqFrames, List.map_cons, List.cons_append]
  rcases cexpand_liftHost P own ok (mapScope below outer) frame (mapFrames below returns) ibelow with
    ⟨silent, lifted⟩ | ⟨context', value, delivered, lifted⟩
  · have pulled : (cutHost P).pull (ht :: hrest) = .suspend (Scopes.cexpand P ht hrest).1 := by
      simp [cutHost, cpull, silent]
    rw [cstep_host_suspend P isHost (cutHost P) context _ scope below emitted pulled, cstep_cons P,
      lifted]
    refine ⟨?_, by simp⟩
    have := FRel.host (context := context) (frame := frame) (outer := outer) (returns := returns)
      (scope := some below.length) rel (ok.cexpand P own)
    rw [eqFrames] at this
    exact this
  · have pulled : (cutHost P).pull (ht :: hrest) = .yield (context', value) hrest := by
      simp [cutHost, cpull, delivered]
    rw [cstep_host_yield P isHost (cutHost P) context _ scope below emitted pulled, cstep_cons P,
      lifted]
    refine ⟨?_, by simp⟩
    have := FRel.answer (context := context') (value := value) (frame := frame) (outer := outer)
      (returns := returns) (scope := some below.length)
      (FRel.host (context := context) (frame := frame) (outer := outer) (returns := returns)
        (scope := some below.length) rel ok.tail)
    have sameOuter : mapScope ((⟨context, Node.host hrest, (frame, outer) :: returns,
        some below.length⟩ : HTask C K F A) :: below) outer = mapScope below outer :=
      mapScope_append [_] below outerFits
    have sameFrames : mapFrames ((⟨context, Node.host hrest, (frame, outer) :: returns,
        some below.length⟩ : HTask C K F A) :: below) returns = mapFrames below returns :=
      mapFrames_append [_] below restFit
    rw [sameOuter, sameFrames, eqFrames] at this
    exact this

omit own goals in
theorem WellScoped.tail {t : CTask C K F} {rest : List (CTask C K F)}
    (wellScoped : WellScoped (t :: rest)) : WellScoped rest := by
  cases wellScoped with
  | cons _ _ rest => exact rest

/-- **One hosted step is at most one inline step.** -/
theorem hosted_step {sH : CState C (Node K (List (CTask C K F)) A) F A} {sI : CState C K F A}
    (srel : SRel P S Fr sH sI) (wellScoped : WellScoped sH.frontier) :
    ∃ k ≤ 1, SRel P S Fr (cstep (hostedCut P isHost) sH) (repeats (cstep P) k sI) := by
  obtain ⟨rel, emitted⟩ := srel
  rcases sH with ⟨hs, e⟩
  rcases sI with ⟨is, e'⟩
  simp only at rel emitted wellScoped
  subst emitted
  cases rel with
  | nil => exact ⟨0, Nat.zero_le _, .nil, rfl⟩
  | run rel' => exact ⟨1, Nat.le_refl _, step_run P isHost goals rel' wellScoped e⟩
  | answer rel' => exact ⟨0, Nat.zero_le _, step_answer P isHost rel' e⟩
  | @host below ibelow context h frame outer returns scope rel' ok =>
    cases h with
    | nil =>
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [cstep_host_nil_eq P isHost]
      exact ⟨rel', rfl⟩
    | cons ht hrest => exact ⟨1, Nat.le_refl _, step_host_pull P isHost own rel' ok wellScoped e⟩

/-- **The hosted run follows the inline run.**  After `m` hosted steps, the inline run has taken
at most `m` steps to a corresponding state. -/
theorem hosted_follows : ∀ (m : ℕ) {sH : CState C (Node K (List (CTask C K F)) A) F A}
    {sI : CState C K F A}, SRel P S Fr sH sI → WellScoped sH.frontier →
    ∃ n ≤ m, SRel P S Fr (repeats (cstep (hostedCut P isHost)) m sH) (repeats (cstep P) n sI)
  | 0, _, _, srel, _ => ⟨0, Nat.le_refl _, srel⟩
  | m + 1, sH, sI, srel, wellScoped => by
    obtain ⟨k, below, srel'⟩ := hosted_step P isHost own goals srel wellScoped
    obtain ⟨n, bound, srel''⟩ := hosted_follows m srel' (wellScoped.cstep _)
    refine ⟨k + n, by omega, ?_⟩
    rw [Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats_add (cstep P) k n sI]
    exact srel''

/-- **The inline run's steps are matched.**  From corresponding states, one inline step is
matched by finitely many hosted steps: an answer's resumption and an exhausted host's pop
first, when they are on top. -/
theorem inline_step {hs : List (HTask C K F A)} {is : List (CTask C K F)}
    (rel : FRel P S Fr hs is) :
    ∀ (e : List (C × A)), WellScoped hs →
      ∃ k, SRel P S Fr (repeats (cstep (hostedCut P isHost)) k ⟨hs, e⟩) (cstep P ⟨is, e⟩) := by
  induction rel with
  | nil => intro e _; exact ⟨0, .nil, rfl⟩
  | run rel' _ => intro e wellScoped; exact ⟨1, step_run P isHost goals rel' wellScoped e⟩
  | @answer below ibelow context value frame outer returns scope rel' _ =>
    intro e wellScoped
    refine ⟨2, ?_⟩
    have next := WellScoped.cstep (hostedCut P isHost) (s := ⟨_, e⟩) wellScoped
    rw [cstep_answer_eq P isHost] at next
    have twice : repeats (cstep (hostedCut P isHost)) 2
        ⟨⟨context, .answer value, (frame, outer) :: returns, scope⟩ :: below, e⟩ =
        cstep (hostedCut P isHost) (cstep (hostedCut P isHost)
          ⟨⟨context, .answer value, (frame, outer) :: returns, scope⟩ :: below, e⟩) := rfl
    rw [twice, cstep_answer_eq P isHost]
    exact step_run P isHost goals rel' next e
  | @host below ibelow context h frame outer returns scope rel' ok ih =>
    intro e wellScoped
    cases h with
    | nil =>
      obtain ⟨k, srel⟩ := ih e wellScoped.tail
      refine ⟨k + 1, ?_⟩
      show SRel P S Fr (repeats (cstep (hostedCut P isHost)) k (cstep (hostedCut P isHost) _)) _
      rw [cstep_host_nil_eq P isHost]
      simpa using srel
    | cons ht hrest => exact ⟨1, step_host_pull P isHost own rel' ok wellScoped e⟩

/-- **The inline run follows the hosted run.**  After `n` inline steps, the hosted run has taken
some number of steps to a corresponding state. -/
theorem inline_follows : ∀ (n : ℕ) {sH : CState C (Node K (List (CTask C K F)) A) F A}
    {sI : CState C K F A}, SRel P S Fr sH sI → WellScoped sH.frontier →
    ∃ m, SRel P S Fr (repeats (cstep (hostedCut P isHost)) m sH) (repeats (cstep P) n sI)
  | 0, _, _, srel, _ => ⟨0, srel⟩
  | n + 1, ⟨hs, e⟩, ⟨is, e'⟩, ⟨rel, emitted⟩, wellScoped => by
    simp only at emitted rel wellScoped
    subst emitted
    obtain ⟨k, srel⟩ := inline_step P isHost own goals rel e wellScoped
    obtain ⟨m, srel'⟩ := inline_follows n srel (WellScoped.repeats _ k wellScoped)
    refine ⟨k + m, ?_⟩
    rw [Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats_add]
    exact srel'

omit own goals in
theorem FRel.nil_left {is : List (CTask C K F)} (rel : FRel P S Fr [] is) : is = [] := by
  cases rel
  rfl

omit own goals in
/-- A hosted frontier that stands for no inline task holds only exhausted host nodes, which pop
one per step. -/
theorem FRel.exhausted {hs : List (HTask C K F A)} {is : List (CTask C K F)}
    (rel : FRel P S Fr hs is) (empty : is = []) (e : List (C × A)) :
    repeats (cstep (hostedCut P isHost)) hs.length ⟨hs, e⟩ = ⟨[], e⟩ := by
  induction rel generalizing e with
  | nil => rfl
  | run _ _ => cases empty
  | answer _ _ => cases empty
  | @host below ibelow context h frame outer returns scope rel' ok ih =>
    have parts := List.append_eq_nil_iff.mp empty
    have hEmpty : h = [] := by simpa using parts.1
    subst hEmpty
    show repeats (cstep (hostedCut P isHost)) below.length (cstep (hostedCut P isHost) _) = _
    rw [cstep_host_nil_eq P isHost]
    exact ih parts.2 e

end Step

/-- A state of the inline run, running in the machine with host goals. -/
def liftState (s : CState C K F A) : CState C (Node K (List (CTask C K F)) A) F A :=
  ⟨s.frontier.map liftRun, s.emitted⟩

theorem WellScoped.liftRun {tasks : List (CTask C K F)} (wellScoped : WellScoped tasks) :
    WellScoped (tasks.map (liftRun (A := A))) := by
  induction wellScoped with
  | nil => exact .nil
  | cons fits nested _ ih => exact .cons (by rw [List.length_map]; exact fits) nested ih

theorem SRel.start {s : CState C K F A} (wellScoped : WellScoped s.frontier) :
    SRel P S Fr (liftState s) s :=
  ⟨FRel.ofWellScoped wellScoped, rfl⟩

section Composition

variable (P) (isHost : Call → Bool) (own : OwnLevel P S Fr) (goals : GoalsOwn P isHost S)
include own goals

/-- **The composition, answers (inline to hosted).**  For a program whose host goals have no cut
in their own code, and whatever cuts the rest of the program makes: every answer list the inline
run delivers, each host goal run as code of the activation that entered it, the machine with
host goals delivers too, each host goal served by its own run in `cutHost`: the same list. -/
theorem hosted_answers_cut {s : CState C K F A} (wellScoped : WellScoped s.frontier) (n : ℕ) :
    ∃ m, (repeats (cstep (hostedCut P isHost)) m (liftState s)).emitted =
      (repeats (cstep P) n s).emitted := by
  obtain ⟨m, srel⟩ := inline_follows P isHost own goals n (SRel.start wellScoped)
    wellScoped.liftRun
  exact ⟨m, srel.2⟩

/-- **The composition, answers (hosted to inline).**  Every answer list the machine with host
goals delivers within `m` steps, the inline run delivers within at most `m` steps. -/
theorem inline_answers_cut {s : CState C K F A} (wellScoped : WellScoped s.frontier) (m : ℕ) :
    ∃ n ≤ m, (repeats (cstep P) n s).emitted =
      (repeats (cstep (hostedCut P isHost)) m (liftState s)).emitted := by
  obtain ⟨n, bound, srel⟩ := hosted_follows P isHost own goals m (SRel.start wellScoped)
    wellScoped.liftRun
  exact ⟨n, bound, srel.2.symm⟩

/-- **The composition, termination (inline to hosted).**  When the inline run exhausts its
frontier, the machine with host goals exhausts its own, with the same answers. -/
theorem hosted_terminates_cut {s : CState C K F A} (wellScoped : WellScoped s.frontier) {n : ℕ}
    (done : (repeats (cstep P) n s).frontier = []) :
    ∃ m, (repeats (cstep (hostedCut P isHost)) m (liftState s)).frontier = [] ∧
      (repeats (cstep (hostedCut P isHost)) m (liftState s)).emitted =
        (repeats (cstep P) n s).emitted := by
  obtain ⟨m, rel, emitted⟩ := inline_follows P isHost own goals n (SRel.start wellScoped)
    wellScoped.liftRun
  refine ⟨m + (repeats (cstep (hostedCut P isHost)) m (liftState s)).frontier.length, ?_⟩
  rw [Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats_add]
  have popped := rel.exhausted P isHost done
    (repeats (cstep (hostedCut P isHost)) m (liftState s)).emitted
  rw [show (⟨(repeats (cstep (hostedCut P isHost)) m (liftState s)).frontier,
      (repeats (cstep (hostedCut P isHost)) m (liftState s)).emitted⟩ :
        CState C (Node K (List (CTask C K F)) A) F A) =
      repeats (cstep (hostedCut P isHost)) m (liftState s) from rfl] at popped
  rw [popped]
  exact ⟨rfl, emitted⟩

/-- **The composition, termination (hosted to inline).**  When the machine with host goals
exhausts its frontier, the inline run has exhausted its own within at most as many steps, with
the same answers. -/
theorem inline_terminates_cut {s : CState C K F A} (wellScoped : WellScoped s.frontier) {m : ℕ}
    (done : (repeats (cstep (hostedCut P isHost)) m (liftState s)).frontier = []) :
    ∃ n ≤ m, (repeats (cstep P) n s).frontier = [] ∧
      (repeats (cstep P) n s).emitted =
        (repeats (cstep (hostedCut P isHost)) m (liftState s)).emitted := by
  obtain ⟨n, bound, rel, emitted⟩ := hosted_follows P isHost own goals m (SRel.start wellScoped)
    wellScoped.liftRun
  rw [done] at rel
  exact ⟨n, bound, rel.nil_left, emitted.symm⟩

end Composition

end Correspondence

/-! ## Controls -/

namespace Controls

/-- The relations and goals of the controls. -/
inductive Rel where
  | pairs
  | cutFirst
  | outer
  | plain
  | withCut
  | viaPlain
  | viaCut
  | cutAfter
  deriving DecidableEq

/-- The code of an equation: return the value received last (`none`) or a literal, fail, call a
relation, enter a goal (an expression of the same equation), or cut; each call or goal continues
with `next` on its answer. -/
inductive Code where
  | give (value : Option ℕ)
  | fail
  | call (rel : Rel) (next : Code)
  | enter (goal : Rel) (next : Code)
  | cut (next : Code)
  deriving DecidableEq

/-- The equations of each relation and goal, in order.
* `(pairs)` answers `0`, then `1`.
* `(cutFirst)`: `(cut 0)`, then `1`; `(outer)`: `(cutFirst)`, then `5`.
* The goal `plain` calls `(pairs)`; the goal `withCut` cuts, then calls `(pairs)`.
* `(viaPlain)`: enter `plain`, then `2`; `(viaCut)`: enter `withCut`, then `2`;
  `(cutAfter)`: enter `plain` and cut on its answer, then `2`. -/
def equations : Rel → List Code
  | .pairs => [.give (some 0), .give (some 1)]
  | .cutFirst => [.cut (.give (some 0)), .give (some 1)]
  | .outer => [.call .cutFirst (.give none), .give (some 5)]
  | .plain => [.call .pairs (.give none)]
  | .withCut => [.cut (.call .pairs (.give none))]
  | .viaPlain => [.enter .plain (.give none), .give (some 2)]
  | .viaCut => [.enter .withCut (.give none), .give (some 2)]
  | .cutAfter => [.enter .plain (.cut (.give none)), .give (some 2)]

/-- The program: a control is the code and the value received last. -/
def program : CProgram Unit (Code × ℕ) Rel Code ℕ where
  inspect
    | (.give none, x) => .ret x
    | (.give (some n), _) => .ret n
    | (.fail, _) => .fail
    | (.call rel next, _) => .call rel next
    | (.enter goal next, _) => .enter goal next
    | (.cut next, x) => .cut (next, x)
  branches _ rel := (equations rel).map fun code => ((), (code, 0))
  resume _ next value := ((), (next, value))

/-- The query `(rel)`: a call of `rel` outside every activation. -/
def query (rel : Rel) : CState Unit (Code × ℕ) Code ℕ :=
  ⟨[⟨(), (.call rel (.give none), 0), [], none⟩], []⟩

/-- The goals the tier hands to a host: `plain` only, or also `withCut`. -/
def hostPlain (goal : Rel) : Bool := goal == .plain

def hostBoth (goal : Rel) : Bool := goal == .plain || goal == .withCut

/-- **A cut drops its own activation's choices, and nothing below.**  `(cutFirst)` cuts in its
first equation: its second equation, `1`, goes.  `(outer)` calls `(cutFirst)` in its first
equation: its own second equation, `5`, stays.  The run delivers `0` and `5` and is exhausted. -/
theorem cut_scope_runs :
    (repeats (cstep program) 10 (query .outer)).frontier.isEmpty = true ∧
      (repeats (cstep program) 10 (query .outer)).emitted.map Prod.snd = [0, 5] := by
  decide

/-- **A host goal with no cut: the same answers.**  `(viaPlain)` enters the goal `plain`, which
calls `(pairs)`: inline and with `plain` a host goal, the run delivers `0`, `1` and then `2`. -/
theorem plain_runs :
    (repeats (cstep program) 20 (query .viaPlain)).frontier.isEmpty = true ∧
      (repeats (cstep program) 20 (query .viaPlain)).emitted.map Prod.snd = [0, 1, 2] ∧
      (repeats (cstep (hostedCut program hostPlain)) 20 (liftState (query .viaPlain))).frontier.isEmpty =
        true ∧
      (repeats (cstep (hostedCut program hostPlain)) 20
        (liftState (query .viaPlain))).emitted.map Prod.snd = [0, 1, 2] := by
  decide

/-- **A cut of the tier after a host goal: the same answers.**  `(cutAfter)` enters `plain` and
cuts when its first answer arrives: inline, the cut drops `(pairs)`'s second equation and
`(cutAfter)`'s own; with `plain` a host goal, it drops the host node and `(cutAfter)`'s second
equation.  Both deliver `0` alone. -/
theorem cutAfter_runs :
    (repeats (cstep program) 20 (query .cutAfter)).frontier.isEmpty = true ∧
      (repeats (cstep program) 20 (query .cutAfter)).emitted.map Prod.snd = [0] ∧
      (repeats (cstep (hostedCut program hostPlain)) 20 (liftState (query .cutAfter))).frontier.isEmpty =
        true ∧
      (repeats (cstep (hostedCut program hostPlain)) 20
        (liftState (query .cutAfter))).emitted.map Prod.snd = [0] := by
  decide

/-- **A cut delegated to the host cuts nothing it should.**  `(viaCut)` enters the goal
`withCut`, which cuts and then calls `(pairs)`.  Inline, the goal's cut is `(viaCut)`'s: it drops
`(viaCut)`'s second equation, and the run delivers `0` and `1`.  Delegated to the host, the cut
prunes only the host's own frontier: `(viaCut)`'s second equation stays, and the run delivers
`0`, `1` and `2`.  Both runs are exhausted. -/
theorem delegated_cut_runs :
    (repeats (cstep program) 20 (query .viaCut)).frontier.isEmpty = true ∧
      (repeats (cstep program) 20 (query .viaCut)).emitted.map Prod.snd = [0, 1] ∧
      (repeats (cstep (hostedCut program hostBoth)) 20 (liftState (query .viaCut))).frontier.isEmpty =
        true ∧
      (repeats (cstep (hostedCut program hostBoth)) 20
        (liftState (query .viaCut))).emitted.map Prod.snd = [0, 1, 2] := by
  decide

/-- The own code of the goal `plain`: its call of `(pairs)` and the return of its answer. -/
def plainOwn (control : Code × ℕ) : Prop :=
  control.1 = .call .pairs (.give none) ∨ control.1 = .give none

/-- Its frames: the return of the answer. -/
def plainFrames (frame : Code) : Prop := frame = .give none

theorem plain_ownLevel : OwnLevel program plainOwn plainFrames where
  noCut := by
    rintro ⟨code, x⟩ (rfl | rfl) next inspect <;> cases x <;> simp [program] at inspect
  enter := by
    rintro ⟨code, x⟩ callee frame (rfl | rfl) inspect <;> cases x <;> simp [program] at inspect
  call := by
    rintro ⟨code, x⟩ callee frame (rfl | rfl) inspect <;> simp [program] at inspect
    exact inspect.2.symm
  resume := by
    intro frame framed context value
    subst framed
    exact .inr rfl

theorem plain_goalsOwn : GoalsOwn program hostPlain plainOwn := by
  intro context callee hosting next member
  cases callee <;> simp [hostPlain] at hosting
  simp [program, equations] at member
  subst member
  exact .inl rfl

/-- **The law, instantiated.**  For `(cutAfter)`, whose tier code cuts and whose one host goal has
no cut: every answer list the inline run delivers, the machine with host goals delivers. -/
theorem cutAfter_answers (n : ℕ) :
    ∃ m, (repeats (cstep (hostedCut program hostPlain)) m (liftState (query .cutAfter))).emitted =
      (repeats (cstep program) n (query .cutAfter)).emitted :=
  hosted_answers_cut program hostPlain plain_ownLevel plain_goalsOwn
    (.cons (fun k eq => by cases eq) (.nil _) .nil) n

/-- **The hypothesis is needed.**  No own code of a goal with no cut contains `withCut`'s
alternatives, which begin with a cut. -/
theorem withCut_not_own (S : Code × ℕ → Prop) (Fr : Code → Prop) (own : OwnLevel program S Fr) :
    ¬ GoalsOwn program hostBoth S := by
  intro goals
  have inS := goals () .withCut rfl ((), (.cut (.call .pairs (.give none)), 0))
    (by simp [program, equations])
  exact own.noCut _ inS _ rfl

end Controls

end Mettapedia.GSLT.LanguageDef.HostGoals.Scopes
