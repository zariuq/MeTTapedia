import Mettapedia.GSLT.LanguageDef.HostCallRefinement

/-!
# Host goals evaluated by the machines

`HostCallMachine` runs host calls against any ordered answer source (`Host`),
and `HostCallRefinement` proves that host calls compose with output-first
refinement for every host meeting `HostCorrect`.  This module defines the two
hosts CeTTa's compiled open equation tier uses: a host goal is evaluated by
the machines already modelled, on the program's own equations.

**Runs as hosts.**  `machineHost P start` answers a goal by running `P` from
the tasks `start` gives it.  A pull expands the first task of the frontier
(`machinePull`): it yields the answer that step delivers, suspends when the
step delivers none, and is done when the frontier is empty.  A step delivers
at most one answer, and a task that delivers one leaves no successor
(`expand_delivers`), so a pull is exactly one step (`machinePull_step`).  The
batch is one step: a pull never runs more than one, the stream is lazy, and a
goal whose run never answers again suspends forever, as `Host` allows.
`collect_machine`: the collection within `n + 1` pulls is the run's collection
after `n` steps, so it is published exactly when the run has exhausted its
frontier.

**The two hosts.**  `referenceHost PA` evaluates a goal `(rel, args, σ)` with
the output-at-return machine `compiled PA`, from the goal's activations
(`initial`), each answer delivered at return.  `outputFirstHost PF` evaluates a
goal `(rel, args, σ, E)` with the output-first machine `outputFirst PF`, from
the goal's activations against the destination `E` (`goalTasksOut`): the goal
is evaluated as `(let E G E)`, the destination met as each equation of `G` is
activated.  Calls made inside a goal's run, including calls of host relations,
are run by the same machine on the program's equations.
`referenceHost_collect` and `outputFirstHost_collect` are `collect_machine`
for the two hosts.

**The host frame.**  In the machine with host calls (`withHost`), a host call
has one alternative, the host node (`hostCall_branches`).  A pull that yields
puts the answer above the host node: the answer returns to the frames the host
call pushed and resumes the tier's continuation, while the host node waits
below it for the next pull (`step_host_yield`).  A suspension leaves the node in
place (`step_host_suspend`).  Exhaustion removes it, and the tasks below it
continue (`step_host_done`).  `repeats_append`: until the run of a segment `ys`
of the frontier is exhausted, the run of `ys ++ rest` is the run of `ys` with
`rest` unchanged beneath it; afterwards exactly `rest` is left
(`repeats_append_exhausted`).  For a host node the segment is the host goal's
whole run: its pulls, the resumptions of its answers and every task they
create (`host_keeps_below`).

**Correspondence with the C.**  The host node is the host frame.  The tier
yields the host goal `G` with its destination `E` to the enclosing search
machine, which evaluates `(let E G E)` on its one choice stack.  Each answer
resumes the tier once, in order (`step_host_yield`).  The tasks the resumed
tier creates lie above the host node, as the C holds them in a separate choice
above the host goal's choice points, and they are exhausted before the goal is
pulled again.  Exhaustion pops the host frame (`step_host_done`), and the
alternatives below continue.

**Cut.**  Host goals are cut-free by construction: the compiler never makes a
cut a host goal.  The machine has no cut, and `host_keeps_below` is the fact
that makes this usable.  Nothing a host goal's run does removes a task below
its host node.  In particular it never removes the remaining equations of the
relation whose body made the host call: they were placed below it when that
relation was activated, and they are exactly what is left when the goal is
exhausted.

This is a model of the interface between the tier and the enclosing machine,
not a verified translation of the C.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostGoals

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.HostCalls
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## Runs as hosts -/

section Runs

variable {C K Call' F A : Type}

/-- A task delivers at most one answer, and a task that delivers one leaves no
successor. -/
theorem expand_delivers (P : Program C K Call' F A) (t : Task C K F) :
    (expand P t).2 = [] ∨ ∃ a, expand P t = ([], [a]) := by
  unfold expand
  cases P.inspect t.control with
  | ret value => cases t.returns <;> simp [expandWith]
  | fail => simp [expandWith]
  | call callee f => simp [expandWith]
  | tail callee => simp [expandWith]

/-- One step of a run as a pull: the first task expands, and the host yields the
answer it delivers or suspends when it delivers none.  An empty frontier is an
exhausted goal. -/
def machinePull (P : Program C K Call' F A) : List (Task C K F) → Pull (List (Task C K F)) A
  | [] => .done
  | t :: rest =>
      match (expand P t).2 with
      | [] => .suspend ((expand P t).1 ++ rest)
      | a :: _ => .yield a.2 ((expand P t).1 ++ rest)

/-- A run of `P` as an ordered answer source: a goal starts the tasks `start`
gives it, and each pull takes one step. -/
def machineHost {Goal : Type} (P : Program C K Call' F A) (start : Goal → List (Task C K F)) :
    Host Goal (List (Task C K F)) A :=
  ⟨start, machinePull P⟩

theorem machinePull_silent (P : Program C K Call' F A) {t : Task C K F}
    (rest : List (Task C K F)) (silent : (expand P t).2 = []) :
    machinePull P (t :: rest) = .suspend ((expand P t).1 ++ rest) := by
  simp [machinePull, silent]

theorem machinePull_delivers (P : Program C K Call' F A) {t : Task C K F} {a : C × A}
    (rest : List (Task C K F)) (delivers : expand P t = ([], [a])) :
    machinePull P (t :: rest) = .yield a.2 rest := by
  simp [machinePull, delivers]

/-- A step's frontier does not read the answers delivered so far, which it only
extends. -/
theorem step_emitted (P : Program C K Call' F A) (frontier : List (Task C K F))
    (emitted : List (C × A)) :
    step P ⟨frontier, emitted⟩ =
      ⟨(step P ⟨frontier, []⟩).frontier,
        emitted ++ (step P ⟨frontier, []⟩).emitted⟩ := by
  cases frontier with
  | nil => simp [step]
  | cons t rest => simp [step_cons]

/-- A run's frontier does not read the answers delivered before it starts. -/
theorem repeats_emitted (P : Program C K Call' F A) :
    ∀ (n : ℕ) (frontier : List (Task C K F)) (emitted : List (C × A)),
      repeats (step P) n ⟨frontier, emitted⟩ =
        ⟨(repeats (step P) n ⟨frontier, []⟩).frontier,
          emitted ++ (repeats (step P) n ⟨frontier, []⟩).emitted⟩
  | 0, frontier, emitted => by simp [repeats]
  | n + 1, frontier, emitted => by
      simp only [repeats]
      rw [step_emitted P frontier emitted]
      generalize step P ⟨frontier, []⟩ = s
      rcases s with ⟨next, delivered⟩
      dsimp only
      rw [repeats_emitted P n next (emitted ++ delivered), repeats_emitted P n next delivered]
      simp

/-- An exhausted run stays exhausted. -/
theorem repeats_idle (P : Program C K Call' F A) (emitted : List (C × A)) :
    ∀ n, repeats (step P) n ⟨[], emitted⟩ = ⟨[], emitted⟩
  | 0 => rfl
  | n + 1 => repeats_idle P emitted n

/-- **A pull is one step.**  Pulling a nonempty frontier yields the answer the
step delivers, or suspends when it delivers none, and continues from the
frontier the step leaves. -/
theorem machinePull_step (P : Program C K Call' F A) (t : Task C K F)
    (rest : List (Task C K F)) :
    (∃ c a, machinePull P (t :: rest) = .yield a (step P ⟨t :: rest, []⟩).frontier ∧
        (step P ⟨t :: rest, []⟩).emitted = [(c, a)]) ∨
      (machinePull P (t :: rest) = .suspend (step P ⟨t :: rest, []⟩).frontier ∧
        (step P ⟨t :: rest, []⟩).emitted = []) := by
  rw [step_cons]
  rcases expand_delivers P t with silent | ⟨⟨c, a⟩, delivers⟩
  · exact .inr ⟨machinePull_silent P rest silent, by simp [silent]⟩
  · refine .inl ⟨c, a, ?_, by simp [delivers]⟩
    rw [machinePull_delivers P rest delivers, delivers]
    rfl

theorem collectRun_emitted (P : Program C K Call' F A) (n : ℕ) (frontier : List (Task C K F))
    (emitted : List (C × A)) :
    collectRun P n ⟨frontier, emitted⟩ =
      (collectRun P n ⟨frontier, []⟩).map (emitted ++ ·) := by
  unfold collectRun
  rw [repeats_emitted P n frontier emitted]
  split <;> simp_all

/-- **The collection of a run.**  A host running `P` publishes its collection
within `n + 1` pulls exactly when the run has exhausted its frontier after `n`
steps, and the collection is the run's answers, in order. -/
theorem collect_machine (P : Program C K Call' F A) :
    ∀ (n : ℕ) (frontier : List (Task C K F)),
      collect (machinePull P) (n + 1) frontier =
        (collectRun P n ⟨frontier, []⟩).map (List.map Prod.snd)
  | n, [] => by simp [collect, machinePull, collectRun, repeats_idle]
  | 0, t :: rest => by
      rcases machinePull_step P t rest with ⟨c, a, pulled, _⟩ | ⟨pulled, _⟩ <;>
        simp [collect, pulled, collectRun, repeats]
  | n + 1, t :: rest => by
      have run : collectRun P (n + 1) ⟨t :: rest, []⟩ =
          (collectRun P n ⟨(step P ⟨t :: rest, []⟩).frontier, []⟩).map
            ((step P ⟨t :: rest, []⟩).emitted ++ ·) :=
        collectRun_emitted P n _ _
      rcases machinePull_step P t rest with ⟨c, a, pulled, delivered⟩ | ⟨pulled, delivered⟩
      · rw [collect, pulled]
        dsimp only
        rw [collect_machine P n, run, delivered]
        simp [Option.map_map, Function.comp_def]
      · rw [collect, pulled]
        dsimp only
        rw [collect_machine P n, run, delivered]
        simp

/-! ## Segments of the frontier -/

/-- A step of a nonempty frontier followed by `rest` is the step of that
frontier, with `rest` unchanged below it. -/
theorem step_append (P : Program C K Call' F A) {ys : List (Task C K F)} (live : ys ≠ [])
    (rest : List (Task C K F)) (emitted : List (C × A)) :
    step P ⟨ys ++ rest, emitted⟩ =
      ⟨(step P ⟨ys, []⟩).frontier ++ rest, emitted ++ (step P ⟨ys, []⟩).emitted⟩ := by
  obtain ⟨t, ys, rfl⟩ := List.exists_cons_of_ne_nil live
  simp [step_cons]

/-- **Segments.**  Until the run of `ys` is exhausted, the run of `ys ++ rest`
is the run of `ys` with `rest` unchanged below it. -/
theorem repeats_append (P : Program C K Call' F A) (rest : List (Task C K F)) :
    ∀ (m : ℕ) (ys : List (Task C K F)) (emitted : List (C × A)),
      (∀ m' < m, (repeats (step P) m' ⟨ys, []⟩).frontier ≠ []) →
      repeats (step P) m ⟨ys ++ rest, emitted⟩ =
        ⟨(repeats (step P) m ⟨ys, []⟩).frontier ++ rest,
          emitted ++ (repeats (step P) m ⟨ys, []⟩).emitted⟩
  | 0, ys, emitted, _ => by simp [repeats]
  | m + 1, ys, emitted, live => by
      have nonempty : ys ≠ [] := live 0 (Nat.succ_pos m)
      simp only [repeats]
      rw [step_append P nonempty rest emitted]
      have eta : step P ⟨ys, []⟩ = ⟨(step P ⟨ys, []⟩).frontier, (step P ⟨ys, []⟩).emitted⟩ :=
        rfl
      have later : ∀ m' < m,
          (repeats (step P) m' ⟨(step P ⟨ys, []⟩).frontier, []⟩).frontier ≠ [] := by
        intro m' below
        have := live (m' + 1) (by omega)
        simp only [repeats] at this
        rwa [eta, repeats_emitted] at this
      rw [repeats_append P rest m _ _ later, eta,
        repeats_emitted P m _ (step P ⟨ys, []⟩).emitted]
      simp

/-- When the run of `ys` is exhausted, what is left of the run of `ys ++ rest`
is `rest`. -/
theorem repeats_append_exhausted (P : Program C K Call' F A) (rest : List (Task C K F))
    {m : ℕ} {ys : List (Task C K F)} (emitted : List (C × A))
    (live : ∀ m' < m, (repeats (step P) m' ⟨ys, []⟩).frontier ≠ [])
    (exhausted : (repeats (step P) m ⟨ys, []⟩).frontier = []) :
    repeats (step P) m ⟨ys ++ rest, emitted⟩ =
      ⟨rest, emitted ++ (repeats (step P) m ⟨ys, []⟩).emitted⟩ := by
  rw [repeats_append P rest m ys emitted live, exhausted, List.nil_append]

end Runs

/-! ## The host frame -/

section HostFrame

variable {Context Control Call Frame Answer Goal HState : Type}
variable (P : Program Context Control Call Frame Answer) (goal? : Call → Option Goal)
  (H : Host Goal HState Answer)

/-- A host call has one alternative, the host node: none of the alternatives
already on the frontier, such as the remaining equations of the relation whose
body makes the call, is among them. -/
theorem hostCall_branches (context : Context) {c : Call} {g : Goal} (hit : goal? c = some g) :
    (withHost P goal? H).branches context (.base c) = [(context, .host (H.start g))] := by
  simp [withHost, hit]

/-- **Resumption per answer.**  A pull that yields puts the answer, to be
returned to the host node's frames, above the host node, which waits for the
next pull. -/
theorem step_host_yield (context : Context) {h h' : HState} {a : Answer}
    (returns : List Frame) (rest : List (Task Context (Node Control HState Answer) Frame))
    (emitted : List (Context × Answer)) (pulled : H.pull h = .yield a h') :
    step (withHost P goal? H) ⟨⟨context, .host h, returns⟩ :: rest, emitted⟩ =
      ⟨⟨context, .answer a, returns⟩ :: ⟨context, .host h', returns⟩ :: rest,
        emitted⟩ := by
  rw [step_cons, expand_host, pulled]
  simp [pullBranches]

/-- A suspension leaves the host node in place, resumed from its new state. -/
theorem step_host_suspend (context : Context) {h h' : HState} (returns : List Frame)
    (rest : List (Task Context (Node Control HState Answer) Frame))
    (emitted : List (Context × Answer)) (pulled : H.pull h = .suspend h') :
    step (withHost P goal? H) ⟨⟨context, .host h, returns⟩ :: rest, emitted⟩ =
      ⟨⟨context, .host h', returns⟩ :: rest, emitted⟩ := by
  rw [step_cons, expand_host, pulled]
  simp [pullBranches]

/-- **Exhaustion pops the host frame.**  An exhausted goal leaves nothing, and
the tasks below it continue. -/
theorem step_host_done (context : Context) {h : HState} (returns : List Frame)
    (rest : List (Task Context (Node Control HState Answer) Frame))
    (emitted : List (Context × Answer)) (pulled : H.pull h = .done) :
    step (withHost P goal? H) ⟨⟨context, .host h, returns⟩ :: rest, emitted⟩ =
      ⟨rest, emitted⟩ := by
  rw [step_cons, expand_host, pulled]
  simp [pullBranches]

/-- **A host goal keeps the alternatives below it.**  Until the run of a host
node is exhausted (its pulls, the resumptions of its answers and everything
they spawn), the frontier is that run's frontier with the tasks below the node
unchanged beneath it; once it is exhausted, those tasks are all that is left. -/
theorem host_keeps_below (context : Context) (h : HState) (returns : List Frame)
    (rest : List (Task Context (Node Control HState Answer) Frame))
    (emitted : List (Context × Answer)) {m : ℕ}
    (live : ∀ m' < m, (repeats (step (withHost P goal? H)) m'
      ⟨[⟨context, .host h, returns⟩], []⟩).frontier ≠ []) :
    repeats (step (withHost P goal? H)) m ⟨⟨context, .host h, returns⟩ :: rest, emitted⟩ =
      ⟨(repeats (step (withHost P goal? H)) m
          ⟨[⟨context, .host h, returns⟩], []⟩).frontier ++ rest,
        emitted ++ (repeats (step (withHost P goal? H)) m
          ⟨[⟨context, .host h, returns⟩], []⟩).emitted⟩ :=
  repeats_append _ rest m [_] emitted live

end HostFrame

/-! ## The two hosts -/

section Hosts

variable {Term Store Rel Op : Type} (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op)
variable [Inhabited Term] [DecidableEq Rel]

/-- A goal on the output-first side: every output-first activation of the call
against its destination, in authored order, with no return frame. -/
def goalTasksOut (PF : EqProgram L Rel Op) (c : DestCall Term Store Rel) :
    List (Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op)) :=
  (activateOut L S PF c).map fun a => ⟨(), a, []⟩

/-- **The reference host**: the output-at-return machine evaluating the goal on
its own frontier, each answer delivered at return. -/
def referenceHost (PA : EqProgram L Rel Op) :
    Host (Call Term Store Rel) (List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)))
      (Answer Term Store) :=
  machineHost (compiled L S PA) fun c => (initial L S PA c).frontier

/-- **The output-first host**: the output-first machine evaluating the goal
against its destination, as `(let E G E)`: the destination is met when each
equation of the goal is activated. -/
def outputFirstHost (PF : EqProgram L Rel Op) :
    Host (DestCall Term Store Rel)
      (List (Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op))) (Answer Term Store) :=
  machineHost (outputFirst L S PF) (goalTasksOut L S PF)

omit [Inhabited Term] in
/-- Without a destination, the output-first host starts the goal as
`initialOut` does. -/
theorem goalTasksOut_none (PF : EqProgram L Rel Op) (c : Call Term Store Rel) :
    goalTasksOut L S PF (c.1, c.2.1, c.2.2, none) = (initialOut L S PF c).frontier := rfl

/-- The reference host's collection is published within `n + 1` pulls exactly
when the goal's output-at-return run has exhausted its frontier after `n`
steps, and it is that run's answers. -/
theorem referenceHost_collect (PA : EqProgram L Rel Op) (c : Call Term Store Rel) (n : ℕ) :
    collect (referenceHost L S PA).pull (n + 1) ((referenceHost L S PA).start c) =
      (collectRun (compiled L S PA) n (initial L S PA c)).map (List.map Prod.snd) :=
  collect_machine _ n _

/-- The same for the output-first host and the goal's output-first run. -/
theorem outputFirstHost_collect (PF : EqProgram L Rel Op) (c : DestCall Term Store Rel) (n : ℕ) :
    collect (outputFirstHost L S PF).pull (n + 1) ((outputFirstHost L S PF).start c) =
      (collectRun (outputFirst L S PF) n ⟨goalTasksOut L S PF c, []⟩).map (List.map Prod.snd) :=
  collect_machine _ n _

end Hosts

end Mettapedia.GSLT.LanguageDef.HostGoals
