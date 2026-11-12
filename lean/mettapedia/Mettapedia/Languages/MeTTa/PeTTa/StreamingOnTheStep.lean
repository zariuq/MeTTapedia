import Mettapedia.Languages.MeTTa.PeTTa.Streaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.FramedMachines

/-!
# PeTTa's streaming machine on the step: one transition, one firing

`RunsAsFirings` projects an evaluation of the streaming PeTTa machine onto the store: its
space operations are a run of the ordered-store step, and that run does not determine the
evaluation's answers. This module is the inclusion. The whole machine state is placed on the
step's store, the pending work included, and every transition of `Streaming.step` is exactly
one firing.

The construction is the tree's framed machines (`HEOnTheStep.FramedMachines`): a machine with
a world, a control and a stack of frames is strongly bisimilar to the step restricted to its
rules when each transition touches only the frames it pops. For PeTTa:

* the **stack is the agenda**: the pending alternatives and the closing markers of `collapse`,
  `once` and the dynamic-call handler, newest first;
* the **world** is what every alternative shares: the effect state with input, output and
  supply, the answers so far, and the next boundary;
* the control is trivial; answers are part of the world, since a PeTTa answer is published
  while alternatives are still pending.

* `step_framed`: a transition pops a prefix of the agenda and pushes jobs in its place, and
  is the same transition over every other rest of the agenda. The prefix is one job, or
  reaches to the marker the transition looks for (the collection a `collapse` answer joins,
  the `once` marker its first answer cuts to, the handler a fault unwinds to).
* `machine_local`, `streaming_bisimulation`: so the machine is local, and representation is a
  strong bisimulation between the step restricted to its rules and `Streaming.step`
  (`step_iff`).
* `streaming_stuck_iff`, `streaming_divergence_iff`: a store has no firing exactly when the
  machine has no transition, and infinite executions correspond.
* `world_readout`: the answers so far and the effect state are read off the store's one world
  occurrence.

Positive and negative examples: `Controls.markerless_once_answer_is_stuck` (an answer under a
`once` frame whose marker is not on the agenda has no transition, whatever is appended below:
the transition looks for its marker and nothing else) and `Controls.empty_agenda_is_stuck`.

Not here: that the machine's text-level evaluation (`Streaming.enter`, parsing) is PeTTa's;
the adequacy of `Unifying.step`, which this machine calls for each source phase and which
stays one firing here whatever it computes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StreamingOnTheStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open DialectsAsStrategies.HEOnTheStep
open FragmentsOfTheStep.TransitionMaps (IsBisimulation)
open Unifying (Answer Control)
open Streaming (World Frame Task Job State)
open List.FirstSelection (after? After Change)

/-! ## First selections over a longer list -/

section Lists

variable {α : Type}

theorem after_append {selected : α → Bool} {source suffix : List α}
    (found : after? selected source = some suffix) (base : List α) :
    after? selected (source ++ base) = some (suffix ++ base) := by
  induction source with
  | nil => cases found
  | cons first rest ih =>
      cases choice : selected first with
      | true =>
          simp only [after?, choice, ↓reduceIte, Option.some.injEq] at found
          subst found
          simp [after?, choice]
      | false =>
          simp only [after?, choice, Bool.false_eq_true, ↓reduceIte] at found
          simp [after?, choice, ih found]

theorem change_append {replace : α → Option α} {source changed : List α}
    (found : List.FirstSelection.change? replace source = some changed) (base : List α) :
    List.FirstSelection.change? replace (source ++ base) = some (changed ++ base) := by
  induction source generalizing changed with
  | nil => cases found
  | cons first rest ih =>
      cases replacement : replace first with
      | some next =>
          simp only [List.FirstSelection.change?, replacement, Option.some.injEq] at found
          subst found
          simp [List.FirstSelection.change?, replacement]
      | none =>
          simp only [List.FirstSelection.change?, replacement, Option.map_eq_some_iff] at found
          obtain ⟨inner, computed, rfl⟩ := found
          simp [List.FirstSelection.change?, replacement, ih computed]

/-- A front none of whose items is selected is passed over. -/
theorem after_quiet {selected : α → Bool} (front rest : List α)
    (quiet : ∀ item ∈ front, selected item = false) :
    after? selected (front ++ rest) = after? selected rest := by
  induction front with
  | nil => rfl
  | cons first more ih =>
      simp only [List.cons_append, after?, quiet first List.mem_cons_self, Bool.false_eq_true,
        ↓reduceIte]
      exact ih fun item member => quiet item (List.mem_cons_of_mem _ member)

/-- A front none of whose items is changed is kept. -/
theorem change_quiet {replace : α → Option α} (front rest : List α)
    (quiet : ∀ item ∈ front, replace item = none) :
    List.FirstSelection.change? replace (front ++ rest) = (List.FirstSelection.change? replace rest).map (front ++ ·) := by
  induction front with
  | nil => simp
  | cons first more ih =>
      have kept := ih fun item member => quiet item (List.mem_cons_of_mem _ member)
      simp only [List.cons_append, List.FirstSelection.change?, quiet first List.mem_cons_self,
        kept, Option.map_map]
      rfl

end Lists

/-! ## The pieces of a transition -/

theorem laterAnswers_append (answers : List Answer) (frames : List Frame) (older : List Job) :
    Streaming.laterAnswers answers frames older =
      Streaming.laterAnswers answers frames [] ++ older := by
  cases answers <;> rfl

/-- The jobs `laterAnswers` puts in front are neither markers nor collections. -/
theorem laterAnswers_quiet (answers : List Answer) (frames : List Frame) :
    ∀ job ∈ Streaming.laterAnswers answers frames [],
      (∀ key answer, Streaming.collectionChange key answer job = none) ∧
        (∀ key, Streaming.firstMarker key job = false) := by
  intro job member
  cases answers with
  | nil => cases member
  | cons first rest =>
      simp only [Streaming.laterAnswers, List.mem_singleton] at member
      subst member
      exact ⟨fun _ _ => rfl, fun _ => rfl⟩

/-- Importing a source phase puts jobs in front of the older ones and looks at nothing else. -/
theorem enqueuePhase_framed (world : World) (answers : List Answer) (boundary : Nat)
    (after : Unifying.Configuration) (caller : List Frame) (front older : List Job)
    (agenda : List Job) (result : State)
    (computed : Streaming.enqueuePhase ⟨world, agenda, answers, boundary⟩ after caller
      (front ++ older) = some result) :
    ∃ push, result.agenda = push ++ older ∧
      ∀ (other agenda' : List Job),
        Streaming.enqueuePhase ⟨world, agenda', answers, boundary⟩ after caller
          (front ++ other) = some { result with agenda := push ++ other } := by
  unfold Streaming.enqueuePhase at computed ⊢
  split at computed
  · cases computed
    exact ⟨_ :: front, rfl, fun other agenda' => by simp [*]⟩
  · cases computed
    exact ⟨_ :: _ :: front, rfl, fun other agenda' => by simp [*, Streaming.openCollection]⟩
  · cases computed
    exact ⟨_ :: _ :: front, rfl, fun other agenda' => by simp [*, Streaming.openHandler]⟩
  · cases computed
  · cases computed
    exact ⟨_ :: front, rfl, fun other agenda' => by simp [*]⟩
  · cases computed

/-- Returning one answer pops the older jobs up to the marker it looks for, if it looks for
one, and is the same over every other rest. -/
theorem returnAnswer_framed (registry : SpaceSemantics.Program) (world : World)
    (answers : List Answer) (boundary : Nat) (agenda : List Job) (answer : Answer)
    (frames : List Frame) (front older : List Job) (result : State)
    (quiet : ∀ job ∈ front,
      (∀ key value, Streaming.collectionChange key value job = none) ∧
        (∀ key, Streaming.firstMarker key job = false))
    (computed : Streaming.returnAnswer registry ⟨world, agenda, answers, boundary⟩ answer frames
      (front ++ older) = some result) :
    ∃ pop push base, older = pop ++ base ∧ result.agenda = push ++ base ∧
      ∀ (other agenda' : List Job),
        Streaming.returnAnswer registry ⟨world, agenda', answers, boundary⟩ answer frames
          (front ++ (pop ++ other)) = some { result with agenda := push ++ other } := by
  cases frames with
  | nil =>
      simp only [Streaming.returnAnswer, Option.some.injEq] at computed
      subst computed
      exact ⟨[], front, older, rfl, rfl, fun other agenda' => by simp [Streaming.returnAnswer]⟩
  | cons frame caller =>
      cases frame with
      | source inner =>
          simp only [Streaming.returnAnswer, Option.bind_eq_bind, Option.bind_eq_some_iff]
            at computed
          obtain ⟨after, stepped, queued⟩ := computed
          obtain ⟨push, shape, uniform⟩ := enqueuePhase_framed world answers boundary after
            caller front older agenda result queued
          refine ⟨[], push, older, rfl, shape, fun other agenda' => ?_⟩
          simp only [Streaming.returnAnswer, Option.bind_eq_bind, List.nil_append]
          have stepped' : Unifying.step registry
              ((⟨world, agenda', answers, boundary⟩ : State).world.configuration
                (.returned [answer]) [inner]) = some after := stepped
          rw [stepped']
          exact uniform other agenda'
      | collection key =>
          simp only [Streaming.returnAnswer, Streaming.collectAnswer,
            change_quiet front older fun job member => (quiet job member).1 key answer,
            Option.map_map, Option.map_eq_some_iff] at computed
          obtain ⟨changed, found, rfl⟩ := computed
          obtain ⟨before, first, next, rest, rfl, rfl, replaced, untouched⟩ :=
            (List.FirstSelection.change_sound _ _ _ found).prefix
          refine ⟨before ++ [first], front ++ (before ++ [next]), rest, by simp, by simp,
            fun other agenda' => ?_⟩
          have here : List.FirstSelection.change? (Streaming.collectionChange key answer)
              (before ++ first :: other) = some (before ++ next :: other) := by
            rw [change_quiet before (first :: other) untouched]
            simp [List.FirstSelection.change?, replaced]
          simp only [Streaming.returnAnswer, Streaming.collectAnswer,
            change_quiet front _ fun job member => (quiet job member).1 key answer,
            List.append_assoc, List.singleton_append, here, Option.map_some]
          rfl
      | handler key =>
          simp only [Streaming.returnAnswer, Option.some.injEq] at computed
          subst computed
          exact ⟨[], _ :: front, older, rfl, rfl,
            fun other agenda' => by simp [Streaming.returnAnswer]⟩
      | first key =>
          simp only [Streaming.returnAnswer,
            after_quiet front older fun job member => (quiet job member).2 key,
            Option.map_eq_some_iff] at computed
          obtain ⟨remaining, found, rfl⟩ := computed
          obtain ⟨before, chosen, rfl, selected, passed⟩ :=
            (List.FirstSelection.after_sound _ _ _ found).prefix
          refine ⟨before ++ [chosen], [_], remaining, by simp, rfl, fun other agenda' => ?_⟩
          have here : after? (Streaming.firstMarker key) (before ++ chosen :: other) =
              some other := by
            rw [after_quiet before (chosen :: other) passed]
            simp [after?, selected]
          simp only [Streaming.returnAnswer,
            after_quiet front _ fun job member => (quiet job member).2 key,
            List.append_assoc, List.singleton_append, here, Option.map_some]

/-- A source phase (the step's last case) puts jobs in front of the older ones. -/
theorem phase_framed (registry : SpaceSemantics.Program) (world : World)
    (answers : List Answer) (boundary : Nat) (control : Control) (frames : List Frame)
    (older agenda : List Job) (result : State)
    (computed : (do
        let after ← Unifying.step registry
          ((⟨world, agenda, answers, boundary⟩ : State).world.configuration control)
        Streaming.enqueuePhase ⟨world, agenda, answers, boundary⟩ after frames older) =
      some result) :
    ∃ push, result.agenda = push ++ older ∧
      ∀ (other agenda' : List Job), (do
          let after ← Unifying.step registry
            ((⟨world, agenda', answers, boundary⟩ : State).world.configuration control)
          Streaming.enqueuePhase ⟨world, agenda', answers, boundary⟩ after frames other) =
        some { result with agenda := push ++ other } := by
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at computed
  obtain ⟨after, stepped, queued⟩ := computed
  obtain ⟨push, shape, uniform⟩ := enqueuePhase_framed world answers boundary after frames []
    older agenda result queued
  refine ⟨push, shape, fun other agenda' => ?_⟩
  have stepped' : Unifying.step registry
      ((⟨world, agenda', answers, boundary⟩ : State).world.configuration control) =
        some after := stepped
  simp only [Option.bind_eq_bind, stepped', Option.bind_some]
  exact uniform other agenda'

/-- Evaluating an expression that is neither a `collapse` nor a `once` is a source phase. -/
theorem step_evaluate_other (registry : SpaceSemantics.Program) (world : World)
    (answers : List Answer) (boundary : Nat) (bindings : Subst) (expression : Atom)
    (frames : List Frame) (older : List Job)
    (notCollapse : ∀ inner, expression ≠ .expression [.symbol "collapse", inner])
    (notOnce : ∀ inner, expression ≠ .expression [.symbol "once", inner]) :
    Streaming.step registry
        ⟨world, .execute ⟨.evaluate bindings expression, frames⟩ :: older, answers, boundary⟩ =
      (do
        let after ← Unifying.step registry
          ((⟨world, .execute ⟨.evaluate bindings expression, frames⟩ :: older, answers,
            boundary⟩ : State).world.configuration (.evaluate bindings expression))
        Streaming.enqueuePhase
          ⟨world, .execute ⟨.evaluate bindings expression, frames⟩ :: older, answers, boundary⟩
          after frames older) := by
  simp only [Streaming.step]
  split <;> first
    | rfl
    | (rename_i heq; cases heq; exact absurd rfl (notCollapse _))
    | (rename_i heq; cases heq; exact absurd rfl (notOnce _))
    | (rename_i heq; cases heq)

/-! ## A transition touches a prefix of the agenda -/

/-- **A transition pops a prefix of the agenda and pushes jobs in its place, and is the same
transition over every other rest of the agenda.** -/
theorem step_framed (registry : SpaceSemantics.Program) (world : World)
    (answers : List Answer) (boundary : Nat) (agenda : List Job) (result : State)
    (computed : Streaming.step registry ⟨world, agenda, answers, boundary⟩ = some result) :
    ∃ pop push base, agenda = pop ++ base ∧ result.agenda = push ++ base ∧
      ∀ other : List Job,
        Streaming.step registry ⟨world, pop ++ other, answers, boundary⟩ =
          some { result with agenda := push ++ other } := by
  cases agenda with
  | nil => simp [Streaming.step] at computed
  | cons job older =>
      cases job with
      | collect key bindings caller collected =>
          simp only [Streaming.step, Option.some.injEq] at computed
          subst computed
          exact ⟨[_], [_], older, rfl, rfl, fun other => by simp [Streaming.step]⟩
      | handler key =>
          simp only [Streaming.step, Option.some.injEq] at computed
          subst computed
          exact ⟨[_], [], older, rfl, rfl, fun other => by simp [Streaming.step]⟩
      | first key =>
          simp only [Streaming.step, Option.some.injEq] at computed
          subst computed
          exact ⟨[_], [], older, rfl, rfl, fun other => by simp [Streaming.step]⟩
      | execute task =>
          obtain ⟨control, frames⟩ := task
          cases control with
          | returned pending =>
              cases pending with
              | nil =>
                  simp only [Streaming.step, Option.some.injEq] at computed
                  subst computed
                  exact ⟨[_], [], older, rfl, rfl, fun other => by simp [Streaming.step]⟩
              | cons answer later =>
                  simp only [Streaming.step] at computed
                  rw [laterAnswers_append] at computed
                  obtain ⟨pop, push, base, rfl, shape, uniform⟩ := returnAnswer_framed registry
                    world answers boundary _ answer frames _ older result
                    (laterAnswers_quiet later frames) computed
                  refine ⟨Job.execute ⟨.returned (answer :: later), frames⟩ :: pop, push, base,
                    rfl, shape, fun other => ?_⟩
                  simp only [List.cons_append, Streaming.step]
                  rw [laterAnswers_append]
                  exact uniform other _
          | sequence controls later =>
              simp only [Streaming.step, Option.some.injEq] at computed
              subst computed
              refine ⟨[_], Streaming.laterAnswers later frames [] ++
                  controls.map (fun item => Job.execute ⟨item, frames⟩), older, rfl, ?_,
                fun other => ?_⟩
              · show Streaming.laterAnswers later frames _ = _
                rw [laterAnswers_append]
                simp
              · simp only [List.singleton_append, Streaming.step]
                rw [laterAnswers_append]
                simp
          | fault reason =>
              simp only [Streaming.step, Option.bind_eq_bind, Option.bind_eq_some_iff,
                Option.some.injEq] at computed
              obtain ⟨key, handled, remaining, found, rfl⟩ := computed
              obtain ⟨before, chosen, rfl, selected, passed⟩ :=
                (List.FirstSelection.after_sound _ _ _ found).prefix
              refine ⟨Job.execute ⟨.fault reason, frames⟩ :: (before ++ [chosen]), [], remaining,
                by simp, rfl, fun other => ?_⟩
              have here : after? (Streaming.handlerMarker key) (before ++ chosen :: other) =
                  some other := by
                rw [after_quiet before (chosen :: other) passed]
                simp [after?, selected]
              simp [Streaming.step, handled, here]
          | dynamic bindings head values =>
              simp only [Streaming.step] at computed
              obtain ⟨push, shape, uniform⟩ := phase_framed registry world answers boundary _
                frames older _ result computed
              exact ⟨[_], push, older, rfl, shape, fun other => by
                simpa only [List.singleton_append, Streaming.step] using uniform other _⟩
          | arguments bindings target remaining values index =>
              simp only [Streaming.step] at computed
              obtain ⟨push, shape, uniform⟩ := phase_framed registry world answers boundary _
                frames older _ result computed
              exact ⟨[_], push, older, rfl, shape, fun other => by
                simpa only [List.singleton_append, Streaming.step] using uniform other _⟩
          | evaluate bindings expression =>
              by_cases collapse : ∃ inner, expression = .expression [.symbol "collapse", inner]
              · obtain ⟨inner, rfl⟩ := collapse
                simp only [Streaming.step, Option.some.injEq] at computed
                subst computed
                exact ⟨[_], [_, _], older, rfl, rfl,
                  fun other => by simp [Streaming.step, Streaming.openCollection]⟩
              · by_cases once : ∃ inner, expression = .expression [.symbol "once", inner]
                · obtain ⟨inner, rfl⟩ := once
                  simp only [Streaming.step, Option.some.injEq] at computed
                  subst computed
                  exact ⟨[_], [_, _], older, rfl, rfl,
                    fun other => by simp [Streaming.step, Streaming.openFirst]⟩
                · have notCollapse : ∀ inner,
                      expression ≠ .expression [.symbol "collapse", inner] :=
                    fun inner same => collapse ⟨inner, same⟩
                  have notOnce : ∀ inner, expression ≠ .expression [.symbol "once", inner] :=
                    fun inner same => once ⟨inner, same⟩
                  rw [step_evaluate_other registry world answers boundary bindings expression
                    frames older notCollapse notOnce] at computed
                  obtain ⟨push, shape, uniform⟩ := phase_framed registry world answers boundary _
                    frames older _ result computed
                  refine ⟨[_], push, older, rfl, shape, fun other => ?_⟩
                  rw [List.singleton_append, step_evaluate_other registry world answers boundary
                    bindings expression frames other notCollapse notOnce]
                  exact uniform other _

/-! ## The framed machine -/

/-- What every pending alternative shares: the effect world, the answers so far, and the
next boundary. -/
structure Shared where
  world : World
  answers : List Answer
  nextBoundary : Nat

/-- **PeTTa's streaming machine as a framed machine**: the stack is the agenda. -/
def machine (registry : SpaceSemantics.Program) : FramedMachine Shared PUnit Job Empty where
  transition := fun shared before shared' pending =>
    Streaming.step registry ⟨shared.world, before.2, shared.answers, shared.nextBoundary⟩ =
      some ⟨shared'.world, pending.2, shared'.answers, shared'.nextBoundary⟩
  publish := fun _ => none

/-- A machine state as a configuration of the framed machine. -/
def configOf (state : State) : Config Shared PUnit Job Empty :=
  ⟨⟨state.world, state.answers, state.nextBoundary⟩, PUnit.unit, state.agenda, []⟩

/-- **The framed machine's steps are the streaming machine's transitions.** -/
theorem step_iff (registry : SpaceSemantics.Program) (before after : State) :
    (machine registry).Step (configOf before) (configOf after) ↔
      Streaming.step registry before = some after := by
  constructor
  · intro step
    generalize source : configOf before = x at step
    generalize target : configOf after = y at step
    cases step with
    | internal transition =>
        cases source
        cases target
        exact transition
    | publish published => cases published
  · intro computed
    exact FramedMachine.Step.internal (M := machine registry) computed

/-- **The machine is local**: every transition pops some jobs, pushes some, and is the same
over every other rest of the agenda. -/
theorem machine_local (registry : SpaceSemantics.Program) : (machine registry).Local := by
  intro shared shared' control control' stack stack' transition
  obtain ⟨pop, push, base, rfl, shape, uniform⟩ := step_framed registry shared.world
    shared.answers shared.nextBoundary stack _ transition
  exact ⟨pop, push, base, rfl, shape, fun other => uniform other⟩

/-- **PeTTa's streaming machine on the step.** Representation is a strong bisimulation
between the step restricted to the machine's rules and the machine: every firing from a
store that represents a configuration is a transition from it, every transition is one
firing, and the results represent each other. -/
theorem streaming_bisimulation (registry : SpaceSemantics.Program) :
    IsBisimulation (StoreStep (machine registry)) (machine registry).Step Represents :=
  bisimulation (machine_local registry)

/-- A store has no firing exactly when the machine has no transition. -/
theorem streaming_stuck_iff (registry : SpaceSemantics.Program)
    {store : Store Shared PUnit Job Empty} {configuration : Config Shared PUnit Job Empty}
    (represented : Represents store configuration) :
    (∀ next, ¬ StoreStep (machine registry) store next) ↔
      ∀ next, ¬ (machine registry).Step configuration next :=
  stuck_iff (machine_local registry) represented

/-- Infinite executions of the step under the machine's rules and of the machine
correspond. -/
theorem streaming_divergence_iff (registry : SpaceSemantics.Program)
    {store : Store Shared PUnit Job Empty} {configuration : Config Shared PUnit Job Empty}
    (represented : Represents store configuration) :
    (∃ stores : ℕ → Store Shared PUnit Job Empty, stores 0 = store ∧
        ∀ n, StoreStep (machine registry) (stores n) (stores (n + 1))) ↔
      ∃ configurations : ℕ → Config Shared PUnit Job Empty, configurations 0 = configuration ∧
        ∀ n, (machine registry).Step (configurations n) (configurations (n + 1)) :=
  divergence_iff (machine_local registry) represented

/-- **The answers and the effect world are read off the store**: a store that represents a
machine state holds exactly one world occurrence, with that state's world, answers and next
boundary. -/
theorem world_readout {store : Store Shared PUnit Job Empty} (state : State)
    (represented : Represents store (configOf state)) :
    worldsOf (Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.labels Prod.fst
        store.present) =
      {(⟨state.world, state.answers, state.nextBoundary⟩ : Shared)} := by
  rw [represented.2, worldsOf_encode]
  rfl

namespace Controls

/-- Negative: with an empty agenda the machine has no transition. -/
theorem empty_agenda_is_stuck (registry : SpaceSemantics.Program) (world : World)
    (answers : List Answer) (boundary : Nat) :
    Streaming.step registry ⟨world, [], answers, boundary⟩ = none := rfl

/-- Negative: an answer under a `once` frame whose marker is not on the agenda has no
transition, and appending jobs that are not that marker does not give it one: the transition
looks for its marker and for nothing else. -/
theorem markerless_once_answer_is_stuck (registry : SpaceSemantics.Program) (world : World)
    (answer : Answer) (below : List Job)
    (unmarked : ∀ job ∈ below, Streaming.firstMarker 7 job = false) :
    Streaming.step registry
      ⟨world, .execute ⟨.returned [answer], [.first 7]⟩ :: below, [], 0⟩ = none := by
  have none : after? (Streaming.firstMarker 7) below = none := by
    induction below with
    | nil => rfl
    | cons first rest ih =>
        simp only [after?, unmarked first List.mem_cons_self, Bool.false_eq_true, ↓reduceIte]
        exact ih fun job member => unmarked job (List.mem_cons_of_mem _ member)
  simp [Streaming.step, Streaming.returnAnswer, Streaming.laterAnswers, none]

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.StreamingOnTheStep
