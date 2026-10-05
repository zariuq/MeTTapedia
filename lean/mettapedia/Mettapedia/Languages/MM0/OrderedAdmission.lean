import Mettapedia.Languages.MM0.Kernel.TheoryAdmission
import Mettapedia.Languages.MM0.ServiceInferenceCache
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.GSLT.Distinction.RunOutcomes

/-!
# MM0 admission under the ordered, progress-aware observer

An abstract instance of the MM0 service's state for the ordered observation and
progress theory of `ProductiveBlocks`.  The service admits a decoded stream of
declarations with the kernel's own `Theory.step?`; a malformed item is a fault.

* **Four outcomes** (`admissionMachine`).  A complete run is accepted with its
  resulting theory, refused at the first unauthorized declaration, or faulted
  at a malformed item; a run whose fuel ends first is exhausted.
* **Authorized updates** (`accepted_run`, `accepted_iff`,
  `published_authorized`).  Every published theory update is an authorized
  kernel step from the theory before it, and an accepted run publishes exactly
  the declarations of a kernel run, in order.
* **Exhaustion is not refusal** (`exhaustion_is_not_refusal`).  A run that the
  kernel accepts is incomplete at every fuel below its length, and never
  refused at any fuel.
* **Equal occurrences are kept** (`duplicate_declaration_refused`,
  `set_observer_unsound`).  A repeated declaration is a second occurrence that
  the kernel refuses; a second matching table row turns a unique lookup into a
  malformed one while the set of rows is unchanged, so a set observer of the
  rows would be unsound.
* **Checker and interpreter, related by a relation** (`checker_interpreter`,
  `interpreter_fuel_bound`, `checker_interpreter_final`).  An interpreter that
  decodes each declaration in an administrative step is related to the checker
  by a relation that is not a function, with an explicit cost bound of two
  interpreter steps per checker step forward and one backward.  Final
  observations coincide, and the interpreter's fuel is bounded by twice the
  checker's, not assumed equal.  An interpreter that decodes silently forever
  never completes and is related to no checker
  (`spinning_interpreter_never_completes`, `spinning_interpreter_not_simulated`).

This is the abstract state of the service. The emitted MeTTa program's
correspondence with the checker is `Presentation.MeTTaExecution`; connecting its
interpreter states to this relation is a separate realization obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.OrderedAdmission

open Kernel
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Dynamics.OrderedDemand (Event Status Observation)

/-- The verdict of a complete admission run. -/
inductive Verdict where
  | accepted (theory : Theory)
  | refused (admission : Admission)

/-- Ordered events: an authorized theory update is a committed effect, and a
malformed item is a fault. -/
abbrev AdmissionEvent := Event Empty Admission Unit

/-- The admission state: the current theory and the decoded items still to
admit (`none` is a malformed item). -/
abbrev AdmissionState := Theory × List (Option Admission)

/-- **The admission machine**: the kernel's `Theory.step?` on each item. -/
def admissionMachine : Machine AdmissionState AdmissionEvent Verdict Empty where
  step
    | (theory, []) => some (.finish (.accepted theory))
    | (_, none :: _) => some (.fail [.fault ()])
    | (theory, some admission :: rest) =>
        match theory.step? admission with
        | some next => some (.publish [.effect admission] (next, rest))
        | none => some (.finish (.refused admission))

theorem step_done (theory : Theory) :
    admissionMachine.step (theory, []) = some (.finish (.accepted theory)) :=
  rfl

theorem step_malformed (theory : Theory) (rest : List (Option Admission)) :
    admissionMachine.step (theory, none :: rest) = some (.fail [.fault ()]) :=
  rfl

theorem step_admitted {theory next : Theory} {admission : Admission} {rest : List (Option Admission)}
    (found : theory.step? admission = some next) :
    admissionMachine.step (theory, some admission :: rest) =
      some (.publish [.effect admission] (next, rest)) := by
  simp [admissionMachine, found]

theorem step_refused {theory : Theory} {admission : Admission} {rest : List (Option Admission)}
    (found : theory.step? admission = none) :
    admissionMachine.step (theory, some admission :: rest) = some (.finish (.refused admission)) := by
  simp [admissionMachine, found]

/-- The admission machine has no administrative steps and no stuck state. -/
def admissionProductive : admissionMachine.Productive where
  rank _ := 0
  silent_decreases := by
    intro state next stepped
    rcases state with ⟨theory, _ | ⟨_ | admission, rest⟩⟩
    · simp [admissionMachine] at stepped
    · simp [admissionMachine] at stepped
    · cases found : theory.step? admission <;> simp [admissionMachine, found] at stepped
  moves state := by
    rcases state with ⟨theory, _ | ⟨_ | admission, rest⟩⟩
    · simp [admissionMachine]
    · simp [admissionMachine]
    · cases found : theory.step? admission <;> simp [admissionMachine, found]

/-- **An accepted kernel run is published in order and accepted.** -/
theorem accepted_run {theory final : Theory} {admissions : List Admission}
    (runs : Theory.Runs theory admissions final) :
    admissionMachine.run (admissions.length + 1) (theory, admissions.map some) =
      (admissions.map .effect, .finished (.accepted final)) := by
  induction runs with
  | nil theory => rfl
  | @cons before middle after head tail step _ ih =>
      have accepted : before.step? head = some middle := (Theory.step_eq_some_iff _ _ _).mpr step
      rw [List.length_cons, List.map_cons, admissionMachine.run_succ_publish (step_admitted accepted), ih]
      rfl

/-- **Acceptance is exactly a kernel run**, at some fuel. -/
theorem accepted_iff (theory final : Theory) (admissions : List Admission) :
    (∃ fuel events, admissionMachine.run fuel (theory, admissions.map some) =
      (events, .finished (.accepted final))) ↔ Theory.Runs theory admissions final := by
  constructor
  · rintro ⟨fuel, events, ran⟩
    induction admissions generalizing theory fuel events with
    | nil =>
        cases fuel with
        | zero => simp [Machine.run] at ran
        | succ fuel =>
            rw [List.map_nil, admissionMachine.run_succ_finish (step_done theory)] at ran
            simp only [Prod.mk.injEq, Outcome.finished.injEq, Verdict.accepted.injEq] at ran
            rw [← ran.2]
            exact .nil theory
    | cons head tail ih =>
        cases fuel with
        | zero => simp [Machine.run] at ran
        | succ fuel =>
            cases found : theory.step? head with
            | none =>
                rw [List.map_cons, admissionMachine.run_succ_finish (step_refused found)] at ran
                simp at ran
            | some middle =>
                rw [List.map_cons, admissionMachine.run_succ_publish (step_admitted found)] at ran
                have second : (admissionMachine.run fuel (middle, tail.map some)).2 =
                    .finished (.accepted final) := congrArg Prod.snd ran
                exact .cons ((Theory.step_eq_some_iff _ _ _).mp found)
                  (ih middle fuel _ (Prod.ext rfl second))
  · intro runs
    exact ⟨_, _, accepted_run runs⟩

/-- The theory updates among published events. -/
def updates (events : List AdmissionEvent) : List Admission :=
  events.filterMap fun
    | .effect admission => some admission
    | _ => none

/-- **Every published theory update is authorized**: the updates published by
any finite run form a kernel run from the initial theory. -/
theorem published_authorized (fuel : ℕ) (state : AdmissionState) :
    ∃ middle, Theory.Runs state.1 (updates (admissionMachine.run fuel state).1) middle := by
  induction fuel generalizing state with
  | zero => exact ⟨state.1, .nil _⟩
  | succ fuel ih =>
      rcases state with ⟨theory, _ | ⟨_ | admission, rest⟩⟩
      · rw [admissionMachine.run_succ_finish (step_done theory)]
        exact ⟨theory, .nil theory⟩
      · rw [admissionMachine.run_succ_fail (step_malformed theory rest)]
        exact ⟨theory, .nil theory⟩
      · cases found : theory.step? admission with
        | none =>
            rw [admissionMachine.run_succ_finish (step_refused found)]
            exact ⟨theory, .nil theory⟩
        | some middle =>
            obtain ⟨final, runs⟩ := ih (middle, rest)
            rw [admissionMachine.run_succ_publish (step_admitted found)]
            exact ⟨final, .cons ((Theory.step_eq_some_iff _ _ _).mp found) runs⟩

/-- **Exhaustion is not refusal**: a run that the kernel accepts is incomplete
at every fuel below its length, and is never refused. -/
theorem exhaustion_is_not_refusal {theory final : Theory} {admissions : List Admission}
    (runs : Theory.Runs theory admissions final) :
    (∀ fuel ≤ admissions.length,
      (admissionMachine.observe fuel (theory, admissions.map some)).status = .incomplete) ∧
      ∀ fuel admission, (admissionMachine.run fuel (theory, admissions.map some)).2 ≠
        .finished (.refused admission) := by
  constructor
  · intro fuel bound
    induction runs generalizing fuel with
    | nil theory =>
        have zero : fuel = 0 := by simpa using bound
        subst zero
        rfl
    | @cons before middle after head tail step _ ih =>
        have accepted : before.step? head = some middle := (Theory.step_eq_some_iff _ _ _).mpr step
        cases fuel with
        | zero => rfl
        | succ fuel =>
            have later := ih fuel (by simpa using bound)
            simp only [Machine.observe] at later ⊢
            rw [List.map_cons, admissionMachine.run_succ_publish (step_admitted accepted)]
            exact later
  · intro fuel admission
    exact admissionMachine.finished_unique (theory, admissions.map some)
      (congrArg Prod.snd (accepted_run runs)) (other := .refused admission)
      (fun impossible => nomatch impossible) fuel

/-! ## Equal occurrences -/

/-- A sort declaration. -/
def sortZero : Admission := .sort 0 {}

/-- **A repeated declaration is a second occurrence**, published once and then
refused: equal occurrences are processed separately. -/
theorem duplicate_declaration_refused :
    admissionMachine.run 3 ({}, [some sortZero, some sortZero]) =
      ([.effect sortZero], .finished (.refused sortZero)) := by
  rfl

open ServiceInferenceCache in
/-- **A set observer of table rows is unsound**: a second matching row turns a
unique lookup into a malformed one, while the set of rows is unchanged. -/
theorem set_observer_unsound :
    let row : Row := (0, ⟨[], 0, ∅⟩)
    lookupRows [row, row] 0 = .malformed ∧ lookupRows [row] 0 = .present ⟨[], 0, ∅⟩ ∧
      ∀ other, other ∈ [row, row] ↔ other ∈ [row] := by
  refine ⟨rfl, rfl, fun other => by simp⟩

/-! ## Checker and interpreter, related by a relation -/

/-- An interpreter that decodes each item in an administrative step before
running the checker's step on it.  The flag records that the head is decoded. -/
def interpreterMachine : Machine (Theory × List (Option Admission) × Bool) AdmissionEvent Verdict Empty where
  step
    | (theory, items, false) => some (.silent (theory, items, true))
    | (theory, [], true) => some (.finish (.accepted theory))
    | (_, none :: _, true) => some (.fail [.fault ()])
    | (theory, some admission :: rest, true) =>
        match theory.step? admission with
        | some next => some (.publish [.effect admission] (next, rest, false))
        | none => some (.finish (.refused admission))

/-- The relation: the same theory and items, whatever the decoding flag.  It is
not a function: each checker state has two related interpreter states. -/
def related (state : AdmissionState) (state' : Theory × List (Option Admission) × Bool) : Prop :=
  state'.1 = state.1 ∧ state'.2.1 = state.2

private theorem decoded_run (theory : Theory) (items : List (Option Admission)) (fuel : ℕ) :
    interpreterMachine.run (fuel + 1) (theory, items, false) =
      interpreterMachine.run fuel (theory, items, true) :=
  rfl

/-- **Forward: every checker step is matched by at most two interpreter steps.** -/
theorem checker_interpreter : CostSimulation admissionMachine interpreterMachine related 2 where
  silent := by
    intro state _ next _ stepped
    rcases state with ⟨theory, _ | ⟨_ | admission, rest⟩⟩
    · simp [admissionMachine] at stepped
    · simp [admissionMachine] at stepped
    · cases found : theory.step? admission <;> simp [admissionMachine, found] at stepped
  publish := by
    rintro ⟨theory, items⟩ ⟨theory', items', decoded⟩ events next relatedStates stepped
    obtain ⟨sameTheory, sameItems⟩ : theory' = theory ∧ items' = items := relatedStates
    subst theory'
    subst items'
    rcases items with _ | ⟨_ | admission, rest⟩
    · simp [admissionMachine] at stepped
    · simp [admissionMachine] at stepped
    · cases found : theory.step? admission with
      | none => simp [admissionMachine, found] at stepped
      | some middle =>
          simp only [admissionMachine, found, Option.some.injEq, Transition.publish.injEq] at stepped
          obtain ⟨rfl, rfl⟩ := stepped
          cases decoded with
          | false =>
              exact ⟨2, le_rfl, (middle, rest, false),
                by simp [Machine.run, interpreterMachine, found], rfl, rfl⟩
          | true =>
              exact ⟨1, by omega, (middle, rest, false),
                by simp [Machine.run, interpreterMachine, found], rfl, rfl⟩
  finish := by
    rintro ⟨theory, items⟩ ⟨theory', items', decoded⟩ verdict relatedStates stepped
    obtain ⟨sameTheory, sameItems⟩ : theory' = theory ∧ items' = items := relatedStates
    subst theory'
    subst items'
    rcases items with _ | ⟨_ | admission, rest⟩
    · simp only [admissionMachine, Option.some.injEq, Transition.finish.injEq] at stepped
      subst stepped
      cases decoded with
      | false => exact ⟨2, le_rfl, rfl⟩
      | true => exact ⟨1, by omega, rfl⟩
    · simp [admissionMachine] at stepped
    · cases found : theory.step? admission with
      | some middle => simp [admissionMachine, found] at stepped
      | none =>
          simp only [admissionMachine, found, Option.some.injEq, Transition.finish.injEq] at stepped
          subst stepped
          cases decoded with
          | false => exact ⟨2, le_rfl, by simp [Machine.run, interpreterMachine, found]⟩
          | true => exact ⟨1, by omega, by simp [Machine.run, interpreterMachine, found]⟩
  fail := by
    rintro ⟨theory, items⟩ ⟨theory', items', decoded⟩ events relatedStates stepped
    obtain ⟨sameTheory, sameItems⟩ : theory' = theory ∧ items' = items := relatedStates
    subst theory'
    subst items'
    rcases items with _ | ⟨_ | admission, rest⟩
    · simp [admissionMachine] at stepped
    · simp only [admissionMachine, Option.some.injEq, Transition.fail.injEq] at stepped
      subst stepped
      cases decoded with
      | false => exact ⟨2, le_rfl, rfl⟩
      | true => exact ⟨1, by omega, rfl⟩
    · cases found : theory.step? admission <;> simp [admissionMachine, found] at stepped
  call := by
    intro state _ request _ _ stepped
    rcases state with ⟨theory, _ | ⟨_ | admission, rest⟩⟩
    · simp [admissionMachine] at stepped
    · simp [admissionMachine] at stepped
    · cases found : theory.step? admission <;> simp [admissionMachine, found] at stepped

/-- **Backward: every interpreter step is matched by at most one checker step**;
the decoding step is matched by none. -/
theorem interpreter_checker :
    CostSimulation interpreterMachine admissionMachine (fun state' state => related state state') 1 where
  silent := by
    rintro ⟨theory', items', decoded⟩ ⟨theory, items⟩ next relatedStates stepped
    obtain ⟨sameTheory, sameItems⟩ : theory' = theory ∧ items' = items := relatedStates
    subst theory
    subst items
    cases decoded with
    | false =>
        simp only [interpreterMachine, Option.some.injEq, Transition.silent.injEq] at stepped
        subst stepped
        exact ⟨0, by omega, (theory', items'), rfl, rfl, rfl⟩
    | true =>
        rcases items' with _ | ⟨_ | admission, rest⟩
        · simp [interpreterMachine] at stepped
        · simp [interpreterMachine] at stepped
        · cases found : theory'.step? admission <;> simp [interpreterMachine, found] at stepped
  publish := by
    rintro ⟨theory', items', decoded⟩ ⟨theory, items⟩ events next relatedStates stepped
    obtain ⟨sameTheory, sameItems⟩ : theory' = theory ∧ items' = items := relatedStates
    subst theory
    subst items
    cases decoded with
    | false => simp [interpreterMachine] at stepped
    | true =>
        rcases items' with _ | ⟨_ | admission, rest⟩
        · simp [interpreterMachine] at stepped
        · simp [interpreterMachine] at stepped
        · cases found : theory'.step? admission with
          | none => simp [interpreterMachine, found] at stepped
          | some middle =>
              simp only [interpreterMachine, found, Option.some.injEq,
                Transition.publish.injEq] at stepped
              obtain ⟨rfl, rfl⟩ := stepped
              exact ⟨1, le_rfl, (middle, rest), by simp [Machine.run, admissionMachine, found],
                rfl, rfl⟩
  finish := by
    rintro ⟨theory', items', decoded⟩ ⟨theory, items⟩ verdict relatedStates stepped
    obtain ⟨sameTheory, sameItems⟩ : theory' = theory ∧ items' = items := relatedStates
    subst theory
    subst items
    cases decoded with
    | false => simp [interpreterMachine] at stepped
    | true =>
        rcases items' with _ | ⟨_ | admission, rest⟩
        · simp only [interpreterMachine, Option.some.injEq, Transition.finish.injEq] at stepped
          subst stepped
          exact ⟨1, le_rfl, rfl⟩
        · simp [interpreterMachine] at stepped
        · cases found : theory'.step? admission with
          | some middle => simp [interpreterMachine, found] at stepped
          | none =>
              simp only [interpreterMachine, found, Option.some.injEq,
                Transition.finish.injEq] at stepped
              subst stepped
              exact ⟨1, le_rfl, by simp [Machine.run, admissionMachine, found]⟩
  fail := by
    rintro ⟨theory', items', decoded⟩ ⟨theory, items⟩ events relatedStates stepped
    obtain ⟨sameTheory, sameItems⟩ : theory' = theory ∧ items' = items := relatedStates
    subst theory
    subst items
    cases decoded with
    | false => simp [interpreterMachine] at stepped
    | true =>
        rcases items' with _ | ⟨_ | admission, rest⟩
        · simp [interpreterMachine] at stepped
        · simp only [interpreterMachine, Option.some.injEq, Transition.fail.injEq] at stepped
          subst stepped
          exact ⟨1, le_rfl, rfl⟩
        · cases found : theory'.step? admission <;> simp [interpreterMachine, found] at stepped
  call := by
    rintro ⟨theory', items', decoded⟩ _ request _ _ stepped
    cases decoded with
    | false => simp [interpreterMachine] at stepped
    | true =>
        rcases items' with _ | ⟨_ | admission, rest⟩
        · simp [interpreterMachine] at stepped
        · simp [interpreterMachine] at stepped
        · cases found : theory'.step? admission <;> simp [interpreterMachine, found] at stepped

/-- **An explicit fuel bound**: the interpreter at twice the checker's fuel
observes an extension of the checker's observation. -/
theorem interpreter_fuel_bound (fuel : ℕ) (theory : Theory) (items : List (Option Admission))
    (decoded : Bool) :
    (admissionMachine.observe fuel (theory, items)).Prefix
      (interpreterMachine.observe (2 * fuel) (theory, items, decoded)) :=
  checker_interpreter.observe_prefix fuel ⟨rfl, rfl⟩

/-- **Final observations coincide**: accepted, refused and faulted runs, with
their published updates. -/
theorem checker_interpreter_final (theory : Theory) (items : List (Option Admission))
    (decoded : Bool) {fuel fuel' : ℕ}
    (final : (admissionMachine.observe fuel (theory, items)).status.Final)
    (final' : (interpreterMachine.observe fuel' (theory, items, decoded)).status.Final) :
    admissionMachine.observe fuel (theory, items) =
      interpreterMachine.observe fuel' (theory, items, decoded) :=
  checker_interpreter.final_eq interpreter_checker ⟨rfl, rfl⟩ final final'

/-! ## A spinning interpreter -/

/-- An interpreter whose decoding never ends. -/
def spinningInterpreter : Machine (Theory × List (Option Admission) × Bool) AdmissionEvent Verdict Empty where
  step state := some (.silent state)

theorem spinning_interpreter_never_completes (fuel : ℕ) (state : Theory × List (Option Admission) × Bool) :
    spinningInterpreter.observe fuel state = ⟨[], .incomplete⟩ :=
  spinningInterpreter.silent_region_incomplete (fun _ => True)
    (fun state _ => ⟨state, rfl, trivial⟩) fuel state trivial

/-- **No relation transports an accepting checker step to a spinning
interpreter**, at any cost. -/
theorem spinning_interpreter_not_simulated (relation : AdmissionState →
      Theory × List (Option Admission) × Bool → Prop) (cost : ℕ) (theory : Theory)
    (state' : Theory × List (Option Admission) × Bool) (start : relation (theory, []) state') :
    ¬ CostSimulation admissionMachine spinningInterpreter relation cost := by
  intro simulation
  obtain ⟨k, _, ran⟩ := simulation.finish start (show admissionMachine.step (theory, []) = _ from rfl)
  have spins := spinning_interpreter_never_completes k state'
  have status := congrArg Observation.status spins
  simp only [Machine.observe, ran, Outcome.status] at status
  cases status

end Mettapedia.Languages.MM0.OrderedAdmission
