import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StandingRuleRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairFiringRuns
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.ParkedWakeups

/-!
# Installed candidate-step rules, wakeups and semantic scheduler fairness

Rule definitions are decoded from labels of physical occurrences. Running
one reads its installation in the same ordinary candidate firing. External
candidate firings can install or remove those occurrences. Sleeping changes
only the agenda; a refused or unfinished attempt does not delete a rule.

The index is an explicit parameter with a no-lost-wakeup obligation. A
conservative reference index watches physical-world and equation changes;
the latter is necessary even when no occurrence is changed. No physical
index implementation or source-schema freshening algorithm is assumed.
This module compares the already prepared common-interface profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StandingRuleMachine

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
open StandingRuleRows

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

structure State (T : Type uT) (O : Type uO) where
  world : Configuration T O
  born : Finset O
  history : List (PropagationHistory.Key O O)
  awake : Set O

inductive Label (T : Type uT) (O : Type uO) where
  | env (firing : ConditionalSchedule.Firing T O)
  | run (installation : O) (picked : Selection O)
  | sleep (installation : O)
  | idle

variable (A : SubstitutionAction T S) (label : O → T) (decode : T → Option (Definition T))

def Ready (state : State T O) (installation : O) : Prop :=
  ∃ definition, decode (label installation) = some definition ∧ ∃ picked : Selection O,
    (StandingRuleRows.selection installation picked).Valid A label
      (StandingRuleRows.rule label installation definition.body) state.world ∧
    Disjoint picked.made.toFinset state.born ∧
    StandingRuleRows.Fresh installation definition.mode picked state.history

theorem ready_present {state : State T O} {installation : O}
    (ready : Ready A label decode state installation) : installation ∈ state.world.present := by
  obtain ⟨definition, _, picked, valid, _, _⟩ := ready
  exact (StandingRuleRows.valid_iff A label installation definition.body picked state.world).mp valid |>.1

def Allowed (state : State T O) : Label T O → Prop
  | .env firing => firing.2.Valid A label firing.1 state.world ∧ Disjoint firing.2.made.toFinset state.born
  | .run installation picked =>
      ∃ definition, decode (label installation) = some definition ∧ installation ∈ state.awake ∧
        (StandingRuleRows.selection installation picked).Valid A label
          (StandingRuleRows.rule label installation definition.body) state.world ∧
        Disjoint picked.made.toFinset state.born ∧
        StandingRuleRows.Fresh installation definition.mode picked state.history
  | .sleep installation => installation ∈ state.awake ∧ ¬ Ready A label decode state installation
  | .idle => True

def baseNext (state : State T O) (firing : ConditionalSchedule.Firing T O)
    (history : List (PropagationHistory.Key O O)) : State T O :=
  ⟨firing.2.result label firing.1 state.world, state.born ∪ firing.2.made.toFinset, history, state.awake⟩

variable (index : Configuration T O → ConditionalSchedule.Firing T O → O → Prop)

def advance (state : State T O) (firing : ConditionalSchedule.Firing T O)
    (history : List (PropagationHistory.Key O O)) : State T O :=
  { baseNext label state firing history with
    awake := {installation | installation ∈ (firing.2.result label firing.1 state.world).present ∧
      (installation ∈ state.awake ∨ index state.world firing installation)} }

def next (state : State T O) : Label T O → State T O
  | .env firing => advance label index state firing state.history
  | .run installation picked =>
      match decode (label installation) with
      | none => state
      | some definition => advance label index state
          (StandingRuleRows.rule label installation definition.body, StandingRuleRows.selection installation picked)
          (StandingRuleRows.record installation definition.mode picked state.history)
  | .sleep installation => {state with awake := state.awake \ {installation}}
  | .idle => state

def system : LTS (State T O) (Label T O) := ⟨Allowed A label decode, next label decode index⟩

theorem allowed_world_transition {state : State T O} {event : Label T O}
    (allowed : Allowed A label decode state event) :
    (next label decode index state event).world = state.world ∨
      ∃ body, Step A label body state.world (next label decode index state event).world := by
  cases event with
  | env firing => exact Or.inr ⟨firing.1, firing.2, allowed.1, rfl⟩
  | run installation picked =>
      obtain ⟨definition, decoded, _, valid, _, _⟩ := allowed
      right
      simp only [next, decoded]
      exact ⟨StandingRuleRows.rule label installation definition.body,
        StandingRuleRows.selection installation picked, valid, rfl⟩
  | sleep installation => exact Or.inl rfl
  | idle => exact Or.inl rfl

def NoLostWakeup : Prop :=
  ∀ (state : State T O) (firing : ConditionalSchedule.Firing T O),
    firing.2.Valid A label firing.1 state.world → Disjoint firing.2.made.toFinset state.born →
    ∀ history, (∀ key ∈ state.history, key ∈ history) → ∀ installation,
      ¬ Ready A label decode state installation → Ready A label decode (baseNext label state firing history) installation →
        index state.world firing installation

def referenceIndex (before : Configuration T O) (firing : ConditionalSchedule.Firing T O) (_ : O) : Prop :=
  before.present ≠ (firing.2.result label firing.1 before).present ∨
    before.equations.length ≠ (firing.2.result label firing.1 before).equations.length

/-- A ready row in the later state was fresh in the earlier history and
allocator. A false-to-true change therefore comes from the actual world or
equation update, not merely from scheduler bookkeeping. -/
theorem reference_no_lost_wakeup : NoLostWakeup A label decode (referenceIndex label) := by
  intro state firing valid fresh history historySubset installation asleep awake
  obtain ⟨definition, decoded, picked, readyAfter, freshAfter, historyAfter⟩ := awake
  have notBefore : ¬ (StandingRuleRows.selection installation picked).Valid A label
      (StandingRuleRows.rule label installation definition.body) state.world := by
    intro readyBefore
    exact asleep ⟨definition, decoded, picked, readyBefore,
      Finset.disjoint_of_subset_right Finset.subset_union_left freshAfter,
      StandingRuleRows.fresh_of_history_subset installation definition.mode picked historySubset historyAfter⟩
  exact EquationWakeups.readiness_flip_requires_world_or_equations A label
    (⟨firing.2, valid, rfl⟩ : Step A label firing.1 state.world (firing.2.result label firing.1 state.world))
    (StandingRuleRows.selection installation picked) notBefore readyAfter

structure WakeInv (state : State T O) : Prop where
  present_born : state.world.present ⊆ state.born
  ready_awake : ∀ installation, Ready A label decode state installation → installation ∈ state.awake

theorem ready_advance (adequate : NoLostWakeup A label decode index) {state : State T O}
    (inv : WakeInv A label decode state) {firing : ConditionalSchedule.Firing T O}
    (valid : firing.2.Valid A label firing.1 state.world) (fresh : Disjoint firing.2.made.toFinset state.born)
    {history : List (PropagationHistory.Key O O)} (historySubset : ∀ key ∈ state.history, key ∈ history)
    {installation : O} (ready : Ready A label decode (advance label index state firing history) installation) :
    installation ∈ (advance label index state firing history).awake := by
  refine ⟨ready_present A label decode ready, ?_⟩
  by_cases before : Ready A label decode state installation
  · exact Or.inl (inv.ready_awake installation before)
  · exact Or.inr (adequate state firing valid fresh history historySubset installation before ready)

theorem wakeInv_next (adequate : NoLostWakeup A label decode index) {state : State T O}
    (inv : WakeInv A label decode state) {event : Label T O} (allowed : Allowed A label decode state event) :
    WakeInv A label decode (next label decode index state event) := by
  cases event with
  | env firing =>
      exact ⟨fire_subset_born inv.present_born,
        fun installation ready => ready_advance A label decode index adequate inv allowed.1 allowed.2 (fun _ member => member) ready⟩
  | run installation picked =>
      obtain ⟨definition, decoded, _, valid, fresh, history⟩ := allowed
      simp only [next, decoded]
      refine ⟨fire_subset_born inv.present_born, ?_⟩
      intro other ready
      exact ready_advance A label decode index adequate inv valid fresh
        (StandingRuleRows.record_mono installation definition.mode picked state.history) ready
  | sleep installation =>
      refine ⟨inv.present_born, ?_⟩
      intro other ready
      refine ⟨inv.ready_awake other ready, ?_⟩
      intro same
      have only := Set.mem_singleton_iff.mp same
      subst other
      exact allowed.2 ready
  | idle => exact inv

theorem Run.wakeInv (adequate : NoLostWakeup A label decode index)
    (run : Liveness.Run (system A label decode index)) (initial : WakeInv A label decode (run.state 0)) :
    ∀ n, WakeInv A label decode (run.state n) := by
  intro n
  induction n with
  | zero => exact initial
  | succ n ih =>
      rw [run.step n]
      exact wakeInv_next A label decode index adequate ih (run.allowed n)

def runTask (installation : O) : Label T O → Prop
  | .run selected _ => selected = installation
  | _ => False

theorem ready_task_enabled {state : State T O} (inv : WakeInv A label decode state) {installation : O}
    (ready : Ready A label decode state installation) :
    (system A label decode index).TaskEnabled (runTask installation) state := by
  obtain ⟨definition, decoded, picked, valid, fresh, history⟩ := ready
  exact ⟨.run installation picked, rfl, definition, decoded,
    inv.ready_awake installation ⟨definition, decoded, picked, valid, fresh, history⟩, valid, fresh, history⟩

/-- Fairness concerns the scheduler's actual awake run labels. The wake
invariant supplies the bridge from semantic readiness to that task. -/
theorem whenever_fires_often (adequate : NoLostWakeup A label decode index)
    (run : Liveness.Run (system A label decode index)) (initial : WakeInv A label decode (run.state 0))
    (installation : O) (often : InfinitelyOften fun n => Ready A label decode (run.state n) installation)
    (fair : run.StronglyFair (runTask installation)) :
    InfinitelyOften fun n => runTask installation (run.label n) := by
  apply fair
  intro start
  obtain ⟨n, later, ready⟩ := often start
  exact ⟨n, later, ready_task_enabled A label decode index
    (Run.wakeInv A label decode index adequate run initial n) ready⟩

theorem weak_fair_fires_of_stable (adequate : NoLostWakeup A label decode index)
    (run : Liveness.Run (system A label decode index)) (initial : WakeInv A label decode (run.state 0))
    (installation : O) (start : Nat)
    (readyUntil : ∀ n ≥ start, (∀ m, start ≤ m → m < n → ¬ runTask installation (run.label m)) →
      Ready A label decode (run.state n) installation)
    (fair : run.WeaklyFair (runTask installation)) :
    ∃ n ≥ start, runTask installation (run.label n) := by
  apply fair.fires start
  intro n later notYet
  exact ready_task_enabled A label decode index (Run.wakeInv A label decode index adequate run initial n)
    (readyUntil n later notYet)

theorem sleeping_keeps_the_installed_rule (state : State T O) (installation : O) :
    (next label decode index state (.sleep installation)).world = state.world ∧
      (next label decode index state (.sleep installation)).history = state.history := ⟨rfl, rfl⟩

theorem run_keeps_its_installation {state : State T O} {installation : O} {picked : Selection O}
    (allowed : Allowed A label decode state (.run installation picked)) :
    installation ∈ (next label decode index state (.run installation picked)).world.present := by
  obtain ⟨definition, decoded, _, valid, _, _⟩ := allowed
  simp only [next, decoded]
  exact StandingRuleRows.installation_survives A label installation definition.body picked state.world valid

theorem history_mono_next (state : State T O) (event : Label T O) :
    ∀ key ∈ state.history, key ∈ (next label decode index state event).history := by
  cases event with
  | env firing => exact fun _ member => member
  | run installation picked =>
      cases decoded : decode (label installation) with
      | none => simpa only [next, decoded] using (fun _ member => member : ∀ key ∈ state.history, key ∈ state.history)
      | some definition =>
          simpa only [next, decoded, advance, baseNext] using StandingRuleRows.record_mono installation definition.mode picked state.history
  | sleep installation => exact fun _ member => member
  | idle => exact fun _ member => member

/-- Once-per-selection is a history contract, independent of whether a
guard has become false and true again in the current physical world. -/
theorem seen_readonly_key_cannot_rearm {state : State T O} {installation : O} {picked : Selection O}
    {definition : StandingRuleRows.Definition T} (decoded : decode (label installation) = some definition)
    (profile : definition.mode = .perSelection) (readOnly : picked.taken = [])
    (seen : (⟨installation, picked.read⟩ : PropagationHistory.Key O O) ∈ state.history) :
    ¬ Allowed A label decode state (.run installation picked) := by
  rintro ⟨actual, actualDecoded, _, _, _, fresh⟩
  have same : definition = actual := Option.some.inj (decoded.symm.trans actualDecoded)
  subst actual
  apply fresh _ seen
  exact (PropagationHistory.tracked_iff _).mpr ⟨by simp [StandingRuleRows.event, profile], readOnly⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StandingRuleMachine
