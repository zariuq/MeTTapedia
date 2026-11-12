import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramAdequacy
import Mettapedia.Machines.ProgressObservation

/-!
# Progress observations for the program core and its admitted occurrence firings

The observer erases the existing program machine's twelve administrative rules.
All other rule names remain observations, including semantic computation which
may itself diverge. Its decreasing measure is proved in `ProgramAdequacy`.

Native events retain the schema name and actual selected occurrences. Their
source interpretation follows from the existing occurrence-firing completeness
theorem, rather than from an assumed source transition. Represented states carry
the already-defined, unique row readback of their occurrence configuration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program.Progress

open Mettapedia.Machines.ProgressObservation
open ProgramRows ProgramTranslation

abbrev World := Multiset Sx

def administrativeRule : RuleName → Bool
  | .varZero | .varSucc | .lam | .app | .appL | .let_ | .quote | .activate
  | .atom | .add | .remove | .demand => true
  | .beta | .letK | .activateK | .ambL | .ambR | .addK | .removeK | .await
  | .demandK | .resume | .call | .redefine => false

/-- A source event retains which of the program's actual schemas fired. -/
structure SourceEvent (before after : World) where
  rule : RuleName
  fired : (schema rule).Fires before after

abbrev sourceQuiver : Quiver World := ⟨SourceEvent⟩
attribute [local instance] sourceQuiver

def sourceObservation : Observation World RuleName :=
  fun event => if administrativeRule event.rule then none else some event.rule

theorem administrative_of_schema {name : RuleName} {before after : World}
    (admin : administrativeRule name = true) (fired : (schema name).Fires before after) :
    Program.Administrative before after := by
  obtain ⟨assignment, frame, rfl, rfl⟩ := fired
  cases name with
  | varZero => exact .varZero (assignment 0) (assignment 1) (assignment 2) frame
  | varSucc => exact .varSucc (assignment 0) (assignment 1) (assignment 2) (assignment 3) frame
  | lam => exact .lam (assignment 0) (assignment 1) (assignment 2) frame
  | app => exact .app (assignment 0) (assignment 1) (assignment 2) (assignment 3) frame
  | appL => exact .appL (assignment 0) (assignment 1) (assignment 2) (assignment 3) frame
  | let_ => exact .let_ (assignment 0) (assignment 1) (assignment 2) (assignment 3) frame
  | quote => exact .quote (assignment 0) (assignment 1) (assignment 2) frame
  | activate => exact .activate (assignment 0) (assignment 1) (assignment 2) frame
  | atom => exact .atom (assignment 0) (assignment 1) (assignment 2) frame
  | add => exact .add (assignment 0) (assignment 1) (assignment 2) frame
  | remove => exact .remove (assignment 0) (assignment 1) (assignment 2) frame
  | demand => exact .demand (assignment 0) (assignment 1) (assignment 2) (assignment 3) frame
  | beta | letK | activateK | ambL | ambR | addK | removeK | await
  | demandK | resume | call | redefine => cases admin

theorem source_erased_decreases {before after : World} (event : SourceEvent before after)
    (erased : sourceObservation event = none) : measure after < measure before := by
  have admin : administrativeRule event.rule = true := by
    simpa [sourceObservation] using erased
  exact administrative_decreases (administrative_of_schema admin event.fired)

theorem source_nonZeno : NonZeno sourceObservation :=
  nonZeno_of_rank sourceObservation measure source_erased_decreases

/-- A well-formed occurrence configuration together with its unique source readback. -/
structure State where
  configuration : Config
  nextScope : ℕ
  world : World
  represents : Represents configuration world nextScope

/-- The exact, named schema instance and occurrence selection admitted by the core. -/
structure Event (before after : State) where
  rule : RuleName
  taken : List Occ
  borrowed : List Occ
  valid : ((schema rule).firing before.nextScope taken borrowed).Valid A Occ.label before.configuration
  result_eq : after.configuration =
    ((schema rule).firing before.nextScope taken borrowed).result Occ.label before.configuration
  scope_eq : after.nextScope = before.nextScope + 1

instance nativeQuiver : Quiver State := ⟨Event⟩

def observation : Observation State RuleName :=
  fun event => if administrativeRule event.rule then none else some event.rule

namespace Event

/-- Every native event is an admitted firing of the existing semantic step. -/
theorem admitted {before after : State} (event : Event before after) :
    ∃ allowed : (Semantic.semanticStep A Occ.label).Admits (s := before.configuration)
      ⟨(schema event.rule).firing before.nextScope event.taken event.borrowed,
        firing_isSemantic _ _ _ _⟩,
      (Semantic.semanticStep A Occ.label).result _ allowed = after.configuration := by
  obtain ⟨allowed, result⟩ := translated_admitted schema event.rule before.nextScope
    event.taken event.borrowed event.valid
  exact ⟨allowed, result.trans event.result_eq.symm⟩

theorem source_fired {before after : State} (event : Event before after) :
    (schema event.rule).Fires before.world after.world := by
  obtain ⟨world, fired, represents⟩ := complete (schema_wellFormed event.rule)
    before.represents event.valid
  have target := after.represents
  rw [event.result_eq, event.scope_eq] at target
  have same := represents_unique represents target
  simpa only [same] using fired

def toSource {before after : State} (event : Event before after) :
    SourceEvent before.world after.world := ⟨event.rule, event.source_fired⟩

@[simp] theorem toSource_rule {before after : State} (event : Event before after) :
    event.toSource.rule = event.rule := rfl

@[simp] theorem observation_toSource {before after : State} (event : Event before after) :
    sourceObservation event.toSource = observation event := rfl

theorem erased_decreases {before after : State} (event : Event before after)
    (erased : observation event = none) : measure after.world < measure before.world :=
  source_erased_decreases event.toSource erased

end Event

/-- The administrative hypothesis is discharged for all represented native events. -/
theorem nonZeno : NonZeno observation :=
  nonZeno_of_rank observation (fun state => measure state.world) Event.erased_decreases

theorem unbounded_native_observations (execution : Execution State) (count : ℕ) :
    ∃ cutoff, count ≤ execution.observedCount observation cutoff :=
  unbounded_observations observation nonZeno execution count

theorem erased_native_path_bound {before after : State} (path : Quiver.Path before after)
    (erased : observePath observation path = []) :
    path.length + measure after.world ≤ measure before.world :=
  erased_path_bound observation (fun state => measure state.world) Event.erased_decreases path erased

/-- Every source event can actually be realized from a represented native state. -/
theorem realize {before : State} {world : World} (event : SourceEvent before.world world) :
    ∃ after : State, after.world = world ∧ ∃ occurrence : Event before after,
      occurrence.rule = event.rule := by
  obtain ⟨taken, borrowed, valid, represents⟩ := sound (schema_wellFormed event.rule)
    before.represents event.fired
  let after : State := ⟨((schema event.rule).firing before.nextScope taken borrowed).result
    Occ.label before.configuration, before.nextScope + 1, world, represents⟩
  exact ⟨after, rfl, ⟨event.rule, taken, borrowed, valid, rfl, rfl⟩, rfl⟩

/-- Source enabledness and native enabledness agree on represented states. -/
theorem enabled_iff (before : State) :
    (∃ after : State, Nonempty (Event before after)) ↔
      ∃ world : World, Nonempty (SourceEvent before.world world) := by
  constructor
  · rintro ⟨after, ⟨event⟩⟩
    exact ⟨after.world, ⟨event.toSource⟩⟩
  · rintro ⟨world, ⟨event⟩⟩
    obtain ⟨after, _, occurrence, _⟩ := realize event
    exact ⟨after, ⟨occurrence⟩⟩

theorem quiescent_iff (before : State) :
    (¬ ∃ after : State, Nonempty (Event before after)) ↔
      ¬ ∃ world : World, Nonempty (SourceEvent before.world world) :=
  not_congr (enabled_iff before)

/-- The represented domain is closed under every raw translated program firing. -/
theorem reify_translated {before : State} {result : Config × ℕ}
    (firing : Translated schema (before.configuration, before.nextScope) result) :
    ∃ after : State, after.configuration = result.1 ∧ after.nextScope = result.2 ∧
      Nonempty (Event before after) := by
  cases firing with
  | fire name taken borrowed valid =>
      obtain ⟨world, _, represents⟩ := complete (schema_wellFormed name) before.represents valid
      exact ⟨⟨_, before.nextScope + 1, world, represents⟩, rfl, rfl,
        ⟨⟨name, taken, borrowed, valid, rfl, rfl⟩⟩⟩

def projectPath {before : State} : {after : State} → Quiver.Path before after →
    Quiver.Path before.world after.world
  | _, .nil => .nil
  | _, .cons path event => (projectPath path).cons event.toSource

theorem projectPath_observation {before after : State} (path : Quiver.Path before after) :
    observePath sourceObservation (projectPath path) = observePath observation path := by
  induction path with
  | nil => rfl
  | cons path event ih => simp [projectPath, observePath, ih, observation, sourceObservation, Event.toSource]

/-- Finite source executions lift with their declared observations and endpoints. -/
theorem liftPath {before : State} {world : World} (path : Quiver.Path before.world world) :
    ∃ after : State, ∃ occurrencePath : Quiver.Path before after,
      after.world = world ∧ observePath observation occurrencePath = observePath sourceObservation path := by
  induction path with
  | nil => exact ⟨before, .nil, rfl, rfl⟩
  | @cons middle last path event ih =>
      obtain ⟨current, earlier, same, observed⟩ := ih
      let source : SourceEvent current.world last := ⟨event.rule, by simpa only [same] using event.fired⟩
      obtain ⟨after, final, occurrence, named⟩ := realize source
      refine ⟨after, earlier.cons occurrence, final, ?_⟩
      simp only [observePath_cons, observed]
      congr 1
      change (if administrativeRule occurrence.rule then none else some occurrence.rule).toList = _
      rw [named]
      rfl

def mapExecution (execution : Execution State) : Execution World where
  state n := (execution.state n).world
  event n := (execution.event n).toSource

theorem mapExecution_counts (execution : Execution State) (cutoff : ℕ) :
    (mapExecution execution).observedCount sourceObservation cutoff =
      execution.observedCount observation cutoff := by
  induction cutoff with
  | zero => rfl
  | succ cutoff ih =>
      rw [Execution.observedCount_succ, Execution.observedCount_succ, ih]
      rfl

structure Realization {before : State} {world : World} (source : SourceEvent before.world world) where
  after : State
  world_eq : after.world = world
  occurrence : Event before after
  rule_eq : occurrence.rule = source.rule

noncomputable def selectRealization {before : State} {world : World}
    (source : SourceEvent before.world world) : Realization source :=
  Classical.choice (by
    obtain ⟨after, same, event, named⟩ := realize source
    exact ⟨⟨after, same, event, named⟩⟩)

noncomputable def liftStage (source : Execution World) (n : ℕ)
    (before : {state : State // state.world = source.state n}) :
    Σ after : {state : State // state.world = source.state (n + 1)},
      {event : Event before.val after.val // event.rule = (source.event n).rule} := by
  let firing : SourceEvent before.val.world (source.state (n + 1)) :=
    ⟨(source.event n).rule, by simpa only [before.property] using (source.event n).fired⟩
  let realized := selectRealization firing
  exact ⟨⟨realized.after, realized.world_eq⟩, realized.occurrence, realized.rule_eq⟩

noncomputable def liftedState (source : Execution World) (before : State)
    (initial : before.world = source.state 0) :
    (n : ℕ) → {state : State // state.world = source.state n}
  | 0 => ⟨before, initial⟩
  | n + 1 => (liftStage source n (liftedState source before initial n)).1

/-- Infinite source executions lift along actual admitted events, starting at a given representation. -/
noncomputable def liftExecution (source : Execution World) (before : State)
    (initial : before.world = source.state 0) : Execution State where
  state n := (liftedState source before initial n).val
  event n := (liftStage source n (liftedState source before initial n)).2.val

@[simp] theorem liftExecution_initial (source : Execution World) (before : State)
    (initial : before.world = source.state 0) :
    (liftExecution source before initial).state 0 = before := rfl

theorem liftExecution_world (source : Execution World) (before : State)
    (initial : before.world = source.state 0) (n : ℕ) :
    ((liftExecution source before initial).state n).world = source.state n :=
  (liftedState source before initial n).property

theorem liftExecution_rule (source : Execution World) (before : State)
    (initial : before.world = source.state 0) (n : ℕ) :
    ((liftExecution source before initial).event n).rule = (source.event n).rule :=
  (liftStage source n (liftedState source before initial n)).2.property

theorem liftExecution_observation (source : Execution World) (before : State)
    (initial : before.world = source.state 0) (n : ℕ) :
    observation ((liftExecution source before initial).event n) = sourceObservation (source.event n) := by
  simp only [observation, sourceObservation, liftExecution_rule]

theorem liftExecution_counts (source : Execution World) (before : State)
    (initial : before.world = source.state 0) (cutoff : ℕ) :
    (liftExecution source before initial).observedCount observation cutoff =
      source.observedCount sourceObservation cutoff := by
  induction cutoff with
  | zero => rfl
  | succ cutoff ih =>
      rw [Execution.observedCount_succ, Execution.observedCount_succ, ih, liftExecution_observation]

/-- Infinite executions exist on exactly the same represented source and occurrence states. -/
theorem infinite_execution_iff (before : State) :
    (∃ execution : Execution State, execution.state 0 = before) ↔
      ∃ execution : Execution World, execution.state 0 = before.world := by
  constructor
  · rintro ⟨execution, initial⟩
    refine ⟨mapExecution execution, ?_⟩
    change (execution.state 0).world = before.world
    rw [initial]
  · rintro ⟨source, initial⟩
    exact ⟨liftExecution source before initial.symm, rfl⟩

/-- A loaded list is a genuine represented state, without an additional readback hypothesis. -/
noncomputable def initialState (rows : List Sx) : State :=
  ⟨initial rows, 1, rows, initial_represents rows⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program.Progress
