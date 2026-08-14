import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Execution and declaration closure criteria

Several distinct questions hide behind the phrase "outside manager".  This
module separates the generic parts that can be stated without choosing a
particular language-definition schema.

* A bounded run is honest when it returns either a quiescent configuration or
  an expired configuration that can be resumed.
* Private driver state is observationally irrelevant only relative to a named
  observer and a predicate of admissible states.
* Control state is reified only when complete driver configurations are terms
  of a control GSLT whose steps agree with the driver.
* Declared vocabulary and installed realizations are different objects.
  Vocabulary may be host-invariant while realization availability varies.

The predicates here deliberately do not add fields to a five-field language
definition.  Authored declaration closure belongs to a coGSLT extension
layer; this file supplies the execution and factorization obligations used to
audit such layers and their hosts.
-/

namespace Mettapedia.GSLT.Core.ClosureCriteria

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization

universe u v w

/-! ## Intrinsic step-shape capabilities -/

/-- Exact data witnessing two composable one-step transitions.  Keeping the
three states and both selected steps in `Type` lets later transports retain
the operational witness rather than only an existential proposition. -/
structure ComposableStepWitness (theory : GSLT) where
  source : theory.Term
  middle : theory.Term
  target : theory.Term
  first : theory.Step source middle
  second : theory.Step middle target

/-- A theory admits internal re-entry when it carries a composable-step
witness.  `Nonempty` exposes the capability proposition without choosing a
distinguished execution globally. -/
def HasComposableSteps (theory : GSLT) : Prop :=
  Nonempty (ComposableStepWitness theory)

namespace ComposableStepWitness

/-- A step-preserving map transports the complete composable-step witness. -/
def map {sourceTheory : GSLT.{u}} {targetTheory : GSLT.{v}}
    (witness : ComposableStepWitness sourceTheory)
    (mapTerm : sourceTheory.Term → targetTheory.Term)
    (mapStep : ∀ {source target},
      sourceTheory.Step source target →
        targetTheory.Step (mapTerm source) (mapTerm target)) :
    ComposableStepWitness targetTheory where
  source := mapTerm witness.source
  middle := mapTerm witness.middle
  target := mapTerm witness.target
  first := mapStep witness.first
  second := mapStep witness.second

/-- A faithful structural embedding transports internal re-entry while
retaining the selected source execution. -/
def mapEmbedding {sourceTheory targetTheory : GSLT.{u}}
    (witness : ComposableStepWitness sourceTheory)
    (embedding : GSLT.Embedding sourceTheory targetTheory) :
    ComposableStepWitness targetTheory :=
  witness.map embedding.toFun fun step =>
    (embedding.step_iff _ _).2 step

end ComposableStepWitness

/-- Every step-preserving map preserves the existence of internal re-entry. -/
theorem hasComposableSteps_of_mapStep
    {sourceTheory : GSLT.{u}} {targetTheory : GSLT.{v}}
    (mapTerm : sourceTheory.Term → targetTheory.Term)
    (mapStep : ∀ {source target},
      sourceTheory.Step source target →
        targetTheory.Step (mapTerm source) (mapTerm target))
    (sourceReentry : HasComposableSteps sourceTheory) :
    HasComposableSteps targetTheory := by
  obtain ⟨witness⟩ := sourceReentry
  exact ⟨witness.map mapTerm mapStep⟩

/-- Structural embeddings preserve internal re-entry as a specialization of
step-preserving witness transport. -/
theorem hasComposableSteps_of_embedding
    {sourceTheory targetTheory : GSLT.{u}}
    (embedding : GSLT.Embedding sourceTheory targetTheory)
    (sourceReentry : HasComposableSteps sourceTheory) :
    HasComposableSteps targetTheory := by
  obtain ⟨witness⟩ := sourceReentry
  exact ⟨witness.mapEmbedding embedding⟩

/-- A one-step-terminal theory sends every transition to a normal form.  This
is a law bundle, not a claim that every theory should have terminal steps. -/
structure OneStepTerminal (theory : GSLT) : Prop where
  target_normal : ∀ {source target},
    theory.Step source target → theory.IsNormalForm target

namespace OneStepTerminal

/-- One-step terminality rules out internal re-entry. -/
theorem not_hasComposableSteps {theory : GSLT}
    (terminal : OneStepTerminal theory) :
    ¬ HasComposableSteps theory := by
  rintro ⟨witness⟩
  exact terminal.target_normal witness.first
    ⟨witness.target, witness.second⟩

end OneStepTerminal

/-! ## Honest bounded execution -/

/-- The result of running for at most a finite budget.  Both constructors
retain the complete residual configuration.  `expired` is not failure and is
therefore resumable. -/
inductive BoundedRunReport (Term : Type u) (State : Type v) where
  /-- The driver inspected the residual configuration and found no next move. -/
  | completed (term : Term) (state : State)
  /-- The budget ended while another move remained available. -/
  | expired (term : Term) (state : State)

namespace BoundedRunReport

variable {Term : Type u} {State : Type v}

/-- The residual configuration retained by either outcome. -/
def configuration : BoundedRunReport Term State → Term × State
  | .completed term state | .expired term state => (term, state)

/-- The residual object-language term. -/
def term (report : BoundedRunReport Term State) : Term :=
  report.configuration.1

/-- The residual private driver state. -/
def state (report : BoundedRunReport Term State) : State :=
  report.configuration.2

@[simp] theorem configuration_completed (term : Term) (state : State) :
    (completed term state : BoundedRunReport Term State).configuration =
      (term, state) :=
  rfl

@[simp] theorem configuration_expired (term : Term) (state : State) :
    (expired term state : BoundedRunReport Term State).configuration =
      (term, state) :=
  rfl

@[simp] theorem term_completed (term : Term) (state : State) :
    (completed term state : BoundedRunReport Term State).term = term :=
  rfl

@[simp] theorem term_expired (term : Term) (state : State) :
    (expired term state : BoundedRunReport Term State).term = term :=
  rfl

end BoundedRunReport

/-! ## Drivers with private state -/

/-- A deterministic driver for a GSLT.  Its state may hold a work queue,
cursor, seed, or continuation not present in the object term. -/
structure HostedDriver (theory : GSLT) where
  State : Type u
  step : theory.Term → State → Option (theory.Term × State)
  sound : ∀ term state next state',
    step term state = some (next, state') → theory.Step term next

namespace HostedDriver

variable {theory : GSLT}

/-- Run at most `fuel` moves.  At zero fuel the driver only inspects whether a
move remains; it never performs the extra move. -/
def runReport (driver : HostedDriver theory) :
    theory.Term → driver.State → Nat →
      BoundedRunReport theory.Term driver.State
  | term, state, 0 =>
      match driver.step term state with
      | none => .completed term state
      | some _ => .expired term state
  | term, state, fuel + 1 =>
      match driver.step term state with
      | none => .completed term state
      | some (next, state') => driver.runReport next state' fuel

/-- Resume an expired report with another budget.  A completed report remains
completed because its residual configuration was already inspected. -/
def resume (driver : HostedDriver theory)
    (report : BoundedRunReport theory.Term driver.State) (fuel : Nat) :
    BoundedRunReport theory.Term driver.State :=
  match report with
  | .completed term state => .completed term state
  | .expired term state => driver.runReport term state fuel

@[simp] theorem resume_completed (driver : HostedDriver theory)
    (term : theory.Term) (state : driver.State) (fuel : Nat) :
    driver.resume (.completed term state) fuel = .completed term state :=
  rfl

@[simp] theorem resume_expired (driver : HostedDriver theory)
    (term : theory.Term) (state : driver.State) (fuel : Nat) :
    driver.resume (.expired term state) fuel =
      driver.runReport term state fuel :=
  rfl

/-- A quiescent residual remains completed under every budget. -/
theorem runReport_of_quiescent (driver : HostedDriver theory)
    {term : theory.Term} {state : driver.State}
    (quiescent : driver.step term state = none) (fuel : Nat) :
    driver.runReport term state fuel = .completed term state := by
  cases fuel <;> simp [runReport, quiescent]

/-- Every residual term reported by a driver is reachable in the object
theory.  Thus a sound driver selects steps but introduces no object step. -/
theorem runReport_multiStep (driver : HostedDriver theory) :
    ∀ (fuel : Nat) (term : theory.Term) (state : driver.State),
      theory.MultiStep term (driver.runReport term state fuel).term
  | 0, term, state => by
      unfold runReport
      cases driver.step term state <;> exact .refl term
  | fuel + 1, term, state => by
      unfold runReport
      cases moved : driver.step term state with
      | none => exact .refl term
      | some next =>
          exact .step (driver.sound term state next.1 next.2 moved)
            (driver.runReport_multiStep fuel next.1 next.2)

/-- A completed bounded report carries an actually quiescent residual
configuration. -/
theorem runReport_completed_quiescent (driver : HostedDriver theory) :
    ∀ {fuel term state finalTerm finalState},
      driver.runReport term state fuel = .completed finalTerm finalState →
        driver.step finalTerm finalState = none
  | 0, term, state, finalTerm, finalState, completed => by
      cases moved : driver.step term state with
      | none =>
          simp [runReport, moved] at completed
          rcases completed with ⟨rfl, rfl⟩
          exact moved
      | some _ => simp [runReport, moved] at completed
  | fuel + 1, term, state, finalTerm, finalState, completed => by
      cases moved : driver.step term state with
      | none =>
          simp [runReport, moved] at completed
          rcases completed with ⟨rfl, rfl⟩
          exact moved
      | some next =>
          apply driver.runReport_completed_quiescent
          simpa [runReport, moved] using completed

/-- An expired report carries a residual configuration with a next move.
This is the information a silent fuel sentinel loses. -/
theorem runReport_expired_has_next (driver : HostedDriver theory) :
    ∀ {fuel term state finalTerm finalState},
      driver.runReport term state fuel = .expired finalTerm finalState →
        ∃ next nextState,
          driver.step finalTerm finalState = some (next, nextState)
  | 0, term, state, finalTerm, finalState, expired => by
      cases moved : driver.step term state with
      | none => simp [runReport, moved] at expired
      | some next =>
          simp [runReport, moved] at expired
          rcases expired with ⟨rfl, rfl⟩
          exact ⟨next.1, next.2, moved⟩
  | fuel + 1, term, state, finalTerm, finalState, expired => by
      cases moved : driver.step term state with
      | none => simp [runReport, moved] at expired
      | some _ =>
          apply driver.runReport_expired_has_next
          simpa [runReport, moved] using expired

end HostedDriver

/-! ## Observation invariance of private state -/

/-- Private state is irrelevant to one declared bounded observation on the
states admitted for the starting term.  This is intentionally weaker than
equality of intermediate terms and intentionally stronger than checking one
chosen initial state. -/
def PrivateStateObservationInvariant {theory : GSLT}
    (driver : HostedDriver theory)
    (admissible : theory.Term → driver.State → Prop)
    {Observation : Type v}
    (observe : BoundedRunReport theory.Term driver.State → Observation) : Prop :=
  ∀ term first second fuel,
    admissible term first → admissible term second →
      observe (driver.runReport term first fuel) =
        observe (driver.runReport term second fuel)

/-- A subsingleton private state is observationally irrelevant for every
observer and every admissibility predicate. -/
theorem privateStateObservationInvariant_of_subsingleton
    {theory : GSLT} (driver : HostedDriver theory)
    (only : ∀ first second : driver.State, first = second)
    (admissible : theory.Term → driver.State → Prop)
    {Observation : Type v}
    (observe : BoundedRunReport theory.Term driver.State → Observation) :
    PrivateStateObservationInvariant driver admissible observe := by
  intro term first second fuel _ _
  rw [only first second]

/-! ## Reifying a driver as a control GSLT -/

/-- The canonical control theory generated by a driver.  Its terms are whole
driver configurations and its rewrites are exactly successful driver moves. -/
def HostedDriver.controlGSLT {theory : GSLT}
    (driver : HostedDriver theory) : GSLT where
  Term := theory.Term × driver.State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    driver.step source.1 source.2 = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Evidence that a language-level control theory contains exactly the
complete configurations and moves of a hosted driver.  This, rather than
bounded result equality, is the carrier-level meaning of control reification. -/
structure ControlReification {theory : GSLT} (driver : HostedDriver theory)
    (control : GSLT) where
  configuration : (theory.Term × driver.State) ≃ control.Term
  step_iff : ∀ source target,
    control.Step (configuration source) (configuration target) ↔
      driver.step source.1 source.2 = some target

namespace ControlReification

variable {theory control : GSLT} {driver : HostedDriver theory}

/-- Forget control state and recover the object term. -/
def erase (reification : ControlReification driver control) :
    control.Term → theory.Term :=
  fun term => (reification.configuration.symm term).1

/-- Erasing a reified control step gives a valid object-theory step. -/
theorem erase_step (reification : ControlReification driver control)
    {source target : control.Term} (step : control.Step source target) :
    theory.Step (reification.erase source) (reification.erase target) := by
  let sourceConfiguration := reification.configuration.symm source
  let targetConfiguration := reification.configuration.symm target
  have encodedStep :
      control.Step (reification.configuration sourceConfiguration)
        (reification.configuration targetConfiguration) := by
    simpa [sourceConfiguration, targetConfiguration] using step
  have moved :=
    (reification.step_iff sourceConfiguration targetConfiguration).mp encodedStep
  exact driver.sound sourceConfiguration.1 sourceConfiguration.2
    targetConfiguration.1 targetConfiguration.2 moved

end ControlReification

/-- Every hosted driver has a canonical freely reified control GSLT.  An
existing language is control-reified only after exhibiting an equivalence to
this construction; the construction itself makes no such claim. -/
def HostedDriver.canonicalControlReification {theory : GSLT}
    (driver : HostedDriver theory) :
    ControlReification driver driver.controlGSLT where
  configuration := Equiv.refl _
  step_iff := fun _ _ => Iff.rfl

/-! ## A private-state obstruction -/

private inductive ForkStep : Nat → Nat → Prop
  | left : ForkStep 0 1
  | right : ForkStep 0 2

@[reducible] private def forkTheory : GSLT where
  Term := Nat
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := ForkStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

@[reducible] private def forkDriver : HostedDriver forkTheory where
  State := Bool
  step := fun term state =>
    match term with
    | 0 => if state then some (1, state) else some (2, state)
    | _ => none
  sound := by
    intro term state next state' moved
    cases term with
    | zero =>
        cases state with
        | false => cases moved; exact ForkStep.right
        | true => cases moved; exact ForkStep.left
    | succ _ => simp at moved

private def allForkStates : forkTheory.Term → forkDriver.State → Prop :=
  fun _ _ => True

/-- Private state can change a declared observation even though every chosen
move is sound. -/
theorem forkDriver_not_privateStateObservationInvariant :
    ¬ PrivateStateObservationInvariant forkDriver allForkStates
      BoundedRunReport.term := by
  intro invariant
  have collision := invariant 0 true false 1 trivial trivial
  simp [forkDriver, HostedDriver.runReport, BoundedRunReport.term,
    BoundedRunReport.configuration] at collision

/-- The same obstruction as a non-trivial fibre over the visible starting
term. -/
private def forkObservationFiber :
    NonTrivialFiber (fun pair : forkTheory.Term × Bool => pair.1)
      (fun pair => (forkDriver.runReport pair.1 pair.2 1).term) where
  left := (0, true)
  right := (0, false)
  sameShadow := rfl
  differentValue := by decide

theorem forkDriver_observation_not_factors_through_term :
    ¬ Factors (fun pair : forkTheory.Term × Bool => pair.1)
      (fun pair => (forkDriver.runReport pair.1 pair.2 1).term) :=
  forkObservationFiber.not_factors

/-! ## Declared vocabulary versus installed realizations -/

/-- The accurate factorization property for a host audit: the reported
vocabulary depends on the language and not on the selected host build. -/
def VocabularyHostInvariant {Language Host Vocabulary : Type*}
    (vocabulary : Language × Host → Vocabulary) : Prop :=
  Factors (fun pair : Language × Host => pair.1) vocabulary

/-- An explicitly declared vocabulary is host-invariant. -/
theorem vocabularyHostInvariant_of_declared
    {Language Host Vocabulary : Type*}
    (declared : Language → Vocabulary)
    (vocabulary : Language × Host → Vocabulary)
    (agrees : ∀ pair, vocabulary pair = declared pair.1) :
    VocabularyHostInvariant vocabulary :=
  ⟨declared, fun pair => (agrees pair).symm⟩

/-- A language declaration and a possibly partial native realization are
separate.  Native code may be absent, but any installed implementation must
realize an operation declared by the language. -/
structure DeclaredRealizationBoundary
    (Language Host Declaration Implementation : Type*) where
  declared : Language → Declaration → Prop
  realize? : Language → Host → Declaration → Option Implementation
  realizes_declared : ∀ language host declaration implementation,
    realize? language host declaration = some implementation →
      declared language declaration

namespace DeclaredRealizationBoundary

variable {Language Host Declaration Implementation : Type*}

/-- The declared interface ignores which host realization is installed. -/
def vocabulary
    (boundary : DeclaredRealizationBoundary
      Language Host Declaration Implementation) :
    Language × Host → (Declaration → Prop) :=
  fun pair => boundary.declared pair.1

/-- Declaration vocabulary remains host-invariant even when realization
availability does not. -/
theorem vocabulary_hostInvariant
    (boundary : DeclaredRealizationBoundary
      Language Host Declaration Implementation) :
    VocabularyHostInvariant boundary.vocabulary :=
  ⟨boundary.declared, fun _ => rfl⟩

end DeclaredRealizationBoundary

private inductive SolverHost where
  | withSolver
  | withoutSolver
deriving DecidableEq

private inductive SolverDeclaration where
  | solve
deriving DecidableEq

private def solverBoundary :
    DeclaredRealizationBoundary Unit SolverHost SolverDeclaration Unit where
  declared := fun _ _ => True
  realize? := fun _ host _ =>
    match host with
    | .withSolver => some ()
    | .withoutSolver => none
  realizes_declared := by
    intro _ _ _ _ _
    trivial

private def solverAvailable : Unit × SolverHost → Bool
  | (_, .withSolver) => true
  | (_, .withoutSolver) => false

private def solverAvailabilityFiber :
    NonTrivialFiber (fun pair : Unit × SolverHost => pair.1)
      solverAvailable where
  left := ((), .withSolver)
  right := ((), .withoutSolver)
  sameShadow := rfl
  differentValue := by decide

/-- A native solver may be unavailable on one host without disappearing from
the language's declared interface. -/
theorem solver_declaration_invariant_but_availability_not :
    VocabularyHostInvariant solverBoundary.vocabulary ∧
      ¬ VocabularyHostInvariant solverAvailable :=
  ⟨solverBoundary.vocabulary_hostInvariant,
    solverAvailabilityFiber.not_factors⟩

/-! ## Independence of the two audits -/

/-- A single hosted-language audit packages the two otherwise independent
questions over one system. -/
structure HostedLanguageAudit {theory : GSLT}
    (driver : HostedDriver theory)
    (Language Host Vocabulary Observation : Type*) where
  admissible : theory.Term → driver.State → Prop
  observe : BoundedRunReport theory.Term driver.State → Observation
  vocabulary : Language × Host → Vocabulary

namespace HostedLanguageAudit

def privateStateInvariant {theory : GSLT} {driver : HostedDriver theory}
    {Language Host Vocabulary Observation : Type*}
    (audit : HostedLanguageAudit driver Language Host Vocabulary Observation) :
    Prop :=
  PrivateStateObservationInvariant driver audit.admissible audit.observe

def vocabularyInvariant {theory : GSLT} {driver : HostedDriver theory}
    {Language Host Vocabulary Observation : Type*}
    (audit : HostedLanguageAudit driver Language Host Vocabulary Observation) :
    Prop :=
  VocabularyHostInvariant audit.vocabulary

end HostedLanguageAudit

@[reducible] private def inertTheory : GSLT where
  Term := Nat
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by simp
  rewrites_resp_right := by simp

@[reducible] private def statelessDriver : HostedDriver inertTheory where
  State := Unit
  step := fun _ _ => none
  sound := by simp

private def stateIndependentHostDependentAudit :
    HostedLanguageAudit statelessDriver Unit SolverHost Bool Nat where
  admissible := fun _ _ => True
  observe := BoundedRunReport.term
  vocabulary := solverAvailable

private def stateDependentHostIndependentAudit :
    HostedLanguageAudit forkDriver Unit Unit Unit Nat where
  admissible := allForkStates
  observe := BoundedRunReport.term
  vocabulary := fun _ => ()

/-- Private-state observation invariance does not imply host-invariant
vocabulary. -/
theorem privateStateInvariant_does_not_imply_vocabularyInvariant :
    stateIndependentHostDependentAudit.privateStateInvariant ∧
      ¬ stateIndependentHostDependentAudit.vocabularyInvariant := by
  constructor
  · exact privateStateObservationInvariant_of_subsingleton
      statelessDriver (fun first second => by cases first; cases second; rfl)
      (fun _ _ => True) BoundedRunReport.term
  · exact solverAvailabilityFiber.not_factors

/-- Host-invariant vocabulary does not imply private-state observation
invariance. -/
theorem vocabularyInvariant_does_not_imply_privateStateInvariant :
    stateDependentHostIndependentAudit.vocabularyInvariant ∧
      ¬ stateDependentHostIndependentAudit.privateStateInvariant := by
  constructor
  · exact ⟨fun _ => (), fun _ => rfl⟩
  · exact forkDriver_not_privateStateObservationInvariant

end Mettapedia.GSLT.Core.ClosureCriteria
