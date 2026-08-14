import Mettapedia.GSLT.Core.Composition

/-!
# Escape-free worklist region compilation

A value-owned worklist transition consumes one state and returns complete
successor values plus persistent observations.  Once those values have been
copied across the transition boundary, the consumed state cannot influence a
future transition.  A backend may therefore reclaim its allocation region at
dequeue instead of retaining every processed state until the whole run ends.

This module makes the ownership condition structural: `OwnedStep` contains
values, not references into a retired state.  The reference machine retains
processed states; the compiled machine erases that history.  Projection
commutes with every step and every bounded run, including the exact residual
queue and observation order.
-/

namespace Mettapedia.GSLT.LanguageDef.WorklistRegionCompilation

universe uState uObservation

/-- Complete values crossing one transition boundary.  A physical backend
must copy these values into successor/output ownership before reclaiming the
current region. -/
structure OwnedStep (State : Type uState) (Observation : Type uObservation) where
  successors : List State
  observations : List Observation

/-- A deterministic value-owned worklist program. -/
abbrev Machine (State : Type uState) (Observation : Type uObservation) :=
  State → OwnedStep State Observation

/-- Reference configuration that retains every consumed state. -/
structure RetainedConfiguration
    (State : Type uState) (Observation : Type uObservation) where
  pending : List State
  retired : List State
  observations : List Observation
  deriving DecidableEq, Repr

/-- Region configuration after proof-irrelevant retired storage is erased. -/
structure RegionConfiguration
    (State : Type uState) (Observation : Type uObservation) where
  pending : List State
  observations : List Observation
  deriving DecidableEq, Repr

/-- Forget only processed states; all future inputs and persistent
observations remain exact. -/
def eraseRetired
    (configuration : RetainedConfiguration State Observation) :
    RegionConfiguration State Observation :=
  { pending := configuration.pending
    observations := configuration.observations }

/-- One FIFO reference step.  Successors are appended in their authored
order, while the consumed value remains in the retired region. -/
def retainedStep (machine : Machine State Observation)
    (configuration : RetainedConfiguration State Observation) :
    Option (RetainedConfiguration State Observation) :=
  match configuration.pending with
  | [] => none
  | current :: pending =>
      let produced := machine current
      some {
        pending := pending ++ produced.successors
        retired := current :: configuration.retired
        observations := configuration.observations ++ produced.observations }

/-- One compiled FIFO step.  The consumed value is absent after its complete
successor and observation payloads cross the ownership boundary. -/
def regionStep (machine : Machine State Observation)
    (configuration : RegionConfiguration State Observation) :
    Option (RegionConfiguration State Observation) :=
  match configuration.pending with
  | [] => none
  | current :: pending =>
      let produced := machine current
      some {
        pending := pending ++ produced.successors
        observations := configuration.observations ++ produced.observations }

/-- Reclaiming the consumed region commutes with one worklist step. -/
theorem eraseRetired_retainedStep
    (machine : Machine State Observation)
    (configuration : RetainedConfiguration State Observation) :
    (retainedStep machine configuration).map eraseRetired =
      regionStep machine (eraseRetired configuration) := by
  cases configuration with
  | mk pending retired observations =>
      cases pending <;> rfl

/-- Bounded execution of the retain-everything reference machine. -/
def retainedRun (machine : Machine State Observation) :
    Nat → RetainedConfiguration State Observation →
      RetainedConfiguration State Observation
  | 0, configuration => configuration
  | fuel + 1, configuration =>
      match retainedStep machine configuration with
      | none => configuration
      | some next => retainedRun machine fuel next

/-- Bounded execution with one reclaimable region per pending state. -/
def regionRun (machine : Machine State Observation) :
    Nat → RegionConfiguration State Observation →
      RegionConfiguration State Observation
  | 0, configuration => configuration
  | fuel + 1, configuration =>
      match regionStep machine configuration with
      | none => configuration
      | some next => regionRun machine fuel next

/-- Region reclamation preserves the exact residual FIFO queue and persistent
observation sequence at every finite budget. -/
theorem eraseRetired_retainedRun
    (machine : Machine State Observation) :
    ∀ fuel configuration,
      eraseRetired (retainedRun machine fuel configuration) =
        regionRun machine fuel (eraseRetired configuration)
  | 0, _ => rfl
  | fuel + 1, configuration => by
      cases configuration with
      | mk pending retired observations =>
          cases pending with
          | nil => rfl
          | cons current pending =>
              exact eraseRetired_retainedRun machine fuel {
                pending := pending ++ (machine current).successors
                retired := current :: retired
                observations :=
                  observations ++ (machine current).observations }

/-- Every successful reference step retains exactly one additional processed
state.  The compiled configuration has no corresponding field. -/
theorem retainedStep_retired_length
    (machine : Machine State Observation)
    (configuration next : RetainedConfiguration State Observation)
    (stepped : retainedStep machine configuration = some next) :
    next.retired.length = configuration.retired.length + 1 := by
  cases configuration with
  | mk pending retired observations =>
      cases pending with
      | nil => simp [retainedStep] at stepped
      | cons current pending =>
          simp [retainedStep] at stepped
          subst next
          simp

/-- Source package whose observable behavior excludes retired allocation
history. -/
structure RetainingWorklist
    (State : Type uState) (Observation : Type uObservation) where
  machine : Machine State Observation
  initial : List State

/-- Compiled artifact with the history-retention field removed. -/
structure RegionWorklist
    (State : Type uState) (Observation : Type uObservation) where
  machine : Machine State Observation
  initial : List State

/-- Erase the retain-everything policy while preserving the executable
transition program and initial frontier. -/
def compile (source : RetainingWorklist State Observation) :
    RegionWorklist State Observation :=
  { machine := source.machine, initial := source.initial }

/-- Common bounded observation: residual frontier plus persistent outputs. -/
abbrev ObservationAt (State : Type uState) (Observation : Type uObservation) :=
  List State × List Observation

def observeSource (source : RetainingWorklist State Observation)
    (fuel : Nat) : ObservationAt State Observation :=
  let final := retainedRun source.machine fuel {
    pending := source.initial
    retired := []
    observations := [] }
  (final.pending, final.observations)

def observeArtifact (artifact : RegionWorklist State Observation)
    (fuel : Nat) : ObservationAt State Observation :=
  let final := regionRun artifact.machine fuel {
    pending := artifact.initial
    observations := [] }
  (final.pending, final.observations)

/-- Compiling an escape-free worklist to per-state regions preserves every
bounded observation. -/
theorem observe_compile
    (source : RetainingWorklist State Observation) :
    observeArtifact (compile source) = observeSource source := by
  funext fuel
  have projected := eraseRetired_retainedRun source.machine fuel {
    pending := source.initial
    retired := []
    observations := [] }
  simpa [observeArtifact, observeSource, compile, eraseRetired] using
    (congrArg (fun final => (final.pending, final.observations)) projected).symm

/-- Worklist-region lowering as a composable certified realization. -/
def worklistRegionRealization :
    Mettapedia.GSLT.SimpleRealization
      (RetainingWorklist State Observation)
      (RegionWorklist State Observation)
      (Nat → ObservationAt State Observation) where
  compile := fun _ source => compile source
  observeSource := fun _ => observeSource
  observeArtifact := fun _ => observeArtifact
  adequate := fun _ => observe_compile

/-! ## Independent positive and negative canaries -/

private def descendingMachine : Machine Nat Nat
  | 0 => { successors := [], observations := [0] }
  | n + 1 => { successors := [n], observations := [n + 1] }

private def branchingMachine : Machine Bool String
  | false => { successors := [true, true], observations := ["fork"] }
  | true => { successors := [], observations := ["leaf"] }

/-- A linear evaluator retains the exact same residual state and trace after
region compilation. -/
example :
    observeArtifact (compile {
      machine := descendingMachine, initial := [3] }) 4 =
      ([], [3, 2, 1, 0]) := by
  decide

/-- A branching rule machine independently preserves FIFO multiplicity and
observation order. -/
example :
    observeArtifact (compile {
      machine := branchingMachine, initial := [false] }) 3 =
      ([], ["fork", "leaf", "leaf"]) := by
  decide

/-- Retired history is genuinely unobservable only under the declared
observation.  An observer that asks for allocation history would distinguish
configurations erased to the same region state and is therefore outside the
optimization's admitted contract. -/
example :
    let first : RetainedConfiguration Nat Nat := {
      pending := [1], retired := [], observations := [7] }
    let second : RetainedConfiguration Nat Nat := {
      pending := [1], retired := [9], observations := [7] }
    eraseRetired first = eraseRetired second ∧
      first.retired.length ≠ second.retired.length := by
  decide

end Mettapedia.GSLT.LanguageDef.WorklistRegionCompilation
