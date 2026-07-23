import Mettapedia.MachineLearning.NeuralNetworks.Architecture.StateCarrier
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromInheritance

/-!
# Routed CAROM carriers

This module adapts routed triple-slot CAROM state without moving immutable
evidence or fixed parameters into the mutable carrier projection.  Commands
are observed only through their declared routing image.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open StateCarrier
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCarom

universe uEnvironment uSlow uCommand uExpert uSlot uEvidence uFixed uContent
  uObservation uPolicy

section RoutedAdapter

variable {Environment : Type uEnvironment} {Slow : Type uSlow}
  {Command : Type uCommand} {Expert : Type uExpert} [Fintype Expert]
  {Slot : Type uSlot} {Evidence : Type uEvidence} {Fixed : Type uFixed}
  {Content : Type uContent} {Observation : Type uObservation}
  {Policy : Type uPolicy}

/-- Route a command to a simplex point, update only the workspace projection,
and retain evidence and fixed slot parameters by construction. -/
def routedTripleSlotCarrier
    (initialState : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content)
    (route : Environment → Slow → Command → SimplexWeights Expert)
    (nextWorkspace : Environment → Slow → SimplexWeights Expert →
      Workspace Slot Content → Workspace Slot Content)
    (observe : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content → Observation)
    (policy : Environment → Slow → Observation → Policy) :
    StateCarrier Environment Slow Command
      (TripleSlotState Slot Evidence Fixed Content) (Workspace Slot Content)
      (SimplexWeights Expert) (Workspace Slot Content) Observation Policy where
  initialState := initialState
  read := fun _environment _slow state => state.workspace
  route := fun environment slow command _state _read =>
    route environment slow command
  propose := fun environment slow _command _state read routing =>
    nextWorkspace environment slow routing read
  write := fun _environment _slow _command state _routing proposal =>
    state.updateWorkspace (fun _oldWorkspace => proposal)
  observe := observe
  policy := policy

/-- One routed carrier step is exactly the existing workspace-only update of
the triple-slot state. -/
@[simp] theorem routedTripleSlotCarrier_step_eq
    (initialState : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content)
    (route : Environment → Slow → Command → SimplexWeights Expert)
    (nextWorkspace : Environment → Slow → SimplexWeights Expert →
      Workspace Slot Content → Workspace Slot Content)
    (observe : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content → Observation)
    (policy : Environment → Slow → Observation → Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (state : TripleSlotState Slot Evidence Fixed Content) :
    (routedTripleSlotCarrier initialState route nextWorkspace observe policy).step
        environment slow command state =
      state.updateWorkspace
        (nextWorkspace environment slow (route environment slow command)) := rfl

/-- Carrier recurrence agrees exactly with the existing routed schedule fold. -/
theorem routedTripleSlotCarrier_run_eq
    (initialState : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content)
    (route : Environment → Slow → Command → SimplexWeights Expert)
    (nextWorkspace : Environment → Slow → SimplexWeights Expert →
      Workspace Slot Content → Workspace Slot Content)
    (observe : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content → Observation)
    (policy : Environment → Slow → Observation → Policy)
    (environment : Environment) (slow : Slow)
    (state : TripleSlotState Slot Evidence Fixed Content)
    (commands : List Command) :
    (routedTripleSlotCarrier initialState route nextWorkspace observe policy).run
        environment slow state commands =
      runTripleSlotSchedule (nextWorkspace environment slow)
        (commands.map (route environment slow)) state := by
  induction commands generalizing state with
  | nil => rfl
  | cons command commands inductionHypothesis =>
      exact inductionHypothesis
        (state.updateWorkspace
          (nextWorkspace environment slow (route environment slow command)))

/-- Immutable evidence survives every finite carrier schedule. -/
theorem routedTripleSlotCarrier_run_evidence
    (initialState : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content)
    (route : Environment → Slow → Command → SimplexWeights Expert)
    (nextWorkspace : Environment → Slow → SimplexWeights Expert →
      Workspace Slot Content → Workspace Slot Content)
    (observe : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content → Observation)
    (policy : Environment → Slow → Observation → Policy)
    (environment : Environment) (slow : Slow)
    (state : TripleSlotState Slot Evidence Fixed Content)
    (commands : List Command) :
    ((routedTripleSlotCarrier initialState route nextWorkspace observe policy).run
      environment slow state commands).evidence = state.evidence := by
  rw [routedTripleSlotCarrier_run_eq]
  exact runTripleSlotSchedule_evidence _ _ _

/-- Fixed per-slot parameters survive every finite carrier schedule. -/
theorem routedTripleSlotCarrier_run_fixed
    (initialState : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content)
    (route : Environment → Slow → Command → SimplexWeights Expert)
    (nextWorkspace : Environment → Slow → SimplexWeights Expert →
      Workspace Slot Content → Workspace Slot Content)
    (observe : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content → Observation)
    (policy : Environment → Slow → Observation → Policy)
    (environment : Environment) (slow : Slow)
    (state : TripleSlotState Slot Evidence Fixed Content)
    (commands : List Command) :
    ((routedTripleSlotCarrier initialState route nextWorkspace observe policy).run
      environment slow state commands).fixed = state.fixed := by
  rw [routedTripleSlotCarrier_run_eq]
  exact runTripleSlotSchedule_fixed _ _ _

/-- Command syntax is opaque beyond its routing image: equal routed schedules
produce equal complete carrier states. -/
theorem routedTripleSlotCarrier_run_eq_of_routeSchedules_eq
    (initialState : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content)
    (route : Environment → Slow → Command → SimplexWeights Expert)
    (nextWorkspace : Environment → Slow → SimplexWeights Expert →
      Workspace Slot Content → Workspace Slot Content)
    (observe : Environment → Slow →
      TripleSlotState Slot Evidence Fixed Content → Observation)
    (policy : Environment → Slow → Observation → Policy)
    (environment : Environment) (slow : Slow)
    (state : TripleSlotState Slot Evidence Fixed Content)
    (first second : List Command)
    (routesEqual : first.map (route environment slow) =
      second.map (route environment slow)) :
    (routedTripleSlotCarrier initialState route nextWorkspace observe policy).run
        environment slow state first =
      (routedTripleSlotCarrier initialState route nextWorkspace observe policy).run
        environment slow state second := by
  rw [routedTripleSlotCarrier_run_eq, routedTripleSlotCarrier_run_eq,
    routesEqual]

end RoutedAdapter

/-! ## Routed gated-operator specialization -/

section RoutedGated

variable {Expert : Type uExpert} [Fintype Expert]
  {Slot : Type uSlot} {Operator : Type*} {Content : Type uContent}
  {Read : Type*} {Latent : Type*} [Fintype Operator]
  [NormedAddCommGroup Content] [NormedSpace ℝ Content]

/-- The routed mixture of existing gated-operator experts as a triple-slot
carrier. -/
noncomputable def routedGatedTripleSlotCarrier
    {Evidence : Type uEvidence} {Fixed : Type uFixed} :
    StateCarrier (TripleSlotState Slot Evidence Fixed Content)
      (Expert → GatedOperatorFamily Slot Operator Content Read Latent)
      (SimplexWeights Expert) (TripleSlotState Slot Evidence Fixed Content)
      (Workspace Slot Content) (SimplexWeights Expert) (Workspace Slot Content)
      (Workspace Slot Content) (Workspace Slot Content) :=
  routedTripleSlotCarrier
    (fun initial _experts => initial)
    (fun _initial _experts routing => routing)
    (fun _initial experts routing workspace =>
      routedGatedStep routing experts workspace)
    (fun _initial _experts state => state.workspace)
    (fun _initial _experts observation => observation)

/-- The specialization exposes exactly the sealed routed gated step in its
workspace projection. -/
@[simp] theorem routedGatedTripleSlotCarrier_step_workspace
    {Evidence : Type uEvidence} {Fixed : Type uFixed}
    (initial state : TripleSlotState Slot Evidence Fixed Content)
    (experts : Expert → GatedOperatorFamily Slot Operator Content Read Latent)
    (routing : SimplexWeights Expert) :
    ((routedGatedTripleSlotCarrier (Expert := Expert) (Slot := Slot)
      (Operator := Operator) (Content := Content) (Read := Read)
      (Latent := Latent)).step initial experts routing state).workspace =
      routedGatedStep routing experts state.workspace := rfl

/-- When every expert is the same gated family, routing leaves that exact
workspace step unchanged. -/
theorem routedGatedTripleSlotCarrier_constantExperts
    {Evidence : Type uEvidence} {Fixed : Type uFixed}
    (initial state : TripleSlotState Slot Evidence Fixed Content)
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (routing : SimplexWeights Expert) :
    ((routedGatedTripleSlotCarrier (Expert := Expert) (Slot := Slot)
      (Operator := Operator) (Content := Content) (Read := Read)
      (Latent := Latent)).step initial (fun _expert => family) routing state).workspace =
      family.step state.workspace := by
  rw [routedGatedTripleSlotCarrier_step_workspace]
  exact routedGatedStep_constantExperts routing family state.workspace

end RoutedGated

namespace CaromCarrierFixtures

open WorkspaceDecoder.DynamicsFixtures

private noncomputable def zeroState : TripleSlotState One Nat Nat ℝ where
  evidence := fun _slot => 7
  fixed := fun _slot => 11
  workspace := fun _slot => 0

/-- The routed CAROM carrier is nondegenerate: a unit-gated constant expert
moves the mutable workspace under a valid simplex route. -/
theorem routedCarrier_moves_workspace :
    (((routedGatedTripleSlotCarrier
      (Expert := Fin 2) (Slot := One) (Operator := One) (Content := ℝ)
      (Read := ℝ) (Latent := ℝ)).step zeroState
        (fun _expert => scalarFamily 1) halfRouting zeroState).workspace 0) ≠ 0 := by
  rw [routedGatedTripleSlotCarrier_constantExperts]
  exact unitGate_moves_negativeExample

/-- Distinct Boolean commands are observationally opaque when the router maps
both to the same simplex point. -/
theorem equalRoute_booleanCommands_are_opaque :
    let carrier := routedTripleSlotCarrier
      (fun (_environment : Unit) (_slow : Unit) => zeroState)
      (fun _environment _slow (_command : Bool) => halfRouting)
      (fun _environment _slow _routing workspace => workspace)
      (fun _environment _slow state => state.workspace)
      (fun _environment _slow observation => observation)
    carrier.run () () zeroState [false] =
      carrier.run () () zeroState [true] := by
  dsimp only
  apply routedTripleSlotCarrier_run_eq_of_routeSchedules_eq
  rfl

end CaromCarrierFixtures

#print axioms routedTripleSlotCarrier_step_eq
#print axioms routedTripleSlotCarrier_run_eq
#print axioms routedTripleSlotCarrier_run_evidence
#print axioms routedTripleSlotCarrier_run_fixed
#print axioms routedTripleSlotCarrier_run_eq_of_routeSchedules_eq
#print axioms routedGatedTripleSlotCarrier_constantExperts
#print axioms CaromCarrierFixtures.routedCarrier_moves_workspace
#print axioms CaromCarrierFixtures.equalRoute_booleanCommands_are_opaque

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
