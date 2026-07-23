import Mettapedia.MachineLearning.NeuralNetworks.Architecture.StateCarrier
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Dynamics

/-!
# Fixed-address workspace carriers

This module factors the existing gated workspace recurrence through
`StateCarrier`.  It does not restate the workspace update: the carrier proposal
calls `GatedOperatorFamily.step`, and the conformance theorem exposes that
equality directly.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open StateCarrier
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

universe uEnvironment uSlow uCommand uSlot uOperator uContent uRead uLatent
  uObservation uPolicy

section Adapter

variable {Environment : Type uEnvironment} {Slow : Type uSlow}
  {Command : Type uCommand} {Slot : Type uSlot} {Operator : Type uOperator}
  {Content : Type uContent} {Read : Type uRead} {Latent : Type uLatent}
  {Observation : Type uObservation} {Policy : Type uPolicy}
  [Fintype Operator]
  [NormedAddCommGroup Content] [NormedSpace ℝ Content]

/-- Adapt a possibly command-indexed gated-operator family to the common
carrier interface.  The entire current workspace is the read, routing is
trivial at this layer, and the exact existing simultaneous update is the
replacement proposal. -/
noncomputable def gatedWorkspaceCarrier
    (initialState : Environment → Slow → Workspace Slot Content)
    (familyAt : Environment → Slow → Command →
      GatedOperatorFamily Slot Operator Content Read Latent)
    (observe : Environment → Slow → Workspace Slot Content → Observation)
    (policy : Environment → Slow → Observation → Policy) :
    StateCarrier Environment Slow Command (Workspace Slot Content)
      (Workspace Slot Content) Unit (Workspace Slot Content) Observation Policy where
  initialState := initialState
  read := fun _environment _slow workspace => workspace
  route := fun _environment _slow _command _workspace _read => ()
  propose := fun environment slow command _workspace read _route =>
    (familyAt environment slow command).step read
  write := fun _environment _slow _command _workspace _route proposal => proposal
  observe := observe
  policy := policy

/-- One carrier transition is exactly one step of the selected existing
gated-operator family. -/
@[simp] theorem gatedWorkspaceCarrier_step_eq
    (initialState : Environment → Slow → Workspace Slot Content)
    (familyAt : Environment → Slow → Command →
      GatedOperatorFamily Slot Operator Content Read Latent)
    (observe : Environment → Slow → Workspace Slot Content → Observation)
    (policy : Environment → Slow → Observation → Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (workspace : Workspace Slot Content) :
    (gatedWorkspaceCarrier initialState familyAt observe policy).step
        environment slow command workspace =
      (familyAt environment slow command).step workspace := rfl

end Adapter

/-! ## A fixed-family specialization and boundary fixtures -/

section FixedFamily

variable {Slot : Type uSlot} {Operator : Type uOperator}
  {Content : Type uContent} {Read : Type uRead} {Latent : Type uLatent}
  [Fintype Operator]
  [NormedAddCommGroup Content] [NormedSpace ℝ Content]

/-- A fixed gated family with its initial workspace supplied as immutable
environment.  Observation and policy expose the workspace itself. -/
noncomputable def fixedGatedWorkspaceCarrier :
    StateCarrier (Workspace Slot Content)
      (GatedOperatorFamily Slot Operator Content Read Latent) Unit
      (Workspace Slot Content) (Workspace Slot Content) Unit
      (Workspace Slot Content) (Workspace Slot Content) (Workspace Slot Content) :=
  gatedWorkspaceCarrier
    (fun initialWorkspace _family => initialWorkspace)
    (fun _initialWorkspace family _command => family)
    (fun _initialWorkspace _family workspace => workspace)
    (fun _initialWorkspace _family observation => observation)

/-- The fixed specialization retains exact one-step conformance. -/
@[simp] theorem fixedGatedWorkspaceCarrier_step_eq
    (initialWorkspace workspace : Workspace Slot Content)
    (family : GatedOperatorFamily Slot Operator Content Read Latent) :
    (fixedGatedWorkspaceCarrier (Slot := Slot) (Operator := Operator)
      (Content := Content) (Read := Read) (Latent := Latent)).step
        initialWorkspace family () workspace = family.step workspace := rfl

end FixedFamily

namespace WorkspaceCarrierFixtures

open WorkspaceDecoder.DynamicsFixtures

private noncomputable def zeroWorkspace : Workspace One ℝ := fun _slot => 0

/-- A nonzero gate moves the carrier's unique fixed address. -/
theorem unitGate_carrier_moves :
    ((fixedGatedWorkspaceCarrier
      (Slot := One) (Operator := One) (Content := ℝ) (Read := ℝ)
      (Latent := ℝ)).step zeroWorkspace (scalarFamily 1) () zeroWorkspace) 0
      ≠ (0 : ℝ) := by
  exact unitGate_moves_negativeExample

/-- A zero gate freezes the carrier's unique fixed address exactly. -/
theorem zeroGate_carrier_freezes (workspace : Workspace One ℝ) :
    ((fixedGatedWorkspaceCarrier
      (Slot := One) (Operator := One) (Content := ℝ) (Read := ℝ)
      (Latent := ℝ)).step workspace (scalarFamily 0) () workspace) 0 =
      workspace 0 := by
  exact zeroGate_freezes_positiveExample workspace

end WorkspaceCarrierFixtures

#print axioms gatedWorkspaceCarrier_step_eq
#print axioms fixedGatedWorkspaceCarrier_step_eq
#print axioms WorkspaceCarrierFixtures.unitGate_carrier_moves
#print axioms WorkspaceCarrierFixtures.zeroGate_carrier_freezes

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
