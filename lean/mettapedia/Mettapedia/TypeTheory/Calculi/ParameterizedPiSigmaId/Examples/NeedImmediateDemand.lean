import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedImmediateDemand
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalAdequacy
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.NeedNaturalAdequacy
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineExamples

/-! # Finite execution and admission controls -/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedNeedImmediateDemand
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false
open NeedReference ScopedNeedMachine ScopedNeedNaturalSemantics
open ScopedNeedComputation (Code)
variable {Head Operation Effect StableFault NativeFault : Type} {n m k : Nat}

namespace Controls

open ScopedNeedMachineExamples

/-- Complete worlds and optional completed outcomes remain visible; this
projection discards only control details and work, not receipts or caches. -/
def worldOutcomes (source : Source) :=
  (frontier 16 source).map fun machine => (machine.world, haltedOutcome machine)

/-- An actual effectful nondeterministic producer exercises both distinct
source forms. Their complete worlds agree, not merely their native answers. -/
theorem immediate_choice_worlds :
    worldOutcomes (immediateNeed producer) = worldOutcomes (immediateSequence producer) := by
  cbv

theorem immediate_choice_effects :
    observations 16 (immediateNeed producer) =
      [(some (.value (.head 10)), [7]), (some (.value (.head 20)), [7])] := rfl

def plain : Source := .returnValue (.head 42)

def protocol (machine : ExampleMachine) : Nat × Nat × Nat :=
  (machine.world.nextCell, machine.world.nextEvaluator, machine.world.receipts.nextSerial)

/-- Even a raw return acquires an allocation, entry, selection and observation
when it is executed as an owned suspension. Direct evaluation does not. -/
theorem direct_and_suspended_protocols :
    (frontier 64 plain).map protocol = [(0, 0, 0)] ∧
      (frontier 64 (immediateNeed plain)).map protocol = [(1, 1, 4)] := ⟨rfl, rfl⟩

theorem suspension_erasure_changes_world :
    worldOutcomes (immediateNeed plain) ≠ worldOutcomes plain := by
  intro equal
  have counts := congrArg (fun results => results.map fun result => result.1.nextCell) equal
  change [1] = ([0] : List Nat) at counts
  cases counts

end Controls

namespace NativeControls

open ScopedNeedMachine.PreservationExamples

abbrev NativeOperation := ScopedNeedMachine.PreservationExamples.Operation

def first : Code Tower.Head NativeOperation Nat 2 0 := .call .retain older

def body {handles : Nat} : Code Tower.Head NativeOperation Nat 3 handles :=
  .call .reflexivity (.var 0)

def direct : Code Tower.Head NativeOperation Nat 2 0 := .sequenceSigma first body

/-- `sequenceSigma (force 0)` creates a second cell whose origin forwards to
the first one. It is not an allocation-free native value bind. -/
def forwarding : Code Tower.Head NativeOperation Nat 2 0 :=
  .letNeed first (.sequenceSigma (.force 0) body)

theorem direct_typed : ScopedNeedComputation.Typing Tower.rules signature context Fin.elim0
    direct (.sigma ground identityFamily) :=
  .sequenceSigma sigma_formed (.sort _)
    (.call (operation_formation .retain) (.var 1))
    (.call (operation_formation .reflexivity) (.var 0))

theorem forwarding_typed : ScopedNeedComputation.Typing Tower.rules signature context Fin.elim0
    forwarding (.sigma ground identityFamily) := by
  refine .letNeed (.headType .legacyGround) (.sort Tower.zero) sigma_formed (.sort _)
    (.call (operation_formation .retain) (.var 1)) ?_
  exact .sequenceSigma sigma_formed (.sort _) (.force 0)
    (.call (operation_formation .reflexivity) (.var 0))

def completed (source : Code Tower.Head NativeOperation Nat 2 0) :=
  runFrontier (spec primitive) 32 [initial source ids]

theorem dependent_answers_agree :
    (completed direct).filterMap haltedOutcome = [.value (.pair older (.refl older))] ∧
      (completed forwarding).filterMap haltedOutcome = [.value (.pair older (.refl older))] := ⟨rfl, rfl⟩

/-- Native dependent typing does not hide the extra protocol allocation. -/
theorem forwarding_adds_cell_and_receipts :
    (completed direct).map (fun machine => (machine.world.nextCell, machine.world.receipts.nextSerial)) =
      [(1, 4)] ∧
    (completed forwarding).map (fun machine => (machine.world.nextCell, machine.world.receipts.nextSerial)) =
      [(2, 8)] := ⟨rfl, rfl⟩

theorem forwarding_worlds_differ :
    (completed forwarding).map (fun machine => machine.world) ≠
      (completed direct).map (fun machine => machine.world) := by
  intro equal
  have counts := congrArg (fun worlds => worlds.map fun world => world.nextCell) equal
  change [2] = ([1] : List Nat) at counts
  cases counts

end NativeControls

#print axioms Controls.immediate_choice_worlds

#print axioms Controls.immediate_choice_effects

#print axioms Controls.direct_and_suspended_protocols

#print axioms Controls.suspension_erasure_changes_world

#print axioms NativeControls.direct_typed

#print axioms NativeControls.forwarding_typed

#print axioms NativeControls.dependent_answers_agree

#print axioms NativeControls.forwarding_adds_cell_and_receipts

#print axioms NativeControls.forwarding_worlds_differ

end ScopedNeedImmediateDemand
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
