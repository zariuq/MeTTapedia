import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedRecordedExecution

/-!
# Captured source application on the recorded execution machines

These are operational controls over raw native-domain functions. They do not
assert a dependent typing judgment without its independent source formation
and primitive contracts. Both machines retain the actual shared Need cells.
-/

open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedNeedRecordedExecution.Controls

open NeedReference ScopedNeedMachine ScopedNeedComputation ScopedNeedComputationFunction

def primitive (_ : Unit) (argument : Tm Nat 0) : Produced (Tm Nat 0) Nat Nat := .value argument

def producer : Code Nat Unit Nat 1 0 :=
  .emit 5 (.choose (.returnValue (.var 0)) (.returnValue (.head 8)))

def function : Function Nat Unit Nat 0 0 where
  domain := .head 0
  result := .sigma (.head 0) (.head 0)
  body := .letNeed producer (.sequenceSigma (.force 0) (.force 0))

def origin : Closure Nat Unit Nat 0 := function.open ids Fin.elim0 (.head 7)

def world : NeedWorld Nat Unit Nat Nat Nat 0 :=
  ⟨0, [], .empty, .empty, 0, 0⟩

def observe (machine : NeedMachine Nat Unit Nat Nat Nat 0) :=
  (NeedReference.haltedOutcome machine, machine.world.receipts.effects)

theorem recorded_application_shares_the_captured_choice :
    ((recordedFrontier primitive 100 origin world).mapM NeedExecution.CoreMachine.readback?).map
        (List.map observe) =
      some [(some (.value (.pair (.head 7) (.head 7))), [5]),
        (some (.value (.pair (.head 8) (.head 8))), [5])] := by
  decide +kernel

theorem shared_coordinator_realizes_the_same_completed_observation :
    (sharedReadback primitive 150 origin world).map (List.map observe) =
      some [(some (.value (.pair (.head 7) (.head 7))), [5]),
        (some (.value (.pair (.head 8) (.head 8))), [5])] := by
  decide +kernel

def independentFunction : Function Nat Unit Nat 0 0 where
  domain := .head 0
  result := .sigma (.head 0) (.head 0)
  body := .letNeed producer
    (.letNeed (producer.renameHandles Fin.elim0) (.sequenceSigma (.force 1) (.force 0)))

theorem independent_allocations_change_choice_and_effect_multiplicity :
    ((recordedFrontier primitive 120
      (independentFunction.open ids Fin.elim0 (.head 7)) world).mapM
        NeedExecution.CoreMachine.readback?).map (List.map observe) =
      some [(some (.value (.pair (.head 7) (.head 7))), [5, 5]),
        (some (.value (.pair (.head 7) (.head 8))), [5, 5]),
        (some (.value (.pair (.head 8) (.head 7))), [5, 5]),
        (some (.value (.pair (.head 8) (.head 8))), [5, 5])] := by
  decide +kernel

theorem unfinished_recorded_work_is_not_a_source_refutation :
    ((recordedFrontier primitive 1 origin world).filterMap NeedExecution.haltedOutcome) = [] ∧
      ((recordedFrontier primitive 100 origin world).filterMap NeedExecution.haltedOutcome).length = 2 := by
  constructor <;> decide +kernel

end ScopedNeedRecordedExecution.Controls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
