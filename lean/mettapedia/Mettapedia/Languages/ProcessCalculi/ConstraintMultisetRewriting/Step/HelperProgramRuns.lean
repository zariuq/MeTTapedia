import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperProgramEvents
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRunObservations

/-!
# Native realization of every finite origin-indexed program execution

The contextual event profile has the same complete choice fibres as the two
asynchronous component programs. Each finite execution constructs an actual
native run, its final placement isomorphism and its ordered declaration
observations. The origin-indexed executions remain the record: erasure to
primitive native firings is not asserted to be injective.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextProgram

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open EventMultiplicity
variable {S : Signature} {O : Type} [DecidableEq O]

structure ExecutionResult {count : Nat} {pair : ContextProgram S O} (run : system.Execution count pair) where
  execution : helperStep.Run pair.place.state
  resultIso : helperTransport.Iso execution.last (system.last run).place.state
  length_preserved : execution.word.length = count

def realize : ∀ {count : Nat} {pair : ContextProgram S O} (run : system.Execution count pair), ExecutionResult run
  | 0, pair, _run => ⟨.nil _, helperTransport.refl pair.place.state, rfl⟩
  | _ + 1, pair, ⟨choice, rest⟩ => by
      let later := realize rest
      let invStep := helperTransport.symm (pair.resultIso choice)
      let moved := helperTransport.moveRun invStep later.execution
      refine ⟨.cons (pair.originFiring choice.val) choice.property moved,
        helperTransport.trans (helperTransport.symm (helperTransport.moveRunEndIso invStep later.execution)) later.resultIso, ?_⟩
      have unchanged := Transport.Similar.length_eq (Transport.Similar.moveRun invStep later.execution)
      change moved.word.length + 1 = _ + 1
      rw [← unchanged, later.length_preserved]

theorem realize_word : ∀ {count : Nat} {pair : ContextProgram S O} (run : system.Execution count pair),
    helperWord (realize run).execution = system.word run
  | 0, _, _ => rfl
  | _ + 1, pair, ⟨choice, rest⟩ => by
      change (pair.originFiring choice.val).helper :: helperWord
        (helperTransport.moveRun (helperTransport.symm (pair.resultIso choice)) (realize rest).execution) =
          (pair.originFiring choice.val).helper :: system.word rest
      rw [helperWord_moveRun, realize_word]

def executions (pair : ContextProgram S O) (count : Nat) :
    (asynchronous Program.system Program.system).Execution count pair.project ≃ system.Execution count pair :=
  (projection.executions count rfl).symm

def realizeComponents {pair : ContextProgram S O} {count : Nat}
    (run : (asynchronous Program.system Program.system).Execution count pair.project) :
    ExecutionResult (pair.executions count run) := realize (pair.executions count run)

theorem component_word {pair : ContextProgram S O} {count : Nat}
    (run : (asynchronous Program.system Program.system).Execution count pair.project) :
    helperWord (realizeComponents run).execution = (asynchronous Program.system Program.system).word run := by
  rw [realizeComponents, realize_word]
  have related := projection.execution_word rfl (pair.executions count run)
  simpa only [executions, Equiv.apply_symm_apply] using related.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextProgram
