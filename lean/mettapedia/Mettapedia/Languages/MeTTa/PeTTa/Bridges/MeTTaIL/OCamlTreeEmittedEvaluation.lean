import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedFiniteEvaluation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceTreeEvaluation

/-! Actual source lowering, expression-tree evaluation and named emitted
execution compose. Completed readout agrees with any finite tree evaluation;
general target termination reflection remains a separate obligation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTreeEmittedEvaluation

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlEmittedEntrySource OCamlEmittedWrapperExecution OCamlTerminalObservation
open OCamlInstallExecution OCamlControllerInvariant DeclarativeSpec

theorem finite_source_tree_realized (state : State) (program : OCaml.Program) (tree : OCaml.TreeProgram)
    (input : String) (source : ModuleFormat.SourcePacket.Packet) (prepared : Prepared)
    (name : String) (emitted : SpaceSemantics.Program) (result : OCaml.TreeResult) (quantum : Nat)
    (lowered : ModuleFormat.OCamlSourceLowering.lower input source = .ok program)
    (parsed : ModuleFormat.OCamlSourceLowering.lowerTree input source = .ok tree)
    (preparedSource : prepare program = .ok prepared) (built : ExecutionData.emit? prepared name = .ok emitted)
    (evaluation : OCaml.TreeEvaluates tree.constructors [] tree.expression result) (positive : 0 < quantum) :
    ∃ (actual : OCaml.Result) (ticks : Nat) (epochs current : Term), OCaml.TreeResultRelated program.code result actual ∧
      PureReturns (moduleRuntime prepared name) [] state
        (apply (ExecutionData.runHead name) [number ticks, number quantum]) state
        (encoded (.application "MlResult" [.symbol "MlComplete", InferenceCettaWire.encodePattern (resultPattern actual), epochs, current])) := by
  obtain ⟨constructors, read⟩ := ModuleFormat.OCamlSourceLowering.lower_tree_graph lowered parsed
  have evaluated : OCaml.TreeEvaluates program.constructors [] tree.expression result := constructors ▸ evaluation
  obtain ⟨actual, indexed, related⟩ := evaluated.toIndexed program read .nil
  obtain ⟨ticks, epochs, current, executed⟩ := OCamlEmittedFiniteEvaluation.finite_evaluation_realized state program prepared name emitted actual quantum
    preparedSource built indexed positive
  exact ⟨actual, ticks, epochs, current, related, executed⟩

theorem completed_source_tree_readback (state after : State) (program : OCaml.Program) (tree : OCaml.TreeProgram)
    (input : String) (source : ModuleFormat.SourcePacket.Packet) (prepared : Prepared)
    (name : String) (emitted : SpaceSemantics.Program) (result : OCaml.TreeResult) (observed : OCaml.Result)
    (ticks quantum : Nat) (epochs current : Term)
    (lowered : ModuleFormat.OCamlSourceLowering.lower input source = .ok program)
    (parsed : ModuleFormat.OCamlSourceLowering.lowerTree input source = .ok tree)
    (preparedSource : prepare program = .ok prepared) (built : ExecutionData.emit? prepared name = .ok emitted)
    (evaluation : OCaml.TreeEvaluates tree.constructors [] tree.expression result)
    (completed : Runs (moduleRuntime prepared name) {state := state, control := .evaluate [] (apply
      (ExecutionData.runHead name) [number ticks, number quantum])}
      (.complete after [encoded (.application "MlResult" [.symbol "MlComplete",
        InferenceCettaWire.encodePattern (resultPattern observed), epochs, current])] [] [])) :
    OCaml.TreeResultRelated program.code result observed := by
  obtain ⟨constructors, read⟩ := ModuleFormat.OCamlSourceLowering.lower_tree_graph lowered parsed
  have evaluated : OCaml.TreeEvaluates program.constructors [] tree.expression result := constructors ▸ evaluation
  obtain ⟨actual, indexed, related⟩ := evaluated.toIndexed program read .nil
  have same := OCamlEmittedFiniteEvaluation.completed_run_readback state after program prepared name emitted actual observed
    ticks quantum epochs current preparedSource built indexed completed
  exact same.symm ▸ related

#print axioms finite_source_tree_realized
#print axioms completed_source_tree_readback

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTreeEmittedEvaluation
