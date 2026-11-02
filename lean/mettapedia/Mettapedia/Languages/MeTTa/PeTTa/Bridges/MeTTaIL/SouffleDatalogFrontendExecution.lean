import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SouffleDatalogReferenceExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontendSource

/-! Accepted ordinary source reaches the independent source semantics and
the retained MeTTa closure. The source judgment is derived from the actual
frontend check, rather than supplied as a second assumption. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem run_source_checked_frontend (state : State) (environment : Engine.RelationEnv)
    (input : String) (tree : Frontend.SourceAtom) (program : Program)
    (read : Frontend.read input (.expression [.symbol "result", tree, .symbol "nil"]) = .ok program)
    (seeds : List GroundFact) (typed : ProgramStatic.ProgramTyped program)
    (inputs : ∀ fact ∈ seeds, StaticTyping.FactTyped (ProgramStatic.signature program) fact)
    (supported : Executable.Nonfloating program seeds)
    (quantum : Nat) (positive : 0 < quantum) :
    ReferenceReader.SourceProgram (stringScalars input) program ∧
      program ∈ ReferenceReader.programs (stringScalars input) ∧
      ∃ prepared, Executable.prepare program seeds = .ok prepared ∧
        ∃ ticks,
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).complete = true ∧
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).fault = none ∧
          PureReturns runtime [] state
            (apply "gslt:snapshot:advance"
              [encoded (ClosureMachine.machineTerm prepared (ClosureMachine.begin prepared)), number ticks, number quantum]) state
            (encoded (ClosureMachine.machineTerm prepared
              (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)))) ∧
          ∀ fact : GroundFact,
            fact ∈ ((ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).facts.filterMap
              (Executable.decodeFact? prepared)) ↔ Closure.Derives Executable.policy program seeds fact := by
  have source := Frontend.read_source environment input tree program read
  exact ⟨source, run_complete_source_reference state (stringScalars input) program source
    seeds typed inputs supported quantum positive⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
