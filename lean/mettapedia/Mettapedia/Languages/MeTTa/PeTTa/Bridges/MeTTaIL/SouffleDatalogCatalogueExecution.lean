import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SouffleDatalogFrontendExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogCatalogueUniqueness
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSelectedSource

/-! A checked complete singleton unfiltered catalogue fixes the raw grammar's
program meaning. This theorem retains its explicit empty-filter premise;
the declared reserved-word policy needs the selected-source adequacy join. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat DatalogIR SouffleDatalog
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem run_complete_native_source (state : State) (environment : Engine.RelationEnv)
    (input : String) (tree : Frontend.SourceAtom) (program : Program)
    (forestBytes identityBytes : List UInt8) (forestRounds catalogueRounds : Nat)
    (forestComplete : SourceSyntaxForest.complete? CatalogueCoverage.spec input forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : SourceCatalogue.validate? CatalogueCoverage.spec [] input forestBytes identityBytes
      [.expression [.symbol "result", tree, .symbol "nil"]] catalogueRounds = some true)
    (read : Frontend.read input (.expression [.symbol "result", tree, .symbol "nil"]) = .ok program)
    (seeds : List GroundFact) (typed : ProgramStatic.ProgramTyped program)
    (inputs : ∀ fact ∈ seeds, StaticTyping.FactTyped (ProgramStatic.signature program) fact)
    (supported : Executable.Nonfloating program seeds) (quantum : Nat) (positive : 0 < quantum) :
    ReferenceReader.SourceProgram (stringScalars input) program ∧
      (∀ other, ReferenceReader.SourceProgram (stringScalars input) other → other = program) ∧
      ∃ prepared, Executable.prepare program seeds = .ok prepared ∧
        ∃ ticks,
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).complete = true ∧
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).fault = none ∧
          PureReturns runtime [] state
            (apply "gslt:snapshot:advance"
              [encoded (ClosureMachine.machineTerm prepared (ClosureMachine.begin prepared)), number ticks, number quantum]) state
            (encoded (ClosureMachine.machineTerm prepared
              (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)))) ∧
          ∀ other, ReferenceReader.SourceProgram (stringScalars input) other → ∀ fact : GroundFact,
            fact ∈ ((ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).facts.filterMap
              (Executable.decodeFact? prepared)) ↔ Closure.Derives Executable.policy other seeds fact := by
  obtain ⟨source, _, prepared, preparedRead, ticks, complete, fault, returns, exactFacts⟩ :=
    run_source_checked_frontend state environment input tree program read seeds typed inputs supported quantum positive
  have unique : ∀ other, ReferenceReader.SourceProgram (stringScalars input) other → other = program :=
    fun other otherSource => CatalogueCoverage.checked_unique_program forestComplete catalogueComplete
      other program otherSource source
  refine ⟨source, unique, prepared, preparedRead, ticks, complete, fault, returns, ?_⟩
  intro other otherSource fact
  rw [unique other otherSource]
  exact exactFacts fact

theorem run_complete_selected_native_source (state : State) (environment : Engine.RelationEnv)
    (input : String) (tree : Frontend.SourceAtom) (program : Program)
    (forestBytes identityBytes : List UInt8) (forestRounds catalogueRounds : Nat)
    (forestComplete : SourceSyntaxForest.complete? SelectedSource.spec input forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : SourceCatalogue.validate? SelectedSource.spec SourcePolicy.filters input forestBytes identityBytes
      [.expression [.symbol "result", tree, .symbol "nil"]] catalogueRounds = some true)
    (read : Frontend.read input (.expression [.symbol "result", tree, .symbol "nil"]) = .ok program)
    (seeds : List GroundFact) (typed : ProgramStatic.ProgramTyped program)
    (inputs : ∀ fact ∈ seeds, StaticTyping.FactTyped (ProgramStatic.signature program) fact)
    (supported : Executable.Nonfloating program seeds) (quantum : Nat) (positive : 0 < quantum) :
    SelectedSource.ProgramMeaning environment input program ∧
      (∀ other, SelectedSource.ProgramMeaning environment input other → other = program) ∧
      ∃ prepared, Executable.prepare program seeds = .ok prepared ∧
        ∃ ticks,
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).complete = true ∧
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).fault = none ∧
          PureReturns runtime [] state
            (apply "gslt:snapshot:advance"
              [encoded (ClosureMachine.machineTerm prepared (ClosureMachine.begin prepared)), number ticks, number quantum]) state
            (encoded (ClosureMachine.machineTerm prepared
              (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)))) ∧
          ∀ other, SelectedSource.ProgramMeaning environment input other → ∀ fact : GroundFact,
            fact ∈ ((ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).facts.filterMap
              (Executable.decodeFact? prepared)) ↔ Closure.Derives Executable.policy other seeds fact := by
  obtain ⟨_, _, prepared, preparedRead, ticks, complete, fault, returns, exactFacts⟩ :=
    run_source_checked_frontend state environment input tree program read seeds typed inputs supported quantum positive
  have source := SelectedSource.read_sound environment input tree program read
  have unique : ∀ other, SelectedSource.ProgramMeaning environment input other → other = program :=
    fun other otherSource => SelectedSource.checked_unique_program forestComplete catalogueComplete
      environment other program otherSource source
  refine ⟨source, unique, prepared, preparedRead, ticks, complete, fault, returns, ?_⟩
  intro other otherSource fact
  rw [unique other otherSource]
  exact exactFacts fact

#print axioms run_complete_native_source
#print axioms run_complete_selected_native_source

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
