import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SouffleDatalogPrintedExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogCapturedInputTyping
import Mettapedia.Languages.Datalog.SpaceOutput

/-! Ordinary selected source, captured host inputs, retained execution and
declared output observations compose. Input typing follows from successful
capture. The isolated observation is a fact set; publication retains the
destination's existing occurrences. Native Space lifetime/effect adapters
remain implementation boundaries of these value-level laws. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat DatalogIR SouffleDatalog
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit
open Mettapedia.Machines.SetOutputPublication

/-- This is the declared output observation of a machine, not a second
execution of its rules. Equal fact values occur once. -/
def outputFacts (program : Program) (prepared : Executable.Prepared)
    (machine : ClosureMachine.Machine prepared) : List GroundFact :=
  (SpaceOutput.select program (machine.facts.filterMap (Executable.decodeFact? prepared))).eraseDups

@[simp] theorem mem_outputFacts (program : Program) (prepared : Executable.Prepared)
    (machine : ClosureMachine.Machine prepared) (fact : GroundFact) :
    fact ∈ outputFacts program prepared machine ↔
      fact ∈ machine.facts.filterMap (Executable.decodeFact? prepared) ∧
        fact.relation ∈ SpaceOutput.relations program := by
  simp [outputFacts]

theorem resumed_outputFacts (program : Program) (prepared : Executable.Prepared)
    (first second quantum : Nat) (machine : ClosureMachine.Machine prepared) :
    outputFacts program prepared (ClosureMachine.advance prepared (first + second) quantum machine) =
      outputFacts program prepared (ClosureMachine.advance prepared second quantum
        (ClosureMachine.advance prepared first quantum machine)) := by
  rw [ClosureMachine.advance_add]

/-- Retained sequential publication has the same eventual store at every
cut, including cuts that have already published some output facts. -/
theorem resumed_publication (program : Program) (prepared : Executable.Prepared)
    (machine : ClosureMachine.Machine prepared) (destination : List GroundFact) (budget : Nat) :
    publish (advance budget (⟨destination, outputFacts program prepared machine⟩ :
        Mettapedia.Machines.SetOutputPublication.State GroundFact)).store
      (advance budget (⟨destination, outputFacts program prepared machine⟩ :
        Mettapedia.Machines.SetOutputPublication.State GroundFact)).pending =
      publish destination (outputFacts program prepared machine) := advance_completion _ _

theorem run_captured_selected_source_outputs
    (state : Mettapedia.Languages.MeTTa.PeTTa.Effects.State) (environment : Engine.RelationEnv)
    (input : String) (tree : Frontend.SourceAtom) (program : Program)
    (forestBytes identityBytes : List UInt8) (verificationRounds : Nat)
    (verified : SourceCatalogueVerification.verify? SelectedSource.spec SourcePolicy.filters input forestBytes identityBytes
      [.expression [.symbol "result", tree, .symbol "nil"]] verificationRounds = some true)
    (read : Frontend.read input (.expression [.symbol "result", tree, .symbol "nil"]) = .ok program)
    (separator : String) (rows : List Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (seeds : List GroundFact) (captured : DatalogRuntimeCompiler.capture separator program rows = .ok seeds)
    (typed : ProgramStatic.ProgramTyped program)
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
          (∀ other, SelectedSource.ProgramMeaning environment input other → ∀ fact : GroundFact,
            fact ∈ outputFacts program prepared (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)) ↔
              Closure.Derives Executable.policy other seeds fact ∧ fact.relation ∈ SpaceOutput.relations other) ∧
          (∀ destination : List GroundFact, ∀ fact : GroundFact,
            fact ∈ publish destination (outputFacts program prepared
                (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared))) ↔
              fact ∈ destination ∨
                (Closure.Derives Executable.policy program seeds fact ∧ fact.relation ∈ SpaceOutput.relations program)) := by
  have inputs := DatalogRuntimeCompiler.capture_typed separator program rows seeds captured
  obtain ⟨forestComplete, catalogueComplete⟩ := SourceCatalogueVerification.verify?_sound _ _ _ _ _ _ _ verified
  obtain ⟨meaning, unique, prepared, accepted, ticks, complete, fault, returns, exactFacts⟩ :=
    run_complete_selected_native_source state environment input tree program
      forestBytes identityBytes verificationRounds verificationRounds forestComplete catalogueComplete read
      seeds typed inputs supported quantum positive
  refine ⟨meaning, unique, prepared, accepted, ticks, complete, fault, returns, ?_, ?_⟩
  · intro other otherMeaning fact
    rw [mem_outputFacts, exactFacts other otherMeaning fact, unique other otherMeaning]
  · intro destination fact
    rw [mem_publish, mem_outputFacts, exactFacts program meaning fact]

theorem output_publication_idempotent (program : Program) (prepared : Executable.Prepared)
    (machine : ClosureMachine.Machine prepared) (destination : List GroundFact) :
    publish (publish destination (outputFacts program prepared machine)) (outputFacts program prepared machine) =
      publish destination (outputFacts program prepared machine) := publish_idempotent _ _

theorem output_publication_preserves_occurrences (program : Program) (prepared : Executable.Prepared)
    (machine : ClosureMachine.Machine prepared) (destination : List GroundFact) (fact : GroundFact)
    (present : fact ∈ destination) :
    (publish destination (outputFacts program prepared machine)).count fact = destination.count fact :=
  publish_existing_count _ _ _ present

#print axioms run_captured_selected_source_outputs
#print axioms resumed_outputFacts
#print axioms resumed_publication

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
