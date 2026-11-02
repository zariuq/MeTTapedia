import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontendMeaning
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueMeaning

/-! Datalog's declared source profile composes with its independent program
meaning. Native singleton/empty catalogue claims range over the selected
grammar, including reserved identifiers, rather than an unfiltered surrogate. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SelectedSource

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

def ProgramMeaning (environment : Engine.RelationEnv) (input : String) (program : Program) : Prop :=
  ∃ core, SourcePacketSelection.Source SourcePrinter.description SelectedReader.parser SourcePolicy.filters
    (input.toList.map Char.toNat) "DlProgram" core ∧ SourceMeaning.Denotes environment core program

theorem read_sound (environment : Engine.RelationEnv) (input : String) (tree : Frontend.SourceAtom)
    (program : Program)
    (read : Frontend.read input (.expression [.symbol "result", tree, .symbol "nil"]) = .ok program) :
    ProgramMeaning environment input program := by
  obtain ⟨core, coreRead, _, meaning⟩ := SourceMeaning.read_sound environment input tree program read
  exact ⟨core, SelectedReader.core?_source coreRead, meaning⟩

theorem read_complete (environment : Engine.RelationEnv) (input : String) (program : Program)
    (source : ProgramMeaning environment input program) :
    ∃ tree, Frontend.read input (.expression [.symbol "result", tree, .symbol "nil"]) = .ok program := by
  obtain ⟨core, selected, meaning⟩ := source
  obtain ⟨tree, read⟩ := SelectedReader.source_has_packet selected
  exact ⟨tree, SourceMeaning.read_complete environment input tree core program read meaning⟩

theorem read_exact (environment : Engine.RelationEnv) (input : String) (program : Program) :
    ProgramMeaning environment input program ↔
      ∃ tree, Frontend.read input (.expression [.symbol "result", tree, .symbol "nil"]) = .ok program :=
  ⟨read_complete environment input program, fun ⟨tree, read⟩ => read_sound environment input tree program read⟩

def spec : Portable.SyntaxDescription := ⟨SourceViews.grammar, SourceViews.profile⟩

theorem source_program_returned {input : String} {forestBytes identityBytes : List UInt8}
    {packets : List SourcePacket.Packet} {forestRounds catalogueRounds : Nat}
    (forestComplete : SourceSyntaxForest.complete? spec input forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : SourceCatalogue.validate? spec SourcePolicy.filters input
      forestBytes identityBytes packets catalogueRounds = some true)
    (environment : Engine.RelationEnv) (program : Program) (source : ProgramMeaning environment input program) :
    ∃ packet ∈ packets, ∃ tree core, SourceCatalogue.packetTree? packet = some tree ∧
      SelectedReader.core? input tree = some core ∧ SourceMeaning.Denotes environment core program := by
  obtain ⟨core, selected, meaning⟩ := source
  have start : SelectedReader.parser.plan.lexical.startSort = "DlProgram" := SourceReader.agreement.startSort_eq
  have selected' : SourcePacketSelection.Source SourcePrinter.description SelectedReader.parser SourcePolicy.filters
      (input.toList.map Char.toNat) SelectedReader.parser.plan.lexical.startSort core := by
    simpa only [start] using selected
  obtain ⟨packet, member, tree, packetRead, coreRead⟩ := SourceCatalogue.selected_source_returned
    SelectedReader.parser SourcePrinter.description_shape forestComplete catalogueComplete selected'
  exact ⟨packet, member, tree, core, packetRead, by simpa only [SelectedReader.core?, start] using coreRead, meaning⟩

theorem checked_unique_program {input : String} {forestBytes identityBytes : List UInt8}
    {packet : SourcePacket.Packet} {forestRounds catalogueRounds : Nat}
    (forestComplete : SourceSyntaxForest.complete? spec input forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : SourceCatalogue.validate? spec SourcePolicy.filters input
      forestBytes identityBytes [packet] catalogueRounds = some true)
    (environment : Engine.RelationEnv) (first second : Program)
    (firstSource : ProgramMeaning environment input first) (secondSource : ProgramMeaning environment input second) :
    first = second := by
  obtain ⟨left, leftMember, leftTree, leftCore, leftPacket, leftRead, leftMeaning⟩ :=
    source_program_returned forestComplete catalogueComplete environment first firstSource
  obtain ⟨right, rightMember, rightTree, rightCore, rightPacket, rightRead, rightMeaning⟩ :=
    source_program_returned forestComplete catalogueComplete environment second secondSource
  have leftSame := List.mem_singleton.mp leftMember
  have rightSame := List.mem_singleton.mp rightMember
  subst left
  subst right
  have treeSame := Option.some.inj (leftPacket.symm.trans rightPacket)
  subst rightTree
  have coreSame := Option.some.inj (leftRead.symm.trans rightRead)
  subst rightCore
  exact SourceMeaning.denotes_functional environment leftCore first second leftMeaning rightMeaning

theorem checked_empty_has_no_source {input : String} {forestBytes identityBytes : List UInt8}
    {forestRounds catalogueRounds : Nat}
    (forestComplete : SourceSyntaxForest.complete? spec input forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : SourceCatalogue.validate? spec SourcePolicy.filters input
      forestBytes identityBytes [] catalogueRounds = some true)
    (environment : Engine.RelationEnv) (program : Program) : ¬ ProgramMeaning environment input program := by
  intro source
  obtain ⟨packet, member, _⟩ := source_program_returned forestComplete catalogueComplete environment program source
  cases member

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SelectedSource
