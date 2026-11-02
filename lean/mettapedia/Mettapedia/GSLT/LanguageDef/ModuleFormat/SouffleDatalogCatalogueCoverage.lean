import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueMeaning
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPacketCoverage

/-! Complete unfiltered catalogues cover the raw Datalog grammar and its
independent program IR. The declared source profile additionally rejects
reserved identifiers. Its selected-source adequacy is a separate obligation;
the empty-filter premise here must not stand in for that profile. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.CatalogueCoverage

open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL.Syntax
open ScalarSyntaxCore

def spec : Portable.SyntaxDescription := ⟨SourceViews.grammar, SourceViews.profile⟩

theorem plan_exact : SourceSyntaxExport.plan? spec = some SourceReader.plan := by
  unfold SourceSyntaxExport.plan?
  rw [show LanguageDefSyntaxCompiler.compileRules? (SourceSyntaxExport.binding spec.profile) spec.grammar =
      some SourceReader.rules from SourceReader.rules_compiled]
  exact SourceReader.plan_compiled

theorem start_exact : SourceReader.plan.lexical.startSort = "DlProgram" := SourceReader.agreement.startSort_eq

theorem source_program_returned {input : String} {forestBytes identityBytes : List UInt8}
    {packets : List SourcePacket.Packet} {forestRounds catalogueRounds : Nat}
    (forestComplete : SourceSyntaxForest.complete? spec input forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : SourceCatalogue.validate? spec [] input forestBytes identityBytes packets catalogueRounds = some true)
    (program : Program) (source : ReferenceReader.SourceProgram (input.toList.map Char.toNat) program) :
    ∃ packet ∈ packets, ∃ treePacket pattern,
      SourceCatalogue.packetTree? packet = some treePacket ∧
      SourcePacketCertificate.core? SourcePrinter.description PacketCoverage.parser SourcePrinter.description_shape
        (input.toList.map Char.toNat) "DlProgram" treePacket = some pattern ∧
      ((ProgramProjection.Reference.projectProgram? pattern).bind Frontend.normalize?).bind IRCodec.program? = some program := by
  obtain ⟨tree, pattern, ⟨derived⟩, lowered, projected⟩ := source
  obtain ⟨sourcePlan⟩ := LanguageDefScalarSyntax.preserve SourceReader.rules_compiled derived
  let target := preserveSourcePlanDerivation SourceReader.agreement sourcePlan
  have sourceMeaning : SourcePacketSelection.Source SourcePrinter.description PacketCoverage.parser []
      (input.toList.map Char.toNat) SourceReader.plan.lexical.startSort pattern :=
    ⟨tree, target, by intro family _; simp [SourcePacketSelection.allows],
      (SourcePrinter.shared_lower _ _).trans lowered⟩
  obtain ⟨packet, member, treePacket, packetRead, coreRead⟩ := SourceCatalogue.selected_source_returned
    PacketCoverage.parser SourcePrinter.description_shape forestComplete catalogueComplete sourceMeaning
  change SourcePacketSelection.core? _ _ _ [] _ SourceReader.plan.lexical.startSort _ = _ at coreRead
  rw [start_exact] at coreRead
  refine ⟨packet, member, treePacket, pattern, packetRead, ?_, projected⟩
  simpa only [SourcePacketSelection.core?, SourcePacketSelection.read?_nil, SourcePacketCertificate.core?] using coreRead

#print axioms source_program_returned

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.CatalogueCoverage
