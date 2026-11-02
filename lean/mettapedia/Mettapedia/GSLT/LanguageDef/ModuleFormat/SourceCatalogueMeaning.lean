import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSelectedMeaning

/-! A complete native catalogue returns every independently selected source
core through the checked reader. This join is uniform in grammar, lexical
profile, leaf representation and declared selection filters. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ScalarSyntaxCore

theorem selected_source_returned {description : Description} (parser : Parser description)
    (shape : Shape description) {filters : List SourceSyntax.FamilyFilter}
    {input : String} {forestBytes identityBytes : List UInt8} {packets : List SourcePacket.Packet}
    {forestRounds catalogueRounds : Nat} {core : Pattern}
    (forestComplete : SourceSyntaxForest.complete? ⟨description.grammar, description.profile⟩
      input forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : validate? ⟨description.grammar, description.profile⟩ filters
      input forestBytes identityBytes packets catalogueRounds = some true)
    (source : SourcePacketSelection.Source description parser filters
      (input.toList.map Char.toNat) parser.plan.lexical.startSort core) :
    ∃ packet ∈ packets, ∃ treePacket, packetTree? packet = some treePacket ∧
      SourcePacketSelection.core? description parser shape filters
        (input.toList.map Char.toNat) parser.plan.lexical.startSort treePacket = some core := by
  obtain ⟨plan, compiled, covers⟩ := checked_complete forestComplete catalogueComplete
  have planExact : SourceSyntaxExport.plan? ⟨description.grammar, description.profile⟩ = some parser.plan := by
    unfold SourceSyntaxExport.plan?
    rw [parser.rulesCompiled]
    exact parser.planCompiled
  have samePlan : plan = parser.plan := Option.some.inj (compiled.symm.trans planExact)
  subst plan
  obtain ⟨tree, derived, policy, lowered⟩ := source
  obtain ⟨packet, member, treePacket, packetRead, proposed⟩ := covers tree derived policy
  obtain ⟨reading, read, certificateSame, treeSame⟩ :=
    reading_of_replay parser shape (Replays.ofDerivation derived)
  have coreSame : reading.core = core :=
    Option.some.inj ((treeSame ▸ reading.construction).symm.trans lowered)
  refine ⟨packet, member, treePacket, packetRead, ?_⟩
  simp only [SourcePacketSelection.core?, SourcePacketSelection.read?, SourcePacketCertificate.readPacket?,
    proposed, Bind.bind, Option.bind, read, certificateSame,
    (SourcePacketSelection.selected_iff _ _ _).mpr policy, ↓reduceIte, Option.map_some, coreSame]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue
