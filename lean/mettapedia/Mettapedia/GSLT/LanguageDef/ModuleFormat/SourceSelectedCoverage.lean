import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection

/-! A selected source derivation survives packet transport with the same
certificate and core. Selection is stated independently over all families
of the original compiled derivation, not as success of the packet reader. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSelectedCoverage

open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate PresentationExprSemantics
open ClassAwarePackedForest ScalarSyntaxCore SourcePacketEncoding SourcePacketSelection

theorem derivation_read {description : Description} (parser : Parser description) (shape : Shape description)
    (formed : Profile parser.plan) (filters : List SourceSyntax.FamilyFilter)
    {input : List Nat} {sort : String} {tree : CST}
    (derivation : ParserPackDerivesAt description.profile parser.plan input sort 0 input.length tree)
    (policy : ∀ family ∈ certificateFamilies sort (Certificate.ofDerivation derivation),
      allows filters input family = true) :
    ∃ reading : Reading description parser shape input sort 0 input.length,
      SourcePacketSelection.read? description parser shape filters input sort (encode tree) = some reading ∧
      reading.certificate = Certificate.ofDerivation derivation ∧ reading.tree = tree := by
  obtain ⟨reading, read, same, treeSame⟩ := reading_of_replay parser shape (Replays.ofDerivation derivation)
  refine ⟨reading, ?_, same, treeSame⟩
  simp only [SourcePacketSelection.read?, SourcePacketCertificate.readPacket?,
    SourcePacketCoverage.propose_complete formed derivation, Bind.bind, Option.bind, read, same,
    (selected_iff _ _ _).mpr policy, ↓reduceIte]

#print axioms derivation_read

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSelectedCoverage
