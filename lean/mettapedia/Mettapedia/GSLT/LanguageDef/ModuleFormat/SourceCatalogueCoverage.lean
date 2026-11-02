import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue

/-! The two live checks compose: independent native-forest completeness
and selected-catalogue equality entail coverage of every selected whole-input
ParserPack derivation by a submitted native packet. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue

open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ClassAwareNativeForestParserCompleteness ClassAwarePackedForest PresentationExprSemantics

theorem checked_complete {spec : Portable.SyntaxDescription} {filters : List SourceSyntax.FamilyFilter}
    {input : String} {forestBytes identityBytes : List UInt8} {packets : List SourcePacket.Packet}
    {forestRounds catalogueRounds : Nat}
    (forestComplete : SourceSyntaxForest.complete? spec input forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : validate? spec filters input forestBytes identityBytes packets catalogueRounds = some true) :
    ∃ plan, SourceSyntaxExport.plan? spec = some plan ∧
      ∀ (tree : CST) (source : ParserPackRootDerives spec.profile plan (input.toList.map Char.toNat) tree),
        (∀ family ∈ certificateFamilies plan.lexical.startSort (Certificate.ofDerivation source),
          SourcePacketSelection.allows filters (input.toList.map Char.toNat) family = true) →
        ∃ packet ∈ packets, ∃ treePacket, packetTree? packet = some treePacket ∧
          SourcePacketCertificate.propose? plan (input.toList.map Char.toNat) plan.lexical.startSort treePacket =
            some (Certificate.ofDerivation source) := by
  obtain ⟨plan, snapshot, identity, view, inventory, compiled, forestRead, identityRead,
    viewed, scalars, resolved, inputs, qualified⟩ := SourceSyntaxForest.complete?_sound forestComplete
  unfold validate? at catalogueComplete
  simp only [compiled, forestRead, identityRead, viewed, Bind.bind, Option.bind] at catalogueComplete
  have scalarCheck : (view.codepoints != input.toList.map Char.toNat) = false := by simp [scalars]
  rw [scalarCheck] at catalogueComplete
  simp only [Bool.false_eq_true, ↓reduceIte, resolved] at catalogueComplete
  split at catalogueComplete
  · cases catalogueComplete
  · cases nativeRead : certificates? plan view.codepoints packets with
    | none => simp [nativeRead] at catalogueComplete
    | some native =>
      simp only [nativeRead] at catalogueComplete
      have complete := qualified.parserComplete
      rw [decodedForest_eq_data inputs.families] at complete
      rw [← scalars]
      refine ⟨plan, compiled, ?_⟩
      intro tree source selected
      have present : Certificate.ofDerivation source ∈ native :=
        ClassAwareCatalogueValidation.validate?_root_complete complete catalogueComplete source selected
      exact certificates?_member nativeRead present

#print axioms checked_complete

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue
