import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueMeaning
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueCertifiedVerification

/-! The checks that admit execution compose. Certified whole-input coverage
of the native forest and the selected-catalogue check entail that every
selected whole-input interpretation of the input is returned by a submitted
packet. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ClassAwareNativeForestParserCompleteness ClassAwarePackedForest PresentationExprSemantics
open ScalarSyntaxCore

/-- Certified forest coverage and an accepted catalogue check cover every
selected root derivation by a submitted packet. -/
theorem certified_complete {spec : Portable.SyntaxDescription} {filters : List SourceSyntax.FamilyFilter}
    {input : String} {forestBytes identityBytes : List UInt8} {packets : List SourcePacket.Packet}
    {forestRounds catalogueRounds : Nat}
    (forestComplete :
      SourceCatalogueCertifiedVerification.complete? spec input forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : validate? spec filters input forestBytes identityBytes packets catalogueRounds = some true) :
    ∃ plan, SourceSyntaxExport.plan? spec = some plan ∧
      ∀ (tree : CST) (source : ParserPackRootDerives spec.profile plan (input.toList.map Char.toNat) tree),
        (∀ family ∈ certificateFamilies plan.lexical.startSort (Certificate.ofDerivation source),
          SourcePacketSelection.allows filters (input.toList.map Char.toNat) family = true) →
        ∃ packet ∈ packets, ∃ treePacket, packetTree? packet = some treePacket ∧
          SourcePacketCertificate.propose? plan (input.toList.map Char.toNat) plan.lexical.startSort treePacket =
            some (Certificate.ofDerivation source) := by
  obtain ⟨plan, snapshot, identity, view, inventory, compiled, forestRead, identityRead,
    viewed, scalars, resolved, inputs, qualified⟩ :=
    SourceCatalogueCertifiedVerification.complete?_sound forestComplete
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

/-- **Execution admission returns every selected interpretation.** When the
certified verifier accepts an input, its native forest and its selected
catalogue, every selected whole-input interpretation of the input is the
selected core of a submitted packet. -/
theorem verified_source_returned {description : Description} (parser : Parser description)
    (shape : Shape description) {filters : List SourceSyntax.FamilyFilter}
    {input : String} {forestBytes identityBytes : List UInt8} {packets : List SourcePacket.Packet}
    {rounds : Nat} {core : Pattern}
    (verified : SourceCatalogueCertifiedVerification.verify? ⟨description.grammar, description.profile⟩ filters
      input forestBytes identityBytes packets rounds = some true)
    (source : SourcePacketSelection.Source description parser filters
      (input.toList.map Char.toNat) parser.plan.lexical.startSort core) :
    ∃ packet ∈ packets, ∃ treePacket, packetTree? packet = some treePacket ∧
      SourcePacketSelection.core? description parser shape filters
        (input.toList.map Char.toNat) parser.plan.lexical.startSort treePacket = some core := by
  obtain ⟨forestComplete, catalogueComplete⟩ :=
    SourceCatalogueCertifiedVerification.verify?_sound _ _ _ _ _ _ _ verified
  obtain ⟨plan, compiled, covers⟩ := certified_complete forestComplete catalogueComplete
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

#print axioms certified_complete
#print axioms verified_source_returned

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue
