import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSelectedCoverage

/-! Independent selected-source meaning and its packet transport. The
relation refers to grammar derivations, declared family policies and the
source fold; neither native enumeration nor reader success defines it. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate PresentationExprSemantics
open ClassAwarePackedForest
open ScalarSyntaxCore

def Source (description : Description) (parser : Parser description)
    (filters : List SourceSyntax.FamilyFilter) (input : List Nat) (sort : String) (core : Pattern) : Prop :=
  ∃ (tree : CST) (derivation : ParserPackDerivesAt description.profile parser.plan input sort 0 input.length tree),
    (∀ family ∈ certificateFamilies sort (Certificate.ofDerivation derivation), allows filters input family = true) ∧
    lowerCST? description sort tree = some core

def core? (description : Description) (parser : Parser description) (shape : Shape description)
    (filters : List SourceSyntax.FamilyFilter) (input : List Nat) (sort : String)
    (packet : SourcePacket.Packet) : Option Pattern :=
  (read? description parser shape filters input sort packet).map (·.core)

theorem core?_sound {description : Description} {parser : Parser description} {shape : Shape description}
    {filters : List SourceSyntax.FamilyFilter} {input : List Nat} {sort : String}
    {packet : SourcePacket.Packet} {core : Pattern}
    (accepted : core? description parser shape filters input sort packet = some core) :
    Source description parser filters input sort core := by
  obtain ⟨reading, read, same⟩ := Option.map_eq_some_iff.mp accepted
  obtain ⟨_, policy⟩ := read?_selected read
  refine ⟨reading.tree, reading.replayed.derivation, ?_, same ▸ reading.construction⟩
  simpa only [Replays.certificate_derivation] using policy

theorem core?_prints {description : Description} {parser : Parser description} {shape : Shape description}
    {filters : List SourceSyntax.FamilyFilter} {input : List Nat} {sort : String}
    {packet : SourcePacket.Packet} {core : Pattern}
    (accepted : core? description parser shape filters input sort packet = some core) :
    printScalars? description sort core = some input := by
  obtain ⟨reading, _, same⟩ := Option.map_eq_some_iff.mp accepted
  exact same ▸ reading.full_source

theorem source_has_packet {description : Description} (parser : Parser description) (shape : Shape description)
    (formed : SourcePacketEncoding.Profile parser.plan) {filters : List SourceSyntax.FamilyFilter}
    {input : List Nat} {sort : String} {core : Pattern}
    (source : Source description parser filters input sort core) :
    ∃ packet, core? description parser shape filters input sort packet = some core := by
  obtain ⟨tree, derivation, policy, lowered⟩ := source
  obtain ⟨reading, read, _, treeSame⟩ := SourceSelectedCoverage.derivation_read parser shape formed filters derivation policy
  have coreSame : reading.core = core := by
    have built := reading.construction
    rw [treeSame, lowered] at built
    exact (Option.some.inj built).symm
  exact ⟨SourcePacketEncoding.encode tree, by simp only [core?, read, Option.map_some, coreSame]⟩

theorem source_iff_packet {description : Description} (parser : Parser description) (shape : Shape description)
    (formed : SourcePacketEncoding.Profile parser.plan) (filters : List SourceSyntax.FamilyFilter)
    (input : List Nat) (sort : String) (core : Pattern) :
    Source description parser filters input sort core ↔
      ∃ packet, core? description parser shape filters input sort packet = some core :=
  ⟨source_has_packet parser shape formed, fun ⟨_, read⟩ => core?_sound read⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection
