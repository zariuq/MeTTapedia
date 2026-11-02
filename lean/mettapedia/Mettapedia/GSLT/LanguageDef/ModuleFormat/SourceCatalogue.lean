import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxForest
import Mettapedia.GSLT.Parsing.ClassAwareCatalogueValidation

/-! Native output catalogues are checked against the resolved packed forest.
The file-level caller separately requires whole-input forest completeness.
This check preserves certificate multiplicity and applies declared selection
before constructing combinations of child alternatives. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue

open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ClassAwareNativeForestWire ClassAwareNativeForestIdentityWire
open ClassAwareNativeForestFamilyWitness ClassAwareNativeForestFamilyCompleteness
open ClassAwareNativeForestQualification ClassAwarePackedForest
open ClassAwareNativeForestParserCompleteness

def packetTree? : SourcePacket.Packet → Option SourcePacket.Packet
  | .expression [.symbol "result", tree, .symbol "nil"] => some tree
  | _ => none

def certificates? (plan : CompiledParserPackPlan) (input : List Nat) (packets : List SourcePacket.Packet) :
    Option (List Certificate) :=
  packets.mapM fun packet => do
    let tree ← packetTree? packet
    SourcePacketCertificate.propose? plan input plan.lexical.startSort tree

def validate? (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter) (input : String)
    (forestBytes identityBytes : List UInt8) (packets : List SourcePacket.Packet) (rounds : Nat) : Option Bool := do
  let plan ← SourceSyntaxExport.plan? spec
  let snapshot ← ClassAwareNativeForestWire.decodeSnapshot? forestBytes
  let identity ← ClassAwareNativeForestIdentityWire.decodeSnapshot? identityBytes
  let view ← snapshot.completedView?
  if view.codepoints != input.toList.map Char.toNat then some false else do
    let inventory ← identity.resolveInventory? plan
    if !validateExactFamilyRepresentation view inventory spec.profile plan then some false else do
      let native ← certificates? plan view.codepoints packets
      let forest := decodedForestData view inventory spec.profile
      ClassAwareCatalogueValidation.validate? forest (SourcePacketSelection.allows filters view.codepoints)
        ⟨plan.lexical.startSort, 0, view.codepoints.length⟩ rounds native

theorem certificates?_member {plan : CompiledParserPackPlan} {input : List Nat}
    {packets : List SourcePacket.Packet} {certificates : List Certificate}
    (read : certificates? plan input packets = some certificates)
    {certificate : Certificate} (member : certificate ∈ certificates) :
    ∃ packet ∈ packets, ∃ tree, packetTree? packet = some tree ∧
      SourcePacketCertificate.propose? plan input plan.lexical.startSort tree = some certificate := by
  induction packets generalizing certificates with
  | nil => simp [certificates?] at read; subst certificates; cases member
  | cons first rest ih =>
    simp only [certificates?, List.mapM_cons] at read
    obtain ⟨head, headRead, restRead⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨tail, tailRead, result⟩ := Option.bind_eq_some_iff.mp restRead
    cases Option.some.inj result
    rcases List.mem_cons.mp member with same | later
    · subst certificate
      obtain ⟨tree, treeRead, proposed⟩ := Option.bind_eq_some_iff.mp headRead
      exact ⟨first, List.mem_cons_self, tree, treeRead, proposed⟩
    · obtain ⟨packet, present, tree, treeRead, proposed⟩ := ih tailRead later
      exact ⟨packet, List.mem_cons_of_mem _ present, tree, treeRead, proposed⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue
