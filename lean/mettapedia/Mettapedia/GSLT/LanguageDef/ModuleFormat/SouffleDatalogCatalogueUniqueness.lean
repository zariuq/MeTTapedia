import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogCatalogueCoverage

/-! The compiler's unique-result admission is justified against the original
source semantics once the forest and complete catalogue checks succeed.
No assumption of grammar-wide unambiguity is substituted for these checks. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.CatalogueCoverage

open Mettapedia.Languages.Datalog

theorem checked_unique_program {input : String} {forestBytes identityBytes : List UInt8}
    {packet : SourcePacket.Packet} {forestRounds catalogueRounds : Nat}
    (forestComplete : SourceSyntaxForest.complete? spec input forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : SourceCatalogue.validate? spec [] input forestBytes identityBytes [packet] catalogueRounds = some true)
    (first second : Program)
    (firstSource : ReferenceReader.SourceProgram (input.toList.map Char.toNat) first)
    (secondSource : ReferenceReader.SourceProgram (input.toList.map Char.toNat) second) : first = second := by
  obtain ⟨leftPacket, leftMember, leftTree, leftCore, leftPacketRead, leftRead, leftProgram⟩ :=
    source_program_returned forestComplete catalogueComplete first firstSource
  obtain ⟨rightPacket, rightMember, rightTree, rightCore, rightPacketRead, rightRead, rightProgram⟩ :=
    source_program_returned forestComplete catalogueComplete second secondSource
  have leftSame := List.mem_singleton.mp leftMember
  have rightSame := List.mem_singleton.mp rightMember
  subst leftPacket
  subst rightPacket
  have treeSame := Option.some.inj (leftPacketRead.symm.trans rightPacketRead)
  subst rightTree
  have coreSame := Option.some.inj (leftRead.symm.trans rightRead)
  subst rightCore
  exact Option.some.inj (leftProgram.symm.trans rightProgram)

theorem checked_empty_has_no_source {input : String} {forestBytes identityBytes : List UInt8}
    {forestRounds catalogueRounds : Nat}
    (forestComplete : SourceSyntaxForest.complete? spec input forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : SourceCatalogue.validate? spec [] input forestBytes identityBytes [] catalogueRounds = some true)
    (program : Program) : ¬ ReferenceReader.SourceProgram (input.toList.map Char.toNat) program := by
  intro source
  obtain ⟨packet, member, _⟩ := source_program_returned forestComplete catalogueComplete program source
  cases member

#print axioms checked_unique_program
#print axioms checked_empty_has_no_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.CatalogueCoverage
