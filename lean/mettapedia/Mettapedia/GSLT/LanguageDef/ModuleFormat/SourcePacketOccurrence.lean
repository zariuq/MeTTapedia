import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCoverage

/-! Within the checked row profile, equal packets cannot conceal different
physical production certificates at a fixed input, sort and whole-input span.
Ambiguity with distinct constructors therefore survives packet transport. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketOccurrence

open Mettapedia.GSLT.Parsing
open ParserProfileSemantics PresentationExprSemantics ClassAwareParserPackCorrespondence
open ClassAwareParserPackCertificate SourcePacketEncoding

theorem certificate_injective {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (formed : Profile plan) {input : List Nat} {sort : String} {first second : CST}
    (left : ParserPackDerivesAt profile plan input sort 0 input.length first)
    (right : ParserPackDerivesAt profile plan input sort 0 input.length second)
    (same : encode first = encode second) : Certificate.ofDerivation left = Certificate.ofDerivation right := by
  have leftRead := SourcePacketCoverage.propose_complete formed left
  have rightRead := SourcePacketCoverage.propose_complete formed right
  rw [same, rightRead] at leftRead
  exact (Option.some.inj leftRead).symm

theorem tree_injective {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (formed : Profile plan) {input : List Nat} {sort : String} {first second : CST}
    (left : ParserPackDerivesAt profile plan input sort 0 input.length first)
    (right : ParserPackDerivesAt profile plan input sort 0 input.length second)
    (same : encode first = encode second) : first = second := by
  have certificateSame := certificate_injective formed left right same
  have replayed := Replays.ofDerivation left
  rw [certificateSame] at replayed
  exact ClassAwareParserPackOutput.output_unique replayed (Replays.ofDerivation right)

theorem distinct_certificates_stay_distinct {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (formed : Profile plan) {input : List Nat} {sort : String} {first second : CST}
    (left : ParserPackDerivesAt profile plan input sort 0 input.length first)
    (right : ParserPackDerivesAt profile plan input sort 0 input.length second)
    (distinct : Certificate.ofDerivation left ≠ Certificate.ofDerivation right) : encode first ≠ encode second :=
  fun same => distinct (certificate_injective formed left right same)

#print axioms certificate_injective
#print axioms tree_injective

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketOccurrence
