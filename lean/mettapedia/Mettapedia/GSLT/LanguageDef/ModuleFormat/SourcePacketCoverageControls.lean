import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxPacketInverse
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxTextInverseControls

/-! Packet reconstruction distinguishes a source derivation from an
ambiguous row identity, a corrupt scalar, missing fuel and a changed child.
The positive roundtrip uses the general inverse theorem. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCoverage.Controls

open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ParserProfileSemantics
open SourcePacketEncoding SourcePacketCertificate SourceSyntaxIO ScalarSyntaxCore

def row : CompiledLexicalProduction := ⟨"Digit", "Word", .char 55, [0]⟩
def plan : CompiledParserPackPlan := {lexical := ⟨"Packet", "Word", [], [row]⟩, structural := []}

theorem unique_row_admitted : checkProfile plan = true := by decide_cbv
theorem duplicate_row_refused : checkProfile {plan with lexical := {plan.lexical with productions := [row,row]}} = false := by
  decide_cbv
theorem eof_lexical_refused :
    checkProfile {plan with lexical := {plan.lexical with productions := [{row with matcher := .eof}]}} = false := by
  decide_cbv

theorem scalar_reconstructed : propose? plan [55] "Word" (lexical "Digit" 55) =
    some (.lexical 0 (.char 55) 0 1) := by decide_cbv
theorem corrupt_scalar_refused : propose? plan [55] "Word" (lexical "Digit" 56) = none := by decide_cbv
theorem no_fuel_refused : proposeFuel plan [55] 0 "Word" 0 (lexical "Digit" 55) = none := by
  rw [proposeFuel]

def admitted : Admitted (description SourceSyntaxIO.Controls.spec) :=
  (admit? (description SourceSyntaxIO.Controls.spec)).get (by decide_cbv)

theorem admitted_exact : admit? (description SourceSyntaxIO.Controls.spec) = some admitted :=
  Option.eq_some_of_isSome _

theorem profile : Profile admitted.parser.plan := (checkProfile_exact _).mp (by decide_cbv)

theorem nested_print_has_packet :
    ∃ packet, read? SourceSyntaxIO.Controls.spec "(x,x)" packet =
      some (.apply "Pair" [.apply "First" [], .apply "Second" []]) :=
  printed_has_packet _ admitted admitted_exact profile _ _ (by decide_cbv)

theorem duplicate_children_retained :
    SourcePacket.children? (children [lexical "Digit" 55, lexical "Digit" 55]) =
      some [lexical "Digit" 55, lexical "Digit" 55] := children_read _

theorem changed_child_is_distinct :
    structural "Pair" [lexical "Digit" 55, lexical "Digit" 56] ≠
      structural "Pair" [lexical "Digit" 55, lexical "Digit" 55] := by decide_cbv

#print axioms nested_print_has_packet

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCoverage.Controls
