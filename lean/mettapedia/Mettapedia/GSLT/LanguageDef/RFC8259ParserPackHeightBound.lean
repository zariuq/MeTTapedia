import Mettapedia.GSLT.LanguageDef.RFC8259SyntaxNTT
import Mettapedia.GSLT.Parsing.ClassAwareParserPackHeightPotential
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification

/-!
# A complete derivation-height bound for the RFC 8259 ParserPack plan

The potential below is checked against all eight lexical and forty-five
structural productions of the supplied compiled plan.  Its per-codepoint
budget pays for the recursive whitespace, string, digit, member, element,
object, and array structure.  The resulting bound makes the independent
ParserPack reference enumerator exhaustive for every RFC 8259 input.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RFC8259ParserPackHeightBound

open Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileNTT
open Mettapedia.GSLT.LanguageDef.RFC8259SyntaxNTT
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate
open Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
open Mettapedia.GSLT.Parsing.ClassAwareParserPackHeightPotential
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-- One presentation-specific witness for the generic affine height theorem.
Negative values are deliberate: a lexical child consumes one codepoint and
therefore leaves most of the per-codepoint budget available to its enclosing
recursive production. -/
def rfc8259HeightPotential : HeightPotential := {
  perCodepoint := 1000
  sortPotentials := [
    ("JsonText", 110),
    ("JsonWs", 2),
    ("JsonWsChar", -999),
    ("JsonValue", 100),
    ("JsonObject", -100),
    ("JsonMembersOpt", 2),
    ("JsonMembers", -900),
    ("JsonMember", -989),
    ("JsonMemberTail", 2),
    ("JsonArray", -100),
    ("JsonElementsOpt", 109),
    ("JsonElements", 106),
    ("JsonElementTail", 2),
    ("JsonString", -100),
    ("JsonStringChars", 2),
    ("JsonStringChar", -97),
    ("JsonUnescaped", -999),
    ("JsonEscape", -100),
    ("JsonSimpleEscape", -999),
    ("JsonHexDigit", -999),
    ("JsonNumber", -88),
    ("JsonMinusOpt", 2),
    ("JsonInt", -100),
    ("JsonDigits", 2),
    ("JsonDigit", -999),
    ("JsonDigit19", -999),
    ("JsonFracOpt", 2),
    ("JsonFrac", -100),
    ("JsonExpOpt", 2),
    ("JsonExp", -100),
    ("JsonExpMark", -999),
    ("JsonSignOpt", 2),
    ("JsonSign", -999)]
}

/-- The executable validator inspects every production of the actual compiled
RFC 8259 plan. -/
theorem rfc8259_height_potential_validates :
    rfc8259HeightPotential.validate rfc8259ParserPackPlan = true := by
  decide +kernel

theorem rfc8259_height_potential_valid :
    rfc8259HeightPotential.ValidFor rfc8259ParserPackPlan :=
  (HeightPotential.validate_eq_true_iff _ _).mp
    rfc8259_height_potential_validates

theorem rfc8259_root_height_bound (input : List Nat) :
    RootHeightBound rfc8259ParserProfile rfc8259ParserPackPlan input
      (1000 * input.length + 110) := by
  have fuelExact :
      rfc8259HeightPotential.rootFuel rfc8259ParserPackPlan input =
        1000 * input.length + 110 := by
    simp [HeightPotential.rootFuel, rfc8259HeightPotential,
      HeightPotential.sortPotential,
      rfc8259_parser_pack_start_sort_agrees, rfc8259ParserProfile]
  rw [← fuelExact]
  exact rfc8259HeightPotential.rootHeightBound
    rfc8259_height_potential_valid input

/-- The bound feeds the independent certificate/CST catalogue directly. -/
def rfc8259RootCatalogueRows (input : List Nat) :
    List (Certificate × CST) :=
  rootCatalogueRows (1000 * input.length + 110)
    rfc8259ParserProfile rfc8259ParserPackPlan input

theorem rfc8259_root_catalogue_replay
    {input : List Nat} {entry : Certificate × CST}
    (member : entry ∈ rfc8259RootCatalogueRows input) :
    Nonempty (Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Replays
      rfc8259ParserProfile rfc8259ParserPackPlan input entry.1
      rfc8259ParserPackPlan.lexical.startSort 0 input.length entry.2) := by
  change entry ∈ rootCatalogueRows (1000 * input.length + 110)
    rfc8259ParserProfile rfc8259ParserPackPlan input at member
  exact rootCatalogueRows_replay member

theorem rfc8259_root_catalogue_complete
    {input : List Nat} {tree : CST}
    (derivation : ParserPackRootDerives rfc8259ParserProfile
      rfc8259ParserPackPlan input tree) :
    (Certificate.ofDerivation derivation, tree) ∈
      rfc8259RootCatalogueRows input := by
  exact rootCatalogueRows_complete
    (rfc8259_root_height_bound input) tree derivation

/-- The reusable qualification boundary populated by the independent RFC
height theorem and reference enumerator. -/
def rfc8259RootCertificateCatalogue (input : List Nat) :
    RootCertificateCatalogue rfc8259ParserProfile
      rfc8259ParserPackPlan input :=
  RootCertificateCatalogue.ofHeightBound
    (rfc8259_root_height_bound input)

/-! ## Mutation control -/

private def zeroWidthCycleProduction : CompiledStructuralProduction := {
  label := "json:invented-zero-width-cycle"
  resultSort := "JsonText"
  items := [.nonterminal "JsonText"]
  childSlots := [0]
  source := {
    label := "json:invented-zero-width-cycle"
    category := "JsonText"
    params := []
    syntaxPattern := []
  }
}

private def zeroWidthCycleMutation : CompiledParserPackPlan :=
  { rfc8259ParserPackPlan with
    structural := zeroWidthCycleProduction ::
      rfc8259ParserPackPlan.structural }

/-- Adding an unproductive recursive source row invalidates the certificate;
the large numeric budget cannot hide the semantic mutation. -/
theorem zero_width_cycle_mutation_is_rejected :
    rfc8259HeightPotential.validate zeroWidthCycleMutation = false := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.RFC8259ParserPackHeightBound
