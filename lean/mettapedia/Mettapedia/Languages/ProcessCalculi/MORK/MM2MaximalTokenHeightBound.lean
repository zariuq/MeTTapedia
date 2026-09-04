import Mettapedia.GSLT.Parsing.ClassAwareParserPackHeightPotential
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSyntax

/-!
# Complete height bound for maximal-token MM2 parsing

The affine potential is checked against every generated lexical and
structural production.  It makes bounded reference enumeration exhaustive
for each finite scalar input while rejecting nullable recursive mutations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenHeightBound

open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
open Mettapedia.GSLT.Parsing.ClassAwareParserPackHeightPotential
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSyntax
open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-- One checked affine certificate for the maximal-token parser plan. -/
def heightPotential : HeightPotential := {
  perCodepoint := 1000
  sortPotentials := [
    ("MM2Program", 9),
    ("MM2ProgramAfterOpen", 2),
    ("MM2Atoms", 2),
    ("MM2AtomsAfterOpen", 2),
    ("MM2Expression", -1993),
    ("MM2ClosedAtom", -1990),
    ("MM2OpenAtom", -991),
    ("MM2LineComment", -100),
    ("MM2EOFComment", -994),
    ("MM2CommentTail", 2),
    ("MM2BareHead", -999),
    ("MM2BareTail", 2),
    ("MM2BareChar", -999),
    ("MM2Variable", -994),
    ("MM2VariableChars", 2),
    ("MM2VariableChar", -999),
    ("MM2QuotedSymbol", -1993),
    ("MM2QuotedChars", 2),
    ("MM2QuotedChar", -999),
    ("MM2EscapedChar", -999),
    ("MM2Whitespace", -999),
    ("MM2CommentChar", -999),
    ("MM2LineFeed", -999)]
}

theorem height_potential_validates :
    heightPotential.validate parserPackPlan = true := by
  decide +kernel

theorem height_potential_valid :
    heightPotential.ValidFor parserPackPlan :=
  (HeightPotential.validate_eq_true_iff _ _).mp
    height_potential_validates

theorem root_height_bound (input : List Nat) :
    RootHeightBound mm2ParserProfile parserPackPlan input
      (1000 * input.length + 9) := by
  have fuelExact :
      heightPotential.rootFuel parserPackPlan input =
        1000 * input.length + 9 := by
    rw [HeightPotential.rootFuel, parserPackAgreement.startSort_eq]
    rfl
  rw [← fuelExact]
  exact heightPotential.rootHeightBound height_potential_valid input

theorem root_enumeration_complete
    {input : List Nat} {tree :
      Mettapedia.GSLT.Parsing.PresentationExprSemantics.CST}
    (derivation : ParserPackRootDerives mm2ParserProfile
      parserPackPlan input tree) :
    ∃ row ∈ enumerateRootWithin (1000 * input.length + 9)
        mm2ParserProfile parserPackPlan input,
      row.tree = tree := by
  refine ⟨{
    certificate :=
      Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Certificate.ofDerivation
        derivation
    tree := tree }, ?_, rfl⟩
  exact ParserPackRootDerives.mem_enumerateRootWithin derivation
    (root_height_bound input tree derivation)

private def zeroWidthProgramCycle : CompiledStructuralProduction := {
  label := "mm2:invented-zero-width-program-cycle"
  resultSort := "MM2Program"
  items := [.nonterminal "MM2Program", .terminal .eof]
  childSlots := [0]
  source := {
    label := "mm2:invented-zero-width-program-cycle"
    category := "MM2Program"
    params := []
    syntaxPattern := []
  }
}

private def zeroWidthCycleMutation : CompiledParserPackPlan :=
  { parserPackPlan with
    structural := zeroWidthProgramCycle :: parserPackPlan.structural }

theorem zero_width_program_cycle_is_rejected :
    heightPotential.validate zeroWidthCycleMutation = false := by
  decide +kernel

#print axioms height_potential_valid
#print axioms root_height_bound
#print axioms root_enumeration_complete
#print axioms zero_width_program_cycle_is_rejected

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenHeightBound
