import Mettapedia.GSLT.Parsing.ClassAwareParserPackHeightPotential
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-!
# Complete derivation-height bound for the MM2 syntax ParserPack

The potential below is checked against every lexical and structural row of
the generated MM2 parser plan.  It turns the generic height-bounded reference
enumerator into an exhaustive catalogue for each finite scalar input.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxHeightBound

open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
open Mettapedia.GSLT.Parsing.ClassAwareParserPackHeightPotential
open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-- One source-sensitive affine certificate for the generated MM2 plan.
Negative lexical potentials are deliberate: every lexical row consumes one
scalar and leaves its enclosing recursive constructor most of that budget.
-/
def mm2SyntaxHeightPotential : HeightPotential := {
  perCodepoint := 1000
  sortPotentials := [
    ("MM2Program", 9),
    ("MM2Atom", -990),
    ("MM2Atoms", 2),
    ("MM2Expression", -1990),
    ("MM2Gap", 2),
    ("MM2GapUnit", -4),
    ("MM2FinalGap", 5),
    ("MM2LineComment", -100),
    ("MM2EOFComment", -994),
    ("MM2CommentTail", 2),
    ("MM2Symbol", -993),
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

/-- Executable validation inspects all eight lexical and twenty-nine
structural productions of the exact generated plan. -/
theorem mm2_syntax_height_potential_validates :
    mm2SyntaxHeightPotential.validate mm2ParserPackPlan = true := by
  decide +kernel

theorem mm2_syntax_height_potential_valid :
    mm2SyntaxHeightPotential.ValidFor mm2ParserPackPlan :=
  (HeightPotential.validate_eq_true_iff _ _).mp
    mm2_syntax_height_potential_validates

theorem mm2_root_height_bound (input : List Nat) :
    RootHeightBound mm2ParserProfile mm2ParserPackPlan input
      (1000 * input.length + 9) := by
  have fuelExact :
      mm2SyntaxHeightPotential.rootFuel mm2ParserPackPlan input =
        1000 * input.length + 9 := by
    rw [HeightPotential.rootFuel, mm2ParserPackAgreement.startSort_eq]
    rfl
  rw [← fuelExact]
  exact mm2SyntaxHeightPotential.rootHeightBound
    mm2_syntax_height_potential_valid input

/-- The bounded enumerator is complete at the certified MM2 fuel. -/
theorem mm2_root_enumeration_complete
    {input : List Nat} {tree :
      Mettapedia.GSLT.Parsing.PresentationExprSemantics.CST}
    (derivation : ParserPackRootDerives mm2ParserProfile
      mm2ParserPackPlan input tree) :
    ∃ row ∈ enumerateRootWithin (1000 * input.length + 9)
        mm2ParserProfile mm2ParserPackPlan input,
      row.tree = tree := by
  refine ⟨{
    certificate :=
      Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Certificate.ofDerivation
        derivation
    tree := tree }, ?_, rfl⟩
  exact ParserPackRootDerives.mem_enumerateRootWithin derivation
    (mm2_root_height_bound input tree derivation)

/-! ## Mutation control -/

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
  { mm2ParserPackPlan with
    structural := zeroWidthProgramCycle :: mm2ParserPackPlan.structural }

/-- A zero-width recursive start row cannot be hidden by the large numeric
budget. -/
theorem zero_width_program_cycle_is_rejected :
    mm2SyntaxHeightPotential.validate zeroWidthCycleMutation = false := by
  decide +kernel

#print axioms mm2_syntax_height_potential_valid
#print axioms mm2_root_height_bound
#print axioms mm2_root_enumeration_complete
#print axioms zero_width_program_cycle_is_rejected

end Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxHeightBound
