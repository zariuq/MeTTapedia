import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourceReader
import Mettapedia.GSLT.Parsing.ClassAwareParserPackHeightPotential
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification

/-! A checked affine height bound for every derivation of the authored
Datalog parser plan. This makes an independent complete root catalogue
available for qualifying a native packed forest. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceReader

open Mettapedia.GSLT.Parsing
open ClassAwareParserPackHeightPotential ClassAwareParserPackEnumeration
open ClassAwareNativeForestQualification

def heightPotential : HeightPotential :=
  ⟨14,[
    ("DlAtom",-18),
    ("DlAttribute",-76),
    ("DlAttributes",2),
    ("DlBinaryDigitScalar",-13),
    ("DlBinaryDigits",-10),
    ("DlBlockCommentAfterStar",12),
    ("DlBlockCommentAfterStarScalar",-13),
    ("DlBlockCommentBody",21),
    ("DlBlockCommentScalar",-4),
    ("DlBody",9),
    ("DlComparison",-2),
    ("DlComparisonOperator",-11),
    ("DlConstant",-4),
    ("DlConstants",2),
    ("DlDeclaration",-10),
    ("DlDigitScalar",-13),
    ("DlDigits",-10),
    ("DlDirectiveSpace",-7),
    ("DlEscape",9),
    ("DlFact",-10),
    ("DlFloat",-29),
    ("DlGroundAtom",-21),
    ("DlHexDigitScalar",-13),
    ("DlHexDigits",-10),
    ("DlHorizontalSpaceScalar",-13),
    ("DlIdentifier",-10),
    ("DlIdentifierFirstScalar",-13),
    ("DlIdentifierNonempty",-10),
    ("DlIdentifierRestScalar",-13),
    ("DlInput",-10),
    ("DlInteger",-7),
    ("DlItem",-7),
    ("DlItems",2),
    ("DlLineCommentBody",2),
    ("DlLineCommentScalar",-4),
    ("DlOutput",-10),
    ("DlPositiveLiteral",3),
    ("DlPrimitiveType",-63),
    ("DlProgram",8),
    ("DlQualifiedName",-7),
    ("DlRelations",-7),
    ("DlRule",-10),
    ("DlSingleIdentifierScalar",-13),
    ("DlStringScalar",-4),
    ("DlSymbol",-21),
    ("DlSymbolBody",2),
    ("DlTerm",-1),
    ("DlTerms",5),
    ("DlTrivia",2),
    ("DlUnsigned",-20),
    ("DlWhitespaceScalar",-4)]⟩

theorem heightPotential_valid : heightPotential.ValidFor plan :=
  (heightPotential.validate_eq_true_iff plan).mp (by decide +kernel)

theorem root_height_bound (input : List Nat) :
    RootHeightBound SourceViews.profile plan input (heightPotential.rootFuel plan input) :=
  heightPotential.rootHeightBound heightPotential_valid input

theorem root_fuel (input : List Nat) : heightPotential.rootFuel plan input = 14 * input.length + 8 := by
  have coefficient : heightPotential.perCodepoint = 14 := rfl
  have potential : heightPotential.sortPotential plan.lexical.startSort = 8 := by decide +kernel
  simp only [HeightPotential.rootFuel, coefficient, potential]
  rfl

theorem root_height_bound_explicit (input : List Nat) :
    RootHeightBound SourceViews.profile plan input (14 * input.length + 8) := by
  rw [← root_fuel]
  exact root_height_bound input

def completeCatalogue (input : List Nat) : RootCertificateCatalogue SourceViews.profile plan input :=
  RootCertificateCatalogue.ofHeightBound (root_height_bound input)

theorem zero_progress_credit_refused :
    ({ heightPotential with perCodepoint := 0 } : HeightPotential).validate plan = false := by
  decide +kernel

theorem insufficient_root_potential_refused :
    ({ heightPotential with sortPotentials := ("DlProgram",0) :: heightPotential.sortPotentials } : HeightPotential).validate plan = false := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceReader
