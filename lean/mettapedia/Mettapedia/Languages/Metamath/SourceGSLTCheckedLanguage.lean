import Mettapedia.GSLT.CheckedLanguage
import Mettapedia.Languages.Metamath.SourceGSLTCheckerAlignment

/-!
# Metamath as a checked language

This module is the only composition layer in the source-GSLT pipeline that
imports Metamath operational and declarative semantics.  The syntax root and
generic parser compiler remain independent of both.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTCheckedLanguage

open Mettapedia.GSLT
open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.SourceGSLTCheckerAlignment
open Mettapedia.Languages.Metamath.VerifiedCheckerSemantics

structure MetamathClaim where
  label : String
  formula : RuntimeFormula

def skeleton : CheckedLanguageSkeleton where
  Input := ByteArray
  SyntaxCertificate := CheckedParserOutput
  SemanticState := RuntimeDB
  Claim := MetamathClaim
  canonicalState := checkBytesDB
  Lowering := fun {bytes} output database =>
    TypedLoweringCertificate bytes output.source ∧
      database = checkBytesDB bytes
  CheckerAccepts := fun database claim =>
    RuntimeAccepts database claim.label claim.formula
  DeclarativeAccepts := fun bytes claim =>
    DeclarativeAccepts bytes claim.formula

def checkedLanguage : CheckedLanguage where
  toCheckedLanguageSkeleton := skeleton
  lowering_exact := fun output => ⟨output.typedLoweringExact, rfl⟩
  checker_adequate := by
    intro bytes output claim
    exact
      (implementationAccepts_iff_runtimeAccepts
        bytes claim.label claim.formula).symm.trans
        (output.implementationAcceptance_iff_specProvability
          claim.label claim.formula)

/-- Metamath's certificate-indexed equivalence theorem, obtained from the generic
checked-language composition rather than re-proved for this language. -/
theorem certificateAcceptance_iff_specProvability
    {bytes : ByteArray} (output : CheckedParserOutput bytes)
    (claim : MetamathClaim) :
    skeleton.CertificatePipelineAccepts output claim ↔
      DeclarativeAccepts bytes claim.formula := by
  let certificate : checkedLanguage.SyntaxCertificate bytes := output
  simpa [checkedLanguage, skeleton] using
    checkedLanguage.certificatePipelineAccepts_iff_declarative
      certificate claim

/-- Positive composition theorem: a checked parser certificate plus
declarative provability yields whole-pipeline acceptance. -/
theorem pipelineAcceptance_iff_parserAndSpec
    (bytes : ByteArray) (claim : MetamathClaim) :
    skeleton.PipelineAccepts bytes claim ↔
      skeleton.ParserAccepts bytes ∧
        DeclarativeAccepts bytes claim.formula := by
  simpa [checkedLanguage, skeleton] using
    checkedLanguage.pipelineAccepts_iff_parserAccepts_and_declarative
      bytes claim

/-- Negative state example: a database distinct from the verified reader's
result cannot satisfy the Metamath lowering relation. -/
theorem wrongDatabase_not_lowered
    {bytes : ByteArray} (output : CheckedParserOutput bytes)
    (database : RuntimeDB) (different : database ≠ checkBytesDB bytes) :
    ¬ skeleton.Lowering output database := by
  intro lowered
  exact different lowered.2

end Mettapedia.Languages.Metamath.SourceGSLTCheckedLanguage
