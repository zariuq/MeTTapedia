import Mettapedia.GSLT.LanguageDef.RFC8259SyntaxNTT
import Mettapedia.GSLT.Parsing.ParserPackSemanticGSLT

/-!
# RFC 8259 ParserPack compilation as a GSLT translation

This module instantiates the generic proof-relevant ParserPack compiler seam
on the complete RFC 8259 presentation.  Its public semantic endpoints are the
source parser GSLT and the compiled parser GSLT.  The concrete plan is only
implementation evidence used to construct the exact arrow between them.

Both native type theories are generated from those GSLT endpoints.  Thus the
parser pipeline composes semantic languages and their exact translations; a
host plan record never becomes an additional semantic intermediate language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RFC8259ParserPackGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.ProofRelevantJudgment
open Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileNTT
open Mettapedia.GSLT.LanguageDef.RFC8259SyntaxNTT
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ParserPackSemanticGSLT
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-! ## One semantic compiler arrow -/

/-- Compilation retains and reflects every fixed-input, fixed-tree receipt
fibre.  The concrete plan occurs only while constructing this witness. -/
def exactCompiler :=
  compilerExactTranslation rfc8259ParserPackAgreement

/-- The complete RFC 8259 compiler, sealed as one proof-relevant GSLT target
and one exact arrow from the scannerless source semantics. -/
def compilation :
    SemanticCompilation jsonTerminalScalars? rfc8259ParserProfile
      compiledSyntaxRules where
  target := parserPackSystem rfc8259ParserProfile rfc8259ParserPackPlan
  compiler := exactCompiler

/-- The scannerless RFC 8259 parsing judgment as the source GSLT. -/
abbrev sourceParserGSLT : GSLT :=
  sourceGSLT jsonTerminalScalars? rfc8259ParserProfile compiledSyntaxRules

/-- The compiled RFC 8259 ParserPack judgment as the target GSLT. -/
abbrev compiledParserGSLT : GSLT :=
  compilation.targetTheory

/-- Erasing only receipt identity gives the equation-class semantic compiler
arrow consumed by ordinary GSLT and OSLF constructions. -/
def semanticCompiler :
    SemanticCoveredTranslation sourceParserGSLT compiledParserGSLT :=
  compilation.semanticCompiler

/-- The source and compiled parser steps coincide for every input and CST. -/
theorem compiler_step_iff_for_rfc8259
    (source target :
      Term (sourceJudgment jsonTerminalScalars? rfc8259ParserProfile
        compiledSyntaxRules)) :
    sourceParserGSLT.Step source target <->
      compiledParserGSLT.Step
        (source.rebase
          (parserPackJudgment rfc8259ParserProfile rfc8259ParserPackPlan))
        (target.rebase
          (parserPackJudgment rfc8259ParserProfile rfc8259ParserPackPlan)) :=
  compiler_step_iff rfc8259ParserPackAgreement source target

/-! ## A complete JSON witness and its negative control -/

def nullInput : List Nat := [110, 117, 108, 108]

def nullTree : CST :=
  .node "json:text" 0 4
    [.node "json:ws-empty" 0 0 [],
     .node "json:value-null" 0 4 [],
     .node "json:ws-empty" 4 4 []]

/-- The independently defined source parser recognizes the complete JSON
document `null`, including both zero-width whitespace occurrences. -/
theorem source_recognizes_null :
    sourceParserGSLT.Step (.query nullInput) (.answer nullInput nullTree) := by
  rw [Judgment.query_step_answer_iff]
  simpa [sourceJudgment, nullInput, nullTree] using
    rfc8259_source_plan_null_is_preserved.1

/-- The semantic compiler arrow maps that source recognition to the compiled
ParserPack GSLT. -/
theorem compiler_maps_null :
    compiledParserGSLT.Step (.query nullInput) (.answer nullInput nullTree) := by
  have mapped :=
    (compiler_step_iff_for_rfc8259
      (.query nullInput) (.answer nullInput nullTree)).mp
      source_recognizes_null
  exact mapped

/-- Negative control: the compiled parser cannot invent this root judgment
when the source parser does not derive it. -/
theorem compiled_null_cannot_be_spurious :
    Not (compiledParserGSLT.Step (.query nullInput) (.answer nullInput nullTree) /\
      Not (sourceParserGSLT.Step (.query nullInput) (.answer nullInput nullTree))) := by
  rintro ⟨compiledStep, sourceMissing⟩
  apply sourceMissing
  exact (compiler_step_iff_for_rfc8259
    (.query nullInput) (.answer nullInput nullTree)).mpr compiledStep

/-! ## OSLF-generated native type readouts -/

/-- The source native type theory is generated from the source parser GSLT. -/
def sourceNTT :=
  compilation.sourceNTT

/-- The target native type theory is generated from the compiled parser GSLT. -/
def compiledNTT :=
  compilation.targetNTT

#print axioms compiler_step_iff_for_rfc8259
#print axioms source_recognizes_null
#print axioms compiler_maps_null
#print axioms compiled_null_cannot_be_spurious

end Mettapedia.GSLT.LanguageDef.RFC8259ParserPackGSLT
