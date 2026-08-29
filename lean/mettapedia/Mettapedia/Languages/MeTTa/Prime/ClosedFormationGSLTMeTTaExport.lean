import Mettapedia.Languages.MeTTa.Prime.ClosedFormationGSLT
import Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

/-!
# Export Prime closed formation GSLT

The emitted artifact is the ordinary generic-inference-checker image used by
compile-time specializers and independent RawProof replay.  It contains no
runtime search policy.
-/

namespace Mettapedia.Languages.MeTTa.Prime.ClosedFormationGSLTMeTTaExport

open Mettapedia.Languages.MeTTa.Prime.ClosedFormationGSLT
open Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

def finiteHornDefinition? : Option String :=
  Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender.renderDefinition?
    exportedDefinition

theorem finiteHornDefinition_renders :
    finiteHornDefinition?.isSome = true := by
  simp [finiteHornDefinition?, exportedDefinition,
    definition, renderDefinition?, operatorSignature,
    noDuplicateOperators, renderOperators?, renderOperator?, renderRules?,
    renderRule?, renderTerm?, renderTerms?, safeSymbol, safeVariable,
    safeToken, safeTokenCharacter, integerToken, isApplication,
    termType, termConstructor, formType, formDynamic, formAtom, formSymbol,
    formVariable, formExpression, formGrounded, formNumber, formBool,
    formString, formError, formComponentsOne, formComponentsCons, formArrow,
    notFormEmptyArrow, primitiveRule, form, formComponents, notForm, pType,
    pDynamic, pAtom, pSymbol, pVariable, pExpression, pGrounded, pNumber,
    pBool, pString, pError, pNil, pCons, pArrow, ruleId]

def renderNullaryMap (entry : SyntaxNullaryMap) : String :=
  s!"(GNullaryMap {quote entry.sourceHead} {quote entry.targetConstructor})"

def renderVariadicListMap (entry : SyntaxVariadicListMap) : String :=
  s!"(GVariadicListMap {quote entry.sourceHead} {entry.minimumArity} " ++
    s!"{quote entry.targetWrapper} {quote entry.targetCons} " ++
    s!"{quote entry.targetNil})"

def renderSyntaxBinding (binding : GroundStructuralBinding) : String :=
  s!"(GGroundStructuralBindingV1 {renderList renderNullaryMap binding.nullary} " ++
    s!"{renderVariadicListMap binding.variadic} " ++
    s!"{quote binding.positiveJudgment} {quote binding.negativeJudgment})"

def audit : String :=
  "; Generated from the admitted Prime closed-formation GSLT root.\n" ++
  "; Edit ClosedFormationGSLT.lean and regenerate this artifact.\n\n" ++
  "!(import! &self generic_inference_checker_v0)\n\n" ++
  s!"(= (prime-closed-formation-language) " ++
    s!"{renderDefinition exportedDefinition})\n" ++
  s!"(= (prime-closed-formation-binding) " ++
    s!"{renderSyntaxBinding syntaxBinding})\n" ++
  s!"(= (prime-closed-formation-goal) {renderPattern sampleFormGoal})\n" ++
  s!"(= (prime-closed-formation-proof) {renderRawProof sampleFormProof})\n" ++
  s!"(= (prime-closed-refute-goal) {renderPattern sampleRefuteGoal})\n" ++
  s!"(= (prime-closed-refute-proof) {renderRawProof sampleRefuteProof})\n\n" ++
  "!(assertEqual (gic-language-valid " ++
    "(prime-closed-formation-language)) True)\n" ++
  "!(assertEqual (gic-check (prime-closed-formation-language) " ++
    "(prime-closed-formation-goal) (prime-closed-formation-proof)) True)\n" ++
  "!(assertEqual (gic-check (prime-closed-formation-language) " ++
    "(prime-closed-refute-goal) (prime-closed-refute-proof)) True)\n" ++
  "!(PrimeClosedFormationGICSummary 14 3 15 2)\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [auditPath] =>
      IO.FS.writeFile auditPath audit
      IO.println s!"wrote {audit.toUTF8.size} bytes to {auditPath}"
      pure 0
  | [auditPath, definitionPath] =>
      match finiteHornDefinition? with
      | none =>
          IO.eprintln "Prime formation rule outside the finite-Horn source fragment"
          pure 1
      | some renderedDefinition => do
          IO.FS.writeFile auditPath audit
          IO.FS.writeFile definitionPath renderedDefinition
          IO.println s!"wrote {audit.toUTF8.size} bytes to {auditPath}"
          IO.println s!"wrote {renderedDefinition.toUTF8.size} bytes to {definitionPath}"
          pure 0
  | _ =>
      IO.eprintln "usage: <audit-output.metta> [<language-definition-output.metta>]"
      pure 2

end Mettapedia.Languages.MeTTa.Prime.ClosedFormationGSLTMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.Prime.ClosedFormationGSLTMeTTaExport.main arguments
