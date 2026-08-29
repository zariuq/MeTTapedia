import Mettapedia.Languages.MeTTa.HE.TypeSystemGSLT
import Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender

/-!
# Export the HE typing consistency core

This build-time exporter emits the authored finite-Horn source definition.
The native runtime does not import or interpret this file; qualification
tooling binds its digest and semantic scope to the direct C realization.
-/

namespace Mettapedia.Languages.MeTTa.HE.TypeSystemGSLTMeTTaExport

open Mettapedia.Languages.MeTTa.HE.TypeSystemGSLT
open Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender

def finiteHornDefinition? : Option String :=
  Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender.renderDefinition?
    coreDefinition

/-- A future rule that crosses the finite-Horn source boundary fails this
theorem and the exporter itself also refuses to write output. -/
theorem finiteHornDefinition_renders :
    finiteHornDefinition?.isSome = true := by
  simp [finiteHornDefinition?, coreDefinition, definition,
    renderDefinition?, operatorSignature, noDuplicateOperators,
    renderOperators?, renderOperator?, renderRules?, renderRule?, renderTerm?,
    renderTerms?, safeSymbol, safeVariable, safeToken, safeTokenCharacter,
    integerToken, isApplication, termType, termConstructor, factRule,
    unaryRule, typeNumber, typeString, typeBool, typeDynamic, typeAtom,
    typeList, typeArrow, nonDynamicNumber, nonDynamicString, nonDynamicBool,
    nonDynamicAtom, nonDynamicList, nonDynamicArrow, ordinaryNumber,
    ordinaryString, ordinaryBool, ordinaryList, ordinaryArrow,
    consistentExact, consistentDynamicLeft, consistentDynamicRight,
    consistentTopRight, isType, isNonDynamic, isOrdinaryRoot, consistent,
    tNumber, tString, tBool, tDynamic, tAtom, tList, tArrow, edgeExact,
    edgeDynamic, edgeTop, ruleId]

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      match finiteHornDefinition? with
      | none =>
          IO.eprintln "HE typing rule outside the finite-Horn source fragment"
          pure 1
      | some rendered => do
          IO.FS.writeFile outputPath rendered
          IO.println s!"wrote {rendered.toUTF8.size} bytes to {outputPath}"
          pure 0
  | _ =>
      IO.eprintln "usage: TypeSystemGSLTMeTTaExport <definition.metta>"
      pure 2

end Mettapedia.Languages.MeTTa.HE.TypeSystemGSLTMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.HE.TypeSystemGSLTMeTTaExport.run arguments
