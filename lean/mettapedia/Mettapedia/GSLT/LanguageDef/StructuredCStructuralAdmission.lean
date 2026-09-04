import Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
import Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission

/-!
# Structural-runtime admission into the authored StructuredC GSLT

The structural runtime computes the four relations queried by StructuredC.
This module turns successful structural computations into exact one-step
theorems for the actual `StructuredC.language` rewrite system.  It introduces
no second statement semantics: every conclusion is an exact `rewriteAt`
result obtained from the authored transition rules.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission

/-- A successful structural effect evaluation admits exactly the authored
effect-value transition. -/
theorem effect_rewriteAt_exact_of_evaluate
    (handler : ExternalHandler)
    (expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern)
    (evaluated :
      evaluate? handler expression environment receipt =
        some ⟨.value value, evaluatedEnvironment, evaluatedReceipt⟩) :
    rewriteAt (engineBasePremises (relationEnv handler))
        StructuredC.language 1
        (run (consStatement (a "structured-c:effect" [expression]) rest)
          environment receipt) =
      [run rest evaluatedEnvironment evaluatedReceipt] := by
  apply effectValueTransition_rewriteAt_exact_of_tuples
  intro result outputEnvironment outputReceipt
  rw [relationEnv_evaluate_tuples, evaluated]

/-- A successful structural return evaluation admits exactly the authored
return-value transition. -/
theorem return_rewriteAt_exact_of_evaluate
    (handler : ExternalHandler)
    (expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern)
    (evaluated :
      evaluate? handler expression environment receipt =
        some ⟨.value value, evaluatedEnvironment, evaluatedReceipt⟩) :
    rewriteAt (engineBasePremises (relationEnv handler))
        StructuredC.language 1
        (run (consStatement (a "structured-c:return" [expression]) rest)
          environment receipt) =
      [halted (a "structured-c:outcome-return" [value])
        evaluatedEnvironment evaluatedReceipt] := by
  apply returnValueTransition_rewriteAt_exact_of_tuples
  intro result outputEnvironment outputReceipt
  rw [relationEnv_evaluate_tuples, evaluated]

/-- Structural evaluation and persistent storage admit exactly the authored
declaration transition. -/
theorem declare_rewriteAt_exact_of_evaluate
    (handler : ExternalHandler)
    (variableName type expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt nextEnvironment : Pattern)
    (evaluated :
      evaluate? handler expression environment receipt =
        some ⟨.value value, evaluatedEnvironment, evaluatedReceipt⟩)
    (stored :
      store? evaluatedEnvironment variableName value = some nextEnvironment) :
    rewriteAt (engineBasePremises (relationEnv handler))
        StructuredC.language 1
        (run (consStatement
          (a "structured-c:declare" [variableName, type, expression]) rest)
          environment receipt) =
      [run rest nextEnvironment evaluatedReceipt] := by
  apply declareValueTransition_rewriteAt_exact_of_tuples
  · intro result outputEnvironment outputReceipt
    rw [relationEnv_evaluate_tuples, evaluated]
  · intro output
    rw [relationEnv_store_tuples, stored]

/-- Structural condition evaluation and Boolean selection admit exactly the
authored conditional transition. -/
theorem if_rewriteAt_exact_of_evaluate
    (handler : ExternalHandler)
    (condition thenBranch elseBranch rest environment receipt value
      evaluatedEnvironment evaluatedReceipt selected : Pattern)
    (evaluated :
      evaluate? handler condition environment receipt =
        some ⟨.value value, evaluatedEnvironment, evaluatedReceipt⟩)
    (selectedExact :
      selectBranch? value thenBranch elseBranch = some selected) :
    rewriteAt (engineBasePremises (relationEnv handler))
        StructuredC.language 1
        (run (consStatement
          (a "structured-c:if" [condition, thenBranch, elseBranch]) rest)
          environment receipt) =
      [run (appendStatements selected rest)
        evaluatedEnvironment evaluatedReceipt] := by
  apply ifValueTransition_rewriteAt_exact_of_tuples
  · intro result outputEnvironment outputReceipt
    rw [relationEnv_evaluate_tuples, evaluated]
  · intro output
    rw [relationEnv_branch_tuples, selectedExact]

/-- Structural scrutinee evaluation and first-match case selection admit
exactly the authored switch transition. -/
theorem switch_rewriteAt_exact_of_evaluate
    (handler : ExternalHandler)
    (scrutinee cases defaultBranch rest environment receipt value
      evaluatedEnvironment evaluatedReceipt selected : Pattern)
    (evaluated :
      evaluate? handler scrutinee environment receipt =
        some ⟨.value value, evaluatedEnvironment, evaluatedReceipt⟩)
    (selectedExact :
      selectCase? value defaultBranch cases = some selected) :
    rewriteAt (engineBasePremises (relationEnv handler))
        StructuredC.language 1
        (run (consStatement
          (a "structured-c:switch" [scrutinee, cases, defaultBranch]) rest)
          environment receipt) =
      [run (appendStatements selected rest)
        evaluatedEnvironment evaluatedReceipt] := by
  apply switchValueTransition_rewriteAt_exact_of_tuples
  · intro result outputEnvironment outputReceipt
    rw [relationEnv_evaluate_tuples, evaluated]
  · intro output
    rw [relationEnv_case_tuples, selectedExact]

#print axioms effect_rewriteAt_exact_of_evaluate
#print axioms return_rewriteAt_exact_of_evaluate
#print axioms declare_rewriteAt_exact_of_evaluate
#print axioms if_rewriteAt_exact_of_evaluate
#print axioms switch_rewriteAt_exact_of_evaluate

end Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
