import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCLiteralResultSimulation

/-!
# Shared generated StructuredC prefix for checked and open results

Checked and open results share the same negative passage through the three
authored literal rows.  This module proves that passage against the generated
StructuredC decision tree for an arbitrary non-literal output.  It stops at
the checked-result decision, where the two semantic cases genuinely diverge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission
open Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCDispatcher
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOneStepSimulation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation

def prefixReceipt : Pattern :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation.receipt12

def undefinedReceipt : Pattern :=
  externalReceipt termIsUndefinedQuery prefixReceipt
def holeReceipt : Pattern := externalReceipt termIsHoleQuery undefinedReceipt
def atomReceipt : Pattern := externalReceipt termIsAtomQuery holeReceipt

def baseContinuation : Pattern :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation.baseContinuation
def holeRest : Pattern :=
  StructuredC.appendStatements (statements []) baseContinuation
def atomRest : Pattern :=
  StructuredC.appendStatements (statements []) holeRest
def checkedRest : Pattern :=
  StructuredC.appendStatements
    (statements [openResultDecision, returnSymbol noTransitionOutcome]) atomRest

def checkedEndpoint (data : ResultStateData) : Pattern :=
  run (consStatement checkedResultDecision checkedRest)
    data.environment11 atomReceipt

theorem output_lookup11 (data : ResultStateData) :
    lookup? data.environment11 (identifier "output") =
      some (abiValue (encodeTerm data.declaration.outputType)) := by
  simp [ResultStateData.environment11, ResultStateData.environment10,
    ResultStateData.outputValue, lookup?, bindName, environmentBind,
    identifier, node, token]

theorem undefined_decision_false_rewrite_exact
    (data : ResultStateData)
    (different : data.declaration.outputType ≠ undefinedType) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation.prefixEndpoint
          data) =
      [run (StructuredC.appendStatements generatedUndefinedResultFallback
          baseContinuation) data.environment11 undefinedReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (consStatement generatedUndefinedResultDecision baseContinuation)
        data.environment11 prefixReceipt) = _
  have evaluated :
      evaluate? coldHandler
          (call termIsUndefinedQuery [variableExpression "output"])
          data.environment11 prefixReceipt =
        some ⟨.value falseValue, data.environment11, undefinedReceipt⟩ := by
    simpa [LiteralPredicate.externalName, LiteralPredicate.term,
      undefinedReceipt, different] using
      literalResultPredicate_evaluation_exact .undefined
        data.declaration.outputType data.environment11 prefixReceipt
        (output_lookup11 data)
  have selected :
      selectBranch? falseValue undefinedResultBody
          generatedUndefinedResultFallback =
        some generatedUndefinedResultFallback := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedUndefinedResultDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsUndefinedQuery [variableExpression "output"])
      undefinedResultBody generatedUndefinedResultFallback baseContinuation
      data.environment11 prefixReceipt falseValue data.environment11
      undefinedReceipt generatedUndefinedResultFallback evaluated selected

theorem undefined_fallback_append_rewrite_exact (data : ResultStateData) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedUndefinedResultFallback
          baseContinuation) data.environment11 undefinedReceipt) =
      [run (consStatement generatedHoleResultDecision holeRest)
        data.environment11 undefinedReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement generatedHoleResultDecision (statements []))
        baseContinuation) data.environment11 undefinedReceipt) = _
  simpa [holeRest] using
    appendConsTransition_rewriteAt_exact coldRelations
      generatedHoleResultDecision (statements []) baseContinuation
      data.environment11 undefinedReceipt

theorem hole_decision_false_rewrite_exact
    (data : ResultStateData)
    (different : data.declaration.outputType ≠ holeType) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedHoleResultDecision holeRest)
          data.environment11 undefinedReceipt) =
      [run (StructuredC.appendStatements generatedHoleResultFallback holeRest)
        data.environment11 holeReceipt] := by
  have evaluated :
      evaluate? coldHandler
          (call termIsHoleQuery [variableExpression "output"])
          data.environment11 undefinedReceipt =
        some ⟨.value falseValue, data.environment11, holeReceipt⟩ := by
    simpa [LiteralPredicate.externalName, LiteralPredicate.term, holeReceipt,
      different] using
      literalResultPredicate_evaluation_exact .hole
        data.declaration.outputType data.environment11 undefinedReceipt
        (output_lookup11 data)
  have selected :
      selectBranch? falseValue holeResultBody generatedHoleResultFallback =
        some generatedHoleResultFallback := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedHoleResultDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsHoleQuery [variableExpression "output"])
      holeResultBody generatedHoleResultFallback holeRest data.environment11
      undefinedReceipt falseValue data.environment11 holeReceipt
      generatedHoleResultFallback evaluated selected

theorem hole_fallback_append_rewrite_exact (data : ResultStateData) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedHoleResultFallback
          holeRest) data.environment11 holeReceipt) =
      [run (consStatement generatedAtomResultDecision atomRest)
        data.environment11 holeReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement generatedAtomResultDecision (statements [])) holeRest)
        data.environment11 holeReceipt) = _
  simpa [atomRest] using
    appendConsTransition_rewriteAt_exact coldRelations
      generatedAtomResultDecision (statements []) holeRest
      data.environment11 holeReceipt

theorem atom_decision_false_rewrite_exact
    (data : ResultStateData)
    (different : data.declaration.outputType ≠ atomType) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedAtomResultDecision atomRest)
          data.environment11 holeReceipt) =
      [run (StructuredC.appendStatements generatedCheckedOpenResultFallback
          atomRest) data.environment11 atomReceipt] := by
  have evaluated :
      evaluate? coldHandler
          (call termIsAtomQuery [variableExpression "output"])
          data.environment11 holeReceipt =
        some ⟨.value falseValue, data.environment11, atomReceipt⟩ := by
    simpa [LiteralPredicate.externalName, LiteralPredicate.term, atomReceipt,
      different] using
      literalResultPredicate_evaluation_exact .atom
        data.declaration.outputType data.environment11 holeReceipt
        (output_lookup11 data)
  have selected :
      selectBranch? falseValue atomResultBody
          generatedCheckedOpenResultFallback =
        some generatedCheckedOpenResultFallback := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedAtomResultDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsAtomQuery [variableExpression "output"])
      atomResultBody generatedCheckedOpenResultFallback atomRest
      data.environment11 holeReceipt falseValue data.environment11 atomReceipt
      generatedCheckedOpenResultFallback evaluated selected

theorem checked_fallback_append_rewrite_exact (data : ResultStateData) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedCheckedOpenResultFallback
          atomRest) data.environment11 atomReceipt) =
      [checkedEndpoint data] := by
  rw [generatedCheckedOpenResultFallback_shape]
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement checkedResultDecision
          (statements [openResultDecision, returnSymbol noTransitionOutcome]))
        atomRest) data.environment11 atomReceipt) = _
  simpa [checkedEndpoint, checkedRest] using
    appendConsTransition_rewriteAt_exact coldRelations checkedResultDecision
      (statements [openResultDecision, returnSymbol noTransitionOutcome])
      atomRest data.environment11 atomReceipt

/-- Six target steps expose the checked-result decision after the common
twenty-four-step result prefix. -/
theorem normalize_prefix_exact
    (data : ResultStateData)
    (notUndefined : data.declaration.outputType ≠ undefinedType)
    (notHole : data.declaration.outputType ≠ holeType)
    (notAtom : data.declaration.outputType ≠ atomType)
    (fuel : Nat) :
    normalizeFirstAt (engineBasePremises coldRelations) StructuredC.language 1
        (fuel + 6)
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation.prefixEndpoint
          data) =
      normalizeFirstAt (engineBasePremises coldRelations) StructuredC.language
        1 fuel (checkedEndpoint data) := by
  simp only [normalizeFirstAt,
    undefined_decision_false_rewrite_exact data notUndefined]
  simp only [undefined_fallback_append_rewrite_exact data]
  simp only [hole_decision_false_rewrite_exact data notHole]
  simp only [hole_fallback_append_rewrite_exact data]
  simp only [atom_decision_false_rewrite_exact data notAtom]
  simp only [checked_fallback_append_rewrite_exact data]

#print axioms normalize_prefix_exact

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation
