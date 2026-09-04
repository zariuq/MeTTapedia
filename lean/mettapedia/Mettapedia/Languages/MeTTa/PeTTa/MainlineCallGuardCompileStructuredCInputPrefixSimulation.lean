import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCArgumentsFinishedSimulation

/-!
# Shared generated StructuredC prefix for nonempty argument states

The five nonempty-input source families share exactly one operational prefix:
phase selection, eleven field projections, a false empty-cursor branch, and
two cursor projections.  This module proves that prefix once while retaining
the exact source state, environments, receipts, and target statements.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation

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

structure InputStateData where
  owner : SpaceOwner
  revision : Nat
  head : String
  arity : Nat
  declaration : ArrowDeclaration
  remaining : List ArrowDeclaration
  expected : Term
  inputCursor : List Term
  modes : List ArgMode
  accepted : List GuardPlan
deriving Repr

namespace InputStateData

def source (data : InputStateData) : CompileLanguageControl :=
  .arguments data.owner data.revision data.head data.arity data.declaration
    data.remaining (data.expected :: data.inputCursor) data.modes data.accepted

def ownerValue (data : InputStateData) : Pattern :=
  abiValue (encodeOwner data.owner)
def revisionValue (data : InputStateData) : Pattern :=
  abiValue (encodeNat data.revision)
def headValue (data : InputStateData) : Pattern := abiValue (encodeName data.head)
def arityValue (data : InputStateData) : Pattern := abiValue (encodeNat data.arity)
def acceptedValue (data : InputStateData) : Pattern :=
  abiValue (encodePlans data.accepted)
def remainingValue (data : InputStateData) : Pattern :=
  abiValue (encodeDeclarations data.remaining)
def occurrenceValue (data : InputStateData) : Pattern :=
  abiValue (encodeNat data.declaration.occurrence)
def declarationHeadValue (data : InputStateData) : Pattern :=
  abiValue (encodeName data.declaration.function)
def inputsValue (data : InputStateData) : Pattern :=
  abiValue (encodeTerms data.declaration.inputTypes)
def outputValue (data : InputStateData) : Pattern :=
  abiValue (encodeTerm data.declaration.outputType)
def modesValue (data : InputStateData) : Pattern :=
  abiValue (encodeArgModes data.modes)
def expectedValue (data : InputStateData) : Pattern :=
  abiValue (encodeTerm data.expected)
def inputCursorValue (data : InputStateData) : Pattern :=
  abiValue (encodeTerms data.inputCursor)

def environment0 (data : InputStateData) : Pattern :=
  initialEnvironment data.source
def environment1 (data : InputStateData) : Pattern :=
  bindName "owner" data.ownerValue data.environment0
def environment2 (data : InputStateData) : Pattern :=
  bindName "revision" data.revisionValue data.environment1
def environment3 (data : InputStateData) : Pattern :=
  bindName "head" data.headValue data.environment2
def environment4 (data : InputStateData) : Pattern :=
  bindName "arity" data.arityValue data.environment3
def environment5 (data : InputStateData) : Pattern :=
  bindName "accepted" data.acceptedValue data.environment4
def environment6 (data : InputStateData) : Pattern :=
  bindName "remaining" data.remainingValue data.environment5
def environment7 (data : InputStateData) : Pattern :=
  bindName "occurrence" data.occurrenceValue data.environment6
def environment8 (data : InputStateData) : Pattern :=
  bindName "declaration_head" data.declarationHeadValue data.environment7
def environment9 (data : InputStateData) : Pattern :=
  bindName "inputs" data.inputsValue data.environment8
def environment10 (data : InputStateData) : Pattern :=
  bindName "output" data.outputValue data.environment9
def environment11 (data : InputStateData) : Pattern :=
  bindName "modes" data.modesValue data.environment10
def environment12 (data : InputStateData) : Pattern :=
  bindName "expected" data.expectedValue data.environment11
def environment13 (data : InputStateData) : Pattern :=
  bindName "input_cursor" data.inputCursorValue data.environment12

end InputStateData

def receipt0 : Pattern := readyReceipt
def receipt1 : Pattern := externalReceipt compilePhaseQuery receipt0
def receipt2 : Pattern := externalReceipt ownerProjection receipt1
def receipt3 : Pattern := externalReceipt revisionProjection receipt2
def receipt4 : Pattern := externalReceipt headProjection receipt3
def receipt5 : Pattern := externalReceipt arityProjection receipt4
def receipt6 : Pattern := externalReceipt acceptedProjection receipt5
def receipt7 : Pattern := externalReceipt remainingProjection receipt6
def receipt8 : Pattern := externalReceipt occurrenceProjection receipt7
def receipt9 : Pattern := externalReceipt declarationHeadProjection receipt8
def receipt10 : Pattern := externalReceipt inputsProjection receipt9
def receipt11 : Pattern := externalReceipt outputProjection receipt10
def receipt12 : Pattern := externalReceipt modesProjection receipt11
def receipt13 : Pattern := externalReceipt inputCursorIsEmptyQuery receipt12
def receipt14 : Pattern := externalReceipt inputHeadProjection receipt13
def receipt15 : Pattern := externalReceipt inputTailProjection receipt14

def ownerStatement : Pattern :=
  bindProjection "owner" "CettaPeTTaCallGuardOwnerV1" ownerProjection
def revisionStatement : Pattern :=
  bindProjection "revision" "CettaPeTTaCallGuardNatV1" revisionProjection
def headStatement : Pattern :=
  bindProjection "head" "CettaPeTTaCallGuardNameV1" headProjection
def arityStatement : Pattern :=
  bindProjection "arity" "CettaPeTTaCallGuardNatV1" arityProjection
def acceptedStatement : Pattern :=
  bindProjection "accepted" "CettaPeTTaCallGuardPlansV1" acceptedProjection
def remainingStatement : Pattern :=
  bindProjection "remaining" "CettaPeTTaCallGuardDeclarationsV1"
    remainingProjection
def occurrenceStatement : Pattern :=
  bindProjection "occurrence" "CettaPeTTaCallGuardNatV1" occurrenceProjection
def declarationHeadStatement : Pattern :=
  bindProjection "declaration_head" "CettaPeTTaCallGuardNameV1"
    declarationHeadProjection
def inputsStatement : Pattern :=
  bindProjection "inputs" "CettaPeTTaCallGuardTermsV1" inputsProjection
def outputStatement : Pattern :=
  bindProjection "output" "CettaPeTTaCallGuardTermV1" outputProjection
def modesStatement : Pattern :=
  bindProjection "modes" "CettaPeTTaCallGuardArgModesV1" modesProjection

def tail1 : Pattern := statements [revisionStatement, headStatement,
  arityStatement, acceptedStatement, remainingStatement, occurrenceStatement,
  declarationHeadStatement, inputsStatement, outputStatement, modesStatement,
  generatedArgumentsDecision]
def tail2 : Pattern := statements [headStatement, arityStatement,
  acceptedStatement, remainingStatement, occurrenceStatement,
  declarationHeadStatement, inputsStatement, outputStatement, modesStatement,
  generatedArgumentsDecision]
def tail3 : Pattern := statements [arityStatement, acceptedStatement,
  remainingStatement, occurrenceStatement, declarationHeadStatement,
  inputsStatement, outputStatement, modesStatement,
  generatedArgumentsDecision]
def tail4 : Pattern := statements [acceptedStatement, remainingStatement,
  occurrenceStatement, declarationHeadStatement, inputsStatement,
  outputStatement, modesStatement, generatedArgumentsDecision]
def tail5 : Pattern := statements [remainingStatement, occurrenceStatement,
  declarationHeadStatement, inputsStatement, outputStatement, modesStatement,
  generatedArgumentsDecision]
def tail6 : Pattern := statements [occurrenceStatement,
  declarationHeadStatement, inputsStatement, outputStatement, modesStatement,
  generatedArgumentsDecision]
def tail7 : Pattern := statements [declarationHeadStatement, inputsStatement,
  outputStatement, modesStatement, generatedArgumentsDecision]
def tail8 : Pattern := statements [inputsStatement, outputStatement,
  modesStatement, generatedArgumentsDecision]
def tail9 : Pattern := statements [outputStatement, modesStatement,
  generatedArgumentsDecision]
def tail10 : Pattern := statements [modesStatement, generatedArgumentsDecision]
def tail11 : Pattern := statements [generatedArgumentsDecision]

def expectedStatement : Pattern :=
  bindProjection "expected" "CettaPeTTaCallGuardTermV1" inputHeadProjection
def inputCursorStatement : Pattern :=
  bindProjection "input_cursor" "CettaPeTTaCallGuardTermsV1"
    inputTailProjection
def nonemptyTail1 : Pattern :=
  consStatement inputCursorStatement generatedLiteralInputDispatcher
def nonemptyTail2 : Pattern := generatedLiteralInputDispatcher

theorem phase_selection_exact (data : InputStateData) :
    selectCase? (phaseValue data.source) generatedFaultBody
        generatedPhaseCases = some generatedArgumentsDispatcher := by
  rfl

theorem phase_rewrite_exact (data : InputStateData) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          data.source) =
      [run (StructuredC.appendStatements generatedArgumentsDispatcher
          (statements [])) data.environment0 receipt1] := by
  simpa [coldRelations, InputStateData.source, InputStateData.environment0,
    receipt1, receipt0,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl]
    using phase_switch_rewrite_exact data.source generatedArgumentsDispatcher
      data.environment0 receipt0
      (by
        simp [InputStateData.environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])
      (phase_selection_exact data)

theorem dispatcher_append_rewrite_exact (data : InputStateData) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedArgumentsDispatcher
          (statements [])) data.environment0 receipt1) =
      [run (consStatement ownerStatement
          (StructuredC.appendStatements tail1 (statements [])))
        data.environment0 receipt1] := by
  rw [generatedArgumentsDispatcher_shape]
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement ownerStatement tail1) (statements []))
        data.environment0 receipt1) = _
  exact appendConsTransition_rewriteAt_exact coldRelations ownerStatement tail1
    (statements []) data.environment0 receipt1

theorem owner_declare_rewrite_exact (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement ownerStatement rest) data.environment0 receipt1) =
      [run rest data.environment1 receipt2] := by
  simpa [coldRelations, CommonProjection.externalName, ownerStatement,
    bindProjection, stateArgument, InputStateData.environment1,
    InputStateData.ownerValue, receipt2, InputStateData.source]
    using common_projection_declare_rewrite_exact .owner "owner"
      "CettaPeTTaCallGuardOwnerV1" data.source data.ownerValue rest
      data.environment0 receipt1 (by rfl)
      (by
        simp [InputStateData.environment0, initialEnvironment, lookup?,
          bindName, environmentBind, identifier, node, token])

theorem revision_declare_rewrite_exact
    (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement revisionStatement rest)
          data.environment1 receipt2) =
      [run rest data.environment2 receipt3] := by
  simpa [coldRelations, CommonProjection.externalName, revisionStatement,
    bindProjection, stateArgument, InputStateData.environment2,
    InputStateData.revisionValue, receipt3, InputStateData.source]
    using common_projection_declare_rewrite_exact .revision "revision"
      "CettaPeTTaCallGuardNatV1" data.source data.revisionValue rest
      data.environment1 receipt2 (by rfl)
      (by
        simp [InputStateData.environment1, InputStateData.environment0,
          initialEnvironment, lookup?, bindName, environmentBind, identifier,
          node, token])

theorem head_declare_rewrite_exact (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement headStatement rest) data.environment2 receipt3) =
      [run rest data.environment3 receipt4] := by
  simpa [coldRelations, CommonProjection.externalName, headStatement,
    bindProjection, stateArgument, InputStateData.environment3,
    InputStateData.headValue, receipt4, InputStateData.source]
    using common_projection_declare_rewrite_exact .head "head"
      "CettaPeTTaCallGuardNameV1" data.source data.headValue rest
      data.environment2 receipt3 (by rfl)
      (by
        simp [InputStateData.environment2, InputStateData.environment1,
          InputStateData.environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem arity_declare_rewrite_exact (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement arityStatement rest) data.environment3 receipt4) =
      [run rest data.environment4 receipt5] := by
  simpa [coldRelations, CommonProjection.externalName, arityStatement,
    bindProjection, stateArgument, InputStateData.environment4,
    InputStateData.arityValue, receipt5, InputStateData.source]
    using common_projection_declare_rewrite_exact .arity "arity"
      "CettaPeTTaCallGuardNatV1" data.source data.arityValue rest
      data.environment3 receipt4 (by rfl)
      (by
        simp [InputStateData.environment3, InputStateData.environment2,
          InputStateData.environment1, InputStateData.environment0,
          initialEnvironment, lookup?, bindName, environmentBind, identifier,
          node, token])

theorem accepted_declare_rewrite_exact
    (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement acceptedStatement rest)
          data.environment4 receipt5) =
      [run rest data.environment5 receipt6] := by
  simpa [coldRelations, CommonProjection.externalName, acceptedStatement,
    bindProjection, stateArgument, InputStateData.environment5,
    InputStateData.acceptedValue, receipt6, InputStateData.source]
    using common_projection_declare_rewrite_exact .accepted "accepted"
      "CettaPeTTaCallGuardPlansV1" data.source data.acceptedValue rest
      data.environment4 receipt5 (by rfl)
      (by
        simp [InputStateData.environment4, InputStateData.environment3,
          InputStateData.environment2, InputStateData.environment1,
          InputStateData.environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem tail1_shape : tail1 = consStatement revisionStatement tail2 := by rfl
theorem tail2_shape : tail2 = consStatement headStatement tail3 := by rfl
theorem tail3_shape : tail3 = consStatement arityStatement tail4 := by rfl
theorem tail4_shape : tail4 = consStatement acceptedStatement tail5 := by rfl
theorem tail5_shape : tail5 = consStatement remainingStatement tail6 := by rfl
theorem tail6_shape : tail6 = consStatement occurrenceStatement tail7 := by rfl
theorem tail7_shape :
    tail7 = consStatement declarationHeadStatement tail8 := by rfl
theorem tail8_shape : tail8 = consStatement inputsStatement tail9 := by rfl
theorem tail9_shape : tail9 = consStatement outputStatement tail10 := by rfl
theorem tail10_shape : tail10 = consStatement modesStatement tail11 := by rfl
theorem tail11_shape :
    tail11 = consStatement generatedArgumentsDecision (statements []) := by
  rfl

theorem remaining_declare_rewrite_exact
    (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement remainingStatement rest)
          data.environment5 receipt6) =
      [run rest data.environment6 receipt7] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    remainingStatement, bindProjection, stateArgument,
    InputStateData.environment6, InputStateData.remainingValue, receipt7,
    InputStateData.source]
    using declaration_projection_declare_rewrite_exact .remaining "remaining"
      "CettaPeTTaCallGuardDeclarationsV1" data.source data.remainingValue rest
      data.environment5 receipt6 (by rfl)
      (by
        simp [InputStateData.environment5, InputStateData.environment4,
          InputStateData.environment3, InputStateData.environment2,
          InputStateData.environment1, InputStateData.environment0,
          initialEnvironment, lookup?, bindName, environmentBind, identifier,
          node, token])

theorem occurrence_declare_rewrite_exact
    (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement occurrenceStatement rest)
          data.environment6 receipt7) =
      [run rest data.environment7 receipt8] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    occurrenceStatement, bindProjection, stateArgument,
    InputStateData.environment7, InputStateData.occurrenceValue, receipt8,
    InputStateData.source]
    using declaration_projection_declare_rewrite_exact .occurrence "occurrence"
      "CettaPeTTaCallGuardNatV1" data.source data.occurrenceValue rest
      data.environment6 receipt7 (by rfl)
      (by
        simp [InputStateData.environment6, InputStateData.environment5,
          InputStateData.environment4, InputStateData.environment3,
          InputStateData.environment2, InputStateData.environment1,
          InputStateData.environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem declarationHead_declare_rewrite_exact
    (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement declarationHeadStatement rest)
          data.environment7 receipt8) =
      [run rest data.environment8 receipt9] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    declarationHeadStatement, bindProjection, stateArgument,
    InputStateData.environment8, InputStateData.declarationHeadValue, receipt9,
    InputStateData.source]
    using declaration_projection_declare_rewrite_exact .head
      "declaration_head" "CettaPeTTaCallGuardNameV1" data.source
      data.declarationHeadValue rest data.environment7 receipt8 (by rfl)
      (by
        simp [InputStateData.environment7, InputStateData.environment6,
          InputStateData.environment5, InputStateData.environment4,
          InputStateData.environment3, InputStateData.environment2,
          InputStateData.environment1, InputStateData.environment0,
          initialEnvironment, lookup?, bindName, environmentBind, identifier,
          node, token])

theorem inputs_declare_rewrite_exact
    (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement inputsStatement rest)
          data.environment8 receipt9) =
      [run rest data.environment9 receipt10] := by
  simpa [coldRelations, DeclarationProjection.externalName, inputsStatement,
    bindProjection, stateArgument, InputStateData.environment9,
    InputStateData.inputsValue, receipt10, InputStateData.source]
    using declaration_projection_declare_rewrite_exact .inputs "inputs"
      "CettaPeTTaCallGuardTermsV1" data.source data.inputsValue rest
      data.environment8 receipt9 (by rfl)
      (by
        simp [InputStateData.environment8, InputStateData.environment7,
          InputStateData.environment6, InputStateData.environment5,
          InputStateData.environment4, InputStateData.environment3,
          InputStateData.environment2, InputStateData.environment1,
          InputStateData.environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem output_declare_rewrite_exact
    (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement outputStatement rest)
          data.environment9 receipt10) =
      [run rest data.environment10 receipt11] := by
  simpa [coldRelations, DeclarationProjection.externalName, outputStatement,
    bindProjection, stateArgument, InputStateData.environment10,
    InputStateData.outputValue, receipt11, InputStateData.source]
    using declaration_projection_declare_rewrite_exact .output "output"
      "CettaPeTTaCallGuardTermV1" data.source data.outputValue rest
      data.environment9 receipt10 (by rfl)
      (by
        simp [InputStateData.environment9, InputStateData.environment8,
          InputStateData.environment7, InputStateData.environment6,
          InputStateData.environment5, InputStateData.environment4,
          InputStateData.environment3, InputStateData.environment2,
          InputStateData.environment1, InputStateData.environment0,
          initialEnvironment, lookup?, bindName, environmentBind, identifier,
          node, token])

theorem modes_declare_rewrite_exact
    (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement modesStatement rest)
          data.environment10 receipt11) =
      [run rest data.environment11 receipt12] := by
  simpa [coldRelations, ArgumentProjection.externalName, modesStatement,
    bindProjection, stateArgument, InputStateData.environment11,
    InputStateData.modesValue, receipt12, InputStateData.source,
    ArgumentProjection.value?]
    using argument_projection_declare_rewrite_exact .modes "modes"
      "CettaPeTTaCallGuardArgModesV1" data.source data.modesValue rest
      data.environment10 receipt11 (by rfl)
      (by
        simp [InputStateData.environment10, InputStateData.environment9,
          InputStateData.environment8, InputStateData.environment7,
          InputStateData.environment6, InputStateData.environment5,
          InputStateData.environment4, InputStateData.environment3,
          InputStateData.environment2, InputStateData.environment1,
          InputStateData.environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem source_lookup11 (data : InputStateData) :
    lookup? data.environment11 (identifier "state") =
      some (stateValue data.source) := by
  simp [InputStateData.environment11, InputStateData.environment10,
    InputStateData.environment9, InputStateData.environment8,
    InputStateData.environment7, InputStateData.environment6,
    InputStateData.environment5, InputStateData.environment4,
    InputStateData.environment3, InputStateData.environment2,
    InputStateData.environment1, InputStateData.environment0,
    initialEnvironment, lookup?, bindName, environmentBind, identifier, node,
    token]

theorem cursor_nonempty_decision_rewrite_exact
    (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedArgumentsDecision rest)
          data.environment11 receipt12) =
      [run (StructuredC.appendStatements generatedArgumentsNonempty rest)
        data.environment11 receipt13] := by
  have evaluated := arguments_cursor_nonempty_evaluation_exact data.owner
    data.revision data.head data.arity data.declaration data.remaining
    data.expected data.inputCursor data.modes data.accepted data.environment11
    receipt12 (source_lookup11 data)
  have selected :
      selectBranch? falseValue argumentsFinishedBody
          generatedArgumentsNonempty =
        some generatedArgumentsNonempty := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedArgumentsDecision, ifThenElse, node, StructuredC.a, receipt13]
    using if_rewriteAt_exact_of_evaluate coldHandler
      (call inputCursorIsEmptyQuery stateArgument) argumentsFinishedBody
      generatedArgumentsNonempty rest data.environment11 receipt12 falseValue
      data.environment11 receipt13 generatedArgumentsNonempty evaluated selected

theorem nonempty_append_rewrite_exact
    (data : InputStateData) (continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedArgumentsNonempty
          continuation) data.environment11 receipt13) =
      [run (consStatement expectedStatement
          (StructuredC.appendStatements nonemptyTail1 continuation))
        data.environment11 receipt13] := by
  rw [generatedArgumentsNonempty_shape]
  exact appendConsTransition_rewriteAt_exact coldRelations expectedStatement
    nonemptyTail1 continuation data.environment11 receipt13

theorem expected_declare_rewrite_exact
    (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement expectedStatement rest)
          data.environment11 receipt13) =
      [run rest data.environment12 receipt14] := by
  simpa [coldRelations, ArgumentProjection.externalName, expectedStatement,
    bindProjection, stateArgument, InputStateData.environment12,
    InputStateData.expectedValue, receipt14, InputStateData.source,
    ArgumentProjection.value?]
    using argument_projection_declare_rewrite_exact .inputHead "expected"
      "CettaPeTTaCallGuardTermV1" data.source data.expectedValue rest
      data.environment11 receipt13 (by rfl) (source_lookup11 data)

theorem nonempty_tail_append_rewrite_exact
    (data : InputStateData) (continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements nonemptyTail1 continuation)
          data.environment12 receipt14) =
      [run (consStatement inputCursorStatement
          (StructuredC.appendStatements nonemptyTail2 continuation))
        data.environment12 receipt14] := by
  exact appendConsTransition_rewriteAt_exact coldRelations inputCursorStatement
    nonemptyTail2 continuation data.environment12 receipt14

theorem source_lookup12 (data : InputStateData) :
    lookup? data.environment12 (identifier "state") =
      some (stateValue data.source) := by
  simp [InputStateData.environment12, InputStateData.environment11,
    InputStateData.environment10, InputStateData.environment9,
    InputStateData.environment8, InputStateData.environment7,
    InputStateData.environment6, InputStateData.environment5,
    InputStateData.environment4, InputStateData.environment3,
    InputStateData.environment2, InputStateData.environment1,
    InputStateData.environment0, initialEnvironment, lookup?, bindName,
    environmentBind, identifier, node, token]

theorem inputCursor_declare_rewrite_exact
    (data : InputStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement inputCursorStatement rest)
          data.environment12 receipt14) =
      [run rest data.environment13 receipt15] := by
  simpa [coldRelations, ArgumentProjection.externalName, inputCursorStatement,
    bindProjection, stateArgument, InputStateData.environment13,
    InputStateData.inputCursorValue, receipt15, InputStateData.source,
    ArgumentProjection.value?]
    using argument_projection_declare_rewrite_exact .inputTail "input_cursor"
      "CettaPeTTaCallGuardTermsV1" data.source data.inputCursorValue rest
      data.environment12 receipt14 (by rfl) (source_lookup12 data)

def prefixEndpoint (data : InputStateData) : Pattern :=
  run (StructuredC.appendStatements generatedLiteralInputDispatcher
    (StructuredC.appendStatements (statements []) (statements [])))
    data.environment13 receipt15

/-- The exact common prefix consumes twenty-nine authored StructuredC steps.
The remaining fuel is left abstract so each of the five source families can
continue through its own generated branch without replaying this proof. -/
theorem normalize_prefix_exact (data : InputStateData) (fuel : Nat) :
    normalizeFirstUsing coldRelations StructuredC.language 1 (fuel + 29)
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          data.source) =
      normalizeFirstAt (engineBasePremises coldRelations) StructuredC.language
        1 fuel (prefixEndpoint data) := by
  unfold normalizeFirstUsing
  simp only [normalizeFirstAt, phase_rewrite_exact data]
  simp only [dispatcher_append_rewrite_exact data]
  simp only [owner_declare_rewrite_exact data]
  simp only [tail1_shape, appendConsTransition_rewriteAt_exact]
  simp only [revision_declare_rewrite_exact data]
  simp only [tail2_shape, appendConsTransition_rewriteAt_exact]
  simp only [head_declare_rewrite_exact data]
  simp only [tail3_shape, appendConsTransition_rewriteAt_exact]
  simp only [arity_declare_rewrite_exact data]
  simp only [tail4_shape, appendConsTransition_rewriteAt_exact]
  simp only [accepted_declare_rewrite_exact data]
  simp only [tail5_shape, appendConsTransition_rewriteAt_exact]
  simp only [remaining_declare_rewrite_exact data]
  simp only [tail6_shape, appendConsTransition_rewriteAt_exact]
  simp only [occurrence_declare_rewrite_exact data]
  simp only [tail7_shape, appendConsTransition_rewriteAt_exact]
  simp only [declarationHead_declare_rewrite_exact data]
  simp only [tail8_shape, appendConsTransition_rewriteAt_exact]
  simp only [inputs_declare_rewrite_exact data]
  simp only [tail9_shape, appendConsTransition_rewriteAt_exact]
  simp only [output_declare_rewrite_exact data]
  simp only [tail10_shape, appendConsTransition_rewriteAt_exact]
  simp only [modes_declare_rewrite_exact data]
  simp only [tail11_shape, appendConsTransition_rewriteAt_exact]
  simp only [cursor_nonempty_decision_rewrite_exact data]
  simp only [nonempty_append_rewrite_exact data]
  simp only [expected_declare_rewrite_exact data]
  simp only [nonempty_tail_append_rewrite_exact data]
  simp only [inputCursor_declare_rewrite_exact data]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation
