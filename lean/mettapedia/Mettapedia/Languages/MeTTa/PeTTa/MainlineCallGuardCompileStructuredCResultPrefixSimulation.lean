import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOpenInputSimulation

/-!
# Shared generated StructuredC prefix for result states

All five result families share phase selection followed by the exact common,
declaration, and accumulated-mode projections.  This module proves those
twenty-four StructuredC reductions once and stops at the first authored result
decision.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation

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

structure ResultStateData where
  owner : SpaceOwner
  revision : Nat
  head : String
  arity : Nat
  declaration : ArrowDeclaration
  remaining : List ArrowDeclaration
  modes : List ArgMode
  accepted : List GuardPlan
deriving Repr

namespace ResultStateData

def source (data : ResultStateData) : CompileLanguageControl :=
  .result data.owner data.revision data.head data.arity data.declaration
    data.remaining data.modes data.accepted

def ownerValue (data : ResultStateData) : Pattern :=
  abiValue (encodeOwner data.owner)
def revisionValue (data : ResultStateData) : Pattern :=
  abiValue (encodeNat data.revision)
def headValue (data : ResultStateData) : Pattern :=
  abiValue (encodeName data.head)
def arityValue (data : ResultStateData) : Pattern :=
  abiValue (encodeNat data.arity)
def acceptedValue (data : ResultStateData) : Pattern :=
  abiValue (encodePlans data.accepted)
def remainingValue (data : ResultStateData) : Pattern :=
  abiValue (encodeDeclarations data.remaining)
def occurrenceValue (data : ResultStateData) : Pattern :=
  abiValue (encodeNat data.declaration.occurrence)
def declarationHeadValue (data : ResultStateData) : Pattern :=
  abiValue (encodeName data.declaration.function)
def inputsValue (data : ResultStateData) : Pattern :=
  abiValue (encodeTerms data.declaration.inputTypes)
def outputValue (data : ResultStateData) : Pattern :=
  abiValue (encodeTerm data.declaration.outputType)
def modesValue (data : ResultStateData) : Pattern :=
  abiValue (encodeArgModes data.modes)

def environment0 (data : ResultStateData) : Pattern :=
  initialEnvironment data.source
def environment1 (data : ResultStateData) : Pattern :=
  bindName "owner" data.ownerValue data.environment0
def environment2 (data : ResultStateData) : Pattern :=
  bindName "revision" data.revisionValue data.environment1
def environment3 (data : ResultStateData) : Pattern :=
  bindName "head" data.headValue data.environment2
def environment4 (data : ResultStateData) : Pattern :=
  bindName "arity" data.arityValue data.environment3
def environment5 (data : ResultStateData) : Pattern :=
  bindName "accepted" data.acceptedValue data.environment4
def environment6 (data : ResultStateData) : Pattern :=
  bindName "remaining" data.remainingValue data.environment5
def environment7 (data : ResultStateData) : Pattern :=
  bindName "occurrence" data.occurrenceValue data.environment6
def environment8 (data : ResultStateData) : Pattern :=
  bindName "declaration_head" data.declarationHeadValue data.environment7
def environment9 (data : ResultStateData) : Pattern :=
  bindName "inputs" data.inputsValue data.environment8
def environment10 (data : ResultStateData) : Pattern :=
  bindName "output" data.outputValue data.environment9
def environment11 (data : ResultStateData) : Pattern :=
  bindName "modes" data.modesValue data.environment10

end ResultStateData

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
  generatedUndefinedResultDecision]
def tail2 : Pattern := statements [headStatement, arityStatement,
  acceptedStatement, remainingStatement, occurrenceStatement,
  declarationHeadStatement, inputsStatement, outputStatement, modesStatement,
  generatedUndefinedResultDecision]
def tail3 : Pattern := statements [arityStatement, acceptedStatement,
  remainingStatement, occurrenceStatement, declarationHeadStatement,
  inputsStatement, outputStatement, modesStatement,
  generatedUndefinedResultDecision]
def tail4 : Pattern := statements [acceptedStatement, remainingStatement,
  occurrenceStatement, declarationHeadStatement, inputsStatement,
  outputStatement, modesStatement, generatedUndefinedResultDecision]
def tail5 : Pattern := statements [remainingStatement, occurrenceStatement,
  declarationHeadStatement, inputsStatement, outputStatement, modesStatement,
  generatedUndefinedResultDecision]
def tail6 : Pattern := statements [occurrenceStatement,
  declarationHeadStatement, inputsStatement, outputStatement, modesStatement,
  generatedUndefinedResultDecision]
def tail7 : Pattern := statements [declarationHeadStatement, inputsStatement,
  outputStatement, modesStatement, generatedUndefinedResultDecision]
def tail8 : Pattern := statements [inputsStatement, outputStatement,
  modesStatement, generatedUndefinedResultDecision]
def tail9 : Pattern := statements [outputStatement, modesStatement,
  generatedUndefinedResultDecision]
def tail10 : Pattern := statements [modesStatement,
  generatedUndefinedResultDecision]
def tail11 : Pattern := statements [generatedUndefinedResultDecision]

theorem phase_selection_exact (data : ResultStateData) :
    selectCase? (phaseValue data.source) generatedFaultBody
        generatedPhaseCases = some generatedResultDispatcher := by
  rfl

theorem phase_rewrite_exact (data : ResultStateData) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          data.source) =
      [run (StructuredC.appendStatements generatedResultDispatcher
          (statements [])) data.environment0 receipt1] := by
  simpa [coldRelations, ResultStateData.source, ResultStateData.environment0,
    receipt1, receipt0,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl]
    using phase_switch_rewrite_exact data.source generatedResultDispatcher
      data.environment0 receipt0
      (by
        simp [ResultStateData.environment0, initialEnvironment, lookup?,
          bindName, environmentBind, identifier, node, token])
      (phase_selection_exact data)

theorem dispatcher_append_rewrite_exact (data : ResultStateData) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedResultDispatcher
          (statements [])) data.environment0 receipt1) =
      [run (consStatement ownerStatement
          (StructuredC.appendStatements tail1 (statements [])))
        data.environment0 receipt1] := by
  rw [generatedResultDispatcher_shape]
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement ownerStatement tail1) (statements []))
        data.environment0 receipt1) = _
  exact appendConsTransition_rewriteAt_exact coldRelations ownerStatement tail1
    (statements []) data.environment0 receipt1

theorem source_lookup0 (data : ResultStateData) :
    lookup? data.environment0 (identifier "state") =
      some (stateValue data.source) := by
  simp [ResultStateData.environment0, initialEnvironment, lookup?, bindName,
    environmentBind, identifier, node, token]

theorem source_lookup1 (data : ResultStateData) :
    lookup? data.environment1 (identifier "state") =
      some (stateValue data.source) := by
  simp [ResultStateData.environment1, ResultStateData.environment0,
    initialEnvironment, lookup?, bindName, environmentBind, identifier, node,
    token]

theorem owner_declare_rewrite_exact (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement ownerStatement rest) data.environment0 receipt1) =
      [run rest data.environment1 receipt2] := by
  simpa [coldRelations, CommonProjection.externalName, ownerStatement,
    bindProjection, stateArgument, ResultStateData.environment1,
    ResultStateData.ownerValue, receipt2, ResultStateData.source] using
    common_projection_declare_rewrite_exact .owner "owner"
      "CettaPeTTaCallGuardOwnerV1" data.source data.ownerValue rest
      data.environment0 receipt1 (by rfl) (source_lookup0 data)

theorem revision_declare_rewrite_exact
    (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement revisionStatement rest)
          data.environment1 receipt2) =
      [run rest data.environment2 receipt3] := by
  simpa [coldRelations, CommonProjection.externalName, revisionStatement,
    bindProjection, stateArgument, ResultStateData.environment2,
    ResultStateData.revisionValue, receipt3, ResultStateData.source] using
    common_projection_declare_rewrite_exact .revision "revision"
      "CettaPeTTaCallGuardNatV1" data.source data.revisionValue rest
      data.environment1 receipt2 (by rfl) (source_lookup1 data)

theorem source_lookup2 (data : ResultStateData) :
    lookup? data.environment2 (identifier "state") =
      some (stateValue data.source) := by
  simp [ResultStateData.environment2, ResultStateData.environment1,
    ResultStateData.environment0, initialEnvironment, lookup?, bindName,
    environmentBind, identifier, node, token]

theorem head_declare_rewrite_exact
    (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement headStatement rest) data.environment2 receipt3) =
      [run rest data.environment3 receipt4] := by
  simpa [coldRelations, CommonProjection.externalName, headStatement,
    bindProjection, stateArgument, ResultStateData.environment3,
    ResultStateData.headValue, receipt4, ResultStateData.source] using
    common_projection_declare_rewrite_exact .head "head"
      "CettaPeTTaCallGuardNameV1" data.source data.headValue rest
      data.environment2 receipt3 (by rfl) (source_lookup2 data)

theorem source_lookup3 (data : ResultStateData) :
    lookup? data.environment3 (identifier "state") =
      some (stateValue data.source) := by
  simp [ResultStateData.environment3, ResultStateData.environment2,
    ResultStateData.environment1, ResultStateData.environment0,
    initialEnvironment, lookup?, bindName, environmentBind, identifier, node,
    token]

theorem arity_declare_rewrite_exact
    (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement arityStatement rest) data.environment3 receipt4) =
      [run rest data.environment4 receipt5] := by
  simpa [coldRelations, CommonProjection.externalName, arityStatement,
    bindProjection, stateArgument, ResultStateData.environment4,
    ResultStateData.arityValue, receipt5, ResultStateData.source] using
    common_projection_declare_rewrite_exact .arity "arity"
      "CettaPeTTaCallGuardNatV1" data.source data.arityValue rest
      data.environment3 receipt4 (by rfl) (source_lookup3 data)

theorem source_lookup4 (data : ResultStateData) :
    lookup? data.environment4 (identifier "state") =
      some (stateValue data.source) := by
  simp [ResultStateData.environment4, ResultStateData.environment3,
    ResultStateData.environment2, ResultStateData.environment1,
    ResultStateData.environment0, initialEnvironment, lookup?, bindName,
    environmentBind, identifier, node, token]

theorem accepted_declare_rewrite_exact
    (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement acceptedStatement rest)
          data.environment4 receipt5) =
      [run rest data.environment5 receipt6] := by
  simpa [coldRelations, CommonProjection.externalName, acceptedStatement,
    bindProjection, stateArgument, ResultStateData.environment5,
    ResultStateData.acceptedValue, receipt6, ResultStateData.source] using
    common_projection_declare_rewrite_exact .accepted "accepted"
      "CettaPeTTaCallGuardPlansV1" data.source data.acceptedValue rest
      data.environment4 receipt5 (by rfl) (source_lookup4 data)

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
    tail11 = consStatement generatedUndefinedResultDecision (statements []) := by
  rfl

theorem source_lookup5 (data : ResultStateData) :
    lookup? data.environment5 (identifier "state") =
      some (stateValue data.source) := by
  simp [ResultStateData.environment5, ResultStateData.environment4,
    ResultStateData.environment3, ResultStateData.environment2,
    ResultStateData.environment1, ResultStateData.environment0,
    initialEnvironment, lookup?, bindName, environmentBind, identifier, node,
    token]

theorem remaining_declare_rewrite_exact
    (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement remainingStatement rest)
          data.environment5 receipt6) =
      [run rest data.environment6 receipt7] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    remainingStatement, bindProjection, stateArgument,
    ResultStateData.environment6, ResultStateData.remainingValue, receipt7,
    ResultStateData.source] using
    declaration_projection_declare_rewrite_exact .remaining "remaining"
      "CettaPeTTaCallGuardDeclarationsV1" data.source data.remainingValue rest
      data.environment5 receipt6 (by rfl) (source_lookup5 data)

theorem source_lookup6 (data : ResultStateData) :
    lookup? data.environment6 (identifier "state") =
      some (stateValue data.source) := by
  simp [ResultStateData.environment6, ResultStateData.environment5,
    ResultStateData.environment4, ResultStateData.environment3,
    ResultStateData.environment2, ResultStateData.environment1,
    ResultStateData.environment0, initialEnvironment, lookup?, bindName,
    environmentBind, identifier, node, token]

theorem occurrence_declare_rewrite_exact
    (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement occurrenceStatement rest)
          data.environment6 receipt7) =
      [run rest data.environment7 receipt8] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    occurrenceStatement, bindProjection, stateArgument,
    ResultStateData.environment7, ResultStateData.occurrenceValue, receipt8,
    ResultStateData.source] using
    declaration_projection_declare_rewrite_exact .occurrence "occurrence"
      "CettaPeTTaCallGuardNatV1" data.source data.occurrenceValue rest
      data.environment6 receipt7 (by rfl) (source_lookup6 data)

theorem source_lookup7 (data : ResultStateData) :
    lookup? data.environment7 (identifier "state") =
      some (stateValue data.source) := by
  simp [ResultStateData.environment7, ResultStateData.environment6,
    ResultStateData.environment5, ResultStateData.environment4,
    ResultStateData.environment3, ResultStateData.environment2,
    ResultStateData.environment1, ResultStateData.environment0,
    initialEnvironment, lookup?, bindName, environmentBind, identifier, node,
    token]

theorem declarationHead_declare_rewrite_exact
    (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement declarationHeadStatement rest)
          data.environment7 receipt8) =
      [run rest data.environment8 receipt9] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    declarationHeadStatement, bindProjection, stateArgument,
    ResultStateData.environment8, ResultStateData.declarationHeadValue,
    receipt9, ResultStateData.source] using
    declaration_projection_declare_rewrite_exact .head "declaration_head"
      "CettaPeTTaCallGuardNameV1" data.source data.declarationHeadValue rest
      data.environment7 receipt8 (by rfl) (source_lookup7 data)

theorem source_lookup8 (data : ResultStateData) :
    lookup? data.environment8 (identifier "state") =
      some (stateValue data.source) := by
  simp [ResultStateData.environment8, ResultStateData.environment7,
    ResultStateData.environment6, ResultStateData.environment5,
    ResultStateData.environment4, ResultStateData.environment3,
    ResultStateData.environment2, ResultStateData.environment1,
    ResultStateData.environment0, initialEnvironment, lookup?, bindName,
    environmentBind, identifier, node, token]

theorem inputs_declare_rewrite_exact
    (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement inputsStatement rest)
          data.environment8 receipt9) =
      [run rest data.environment9 receipt10] := by
  simpa [coldRelations, DeclarationProjection.externalName, inputsStatement,
    bindProjection, stateArgument, ResultStateData.environment9,
    ResultStateData.inputsValue, receipt10, ResultStateData.source] using
    declaration_projection_declare_rewrite_exact .inputs "inputs"
      "CettaPeTTaCallGuardTermsV1" data.source data.inputsValue rest
      data.environment8 receipt9 (by rfl) (source_lookup8 data)

theorem source_lookup9 (data : ResultStateData) :
    lookup? data.environment9 (identifier "state") =
      some (stateValue data.source) := by
  simp [ResultStateData.environment9, ResultStateData.environment8,
    ResultStateData.environment7, ResultStateData.environment6,
    ResultStateData.environment5, ResultStateData.environment4,
    ResultStateData.environment3, ResultStateData.environment2,
    ResultStateData.environment1, ResultStateData.environment0,
    initialEnvironment, lookup?, bindName, environmentBind, identifier, node,
    token]

theorem output_declare_rewrite_exact
    (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement outputStatement rest)
          data.environment9 receipt10) =
      [run rest data.environment10 receipt11] := by
  simpa [coldRelations, DeclarationProjection.externalName, outputStatement,
    bindProjection, stateArgument, ResultStateData.environment10,
    ResultStateData.outputValue, receipt11, ResultStateData.source] using
    declaration_projection_declare_rewrite_exact .output "output"
      "CettaPeTTaCallGuardTermV1" data.source data.outputValue rest
      data.environment9 receipt10 (by rfl) (source_lookup9 data)

theorem source_lookup10 (data : ResultStateData) :
    lookup? data.environment10 (identifier "state") =
      some (stateValue data.source) := by
  simp [ResultStateData.environment10, ResultStateData.environment9,
    ResultStateData.environment8, ResultStateData.environment7,
    ResultStateData.environment6, ResultStateData.environment5,
    ResultStateData.environment4, ResultStateData.environment3,
    ResultStateData.environment2, ResultStateData.environment1,
    ResultStateData.environment0, initialEnvironment, lookup?, bindName,
    environmentBind, identifier, node, token]

theorem modes_declare_rewrite_exact
    (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement modesStatement rest)
          data.environment10 receipt11) =
      [run rest data.environment11 receipt12] := by
  simpa [coldRelations, ArgumentProjection.externalName, modesStatement,
    bindProjection, stateArgument, ResultStateData.environment11,
    ResultStateData.modesValue, receipt12, ResultStateData.source,
    ArgumentProjection.value?] using
    argument_projection_declare_rewrite_exact .modes "modes"
      "CettaPeTTaCallGuardArgModesV1" data.source data.modesValue rest
      data.environment10 receipt11 (by rfl) (source_lookup10 data)

def baseContinuation : Pattern :=
  StructuredC.appendStatements (statements []) (statements [])

def prefixEndpoint (data : ResultStateData) : Pattern :=
  run (consStatement generatedUndefinedResultDecision baseContinuation)
    data.environment11 receipt12

/-- The exact shared result prefix consumes twenty-four authored StructuredC
steps. -/
theorem normalize_prefix_exact (data : ResultStateData) (fuel : Nat) :
    normalizeFirstUsing coldRelations StructuredC.language 1 (fuel + 24)
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
  rfl

#print axioms normalize_prefix_exact

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation
