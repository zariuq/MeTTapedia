import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCBeginDeclarationSimulation

/-!
# Generated StructuredC realization of arguments-finished

The first argument-phase family is premise-free but not structure-free.  The
generated program projects eleven source fields, checks that the input cursor
is empty, constructs the exact result-compilation state from twelve ordered
operands, and returns through the authored StructuredC semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCArgumentsFinishedSimulation

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission
open Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
open Mettapedia.GSLT.LanguageDef.NormalizationPath
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

def source
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    CompileLanguageControl :=
  .arguments owner revision head arity declaration remaining [] modes accepted

def target
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    CompileLanguageControl :=
  .result owner revision head arity declaration remaining modes accepted

def ownerValue (owner : SpaceOwner) : Pattern := abiValue (encodeOwner owner)
def revisionValue (revision : Nat) : Pattern := abiValue (encodeNat revision)
def headValue (head : String) : Pattern := abiValue (encodeName head)
def arityValue (arity : Nat) : Pattern := abiValue (encodeNat arity)
def acceptedValue (accepted : List GuardPlan) : Pattern :=
  abiValue (encodePlans accepted)
def remainingValue (remaining : List ArrowDeclaration) : Pattern :=
  abiValue (encodeDeclarations remaining)
def occurrenceValue (declaration : ArrowDeclaration) : Pattern :=
  abiValue (encodeNat declaration.occurrence)
def declarationHeadValue (declaration : ArrowDeclaration) : Pattern :=
  abiValue (encodeName declaration.function)
def inputsValue (declaration : ArrowDeclaration) : Pattern :=
  abiValue (encodeTerms declaration.inputTypes)
def outputValue (declaration : ArrowDeclaration) : Pattern :=
  abiValue (encodeTerm declaration.outputType)
def modesValue (modes : List ArgMode) : Pattern := abiValue (encodeArgModes modes)

def environment0
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  initialEnvironment
    (source owner revision head arity declaration remaining modes accepted)

def environment1
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "owner" (ownerValue owner)
    (environment0 owner revision head arity declaration remaining modes accepted)

def environment2
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "revision" (revisionValue revision)
    (environment1 owner revision head arity declaration remaining modes accepted)

def environment3
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "head" (headValue head)
    (environment2 owner revision head arity declaration remaining modes accepted)

def environment4
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "arity" (arityValue arity)
    (environment3 owner revision head arity declaration remaining modes accepted)

def environment5
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "accepted" (acceptedValue accepted)
    (environment4 owner revision head arity declaration remaining modes accepted)

def environment6
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "remaining" (remainingValue remaining)
    (environment5 owner revision head arity declaration remaining modes accepted)

def environment7
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "occurrence" (occurrenceValue declaration)
    (environment6 owner revision head arity declaration remaining modes accepted)

def environment8
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "declaration_head" (declarationHeadValue declaration)
    (environment7 owner revision head arity declaration remaining modes accepted)

def environment9
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "inputs" (inputsValue declaration)
    (environment8 owner revision head arity declaration remaining modes accepted)

def environment10
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "output" (outputValue declaration)
    (environment9 owner revision head arity declaration remaining modes accepted)

def environment11
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "modes" (modesValue modes)
    (environment10 owner revision head arity declaration remaining modes accepted)

def environment12
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  bindName "state"
    (stateValue (target owner revision head arity declaration remaining modes
      accepted))
    (environment11 owner revision head arity declaration remaining modes accepted)

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
def receipt14 : Pattern := externalReceipt setCompileResultDelta receipt13

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

theorem generated_arguments_dispatcher_spine :
    generatedArgumentsDispatcher = consStatement ownerStatement tail1 := by
  rw [generatedArgumentsDispatcher_shape]
  rfl

theorem tail1_shape : tail1 = consStatement revisionStatement tail2 := by rfl
theorem tail2_shape : tail2 = consStatement headStatement tail3 := by rfl
theorem tail3_shape : tail3 = consStatement arityStatement tail4 := by rfl
theorem tail4_shape : tail4 = consStatement acceptedStatement tail5 := by rfl
theorem tail5_shape : tail5 = consStatement remainingStatement tail6 := by rfl
theorem tail6_shape : tail6 = consStatement occurrenceStatement tail7 := by rfl
theorem tail7_shape : tail7 = consStatement declarationHeadStatement tail8 := by rfl
theorem tail8_shape : tail8 = consStatement inputsStatement tail9 := by rfl
theorem tail9_shape : tail9 = consStatement outputStatement tail10 := by rfl
theorem tail10_shape : tail10 = consStatement modesStatement tail11 := by rfl
theorem tail11_shape :
    tail11 = consStatement generatedArgumentsDecision (statements []) := by
  rfl

theorem phase_selection_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    selectCase?
        (phaseValue
          (source owner revision head arity declaration remaining modes
            accepted))
        generatedFaultBody generatedPhaseCases =
      some generatedArgumentsDispatcher := by
  rfl

theorem phase_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source owner revision head arity declaration remaining modes
            accepted)) =
      [run (StructuredC.appendStatements generatedArgumentsDispatcher
          (statements []))
        (environment0 owner revision head arity declaration remaining modes
          accepted) receipt1] := by
  simpa [coldRelations, source, environment0, receipt1, receipt0,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl]
    using phase_switch_rewrite_exact
      (source owner revision head arity declaration remaining modes accepted)
      generatedArgumentsDispatcher
      (environment0 owner revision head arity declaration remaining modes
        accepted) receipt0
      (by
        simp [environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])
      (phase_selection_exact owner revision head arity declaration remaining
        modes accepted)

theorem dispatcher_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedArgumentsDispatcher
          (statements []))
          (environment0 owner revision head arity declaration remaining modes
            accepted) receipt1) =
      [run (consStatement ownerStatement
          (StructuredC.appendStatements tail1 (statements [])))
        (environment0 owner revision head arity declaration remaining modes
          accepted) receipt1] := by
  rw [generated_arguments_dispatcher_spine]
  exact appendConsTransition_rewriteAt_exact coldRelations ownerStatement tail1
    (statements [])
    (environment0 owner revision head arity declaration remaining modes accepted)
    receipt1

theorem owner_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement ownerStatement rest)
          (environment0 owner revision head arity declaration remaining modes
            accepted) receipt1) =
      [run rest
        (environment1 owner revision head arity declaration remaining modes
          accepted) receipt2] := by
  simpa [coldRelations, CommonProjection.externalName, ownerStatement,
    bindProjection, stateArgument, environment1, ownerValue, receipt2, source]
    using common_projection_declare_rewrite_exact .owner "owner"
      "CettaPeTTaCallGuardOwnerV1"
      (source owner revision head arity declaration remaining modes accepted)
      (ownerValue owner) rest
      (environment0 owner revision head arity declaration remaining modes
        accepted) receipt1 (by rfl)
      (by
        simp [environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem revision_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement revisionStatement rest)
          (environment1 owner revision head arity declaration remaining modes
            accepted) receipt2) =
      [run rest
        (environment2 owner revision head arity declaration remaining modes
          accepted) receipt3] := by
  simpa [coldRelations, CommonProjection.externalName, revisionStatement,
    bindProjection, stateArgument, environment2, revisionValue, receipt3,
    source] using
    common_projection_declare_rewrite_exact .revision "revision"
      "CettaPeTTaCallGuardNatV1"
      (source owner revision head arity declaration remaining modes accepted)
      (revisionValue revision) rest
      (environment1 owner revision head arity declaration remaining modes
        accepted) receipt2 (by rfl)
      (by
        simp [environment1, environment0, initialEnvironment, lookup?,
          bindName, environmentBind, identifier, node, token])

theorem head_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement headStatement rest)
          (environment2 owner revision head arity declaration remaining modes
            accepted) receipt3) =
      [run rest
        (environment3 owner revision head arity declaration remaining modes
          accepted) receipt4] := by
  simpa [coldRelations, CommonProjection.externalName, headStatement,
    bindProjection, stateArgument, environment3, headValue, receipt4, source]
    using common_projection_declare_rewrite_exact .head "head"
      "CettaPeTTaCallGuardNameV1"
      (source owner revision head arity declaration remaining modes accepted)
      (headValue head) rest
      (environment2 owner revision head arity declaration remaining modes
        accepted) receipt3 (by rfl)
      (by
        simp [environment2, environment1, environment0, initialEnvironment,
          lookup?, bindName, environmentBind, identifier, node, token])

theorem arity_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement arityStatement rest)
          (environment3 owner revision head arity declaration remaining modes
            accepted) receipt4) =
      [run rest
        (environment4 owner revision head arity declaration remaining modes
          accepted) receipt5] := by
  simpa [coldRelations, CommonProjection.externalName, arityStatement,
    bindProjection, stateArgument, environment4, arityValue, receipt5, source]
    using common_projection_declare_rewrite_exact .arity "arity"
      "CettaPeTTaCallGuardNatV1"
      (source owner revision head arity declaration remaining modes accepted)
      (arityValue arity) rest
      (environment3 owner revision head arity declaration remaining modes
        accepted) receipt4 (by rfl)
      (by
        simp [environment3, environment2, environment1, environment0,
          initialEnvironment, lookup?, bindName, environmentBind, identifier,
          node, token])

theorem accepted_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement acceptedStatement rest)
          (environment4 owner revision head arity declaration remaining modes
            accepted) receipt5) =
      [run rest
        (environment5 owner revision head arity declaration remaining modes
          accepted) receipt6] := by
  simpa [coldRelations, CommonProjection.externalName, acceptedStatement,
    bindProjection, stateArgument, environment5, acceptedValue, receipt6,
    source] using
    common_projection_declare_rewrite_exact .accepted "accepted"
      "CettaPeTTaCallGuardPlansV1"
      (source owner revision head arity declaration remaining modes accepted)
      (acceptedValue accepted) rest
      (environment4 owner revision head arity declaration remaining modes
        accepted) receipt5 (by rfl)
      (by
        simp [environment4, environment3, environment2, environment1,
          environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem remaining_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement remainingStatement rest)
          (environment5 owner revision head arity declaration remaining modes
            accepted) receipt6) =
      [run rest
        (environment6 owner revision head arity declaration remaining modes
          accepted) receipt7] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    remainingStatement, bindProjection, stateArgument, environment6,
    remainingValue, receipt7, source] using
    declaration_projection_declare_rewrite_exact .remaining "remaining"
      "CettaPeTTaCallGuardDeclarationsV1"
      (source owner revision head arity declaration remaining modes accepted)
      (remainingValue remaining) rest
      (environment5 owner revision head arity declaration remaining modes
        accepted) receipt6 (by rfl)
      (by
        simp [environment5, environment4, environment3, environment2,
          environment1, environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem occurrence_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement occurrenceStatement rest)
          (environment6 owner revision head arity declaration remaining modes
            accepted) receipt7) =
      [run rest
        (environment7 owner revision head arity declaration remaining modes
          accepted) receipt8] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    occurrenceStatement, bindProjection, stateArgument, environment7,
    occurrenceValue, receipt8, source] using
    declaration_projection_declare_rewrite_exact .occurrence "occurrence"
      "CettaPeTTaCallGuardNatV1"
      (source owner revision head arity declaration remaining modes accepted)
      (occurrenceValue declaration) rest
      (environment6 owner revision head arity declaration remaining modes
        accepted) receipt7 (by rfl)
      (by
        simp [environment6, environment5, environment4, environment3,
          environment2, environment1, environment0, initialEnvironment,
          lookup?, bindName, environmentBind, identifier, node, token])

theorem declarationHead_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement declarationHeadStatement rest)
          (environment7 owner revision head arity declaration remaining modes
            accepted) receipt8) =
      [run rest
        (environment8 owner revision head arity declaration remaining modes
          accepted) receipt9] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    declarationHeadStatement, bindProjection, stateArgument, environment8,
    declarationHeadValue, receipt9, source] using
    declaration_projection_declare_rewrite_exact .head "declaration_head"
      "CettaPeTTaCallGuardNameV1"
      (source owner revision head arity declaration remaining modes accepted)
      (declarationHeadValue declaration) rest
      (environment7 owner revision head arity declaration remaining modes
        accepted) receipt8 (by rfl)
      (by
        simp [environment7, environment6, environment5, environment4,
          environment3, environment2, environment1, environment0,
          initialEnvironment, lookup?, bindName, environmentBind, identifier,
          node, token])

theorem inputs_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement inputsStatement rest)
          (environment8 owner revision head arity declaration remaining modes
            accepted) receipt9) =
      [run rest
        (environment9 owner revision head arity declaration remaining modes
          accepted) receipt10] := by
  simpa [coldRelations, DeclarationProjection.externalName, inputsStatement,
    bindProjection, stateArgument, environment9, inputsValue, receipt10,
    source] using
    declaration_projection_declare_rewrite_exact .inputs "inputs"
      "CettaPeTTaCallGuardTermsV1"
      (source owner revision head arity declaration remaining modes accepted)
      (inputsValue declaration) rest
      (environment8 owner revision head arity declaration remaining modes
        accepted) receipt9 (by rfl)
      (by
        simp [environment8, environment7, environment6, environment5,
          environment4, environment3, environment2, environment1,
          environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem output_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement outputStatement rest)
          (environment9 owner revision head arity declaration remaining modes
            accepted) receipt10) =
      [run rest
        (environment10 owner revision head arity declaration remaining modes
          accepted) receipt11] := by
  simpa [coldRelations, DeclarationProjection.externalName, outputStatement,
    bindProjection, stateArgument, environment10, outputValue, receipt11,
    source] using
    declaration_projection_declare_rewrite_exact .output "output"
      "CettaPeTTaCallGuardTermV1"
      (source owner revision head arity declaration remaining modes accepted)
      (outputValue declaration) rest
      (environment9 owner revision head arity declaration remaining modes
        accepted) receipt10 (by rfl)
      (by
        simp [environment9, environment8, environment7, environment6,
          environment5, environment4, environment3, environment2,
          environment1, environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem modes_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement modesStatement rest)
          (environment10 owner revision head arity declaration remaining modes
            accepted) receipt11) =
      [run rest
        (environment11 owner revision head arity declaration remaining modes
          accepted) receipt12] := by
  simpa [coldRelations, ArgumentProjection.externalName, modesStatement,
    bindProjection, stateArgument, environment11, modesValue, receipt12,
    source, ArgumentProjection.value?] using
    argument_projection_declare_rewrite_exact .modes "modes"
      "CettaPeTTaCallGuardArgModesV1"
      (source owner revision head arity declaration remaining modes accepted)
      (modesValue modes) rest
      (environment10 owner revision head arity declaration remaining modes
        accepted) receipt11 (by rfl)
      (by
        simp [environment10, environment9, environment8, environment7,
          environment6, environment5, environment4, environment3,
          environment2, environment1, environment0, initialEnvironment,
          lookup?, bindName, environmentBind, identifier, node, token])

theorem source_lookup11
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    lookup?
        (environment11 owner revision head arity declaration remaining modes
          accepted) (identifier "state") =
      some (stateValue
        (source owner revision head arity declaration remaining modes
          accepted)) := by
  simp [environment11, environment10, environment9, environment8,
    environment7, environment6, environment5, environment4, environment3,
    environment2, environment1, environment0, initialEnvironment, lookup?,
    bindName, environmentBind, identifier, node, token]

theorem cursor_empty_decision_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedArgumentsDecision rest)
          (environment11 owner revision head arity declaration remaining modes
            accepted) receipt12) =
      [run (StructuredC.appendStatements argumentsFinishedBody rest)
        (environment11 owner revision head arity declaration remaining modes
          accepted) receipt13] := by
  have evaluated := arguments_cursor_empty_evaluation_exact owner revision head
    arity declaration remaining modes accepted
    (environment11 owner revision head arity declaration remaining modes
      accepted) receipt12
    (source_lookup11 owner revision head arity declaration remaining modes
      accepted)
  have selected :
      selectBranch? trueValue argumentsFinishedBody generatedArgumentsNonempty =
        some argumentsFinishedBody := by
    simp [selectBranch?]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedArgumentsDecision, ifThenElse, node, StructuredC.a, receipt13]
    using if_rewriteAt_exact_of_evaluate coldHandler
      (call inputCursorIsEmptyQuery stateArgument) argumentsFinishedBody
      generatedArgumentsNonempty rest
      (environment11 owner revision head arity declaration remaining modes
        accepted) receipt12 trueValue
      (environment11 owner revision head arity declaration remaining modes
        accepted) receipt13 argumentsFinishedBody evaluated selected

def effectStatement : Pattern :=
  effect (call setCompileResultDelta
    (["state", "owner", "revision", "head", "arity", "occurrence",
      "declaration_head", "inputs", "output", "remaining", "modes",
      "accepted"].map variableExpression))

def returnStatements : Pattern := statements [returnSymbol advancedOutcome]

theorem finished_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements argumentsFinishedBody continuation)
          (environment11 owner revision head arity declaration remaining modes
            accepted) receipt13) =
      [run (consStatement effectStatement
          (StructuredC.appendStatements returnStatements continuation))
        (environment11 owner revision head arity declaration remaining modes
          accepted) receipt13] := by
  rw [argumentsFinishedBody_shape]
  simpa [effectStatement, returnStatements, statements, node,
    StructuredC.consStatement, StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations effectStatement
      returnStatements continuation
      (environment11 owner revision head arity declaration remaining modes
        accepted) receipt13

theorem delta_operands_lookup
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    List.Forall₂
      (fun slot value =>
        lookup?
          (environment11 owner revision head arity declaration remaining modes
            accepted) (identifier slot) = some value)
      ["state", "owner", "revision", "head", "arity", "occurrence",
        "declaration_head", "inputs", "output", "remaining", "modes",
        "accepted"]
      [ stateValue
          (source owner revision head arity declaration remaining modes
            accepted)
      , ownerValue owner
      , revisionValue revision
      , headValue head
      , arityValue arity
      , occurrenceValue declaration
      , declarationHeadValue declaration
      , inputsValue declaration
      , outputValue declaration
      , remainingValue remaining
      , modesValue modes
      , acceptedValue accepted ] := by
  simp [source, environment11, environment10, environment9, environment8,
    environment7, environment6, environment5, environment4, environment3,
    environment2, environment1, environment0, initialEnvironment, ownerValue,
    revisionValue, headValue, arityValue, occurrenceValue,
    declarationHeadValue, inputsValue, outputValue, remainingValue, modesValue,
    acceptedValue, lookup?, bindName, environmentBind, environmentEmpty,
    identifier, node, token]

theorem delta_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement effectStatement rest)
          (environment11 owner revision head arity declaration remaining modes
            accepted) receipt13) =
      [run rest
        (environment12 owner revision head arity declaration remaining modes
          accepted) receipt14] := by
  have evaluated := argumentsFinished_delta_evaluation_exact owner revision head
    arity declaration remaining modes accepted
    (environment11 owner revision head arity declaration remaining modes
      accepted) receipt13
    (source_lookup11 owner revision head arity declaration remaining modes
      accepted)
    (by
      simpa [source, ownerValue, revisionValue, headValue, arityValue,
        occurrenceValue, declarationHeadValue, inputsValue, outputValue,
        remainingValue, modesValue, acceptedValue] using
        delta_operands_lookup owner revision head arity declaration remaining
          modes accepted)
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    effectStatement, environment12, target, receipt14, effect, node,
    StructuredC.a] using
    effect_rewriteAt_exact_of_evaluate coldHandler
      (call setCompileResultDelta
        (["state", "owner", "revision", "head", "arity", "occurrence",
          "declaration_head", "inputs", "output", "remaining", "modes",
          "accepted"].map variableExpression)) rest
      (environment11 owner revision head arity declaration remaining modes
        accepted) receipt13 valueUnit
      (environment12 owner revision head arity declaration remaining modes
        accepted) receipt14 evaluated

theorem delta_effect_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement
          (effect (call setCompileResultDelta
            (["state", "owner", "revision", "head", "arity", "occurrence",
              "declaration_head", "inputs", "output", "remaining", "modes",
              "accepted"].map variableExpression))) rest)
          (environment11 owner revision head arity declaration remaining modes
            accepted) receipt13) =
      [run rest
        (environment12 owner revision head arity declaration remaining modes
          accepted) receipt14] := by
  simpa [effectStatement] using
    delta_rewrite_exact owner revision head arity declaration remaining modes
      accepted rest

theorem return_statements_append_rewrite_exact
    (continuation environment receipt : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements returnStatements continuation)
          environment receipt) =
      [run (consStatement (returnSymbol advancedOutcome)
          (StructuredC.appendStatements (statements []) continuation))
        environment receipt] := by
  simpa [returnStatements, statements, node, StructuredC.consStatement,
    StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations
      (returnSymbol advancedOutcome) (statements []) continuation environment
      receipt

theorem return_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol advancedOutcome) rest)
          (environment12 owner revision head arity declaration remaining modes
            accepted) receipt14) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol advancedOutcome])
        (environment12 owner revision head arity declaration remaining modes
          accepted) receipt14] := by
  have evaluated := evaluate_symbol_exact coldHandler advancedOutcome
    (environment12 owner revision head arity declaration remaining modes
      accepted) receipt14
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a] using
    return_rewriteAt_exact_of_evaluate coldHandler (symbol advancedOutcome)
      rest
      (environment12 owner revision head arity declaration remaining modes
        accepted) receipt14 (valueSymbol advancedOutcome)
      (environment12 owner revision head arity declaration remaining modes
        accepted) receipt14 evaluated

def haltedTarget
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol advancedOutcome])
    (environment12 owner revision head arity declaration remaining modes
      accepted) receipt14

theorem terminal_observation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    terminalControl?
        (haltedTarget owner revision head arity declaration remaining modes
          accepted) =
      some (target owner revision head arity declaration remaining modes
        accepted) := by
  simp [haltedTarget, terminalControl?, environment12, target, halted,
    StructuredC.a, lookup?, bindName, environmentBind, identifier,
    decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue,
    node, token]

theorem source_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    compileLanguageGSLT.Step
      (source owner revision head arity declaration remaining modes accepted)
      (target owner revision head arity declaration remaining modes accepted) := by
  change compileLanguageStep?
      (source owner revision head arity declaration remaining modes accepted) =
    some (target owner revision head arity declaration remaining modes accepted)
  simp [source, target, compileLanguageStep?]

theorem normalizes_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source owner revision head arity declaration remaining modes
            accepted)) =
      haltedTarget owner revision head arity declaration remaining modes
        accepted := by
  unfold normalizeFirstUsing
  simp only [normalizeFirstAt,
    phase_rewrite_exact owner revision head arity declaration remaining modes
      accepted]
  simp only [dispatcher_append_rewrite_exact owner revision head arity
    declaration remaining modes accepted]
  simp only [owner_declare_rewrite_exact owner revision head arity declaration
    remaining modes accepted]
  simp only [tail1_shape, appendConsTransition_rewriteAt_exact]
  simp only [revision_declare_rewrite_exact owner revision head arity
    declaration remaining modes accepted]
  simp only [tail2_shape, appendConsTransition_rewriteAt_exact]
  simp only [head_declare_rewrite_exact owner revision head arity declaration
    remaining modes accepted]
  simp only [tail3_shape, appendConsTransition_rewriteAt_exact]
  simp only [arity_declare_rewrite_exact owner revision head arity declaration
    remaining modes accepted]
  simp only [tail4_shape, appendConsTransition_rewriteAt_exact]
  simp only [accepted_declare_rewrite_exact owner revision head arity
    declaration remaining modes accepted]
  simp only [tail5_shape, appendConsTransition_rewriteAt_exact]
  simp only [remaining_declare_rewrite_exact owner revision head arity
    declaration remaining modes accepted]
  simp only [tail6_shape, appendConsTransition_rewriteAt_exact]
  simp only [occurrence_declare_rewrite_exact owner revision head arity
    declaration remaining modes accepted]
  simp only [tail7_shape, appendConsTransition_rewriteAt_exact]
  simp only [declarationHead_declare_rewrite_exact owner revision head arity
    declaration remaining modes accepted]
  simp only [tail8_shape, appendConsTransition_rewriteAt_exact]
  simp only [inputs_declare_rewrite_exact owner revision head arity declaration
    remaining modes accepted]
  simp only [tail9_shape, appendConsTransition_rewriteAt_exact]
  simp only [output_declare_rewrite_exact owner revision head arity declaration
    remaining modes accepted]
  simp only [tail10_shape, appendConsTransition_rewriteAt_exact]
  simp only [modes_declare_rewrite_exact owner revision head arity declaration
    remaining modes accepted]
  simp only [tail11_shape, appendConsTransition_rewriteAt_exact]
  simp only [cursor_empty_decision_rewrite_exact owner revision head arity
    declaration remaining modes accepted]
  simp only [finished_append_rewrite_exact owner revision head arity declaration
    remaining modes accepted]
  simp only [effectStatement]
  simp only [delta_effect_rewrite_exact owner revision head arity declaration
    remaining modes accepted]
  simp only [return_statements_append_rewrite_exact]
  simp only [return_rewrite_exact owner revision head arity declaration
    remaining modes accepted]
  simp only [halted_rewriteAt_empty]
  rfl

abbrev run
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (source owner revision head arity declaration remaining modes
          accepted)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (source owner revision head arity declaration remaining modes accepted))

theorem run_endpoint_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    (run owner revision head arity declaration remaining modes accepted).endpoint =
      haltedTarget owner revision head arity declaration remaining modes
        accepted := by
  calc
    _ = normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source owner revision head arity declaration remaining modes
            accepted)) :=
      (run owner revision head arity declaration remaining modes
        accepted).endpoint_eq
    _ = _ := normalizes_exact owner revision head arity declaration remaining
      modes accepted

theorem run_observation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    terminalControl?
        (run owner revision head arity declaration remaining modes
          accepted).endpoint =
      some (target owner revision head arity declaration remaining modes
        accepted) := by
  rw [run_endpoint_exact owner revision head arity declaration remaining modes
    accepted]
  exact terminal_observation_exact owner revision head arity declaration
    remaining modes accepted

theorem run_path_bounded
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    (run owner revision head arity declaration remaining modes
      accepted).path.length ≤ 64 :=
  (run owner revision head arity declaration remaining modes
    accepted).length_le

theorem run_path_nonempty
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    0 < (run owner revision head arity declaration remaining modes
      accepted).path.length := by
  apply (run owner revision head arity declaration remaining modes
    accepted).nonempty_of_reduct
  · decide
  · rw [phase_rewrite_exact owner revision head arity declaration remaining
      modes accepted]
    simp

theorem step_realization
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    ∃ endpoint : Pattern,
      ∃ path : ExecutionPath coldGSLT
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source owner revision head arity declaration remaining modes
              accepted)) endpoint,
      terminalControl? endpoint =
          some (target owner revision head arity declaration remaining modes
            accepted) ∧
        0 < path.length ∧ path.length ≤ 64 := by
  let execution := run owner revision head arity declaration remaining modes
    accepted
  refine ⟨execution.endpoint, execution.path, ?_, ?_, ?_⟩
  · exact run_observation_exact owner revision head arity declaration remaining
      modes accepted
  · exact run_path_nonempty owner revision head arity declaration remaining
      modes accepted
  · exact run_path_bounded owner revision head arity declaration remaining
      modes accepted

theorem normalized_observation_iff
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source owner revision head arity declaration remaining modes
              accepted))) = some observed ↔
      observed = target owner revision head arity declaration remaining modes
        accepted := by
  rw [normalizes_exact owner revision head arity declaration remaining modes
    accepted]
  have observedExact := terminal_observation_exact owner revision head arity
    declaration remaining modes accepted
  rw [observedExact]
  simp [eq_comm]

theorem wrong_target_rejected
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (observed : CompileLanguageControl)
    (wrong : observed ≠ target owner revision head arity declaration remaining
      modes accepted) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source owner revision head arity declaration remaining modes
              accepted))) ≠ some observed := by
  intro invented
  exact wrong ((normalized_observation_iff owner revision head arity declaration
    remaining modes accepted observed).mp invented)

#print axioms source_step
#print axioms normalizes_exact
#print axioms run_endpoint_exact
#print axioms run_observation_exact
#print axioms run_path_bounded
#print axioms run_path_nonempty
#print axioms step_realization
#print axioms normalized_observation_iff
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCArgumentsFinishedSimulation
