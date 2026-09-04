import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOneStepSimulation

/-!
# Generated StructuredC realization of the cold skip-head transition

This module proves the second universal cold-compiler family.  An arbitrary
nonempty running state is projected through the generated dispatcher.  The
authored declaration-head disequality is evaluated from its two visible
operands, and the exact seven-field successor is constructed by the generated
delta.  All target edges are rewrites of `StructuredC.language`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSkipHeadSimulation

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

def skipHeadSource
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  .running owner revision head arity (declaration :: remaining) accepted

def skipHeadTarget
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    CompileLanguageControl :=
  .running owner revision head arity remaining accepted

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

def environment0
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  initialEnvironment
    (skipHeadSource owner revision head arity declaration remaining accepted)

def environment1
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  bindName "owner" (ownerValue owner)
    (environment0 owner revision head arity declaration remaining accepted)

def environment2
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  bindName "revision" (revisionValue revision)
    (environment1 owner revision head arity declaration remaining accepted)

def environment3
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  bindName "head" (headValue head)
    (environment2 owner revision head arity declaration remaining accepted)

def environment4
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  bindName "arity" (arityValue arity)
    (environment3 owner revision head arity declaration remaining accepted)

def environment5
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  bindName "accepted" (acceptedValue accepted)
    (environment4 owner revision head arity declaration remaining accepted)

def environment6
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  bindName "remaining" (remainingValue remaining)
    (environment5 owner revision head arity declaration remaining accepted)

def environment7
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  bindName "occurrence" (occurrenceValue declaration)
    (environment6 owner revision head arity declaration remaining accepted)

def environment8
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  bindName "declaration_head" (declarationHeadValue declaration)
    (environment7 owner revision head arity declaration remaining accepted)

def environment9
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  bindName "inputs" (inputsValue declaration)
    (environment8 owner revision head arity declaration remaining accepted)

def environment10
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  bindName "output" (outputValue declaration)
    (environment9 owner revision head arity declaration remaining accepted)

def environment11
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  bindName "state" (stateValue
      (skipHeadTarget owner revision head arity remaining accepted))
    (environment10 owner revision head arity declaration remaining accepted)

def receipt0 : Pattern := readyReceipt
def receipt1 : Pattern := externalReceipt compilePhaseQuery receipt0
def receipt2 : Pattern := externalReceipt ownerProjection receipt1
def receipt3 : Pattern := externalReceipt revisionProjection receipt2
def receipt4 : Pattern := externalReceipt headProjection receipt3
def receipt5 : Pattern := externalReceipt arityProjection receipt4
def receipt6 : Pattern := externalReceipt acceptedProjection receipt5
def receipt7 : Pattern := externalReceipt declarationsAreEmptyQuery receipt6
def receipt8 : Pattern := externalReceipt remainingProjection receipt7
def receipt9 : Pattern := externalReceipt occurrenceProjection receipt8
def receipt10 : Pattern := externalReceipt declarationHeadProjection receipt9
def receipt11 : Pattern := externalReceipt inputsProjection receipt10
def receipt12 : Pattern := externalReceipt outputProjection receipt11
def receipt13 : Pattern := externalReceipt nameNotEqualQuery receipt12
def receipt14 : Pattern := externalReceipt setCompileRunningDelta receipt13

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
  bindProjection "occurrence" "CettaPeTTaCallGuardNatV1"
    occurrenceProjection
def declarationHeadStatement : Pattern :=
  bindProjection "declaration_head" "CettaPeTTaCallGuardNameV1"
    declarationHeadProjection
def inputsStatement : Pattern :=
  bindProjection "inputs" "CettaPeTTaCallGuardTermsV1" inputsProjection
def outputStatement : Pattern :=
  bindProjection "output" "CettaPeTTaCallGuardTermV1" outputProjection

def commonTail1 : Pattern := statements [revisionStatement, headStatement,
  arityStatement, acceptedStatement, generatedRunningDecision]
def commonTail2 : Pattern := statements [headStatement, arityStatement,
  acceptedStatement, generatedRunningDecision]
def commonTail3 : Pattern := statements [arityStatement, acceptedStatement,
  generatedRunningDecision]
def commonTail4 : Pattern := statements [acceptedStatement,
  generatedRunningDecision]
def commonTail5 : Pattern := statements [generatedRunningDecision]

def declarationTail5 : Pattern :=
  consStatement skipHeadDecision generatedRunningAfterSkipHead
def declarationTail4 : Pattern := consStatement outputStatement declarationTail5
def declarationTail3 : Pattern := consStatement inputsStatement declarationTail4
def declarationTail2 : Pattern :=
  consStatement declarationHeadStatement declarationTail3
def declarationTail1 : Pattern :=
  consStatement occurrenceStatement declarationTail2

theorem generated_running_dispatcher_spine :
    generatedRunningDispatcher = consStatement ownerStatement commonTail1 := by
  rw [generatedRunningDispatcher_shape]
  rfl

theorem generated_running_fallback_spine :
    generatedRunningFallback =
      consStatement remainingStatement declarationTail1 := by
  rfl

theorem source_lookup0
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    lookup? (environment0 owner revision head arity declaration remaining
        accepted) (identifier "state") =
      some (stateValue
        (skipHeadSource owner revision head arity declaration remaining
          accepted)) := by
  simp [environment0, initialEnvironment, lookup?, bindName, environmentBind,
    identifier, node, token]

theorem source_lookup5
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    lookup? (environment5 owner revision head arity declaration remaining
        accepted) (identifier "state") =
      some (stateValue
        (skipHeadSource owner revision head arity declaration remaining
          accepted)) := by
  simp [environment5, environment4, environment3, environment2, environment1,
    environment0, initialEnvironment, lookup?, bindName, environmentBind,
    identifier, node, token]

theorem source_lookup10
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    lookup? (environment10 owner revision head arity declaration remaining
        accepted) (identifier "state") =
      some (stateValue
        (skipHeadSource owner revision head arity declaration remaining
          accepted)) := by
  simp [environment10, environment9, environment8, environment7, environment6,
    environment5, environment4, environment3, environment2, environment1,
    environment0, initialEnvironment, lookup?, bindName, environmentBind,
    identifier, node, token]

theorem operands_lookup10
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    List.Forall₂
      (fun slot value =>
        lookup? (environment10 owner revision head arity declaration remaining
          accepted) (identifier slot) = some value)
      ["state", "owner", "revision", "head", "arity", "remaining",
        "accepted"]
      [ stateValue
          (skipHeadSource owner revision head arity declaration remaining
            accepted)
      , ownerValue owner, revisionValue revision, headValue head,
        arityValue arity, remainingValue remaining, acceptedValue accepted ] := by
  simp [environment10, environment9, environment8, environment7, environment6,
    environment5, environment4, environment3, environment2, environment1,
    environment0, initialEnvironment, ownerValue, revisionValue, headValue,
    arityValue, remainingValue, acceptedValue, lookup?, bindName,
    environmentBind, environmentEmpty, identifier, node, token]

theorem guard_operands_lookup10
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    List.Forall₂
      (fun slot value =>
        lookup? (environment10 owner revision head arity declaration remaining
          accepted) (identifier slot) = some value)
      ["declaration_head", "head"]
      [declarationHeadValue declaration, headValue head] := by
  simp [environment10, environment9, environment8, environment7, environment6,
    environment5, environment4, environment3, environment2, environment1,
    environment0, initialEnvironment, declarationHeadValue, headValue,
    lookup?, bindName, environmentBind, environmentEmpty, identifier, node,
    token]

theorem phase_selection_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    selectCase?
        (phaseValue
          (skipHeadSource owner revision head arity declaration remaining
            accepted)) generatedFaultBody generatedPhaseCases =
      some generatedRunningDispatcher := by
  rfl

theorem phase_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (skipHeadSource owner revision head arity declaration remaining
            accepted)) =
      [run (StructuredC.appendStatements generatedRunningDispatcher
          (statements []))
        (environment0 owner revision head arity declaration remaining accepted)
        receipt1] := by
  simpa [coldRelations, environment0, receipt1, receipt0,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl]
    using phase_switch_rewrite_exact
      (skipHeadSource owner revision head arity declaration remaining accepted)
      generatedRunningDispatcher
      (environment0 owner revision head arity declaration remaining accepted)
      receipt0
      (source_lookup0 owner revision head arity declaration remaining accepted)
      (phase_selection_exact owner revision head arity declaration remaining
        accepted)

theorem dispatcher_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedRunningDispatcher
          (statements []))
          (environment0 owner revision head arity declaration remaining
            accepted) receipt1) =
      [run (consStatement ownerStatement
          (StructuredC.appendStatements commonTail1 (statements [])))
        (environment0 owner revision head arity declaration remaining accepted)
        receipt1] := by
  rw [generated_running_dispatcher_spine]
  exact appendConsTransition_rewriteAt_exact coldRelations ownerStatement
    commonTail1 (statements [])
    (environment0 owner revision head arity declaration remaining accepted)
    receipt1

theorem owner_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement ownerStatement rest)
          (environment0 owner revision head arity declaration remaining
            accepted) receipt1) =
      [run rest
        (environment1 owner revision head arity declaration remaining accepted)
        receipt2] := by
  simpa [coldRelations, CommonProjection.externalName, ownerStatement,
    bindProjection, stateArgument, environment1, ownerValue, receipt2,
    skipHeadSource] using
    common_projection_declare_rewrite_exact .owner "owner"
      "CettaPeTTaCallGuardOwnerV1"
      (skipHeadSource owner revision head arity declaration remaining accepted)
      (ownerValue owner) rest
      (environment0 owner revision head arity declaration remaining accepted)
      receipt1 (by rfl)
      (source_lookup0 owner revision head arity declaration remaining accepted)

theorem revision_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement revisionStatement rest)
          (environment1 owner revision head arity declaration remaining
            accepted) receipt2) =
      [run rest
        (environment2 owner revision head arity declaration remaining accepted)
        receipt3] := by
  simpa [coldRelations, CommonProjection.externalName, revisionStatement,
    bindProjection, stateArgument, environment2, revisionValue, receipt3,
    skipHeadSource] using
    common_projection_declare_rewrite_exact .revision "revision"
      "CettaPeTTaCallGuardNatV1"
      (skipHeadSource owner revision head arity declaration remaining accepted)
      (revisionValue revision) rest
      (environment1 owner revision head arity declaration remaining accepted)
      receipt2 (by rfl)
      (by
        simp [environment1, environment0, initialEnvironment, lookup?,
          bindName, environmentBind, identifier, node, token])

theorem head_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement headStatement rest)
          (environment2 owner revision head arity declaration remaining
            accepted) receipt3) =
      [run rest
        (environment3 owner revision head arity declaration remaining accepted)
        receipt4] := by
  simpa [coldRelations, CommonProjection.externalName, headStatement,
    bindProjection, stateArgument, environment3, headValue, receipt4,
    skipHeadSource] using
    common_projection_declare_rewrite_exact .head "head"
      "CettaPeTTaCallGuardNameV1"
      (skipHeadSource owner revision head arity declaration remaining accepted)
      (headValue head) rest
      (environment2 owner revision head arity declaration remaining accepted)
      receipt3 (by rfl)
      (by
        simp [environment2, environment1, environment0, initialEnvironment,
          lookup?, bindName, environmentBind, identifier, node, token])

theorem arity_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement arityStatement rest)
          (environment3 owner revision head arity declaration remaining
            accepted) receipt4) =
      [run rest
        (environment4 owner revision head arity declaration remaining accepted)
        receipt5] := by
  simpa [coldRelations, CommonProjection.externalName, arityStatement,
    bindProjection, stateArgument, environment4, arityValue, receipt5,
    skipHeadSource] using
    common_projection_declare_rewrite_exact .arity "arity"
      "CettaPeTTaCallGuardNatV1"
      (skipHeadSource owner revision head arity declaration remaining accepted)
      (arityValue arity) rest
      (environment3 owner revision head arity declaration remaining accepted)
      receipt4 (by rfl)
      (by
        simp [environment3, environment2, environment1, environment0,
          initialEnvironment, lookup?, bindName, environmentBind, identifier,
          node, token])

theorem accepted_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement acceptedStatement rest)
          (environment4 owner revision head arity declaration remaining
            accepted) receipt5) =
      [run rest
        (environment5 owner revision head arity declaration remaining accepted)
        receipt6] := by
  simpa [coldRelations, CommonProjection.externalName, acceptedStatement,
    bindProjection, stateArgument, environment5, acceptedValue, receipt6,
    skipHeadSource] using
    common_projection_declare_rewrite_exact .accepted "accepted"
      "CettaPeTTaCallGuardPlansV1"
      (skipHeadSource owner revision head arity declaration remaining accepted)
      (acceptedValue accepted) rest
      (environment4 owner revision head arity declaration remaining accepted)
      receipt5 (by rfl)
      (by
        simp [environment4, environment3, environment2, environment1,
          environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem commonTail1_shape :
    commonTail1 = consStatement revisionStatement commonTail2 := by rfl
theorem commonTail2_shape :
    commonTail2 = consStatement headStatement commonTail3 := by rfl
theorem commonTail3_shape :
    commonTail3 = consStatement arityStatement commonTail4 := by rfl
theorem commonTail4_shape :
    commonTail4 = consStatement acceptedStatement commonTail5 := by rfl
theorem commonTail5_shape :
    commonTail5 = consStatement generatedRunningDecision (statements []) := by
  rfl

theorem running_decision_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedRunningDecision rest)
          (environment5 owner revision head arity declaration remaining
            accepted) receipt6) =
      [run (StructuredC.appendStatements generatedRunningFallback rest)
        (environment5 owner revision head arity declaration remaining accepted)
        receipt7] := by
  have evaluated := declarations_nonempty_evaluation_exact owner revision head
    arity declaration remaining accepted
    (environment5 owner revision head arity declaration remaining accepted)
    receipt6
    (source_lookup5 owner revision head arity declaration remaining accepted)
  have selected :
      selectBranch? falseValue finishBody generatedRunningFallback =
        some generatedRunningFallback := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedRunningDecision, stateArgument, ifThenElse, node, StructuredC.a,
    receipt7] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call declarationsAreEmptyQuery [variableExpression "state"])
      finishBody generatedRunningFallback rest
      (environment5 owner revision head arity declaration remaining accepted)
      receipt6 falseValue
      (environment5 owner revision head arity declaration remaining accepted)
      receipt7 generatedRunningFallback evaluated selected

theorem fallback_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedRunningFallback
          continuation)
          (environment5 owner revision head arity declaration remaining
            accepted) receipt7) =
      [run (consStatement remainingStatement
          (StructuredC.appendStatements declarationTail1 continuation))
        (environment5 owner revision head arity declaration remaining accepted)
        receipt7] := by
  rw [generated_running_fallback_spine]
  exact appendConsTransition_rewriteAt_exact coldRelations remainingStatement
    declarationTail1 continuation
    (environment5 owner revision head arity declaration remaining accepted)
    receipt7

theorem remaining_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement remainingStatement rest)
          (environment5 owner revision head arity declaration remaining
            accepted) receipt7) =
      [run rest
        (environment6 owner revision head arity declaration remaining accepted)
        receipt8] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    remainingStatement, bindProjection, stateArgument, environment6,
    remainingValue, receipt8, skipHeadSource] using
    declaration_projection_declare_rewrite_exact .remaining "remaining"
      "CettaPeTTaCallGuardDeclarationsV1"
      (skipHeadSource owner revision head arity declaration remaining accepted)
      (remainingValue remaining) rest
      (environment5 owner revision head arity declaration remaining accepted)
      receipt7 (by rfl)
      (source_lookup5 owner revision head arity declaration remaining accepted)

theorem occurrence_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement occurrenceStatement rest)
          (environment6 owner revision head arity declaration remaining
            accepted) receipt8) =
      [run rest
        (environment7 owner revision head arity declaration remaining accepted)
        receipt9] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    occurrenceStatement, bindProjection, stateArgument, environment7,
    occurrenceValue, receipt9, skipHeadSource] using
    declaration_projection_declare_rewrite_exact .occurrence "occurrence"
      "CettaPeTTaCallGuardNatV1"
      (skipHeadSource owner revision head arity declaration remaining accepted)
      (occurrenceValue declaration) rest
      (environment6 owner revision head arity declaration remaining accepted)
      receipt8 (by rfl)
      (by
        simp [environment6, environment5, environment4, environment3,
          environment2, environment1, environment0, initialEnvironment,
          lookup?, bindName, environmentBind, identifier, node, token])

theorem declarationHead_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement declarationHeadStatement rest)
          (environment7 owner revision head arity declaration remaining
            accepted) receipt9) =
      [run rest
        (environment8 owner revision head arity declaration remaining accepted)
        receipt10] := by
  simpa [coldRelations, DeclarationProjection.externalName,
    declarationHeadStatement, bindProjection, stateArgument, environment8,
    declarationHeadValue, receipt10, skipHeadSource] using
    declaration_projection_declare_rewrite_exact .head "declaration_head"
      "CettaPeTTaCallGuardNameV1"
      (skipHeadSource owner revision head arity declaration remaining accepted)
      (declarationHeadValue declaration) rest
      (environment7 owner revision head arity declaration remaining accepted)
      receipt9 (by rfl)
      (by
        simp [environment7, environment6, environment5, environment4,
          environment3, environment2, environment1, environment0,
          initialEnvironment, lookup?, bindName, environmentBind, identifier,
          node, token])

theorem inputs_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement inputsStatement rest)
          (environment8 owner revision head arity declaration remaining
            accepted) receipt10) =
      [run rest
        (environment9 owner revision head arity declaration remaining accepted)
        receipt11] := by
  simpa [coldRelations, DeclarationProjection.externalName, inputsStatement,
    bindProjection, stateArgument, environment9, inputsValue, receipt11,
    skipHeadSource] using
    declaration_projection_declare_rewrite_exact .inputs "inputs"
      "CettaPeTTaCallGuardTermsV1"
      (skipHeadSource owner revision head arity declaration remaining accepted)
      (inputsValue declaration) rest
      (environment8 owner revision head arity declaration remaining accepted)
      receipt10 (by rfl)
      (by
        simp [environment8, environment7, environment6, environment5,
          environment4, environment3, environment2, environment1,
          environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem output_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement outputStatement rest)
          (environment9 owner revision head arity declaration remaining
            accepted) receipt11) =
      [run rest
        (environment10 owner revision head arity declaration remaining accepted)
        receipt12] := by
  simpa [coldRelations, DeclarationProjection.externalName, outputStatement,
    bindProjection, stateArgument, environment10, outputValue, receipt12,
    skipHeadSource] using
    declaration_projection_declare_rewrite_exact .output "output"
      "CettaPeTTaCallGuardTermV1"
      (skipHeadSource owner revision head arity declaration remaining accepted)
      (outputValue declaration) rest
      (environment9 owner revision head arity declaration remaining accepted)
      receipt11 (by rfl)
      (by
        simp [environment9, environment8, environment7, environment6,
          environment5, environment4, environment3, environment2,
          environment1, environment0, initialEnvironment, lookup?, bindName,
          environmentBind, identifier, node, token])

theorem declarationTail1_shape :
    declarationTail1 = consStatement occurrenceStatement declarationTail2 := by
  rfl
theorem declarationTail2_shape :
    declarationTail2 =
      consStatement declarationHeadStatement declarationTail3 := by rfl
theorem declarationTail3_shape :
    declarationTail3 = consStatement inputsStatement declarationTail4 := by rfl
theorem declarationTail4_shape :
    declarationTail4 = consStatement outputStatement declarationTail5 := by rfl
theorem declarationTail5_shape :
    declarationTail5 =
      consStatement skipHeadDecision generatedRunningAfterSkipHead := by rfl

theorem guard_decision_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (different : declaration.function ≠ head)
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement skipHeadDecision rest)
          (environment10 owner revision head arity declaration remaining
            accepted) receipt12) =
      [run (StructuredC.appendStatements skipHeadSuccess rest)
        (environment10 owner revision head arity declaration remaining accepted)
        receipt13] := by
  have evaluated := nameNotEqual_evaluation_exact declaration.function head
    (environment10 owner revision head arity declaration remaining accepted)
    receipt12 different
    (by
      simpa [declarationHeadValue, headValue] using
        guard_operands_lookup10 owner revision head arity declaration remaining
          accepted)
  have selected :
      selectBranch? trueValue skipHeadSuccess (statements []) =
        some skipHeadSuccess := by
    simp [selectBranch?]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    skipHeadDecision, skipHeadCondition, ifThenElse, node, StructuredC.a,
    receipt13] using
    if_rewriteAt_exact_of_evaluate coldHandler skipHeadCondition
      skipHeadSuccess (statements []) rest
      (environment10 owner revision head arity declaration remaining accepted)
      receipt12 trueValue
      (environment10 owner revision head arity declaration remaining accepted)
      receipt13 skipHeadSuccess evaluated selected

def effectStatement : Pattern :=
  effect (call setCompileRunningDelta
    (["state", "owner", "revision", "head", "arity", "remaining",
      "accepted"].map variableExpression))

def returnStatements : Pattern :=
  statements [returnSymbol advancedOutcome]

theorem success_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements skipHeadSuccess continuation)
          (environment10 owner revision head arity declaration remaining
            accepted) receipt13) =
      [run (consStatement effectStatement
          (StructuredC.appendStatements returnStatements continuation))
        (environment10 owner revision head arity declaration remaining accepted)
        receipt13] := by
  rw [skipHeadSuccess_shape]
  simpa [effectStatement, returnStatements, statements, node,
    StructuredC.consStatement, StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations effectStatement
      returnStatements continuation
      (environment10 owner revision head arity declaration remaining accepted)
      receipt13

theorem delta_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (different : declaration.function ≠ head)
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement effectStatement rest)
          (environment10 owner revision head arity declaration remaining
            accepted) receipt13) =
      [run rest
        (environment11 owner revision head arity declaration remaining accepted)
        receipt14] := by
  have evaluated := skipHead_delta_evaluation_exact owner revision head arity
    declaration remaining accepted
    (environment10 owner revision head arity declaration remaining accepted)
    receipt13 different
    (source_lookup10 owner revision head arity declaration remaining accepted)
    (by
      simpa [ownerValue, revisionValue, headValue, arityValue, remainingValue,
        acceptedValue, skipHeadSource] using
        operands_lookup10 owner revision head arity declaration remaining
          accepted)
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    effectStatement, environment11, receipt14, effect, node, StructuredC.a]
    using effect_rewriteAt_exact_of_evaluate coldHandler
      (call setCompileRunningDelta
        (["state", "owner", "revision", "head", "arity", "remaining",
          "accepted"].map variableExpression)) rest
      (environment10 owner revision head arity declaration remaining accepted)
      receipt13 valueUnit
      (environment11 owner revision head arity declaration remaining accepted)
      receipt14 evaluated

theorem delta_effect_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (different : declaration.function ≠ head)
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement
          (effect (call setCompileRunningDelta
            (["state", "owner", "revision", "head", "arity", "remaining",
              "accepted"].map variableExpression))) rest)
          (environment10 owner revision head arity declaration remaining
            accepted) receipt13) =
      [run rest
        (environment11 owner revision head arity declaration remaining accepted)
        receipt14] := by
  simpa [effectStatement] using
    delta_rewrite_exact owner revision head arity declaration remaining accepted
      different rest

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
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol advancedOutcome) rest)
          (environment11 owner revision head arity declaration remaining
            accepted) receipt14) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol advancedOutcome])
        (environment11 owner revision head arity declaration remaining accepted)
        receipt14] := by
  have evaluated := evaluate_symbol_exact coldHandler advancedOutcome
    (environment11 owner revision head arity declaration remaining accepted)
    receipt14
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a] using
    return_rewriteAt_exact_of_evaluate coldHandler (symbol advancedOutcome)
      rest
      (environment11 owner revision head arity declaration remaining accepted)
      receipt14 (valueSymbol advancedOutcome)
      (environment11 owner revision head arity declaration remaining accepted)
      receipt14 evaluated

def haltedTarget
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol advancedOutcome])
    (environment11 owner revision head arity declaration remaining accepted)
    receipt14

theorem terminal_observation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    terminalControl?
        (haltedTarget owner revision head arity declaration remaining
          accepted) =
      some (skipHeadTarget owner revision head arity remaining accepted) := by
  simp [haltedTarget, terminalControl?, environment11, skipHeadTarget, halted,
    StructuredC.a, lookup?, bindName, environmentBind, identifier,
    decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue,
    node, token]

theorem source_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (different : declaration.function ≠ head) :
    compileLanguageGSLT.Step
      (skipHeadSource owner revision head arity declaration remaining accepted)
      (skipHeadTarget owner revision head arity remaining accepted) := by
  change compileLanguageStep?
      (skipHeadSource owner revision head arity declaration remaining accepted) =
    some (skipHeadTarget owner revision head arity remaining accepted)
  simp [skipHeadSource, skipHeadTarget, compileLanguageStep?, Relevant,
    different]

/-- The generated skip-head program normalizes through the authored switch,
append, declaration, guard, effect, and return rules to the exact source
successor. -/
theorem normalizes_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (different : declaration.function ≠ head) :
    normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (skipHeadSource owner revision head arity declaration remaining
            accepted)) =
      haltedTarget owner revision head arity declaration remaining accepted := by
  unfold normalizeFirstUsing
  simp only [normalizeFirstAt,
    phase_rewrite_exact owner revision head arity declaration remaining
      accepted]
  simp only [
    dispatcher_append_rewrite_exact owner revision head arity declaration
      remaining accepted]
  simp only [
    owner_declare_rewrite_exact owner revision head arity declaration remaining
      accepted]
  simp only [commonTail1_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    revision_declare_rewrite_exact owner revision head arity declaration
      remaining accepted]
  simp only [commonTail2_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    head_declare_rewrite_exact owner revision head arity declaration remaining
      accepted]
  simp only [commonTail3_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    arity_declare_rewrite_exact owner revision head arity declaration remaining
      accepted]
  simp only [commonTail4_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    accepted_declare_rewrite_exact owner revision head arity declaration
      remaining accepted]
  simp only [commonTail5_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    running_decision_rewrite_exact owner revision head arity declaration
      remaining accepted]
  simp only [
    fallback_append_rewrite_exact owner revision head arity declaration
      remaining accepted]
  simp only [
    remaining_declare_rewrite_exact owner revision head arity declaration
      remaining accepted]
  simp only [declarationTail1_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    occurrence_declare_rewrite_exact owner revision head arity declaration
      remaining accepted]
  simp only [declarationTail2_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    declarationHead_declare_rewrite_exact owner revision head arity declaration
      remaining accepted]
  simp only [declarationTail3_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    inputs_declare_rewrite_exact owner revision head arity declaration remaining
      accepted]
  simp only [declarationTail4_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    output_declare_rewrite_exact owner revision head arity declaration remaining
      accepted]
  simp only [declarationTail5_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    guard_decision_rewrite_exact owner revision head arity declaration remaining
      accepted different]
  simp only [
    success_append_rewrite_exact owner revision head arity declaration remaining
      accepted]
  simp only [effectStatement]
  simp only [
    delta_effect_rewrite_exact owner revision head arity declaration remaining accepted
      different]
  simp only [return_statements_append_rewrite_exact]
  simp only [
    return_rewrite_exact owner revision head arity declaration remaining
      accepted]
  simp only [halted_rewriteAt_empty]
  rfl

abbrev run
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (skipHeadSource owner revision head arity declaration remaining
          accepted)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (skipHeadSource owner revision head arity declaration remaining accepted))

theorem run_endpoint_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (different : declaration.function ≠ head) :
    (run owner revision head arity declaration remaining accepted).endpoint =
      haltedTarget owner revision head arity declaration remaining accepted := by
  calc
    _ = normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (skipHeadSource owner revision head arity declaration remaining
            accepted)) :=
      (run owner revision head arity declaration remaining accepted).endpoint_eq
    _ = _ := normalizes_exact owner revision head arity declaration remaining
      accepted different

theorem run_observation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (different : declaration.function ≠ head) :
    terminalControl?
        (run owner revision head arity declaration remaining accepted).endpoint =
      some (skipHeadTarget owner revision head arity remaining accepted) := by
  rw [run_endpoint_exact owner revision head arity declaration remaining
    accepted different]
  exact terminal_observation_exact owner revision head arity declaration
    remaining accepted

theorem run_path_bounded
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    (run owner revision head arity declaration remaining accepted).path.length ≤
      64 :=
  (run owner revision head arity declaration remaining accepted).length_le

theorem run_path_nonempty
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    0 < (run owner revision head arity declaration remaining accepted).path.length := by
  apply (run owner revision head arity declaration remaining accepted).nonempty_of_reduct
  · decide
  · rw [phase_rewrite_exact owner revision head arity declaration remaining
      accepted]
    simp

/-- Every source skip-head step owns a retained bounded nonempty path in the
actual generated StructuredC GSLT, with exactly the source target as terminal
observation. -/
theorem step_realization
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (different : declaration.function ≠ head) :
    ∃ endpoint : Pattern,
      ∃ path : ExecutionPath coldGSLT
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (skipHeadSource owner revision head arity declaration remaining
              accepted)) endpoint,
      terminalControl? endpoint =
          some (skipHeadTarget owner revision head arity remaining accepted) ∧
        0 < path.length ∧ path.length ≤ 64 := by
  let execution := run owner revision head arity declaration remaining accepted
  refine ⟨execution.endpoint, execution.path, ?_, ?_, ?_⟩
  · exact run_observation_exact owner revision head arity declaration remaining
      accepted different
  · exact run_path_nonempty owner revision head arity declaration remaining
      accepted
  · exact run_path_bounded owner revision head arity declaration remaining
      accepted

/-- Deterministic generated execution cannot invent a different observed
skip-head successor. -/
theorem normalized_observation_iff
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (different : declaration.function ≠ head)
    (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (skipHeadSource owner revision head arity declaration remaining
              accepted))) = some observed ↔
      observed = skipHeadTarget owner revision head arity remaining accepted := by
  rw [normalizes_exact owner revision head arity declaration remaining accepted
    different]
  have observedExact := terminal_observation_exact owner revision head arity
    declaration remaining accepted
  rw [observedExact]
  simp [eq_comm]

theorem wrong_target_rejected
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (different : declaration.function ≠ head)
    (observed : CompileLanguageControl)
    (wrong : observed ≠ skipHeadTarget owner revision head arity remaining
      accepted) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (skipHeadSource owner revision head arity declaration remaining
              accepted))) ≠ some observed := by
  intro invented
  exact wrong ((normalized_observation_iff owner revision head arity declaration
    remaining accepted different observed).mp invented)

#print axioms source_step
#print axioms normalizes_exact
#print axioms run_endpoint_exact
#print axioms run_observation_exact
#print axioms run_path_bounded
#print axioms run_path_nonempty
#print axioms step_realization
#print axioms normalized_observation_iff
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSkipHeadSimulation
