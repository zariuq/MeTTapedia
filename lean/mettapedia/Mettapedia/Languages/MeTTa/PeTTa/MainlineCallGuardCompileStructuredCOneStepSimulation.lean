import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics
import Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission

/-!
# Source-step realization by generated StructuredC execution

This module begins the universal one-step simulation for the cold PeTTa
call-guard compiler.  The first family is `finish`: arbitrary source fields
are projected by the generated dispatcher, checked by its visible branch,
and supplied to the generated state delta.  Every target edge is an authored
`StructuredC.language` rewrite; no transition table or expected target is an
input to execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOneStepSimulation

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
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCDispatcher
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics

abbrev coldRelations : RelationEnv :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations

abbrev coldHandler : ExternalHandler :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.handler

abbrev coldLaws : ReductionRespectsEquationsUsing coldRelations
    StructuredC.language :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.reductionLaws

abbrev coldGSLT : GSLT :=
  languageGSLTUsing coldRelations StructuredC.language coldLaws

def finishSource
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  .running owner revision head arity [] accepted

def finishTarget
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  .halted (.compiled ⟨owner, revision, head, arity, accepted⟩)

def finishOwnerValue (owner : SpaceOwner) : Pattern :=
  abiValue (encodeOwner owner)

def finishRevisionValue (revision : Nat) : Pattern :=
  abiValue (encodeNat revision)

def finishHeadValue (head : String) : Pattern :=
  abiValue (encodeName head)

def finishArityValue (arity : Nat) : Pattern :=
  abiValue (encodeNat arity)

def finishAcceptedValue (accepted : List GuardPlan) : Pattern :=
  abiValue (encodePlans accepted)

def finishEnvironment0
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) : Pattern :=
  initialEnvironment (finishSource owner revision head arity accepted)

def finishEnvironment1
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) : Pattern :=
  bindName "owner" (finishOwnerValue owner)
    (finishEnvironment0 owner revision head arity accepted)

def finishEnvironment2
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) : Pattern :=
  bindName "revision" (finishRevisionValue revision)
    (finishEnvironment1 owner revision head arity accepted)

def finishEnvironment3
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) : Pattern :=
  bindName "head" (finishHeadValue head)
    (finishEnvironment2 owner revision head arity accepted)

def finishEnvironment4
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) : Pattern :=
  bindName "arity" (finishArityValue arity)
    (finishEnvironment3 owner revision head arity accepted)

def finishEnvironment5
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) : Pattern :=
  bindName "accepted" (finishAcceptedValue accepted)
    (finishEnvironment4 owner revision head arity accepted)

def finishEnvironment6
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) : Pattern :=
  bindName "state"
    (stateValue (finishTarget owner revision head arity accepted))
    (finishEnvironment5 owner revision head arity accepted)

def finishReceipt0 : Pattern := readyReceipt
def finishReceipt1 : Pattern := externalReceipt compilePhaseQuery finishReceipt0
def finishReceipt2 : Pattern := externalReceipt ownerProjection finishReceipt1
def finishReceipt3 : Pattern := externalReceipt revisionProjection finishReceipt2
def finishReceipt4 : Pattern := externalReceipt headProjection finishReceipt3
def finishReceipt5 : Pattern := externalReceipt arityProjection finishReceipt4
def finishReceipt6 : Pattern := externalReceipt acceptedProjection finishReceipt5
def finishReceipt7 : Pattern :=
  externalReceipt declarationsAreEmptyQuery finishReceipt6
def finishReceipt8 : Pattern :=
  externalReceipt setCompiledFamilyDelta finishReceipt7

def finishOwnerStatement : Pattern :=
  bindProjection "owner" "CettaPeTTaCallGuardOwnerV1" ownerProjection

def finishRevisionStatement : Pattern :=
  bindProjection "revision" "CettaPeTTaCallGuardNatV1" revisionProjection

def finishHeadStatement : Pattern :=
  bindProjection "head" "CettaPeTTaCallGuardNameV1" headProjection

def finishArityStatement : Pattern :=
  bindProjection "arity" "CettaPeTTaCallGuardNatV1" arityProjection

def finishAcceptedStatement : Pattern :=
  bindProjection "accepted" "CettaPeTTaCallGuardPlansV1" acceptedProjection

def finishTail1 : Pattern := statements [finishRevisionStatement,
  finishHeadStatement, finishArityStatement, finishAcceptedStatement,
  generatedRunningDecision]

def finishTail2 : Pattern := statements [finishHeadStatement,
  finishArityStatement, finishAcceptedStatement, generatedRunningDecision]

def finishTail3 : Pattern := statements [finishArityStatement,
  finishAcceptedStatement, generatedRunningDecision]

def finishTail4 : Pattern :=
  statements [finishAcceptedStatement, generatedRunningDecision]

def finishTail5 : Pattern := statements [generatedRunningDecision]

theorem generated_running_dispatcher_finish_spine :
    generatedRunningDispatcher =
      consStatement finishOwnerStatement finishTail1 := by
  rw [generatedRunningDispatcher_shape]
  rfl

theorem finish_phase_selection_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    selectCase?
        (phaseValue (finishSource owner revision head arity accepted))
        generatedFaultBody generatedPhaseCases =
      some generatedRunningDispatcher := by
  rfl

theorem finish_phase_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (finishSource owner revision head arity accepted)) =
      [run (StructuredC.appendStatements generatedRunningDispatcher
          (statements []))
        (finishEnvironment0 owner revision head arity accepted)
        finishReceipt1] := by
  simpa [coldRelations, finishSource, finishEnvironment0, finishReceipt1,
    finishReceipt0,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl]
    using phase_switch_rewrite_exact
      (finishSource owner revision head arity accepted)
      generatedRunningDispatcher
      (finishEnvironment0 owner revision head arity accepted) finishReceipt0
      (by
        simp [finishEnvironment0, initialEnvironment, lookup?, bindName,
          environmentBind,
          Mettapedia.GSLT.LanguageDef.StructuredC.Builder.identifier,
          Mettapedia.GSLT.LanguageDef.StructuredC.Builder.node,
          Mettapedia.GSLT.LanguageDef.StructuredC.Builder.token])
      (finish_phase_selection_exact owner revision head arity accepted)

theorem finish_dispatcher_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedRunningDispatcher
          (statements []))
          (finishEnvironment0 owner revision head arity accepted)
          finishReceipt1) =
      [run (consStatement finishOwnerStatement
          (StructuredC.appendStatements finishTail1 (statements [])))
        (finishEnvironment0 owner revision head arity accepted)
        finishReceipt1] := by
  rw [generated_running_dispatcher_finish_spine]
  exact appendConsTransition_rewriteAt_exact coldRelations
    finishOwnerStatement finishTail1 (statements [])
    (finishEnvironment0 owner revision head arity accepted) finishReceipt1

theorem finish_source_lookup0
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    lookup? (finishEnvironment0 owner revision head arity accepted)
        (identifier "state") =
      some (stateValue (finishSource owner revision head arity accepted)) := by
  simp [finishEnvironment0, initialEnvironment, lookup?, bindName,
    environmentBind,
    Mettapedia.GSLT.LanguageDef.StructuredC.Builder.identifier,
    Mettapedia.GSLT.LanguageDef.StructuredC.Builder.node,
    Mettapedia.GSLT.LanguageDef.StructuredC.Builder.token]

theorem finish_source_lookup1
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    lookup? (finishEnvironment1 owner revision head arity accepted)
        (identifier "state") =
      some (stateValue (finishSource owner revision head arity accepted)) := by
  calc
    _ = lookup? (finishEnvironment0 owner revision head arity accepted)
          (identifier "state") := by
      simpa [finishEnvironment1] using
        lookup_bindName_of_ne "owner" "state" (finishOwnerValue owner)
          (finishEnvironment0 owner revision head arity accepted) (by decide)
    _ = _ := finish_source_lookup0 owner revision head arity accepted

theorem finish_owner_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement finishOwnerStatement rest)
          (finishEnvironment0 owner revision head arity accepted)
          finishReceipt1) =
      [run rest (finishEnvironment1 owner revision head arity accepted)
        finishReceipt2] := by
  simpa [coldRelations, CommonProjection.externalName,
    finishOwnerStatement, bindProjection, stateArgument, finishEnvironment1,
    finishOwnerValue, finishReceipt2, finishSource] using
    common_projection_declare_rewrite_exact .owner "owner"
      "CettaPeTTaCallGuardOwnerV1"
      (finishSource owner revision head arity accepted)
      (finishOwnerValue owner) rest
      (finishEnvironment0 owner revision head arity accepted) finishReceipt1
      (by rfl)
      (finish_source_lookup0 owner revision head arity accepted)

theorem finish_source_lookup2
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    lookup? (finishEnvironment2 owner revision head arity accepted)
        (identifier "state") =
      some (stateValue (finishSource owner revision head arity accepted)) := by
  calc
    _ = lookup? (finishEnvironment1 owner revision head arity accepted)
          (identifier "state") := by
      simpa [finishEnvironment2] using
        lookup_bindName_of_ne "revision" "state"
          (finishRevisionValue revision)
          (finishEnvironment1 owner revision head arity accepted) (by decide)
    _ = _ := finish_source_lookup1 owner revision head arity accepted

theorem finish_revision_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement finishRevisionStatement rest)
          (finishEnvironment1 owner revision head arity accepted)
          finishReceipt2) =
      [run rest (finishEnvironment2 owner revision head arity accepted)
        finishReceipt3] := by
  simpa [coldRelations, CommonProjection.externalName,
    finishRevisionStatement, bindProjection, stateArgument,
    finishEnvironment2, finishRevisionValue, finishReceipt3, finishSource]
    using common_projection_declare_rewrite_exact .revision "revision"
      "CettaPeTTaCallGuardNatV1"
      (finishSource owner revision head arity accepted)
      (finishRevisionValue revision) rest
      (finishEnvironment1 owner revision head arity accepted) finishReceipt2
      (by rfl)
      (finish_source_lookup1 owner revision head arity accepted)

theorem finish_source_lookup3
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    lookup? (finishEnvironment3 owner revision head arity accepted)
        (identifier "state") =
      some (stateValue (finishSource owner revision head arity accepted)) := by
  calc
    _ = lookup? (finishEnvironment2 owner revision head arity accepted)
          (identifier "state") := by
      simpa [finishEnvironment3] using
        lookup_bindName_of_ne "head" "state" (finishHeadValue head)
          (finishEnvironment2 owner revision head arity accepted) (by decide)
    _ = _ := finish_source_lookup2 owner revision head arity accepted

theorem finish_head_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement finishHeadStatement rest)
          (finishEnvironment2 owner revision head arity accepted)
          finishReceipt3) =
      [run rest (finishEnvironment3 owner revision head arity accepted)
        finishReceipt4] := by
  simpa [coldRelations, CommonProjection.externalName,
    finishHeadStatement, bindProjection, stateArgument, finishEnvironment3,
    finishHeadValue, finishReceipt4, finishSource] using
    common_projection_declare_rewrite_exact .head "head"
      "CettaPeTTaCallGuardNameV1"
      (finishSource owner revision head arity accepted)
      (finishHeadValue head) rest
      (finishEnvironment2 owner revision head arity accepted) finishReceipt3
      (by rfl)
      (finish_source_lookup2 owner revision head arity accepted)

theorem finish_source_lookup4
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    lookup? (finishEnvironment4 owner revision head arity accepted)
        (identifier "state") =
      some (stateValue (finishSource owner revision head arity accepted)) := by
  calc
    _ = lookup? (finishEnvironment3 owner revision head arity accepted)
          (identifier "state") := by
      simpa [finishEnvironment4] using
        lookup_bindName_of_ne "arity" "state" (finishArityValue arity)
          (finishEnvironment3 owner revision head arity accepted) (by decide)
    _ = _ := finish_source_lookup3 owner revision head arity accepted

theorem finish_arity_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement finishArityStatement rest)
          (finishEnvironment3 owner revision head arity accepted)
          finishReceipt4) =
      [run rest (finishEnvironment4 owner revision head arity accepted)
        finishReceipt5] := by
  simpa [coldRelations, CommonProjection.externalName,
    finishArityStatement, bindProjection, stateArgument, finishEnvironment4,
    finishArityValue, finishReceipt5, finishSource] using
    common_projection_declare_rewrite_exact .arity "arity"
      "CettaPeTTaCallGuardNatV1"
      (finishSource owner revision head arity accepted)
      (finishArityValue arity) rest
      (finishEnvironment3 owner revision head arity accepted) finishReceipt4
      (by rfl)
      (finish_source_lookup3 owner revision head arity accepted)

theorem finish_accepted_declare_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement finishAcceptedStatement rest)
          (finishEnvironment4 owner revision head arity accepted)
          finishReceipt5) =
      [run rest (finishEnvironment5 owner revision head arity accepted)
        finishReceipt6] := by
  simpa [coldRelations, CommonProjection.externalName,
    finishAcceptedStatement, bindProjection, stateArgument,
    finishEnvironment5, finishAcceptedValue, finishReceipt6, finishSource]
    using common_projection_declare_rewrite_exact .accepted "accepted"
      "CettaPeTTaCallGuardPlansV1"
      (finishSource owner revision head arity accepted)
      (finishAcceptedValue accepted) rest
      (finishEnvironment4 owner revision head arity accepted) finishReceipt5
      (by rfl)
      (finish_source_lookup4 owner revision head arity accepted)

theorem finish_source_lookup5
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    lookup? (finishEnvironment5 owner revision head arity accepted)
        (identifier "state") =
      some (stateValue (finishSource owner revision head arity accepted)) := by
  simp [finishEnvironment5, finishEnvironment4, finishEnvironment3,
    finishEnvironment2, finishEnvironment1, finishEnvironment0,
    initialEnvironment, lookup?, bindName, environmentBind,
    Mettapedia.GSLT.LanguageDef.StructuredC.Builder.identifier,
    Mettapedia.GSLT.LanguageDef.StructuredC.Builder.node,
    Mettapedia.GSLT.LanguageDef.StructuredC.Builder.token]

theorem finish_operands_lookup5
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    List.Forall₂
      (fun slot value =>
        lookup? (finishEnvironment5 owner revision head arity accepted)
          (identifier slot) = some value)
      ["state", "owner", "revision", "head", "arity", "accepted"]
      [ stateValue (finishSource owner revision head arity accepted)
      , finishOwnerValue owner
      , finishRevisionValue revision
      , finishHeadValue head
      , finishArityValue arity
      , finishAcceptedValue accepted ] := by
  simp [finishEnvironment5, finishEnvironment4, finishEnvironment3,
    finishEnvironment2, finishEnvironment1, finishEnvironment0,
    initialEnvironment, finishOwnerValue, finishRevisionValue,
    finishHeadValue, finishArityValue, finishAcceptedValue, lookup?, bindName,
    environmentBind, environmentEmpty, identifier, node, token]

theorem finishTail1_shape :
    finishTail1 = consStatement finishRevisionStatement finishTail2 := by
  rfl

theorem finishTail2_shape :
    finishTail2 = consStatement finishHeadStatement finishTail3 := by
  rfl

theorem finishTail3_shape :
    finishTail3 = consStatement finishArityStatement finishTail4 := by
  rfl

theorem finishTail4_shape :
    finishTail4 = consStatement finishAcceptedStatement finishTail5 := by
  rfl

theorem finishTail5_shape :
    finishTail5 = consStatement generatedRunningDecision (statements []) := by
  rfl

theorem finish_decision_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedRunningDecision rest)
          (finishEnvironment5 owner revision head arity accepted)
          finishReceipt6) =
      [run (StructuredC.appendStatements finishBody rest)
        (finishEnvironment5 owner revision head arity accepted)
        finishReceipt7] := by
  have evaluated := finish_declarations_empty_evaluation_exact owner revision
    head arity accepted
    (finishEnvironment5 owner revision head arity accepted) finishReceipt6
    (by simpa [finishSource] using
      finish_source_lookup5 owner revision head arity accepted)
  have selected :
      selectBranch? trueValue finishBody generatedRunningFallback =
        some finishBody := by
    simp [selectBranch?]
  simpa [coldRelations, coldHandler, Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedRunningDecision, stateArgument, ifThenElse, node, StructuredC.a,
    finishReceipt7] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call declarationsAreEmptyQuery [variableExpression "state"])
      finishBody generatedRunningFallback rest
      (finishEnvironment5 owner revision head arity accepted) finishReceipt6
      trueValue (finishEnvironment5 owner revision head arity accepted)
      finishReceipt7 finishBody evaluated selected

theorem finish_delta_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement
          (effect (call setCompiledFamilyDelta
            (["state", "owner", "revision", "head", "arity", "accepted"].map
              variableExpression))) rest)
          (finishEnvironment5 owner revision head arity accepted)
          finishReceipt7) =
      [run rest (finishEnvironment6 owner revision head arity accepted)
        finishReceipt8] := by
  have evaluated := finish_delta_evaluation_exact owner revision head arity
    accepted (finishEnvironment5 owner revision head arity accepted)
    finishReceipt7
    (by simpa [finishSource] using
      finish_source_lookup5 owner revision head arity accepted)
    (by simpa [finishSource, finishOwnerValue, finishRevisionValue,
      finishHeadValue, finishArityValue, finishAcceptedValue] using
      finish_operands_lookup5 owner revision head arity accepted)
  simpa [coldRelations, coldHandler, Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    finishEnvironment6, finishTarget, finishReceipt8, effect, node,
    StructuredC.a] using
    effect_rewriteAt_exact_of_evaluate coldHandler
      (call setCompiledFamilyDelta
        (["state", "owner", "revision", "head", "arity", "accepted"].map
          variableExpression))
      rest (finishEnvironment5 owner revision head arity accepted)
      finishReceipt7 valueUnit
      (finishEnvironment6 owner revision head arity accepted) finishReceipt8
      evaluated

theorem finish_return_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol compiledOutcome) rest)
          (finishEnvironment6 owner revision head arity accepted)
          finishReceipt8) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol compiledOutcome])
        (finishEnvironment6 owner revision head arity accepted)
        finishReceipt8] := by
  have evaluated := evaluate_symbol_exact coldHandler compiledOutcome
    (finishEnvironment6 owner revision head arity accepted) finishReceipt8
  simpa [coldRelations, coldHandler, Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a]
    using return_rewriteAt_exact_of_evaluate coldHandler
      (symbol compiledOutcome) rest
      (finishEnvironment6 owner revision head arity accepted) finishReceipt8
      (valueSymbol compiledOutcome)
      (finishEnvironment6 owner revision head arity accepted) finishReceipt8
      evaluated

theorem finish_terminal_observation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    terminalControl?
        (halted (StructuredC.a "structured-c:outcome-return"
            [valueSymbol compiledOutcome])
          (finishEnvironment6 owner revision head arity accepted)
          finishReceipt8) =
      some (finishTarget owner revision head arity accepted) := by
  simp [terminalControl?, finishEnvironment6, finishTarget, halted,
    StructuredC.a, lookup?, bindName, environmentBind, identifier,
    decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue,
    Mettapedia.GSLT.LanguageDef.StructuredC.Builder.node,
    Mettapedia.GSLT.LanguageDef.StructuredC.Builder.token]

def finishEffectStatement : Pattern :=
  effect (call setCompiledFamilyDelta
    (["state", "owner", "revision", "head", "arity", "accepted"].map
      variableExpression))

def finishReturnStatements : Pattern :=
  statements [returnSymbol compiledOutcome]

theorem finish_body_append_rewrite_exact
    (continuation environment receipt : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements finishBody continuation)
          environment receipt) =
      [run (consStatement finishEffectStatement
          (StructuredC.appendStatements finishReturnStatements continuation))
        environment receipt] := by
  rw [finishBody_shape]
  simpa [finishEffectStatement, finishReturnStatements, statements, node,
    StructuredC.consStatement, StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations finishEffectStatement
      finishReturnStatements continuation environment receipt

theorem finish_return_statements_append_rewrite_exact
    (continuation environment receipt : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements finishReturnStatements continuation)
          environment receipt) =
      [run (consStatement (returnSymbol compiledOutcome)
          (StructuredC.appendStatements (statements []) continuation))
        environment receipt] := by
  simpa [finishReturnStatements, statements, node,
    StructuredC.consStatement, StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations
      (returnSymbol compiledOutcome) (statements []) continuation
      environment receipt

def finishHalted
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol compiledOutcome])
    (finishEnvironment6 owner revision head arity accepted) finishReceipt8

/-- The generated program normalizes by exactly the authored switch,
append, declaration, branch, effect, and return rules to the source finish
target.  The proof composes the structural one-step theorems; it does not
unfold the evaluator into a precomputed execution table. -/
theorem finish_normalizes_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (finishSource owner revision head arity accepted)) =
      finishHalted owner revision head arity accepted := by
  unfold normalizeFirstUsing
  simp only [normalizeFirstAt,
    finish_phase_rewrite_exact owner revision head arity accepted]
  simp only [
    finish_dispatcher_append_rewrite_exact owner revision head arity accepted]
  simp only [
    finish_owner_declare_rewrite_exact owner revision head arity accepted]
  simp only [finishTail1_shape,
    appendConsTransition_rewriteAt_exact]
  simp only [
    finish_revision_declare_rewrite_exact owner revision head arity accepted]
  simp only [finishTail2_shape,
    appendConsTransition_rewriteAt_exact]
  simp only [
    finish_head_declare_rewrite_exact owner revision head arity accepted]
  simp only [finishTail3_shape,
    appendConsTransition_rewriteAt_exact]
  simp only [
    finish_arity_declare_rewrite_exact owner revision head arity accepted]
  simp only [finishTail4_shape,
    appendConsTransition_rewriteAt_exact]
  simp only [
    finish_accepted_declare_rewrite_exact owner revision head arity accepted]
  simp only [finishTail5_shape,
    appendConsTransition_rewriteAt_exact]
  simp only [
    finish_decision_rewrite_exact owner revision head arity accepted]
  simp only [finish_body_append_rewrite_exact]
  simp only [
    finish_delta_rewrite_exact owner revision head arity accepted,
    finishEffectStatement]
  simp only [finish_return_statements_append_rewrite_exact]
  simp only [
    finish_return_rewrite_exact owner revision head arity accepted]
  simp only [halted_rewriteAt_empty]
  rfl

abbrev finishRun
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (finishSource owner revision head arity accepted)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (finishSource owner revision head arity accepted))

theorem finish_run_endpoint_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    (finishRun owner revision head arity accepted).endpoint =
      finishHalted owner revision head arity accepted := by
  calc
    _ = normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (finishSource owner revision head arity accepted)) :=
      (finishRun owner revision head arity accepted).endpoint_eq
    _ = _ := finish_normalizes_exact owner revision head arity accepted

theorem finish_run_observation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    terminalControl? (finishRun owner revision head arity accepted).endpoint =
      some (finishTarget owner revision head arity accepted) := by
  rw [finish_run_endpoint_exact]
  exact finish_terminal_observation_exact owner revision head arity accepted

theorem finish_run_path_bounded
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    (finishRun owner revision head arity accepted).path.length ≤ 64 :=
  (finishRun owner revision head arity accepted).length_le

theorem finish_run_path_nonempty
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    0 < (finishRun owner revision head arity accepted).path.length := by
  apply (finishRun owner revision head arity accepted).nonempty_of_reduct
  · decide
  · rw [finish_phase_rewrite_exact owner revision head arity accepted]
    simp

/-- Every source `finish` step owns a retained, bounded, nonempty path in the
actual generated StructuredC GSLT, and that path observes the exact source
target. -/
theorem finish_step_realization
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    ∃ endpoint : Pattern,
      ∃ path : ExecutionPath coldGSLT
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (finishSource owner revision head arity accepted)) endpoint,
      terminalControl? endpoint =
          some (finishTarget owner revision head arity accepted) ∧
        0 < path.length ∧ path.length ≤ 64 := by
  let run := finishRun owner revision head arity accepted
  refine ⟨run.endpoint, run.path, ?_, ?_, ?_⟩
  · exact finish_run_observation_exact owner revision head arity accepted
  · exact finish_run_path_nonempty owner revision head arity accepted
  · exact finish_run_path_bounded owner revision head arity accepted

/-- The deterministic generated execution cannot invent a different observed
finish target. -/
theorem finish_normalized_observation_iff
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (finishSource owner revision head arity accepted))) =
        some observed ↔
      observed = finishTarget owner revision head arity accepted := by
  rw [finish_normalizes_exact]
  have observedExact :
      terminalControl? (finishHalted owner revision head arity accepted) =
        some (finishTarget owner revision head arity accepted) := by
    simpa [finishHalted] using
      finish_terminal_observation_exact owner revision head arity accepted
  rw [observedExact]
  simp [eq_comm]

theorem finish_wrong_target_rejected
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (observed : CompileLanguageControl)
    (wrong : observed ≠ finishTarget owner revision head arity accepted) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (finishSource owner revision head arity accepted))) ≠
      some observed := by
  intro invented
  exact wrong ((finish_normalized_observation_iff owner revision head arity
    accepted observed).mp invented)

theorem finish_source_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    compileLanguageGSLT.Step
      (finishSource owner revision head arity accepted)
      (finishTarget owner revision head arity accepted) := by
  rfl

#print axioms finish_source_lookup0
#print axioms finish_source_lookup5
#print axioms finish_operands_lookup5
#print axioms finish_source_step
#print axioms finish_normalizes_exact
#print axioms finish_run_endpoint_exact
#print axioms finish_run_observation_exact
#print axioms finish_run_path_bounded
#print axioms finish_run_path_nonempty
#print axioms finish_step_realization
#print axioms finish_normalized_observation_iff
#print axioms finish_wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOneStepSimulation
