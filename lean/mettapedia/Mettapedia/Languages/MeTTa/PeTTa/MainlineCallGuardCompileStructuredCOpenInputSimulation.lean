import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedInputSimulation

/-!
# Generated StructuredC realization of the open-input family

For every source term for which the independent argument compiler returns no
mode, the generated target program rejects the literal and checked rows,
confirms the open-input premise, and changes the stored compiler state to the
outside-fragment result.  The returned outcome does not select that result;
the state-changing primitive checks the same source classification again.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOpenInputSimulation

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
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation

namespace Checked

abbrev inputData :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedInputSimulation.inputData
abbrev source :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedInputSimulation.source
abbrev environment13 :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedInputSimulation.environment13
abbrev source_lookup13 :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedInputSimulation.source_lookup13
abbrev expected_lookup13 :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedInputSimulation.expected_lookup13

end Checked

namespace NonLiteral

abbrev inputData :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.inputData
abbrev environment13 :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.environment13
abbrev holeReceipt :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.holeReceipt
abbrev holeRest :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.holeRest
abbrev checkedRest :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.checkedRest
abbrev checkedEndpoint :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.checkedEndpoint
abbrev normalize_prefix_exact :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.normalize_prefix_exact

end NonLiteral

abbrev inputData := Checked.inputData
abbrev source := Checked.source
abbrev environment13 := Checked.environment13

def target : CompileLanguageControl :=
  .halted .outsideFragment

def environment14
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  bindName "state" (stateValue target)
    (environment13 expected owner revision head arity declaration remaining
      inputCursor modes accepted)

def checkedReceipt : Pattern :=
  externalReceipt inputIsCheckedQuery NonLiteral.holeReceipt

def openReceipt : Pattern :=
  externalReceipt inputIsOpenQuery checkedReceipt

def deltaReceipt : Pattern :=
  externalReceipt setOutsideFragmentDelta openReceipt

def openRest : Pattern :=
  StructuredC.appendStatements
    (statements [returnSymbol noTransitionOutcome]) NonLiteral.holeRest

def effectExpression : Pattern :=
  call setOutsideFragmentDelta [variableExpression "state"]

def effectStatement : Pattern := effect effectExpression

def returnStatements : Pattern :=
  statements [returnSymbol outsideFragmentOutcome]

theorem not_atom_of_unsupported (expected : Term)
    (unsupported : compileArgMode expected = none) :
    expected ≠ atomType := by
  intro equal
  subst expected
  simp [compileArgMode, atomType] at unsupported

theorem not_undefined_of_unsupported (expected : Term)
    (unsupported : compileArgMode expected = none) :
    expected ≠ undefinedType := by
  intro equal
  subst expected
  simp [compileArgMode, undefinedType, atomType] at unsupported

theorem not_hole_of_unsupported (expected : Term)
    (unsupported : compileArgMode expected = none) :
    expected ≠ holeType := by
  intro equal
  subst expected
  simp [compileArgMode, holeType, undefinedType, atomType] at unsupported

theorem source_lookup13
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    lookup?
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted)
        (identifier "state") =
      some (stateValue (source expected owner revision head arity declaration
        remaining inputCursor modes accepted)) := by
  exact Checked.source_lookup13 expected owner revision head arity declaration
    remaining inputCursor modes accepted

theorem expected_lookup13
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    lookup?
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted)
        (identifier "expected") = some (abiValue (encodeTerm expected)) := by
  exact Checked.expected_lookup13 expected owner revision head arity
    declaration remaining inputCursor modes accepted

theorem checked_decision_false_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (unsupported : compileArgMode expected = none) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (NonLiteral.checkedEndpoint expected owner revision head arity
          declaration remaining inputCursor modes accepted) =
      [run (StructuredC.appendStatements (statements [])
          NonLiteral.checkedRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) checkedReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (consStatement checkedInputDecision NonLiteral.checkedRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) NonLiteral.holeReceipt) = _
  have evaluated :
      evaluate? coldHandler
          (call inputIsCheckedQuery [variableExpression "expected"])
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) NonLiteral.holeReceipt =
        some ⟨.value falseValue,
          environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted, checkedReceipt⟩ := by
    simpa [checkedInputAnswer, unsupported, checkedReceipt] using
      inputIsChecked_evaluation_exact expected
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) NonLiteral.holeReceipt
        (expected_lookup13 expected owner revision head arity declaration
          remaining inputCursor modes accepted)
  have selected :
      selectBranch? falseValue checkedInputSuccessBody (statements []) =
        some (statements []) := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    checkedInputDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call inputIsCheckedQuery [variableExpression "expected"])
      checkedInputSuccessBody (statements []) NonLiteral.checkedRest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) NonLiteral.holeReceipt falseValue
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) checkedReceipt (statements []) evaluated
      selected

theorem checked_empty_append_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements (statements [])
          NonLiteral.checkedRest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) checkedReceipt) =
      [run NonLiteral.checkedRest
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) checkedReceipt] := by
  simpa [statements, StructuredC.nilStatements, node, StructuredC.a] using
    appendEmptyTransition_rewriteAt_exact coldRelations NonLiteral.checkedRest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) checkedReceipt

theorem checked_rest_append_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run NonLiteral.checkedRest
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) checkedReceipt) =
      [run (consStatement openInputDecision openRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) checkedReceipt] := by
  rw [show NonLiteral.checkedRest =
      StructuredC.appendStatements
        (statements [openInputDecision, returnSymbol noTransitionOutcome])
        NonLiteral.holeRest by rfl]
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement openInputDecision
          (statements [returnSymbol noTransitionOutcome])) NonLiteral.holeRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) checkedReceipt) = _
  simpa [openRest] using
    appendConsTransition_rewriteAt_exact coldRelations openInputDecision
      (statements [returnSymbol noTransitionOutcome]) NonLiteral.holeRest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) checkedReceipt

theorem open_decision_true_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (unsupported : compileArgMode expected = none) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement openInputDecision openRest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) checkedReceipt) =
      [run (StructuredC.appendStatements openInputSuccessBody openRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) openReceipt] := by
  have evaluated :
      evaluate? coldHandler
          (call inputIsOpenQuery [variableExpression "expected"])
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) checkedReceipt =
        some ⟨.value trueValue,
          environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted, openReceipt⟩ := by
    simpa [openInputAnswer, unsupported, openReceipt] using
      inputIsOpen_evaluation_exact expected
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) checkedReceipt
        (expected_lookup13 expected owner revision head arity declaration
          remaining inputCursor modes accepted)
  have selected :
      selectBranch? trueValue openInputSuccessBody (statements []) =
        some openInputSuccessBody := by
    simp [selectBranch?, trueValue, valueSymbol, identifier, node, token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    openInputDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call inputIsOpenQuery [variableExpression "expected"])
      openInputSuccessBody (statements []) openRest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) checkedReceipt trueValue
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) openReceipt openInputSuccessBody evaluated
      selected

theorem open_body_append_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements openInputSuccessBody openRest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) openReceipt) =
      [run (consStatement effectStatement
          (StructuredC.appendStatements returnStatements openRest))
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) openReceipt] := by
  rw [openInputSuccessBody]
  simpa [effectStatement, effectExpression, returnStatements, statements,
    node, StructuredC.consStatement, StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations effectStatement
      returnStatements openRest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) openReceipt

theorem delta_evaluation_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (unsupported : compileArgMode expected = none) :
    evaluate? coldHandler effectExpression
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) openReceipt =
      some ⟨.value valueUnit,
        environment14 expected owner revision head arity declaration remaining
          inputCursor modes accepted, deltaReceipt⟩ := by
  have handled := handler_setOutsideFragment_arguments_exact owner revision
    head arity declaration remaining expected inputCursor modes accepted
    (environment13 expected owner revision head arity declaration remaining
      inputCursor modes accepted) openReceipt unsupported
    (source_lookup13 expected owner revision head arity declaration remaining
      inputCursor modes accepted)
  simpa [effectExpression, environment14, target, deltaReceipt] using
    evaluate_single_variable_call_exact coldHandler setOutsideFragmentDelta
      "state"
      (stateValue (source expected owner revision head arity declaration
        remaining inputCursor modes accepted))
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) openReceipt _
      (source_lookup13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) handled

theorem delta_effect_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (unsupported : compileArgMode expected = none)
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement effectStatement rest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) openReceipt) =
      [run rest
        (environment14 expected owner revision head arity declaration remaining
          inputCursor modes accepted) deltaReceipt] := by
  have evaluated := delta_evaluation_exact expected owner revision head arity
    declaration remaining inputCursor modes accepted unsupported
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    effectStatement, effect, node, StructuredC.a] using
    effect_rewriteAt_exact_of_evaluate coldHandler effectExpression rest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) openReceipt valueUnit
      (environment14 expected owner revision head arity declaration remaining
        inputCursor modes accepted) deltaReceipt evaluated

theorem return_statements_append_rewrite_exact
    (continuation environment receipt : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements returnStatements continuation)
          environment receipt) =
      [run (consStatement (returnSymbol outsideFragmentOutcome)
          (StructuredC.appendStatements (statements []) continuation))
        environment receipt] := by
  simpa [returnStatements, statements, node, StructuredC.consStatement,
    StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations
      (returnSymbol outsideFragmentOutcome) (statements []) continuation
      environment receipt

theorem return_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol outsideFragmentOutcome) rest)
          (environment14 expected owner revision head arity declaration
            remaining inputCursor modes accepted) deltaReceipt) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol outsideFragmentOutcome])
        (environment14 expected owner revision head arity declaration remaining
          inputCursor modes accepted) deltaReceipt] := by
  have evaluated := evaluate_symbol_exact coldHandler outsideFragmentOutcome
    (environment14 expected owner revision head arity declaration remaining
      inputCursor modes accepted) deltaReceipt
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a] using
    return_rewriteAt_exact_of_evaluate coldHandler
      (symbol outsideFragmentOutcome) rest
      (environment14 expected owner revision head arity declaration remaining
        inputCursor modes accepted) deltaReceipt
      (valueSymbol outsideFragmentOutcome)
      (environment14 expected owner revision head arity declaration remaining
        inputCursor modes accepted) deltaReceipt evaluated

def haltedTarget
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol outsideFragmentOutcome])
    (environment14 expected owner revision head arity declaration remaining
      inputCursor modes accepted) deltaReceipt

theorem terminal_observation_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    terminalControl?
        (haltedTarget expected owner revision head arity declaration remaining
          inputCursor modes accepted) = some target := by
  simp [haltedTarget, terminalControl?, environment14, target, halted,
    StructuredC.a, lookup?, bindName, environmentBind, identifier,
    decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue, node,
    token]

theorem source_step
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (unsupported : compileArgMode expected = none) :
    compileLanguageGSLT.Step
      (source expected owner revision head arity declaration remaining
        inputCursor modes accepted) target := by
  change compileLanguageStep?
      (.arguments owner revision head arity declaration remaining
        (expected :: inputCursor) modes accepted) = some target
  simp [target, compileLanguageStep?, unsupported]

theorem normalizes_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (unsupported : compileArgMode expected = none) :
    normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source expected owner revision head arity declaration remaining
            inputCursor modes accepted)) =
      haltedTarget expected owner revision head arity declaration remaining
        inputCursor modes accepted := by
  change normalizeFirstUsing coldRelations StructuredC.language 1 (35 + 29)
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (inputData expected owner revision head arity declaration remaining
          inputCursor modes accepted).source) = _
  rw [Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.normalize_prefix_exact
    (inputData expected owner revision head arity declaration remaining
      inputCursor modes accepted) 35]
  change normalizeFirstAt (engineBasePremises coldRelations)
      StructuredC.language 1 (28 + 7)
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.prefixEndpoint
          (NonLiteral.inputData expected owner revision head arity declaration
            remaining inputCursor modes accepted)) = _
  rw [NonLiteral.normalize_prefix_exact expected owner revision head arity
    declaration remaining inputCursor modes accepted
    (not_atom_of_unsupported expected unsupported)
    (not_undefined_of_unsupported expected unsupported)
    (not_hole_of_unsupported expected unsupported) 28]
  simp only [normalizeFirstAt,
    checked_decision_false_rewrite_exact expected owner revision head arity
      declaration remaining inputCursor modes accepted unsupported]
  simp only [checked_empty_append_rewrite_exact expected owner revision head
    arity declaration remaining inputCursor modes accepted]
  simp only [checked_rest_append_rewrite_exact expected owner revision head
    arity declaration remaining inputCursor modes accepted]
  simp only [open_decision_true_rewrite_exact expected owner revision head arity
    declaration remaining inputCursor modes accepted unsupported]
  simp only [open_body_append_rewrite_exact expected owner revision head arity
    declaration remaining inputCursor modes accepted]
  simp only [delta_effect_rewrite_exact expected owner revision head arity
    declaration remaining inputCursor modes accepted unsupported]
  simp only [return_statements_append_rewrite_exact]
  simp only [return_rewrite_exact expected owner revision head arity declaration
    remaining inputCursor modes accepted]
  simp only [halted_rewriteAt_empty]
  rfl

abbrev execution
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (source expected owner revision head arity declaration remaining
          inputCursor modes accepted)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (source expected owner revision head arity declaration remaining
        inputCursor modes accepted))

theorem execution_endpoint_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (unsupported : compileArgMode expected = none) :
    (execution expected owner revision head arity declaration remaining
      inputCursor modes accepted).endpoint =
      haltedTarget expected owner revision head arity declaration remaining
        inputCursor modes accepted := by
  calc
    _ = normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source expected owner revision head arity declaration remaining
            inputCursor modes accepted)) :=
      (execution expected owner revision head arity declaration remaining
        inputCursor modes accepted).endpoint_eq
    _ = _ := normalizes_exact expected owner revision head arity declaration
      remaining inputCursor modes accepted unsupported

theorem execution_observation_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (unsupported : compileArgMode expected = none) :
    terminalControl?
        (execution expected owner revision head arity declaration remaining
          inputCursor modes accepted).endpoint = some target := by
  rw [execution_endpoint_exact expected owner revision head arity declaration
    remaining inputCursor modes accepted unsupported]
  exact terminal_observation_exact expected owner revision head arity
    declaration remaining inputCursor modes accepted

theorem execution_path_bounded
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    (execution expected owner revision head arity declaration remaining
      inputCursor modes accepted).path.length ≤ 64 :=
  (execution expected owner revision head arity declaration remaining
    inputCursor modes accepted).length_le

theorem execution_path_nonempty
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    0 < (execution expected owner revision head arity declaration remaining
      inputCursor modes accepted).path.length := by
  apply (execution expected owner revision head arity declaration remaining
    inputCursor modes accepted).nonempty_of_reduct
  · decide
  · change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (inputData expected owner revision head arity declaration remaining
            inputCursor modes accepted).source) ≠ []
    rw [Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.phase_rewrite_exact
      (inputData expected owner revision head arity declaration remaining
        inputCursor modes accepted)]
    simp

theorem step_realization
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (unsupported : compileArgMode expected = none) :
    ∃ endpoint : Pattern,
      ∃ path : ExecutionPath coldGSLT
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source expected owner revision head arity declaration remaining
              inputCursor modes accepted)) endpoint,
      terminalControl? endpoint = some target ∧
        0 < path.length ∧ path.length ≤ 64 := by
  let run := execution expected owner revision head arity declaration remaining
    inputCursor modes accepted
  refine ⟨run.endpoint, run.path, ?_, ?_, ?_⟩
  · exact execution_observation_exact expected owner revision head arity
      declaration remaining inputCursor modes accepted unsupported
  · exact execution_path_nonempty expected owner revision head arity declaration
      remaining inputCursor modes accepted
  · exact execution_path_bounded expected owner revision head arity declaration
      remaining inputCursor modes accepted

theorem normalized_observation_iff
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (unsupported : compileArgMode expected = none)
    (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source expected owner revision head arity declaration remaining
              inputCursor modes accepted))) = some observed ↔
      observed = target := by
  rw [normalizes_exact expected owner revision head arity declaration remaining
    inputCursor modes accepted unsupported]
  have observedExact := terminal_observation_exact expected owner revision head
    arity declaration remaining inputCursor modes accepted
  rw [observedExact]
  simp [eq_comm]

theorem wrong_target_rejected
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (unsupported : compileArgMode expected = none)
    (observed : CompileLanguageControl) (wrong : observed ≠ target) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source expected owner revision head arity declaration remaining
              inputCursor modes accepted))) ≠ some observed := by
  intro invented
  exact wrong ((normalized_observation_iff expected owner revision head arity
    declaration remaining inputCursor modes accepted unsupported observed).mp
      invented)

#print axioms source_step
#print axioms normalizes_exact
#print axioms execution_endpoint_exact
#print axioms execution_observation_exact
#print axioms execution_path_bounded
#print axioms execution_path_nonempty
#print axioms step_realization
#print axioms normalized_observation_iff
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOpenInputSimulation
