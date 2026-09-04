import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCHoleInputSimulation

/-!
# Shared generated StructuredC prefix for checked and open inputs

Checked and open inputs share the same negative passage through the three
authored literal rows.  This module proves that passage against the generated
StructuredC decision tree for an arbitrary non-literal term.  It stops at the
checked-input decision, where the two semantic cases genuinely diverge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation

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
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation

def inputData
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : InputStateData :=
  { owner, revision, head, arity, declaration, remaining, expected,
    inputCursor, modes, accepted }

def source
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  (inputData expected owner revision head arity declaration remaining
    inputCursor modes accepted).source

def environment13
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  (inputData expected owner revision head arity declaration remaining
    inputCursor modes accepted).environment13

def prefixReceipt : Pattern :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.receipt15

def atomReceipt : Pattern := externalReceipt termIsAtomQuery prefixReceipt
def undefinedReceipt : Pattern :=
  externalReceipt termIsUndefinedQuery atomReceipt
def holeReceipt : Pattern := externalReceipt termIsHoleQuery undefinedReceipt

def baseContinuation : Pattern :=
  StructuredC.appendStatements (statements []) (statements [])
def atomRest : Pattern :=
  StructuredC.appendStatements (statements []) baseContinuation
def undefinedRest : Pattern :=
  StructuredC.appendStatements (statements []) atomRest
def holeRest : Pattern :=
  StructuredC.appendStatements (statements []) undefinedRest
def checkedRest : Pattern :=
  StructuredC.appendStatements
    (statements [openInputDecision, returnSymbol noTransitionOutcome]) holeRest

def checkedEndpoint
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  run (consStatement checkedInputDecision checkedRest)
    (environment13 expected owner revision head arity declaration remaining
      inputCursor modes accepted) holeReceipt

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
  simp [environment13, inputData, InputStateData.environment13,
    InputStateData.environment12, lookup?, bindName, environmentBind,
    identifier, node, token, InputStateData.expectedValue]

theorem literal_dispatcher_append_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.prefixEndpoint
          (inputData expected owner revision head arity declaration remaining
            inputCursor modes accepted)) =
      [run (consStatement generatedAtomInputDecision atomRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) prefixReceipt] := by
  rw [Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.prefixEndpoint,
    generatedLiteralInputDispatcher_shape]
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement generatedAtomInputDecision (statements []))
        baseContinuation)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) prefixReceipt) = _
  simpa [atomRest] using appendConsTransition_rewriteAt_exact coldRelations
    generatedAtomInputDecision (statements []) baseContinuation
    (environment13 expected owner revision head arity declaration remaining
      inputCursor modes accepted) prefixReceipt

theorem atom_decision_false_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (different : expected ≠ atomType) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedAtomInputDecision atomRest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) prefixReceipt) =
      [run (StructuredC.appendStatements generatedAtomInputFallback atomRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) atomReceipt] := by
  have evaluated :
      evaluate? coldHandler
          (call termIsAtomQuery [variableExpression "expected"])
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) prefixReceipt =
        some ⟨.value falseValue,
          environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted, atomReceipt⟩ := by
    simpa [LiteralPredicate.externalName, LiteralPredicate.term, atomReceipt,
      different] using
      literalPredicate_evaluation_exact .atom expected
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) prefixReceipt
        (expected_lookup13 expected owner revision head arity declaration
          remaining inputCursor modes accepted)
  have selected :
      selectBranch? falseValue rawInputBody generatedAtomInputFallback =
        some generatedAtomInputFallback := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedAtomInputDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsAtomQuery [variableExpression "expected"])
      rawInputBody generatedAtomInputFallback atomRest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) prefixReceipt falseValue
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) atomReceipt generatedAtomInputFallback
      evaluated selected

theorem atom_fallback_append_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedAtomInputFallback atomRest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) atomReceipt) =
      [run (consStatement generatedUndefinedInputDecision undefinedRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) atomReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement generatedUndefinedInputDecision (statements []))
        atomRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) atomReceipt) = _
  simpa [undefinedRest] using appendConsTransition_rewriteAt_exact coldRelations
    generatedUndefinedInputDecision (statements []) atomRest
    (environment13 expected owner revision head arity declaration remaining
      inputCursor modes accepted) atomReceipt

theorem undefined_decision_false_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (different : expected ≠ undefinedType) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedUndefinedInputDecision undefinedRest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) atomReceipt) =
      [run (StructuredC.appendStatements generatedUndefinedInputFallback
          undefinedRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) undefinedReceipt] := by
  have evaluated :
      evaluate? coldHandler
          (call termIsUndefinedQuery [variableExpression "expected"])
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) atomReceipt =
        some ⟨.value falseValue,
          environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted, undefinedReceipt⟩ := by
    simpa [LiteralPredicate.externalName, LiteralPredicate.term,
      undefinedReceipt, different] using
      literalPredicate_evaluation_exact .undefined expected
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) atomReceipt
        (expected_lookup13 expected owner revision head arity declaration
          remaining inputCursor modes accepted)
  have selected :
      selectBranch? falseValue undefinedInputBody
          generatedUndefinedInputFallback =
        some generatedUndefinedInputFallback := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedUndefinedInputDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsUndefinedQuery [variableExpression "expected"])
      undefinedInputBody generatedUndefinedInputFallback undefinedRest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) atomReceipt falseValue
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) undefinedReceipt
      generatedUndefinedInputFallback evaluated selected

theorem undefined_fallback_append_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedUndefinedInputFallback
          undefinedRest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) undefinedReceipt) =
      [run (consStatement generatedHoleInputDecision holeRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) undefinedReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement generatedHoleInputDecision (statements []))
        undefinedRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) undefinedReceipt) = _
  simpa [holeRest] using appendConsTransition_rewriteAt_exact coldRelations
    generatedHoleInputDecision (statements []) undefinedRest
    (environment13 expected owner revision head arity declaration remaining
      inputCursor modes accepted) undefinedReceipt

theorem hole_decision_false_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (different : expected ≠ holeType) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedHoleInputDecision holeRest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) undefinedReceipt) =
      [run (StructuredC.appendStatements generatedCheckedOpenInputFallback
          holeRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) holeReceipt] := by
  have evaluated :
      evaluate? coldHandler
          (call termIsHoleQuery [variableExpression "expected"])
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) undefinedReceipt =
        some ⟨.value falseValue,
          environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted, holeReceipt⟩ := by
    simpa [LiteralPredicate.externalName, LiteralPredicate.term, holeReceipt,
      different] using
      literalPredicate_evaluation_exact .hole expected
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) undefinedReceipt
        (expected_lookup13 expected owner revision head arity declaration
          remaining inputCursor modes accepted)
  have selected :
      selectBranch? falseValue holeInputBody generatedCheckedOpenInputFallback =
        some generatedCheckedOpenInputFallback := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedHoleInputDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsHoleQuery [variableExpression "expected"])
      holeInputBody generatedCheckedOpenInputFallback holeRest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) undefinedReceipt falseValue
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) holeReceipt generatedCheckedOpenInputFallback
      evaluated selected

theorem checked_fallback_append_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedCheckedOpenInputFallback
          holeRest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) holeReceipt) =
      [checkedEndpoint expected owner revision head arity declaration remaining
        inputCursor modes accepted] := by
  rw [generatedCheckedOpenInputFallback_shape]
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement checkedInputDecision
          (statements [openInputDecision, returnSymbol noTransitionOutcome]))
        holeRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) holeReceipt) = _
  simpa [checkedEndpoint, checkedRest] using
    appendConsTransition_rewriteAt_exact coldRelations checkedInputDecision
      (statements [openInputDecision, returnSymbol noTransitionOutcome])
      holeRest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) holeReceipt

/-- Seven target steps expose the checked-input decision after the common
twenty-nine-step argument prefix. -/
theorem normalize_prefix_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (notAtom : expected ≠ atomType)
    (notUndefined : expected ≠ undefinedType)
    (notHole : expected ≠ holeType)
    (fuel : Nat) :
    normalizeFirstAt (engineBasePremises coldRelations) StructuredC.language 1
        (fuel + 7)
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.prefixEndpoint
          (inputData expected owner revision head arity declaration remaining
            inputCursor modes accepted)) =
      normalizeFirstAt (engineBasePremises coldRelations) StructuredC.language
        1 fuel
        (checkedEndpoint expected owner revision head arity declaration remaining
          inputCursor modes accepted) := by
  simp only [normalizeFirstAt,
    literal_dispatcher_append_rewrite_exact expected owner revision head arity
      declaration remaining inputCursor modes accepted]
  simp only [atom_decision_false_rewrite_exact expected owner revision head
    arity declaration remaining inputCursor modes accepted notAtom]
  simp only [atom_fallback_append_rewrite_exact expected owner revision head
    arity declaration remaining inputCursor modes accepted]
  simp only [undefined_decision_false_rewrite_exact expected owner revision
    head arity declaration remaining inputCursor modes accepted notUndefined]
  simp only [undefined_fallback_append_rewrite_exact expected owner revision
    head arity declaration remaining inputCursor modes accepted]
  simp only [hole_decision_false_rewrite_exact expected owner revision head
    arity declaration remaining inputCursor modes accepted notHole]
  simp only [checked_fallback_append_rewrite_exact expected owner revision head
    arity declaration remaining inputCursor modes accepted]

#print axioms normalize_prefix_exact

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation
