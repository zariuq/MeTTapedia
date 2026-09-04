import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation

/-!
# Generated StructuredC realization of the undefined-input family

The generated dispatcher must first reject the earlier raw-atom family and
then recognize the exact PeTTa undefined type.  Only after those ordered tests
does the shared literal suffix consume the cursor and append `evalUnchecked`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCUndefinedInputSimulation

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
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation

def prefixReceipt : Pattern :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.receipt15

def atomReceipt : Pattern := externalReceipt termIsAtomQuery prefixReceipt
def undefinedReceipt : Pattern :=
  externalReceipt termIsUndefinedQuery atomReceipt

def baseContinuation : Pattern :=
  StructuredC.appendStatements (statements []) (statements [])

def atomRest : Pattern :=
  StructuredC.appendStatements (statements []) baseContinuation

def undefinedRest : Pattern :=
  StructuredC.appendStatements (statements []) atomRest

theorem expected_lookup13
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    lookup?
        (environment13 .undefined owner revision head arity declaration
          remaining inputCursor modes accepted)
        (identifier "expected") =
      some (abiValue (encodeTerm undefinedType)) := by
  simpa [LiteralPredicate.term] using
    literal_expected_lookup13 .undefined owner revision head arity declaration
      remaining inputCursor modes accepted

theorem literal_dispatcher_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.prefixEndpoint
          (inputData .undefined owner revision head arity declaration remaining
            inputCursor modes accepted)) =
      [run (consStatement generatedAtomInputDecision atomRest)
        (environment13 .undefined owner revision head arity declaration
          remaining inputCursor modes accepted) prefixReceipt] := by
  rw [Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.prefixEndpoint,
    generatedLiteralInputDispatcher_shape]
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement generatedAtomInputDecision (statements []))
        baseContinuation)
        (environment13 .undefined owner revision head arity declaration
          remaining inputCursor modes accepted) prefixReceipt) = _
  simpa [atomRest] using appendConsTransition_rewriteAt_exact coldRelations
    generatedAtomInputDecision (statements []) baseContinuation
    (environment13 .undefined owner revision head arity declaration remaining
      inputCursor modes accepted) prefixReceipt

theorem atom_decision_false_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedAtomInputDecision atomRest)
          (environment13 .undefined owner revision head arity declaration
            remaining inputCursor modes accepted) prefixReceipt) =
      [run (StructuredC.appendStatements generatedAtomInputFallback atomRest)
        (environment13 .undefined owner revision head arity declaration
          remaining inputCursor modes accepted) atomReceipt] := by
  have evaluated :
      evaluate? coldHandler
          (call termIsAtomQuery [variableExpression "expected"])
          (environment13 .undefined owner revision head arity declaration
            remaining inputCursor modes accepted) prefixReceipt =
        some ⟨.value falseValue,
          environment13 .undefined owner revision head arity declaration
            remaining inputCursor modes accepted,
          atomReceipt⟩ := by
    simpa [LiteralPredicate.externalName, LiteralPredicate.term, atomReceipt,
      prefixReceipt, atomType, undefinedType] using
      literalPredicate_evaluation_exact .atom undefinedType
        (environment13 .undefined owner revision head arity declaration
          remaining inputCursor modes accepted) prefixReceipt
        (expected_lookup13 owner revision head arity declaration remaining
          inputCursor modes accepted)
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
      (environment13 .undefined owner revision head arity declaration remaining
        inputCursor modes accepted) prefixReceipt falseValue
      (environment13 .undefined owner revision head arity declaration remaining
        inputCursor modes accepted) atomReceipt generatedAtomInputFallback
      evaluated selected

theorem atom_fallback_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedAtomInputFallback atomRest)
          (environment13 .undefined owner revision head arity declaration
            remaining inputCursor modes accepted) atomReceipt) =
      [run (consStatement generatedUndefinedInputDecision undefinedRest)
        (environment13 .undefined owner revision head arity declaration
          remaining inputCursor modes accepted) atomReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement generatedUndefinedInputDecision (statements []))
        atomRest)
        (environment13 .undefined owner revision head arity declaration
          remaining inputCursor modes accepted) atomReceipt) = _
  simpa [undefinedRest] using appendConsTransition_rewriteAt_exact coldRelations
    generatedUndefinedInputDecision (statements []) atomRest
    (environment13 .undefined owner revision head arity declaration remaining
      inputCursor modes accepted) atomReceipt

theorem undefined_decision_true_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedUndefinedInputDecision undefinedRest)
          (environment13 .undefined owner revision head arity declaration
            remaining inputCursor modes accepted) atomReceipt) =
      [run (StructuredC.appendStatements undefinedInputBody undefinedRest)
        (environment13 .undefined owner revision head arity declaration
          remaining inputCursor modes accepted) undefinedReceipt] := by
  have evaluated :
      evaluate? coldHandler
          (call termIsUndefinedQuery [variableExpression "expected"])
          (environment13 .undefined owner revision head arity declaration
            remaining inputCursor modes accepted) atomReceipt =
        some ⟨.value trueValue,
          environment13 .undefined owner revision head arity declaration
            remaining inputCursor modes accepted,
          undefinedReceipt⟩ := by
    simpa [LiteralPredicate.externalName, LiteralPredicate.term,
      undefinedReceipt] using
      literalPredicate_evaluation_exact .undefined undefinedType
        (environment13 .undefined owner revision head arity declaration
          remaining inputCursor modes accepted) atomReceipt
        (expected_lookup13 owner revision head arity declaration remaining
          inputCursor modes accepted)
  have selected :
      selectBranch? trueValue undefinedInputBody generatedUndefinedInputFallback =
        some undefinedInputBody := by
    simp [selectBranch?, trueValue, valueSymbol, identifier, node, token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedUndefinedInputDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsUndefinedQuery [variableExpression "expected"])
      undefinedInputBody generatedUndefinedInputFallback undefinedRest
      (environment13 .undefined owner revision head arity declaration remaining
        inputCursor modes accepted) atomReceipt trueValue
      (environment13 .undefined owner revision head arity declaration remaining
        inputCursor modes accepted) undefinedReceipt undefinedInputBody
      evaluated selected

theorem normalizes_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source .undefined owner revision head arity declaration remaining
            inputCursor modes accepted)) =
      haltedTarget .undefined owner revision head arity declaration remaining
        inputCursor modes accepted undefinedReceipt := by
  change normalizeFirstUsing coldRelations StructuredC.language 1 (35 + 29)
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (inputData .undefined owner revision head arity declaration remaining
          inputCursor modes accepted).source) = _
  rw [Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.normalize_prefix_exact
    (inputData .undefined owner revision head arity declaration remaining
      inputCursor modes accepted) 35]
  simp only [normalizeFirstAt,
    literal_dispatcher_append_rewrite_exact owner revision head arity
      declaration remaining inputCursor modes accepted]
  simp only [atom_decision_false_rewrite_exact owner revision head arity
    declaration remaining inputCursor modes accepted]
  simp only [atom_fallback_append_rewrite_exact owner revision head arity
    declaration remaining inputCursor modes accepted]
  simp only [undefined_decision_true_rewrite_exact owner revision head arity
    declaration remaining inputCursor modes accepted]
  exact normalize_suffix_exact .undefined owner revision head arity declaration
    remaining inputCursor modes accepted undefinedReceipt undefinedRest 27

abbrev run
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (source .undefined owner revision head arity declaration remaining
          inputCursor modes accepted)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (source .undefined owner revision head arity declaration remaining
        inputCursor modes accepted))

theorem run_endpoint_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    (run owner revision head arity declaration remaining inputCursor modes
      accepted).endpoint =
      haltedTarget .undefined owner revision head arity declaration remaining
        inputCursor modes accepted undefinedReceipt := by
  calc
    _ = normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source .undefined owner revision head arity declaration remaining
            inputCursor modes accepted)) :=
      (run owner revision head arity declaration remaining inputCursor modes
        accepted).endpoint_eq
    _ = _ := normalizes_exact owner revision head arity declaration remaining
      inputCursor modes accepted

theorem run_observation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    terminalControl?
        (run owner revision head arity declaration remaining inputCursor modes
          accepted).endpoint =
      some (target .undefined owner revision head arity declaration remaining
        inputCursor modes accepted) := by
  rw [run_endpoint_exact owner revision head arity declaration remaining
    inputCursor modes accepted]
  exact terminal_observation_exact .undefined owner revision head arity
    declaration remaining inputCursor modes accepted undefinedReceipt

theorem run_path_bounded
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    (run owner revision head arity declaration remaining inputCursor modes
      accepted).path.length ≤ 64 :=
  (run owner revision head arity declaration remaining inputCursor modes
    accepted).length_le

theorem run_path_nonempty
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    0 < (run owner revision head arity declaration remaining inputCursor modes
      accepted).path.length := by
  apply (run owner revision head arity declaration remaining inputCursor modes
    accepted).nonempty_of_reduct
  · decide
  · change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (inputData .undefined owner revision head arity declaration remaining
            inputCursor modes accepted).source) ≠ []
    rw [Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.phase_rewrite_exact
      (inputData .undefined owner revision head arity declaration remaining
        inputCursor modes accepted)]
    simp

theorem step_realization
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    ∃ endpoint : Pattern,
      ∃ path : ExecutionPath coldGSLT
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source .undefined owner revision head arity declaration remaining
              inputCursor modes accepted)) endpoint,
      terminalControl? endpoint =
          some (target .undefined owner revision head arity declaration
            remaining inputCursor modes accepted) ∧
        0 < path.length ∧ path.length ≤ 64 := by
  let execution := run owner revision head arity declaration remaining
    inputCursor modes accepted
  refine ⟨execution.endpoint, execution.path, ?_, ?_, ?_⟩
  · exact run_observation_exact owner revision head arity declaration remaining
      inputCursor modes accepted
  · exact run_path_nonempty owner revision head arity declaration remaining
      inputCursor modes accepted
  · exact run_path_bounded owner revision head arity declaration remaining
      inputCursor modes accepted

theorem normalized_observation_iff
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source .undefined owner revision head arity declaration remaining
              inputCursor modes accepted))) = some observed ↔
      observed = target .undefined owner revision head arity declaration
        remaining inputCursor modes accepted := by
  rw [normalizes_exact owner revision head arity declaration remaining
    inputCursor modes accepted]
  have observedExact := terminal_observation_exact .undefined owner revision
    head arity declaration remaining inputCursor modes accepted undefinedReceipt
  rw [observedExact]
  simp [eq_comm]

theorem wrong_target_rejected
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (observed : CompileLanguageControl)
    (wrong : observed ≠ target .undefined owner revision head arity declaration
      remaining inputCursor modes accepted) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source .undefined owner revision head arity declaration remaining
              inputCursor modes accepted))) ≠ some observed := by
  intro invented
  exact wrong ((normalized_observation_iff owner revision head arity declaration
    remaining inputCursor modes accepted observed).mp invented)

#print axioms normalizes_exact
#print axioms run_endpoint_exact
#print axioms run_observation_exact
#print axioms run_path_bounded
#print axioms run_path_nonempty
#print axioms step_realization
#print axioms normalized_observation_iff
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCUndefinedInputSimulation
