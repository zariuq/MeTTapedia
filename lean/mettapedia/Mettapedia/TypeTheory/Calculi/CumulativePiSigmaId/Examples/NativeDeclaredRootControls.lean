import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeDeclaredRootExecution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeBranchReturnControls

/-!
# All-root native certificate execution controls

The same independent source/result replay tests exercise both recursive
schemas and the unchanged branch-return cases. Wrong selected endpoints and
missing recursive applications fail. These are finite open-context examples,
not a proof of termination or a contextual execution algorithm.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DeclaredRootControls

open Presentation NativeIndexedFamilies BranchReturnControls

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The positions are obtained by running the shared compiler on the actual
open declarations, not by supplying a positional descriptor as input. -/
theorem recursive_positions_compiled :
    (PayloadSchemaCompilation.compile RecursiveSchemaCertificates.listCons
      Intrinsic.consIotaLeft 4).map (fun plan => List.ofFn plan.positions) =
        some [7, 6, 3, 2, 1, 0] ∧
    (PayloadSchemaCompilation.compile RecursiveSchemaCertificates.relCons
      IntrinsicRelator.consIotaLeft 8).map (fun plan => List.ofFn plan.positions) =
        some [17, 16, 15, 14, 13, 12, 5, 4, 3, 2, 1, 0] := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- An absent payload and a variable without a declared constructor spine
cannot supply a recovery plan. -/
theorem invalid_payload_compilation_rejected :
    (PayloadSchemaCompilation.compile RecursiveSchemaCertificates.listCons
      Intrinsic.consIotaLeft 5).isSome = false ∧
    (PayloadSchemaCompilation.compile RecursiveSchemaCertificates.listCons
      Intrinsic.consIotaLeft 0).isSome = false := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- A recognized, typed nil payload still lacks the head and tail needed
by the recursive schema. Recognition alone is insufficient. -/
theorem missing_schema_variables_rejected :
    (DeclarationSpineReplay.declaredType (Intrinsic.nilApp (.var (5 : Fin 6)))).isSome = true ∧
    (DeclarationSpineReplay.combinedArguments Intrinsic.consIotaLeft
      (Intrinsic.nilApp (.var 5))).isSome = true ∧
    (PayloadSchemaCompilation.compilePositions Intrinsic.contextAPZSHeadTail
      Intrinsic.consIotaLeft (Intrinsic.nilApp (.var 5))).isSome = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem recursive_roots_execute :
    runExecution Intrinsic.contextAPZSHeadTail Intrinsic.consIotaLeft Intrinsic.consIotaResultType
      Intrinsic.consIotaRight NativeRelatorRootConversionCode.Examples.listConsCode
      (runner := DeclaredRootExecution.checkedExecute) = true ∧
    runExecution IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
      IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaResultType IntrinsicRelator.consIotaRight
      NativeRelatorRootConversionCode.Examples.relConsCode
      (runner := DeclaredRootExecution.checkedExecute) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem recursive_displayed_conversion_retained :
    runExecution Intrinsic.contextAPZSHeadTail Intrinsic.consIotaLeft Intrinsic.consIotaResultType
      Intrinsic.consIotaRight NativeRelatorRootConversionCode.Examples.listConsCode true
      (runner := DeclaredRootExecution.checkedExecute) = true ∧
    runExecution IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
      IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaResultType IntrinsicRelator.consIotaRight
      NativeRelatorRootConversionCode.Examples.relConsCode true
      (runner := DeclaredRootExecution.checkedExecute) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem branch_roots_still_execute :
    runExecution Intrinsic.contextAPZS Intrinsic.nilIotaLeft Intrinsic.nilIotaResultType
      Intrinsic.nilIotaRight NativeRelatorRootConversionCode.Examples.listNilCode
      (runner := DeclaredRootExecution.checkedExecute) = true ∧
    runExecution Intrinsic.contextAXPD Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
      Intrinsic.identityIotaRight NativeRelatorRootConversionCode.Examples.identityCode
      (runner := DeclaredRootExecution.checkedExecute) = true ∧
    runExecution IntrinsicRelator.contextABRPZS IntrinsicRelator.nilIotaLeft
      IntrinsicRelator.nilIotaResultType IntrinsicRelator.nilIotaRight
      NativeRelatorRootConversionCode.Examples.relNilCode
      (runner := DeclaredRootExecution.checkedExecute) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem missing_recursive_result_rejected :
    runExecution Intrinsic.contextAPZSHeadTail Intrinsic.consIotaLeft Intrinsic.consIotaResultType
      (.app (.app (.var 2) (.var 1)) (.var 0)) NativeRelatorRootConversionCode.Examples.listConsCode
      (runner := DeclaredRootExecution.checkedExecute) = false ∧
    runExecution IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
      IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaResultType (.var 6)
      NativeRelatorRootConversionCode.Examples.relConsCode
      (runner := DeclaredRootExecution.checkedExecute) = false := by
  decide +kernel

/-- The proposal must check at its own inferred type before rejection at the
requested result type counts as a control. An absent proposal is a failed test. -/
private def checksOnlyAtOwnType {n : Nat} (context : Tower.Ctx n) (contextCode : ContextCode n)
    (subject requested : Tower.Tm n) : Bool :=
  match CertificateProposal.term 64 context subject with
  | none => false
  | some (ownType, code) =>
      check context subject ownType contextCode code &&
        !check context subject requested contextCode code

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Without the recursive argument, both partial branch applications remain
well typed functions, but neither checks as the required dependent result. -/
theorem omitted_recursion_has_wrong_type :
    checksOnlyAtOwnType RecursiveSchemaCertificates.listContext.raw
      RecursiveSchemaCertificates.listContext.code
      (.app (.app (.var (2 : Fin 6)) (.var (1 : Fin 6))) (.var (0 : Fin 6)))
      RecursiveSchemaCertificates.listCons.type = true ∧
    checksOnlyAtOwnType RecursiveSchemaCertificates.relationContext.raw
      RecursiveSchemaCertificates.relationContext.code
      (.app (.app (.app (.app (.app (.app (.var (6 : Fin 12)) (.var (5 : Fin 12)))
        (.var (4 : Fin 12))) (.var (3 : Fin 12))) (.var (2 : Fin 12)))
        (.var (1 : Fin 12))) (.var (0 : Fin 12))) RecursiveSchemaCertificates.relCons.type = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem changed_relational_witness_rejected :
    runExecution IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
      IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaResultType IntrinsicRelator.consIotaRight
      (.relCons (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
        (.var 5) (.var 4) (.var 3) (.var 2) (.var 0) (.var 0))
      (runner := DeclaredRootExecution.checkedExecute) = false := by
  decide +kernel

#print axioms recursive_roots_execute
#print axioms recursive_positions_compiled
#print axioms invalid_payload_compilation_rejected
#print axioms missing_schema_variables_rejected
#print axioms recursive_displayed_conversion_retained
#print axioms branch_roots_still_execute
#print axioms missing_recursive_result_rejected
#print axioms omitted_recursion_has_wrong_type
#print axioms changed_relational_witness_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DeclaredRootControls
