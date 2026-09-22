import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeBranchReturnExecution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeStructuralCertificateProposal

/-!
# Native branch-return certificate execution controls

The shared finite structural proposal supplies input certificates for
the existing complete checker. It does not supply a typing authority or a
general inference theorem. The tests independently replay source contexts,
source certificates, recovered arguments and computed result certificates.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.BranchReturnControls

open Presentation NativeIndexedFamilies DeclarationSpineReplay

def runChecks {n : Nat} (context : Tower.Ctx n) (subject expectedType target : Tower.Tm n)
    (position : Nat) : Bool :=
  match CertificateProposal.context context, CertificateProposal.term 64 context subject with
  | some contextCode, some (_, sourceCode) =>
      check context subject expectedType contextCode sourceCode &&
      match checkedRecover context contextCode subject expectedType sourceCode,
          returnArgument contextCode subject expectedType sourceCode position with
      | some result, some targetCode =>
          result.arguments.all (fun entry => check context entry.subject entry.type contextCode entry.code) &&
          check context target expectedType contextCode targetCode
      | _, _ => false
  | _, _ => false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem all_branch_arguments_replay :
    runChecks Intrinsic.contextAPZS Intrinsic.nilIotaLeft Intrinsic.nilIotaResultType Intrinsic.nilIotaRight 2 = true ∧
    runChecks Intrinsic.contextAXPD Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType Intrinsic.identityIotaRight 3 = true ∧
    runChecks IntrinsicRelator.contextABRPZS IntrinsicRelator.nilIotaLeft
      IntrinsicRelator.nilIotaResultType IntrinsicRelator.nilIotaRight 4 = true := by
  decide +kernel

def runExecution {n : Nat} (context : Tower.Ctx n) (subject expectedType target : Tower.Tm n)
    (root : NativeRelatorRootConversionCode.Code n) (wrapped : Bool := false)
    (runner : Tower.Ctx n → ContextCode n → Tower.Tm n → Tower.Tm n → Code n →
      NativeRelatorRootConversionCode.Code n → Option (PrincipalComputation.Result n) :=
        BranchReturnExecution.checkedExecute) : Bool :=
  match CertificateProposal.context context, CertificateProposal.term 64 context subject with
  | some contextCode, some (_, originalCode) =>
      let sourceCode := if wrapped then do
          let (.head level, formation) ← CertificateProposal.term 64 context expectedType | none
          return StructuralTypingReplay.Code.convert expectedType level originalCode formation (.refl expectedType)
        else some originalCode
      match sourceCode with
      | none => false
      | some code =>
          match runner context contextCode subject expectedType code root with
          | none => false
          | some result =>
              decide (result.term = target) &&
              check context result.term expectedType contextCode result.code &&
              NativeRelatorConversionChecking.checkStep result.step subject result.term &&
              (if wrapped then match result.code with | .convert .. => true | _ => false else true)
  | _, _ => false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem all_branch_executions_replay :
    runExecution Intrinsic.contextAPZS Intrinsic.nilIotaLeft Intrinsic.nilIotaResultType
      Intrinsic.nilIotaRight NativeRelatorRootConversionCode.Examples.listNilCode = true ∧
    runExecution Intrinsic.contextAXPD Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
      Intrinsic.identityIotaRight NativeRelatorRootConversionCode.Examples.identityCode = true ∧
    runExecution IntrinsicRelator.contextABRPZS IntrinsicRelator.nilIotaLeft
      IntrinsicRelator.nilIotaResultType IntrinsicRelator.nilIotaRight
      NativeRelatorRootConversionCode.Examples.relNilCode = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem displayed_conversion_is_retained :
    runExecution Intrinsic.contextAPZS Intrinsic.nilIotaLeft Intrinsic.nilIotaResultType
      Intrinsic.nilIotaRight NativeRelatorRootConversionCode.Examples.listNilCode true = true ∧
    runExecution Intrinsic.contextAXPD Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
      Intrinsic.identityIotaRight NativeRelatorRootConversionCode.Examples.identityCode true = true ∧
    runExecution IntrinsicRelator.contextABRPZS IntrinsicRelator.nilIotaLeft
      IntrinsicRelator.nilIotaResultType IntrinsicRelator.nilIotaRight
      NativeRelatorRootConversionCode.Examples.relNilCode true = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem changed_result_type_and_root_rejected :
    runExecution Intrinsic.contextAPZS Intrinsic.nilIotaLeft Intrinsic.nilIotaResultType
      (.var 0) NativeRelatorRootConversionCode.Examples.listNilCode = false ∧
    runExecution Intrinsic.contextAPZS Intrinsic.nilIotaLeft (.head (.sort Tower.zero))
      Intrinsic.nilIotaRight NativeRelatorRootConversionCode.Examples.listNilCode = false ∧
    runExecution IntrinsicRelator.contextABRPZS IntrinsicRelator.nilIotaLeft
      IntrinsicRelator.nilIotaResultType IntrinsicRelator.nilIotaRight
      (.relNil (.var 5) (.var 4) (.var 2) (.var 2) (.var 1) (.var 0)) = false := by
  decide +kernel

theorem malformed_source_certificate_rejected :
    (match CertificateProposal.context Intrinsic.contextAPZS with
     | none => false
     | some contextCode =>
         (BranchReturnExecution.checkedExecute Intrinsic.contextAPZS contextCode Intrinsic.nilIotaLeft
           Intrinsic.nilIotaResultType .var NativeRelatorRootConversionCode.Examples.listNilCode).isNone) = true := by
  decide +kernel

private def branchRedex : Tower.Tm 4 := .app (.lam (.var 0)) (.var 1)

private def branchSubstitution : Sub Tower.Head 4 4 :=
  fun index => if index = 1 then branchRedex else .var index

private def branchImageCodes : Option (Fin 4 → Code 4) := do
  let (.head (.sort level), formation) ←
    CertificateProposal.term 64 Intrinsic.contextAPZS Intrinsic.nilIotaResultType | none
  let type := Intrinsic.nilIotaResultType
  let code : Code 4 := .appElim type (Presentation.rename Fin.succ type)
    (.lamIntro (.sort (.max level level))
      (.piForm (.sort level) (.sort level) formation (NativeJudgmentReplay.rename Fin.succ formation))
      .var) .var
  return fun index => if index = 1 then code else .var

/-- Replace the selected nil branch by a genuine beta redex through the
existing checked substitution operation, then execute the instantiated root. -/
def runSubstitutedBranch : Bool :=
  match CertificateProposal.context Intrinsic.contextAPZS,
      CertificateProposal.term 64 Intrinsic.contextAPZS Intrinsic.nilIotaLeft, branchImageCodes with
  | some contextCode, some (_, sourceCode), some imageCodes =>
      let subject := subst branchSubstitution Intrinsic.nilIotaLeft
      let type := subst branchSubstitution Intrinsic.nilIotaResultType
      let code := NativeJudgmentReplay.substitute branchSubstitution imageCodes
        Intrinsic.nilIotaLeft Intrinsic.nilIotaResultType sourceCode
      let root := NativeRelatorRootConversionCode.substitute branchSubstitution
        NativeRelatorRootConversionCode.Examples.listNilCode
      TelescopeArgumentChecking.checkArguments
        (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
          Intrinsic.contextAPZS) Intrinsic.contextAPZS branchSubstitution imageCodes &&
      match BranchReturnExecution.checkedExecute Intrinsic.contextAPZS contextCode subject type code root with
      | some output => decide (output.term = branchRedex) &&
          check Intrinsic.contextAPZS output.term type contextCode output.code &&
          NativeRelatorConversionChecking.checkStep output.step subject output.term
      | none => false
  | _, _, _ => false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem nonvariable_branch_substitution_executes : runSubstitutedBranch = true := by decide +kernel

set_option maxRecDepth 10000 in
theorem nonvariable_image_with_variable_certificate_rejected :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
        Intrinsic.contextAPZS) Intrinsic.contextAPZS branchSubstitution (fun _ => .var) = false := by
  decide +kernel

#print axioms all_branch_arguments_replay
#print axioms all_branch_executions_replay
#print axioms displayed_conversion_is_retained
#print axioms changed_result_type_and_root_rejected
#print axioms malformed_source_certificate_rejected
#print axioms nonvariable_branch_substitution_executes
#print axioms nonvariable_image_with_variable_certificate_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.BranchReturnControls
