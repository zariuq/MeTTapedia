import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedPathExecution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeStructuralCertificateProposal

/-!
# Finite native execution: dependent results, J and exact trace retention

These controls independently check the original and returned certificates.
Term-only admission is compared with certificate-producing execution; wrong
order, disconnected steps, malformed evidence and a changed dependent result
are rejected. Repeated selected steps are retained even at equal endpoints.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedPathExecution.Controls

open Presentation NativeIndexedFamilies NativeJudgmentReplay
open NativeRelatorConversionChecking.Examples (ground betaArgument)

private def sameTerm {n : Nat} (left right : Tower.Tm n) : Bool := decide (left = right)

def replay {n : Nat} (context : Tower.Ctx n) (contextCode : ContextCode n)
    (source displayed expected : Tower.Tm n) (input : Code n)
    (codes : List (NativeRelatorConversionChecking.StepCode n)) : Bool :=
  if formed : StructuralTypingReplay.checkContext IntrinsicRelator.rules
      NativeRelatorConversionChecking.check context contextCode = true then
    let checkedContext : NativeCheckedSubstitution.Context := ⟨n, context, contextCode, formed⟩
    match runCodes checkedContext source displayed input codes, decodeSteps source codes with
    | some (target, output), some path =>
        sameTerm target expected && sameTerm path.1 expected &&
        check context target displayed contextCode output &&
        decide (path.2.length = codes.length)
    | _, _ => false
  else false

private def argumentStep : NativeRelatorConversionChecking.StepCode 1 :=
  .congAppArg (.lam (.refl (.var 0))) (.betaPi (.var 0) (.var 0))

private def outerStep : NativeRelatorConversionChecking.StepCode 1 :=
  .betaPi (.refl (.var 0)) (.var 0)

theorem dependent_two_step_execution :
    replay NativeJudgmentReplay.Controls.context NativeJudgmentReplay.Controls.contextCode
      FormationControls.application FormationControls.applicationType (.refl (.var 0))
      FormationControls.applicationCode [argumentStep, outerStep] = true := by decide +kernel

theorem disconnected_order_rejected :
    (decodeSteps FormationControls.application [outerStep, argumentStep]).isNone = true ∧
    (decodeSteps FormationControls.application [argumentStep, argumentStep]).isNone = true := by
  decide +kernel

theorem malformed_source_and_changed_result_rejected :
    replay NativeJudgmentReplay.Controls.context NativeJudgmentReplay.Controls.contextCode
      FormationControls.application FormationControls.applicationType (.refl (.var 0))
      .var [argumentStep, outerStep] = false ∧
    replay NativeJudgmentReplay.Controls.context NativeJudgmentReplay.Controls.contextCode
      FormationControls.application FormationControls.applicationType (.var 0)
      FormationControls.applicationCode [argumentStep, outerStep] = false := by decide +kernel

def proposedReplay {n : Nat} (context : Tower.Ctx n) (source displayed expected : Tower.Tm n)
    (codes : List (NativeRelatorConversionChecking.StepCode n)) : Bool :=
  match CertificateProposal.context context, CertificateProposal.term 64 context source with
  | some contextCode, some (_, input) => replay context contextCode source displayed expected input codes
  | _, _ => false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- J is a declared constant whose reflexivity equation is a selected native
root, not a missing primitive typing constructor. Its actual returned branch
is accepted at the original dependent motive application. -/
theorem declared_identity_elimination_executes :
    proposedReplay Intrinsic.contextAXPD Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
      Intrinsic.identityIotaRight [.root NativeRelatorRootConversionCode.Examples.identityCode] = true := by
  decide +kernel

private def level : Tower.Head := .sort Tower.zero
private def repeatedStep : NativeRelatorConversionChecking.StepCode 0 := .head level level

theorem repeated_steps_are_not_deduplicated :
    ((decodeSteps (.head level) [repeatedStep, repeatedStep]).map (fun path => path.2.length)) = some 2 ∧
    ((decodeSteps (n := 0) (.head level) []).map (fun path => path.2.length)) = some 0 ∧
    replay (.nil : Tower.Ctx 0) .nil (.head level) (.head (.sort (.succ Tower.zero))) (.head level)
      .headType [repeatedStep, repeatedStep] = true := by decide +kernel

/-- Formation extraction cannot replace typing-certificate admission even
on the old public input shape: replacing a genuine application tree by a
variable code neither infers nor recovers that application. -/
theorem formation_is_not_typing_reconstruction :
    (checkedResultFormation NativeJudgmentReplay.Controls.context FormationControls.application
      FormationControls.applicationType NativeJudgmentReplay.Controls.contextCode .var).isNone = true := by
  decide +kernel

#print axioms dependent_two_step_execution
#print axioms disconnected_order_rejected
#print axioms malformed_source_and_changed_result_rejected
#print axioms declared_identity_elimination_executes
#print axioms repeated_steps_are_not_deduplicated
#print axioms formation_is_not_typing_reconstruction

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedPathExecution.Controls
