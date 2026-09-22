import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeContextualComputationReplay

/-!
# Dependent contextual certificate execution controls

The source and actual output are independently replayed. The controls retain
dependent annotations, transport a second component when its first changes,
and exercise binder conversion and capture avoidance. A missing output fails
the test. These finite controls do not prove the driver's general totality.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.ContextualComputationControls

open Presentation NativeIndexedFamilies StructuralTypingReplay
open NativeRelatorConversionChecking.Examples (ground betaArgument)
open NativeJudgmentReplay.Controls (context contextCode betaArgumentCode)

private def zero : Tower.Head := .sort Tower.zero
private def joined : Tower.Head := .sort (.max Tower.zero Tower.zero)
private def beta : NativeRelatorConversionChecking.StepCode 1 := .betaPi (.var 0) (.var 0)

def run {n : Nat} (context : Tower.Ctx n) (contextCode : ContextCode n)
    (source type expected : Tower.Tm n) (code : Code n)
    (step : NativeRelatorConversionChecking.StepCode n) : Bool :=
  check context source type contextCode code &&
    match ContextualComputation.checkedExecute context contextCode source type code step with
    | none => false
    | some result => decide (result.term = expected) &&
        check context result.term type contextCode result.code &&
        NativeRelatorConversionChecking.checkStep result.step source result.term

theorem dependent_argument_executes :
    run context contextCode FormationControls.application FormationControls.applicationType
      (.app (.lam (.refl (.var 0))) (.var 0)) FormationControls.applicationCode
      (.congAppArg (.lam (.refl (.var 0))) beta) = true := by decide +kernel

private def family : Tower.Tm 2 := .id ground (.var 0) (.var 0)
private def pairType : Tower.Tm 1 := .sigma ground family
private def pairFormation : Code 1 :=
  .sigmaForm zero zero .headType (.idForm zero .headType .var .var)
private def pair : Tower.Tm 1 := .pair (betaArgument (.var 0)) (.refl (betaArgument (.var 0)))
private def pairCode : Code 1 :=
  .pairIntro joined pairFormation betaArgumentCode (.reflIntro ground betaArgumentCode)
private def nextPair : Tower.Tm 1 := .pair (.var 0) (.refl (betaArgument (.var 0)))
private def pairStep : NativeRelatorConversionChecking.StepCode 1 :=
  .congPairFst beta (.refl (betaArgument (.var 0)))

theorem dependent_first_component_executes :
    run context contextCode pair pairType nextPair pairCode pairStep = true := by decide +kernel

theorem dependent_projection_below_pair_executes :
    run context contextCode (.snd pair) (inst0 (.fst pair) family) (.snd nextPair)
      (.sndElim ground family pairCode) (.congSnd pairStep) = true := by decide +kernel

theorem unchanged_second_component_rejected :
    check context nextPair pairType contextCode
      (.pairIntro joined pairFormation .var (.reflIntro ground betaArgumentCode)) = false := by
  decide +kernel

theorem refl_and_identity_endpoints_execute :
    run context contextCode (.refl (betaArgument (.var 0)))
      (.id ground (betaArgument (.var 0)) (betaArgument (.var 0))) (.refl (.var 0))
      (.reflIntro ground betaArgumentCode) (.congRefl beta) = true ∧
    run context contextCode (.id ground (betaArgument (.var 0)) (.var 0)) (.head zero)
      (.id ground (.var 0) (.var 0)) (.idForm zero .headType betaArgumentCode .var)
      (.congIdLeft ground beta (.var 0)) = true ∧
    run context contextCode (.id ground (.var 0) (betaArgument (.var 0))) (.head zero)
      (.id ground (.var 0) (.var 0)) (.idForm zero .headType .var betaArgumentCode)
      (.congIdRight ground (.var 0) beta) = true := by decide +kernel

private def oldDomain : Tower.Tm 1 := .app (.lam ground) (.var 0)
private def oldDomainCode : Code 1 :=
  .appElim ground (.head zero)
    (.lamIntro (.sort (.max Tower.zero (.succ Tower.zero)))
      (.piForm zero (.sort (.succ Tower.zero)) .headType .headType) .headType) .var
private def domainStep : NativeRelatorConversionChecking.StepCode 1 := .betaPi ground (.var 0)
private def oldPointCode : Code 1 :=
  .convert ground zero .var oldDomainCode (.symm (.single domainStep))

theorem identity_type_executes :
    run context contextCode (.id oldDomain (.var 0) (.var 0)) (.head zero)
      (.id ground (.var 0) (.var 0)) (.idForm zero oldDomainCode oldPointCode oldPointCode)
      (.congIdTy domainStep (.var 0) (.var 0)) = true := by decide +kernel

private def binderBody : Tower.Tm 2 := .id (Presentation.rename wk oldDomain) (.var 0) (.var 0)
private def binderBodyCode : Code 2 :=
  .idForm zero (NativeJudgmentReplay.rename wk oldDomainCode) .var .var

theorem binder_domains_execute :
    run context contextCode (.pi oldDomain binderBody) (.head joined) (.pi ground binderBody)
      (.piForm zero zero oldDomainCode binderBodyCode) (.congPiDom domainStep binderBody) = true ∧
    run context contextCode (.sigma oldDomain binderBody) (.head joined) (.sigma ground binderBody)
      (.sigmaForm zero zero oldDomainCode binderBodyCode) (.congSigmaDom domainStep binderBody) = true := by
  decide +kernel

theorem untransported_binder_body_rejected :
    check context (.pi ground binderBody) (.head joined) contextCode
      (.piForm zero zero .headType binderBodyCode) = false := by decide +kernel

private def underBinderTerm : Tower.Tm 2 := .refl (betaArgument (.var 1))
private def underBinderType : Tower.Tm 2 := .id ground (betaArgument (.var 1)) (betaArgument (.var 1))
private def underBinderCode : Code 2 := .reflIntro ground (NativeJudgmentReplay.rename wk betaArgumentCode)
private def underBinderFormation : Code 2 :=
  .idForm zero .headType (NativeJudgmentReplay.rename wk betaArgumentCode)
    (NativeJudgmentReplay.rename wk betaArgumentCode)
private def lambdaType : Tower.Tm 1 := .pi ground underBinderType
private def lambdaCode : Code 1 :=
  .lamIntro joined (.piForm zero zero .headType underBinderFormation) underBinderCode
private def lambdaStep : NativeRelatorConversionChecking.StepCode 1 :=
  .congLam (.congRefl (.betaPi (.var 0) (.var 1)))

theorem ambient_variable_survives_binder :
    run context contextCode (.lam underBinderTerm) lambdaType (.lam (.refl (.var 1)))
      lambdaCode lambdaStep = true := by decide +kernel

theorem captured_result_rejected :
    run context contextCode (.lam underBinderTerm) lambdaType (.lam (.refl (.var 0)))
      lambdaCode lambdaStep = false := by decide +kernel

theorem remaining_constructor_positions_execute :
    run context contextCode (.app (.lam underBinderTerm) (.var 0)) (inst0 (.var 0) underBinderType)
      (.app (.lam (.refl (.var 1))) (.var 0)) (.appElim ground underBinderType lambdaCode .var)
      (.congAppFun lambdaStep (.var 0)) = true ∧
    run context contextCode pair pairType (.pair (betaArgument (.var 0)) (.refl (.var 0))) pairCode
      (.congPairSnd (betaArgument (.var 0)) (.congRefl beta)) = true ∧
    run context contextCode (.fst pair) ground (.fst nextPair) (.fstElim family pairCode)
      (.congFst pairStep) = true ∧
    run context contextCode (.pi ground underBinderType) (.head joined)
      (.pi ground (.id ground (.var 1) (betaArgument (.var 1))))
      (.piForm zero zero .headType underBinderFormation)
      (.congPiCod ground (.congIdLeft ground (.betaPi (.var 0) (.var 1)) (betaArgument (.var 1)))) = true ∧
    run context contextCode (.sigma ground underBinderType) (.head joined)
      (.sigma ground (.id ground (.var 1) (betaArgument (.var 1))))
      (.sigmaForm zero zero .headType underBinderFormation)
      (.congSigmaCod ground (.congIdLeft ground (.betaPi (.var 0) (.var 1)) (betaArgument (.var 1)))) = true := by
  decide +kernel

theorem equal_levels_need_successor_conversion :
    run (.nil : Tower.Ctx 0) .nil (.head zero) (.head (.sort (.succ Tower.zero)))
      (.head (.sort (.max Tower.zero Tower.zero))) .headType
      (.head zero (.sort (.max Tower.zero Tower.zero))) = true ∧
    check (.nil : Tower.Ctx 0) (.head (.sort (.max Tower.zero Tower.zero)))
      (.head (.sort (.succ Tower.zero))) .nil .headType = false := by decide +kernel

#print axioms dependent_argument_executes
#print axioms dependent_first_component_executes
#print axioms dependent_projection_below_pair_executes
#print axioms unchanged_second_component_rejected
#print axioms refl_and_identity_endpoints_execute
#print axioms identity_type_executes
#print axioms binder_domains_execute
#print axioms untransported_binder_body_rejected
#print axioms ambient_variable_survives_binder
#print axioms captured_result_rejected
#print axioms remaining_constructor_positions_execute
#print axioms equal_levels_need_successor_conversion

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.ContextualComputationControls
