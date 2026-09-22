import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeDeclaredRootExecution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeDependentCongruence

/-!
# Selected contextual computation of native typing certificates

The selected structural step determines a unique occurrence and its endpoints.
Execution recursively transforms the corresponding premise certificate,
transports dependent indices and binder contexts, and replays the original
outer result conversions. The public boundary independently checks source,
result and selected step. It does not choose a reduction strategy.

The dependent-context transformations have general checking theorems. The
driver's public soundness follows from its independent replay gates. The
companion `NativeContextualComputationCompleteness` proves total success on
every admitted source matching a supplied contextual step.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.ContextualComputation

open Presentation StructuralTypingReplay NativeIndexedFamilies

def decodeStep {n : Nat} (step : NativeRelatorConversionChecking.StepCode n) :=
  StructuralConversionCode.StepCode.decode Tower.HeadEq NativeRelatorRootConversionCode.decode step

/-- Transform the selected premise, then restore the enclosing source's exact
result wrapper. This helper neither invents nor reorders conversion evidence. -/
def atPrincipal {n : Nat} (displayed : Tower.Tm n) (code : Code n)
    (transform : Tower.Tm n → Code n → Option (Code n)) : Option (Code n) := do
  let view ← code.principalView displayed
  let output ← transform view.type view.code
  return view.tail.fill output

theorem atPrincipal_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source target displayed : Tower.Tm n} {code : Code n}
    (transform : Tower.Tm n → Code n → Option (Code n))
    (accepted : check context source displayed contextCode code = true)
    (principalChecked : ∀ type principal, principal.isPrincipal = true →
      check context source type contextCode principal = true →
      ∃ output, transform type principal = some output ∧
        check context target type contextCode output = true) :
    ∃ output, atPrincipal displayed code transform = some output ∧
      check context target displayed contextCode output = true := by
  have inputs := accepted
  simp only [check, checkJudgment, Bool.and_eq_true] at inputs
  obtain ⟨view, computed, innerChecked, replay⟩ :=
    Code.principalView_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check code inputs.2
  have fullInner : check context source view.type contextCode view.code = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 innerChecked
  obtain ⟨replacement, replaced, replacementChecked⟩ := principalChecked view.type view.code
    (Code.principalView_reconstruct code computed).2 fullInner
  refine ⟨view.tail.fill replacement, ?_, ?_⟩
  · simp only [atPrincipal, computed, replaced, bind, Option.bind, pure]
  · simp only [check, checkJudgment, Bool.and_eq_true] at replacementChecked ⊢
    exact ⟨inputs.1, replay target replacement replacementChecked.2⟩

def execute : {n : Nat} → NativeRelatorConversionChecking.StepCode n →
    ContextCode n → Tower.Tm n → Code n → Option (Code n)
  | _, .betaPi body argument, contextCode, displayed, code =>
      (PrincipalComputation.execute contextCode (.app (.lam body) argument) displayed code).map (·.code)
  | _, .betaSigmaFst first second, contextCode, displayed, code =>
      (PrincipalComputation.execute contextCode (.fst (.pair first second)) displayed code).map (·.code)
  | _, .betaSigmaSnd first second, contextCode, displayed, code =>
      (PrincipalComputation.execute contextCode (.snd (.pair first second)) displayed code).map (·.code)
  | _, .root root, contextCode, displayed, code =>
      (DeclaredRootExecution.execute contextCode displayed code root).map (·.code)
  | _, .head left right, contextCode, displayed, code =>
      atPrincipal displayed code fun type principal =>
        DependentCongruence.restoreResult contextCode (.head left) type
          (.head (TowerDecisions.headTarget right)) principal .headType
          (.single (.head (TowerDecisions.headTarget right) (TowerDecisions.headTarget left)))
  | _, .congPiDom nested body, contextCode, displayed, code =>
      atPrincipal displayed code fun _ principal => do
        let (_, next) ← decodeStep nested
        let .piForm u v domain bodyCode := principal | none
        let newDomain ← execute nested contextCode (.head u) domain
        return DependentCongruence.piDomain next body u v domain newDomain bodyCode (.single nested)
  | _, .congSigmaDom nested body, contextCode, displayed, code =>
      atPrincipal displayed code fun _ principal => do
        let (_, next) ← decodeStep nested
        let .sigmaForm u v domain bodyCode := principal | none
        let newDomain ← execute nested contextCode (.head u) domain
        return DependentCongruence.sigmaDomain next body u v domain newDomain bodyCode (.single nested)
  | _, .congPiCod _ nested, contextCode, displayed, code =>
      atPrincipal displayed code fun _ principal => do
        let .piForm u v domain bodyCode := principal | none
        let newBody ← execute nested (.snoc contextCode u domain) (.head v) bodyCode
        return .piForm u v domain newBody
  | _, .congSigmaCod _ nested, contextCode, displayed, code =>
      atPrincipal displayed code fun _ principal => do
        let .sigmaForm u v domain bodyCode := principal | none
        let newBody ← execute nested (.snoc contextCode u domain) (.head v) bodyCode
        return .sigmaForm u v domain newBody
  | _, .congLam nested, contextCode, displayed, code =>
      atPrincipal displayed code fun type principal => do
        let .pi _ B := type | none
        let .lamIntro level formation bodyCode := principal | none
        let (u, _, domain, _) ← formation.piFormation
        let newBody ← execute nested (.snoc contextCode u domain) B bodyCode
        return .lamIntro level formation newBody
  | _, .congAppFun nested _, contextCode, displayed, code =>
      atPrincipal displayed code fun _ principal => do
        let .appElim A B function argument := principal | none
        let newFunction ← execute nested contextCode (.pi A B) function
        return .appElim A B newFunction argument
  | _, .congAppArg function nested, contextCode, displayed, code =>
      atPrincipal displayed code fun _ principal => do
        let (old, next) ← decodeStep nested
        let .appElim A B functionCode argument := principal | none
        let newArgument ← execute nested contextCode A argument
        DependentCongruence.appArgument contextCode A B function old next
          functionCode argument newArgument (.single nested)
  | _, .congPairFst nested _, contextCode, displayed, code =>
      atPrincipal displayed code fun type principal => do
        let (old, next) ← decodeStep nested
        let .sigma A B := type | none
        let .pairIntro level formation first second := principal | none
        let newFirst ← execute nested contextCode A first
        DependentCongruence.pairFirst B old next level formation newFirst second (.single nested)
  | _, .congPairSnd first nested, contextCode, displayed, code =>
      atPrincipal displayed code fun type principal => do
        let .sigma _ B := type | none
        let .pairIntro level formation firstCode second := principal | none
        let newSecond ← execute nested contextCode (inst0 first B) second
        return .pairIntro level formation firstCode newSecond
  | _, .congFst nested, contextCode, displayed, code =>
      atPrincipal displayed code fun type principal => do
        let .fstElim B pair := principal | none
        let newPair ← execute nested contextCode (.sigma type B) pair
        return .fstElim B newPair
  | _, .congSnd nested, contextCode, displayed, code =>
      atPrincipal displayed code fun _ principal => do
        let (old, next) ← decodeStep nested
        let .sndElim A B pair := principal | none
        let newPair ← execute nested contextCode (.sigma A B) pair
        DependentCongruence.sndArgument contextCode A B old next pair newPair (.single nested)
  | _, .congIdTy nested _ _, contextCode, displayed, code =>
      atPrincipal displayed code fun _ principal => do
        let (old, _) ← decodeStep nested
        let .idForm level formation left right := principal | none
        let newFormation ← execute nested contextCode (.head level) formation
        return DependentCongruence.identityType old level newFormation left right (.single nested)
  | _, .congIdLeft A nested _, contextCode, displayed, code =>
      atPrincipal displayed code fun _ principal => do
        let .idForm level formation left right := principal | none
        let newLeft ← execute nested contextCode A left
        return .idForm level formation newLeft right
  | _, .congIdRight A _ nested, contextCode, displayed, code =>
      atPrincipal displayed code fun _ principal => do
        let .idForm level formation left right := principal | none
        let newRight ← execute nested contextCode A right
        return .idForm level formation left newRight
  | _, .congRefl nested, contextCode, displayed, code =>
      atPrincipal displayed code fun _ principal => do
        let (old, next) ← decodeStep nested
        let .reflIntro A term := principal | none
        let newTerm ← execute nested contextCode A term
        DependentCongruence.reflArgument contextCode A old next term newTerm (.single nested)

/-- Independent replay admits only actual source/result typing and the exact
selected directed step. Failure does not refute typing or normalizability. -/
def checkedExecute {n : Nat} (context : Tower.Ctx n) (contextCode : ContextCode n)
    (subject displayed : Tower.Tm n) (code : Code n) (step : NativeRelatorConversionChecking.StepCode n) :
    Option (PrincipalComputation.Result n) := do
  let (source, target) ← decodeStep step
  if source = subject ∧ check context subject displayed contextCode code = true then
    let output ← execute step contextCode displayed code
    if check context target displayed contextCode output then
      return ⟨target, output, step⟩
    else none
  else none

theorem checkedExecute_sound {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject displayed : Tower.Tm n} {code : Code n} {step : NativeRelatorConversionChecking.StepCode n}
    {result : PrincipalComputation.Result n}
    (computed : checkedExecute context contextCode subject displayed code step = some result) :
    check context subject displayed contextCode code = true ∧ result.step = step ∧
      check context result.term displayed contextCode result.code = true ∧
      NativeRelatorConversionChecking.checkStep step subject result.term = true := by
  unfold checkedExecute at computed
  cases decoded : decodeStep step with
  | none => simp [decoded] at computed
  | some pair =>
      obtain ⟨source, target⟩ := pair
      simp only [decoded, bind, Option.bind] at computed
      split at computed
      · rename_i admitted
        obtain ⟨rfl, accepted⟩ := admitted
        cases executed : execute step contextCode displayed code with
        | none => simp [executed] at computed
        | some output =>
            simp only [executed] at computed
            split at computed
            · rename_i outputChecked
              cases computed
              refine ⟨accepted, rfl, outputChecked, ?_⟩
              exact decide_eq_true decoded
            · contradiction
      · contradiction

def resultReceipt {context : NativeCheckedSubstitution.Context}
    (source : NativeCheckedSubstitution.JudgmentReceipt context)
    (step : NativeRelatorConversionChecking.StepCode context.arity)
    (result : PrincipalComputation.Result context.arity)
    (computed : checkedExecute context.raw context.code source.subject source.type source.code step = some result) :
    NativeCheckedSubstitution.JudgmentReceipt context :=
  ⟨result.term, source.type, result.code, (checkedExecute_sound computed).2.2.1⟩

theorem checkedExecute_observation {context : NativeCheckedSubstitution.Context}
    (source : NativeCheckedSubstitution.JudgmentReceipt context)
    (step : NativeRelatorConversionChecking.StepCode context.arity)
    (result : PrincipalComputation.Result context.arity)
    (computed : checkedExecute context.raw context.code source.subject source.type source.code step = some result) :
    source.observe = (resultReceipt source step result computed).observe :=
  source.observe_eq_of_checkedStep (resultReceipt source step result computed) rfl step
    (checkedExecute_sound computed).2.2.2

#print axioms checkedExecute_sound
#print axioms atPrincipal_checked
#print axioms checkedExecute_observation

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.ContextualComputation
