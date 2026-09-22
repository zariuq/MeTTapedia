import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayGeneration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeIntroductionComputationReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeConvertedIntroductionComputation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Contextual.NativeCheckedJudgmentPresheaf

/-!
# Native computation beneath result-conversion certificates

The supplied typing certificate is split at its actual principal rule. A
primitive introduction/elimination computation replaces that principal proof,
and the original cumulative/conversion wrapper is replayed unchanged. Both
the output judgment and its directed computation step are checked.

The executor recognizes lambda/pair eliminations beneath arbitrarily many
outer result wrappers and through arbitrary converted inner introduction
evidence. Direct introductions keep their previous output certificates;
converted premises use computed component alignment. Declared native roots
and reduction below term constructors remain separate execution obligations.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay
namespace PrincipalComputation

open Presentation StructuralTypingReplay NativeIndexedFamilies

structure Result (n : Nat) where
  term : Tower.Tm n
  code : Code n
  step : NativeRelatorConversionChecking.StepCode n

def direct {n : Nat} (contextCode : ContextCode n) (subject type : Tower.Tm n)
    (code : Code n) : Option (Result n) :=
  match subject, code with
  | .app (.lam body) argument, .appElim _ B (.lamIntro _ _ bodyCode) argumentCode =>
      some ⟨inst0 argument body,
        IntroductionComputation.betaPi body B argument bodyCode argumentCode, .betaPi body argument⟩
  | .fst (.pair first second), .fstElim _ (.pairIntro _ _ firstCode _) =>
      some ⟨first, firstCode, .betaSigmaFst first second⟩
  | .snd (.pair first second), .sndElim A B (.pairIntro u formation firstCode secondCode) =>
      (IntroductionComputation.betaSigmaSnd contextCode A B first second u formation firstCode secondCode).map
        fun code => ⟨second, code, .betaSigmaSnd first second⟩
  | .app (.lam body) argument, .appElim A B functionCode argumentCode =>
      (ConvertedIntroductionComputation.betaPi contextCode A B body argument functionCode argumentCode).map
        fun code => ⟨inst0 argument body, code, .betaPi body argument⟩
  | .fst (.pair first second), .fstElim B pairCode =>
      (ConvertedIntroductionComputation.betaSigmaFst contextCode type B first second pairCode).map
        fun code => ⟨first, code, .betaSigmaFst first second⟩
  | .snd (.pair first second), .sndElim A B pairCode =>
      (ConvertedIntroductionComputation.betaSigmaSnd contextCode A B first second pairCode).map
        fun code => ⟨second, code, .betaSigmaSnd first second⟩
  | _, _ => none

/-- Syntactic domain of the current root executor, not an admission test. -/
def directShape {n : Nat} (subject : Tower.Tm n) (code : Code n) : Bool :=
  match subject, code with
  | .app (.lam _) _, .appElim .. => true
  | .fst (.pair ..), .fstElim .. => true
  | .snd (.pair ..), .sndElim .. => true
  | _, _ => false

theorem direct_domain {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject type : Tower.Tm n} {code : Code n}
    (accepted : check context subject type contextCode code = true) :
    (direct contextCode subject type code).isSome = directShape subject code := by
  unfold direct directShape
  split
  · rfl
  · rfl
  · have inputs := accepted
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq] at inputs
    have typeEq := inputs.2.2
    subst type
    obtain ⟨result, computed, _⟩ := IntroductionComputation.betaSigmaSnd_checked accepted
    simp only [computed, Option.map_some, Option.isSome_some]
  · have inputs := accepted
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq] at inputs
    have typeEq := inputs.2.2
    subst type
    obtain ⟨result, computed, _⟩ := ConvertedIntroductionComputation.betaPi_checked accepted
    simp only [computed, Option.map_some, Option.isSome_some]
  · obtain ⟨result, computed, _⟩ := ConvertedIntroductionComputation.betaSigmaFst_checked accepted
    simp only [computed, Option.map_some, Option.isSome_some]
  · have inputs := accepted
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq] at inputs
    have typeEq := inputs.2.2
    subst type
    obtain ⟨result, computed, _⟩ := ConvertedIntroductionComputation.betaSigmaSnd_checked accepted
    simp only [computed, Option.map_some, Option.isSome_some]
  · split <;> simp_all <;> (apply_assumption <;> rfl)

theorem direct_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject type : Tower.Tm n} {code : Code n} {result : Result n}
    (accepted : check context subject type contextCode code = true)
    (computed : direct contextCode subject type code = some result) :
    check context result.term type contextCode result.code = true ∧
      NativeRelatorConversionChecking.checkStep result.step subject result.term = true := by
  unfold direct at computed
  split at computed
  · rename_i body argument A B u formation bodyCode argumentCode
    have typeEq := accepted
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq] at typeEq
    have eqType := typeEq.2.2
    subst type
    cases computed
    exact IntroductionComputation.betaPi_checked accepted
  · cases computed
    exact IntroductionComputation.betaSigmaFst_checked accepted
  · rename_i first second A B u formation firstCode secondCode
    have typeEq := accepted
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq] at typeEq
    have eqType := typeEq.2.2
    subst type
    obtain ⟨resultCode, equation, checked, stepChecked⟩ :=
      IntroductionComputation.betaSigmaSnd_checked accepted
    simp only [equation, Option.map_some, Option.some.injEq] at computed
    subst result
    exact ⟨checked, stepChecked⟩
  · have inputs := accepted
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq] at inputs
    have typeEq := inputs.2.2
    subst type
    obtain ⟨resultCode, equation, checked⟩ := ConvertedIntroductionComputation.betaPi_checked accepted
    simp only [equation, Option.map_some, Option.some.injEq] at computed
    subst result
    refine ⟨checked, ?_⟩
    simp [NativeRelatorConversionChecking.checkStep, StructuralConversionCode.StepCode.check,
      StructuralConversionCode.StepCode.decode]
  · obtain ⟨resultCode, equation, checked⟩ := ConvertedIntroductionComputation.betaSigmaFst_checked accepted
    simp only [equation, Option.map_some, Option.some.injEq] at computed
    subst result
    refine ⟨checked, ?_⟩
    simp [NativeRelatorConversionChecking.checkStep, StructuralConversionCode.StepCode.check,
      StructuralConversionCode.StepCode.decode]
  · have inputs := accepted
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq] at inputs
    have typeEq := inputs.2.2
    subst type
    obtain ⟨resultCode, equation, checked⟩ := ConvertedIntroductionComputation.betaSigmaSnd_checked accepted
    simp only [equation, Option.map_some, Option.some.injEq] at computed
    subst result
    refine ⟨checked, ?_⟩
    simp [NativeRelatorConversionChecking.checkStep, StructuralConversionCode.StepCode.check,
      StructuralConversionCode.StepCode.decode]
  · contradiction

/-- Reuse precisely the source's result-type wrapper, including its formation
and conversion evidence. This does not normalize or replace the displayed type. -/
def execute {n : Nat} (contextCode : ContextCode n) (subject type : Tower.Tm n)
    (code : Code n) : Option (Result n) :=
  (code.principalView type).bind fun view =>
    (direct contextCode subject view.type view.code).map fun result =>
      { result with code := view.tail.fill result.code }

theorem execute_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject type : Tower.Tm n} {code : Code n} {result : Result n}
    (accepted : check context subject type contextCode code = true)
    (computed : execute contextCode subject type code = some result) :
    check context result.term type contextCode result.code = true ∧
      NativeRelatorConversionChecking.checkStep result.step subject result.term = true := by
  have inputs := accepted
  simp only [check, checkJudgment, Bool.and_eq_true] at inputs
  obtain ⟨view, viewComputed, viewChecked, replay⟩ :=
    StructuralTypingReplay.Code.principalView_checked IntrinsicRelator.rules
      NativeRelatorConversionChecking.check code inputs.2
  simp only [execute, viewComputed, Option.bind_some] at computed
  cases directComputed : direct contextCode subject view.type view.code with
  | none => simp [directComputed] at computed
  | some principal =>
      simp only [directComputed, Option.map_some, Option.some.injEq] at computed
      subst result
      have principalAccepted : check context subject view.type contextCode view.code = true :=
        by simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 viewChecked
      obtain ⟨principalChecked, stepChecked⟩ := direct_checked principalAccepted directComputed
      simp only [check, checkJudgment, Bool.and_eq_true] at principalChecked ⊢
      exact ⟨⟨inputs.1, replay principal.term principal.code principalChecked.2⟩, stepChecked⟩

/-- Public admission gate: an unaccepted source certificate cannot produce
an execution receipt, even when its raw principal node is recognizable. -/
def checkedExecute {n : Nat} (context : Tower.Ctx n) (contextCode : ContextCode n)
    (subject type : Tower.Tm n) (code : Code n) : Option (Result n) :=
  if check context subject type contextCode code then execute contextCode subject type code else none

/-- On every admitted judgment, success is exactly the stated syntactic
domain after extraction of the actual principal rule. In particular the
dependent projection's formation computation cannot introduce another failure. -/
theorem checkedExecute_domain {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject type : Tower.Tm n} {code : Code n}
    (accepted : check context subject type contextCode code = true) :
    (checkedExecute context contextCode subject type code).isSome =
      ((code.principalView type).map fun view => directShape subject view.code).getD false := by
  have inputs := accepted
  simp only [check, checkJudgment, Bool.and_eq_true] at inputs
  obtain ⟨view, computed, principalChecked, _⟩ :=
    StructuralTypingReplay.Code.principalView_checked IntrinsicRelator.rules
      NativeRelatorConversionChecking.check code inputs.2
  have principalAccepted : check context subject view.type contextCode view.code = true :=
    by simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 principalChecked
  simp only [checkedExecute, accepted, ↓reduceIte, execute, computed, Option.bind_some,
    Option.map_some, Option.getD_some, Option.isSome_map]
  exact direct_domain principalAccepted

theorem checkedExecute_sound {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject type : Tower.Tm n} {code : Code n} {result : Result n}
    (computed : checkedExecute context contextCode subject type code = some result) :
    check context subject type contextCode code = true ∧
      check context result.term type contextCode result.code = true ∧
      NativeRelatorConversionChecking.checkStep result.step subject result.term = true := by
  unfold checkedExecute at computed
  split at computed
  · rename_i accepted
    exact ⟨accepted, execute_checked accepted computed⟩
  · contradiction

/-- The checked output inhabits the original receipt's type. Its observation
agrees with the source because the returned step is actual native computation. -/
def resultReceipt {context : NativeCheckedSubstitution.Context}
    (source : NativeCheckedSubstitution.JudgmentReceipt context) (result : Result context.arity)
    (computed : execute context.code source.subject source.type source.code = some result) :
    NativeCheckedSubstitution.JudgmentReceipt context :=
  ⟨result.term, source.type, result.code, (execute_checked source.accepted computed).1⟩

theorem execute_observation {context : NativeCheckedSubstitution.Context}
    (source : NativeCheckedSubstitution.JudgmentReceipt context) (result : Result context.arity)
    (computed : execute context.code source.subject source.type source.code = some result) :
    source.observe = (resultReceipt source result computed).observe := by
  exact source.observe_eq_of_checkedStep (resultReceipt source result computed) rfl
    result.step (execute_checked source.accepted computed).2

namespace Controls

open NativeRelatorConversionChecking.Examples (ground)

private def zero : Tower.Head := .sort Tower.zero
private def one : Tower.Head := .sort (.succ Tower.zero)
private def two : Tower.Head := .sort (.succ (.succ Tower.zero))

def universeApplication : Tower.Tm 0 := .app (.lam (.var 0)) ground

def universeApplicationCode : Code 0 :=
  .appElim (.head zero) (.head zero)
    (.lamIntro (.sort (.max (.succ Tower.zero) (.succ Tower.zero)))
      (.piForm one one .headType .headType) .var) .headType

/-- Conversion above a cumulative lift, and another cumulative lift above
that conversion. The source proof must retain this ordering. -/
def raisedCode : Code 0 :=
  .cumul one (.convert (.head one) two (.cumul zero universeApplicationCode)
    .headType (.refl (.head one)))

def raisedResultCode : Code 0 :=
  .cumul one (.convert (.head one) two (.cumul zero .headType)
    .headType (.refl (.head one)))

theorem raised_source_checked :
    check .nil universeApplication (.head two) .nil raisedCode = true := by decide +kernel

theorem raised_execution_computes :
    execute .nil universeApplication (.head two) raisedCode =
      some ⟨ground, raisedResultCode, .betaPi (.var 0) ground⟩ := by rfl

theorem raised_result_checked :
    check .nil ground (.head two) .nil raisedResultCode = true :=
  (execute_checked raised_source_checked raised_execution_computes).1

theorem raised_checked_execution :
    checkedExecute .nil .nil universeApplication (.head two) raisedCode =
      some ⟨ground, raisedResultCode, .betaPi (.var 0) ground⟩ := by
  simp only [checkedExecute, raised_source_checked, ↓reduceIte, raised_execution_computes]

theorem dropping_wrappers_rejected :
    check .nil ground (.head two) .nil .headType = false := by decide +kernel

theorem misplaced_conversion_rejected :
    check .nil universeApplication (.head two) .nil
      (.cumul one (.cumul zero (.convert (.head one) two universeApplicationCode
        .headType (.refl (.head one))))) = false := by decide +kernel

theorem malformed_cumulative_split_rejected :
    raisedCode.principalView (.pi ground ground) = none := by rfl

/-- Splitting is not checking: a structurally readable certificate with the
wrong conversion still splits, but the complete checker rejects it. -/
theorem split_is_not_admission :
    (StructuralTypingReplay.Code.principalView (.head two)
      (.convert ground two (.headType : Code 0) .headType (.refl ground))).isSome = true ∧
    check .nil ground (.head two) .nil
      (.convert ground two .headType .headType (.refl ground)) = false := by decide +kernel

theorem raw_execution_does_not_admit_source :
    (execute .nil universeApplication (.head zero)
      (.appElim (.head zero) (.head zero)
        (.lamIntro one .var .var) .headType)).isSome = true ∧
    (checkedExecute .nil .nil universeApplication (.head zero)
      (.appElim (.head zero) (.head zero)
        (.lamIntro one .var .var) .headType)).isNone = true := by decide +kernel

def convertedInnerCode : Code 0 :=
  .appElim (.head zero) (.head zero)
    (.convert (.pi (.head zero) (.head zero)) (.sort (.max (.succ Tower.zero) (.succ Tower.zero)))
      (.lamIntro (.sort (.max (.succ Tower.zero) (.succ Tower.zero)))
        (.piForm one one .headType .headType) .var)
      (.piForm one one .headType .headType) (.refl (.pi (.head zero) (.head zero)))) .headType

theorem converted_inner_premise_executes :
    check .nil universeApplication (.head zero) .nil convertedInnerCode = true ∧
    (execute .nil universeApplication (.head zero) convertedInnerCode).isSome = true := by
  constructor
  · decide +kernel
  · decide +kernel

theorem inner_conversion_is_retained :
    NativeJudgmentReplay.Controls.functionCode.principalView
      (.pi ground NativeJudgmentReplay.Controls.targetType) =
      some ⟨.pi ground NativeJudgmentReplay.Controls.targetType,
        NativeJudgmentReplay.Controls.functionCode, .hole⟩ := by rfl

def dependentProjection : Tower.Tm 1 := .snd FormationControls.pairTerm

def projectionSourceType : Tower.Tm 1 :=
  inst0 (.fst FormationControls.pairTerm) (.id ground (.var 1) (.var 0))

def wrappedProjectionCode : Code 1 :=
  .convert projectionSourceType zero
    (.sndElim ground (.id ground (.var 1) (.var 0)) FormationControls.pairCode)
    (.idForm zero .headType .var .var)
    (NativeRelatorConversionChecking.inst0Argument (.fst FormationControls.pairTerm) (.var 0)
      (.single (.betaSigmaFst (.var 0) (.refl (.var 0)))) (.id ground (.var 1) (.var 0)))

def wrappedProjectionResult : Result 1 :=
  ⟨.refl (.var 0), .convert projectionSourceType zero
    IntroductionComputation.Controls.projectedCode (.idForm zero .headType .var .var)
    (NativeRelatorConversionChecking.inst0Argument (.fst FormationControls.pairTerm) (.var 0)
      (.single (.betaSigmaFst (.var 0) (.refl (.var 0)))) (.id ground (.var 1) (.var 0))),
    .betaSigmaSnd (.var 0) (.refl (.var 0))⟩

theorem wrapped_projection_source_checked :
    check NativeJudgmentReplay.Controls.context dependentProjection (.id ground (.var 0) (.var 0))
      NativeJudgmentReplay.Controls.contextCode wrappedProjectionCode = true := by decide +kernel

theorem wrapped_projection_computes :
    execute NativeJudgmentReplay.Controls.contextCode dependentProjection (.id ground (.var 0) (.var 0))
      wrappedProjectionCode = some wrappedProjectionResult := by rfl

def projectionReceipt : NativeCheckedSubstitution.JudgmentReceipt NativeCheckedSubstitution.Controls.groundContext :=
  ⟨dependentProjection, .id ground (.var (0 : Fin 1)) (.var (0 : Fin 1)), wrappedProjectionCode,
    wrapped_projection_source_checked⟩

theorem projection_observation_preserved :
    projectionReceipt.observe =
      (resultReceipt projectionReceipt wrappedProjectionResult wrapped_projection_computes).observe :=
  execute_observation projectionReceipt wrappedProjectionResult wrapped_projection_computes

theorem projection_receipt_changed :
    projectionReceipt ≠ resultReceipt projectionReceipt wrappedProjectionResult wrapped_projection_computes := by
  intro equal
  have subjects := congrArg NativeCheckedSubstitution.JudgmentReceipt.subject equal
  cases subjects

end Controls

#print axioms direct_checked
#print axioms direct_domain
#print axioms execute_checked
#print axioms checkedExecute_sound
#print axioms checkedExecute_domain
#print axioms execute_observation
#print axioms Controls.raised_source_checked
#print axioms Controls.raised_execution_computes
#print axioms Controls.raised_result_checked
#print axioms Controls.dropping_wrappers_rejected
#print axioms Controls.misplaced_conversion_rejected
#print axioms Controls.split_is_not_admission
#print axioms Controls.raw_execution_does_not_admit_source
#print axioms Controls.converted_inner_premise_executes
#print axioms Controls.wrapped_projection_computes
#print axioms Controls.projection_observation_preserved
#print axioms Controls.projection_receipt_changed

end PrincipalComputation
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay
