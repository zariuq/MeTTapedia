import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContextRules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuleInstances

/-! # Actual finite source rewrites of the value-directed driver -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.DriverRewrites

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage.Elaboration
open RuleBuilder

variable {all : List (ProgramBinders.Equation MSig [] ())}
  (included : ∀ rule ∈ ContextRules.driver, rule ∈ all)
include included

theorem evaluate_value (term continuation : MClosed) :
    ProgramBinders.Rewrites all.get (evaluateC term continuation) (valueC term continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 2) "hd-eval" [slot 0, slot 1])
    (ContextRules.active "hd-value" [slot 0, slot 1])
    (included _ (by simp [ContextRules.driver])) ![term, continuation]
  simpa [evaluateC, valueC, activeC, ContextRules.active] using step

theorem evaluate_seek (term continuation : MClosed) :
    ProgramBinders.Rewrites all.get (evaluateC term continuation)
      (seekC term emptyContext (nodeC "hd-main-eval-next" [continuation])) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 2) "hd-eval" [slot 0, slot 1])
    (ContextRules.active "hd-seek" [slot 0, node "hd-context-empty" [], node "hd-main-eval-next" [slot 1]])
    (included _ (by simp [ContextRules.driver])) ![term, continuation]
  simpa [evaluateC, seekC, emptyContext, activeC, ContextRules.active] using step

theorem evaluate_next (term continuation : MClosed) :
    ProgramBinders.Rewrites all.get (resumeC term (nodeC "hd-main-eval-next" [continuation]))
      (evaluateC term continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 2) "hd-resume" [slot 0, node "hd-main-eval-next" [slot 1]])
    (ContextRules.active "hd-eval" [slot 0, slot 1])
    (included _ (by simp [ContextRules.driver])) ![term, continuation]
  simpa [resumeC, evaluateC, activeC, ContextRules.active] using step

theorem finish (term : MClosed) :
    ProgramBinders.Rewrites all.get (resumeC term finishContinuation) (doneC term) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 1) "hd-resume" [slot 0, node "hd-main-finish" []])
    (node doneTag [slot 0])
    (included _ (by simp [ContextRules.driver])) ![term]
  simpa [resumeC, finishContinuation, doneC, activeC, ContextRules.active] using step

theorem zero (continuation : MClosed) :
    ProgramBinders.Rewrites all.get (valueC (encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0)) continuation)
      (resumeC (encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0)) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 1) "hd-value" [literal (encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0)), slot 0])
    (ContextRules.active "hd-resume" [literal (encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0)), slot 0])
    (included _ (by simp [ContextRules.driver])) ![continuation]
  simpa [valueC, resumeC, activeC, ContextRules.active] using step

theorem tt (continuation : MClosed) :
    ProgramBinders.Rewrites all.get (valueC (encodeTm (TowerVectorsModel.ttC : Tower.Tm 0)) continuation)
      (resumeC (encodeTm (TowerVectorsModel.ttC : Tower.Tm 0)) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 1) "hd-value" [literal (encodeTm (TowerVectorsModel.ttC : Tower.Tm 0)), slot 0])
    (ContextRules.active "hd-resume" [literal (encodeTm (TowerVectorsModel.ttC : Tower.Tm 0)), slot 0])
    (included _ (by simp [ContextRules.driver])) ![continuation]
  simpa [valueC, resumeC, activeC, ContextRules.active] using step

theorem succ_start (term continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (valueC (nodeC "prime-tm-app" [encodeTm (.const TowerNumbersModel.succ : Tower.Tm 0), term]) continuation)
      (valueC term (nodeC "hd-main-value-succ" [continuation])) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 2) "hd-value"
      [node "prime-tm-app" [literal (encodeTm (.const TowerNumbersModel.succ : Tower.Tm 0)), slot 0], slot 1])
    (ContextRules.active "hd-value" [slot 0, node "hd-main-value-succ" [slot 1]])
    (included _ (by simp [ContextRules.driver])) ![term, continuation]
  simpa [valueC, activeC, ContextRules.active] using step

theorem succ_return (term continuation : MClosed) :
    ProgramBinders.Rewrites all.get (resumeC term (nodeC "hd-main-value-succ" [continuation]))
      (resumeC (nodeC "prime-tm-app" [encodeTm (.const TowerNumbersModel.succ : Tower.Tm 0), term]) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 2) "hd-resume" [slot 0, node "hd-main-value-succ" [slot 1]])
    (ContextRules.active "hd-resume"
      [node "prime-tm-app" [literal (encodeTm (.const TowerNumbersModel.succ : Tower.Tm 0)), slot 0], slot 1])
    (included _ (by simp [ContextRules.driver])) ![term, continuation]
  simpa [resumeC, activeC, ContextRules.active] using step

theorem pair_start (first second continuation : MClosed) :
    ProgramBinders.Rewrites all.get (valueC (nodeC "prime-tm-pair" [first, second]) continuation)
      (valueC first (nodeC "hd-main-value-pair-first" [second, continuation])) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 3) "hd-value" [node "prime-tm-pair" [slot 0, slot 1], slot 2])
    (ContextRules.active "hd-value" [slot 0, node "hd-main-value-pair-first" [slot 1, slot 2]])
    (included _ (by simp [ContextRules.driver])) ![first, second, continuation]
  simpa [valueC, activeC, ContextRules.active] using step

theorem pair_middle (first second continuation : MClosed) :
    ProgramBinders.Rewrites all.get (resumeC first (nodeC "hd-main-value-pair-first" [second, continuation]))
      (valueC second (nodeC "hd-main-value-pair-second" [first, continuation])) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 3) "hd-resume" [slot 0, node "hd-main-value-pair-first" [slot 1, slot 2]])
    (ContextRules.active "hd-value" [slot 1, node "hd-main-value-pair-second" [slot 0, slot 2]])
    (included _ (by simp [ContextRules.driver])) ![first, second, continuation]
  simpa [resumeC, valueC, activeC, ContextRules.active] using step

theorem pair_return (first second continuation : MClosed) :
    ProgramBinders.Rewrites all.get (resumeC second (nodeC "hd-main-value-pair-second" [first, continuation]))
      (resumeC (nodeC "prime-tm-pair" [first, second]) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 3) "hd-resume" [slot 0, node "hd-main-value-pair-second" [slot 1, slot 2]])
    (ContextRules.active "hd-resume" [node "prime-tm-pair" [slot 1, slot 0], slot 2])
    (included _ (by simp [ContextRules.driver])) ![second, first, continuation]
  simpa [resumeC, activeC, ContextRules.active] using step

theorem value_runs {value : Tower.Tm 0}
    (isValue : NativeTypesOnTheStep.Computing.DirectedAnswers.Value value) (continuation : MClosed) :
    RuleInstances.Steps all (valueC (encodeTm value) continuation) (resumeC (encodeTm value) continuation) := by
  induction isValue generalizing continuation with
  | zero => exact .single (zero included continuation)
  | tt => exact .single (tt included continuation)
  | @succ term _ ih =>
      simpa only [TowerVectorsModel.succC, encodeTm_app] using
        (Relation.ReflTransGen.single (succ_start included (encodeTm term) continuation)).trans
          ((ih (nodeC "hd-main-value-succ" [continuation])).trans
            (.single (succ_return included (encodeTm term) continuation)))
  | @pair first second _ _ ihFirst ihSecond =>
      simpa only [encodeTm_pair] using
        (Relation.ReflTransGen.single (pair_start included (encodeTm first) (encodeTm second) continuation)).trans
          ((ihFirst (nodeC "hd-main-value-pair-first" [encodeTm second, continuation])).trans
            ((Relation.ReflTransGen.single (pair_middle included (encodeTm first) (encodeTm second) continuation)).trans
              ((ihSecond (nodeC "hd-main-value-pair-second" [encodeTm first, continuation])).trans
                (.single (pair_return included (encodeTm first) (encodeTm second) continuation)))))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.DriverRewrites
