import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContextRules

/-! # Field readback of the actual driver clauses -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.DriverCases

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage.Elaboration
open RuleBuilder

inductive Case : MClosed → MClosed → Prop
  | value (term continuation : MClosed) : Case (evaluateC term continuation) (valueC term continuation)
  | seek (term continuation : MClosed) :
      Case (evaluateC term continuation)
        (seekC term emptyContext (nodeC "hd-main-eval-next" [continuation]))
  | next (term continuation : MClosed) :
      Case (resumeC term (nodeC "hd-main-eval-next" [continuation])) (evaluateC term continuation)
  | finish (term : MClosed) : Case (resumeC term finishContinuation) (doneC term)
  | zero (continuation : MClosed) :
      Case (valueC (encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0)) continuation)
        (resumeC (encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0)) continuation)
  | unit (continuation : MClosed) :
      Case (valueC (encodeTm (TowerVectorsModel.ttC : Tower.Tm 0)) continuation)
        (resumeC (encodeTm (TowerVectorsModel.ttC : Tower.Tm 0)) continuation)
  | succ (term continuation : MClosed) :
      Case (valueC (nodeC "prime-tm-app" [encodeTm (.const TowerNumbersModel.succ : Tower.Tm 0), term]) continuation)
        (valueC term (nodeC "hd-main-value-succ" [continuation]))
  | succReturn (term continuation : MClosed) :
      Case (resumeC term (nodeC "hd-main-value-succ" [continuation]))
        (resumeC (nodeC "prime-tm-app" [encodeTm (.const TowerNumbersModel.succ : Tower.Tm 0), term]) continuation)
  | pair (left right continuation : MClosed) :
      Case (valueC (nodeC "prime-tm-pair" [left, right]) continuation)
        (valueC left (nodeC "hd-main-value-pair-first" [right, continuation]))
  | pairNext (left right continuation : MClosed) :
      Case (resumeC left (nodeC "hd-main-value-pair-first" [right, continuation]))
        (valueC right (nodeC "hd-main-value-pair-second" [left, continuation]))
  | pairReturn (right left continuation : MClosed) :
      Case (resumeC right (nodeC "hd-main-value-pair-second" [left, continuation]))
        (resumeC (nodeC "prime-tm-pair" [left, right]) continuation)

theorem of_step {before after : MClosed}
    (step : ProgramBinders.Rewrites ContextRules.driver.get before after) : Case before after := by
  obtain ⟨index, answered⟩ := step
  fin_cases index
  all_goals obtain ⟨environment, lhs, rhs⟩ := (answers_iff _ _ before after).mp answered
  all_goals simp only [ContextRules.active, materialize_node, materialize_slot, materialize_literal,
    List.map_cons, List.map_nil] at lhs rhs
  all_goals rw [← lhs, ← rhs]
  · exact .value (environment 0) (environment 1)
  · exact .seek (environment 0) (environment 1)
  · exact .next (environment 0) (environment 1)
  · exact .finish (environment 0)
  · exact .zero (environment 0)
  · exact .unit (environment 0)
  · exact .succ (environment 0) (environment 1)
  · exact .succReturn (environment 0) (environment 1)
  · exact .pair (environment 0) (environment 1) (environment 2)
  · exact .pairNext (environment 0) (environment 1) (environment 2)
  · exact .pairReturn (environment 0) (environment 1) (environment 2)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.DriverCases
