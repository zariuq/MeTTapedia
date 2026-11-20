import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContextRules

/-! # Field readback of the actual primitive root clauses -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PrimitiveCases

open SourceLanguage.Elaboration
open RuleBuilder

inductive Case : MClosed → MClosed → Prop
  | beta (body argument continuation : MClosed) :
      Case (rootC (nodeC "prime-tm-app" [nodeC "prime-tm-lam" [body], argument]) continuation)
        (substituteZeroC argument 0 body continuation)
  | first (left right continuation : MClosed) :
      Case (rootC (nodeC "prime-tm-fst" [nodeC "prime-tm-pair" [left, right]]) continuation)
        (resumeC left continuation)
  | second (left right continuation : MClosed) :
      Case (rootC (nodeC "prime-tm-snd" [nodeC "prime-tm-pair" [left, right]]) continuation)
        (resumeC right continuation)

theorem of_step {before after : MClosed}
    (step : ProgramBinders.Rewrites ContextRules.primitive.get before after) : Case before after := by
  obtain ⟨index, answered⟩ := step
  fin_cases index
  all_goals obtain ⟨environment, lhs, rhs⟩ := (answers_iff _ _ before after).mp answered
  all_goals simp only [ContextRules.active, materialize_node, materialize_slot, materialize_literal,
    List.map_cons, List.map_nil] at lhs rhs
  all_goals rw [← lhs, ← rhs]
  · exact .beta (environment 0) (environment 1) (environment 2)
  · exact .first (environment 0) (environment 1) (environment 2)
  · exact .second (environment 0) (environment 1) (environment 2)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PrimitiveCases
