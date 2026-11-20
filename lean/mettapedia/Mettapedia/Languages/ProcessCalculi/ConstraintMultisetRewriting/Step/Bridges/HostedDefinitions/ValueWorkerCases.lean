import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueContinuation

/-! # Cases of the actual seven value-worker equations -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage.Elaboration
open RuleBuilder ValueContinuation

def rules : List (ProgramBinders.Equation MSig [] ()) := ContextRules.driver.drop 4
abbrev Step := ProgramBinders.Rewrites rules.get
abbrev Runs := Relation.ReflTransGen Step

abbrev zero : MClosed := encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0)
abbrev unit : MClosed := encodeTm (TowerVectorsModel.ttC : Tower.Tm 0)

theorem step_cases {call answer : MClosed} (step : Step call answer) :
    (∃ k, call = valueC zero k ∧ answer = resumeC zero k) ∨
    (∃ k, call = valueC unit k ∧ answer = resumeC unit k) ∨
    (∃ t k, call = valueC (successor t) k ∧
      answer = valueC t (nodeC "hd-main-value-succ" [k])) ∨
    (∃ t k, call = resumeC t (nodeC "hd-main-value-succ" [k]) ∧
      answer = resumeC (successor t) k) ∨
    (∃ a b k, call = valueC (pair a b) k ∧
      answer = valueC a (nodeC "hd-main-value-pair-first" [b, k])) ∨
    (∃ a b k, call = resumeC a (nodeC "hd-main-value-pair-first" [b, k]) ∧
      answer = valueC b (nodeC "hd-main-value-pair-second" [a, k])) ∨
    (∃ b a k, call = resumeC b (nodeC "hd-main-value-pair-second" [a, k]) ∧
      answer = resumeC (pair a b) k) := by
  obtain ⟨index, answered⟩ := step
  fin_cases index
  all_goals obtain ⟨environment, lhs, rhs⟩ := (answers_iff _ _ call answer).mp answered
  all_goals simp only [ContextRules.active, materialize_node, materialize_slot,
    materialize_literal, List.map_cons, List.map_nil] at lhs rhs
  · exact .inl ⟨environment 0, lhs.symm, rhs.symm⟩
  · exact .inr (.inl ⟨environment 0, lhs.symm, rhs.symm⟩)
  · exact .inr (.inr (.inl ⟨environment 0, environment 1, lhs.symm, rhs.symm⟩))
  · exact .inr (.inr (.inr (.inl ⟨environment 0, environment 1, lhs.symm, rhs.symm⟩)))
  · exact .inr (.inr (.inr (.inr (.inl
      ⟨environment 0, environment 1, environment 2, lhs.symm, rhs.symm⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl
      ⟨environment 0, environment 1, environment 2, lhs.symm, rhs.symm⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr
      ⟨environment 0, environment 1, environment 2, lhs.symm, rhs.symm⟩)))))

@[simp] theorem value_eq_iff (first second k l : MClosed) :
    valueC first k = valueC second l ↔ first = second ∧ k = l := by
  simp [valueC, activeC, DataEmbedding.nodeC_eq_iff]

@[simp] theorem resume_eq_iff (first second k l : MClosed) :
    resumeC first k = resumeC second l ↔ first = second ∧ k = l := by
  simp [resumeC, activeC, DataEmbedding.nodeC_eq_iff]

@[simp] theorem value_ne_resume (first second k l : MClosed) :
    valueC first k ≠ resumeC second l := by
  simp [valueC, resumeC, activeC, DataEmbedding.nodeC_eq_iff]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker
