import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.MainReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueWorkerRank

/-!
# Each main traversal step makes finite structural progress

Search descends into a strict subterm or reaches the root boundary.
Reconstruction removes a strict context frame or reaches its return boundary.
The measure counts the actual literal datum, so no choice of native scope is
used to define this progress certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.TraversalProgress

open SourceLanguage.Elaboration
open ValueWorkerRank (weight node_weight)

theorem seek_choice (term context continuation next : MClosed)
    (step : TraversalCases.Case (seekC term context continuation) next) :
    (∃ child rest, next = seekC child rest continuation ∧ weight child < weight term) ∨
      next = rootC term (nodeC "hd-main-plug" [context, continuation]) := by
  generalize same : seekC term context continuation = current at step
  cases step <;> simp [seekC, plugC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  all_goals obtain ⟨rfl, rfl, rfl⟩ := same
  all_goals first
    | exact .inr rfl
    | refine .inl ⟨_, _, rfl, ?_⟩
      simp only [node_weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega

theorem plug_choice (term context continuation next : MClosed)
    (step : TraversalCases.Case (plugC term context continuation) next) :
    (∃ child rest, next = plugC child rest continuation ∧ weight rest < weight context) ∨
      next = resumeC term continuation := by
  generalize same : plugC term context continuation = current at step
  cases step <;> simp [seekC, plugC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  all_goals obtain ⟨rfl, rfl, rfl⟩ := same
  all_goals first
    | exact .inr rfl
    | refine .inl ⟨_, _, rfl, ?_⟩
      simp only [node_weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.TraversalProgress
