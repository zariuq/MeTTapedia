import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ProgramCases

/-! # Exact main-phase boundaries of the assembled source program -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.MainReadback

open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

theorem authored_at_root {entry : RowCompilation.Entry} {rule : ProgramBinders.Equation MSig [] ()}
    (compiled : RowCompiler.row entry = some rule) {current next : MClosed}
    (answered : ProgramBinders.Answers rule current next) :
    RuntimeSubstitution.phaseOf current = some "hd-root" :=
  answered_phase (RowPhases.row_phase compiled).1 answered

theorem seek_step {dev : Definitions.Development} (built : Compiled dev) (term context continuation next : MClosed)
    (step : ProgramBinders.Rewrites built.rules.get (seekC term context continuation) next) :
    TraversalCases.Case (seekC term context continuation) next := by
  have classification := ProgramCases.at_main_phase built (phase := "hd-seek") rfl (by decide) step
  cases classification with
  | traversal edge => exact edge
  | primitive edge =>
      generalize same : seekC term context continuation = current at edge
      cases edge <;> simp [rootC, seekC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | driver edge =>
      generalize same : seekC term context continuation = current at edge
      cases edge <;> simp [evaluateC, seekC, valueC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | authored entry selected rule compiled answered =>
      have impossible := authored_at_root compiled answered
      change some "hd-seek" = some "hd-root" at impossible
      simp at impossible

theorem plug_step {dev : Definitions.Development} (built : Compiled dev) (term context continuation next : MClosed)
    (step : ProgramBinders.Rewrites built.rules.get (plugC term context continuation) next) :
    TraversalCases.Case (plugC term context continuation) next := by
  have classification := ProgramCases.at_main_phase built (phase := "hd-plug") rfl (by decide) step
  cases classification with
  | traversal edge => exact edge
  | primitive edge =>
      generalize same : plugC term context continuation = current at edge
      cases edge <;> simp [rootC, plugC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | driver edge =>
      generalize same : plugC term context continuation = current at edge
      cases edge <;> simp [evaluateC, plugC, valueC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | authored entry selected rule compiled answered =>
      have impossible := authored_at_root compiled answered
      change some "hd-plug" = some "hd-root" at impossible
      simp at impossible

theorem eval_step {dev : Definitions.Development} (built : Compiled dev) (term continuation next : MClosed)
    (step : ProgramBinders.Rewrites built.rules.get (evaluateC term continuation) next) :
    next = valueC term continuation ∨ next = seekC term emptyContext (nodeC "hd-main-eval-next" [continuation]) := by
  have classification := ProgramCases.at_main_phase built (phase := "hd-eval") rfl (by decide) step
  cases classification with
  | traversal edge =>
      generalize same : evaluateC term continuation = current at edge
      cases edge <;> simp [evaluateC, seekC, plugC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | primitive edge =>
      generalize same : evaluateC term continuation = current at edge
      cases edge <;> simp [rootC, evaluateC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | driver edge =>
      generalize same : evaluateC term continuation = current at edge
      cases edge <;> simp [evaluateC, valueC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
      all_goals obtain ⟨rfl, rfl⟩ := same
      · exact .inl rfl
      · exact .inr rfl
  | authored entry selected rule compiled answered =>
      have impossible := authored_at_root compiled answered
      change some "hd-eval" = some "hd-root" at impossible
      simp at impossible

theorem resume_plug_step {dev : Definitions.Development} (built : Compiled dev)
    (term context continuation next : MClosed)
    (step : ProgramBinders.Rewrites built.rules.get
      (resumeC term (nodeC "hd-main-plug" [context, continuation])) next) :
    next = plugC term context continuation := by
  have classification := ProgramCases.at_main_phase built (phase := "hd-resume") rfl (by decide) step
  cases classification with
  | traversal edge =>
      generalize same : resumeC term (nodeC "hd-main-plug" [context, continuation]) = current at edge
      cases edge <;> simp [seekC, plugC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
      obtain ⟨rfl, rfl, rfl⟩ := same
      rfl
  | primitive edge =>
      generalize same : resumeC term (nodeC "hd-main-plug" [context, continuation]) = current at edge
      cases edge <;> simp [rootC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | driver edge =>
      generalize same : resumeC term (nodeC "hd-main-plug" [context, continuation]) = current at edge
      cases edge <;> simp [evaluateC, valueC, resumeC, finishContinuation, activeC, DataEmbedding.nodeC_eq_iff] at same
  | authored entry selected rule compiled answered =>
      have impossible := authored_at_root compiled answered
      change some "hd-resume" = some "hd-root" at impossible
      simp at impossible

theorem resume_eval_step {dev : Definitions.Development} (built : Compiled dev)
    (term continuation next : MClosed)
    (step : ProgramBinders.Rewrites built.rules.get
      (resumeC term (nodeC "hd-main-eval-next" [continuation])) next) :
    next = evaluateC term continuation := by
  have classification := ProgramCases.at_main_phase built (phase := "hd-resume") rfl (by decide) step
  cases classification with
  | traversal edge =>
      generalize same : resumeC term (nodeC "hd-main-eval-next" [continuation]) = current at edge
      cases edge <;> simp [seekC, plugC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | primitive edge =>
      generalize same : resumeC term (nodeC "hd-main-eval-next" [continuation]) = current at edge
      cases edge <;> simp [rootC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | driver edge =>
      generalize same : resumeC term (nodeC "hd-main-eval-next" [continuation]) = current at edge
      cases edge <;> simp [evaluateC, valueC, resumeC, finishContinuation, activeC, DataEmbedding.nodeC_eq_iff] at same
      obtain ⟨rfl, rfl⟩ := same
      rfl
  | authored entry selected rule compiled answered =>
      have impossible := authored_at_root compiled answered
      change some "hd-resume" = some "hd-root" at impossible
      simp at impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.MainReadback
