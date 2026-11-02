import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeChoiceProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeRigid
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnrefutedPatternAvailability

/-!
# The actual structural-pattern driver finishes without a supplied model

Every structural input has a finite run which either returns an empty
residual or carries a certified refutation. The executable guarded shape
owner supplies a finite shape model whenever it declines to refute. That
model measures the actual frame-changing choices; no higher-order model or
termination witness is supplied to execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTermination

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualShapeErasure
open ContextualSolverMeasure (Work Smaller)
open ContextualFrameUpdate
open ContextualFrameWorklist

variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {source : V → MetaArity S}

inductive Finished {problem : Problem source} : Result problem → Prop
  | solved (update : Update problem) (empty : update.remaining = []) : Finished (.residual update)
  | refuted (proof : ∀ {Next : Type} (next : Next → MetaArity S)
      (candidate : Assignment source next), ¬ Models candidate problem) : Finished (.refuted proof)

omit [DecidableEq V] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] in
theorem Finished.cast {first second : Problem source} (same : first = second)
    {result : Result first} (finished : Finished result) : Finished (result.cast same) := by
  cases same
  exact finished

omit [DecidableEq V] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] in
theorem Finished.after {problem : Problem source} (first : Update problem)
    {last : Result first.remaining} (finished : Finished last) : Finished (Result.after first last) := by
  cases finished with
  | solved update empty => exact .solved (first.then update) empty
  | refuted proof =>
      exact .refuted fun next candidate solved => by
        obtain ⟨residual, residualModels, _⟩ := first.valid.complete next candidate solved
        exact proof next residual residualModels

private theorem finished_of_normalization_failure (fuel : Nat) (problem : Problem source)
    (failed : ContextualRigidSolver.normalize problem = none) : Finished (run (fuel + 1) source problem) := by
  simp only [run, runWithRefuter]
  split
  · exact .refuted _
  · rename_i remaining computed
    cases failed.symm.trans computed

private theorem finished_of_refutation (fuel : Nat) (problem remaining : Problem source)
    (normalized : ContextualRigidSolver.normalize problem = some remaining)
    (refutation : ContextualEquationRefutation.Refutation remaining)
    (refused : ContextualFrameRefutation.choose remaining = some refutation) : Finished (run (fuel + 1) source problem) := by
  simp only [run, runWithRefuter]
  split
  · exact .refuted _
  · rename_i rest computed
    have same : rest = remaining := Option.some.inj (computed.symm.trans normalized)
    subst rest
    split
    · exact .refuted fun next candidate solved => by
        have same := (ContextualRigidSolver.models_normalize candidate problem)
        rw [normalized] at same
        exact refutation.noModel next candidate (same.mpr solved)
    · rename_i declined
      cases refused.symm.trans declined

/-- A computed refusal in the normalization phase is returned by the same
bounded driver, before any solver choice is performed. -/
theorem refutes_at (fuel : Nat) (problem remaining : Problem source)
    (normalized : ContextualRigidSolver.normalize problem = some remaining)
    (refutation : ContextualEquationRefutation.Refutation remaining)
    (refused : ContextualFrameRefutation.choose remaining = some refutation) :
    ∃ proof, run (fuel + 1) source problem = .refuted proof := by
  let failure : ∀ {Next : Type} (next : Next → MetaArity S) (candidate : Assignment source next), ¬ Models candidate problem :=
    fun next candidate solved => by
      have same := ContextualRigidSolver.models_normalize candidate problem
      rw [normalized] at same
      exact refutation.noModel next candidate (same.mpr solved)
  refine ⟨failure, ?_⟩
  simp only [run, runWithRefuter]
  split
  · rfl
  · rename_i rest computed
    have same : rest = remaining := Option.some.inj (computed.symm.trans normalized)
    subst rest
    split
    · rfl
    · rename_i declined
      cases refused.symm.trans declined

private theorem finishes_by_measure {Next : Type} (bound : Work) :
    ∀ {Names : Type} [DecidableEq Names] (declaration : Names → MetaArity S) (problem : Problem declaration)
      (images : ShapeAssignment S Names Next), ContextualShapePotential.measure images problem = bound →
      ProblemPattern problem → ShapeModels images problem → ∃ fuel, Finished (run fuel declaration problem) := by
  induction bound using ContextualSolverMeasure.wellFounded.induction with
  | h bound earlier =>
      intro Names equality declaration problem images measured patterned models
      cases normalized : ContextualRigidSolver.normalize problem with
      | none => exact ⟨1, finished_of_normalization_failure 0 problem normalized⟩
      | some remaining =>
          have restPattern := ContextualRigidPatterns.normalization_patterns problem patterned normalized
          have restModels := (ContextualShapeRigid.normalization_models images problem normalized).mpr models
          cases refused : ContextualFrameRefutation.choose remaining with
          | some refutation => exact ⟨1, finished_of_refutation 0 problem remaining normalized refutation refused⟩
          | none =>
              cases selected : choose remaining with
              | none =>
                  have empty := ContextualUnrefutedPatternAvailability.normal_unrefuted_pattern_saturated_empty remaining
                    (ContextualRigidNormalForm.normalization_normal problem normalized) restPattern
                    (ContextualFrameRefutation.local_none_of_choose_none refused) selected
                  refine ⟨1, ?_⟩
                  unfold run
                  rw [runWithRefuter_normalized _ 0 problem remaining normalized refused]
                  simp only [selected]
                  exact .solved (normalizationUpdate normalized) empty
              | some update =>
                  let _ := update.equality
                  obtain ⟨residual, residualModels, _, decrease⟩ :=
                    ContextualShapeChoiceProgress.computed_progress selected images restPattern restModels
                  have smaller : Smaller (ContextualShapePotential.measure residual update.remaining) bound := by
                    rw [← measured]
                    exact ContextualShapePotential.smaller_after_normalization normalized images decrease
                  have residualPattern := (ContextualSolverPatterns.computed_preserves selected restPattern).2
                  obtain ⟨fuel, finished⟩ := earlier _ smaller update.declaration update.remaining residual rfl residualPattern residualModels
                  refine ⟨fuel + 1, ?_⟩
                  unfold run
                  rw [runWithRefuter_normalized _ fuel problem remaining normalized refused]
                  simp only [selected]
                  exact finished.after ((normalizationUpdate normalized).then update)

theorem finishes_of_shape_model {Next : Type} (problem : Problem source) (images : ShapeAssignment S V Next)
    (patterned : ProblemPattern problem) (models : ShapeModels images problem) :
    ∃ fuel, Finished (run fuel source problem) :=
  finishes_by_measure _ source problem images rfl patterned models

/-- Every structural-pattern input has a finite actual run returning an
empty residual or a proof excluding all models in every later frame. -/
theorem finishes (problem : Problem source) (patterned : ProblemPattern problem) :
    ∃ fuel, Finished (run fuel source problem) := by
  cases normalized : ContextualRigidSolver.normalize problem with
  | none => exact ⟨1, finished_of_normalization_failure 0 problem normalized⟩
  | some remaining =>
      have restPattern := ContextualRigidPatterns.normalization_patterns problem patterned normalized
      cases refused : ContextualFrameRefutation.choose remaining with
      | some refutation => exact ⟨1, finished_of_refutation 0 problem remaining normalized refutation refused⟩
      | none =>
          obtain ⟨images, models⟩ := ContextualFrameRefutation.choose_none_has_shape_model remaining restPattern refused
          exact finishes_of_shape_model problem images patterned
            ((ContextualShapeRigid.normalization_models images problem normalized).mp models)

/-- The successful alternative returns the actual computed answer. It
solves the input and factors every model in every target declaration family. -/
theorem solves_or_refutes (problem : Problem source) (patterned : ProblemPattern problem) :
    ∃ fuel,
      (∃ update : Update problem, run fuel source problem = .residual update ∧ update.remaining = [] ∧
        Models update.answer problem ∧
        ∀ {Next : Type} (next : Next → MetaArity S) (candidate : Assignment source next), Models candidate problem →
          ∃ residual : Assignment update.declaration next,
            ∀ identity, candidate identity = instantiate residual (update.answer identity)) ∨
      (∃ proof, run fuel source problem = .refuted proof) := by
  obtain ⟨fuel, finished⟩ := finishes problem patterned
  refine ⟨fuel, ?_⟩
  generalize computed : run fuel source problem = result at finished
  cases finished with
  | solved update empty =>
      refine .inl ⟨update, rfl, empty, update.completed empty, ?_⟩
      intro Next next candidate models
      obtain ⟨residual, _, components⟩ := update.valid.complete next candidate models
      exact ⟨residual, components⟩
  | refuted proof => exact .inr ⟨proof, rfl⟩

/-- Semantic inconsistency in the structural fragment is eventually
reported by the actual executable driver. -/
theorem refutes_of_no_model (problem : Problem source) (patterned : ProblemPattern problem)
    (impossible : ∀ {Next : Type} (next : Next → MetaArity S) (candidate : Assignment source next),
      ¬ Models candidate problem) : ∃ fuel proof, run fuel source problem = .refuted proof := by
  obtain ⟨fuel, solved | refused⟩ := solves_or_refutes problem patterned
  · obtain ⟨update, _, _, models, _⟩ := solved
    exact False.elim (impossible update.declaration update.answer models)
  · obtain ⟨proof, computed⟩ := refused
    exact ⟨fuel, proof, computed⟩

omit [DecidableEq V] in
/-- The original concatenation need not be a structural-pattern problem.
It suffices that the actual saved residual and transported new equations
are patterns. This also permits an unfinished but supported prefix. -/
theorem finishes_resuming {past : Problem source} (update : Update past) (extra : Problem source)
    (patterned : ProblemPattern (update.remaining ++ mapProblem update.answer extra)) :
    ∃ fuel, Finished ((Result.residual update).resume fuel extra) := by
  let _ := update.equality
  obtain ⟨fuel, finished⟩ := finishes (update.remaining ++ mapProblem update.answer extra) patterned
  exact ⟨fuel, finished.after (update.keep_right extra)⟩

omit [DecidableEq V] in
/-- For the transformed structural fragment, successful resumption is
equivalent to solvability of the entire original problem in some future
family. A completed result factors every such original solution. -/
theorem completed_resume_iff {past : Problem source} (update : Update past) (extra : Problem source)
    (patterned : ProblemPattern (update.remaining ++ mapProblem update.answer extra)) :
    (∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment source future),
      Models candidate (past ++ extra)) ↔
    ∃ fuel result, (Result.residual update).resume fuel extra = .residual result ∧ result.remaining = [] := by
  constructor
  · rintro ⟨Future, future, candidate, model⟩
    obtain ⟨fuel, finished⟩ := finishes_resuming update extra patterned
    generalize computed : (Result.residual update).resume fuel extra = result at finished
    cases finished with
    | solved result empty => exact ⟨fuel, result, computed, empty⟩
    | refuted proof => exact False.elim (proof future candidate model)
  · rintro ⟨fuel, result, _, empty⟩
    exact ⟨result.Variables, result.declaration, result.answer, result.completed empty⟩

theorem completed_incremental_iff {past : Problem source} {firstFuel : Nat}
    (update : Update past) (computed : run firstFuel source past = .residual update)
    (extra : Problem source)
    (patterned : ProblemPattern (update.remaining ++ mapProblem update.answer extra)) :
    (∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment source future),
      Models candidate (past ++ extra)) ↔
    ∃ fuel result, runIncremental firstFuel fuel past extra = .residual result ∧ result.remaining = [] := by
  simp only [runIncremental, computed]
  exact completed_resume_iff update extra patterned

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTermination
