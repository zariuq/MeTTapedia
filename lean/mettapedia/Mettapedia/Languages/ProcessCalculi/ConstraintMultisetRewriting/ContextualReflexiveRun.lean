import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRunSelector

/-!
# Actual worklist completion for arbitrary reflexive contextual equations

The fuel is one plus the number of identical meta-root leaves exposed by
rigid normalization. Each nonempty iteration follows the real reflexive
selector. The resulting declaration family and answer are proved to be
the original family and its generator; the original nonempty queue is
actually discharged, not assumed solved by a zero-fuel identity update.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRun

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual ContextualFrameUpdate ContextualFrameWorklist

variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  [∀ result, DecidableEq (S.Op result)] {source : V → MetaArity S}

theorem actual_leaf_run (refuter : Refuter S) (values : List (Leaf source)) :
    runWithRefuter refuter (values.length + 1) source (leafProblem values) =
      .residual (completed (values.map Leaf.observation)) := by
  induction values with
  | nil =>
      have normalized := normalize_leaves (source := source) []
      have unrefuted := refuter_none_of_model refuter (leafProblem ([] : List (Leaf source)))
        source (generator source) (leaf_models _ _)
      rw [show ([] : List (Leaf source)).length + 1 = 0 + 1 from rfl,
        runWithRefuter_normalized refuter 0 _ [] normalized unrefuted, actual_empty_choice]
      rfl
  | cons first rest earlier =>
      have normalized := normalize_leaves (first :: rest)
      have unrefuted := refuter_none_of_model refuter (leafProblem (first :: rest))
        source (generator source) (leaf_models _ _)
      change runWithRefuter refuter ((rest.length + 1) + 1) source (leafProblem (first :: rest)) = _
      rw [runWithRefuter_normalized refuter (rest.length + 1) _ _ normalized unrefuted, actual_head_choice]
      change Result.after ((normalizationUpdate normalized).then (dropFirst first rest))
        (runWithRefuter refuter (rest.length + 1) source (leafProblem rest)) = _
      rw [earlier]
      simp only [Result.after, Update.then, normalizationUpdate, dropFirst, completed,
        Assignment.compose_identity_left]

theorem actual_runWithRefuter (refuter : Refuter S) (observations : List (Observation S source)) :
    runWithRefuter refuter ((queueLeaves observations).length + 1) source (diagonals observations) =
      .residual (completed observations) := by
  cases found : queueLeaves observations with
  | nil =>
      have normalized : ContextualRigidSolver.normalize (diagonals observations) = some [] := by
        rw [normalize_diagonals, found]
        rfl
      have unrefuted := refuter_none_of_model refuter ([] : Problem source)
        source (generator source) (by intro equation member; cases member)
      rw [show ([] : List (Leaf source)).length + 1 = 0 + 1 from rfl,
        runWithRefuter_normalized refuter 0 _ [] normalized unrefuted, actual_empty_choice]
      rfl
  | cons first rest =>
      have normalized : ContextualRigidSolver.normalize (diagonals observations) = some (leafProblem (first :: rest)) := by
        rw [normalize_diagonals, found]
      have unrefuted := refuter_none_of_model refuter (leafProblem (first :: rest))
        source (generator source) (leaf_models _ _)
      change runWithRefuter refuter ((rest.length + 1) + 1) source (diagonals observations) = _
      rw [runWithRefuter_normalized refuter (rest.length + 1) _ _ normalized unrefuted, actual_head_choice]
      change Result.after ((normalizationUpdate normalized).then (dropFirst first rest))
        (runWithRefuter refuter (rest.length + 1) source (leafProblem rest)) = _
      rw [actual_leaf_run]
      simp only [Result.after, Update.then, normalizationUpdate, dropFirst, completed,
        Assignment.compose_identity_left]

theorem actual_run (observations : List (Observation S source)) :
    run ((queueLeaves observations).length + 1) source (diagonals observations) =
      .residual (completed observations) :=
  actual_runWithRefuter _ observations

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem completed_record_fields (observations : List (Observation S source)) :
    (completed observations).Variables = V ∧ (completed observations).declaration = source ∧
      (completed observations).answer = generator source ∧ (completed observations).remaining = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

def residualLength {problem : Problem source} : Result problem → Option Nat
  | .residual update => some update.remaining.length
  | .refuted _ => none

theorem zero_fuel_keeps_the_original_queue (observations : List (Observation S source)) :
    residualLength (run 0 source (diagonals observations)) = some observations.length := by
  change some (diagonals observations).length = _
  rw [diagonals, List.length_map]

theorem zero_fuel_does_not_complete_a_nonempty_queue (observations : List (Observation S source))
    (nonempty : observations ≠ []) : run 0 source (diagonals observations) ≠ .residual (completed observations) := by
  intro returned
  have lengths := congrArg residualLength returned
  rw [zero_fuel_keeps_the_original_queue] at lengths
  change some observations.length = some 0 at lengths
  exact nonempty (List.length_eq_zero_iff.mp (Option.some.inj lengths))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRun
