import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTermination

/-!
# Structural shape inconsistency yields an actual tuple refusal

The actual combined refuter is complete for necessary first-order shapes
inside its checked structural fragment. This theorem connects an independent
shape contradiction to the existing executable driver; it does not replace
that driver or accept a user-supplied completeness callback.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveRefusal

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries
open ContextualConjunctiveAbsence

universe u
variable {S : Signature} {Query Local Shared : Type} {O : Type u}
  (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  [DecidableEq Query] [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)]

theorem of_shape_inconsistency (fuel : Nat) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (chosen : Fin patterns.length → O)
    (patterned : ContextualPatternFragment.ProblemPattern
      (ContextualResidual.observeProblem (joint queries locals captures problem patterns rows chosen)))
    (impossible : ∀ (Next : Type) (images : ContextualShapeErasure.ShapeAssignment S
      (Query ⊕ (Mettapedia.Logic.LP.ScopedVar Local ⊕ Shared)) Next),
        ¬ ContextualShapeErasure.ShapeModels images
          (ContextualResidual.observeProblem (joint queries locals captures problem patterns rows chosen))) :
    certifiesTuple queries locals captures (fuel + 1) problem patterns rows chosen = true := by
  let original := ContextualResidual.observeProblem (joint queries locals captures problem patterns rows chosen)
  cases normalized : ContextualRigidSolver.normalize original with
  | none =>
      have stops : ∃ proof, ContextualFrameWorklist.run (fuel + 1) (family queries locals captures) original =
          ContextualFrameWorklist.Result.refuted proof := by
        simp only [ContextualFrameWorklist.run, ContextualFrameWorklist.runWithRefuter]
        split
        · exact ⟨fun _ candidate => ContextualRigidSolver.refused_has_no_solution normalized candidate, rfl⟩
        · rename_i remaining computed
          cases normalized.symm.trans computed
      obtain ⟨proof, computed⟩ := stops
      unfold certifiesTuple
      rw [computed]
  | some remaining =>
      have restPattern := ContextualRigidPatterns.normalization_patterns original patterned normalized
      cases selected : ContextualFrameRefutation.choose remaining with
      | none =>
          obtain ⟨images, models⟩ := ContextualFrameRefutation.choose_none_has_shape_model remaining restPattern selected
          exact False.elim (impossible _ images ((ContextualShapeRigid.normalization_models images original normalized).mp models))
      | some refusal =>
          obtain ⟨proof, computed⟩ := ContextualPatternTermination.refutes_at fuel original remaining normalized refusal selected
          unfold certifiesTuple
          rw [computed]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveRefusal
