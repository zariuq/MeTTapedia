import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSelection

/-!
# Selected occurrences commute with the typed change of frame

Moving a chosen declaration to its distinguished port preserves its actual
parameter application. Both sides of the selected equation and all queued
equations therefore enter the same fresh-helper solver frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedOccurrences

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} [DecidableEq V]

abbrev selected (source : V → MetaArity S) (identity : V) :=
  reindex (ContextualFrameSelection.split identity)
    (ContextualFrameSelection.forward_preserves source identity)

theorem selected_image (source : V → MetaArity S) (identity : V) :
    selected source identity identity =
      generator (ContextualFrameSelection.declarations source identity) (.inl ()) := by
  exact cast_generator_of_identity (S := S)
    (source := ContextualFrameSelection.declarations source identity)
    (ContextualFrameSelection.chosen_to_port identity) _

theorem selected_occurrence (source : V → MetaArity S) (identity : V)
    {Γ : Ctx S} (rho : Ren S (source identity).1 Γ) :
    instantiate (selected source identity)
        (rename (S := signature S source) rho (generator source identity)) =
      rename (S := signature S (ContextualFrameSelection.declarations source identity)) rho
        (generator (ContextualFrameSelection.declarations source identity) (.inl ())) := by
  rw [ContextualFamily.instantiate_rename, instantiate_generator, selected_image]

theorem selected_problem (source : V → MetaArity S) (identity : V) {Γ : Ctx S}
    (left right : Ren S (source identity).1 Γ) (rest : ContextualResidual.Problem source) :
    ContextualResidual.mapProblem (selected source identity)
      ((observe (rename (S := signature S source) left (generator source identity)),
        observe (rename (S := signature S source) right (generator source identity))) :: rest) =
      (observe (rename (S := signature S (ContextualFrameSelection.declarations source identity)) left
          (generator (ContextualFrameSelection.declarations source identity) (.inl ()))),
       observe (rename (S := signature S (ContextualFrameSelection.declarations source identity)) right
          (generator (ContextualFrameSelection.declarations source identity) (.inl ())))) ::
        ContextualResidual.mapProblem (selected source identity) rest := by
  simp only [ContextualResidual.mapProblem, List.map_cons, instantiateObservation_observe,
    selected_occurrence]

theorem selected_rigid_problem (source : V → MetaArity S) (identity : V) {Γ : Ctx S}
    (rho : Ren S (source identity).1 Γ) (operator : S.Op (source identity).2)
    (arguments : Args (signature S source) (S.arity operator) Γ) (rest : ContextualResidual.Problem source) :
    ContextualResidual.mapProblem (selected source identity)
      ((observe (rename (S := signature S source) rho (generator source identity)),
        observe (Term.op (.inl operator) arguments)) :: rest) =
      (observe (rename (S := signature S (ContextualFrameSelection.declarations source identity)) rho
          (generator (ContextualFrameSelection.declarations source identity) (.inl ()))),
       observe (Term.op (.inl operator) (instantiateArgs (selected source identity) arguments))) ::
        ContextualResidual.mapProblem (selected source identity) rest := by
  simp only [ContextualResidual.mapProblem, List.map_cons, instantiateObservation_observe,
    selected_occurrence, ContextualFamily.instantiate]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedOccurrences
