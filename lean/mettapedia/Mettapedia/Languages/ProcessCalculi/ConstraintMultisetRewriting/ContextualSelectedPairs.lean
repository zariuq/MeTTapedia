import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairSelection

/-!
# Two selected contextual occurrences retain their respective arities

Each selected name moves to its own port. Parameter renaming and observation
commute with that same change of frame, including when the two observations
were presented with separate result-sort indices.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedPairs

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} [DecidableEq V]

abbrev selected (source : V → MetaArity S) (first second : V) (different : first ≠ second) :=
  reindex (ContextualPairSelection.split first second different)
    (ContextualPairSelection.forward_preserves source first second different)

theorem first_image (source : V → MetaArity S) (first second : V) (different : first ≠ second) :
    selected source first second different first =
      generator (ContextualPairSelection.declarations source first second) (.inl false) :=
  cast_generator_of_identity (S := S)
    (source := ContextualPairSelection.declarations source first second)
    (ContextualPairSelection.first_to_port first second different) _

theorem second_image (source : V → MetaArity S) (first second : V) (different : first ≠ second) :
    selected source first second different second =
      generator (ContextualPairSelection.declarations source first second) (.inl true) :=
  cast_generator_of_identity (S := S)
    (source := ContextualPairSelection.declarations source first second)
    (ContextualPairSelection.second_to_port first second different) _

theorem first_occurrence (source : V → MetaArity S) (first second : V) (different : first ≠ second)
    {Γ : Ctx S} (rho : Ren S (source first).1 Γ) :
    instantiate (selected source first second different)
        (rename (S := signature S source) rho (generator source first)) =
      rename (S := signature S (ContextualPairSelection.declarations source first second)) rho
        (generator (ContextualPairSelection.declarations source first second) (.inl false)) := by
  rw [ContextualFamily.instantiate_rename, instantiate_generator, first_image]

theorem second_occurrence (source : V → MetaArity S) (first second : V) (different : first ≠ second)
    {Γ : Ctx S} (rho : Ren S (source second).1 Γ) :
    instantiate (selected source first second different)
        (rename (S := signature S source) rho (generator source second)) =
      rename (S := signature S (ContextualPairSelection.declarations source first second)) rho
        (generator (ContextualPairSelection.declarations source first second) (.inl true)) := by
  rw [ContextualFamily.instantiate_rename, instantiate_generator, second_image]

theorem selected_problem (source : V → MetaArity S) (first second : V) (different : first ≠ second)
    {Γ : Ctx S} (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Γ)
    (rest : ContextualResidual.Problem source) :
    ContextualResidual.mapProblem (selected source first second different)
      ((observe (rename (S := signature S source) left (generator source first)),
        observe (rename (S := signature S source) right (generator source second))) :: rest) =
      (observe (rename (S := signature S (ContextualPairSelection.declarations source first second)) left
          (generator (ContextualPairSelection.declarations source first second) (.inl false))),
       observe (rename (S := signature S (ContextualPairSelection.declarations source first second)) right
          (generator (ContextualPairSelection.declarations source first second) (.inl true)))) ::
        ContextualResidual.mapProblem (selected source first second different) rest := by
  simp only [ContextualResidual.mapProblem, List.map_cons, instantiateObservation_observe,
    first_occurrence, second_occurrence]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedPairs
