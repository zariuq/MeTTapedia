import Mettapedia.OSLF.Syntax.BindingClosedContextSemantics

/-!
# Simultaneous substitution in the closed binding interpretation

The independently computed target meaning of an open term commutes with
substitution of an arbitrary vector of open terms. The proof compares with
the natural-family binding model and its established substitution theorem.
The resulting context arrows obey identity and composition with their
contravariant orientation explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open CategoricalBindingModel

universe u v

variable {binding : Mettapedia.OSLF.Binding.Signature}

theorem embed_substitution {metas : List (MetaArity binding)}
    {before after : Ctx binding} {sort : binding.Srt}
    (substitution : Sub binding before after) (term : Term binding before sort) :
    embed (M := metas) (bind substitution term) =
      bind (fun result position => embed (M := metas) (substitution result position))
        (embed (M := metas) term) := by
  have compared := mapTerm_bind (metaInclusion binding metas)
    (fun _ position => position) (fun _ position => position) substitution
    (fun result position => embed (M := metas) (substitution result position))
    (fun _ _ => (onTerm_metaInclusion _).symm) term
  simpa only [onTerm_metaInclusion] using compared

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

namespace Operations

variable (operations : Operations binding C)

def substitutionArrow {before after : Ctx binding} (substitution : Sub binding before after) :
    operations.context after ⟶ operations.context before :=
  operations.model.tupleEnv (fun result position => operations.meaning (substitution result position))

theorem substitutionArrow_projection {before after : Ctx binding}
    (substitution : Sub binding before after) {sort : binding.Srt} (position : Var before sort) :
    operations.substitutionArrow substitution ≫ projectVar operations.sort position =
      operations.meaning (substitution sort position) :=
  operations.model.tupleEnv_projectVar _ position

theorem meaning_substitution {before after : Ctx binding} {sort : binding.Srt}
    (substitution : Sub binding before after) (term : Term binding before sort) :
    operations.meaning (bind substitution term) =
      operations.substitutionArrow substitution ≫ operations.meaning term := by
  have compared := operations.model.interp_bind []
    (fun result position => embed (M := []) (substitution result position)) (embed term)
    (operations.context after) (toUnit (operations.context after)) (operations.model.projections after)
  rw [← embed_substitution, operations.meaning_at_projections,
    operations.meaning_model_value] at compared
  have environment :
      (fun result position => (operations.model.interp [] (embed (substitution result position))).value
        (operations.context after) (toUnit (operations.context after))
        (operations.model.projections after)) =
      (fun result position => operations.meaning (substitution result position)) := by
    funext result position
    exact operations.meaning_at_projections (substitution result position)
  rw [environment] at compared
  exact compared

theorem substitutionArrow_identity (context : Ctx binding) :
    operations.substitutionArrow (fun _ position => Term.var (S := binding) position) =
      𝟙 (operations.context context) :=
  operations.model.tupleEnv_projections context

theorem substitutionArrow_compose {before middle after : Ctx binding}
    (first : Sub binding before middle) (second : Sub binding middle after) :
    operations.substitutionArrow (fun result position => bind second (first result position)) =
      operations.substitutionArrow second ≫ operations.substitutionArrow first := by
  symm
  apply operations.model.tupleEnv_unique
  intro result position
  change (operations.substitutionArrow second ≫ operations.substitutionArrow first) ≫
    projectVar operations.sort position = operations.meaning (bind second (first result position))
  rw [Category.assoc, operations.substitutionArrow_projection]
  exact (operations.meaning_substitution second (first result position)).symm

end Operations

end Mettapedia.OSLF.Binding.ClosedPresentation
