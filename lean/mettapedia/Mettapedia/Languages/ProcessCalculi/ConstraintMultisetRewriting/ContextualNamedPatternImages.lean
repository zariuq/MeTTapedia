import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternImages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedImitation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedSelfPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedFlexPair

/-!
# Pattern images of the actual named fresh-helper substitutions

Arity-preserving reindexing and substitution composition carry the existing
image laws to arbitrary named declarations. The heterogeneous flexible-pair
answer transports only its second body along the given result-sort equality.
Its pullback inclusions are injective when the two input occurrences have
injective parameter maps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedPatternImages

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment

variable {S : Signature} {V W Next : Type}
  {source : V → MetaArity S} {target : W → MetaArity S} {next : Next → MetaArity S}

theorem cast_body {first second : MetaArity S} (same : first = second)
    (body : Term (signature S source) first.1 first.2) (patterned : Pattern S source body) :
    Pattern S source (castMetaBody (V := signature S source) same body) := by
  cases same
  exact patterned

theorem reindex_images (forward : V → W) (preserves : ∀ identity, target (forward identity) = source identity) :
    ∀ identity, Pattern S target (reindex forward preserves identity) :=
  fun identity => cast_body (preserves identity) _ (generator_pattern (forward identity))

theorem compose_images (first : Assignment source target) (second : Assignment target next)
    (firstImages : ∀ identity, Pattern S target (first identity))
    (secondImages : ∀ identity, Pattern S next (second identity)) :
    ∀ identity, Pattern S next (Assignment.compose second first identity) :=
  fun identity => instantiate_preserves second secondImages (first identity) (firstImages identity)

theorem heterogeneous_flex_images {Other : Type} [DecidableEq Other]
    (L R : Ctx S) (first second : S.Srt) (same : first = second) (others : Other → MetaArity S)
    {Γ : Ctx S} (left : Ren S L Γ) (right : Ren S R Γ)
    (leftInjective : ∀ sort, Function.Injective (left sort))
    (rightInjective : ∀ sort, Function.Injective (right sort)) :
    ∀ identity, Pattern S
      (ContextualFlexPair.targetDeclarations (ScopePullback.Finite.build left right).context first others)
      (ContextualHeterogeneousFlexPair.answer L R first second same others left right identity) := by
  intro identity
  cases identity with
  | inl chosen =>
      cases chosen with
      | false =>
          exact rename_preserves _ (generator_pattern (S := S)
            (declaration := ContextualFlexPair.targetDeclarations
              (ScopePullback.Finite.build left right).context first others) (.inl ())) _
            ((ScopePullback.Finite.build left right).toLeft_injective rightInjective)
      | true =>
          apply cast_body
          exact rename_preserves _ (generator_pattern (S := S)
            (declaration := ContextualFlexPair.targetDeclarations
              (ScopePullback.Finite.build left right).context first others) (.inl ())) _
            ((ScopePullback.Finite.build left right).toRight_injective leftInjective)
  | inr identity =>
      exact generator_pattern (S := S)
        (declaration := ContextualFlexPair.targetDeclarations
          (ScopePullback.Finite.build left right).context first others) (.inr identity)

variable [DecidableEq V]

theorem imitation_images (identity : V) {Γ : Ctx S} (rho : Ren S (source identity).1 Γ)
    (operator : S.Op (source identity).2) (fields : Args (signature S source) (S.arity operator) Γ)
    (rest : ContextualResidual.Problem source) :
    let update := ContextualNamedImitation.apply source identity rho operator fields rest
    ∀ name, Pattern S update.declaration (update.answer name) := by
  dsimp only [ContextualNamedImitation.apply, id]
  exact compose_images _ _ (reindex_images _ _)
    (ContextualSolverPatternImages.imitation_images _ _ _)

theorem self_images (identity : V) {Γ : Ctx S} (left right : Ren S (source identity).1 Γ)
    (rest : ContextualResidual.Problem source) :
    let update := ContextualNamedSelfPair.apply source identity left right rest
    ∀ name, Pattern S update.declaration (update.answer name) := by
  dsimp only [ContextualNamedSelfPair.apply, id]
  exact compose_images _ _ (reindex_images _ _)
    (ContextualSolverPatternImages.same_hole_images _ _ _)

theorem flex_images (first second : V) (different : first ≠ second)
    (sorts : (source first).2 = (source second).2) {Γ : Ctx S}
    (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Γ)
    (leftInjective : ∀ sort, Function.Injective (left sort))
    (rightInjective : ∀ sort, Function.Injective (right sort))
    (rest : ContextualResidual.Problem source) :
    let update := ContextualNamedFlexPair.apply source first second different sorts left right rest
    ∀ name, Pattern S update.declaration (update.answer name) := by
  dsimp only [ContextualNamedFlexPair.apply, ContextualHeterogeneousFlexPair.apply, id]
  exact compose_images _ _ (reindex_images _ _)
    (heterogeneous_flex_images _ _ _ _ sorts _ left right leftInjective rightInjective)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedPatternImages
