import Mettapedia.OSLF.Syntax.CartesianModelLexTargetEquivalence
import Mettapedia.OSLF.Syntax.CartesianModelLexPresheafFullness
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Relative finite-limit interpretation with retained firing events

An operational interpretation consists of a product-preserving interpretation
of authored contexts, an object of firing events, and an arrow assigning its
two program endpoints. This is a comma category, so its morphisms preserve
both the context interpretation and the actual event witnesses.

The relative finite-limit classification of contexts lifts to these
event-equipped interpretations in any small finitely complete target. This
result does not require an image or a truth classifier. It also does not
construct the free cartesian-closed operational theory: function types and
their laws require a further relative extension.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits

universe u v u' v' u'' v''

/-- Paired values of a varying object, functorial in every interpretation
map. The two projections are the source and target of an event. -/
noncomputable def pairValues {A : Type u} [Category.{v} A]
    {D : Type u'} [Category.{v'} D] [HasBinaryProducts D]
    (P : A ⥤ D) : A ⥤ D where
  obj a := P.obj a ⨯ P.obj a
  map f := prod.map (P.map f) (P.map f)
  map_id a := by simp
  map_comp f g := by simp [Functor.map_comp, prod.map_map]

/-- Interpret the two endpoints of a selected authored program sort. -/
noncomputable def authoredProgramPair
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type u') [Category.{v'} D] [HasFiniteLimits D]
    (program : C) : CartesianTargetInterpretations C D ⥤ D :=
  pairValues (((CartesianTargetInterpretation C D).ι) ⋙
    (evaluation C D).obj program)

/-- An interpreted context model together with its individual event object
and its endpoint map. The comma-category arrows retain maps of events, not
just inclusion of endpoint predicates. -/
abbrev AuthoredEventInterpretations
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type u') [Category.{v'} D] [HasFiniteLimits D]
    (program : C) :=
  Comma (𝟭 D) (authoredProgramPair C D program)

/-- The corresponding event-equipped interpretation of the relative
finite-limit completion. Its program endpoints are obtained by restriction
to the authored program sort. -/
abbrev LeftExactEventInterpretations
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type u') [Category.{v'} D] [HasFiniteLimits D]
    (program : C) :=
  Comma (𝟭 D)
    (restrictLeftExactTarget C D ⋙ authoredProgramPair C D program)

/-- Equivalences of base interpretations lift to categories retaining an
arbitrary event object over a functorially varying endpoint object. -/
noncomputable def liftEventInterpretationEquivalence
    {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B]
    {D : Type u''} [Category.{v''} D]
    (E : A ≌ B) (P : B ⥤ D) :
    Comma (𝟭 D) (E.functor ⋙ P) ≌ Comma (𝟭 D) P := by
  let F : Comma (𝟭 D) (E.functor ⋙ P) ⥤ Comma (𝟭 D) P :=
    Comma.map (𝟙 ((𝟭 D) ⋙ (𝟭 D)))
      (Functor.rightUnitor (E.functor ⋙ P)).hom
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  exact F.asEquivalence

/-- A morphism of event-equipped interpretations extends uniquely across
any equivalence of their base interpretations, including its event map. -/
theorem liftEventMap_extension_unique
    {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B]
    {D : Type u''} [Category.{v''} D]
    (E : A ≌ B) (P : B ⥤ D)
    (T U : Comma (𝟭 D) (E.functor ⋙ P))
    (f : (liftEventInterpretationEquivalence E P).functor.obj T ⟶
      (liftEventInterpretationEquivalence E P).functor.obj U) :
    ∃! g : T ⟶ U,
      (liftEventInterpretationEquivalence E P).functor.map g = f := by
  let R := (liftEventInterpretationEquivalence E P).functor
  obtain ⟨g, hg⟩ := R.map_surjective f
  refine ⟨g, hg, ?_⟩
  intro h hh
  exact R.map_injective (hh.trans hg.symm)

/-- The relative finite-limit universal property still holds after
adjoining an object of firing events with specified program endpoints. It
is an equivalence on interpretations and their event-preserving maps, in
every small finitely complete target. -/
noncomputable def eventInterpretationEquivalence
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type) [SmallCategory D] [HasFiniteLimits D]
    (program : C) :
    LeftExactEventInterpretations C D program ≌
      AuthoredEventInterpretations C D program :=
  liftEventInterpretationEquivalence
    (cartesianTargetLexEquivalence C D)
    (authoredProgramPair C D program)

/-- The same event-preserving comparison for a presheaf target. This covers
semantic settings that are not themselves small categories, including the
canonical presheaf semantics of authored process languages. -/
noncomputable def presheafEventInterpretationEquivalence
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (B : Type) [SmallCategory B]
    (program : C) :
    LeftExactEventInterpretations C (Bᵒᵖ ⥤ Type) program ≌
      AuthoredEventInterpretations C (Bᵒᵖ ⥤ Type) program :=
  liftEventInterpretationEquivalence
    (cartesianPresheafLexEquivalence C B)
    (authoredProgramPair C (Bᵒᵖ ⥤ Type) program)

end Mettapedia.OSLF.CartesianContextModels
