import Mettapedia.GSLT.Core.ContextualPseudoCwfBicategory

/-!
# The locally faithful base pseudofunctor

The corrected pseudo-CwF bicategory has a canonical projection to the
bicategory of categories: retain the category of contexts, the context
functor of every pseudo morphism, and the base natural transformation of
every corrected 2-cell.

This projection is locally faithful.  The corrected comprehension square is
exactly what makes the displayed component uniquely recoverable from its
base natural transformation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe u v w w'

/-- On each hom category, forget a pseudo CwF morphism and corrected
transformation to its context functor and base natural transformation. -/
def pseudoCwfBaseHomFunctor
    (C D : CwfWithTerminal.{u, v, w, w'}) :
    PseudoCwfMorphism C D ⥤
      (Cat.of C.toCwf.base.Context ⟶ Cat.of D.toCwf.base.Context) where
  obj morphism := morphism.base.toCatHom
  map transformation := transformation.base.toCatHom₂
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The homwise base projection is faithful.  No displayed 2-cell data can
change while its context-level natural transformation remains fixed. -/
instance pseudoCwfBaseHomFunctor_faithful
    (C D : CwfWithTerminal.{u, v, w, w'}) :
    (pseudoCwfBaseHomFunctor C D).Faithful where
  map_injective equality :=
    CorrectedTransformationData.ext_of_base_eq _ _
      (congrArg Cat.Hom₂.toNatTrans equality)

/-- The context-category projection as a pseudofunctor.  Identity and
composition comparisons are reflexive because pseudo CwF morphisms use
ordinary identity and composition on their base functors. -/
def pseudoCwfBasePseudofunctor :
    Pseudofunctor CwfWithTerminal.{u, v, w, w'} Cat where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors
    (fun C => Cat.of C.toCwf.base.Context)
    pseudoCwfBaseHomFunctor
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _
  map₂_whisker_left := by
    intro C D E first F G transformation
    apply Cat.Hom₂.ext
    change Functor.whiskerLeft first.base transformation.base =
      𝟙 _ ≫ Functor.whiskerLeft first.base transformation.base ≫ 𝟙 _
    simp
  map₂_whisker_right := by
    intro C D E F G transformation outer
    apply Cat.Hom₂.ext
    change Functor.whiskerRight transformation.base outer.base =
      𝟙 _ ≫ Functor.whiskerRight transformation.base outer.base ≫ 𝟙 _
    simp
  map₂_associator := by
    intro C D E K first second third
    apply Cat.Hom₂.ext
    change (Functor.associator first.base second.base third.base).hom =
      𝟙 _ ≫
        Functor.whiskerRight (𝟙 _) third.base ≫
          (Functor.associator first.base second.base third.base).hom ≫
            Functor.whiskerLeft first.base (𝟙 _) ≫ 𝟙 _
    simp
  map₂_left_unitor := by
    intro C D morphism
    apply Cat.Hom₂.ext
    change (Functor.leftUnitor morphism.base).hom =
      𝟙 _ ≫ Functor.whiskerRight (𝟙 _) morphism.base ≫
        (Functor.leftUnitor morphism.base).hom
    simp
  map₂_right_unitor := by
    intro C D morphism
    apply Cat.Hom₂.ext
    change (Functor.rightUnitor morphism.base).hom =
      𝟙 _ ≫ Functor.whiskerLeft morphism.base (𝟙 _) ≫
        (Functor.rightUnitor morphism.base).hom
    simp

/-- Local faithfulness stated directly at the pseudofunctor interface. -/
theorem pseudoCwfBasePseudofunctor_map₂_injective
    {C D : CwfWithTerminal.{u, v, w, w'}}
    {F G : PseudoCwfMorphism C D}
    (first second : F ⟶ G)
    (equality : pseudoCwfBasePseudofunctor.map₂ first =
      pseudoCwfBasePseudofunctor.map₂ second) :
    first = second :=
  (pseudoCwfBaseHomFunctor C D).map_injective equality

/-- Positive control: the pseudofunctor sends a pseudo morphism to exactly
its authored context functor. -/
@[simp]
theorem pseudoCwfBasePseudofunctor_map_toFunctor
    {C D : CwfWithTerminal.{u, v, w, w'}}
    (morphism : PseudoCwfMorphism C D) :
    (pseudoCwfBasePseudofunctor.map morphism).toFunctor = morphism.base :=
  rfl

/-- Positive control: its 2-cell action is exactly the corrected
transformation's base natural transformation. -/
@[simp]
theorem pseudoCwfBasePseudofunctor_map₂_toNatTrans
    {C D : CwfWithTerminal.{u, v, w, w'}}
    {F G : PseudoCwfMorphism C D}
    (transformation : F ⟶ G) :
    (pseudoCwfBasePseudofunctor.map₂ transformation).toNatTrans =
      transformation.base := rfl

/-! ## The projection deliberately forgets fibre richness -/

/-- The canonical simply typed families model and the dependent families
model have the same projected category of contexts and substitutions. -/
theorem simple_dependent_context_projection_eq :
    pseudoCwfBasePseudofunctor.obj
        simpleFamiliesWithTerminal.toCwfWithTerminal =
      pseudoCwfBasePseudofunctor.obj familiesCwfWithTerminal := rfl

/-- Sharing the projected context category does not collapse the dependent
type fibre to the constant-family image. -/
theorem same_context_projection_with_genuine_dependency :
    pseudoCwfBasePseudofunctor.obj
        simpleFamiliesWithTerminal.toCwfWithTerminal =
        pseudoCwfBasePseudofunctor.obj familiesCwfWithTerminal ∧
      ∃ A : familiesCwf.Ty Bool, ¬ IsConstantFamily A :=
  ⟨simple_dependent_context_projection_eq,
    exists_dependent_family_outside_simple_image⟩

#print axioms pseudoCwfBaseHomFunctor
#print axioms pseudoCwfBaseHomFunctor_faithful
#print axioms pseudoCwfBasePseudofunctor
#print axioms pseudoCwfBasePseudofunctor_map₂_injective
#print axioms same_context_projection_with_genuine_dependency

end Mettapedia.GSLT.Core.ContextualLadder
