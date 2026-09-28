import Mettapedia.GSLT.LanguageDef.MultiSortedCloneTranslation
import Mathlib.CategoryTheory.Yoneda

/-!
# Operations as representable presheaves on clone contexts

An operation with fixed output sort is exactly a morphism from its input
context to the singleton output context. This identification is natural in
substitution. A clone translation gives a natural map between operation
presheaves over its induced context functor.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MultiSortedClone

open CategoryTheory

universe u v

variable {Sorts : Type u} (clone : MultiSortedClone.{u, v} Sorts)

/-- Operations of one output sort, reindexed by simultaneous substitution. -/
def operationPresheaf (sort : Sorts) :
    (ContextObject clone)ᵒᵖ ⥤ Type v where
  obj X := clone.Hom X.unop.context sort
  map f := TypeCat.ofHom (fun term => clone.substitute term f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro term
    exact clone.substitute_projects term
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro term
    exact (clone.substitute_assoc term f.unop g.unop).symm

/-- Operations are arrows into the singleton output context, naturally in
every input context. -/
def operationPresheafYonedaIso (sort : Sorts) :
    operationPresheaf clone sort ≅
      yoneda.obj (ContextObject.ofList clone [sort]) where
  hom := {
    app X := TypeCat.ofHom (clone.operationAsSingletonMorphism)
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      intro term
      funext i
      refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) i
      rfl }
  inv := {
    app X := TypeCat.ofHom (fun arrow => arrow (0 : Fin 1))
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      intro arrow
      rfl }
  hom_inv_id := by
    ext X term
    rfl
  inv_hom_id := by
    ext X arrow
    funext i
    refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) i
    rfl

end Mettapedia.GSLT.LanguageDef.MultiSortedClone

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory

universe u v

variable {Sorts : Type u}
  {source : MultiSortedClone.{u, v} Sorts}
  {target : MultiSortedClone.{u, v} Sorts}

/-- The operation map of a clone translation is natural over its context
functor. -/
def CloneTranslation.operationNatural
    (translation : CloneTranslation source target) (sort : Sorts) :
    MultiSortedClone.operationPresheaf source sort ⟶
      ((translation.contextFunctor).op ⋙
        MultiSortedClone.operationPresheaf target sort) where
  app X := TypeCat.ofHom translation.map
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro term
    exact translation.map_substitute term f.unop

/-- Under the singleton-context Yoneda representation, a clone translation's
operation map is exactly the Yoneda map of its context functor. -/
theorem CloneTranslation.operationNatural_yoneda
    (translation : CloneTranslation source target) (sort : Sorts) :
    (MultiSortedClone.operationPresheafYonedaIso source sort).hom ≫
        yonedaMap translation.contextFunctor
          (MultiSortedClone.ContextObject.ofList source [sort]) =
      translation.operationNatural sort ≫
        Functor.whiskerLeft translation.contextFunctor.op
          (MultiSortedClone.operationPresheafYonedaIso target sort).hom := by
  ext X term
  funext i
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) i
  rfl

end Mettapedia.GSLT.LanguageDef
