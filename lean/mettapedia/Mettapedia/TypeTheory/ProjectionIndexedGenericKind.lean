import Mettapedia.TypeTheory.ProjectionIndexedComprehension
import Mettapedia.CategoryTheory.PredicateDoctrine

/-!
# Generic predicates based on actual terminal kinds

The type and predicate fibrations may have different presentations of
their common base. The domain of an actual type over a terminal object
is compared after the supplied base functor. Classification is transported
along that domain isomorphism and its uniqueness is derived.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.TypeTheory.ProjectionIndexedComprehension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open HasFibers
open Mettapedia.CategoryTheory.FibrationTwoCategory
open Mettapedia.CategoryTheory.PredicateDoctrine

universe u v f h b c w

variable {projection : Fibration.{u,v}} [HasFibers.{h,f} projection.functor]
  {B : Type b} [Category.{c} B]

set_option linter.checkUnivs false in
structure GenericKindPresentation (model : Data.{u,v,f,h} projection)
    (baseFunctor : projection.Base ⥤ B) {doctrine : IndexedHeyting.{b,c,w} B}
    (generic : GenericPredicate B doctrine) where
  object : projection.Total
  baseTerminal : IsTerminal (projection.functor.obj object)
  domainIso : baseFunctor.obj (model.comprehension.display.obj object).left ≅ generic.object

namespace GenericKindPresentation

variable {model : Data.{u,v,f,h} projection} {baseFunctor : projection.Base ⥤ B}
  {doctrine : IndexedHeyting.{b,c,w} B} {generic : GenericPredicate B doctrine}
  (presentation : GenericKindPresentation model baseFunctor generic)

def transported : GenericPredicate B doctrine where
  object := baseFunctor.obj (model.comprehension.display.obj presentation.object).left
  truth := doctrine.reindex presentation.domainIso.hom generic.truth
  characteristic X predicate := generic.characteristic X predicate ≫ presentation.domainIso.inv
  classifies X predicate := by
    rw [← doctrine.reindex_comp, Category.assoc, presentation.domainIso.inv_hom_id,
      Category.comp_id]
    exact generic.classifies X predicate
  unique X predicate map classifies := by
    have mapped : map ≫ presentation.domainIso.hom = generic.characteristic X predicate :=
      generic.unique X predicate (map ≫ presentation.domainIso.hom)
        ((doctrine.reindex_comp _ _ _).trans classifies)
    calc
      map = (map ≫ presentation.domainIso.hom) ≫ presentation.domainIso.inv := by
        rw [Category.assoc, presentation.domainIso.hom_inv_id, Category.comp_id]
      _ = generic.characteristic X predicate ≫ presentation.domainIso.inv :=
        congrArg (fun arrow => arrow ≫ presentation.domainIso.inv) mapped

theorem transported_truth :
    (transported presentation).truth =
      doctrine.reindex presentation.domainIso.hom generic.truth := rfl

theorem transported_classifies (X : B) (predicate : doctrine.Fiber X) :
    doctrine.reindex ((transported presentation).characteristic X predicate)
        (transported presentation).truth = predicate :=
  (transported presentation).classifies X predicate

theorem transported_unique (X : B) (predicate : doctrine.Fiber X)
    (map : X ⟶ (transported presentation).object)
    (classifies : doctrine.reindex map (transported presentation).truth = predicate) :
    map = (transported presentation).characteristic X predicate :=
  (transported presentation).unique X predicate map classifies

theorem transported_characteristic_substitution {X Y : B} (map : X ⟶ Y)
    (predicate : doctrine.Fiber Y) :
    (transported presentation).characteristic X (doctrine.reindex map predicate) =
      map ≫ (transported presentation).characteristic Y predicate :=
  (transported presentation).characteristic_reindex map predicate

end GenericKindPresentation

end Mettapedia.TypeTheory.ProjectionIndexedComprehension
