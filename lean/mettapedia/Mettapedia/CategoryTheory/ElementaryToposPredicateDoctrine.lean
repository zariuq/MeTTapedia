import Mettapedia.CategoryTheory.ElementaryToposPredicateImages
import Mettapedia.CategoryTheory.ElementaryTopos

/-!
# The higher-order predicate doctrine of an elementary topos

The fibres are actual subobject orders. Their Heyting operations and both
quantifiers have been constructed from finite limits, Cartesian closure,
and the classifier. Substitution preserves every finite logical operation;
quantification satisfies Frobenius and Beck--Chevalley across actual
pullbacks. The supplied classifier is the doctrine's unique generic truth.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposPredicateDoctrine

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open ElementaryToposPredicateAdjoints ElementaryToposPredicateHeyting
open ElementaryToposPredicateImages

universe u v
variable {C : Type u} [Category.{v} C]
variable [HasFiniteLimits C] [CartesianMonoidalCategory C] [MonoidalClosed C]

def doctrine (classifier : Subobject.Classifier C) :
    PredicateDoctrine.HigherOrder.{u,v,max u v} C := by
  letI : HasImages C := ElementaryToposImages.hasImages classifier
  letI : HasImageMaps C := inferInstance
  letI (X : C) : HeytingAlgebra (Subobject X) := algebra classifier X
  exact {
    Fiber := Subobject
    algebra := fun X => algebra classifier X
    reindex := reindex
    reindex_mono := reindex_mono
    reindex_id := reindex_id
    reindex_comp := reindex_comp
    reindex_top := reindex_top
    reindex_bot := fun f => (forall_adj classifier f).l_bot
    reindex_inf := reindex_inf
    reindex_sup := fun f _ _ => (forall_adj classifier f).l_sup
    reindex_himp := reindex_implication classifier
    existsAlong := existsAlong
    forallAlong := forallAlong classifier
    exists_mono := exists_mono
    forall_mono := forall_mono classifier
    exists_adj := exists_adj
    forall_adj := forall_adj classifier
    frobenius := frobenius classifier
    exists_baseChange := exists_baseChange classifier
    forall_baseChange := forall_baseChange classifier
    generic := {
      object := classifier.Ω
      truth := ElementaryToposPredicateHeyting.truth classifier
      characteristic := fun _ => characteristic classifier
      classifies := fun _ => classifies classifier
      unique := fun _ => characteristic_unique classifier } }

theorem doctrine_reindex (classifier : Subobject.Classifier C) {X Y : C}
    (f : X ⟶ Y) (P : Subobject Y) :
    (doctrine classifier).reindex f P = (Subobject.pullback f).obj P := rfl

theorem doctrine_forall (classifier : Subobject.Classifier C) {X Y : C}
    (f : X ⟶ Y) (P : Subobject X) :
    (doctrine classifier).forallAlong f P =
      Subobject.mk (ElementaryToposPredicateQuantification.universalInclusion
        classifier f P.arrow) := rfl

def ofTopos (topos : ElementaryTopos.{u,v}) :
    PredicateDoctrine.HigherOrder.{u,v,max u v} topos := doctrine topos.classifier

end Mettapedia.CategoryTheory.ElementaryToposPredicateDoctrine
