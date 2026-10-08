import Mettapedia.CategoryTheory.CompleteCocompleteTopos
import Mettapedia.CategoryTheory.SliceClassifierPullback
import Mettapedia.CategoryTheory.CanonicalSlicePullback
import Mettapedia.TypeTheory.PresheafClosedComprehension
import Mettapedia.GSLT.Topos.SubobjectClassifier

/-!
# Logical substitution between complete and cocomplete presheaf slices

The truth object is the canonical sieve presheaf, obtained from the proved
representation of subobjects. Its product with each base gives the actual
slice classifier. Pullback preserves that classifier through its canonical
characteristic comparison, as well as the chosen cartesian closed structure.
The resulting arrows live in the bicategory of complete and cocomplete
elementary topoi with logical morphisms.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.TypeTheory.PresheafSliceLogicalAction

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafSlice

universe u
variable {C : Type u} [Category.{u} C]

def baseClassifier : Subobject.Classifier (Face.{u, u, u} C) :=
  SubobjectRepresentableBy.classifier
    (Mettapedia.GSLT.Topos.presheafSubobjectRepresentableByOmega C)

def sliceTopos (base : Face.{u, u, u} C) : CompleteCocompleteTopos.{u, u + 1, u} where
  Carrier := Over base
  category := inferInstance
  complete := inferInstance
  cocomplete := inferInstance
  finite := inferInstance
  cartesian := PresheafClosedComprehension.slice_cartesian base
  closed := PresheafClosedComprehension.slice_closed base
  classifier := SliceClassifier.overClassifier baseClassifier base

def substitution {source target : Face.{u, u, u} C} (route : source ⟶ target) :
    sliceTopos target ⟶ sliceTopos source where
  functor := Over.pullback route
  finite := by
    let := (Over.mapPullbackAdj route).rightAdjoint_preservesLimits
    infer_instance
  closed := PresheafClosedComprehension.substitution_closed route
  classifier := SliceClassifierPullback.canonical_comparison_invertible route baseClassifier

@[simp] theorem substitution_functor {source target : Face.{u, u, u} C}
    (route : source ⟶ target) :
    (substitution route).functor = Over.pullback route := rfl

def classifierComparison {source target : Face.{u, u, u} C}
    (route : source ⟶ target) :
    (substitution route).functor.obj (sliceTopos target).classifier.Ω ≅
      (sliceTopos source).classifier.Ω :=
  SliceClassifierPullback.classifierComparison route baseClassifier

theorem characteristic_substitution {source target : Face.{u, u, u} C}
    (route : source ⟶ target) {first second : Over target}
    (inclusion : first ⟶ second) [Mono inclusion] :
    (Over.pullback route).map ((sliceTopos target).classifier.χ inclusion) ≫
        (classifierComparison route).hom =
      (sliceTopos source).classifier.χ ((substitution route).functor.map inclusion) :=
  SliceClassifierPullback.characteristic_substitution route baseClassifier inclusion

end Mettapedia.TypeTheory.PresheafSliceLogicalAction
