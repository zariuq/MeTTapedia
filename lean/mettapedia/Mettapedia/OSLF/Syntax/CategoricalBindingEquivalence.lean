import Mettapedia.OSLF.Syntax.CategoricalBindingInterpretationMaps

/-!
# Categorical equivalence for binding interpretations

The second-order context category classifies binding signatures with chosen
function objects. Its structured interpretations are functors preserving the
specified context products, exponentials, and authored operations. Morphisms
are natural transformations; the assignment law proved for reconstructed maps
ensures that these transformations preserve the whole term interpretation.

This is the binding component of the operational classifier. Equation
presentations and firing evidence require their own relative extensions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingEquivalence

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

variable {S : Signature}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- A structure-preserving interpretation of the second-order context
category. The chosen product/exponential data and operation laws are stated
independently of the model reconstructed from them. -/
structure StructuredFunctor (S : Signature) (D : Type u)
    [Category.{v} D] [CartesianMonoidalCategory D] where
  carrier : SecondOrderContext.Object S ⥤ D
  preserving : Preserving carrier

instance : Category (StructuredFunctor S D) where
  Hom F G := F.carrier ⟶ G.carrier
  id F := 𝟙 F.carrier
  comp f g := f ≫ g
  id_comp := by intros; simp
  comp_id := by intros; simp
  assoc := by intros; exact Category.assoc _ _ _

/-- The classifying construction on objects and on all contextual
interpretation maps. -/
def bindingClassifier : Interpretation S D ⥤ StructuredFunctor S D where
  obj M := ⟨M.model.classifyingFunctor, M.model.classifyingPreserving⟩
  map h := classifyingMap h
  map_id M := by
    apply NatTrans.ext
    funext X
    exact Model.familyMap_id M.model X.arities
  map_comp f g := by
    apply NatTrans.ext
    funext X
    exact Model.familyMap_comp f.underlying.power g.underlying.power X.arities

instance : (bindingClassifier (S := S) (D := D)).Full where
  map_surjective := by
    intro M N τ
    refine ⟨Hom.ofNat τ, ?_⟩
    exact Hom.classifyingMap_ofNat τ

instance : (bindingClassifier (S := S) (D := D)).Faithful where
  map_injective := by
    intro M N f g same
    change classifyingMap f = classifyingMap g at same
    have recovered := congrArg Hom.ofNat same
    simpa only [Hom.ofNat_classifyingMap] using recovered

instance : (bindingClassifier (S := S) (D := D)).EssSurj where
  mem_essImage F := by
    refine ⟨⟨F.preserving.toModel⟩, ⟨?_⟩⟩
    exact {
      hom := F.preserving.isoClassifying.inv
      inv := F.preserving.isoClassifying.hom
      hom_inv_id := F.preserving.isoClassifying.inv_hom_id
      inv_hom_id := F.preserving.isoClassifying.hom_inv_id }

instance : (bindingClassifier (S := S) (D := D)).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- The universal property for the binding signature: models with maps
preserving contextual assignment are equivalent to structure-preserving
interpretations of its syntactic context category. -/
noncomputable def bindingEquivalence :
    Interpretation S D ≌ StructuredFunctor S D :=
  (bindingClassifier (S := S) (D := D)).asEquivalence

end Mettapedia.OSLF.Binding.CategoricalBindingEquivalence

#print axioms Mettapedia.OSLF.Binding.CategoricalBindingEquivalence.bindingEquivalence
