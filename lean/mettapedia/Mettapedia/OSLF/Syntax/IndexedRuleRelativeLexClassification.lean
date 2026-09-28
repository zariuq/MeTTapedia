import Mettapedia.OSLF.Syntax.IndexedRuleFiniteListSkeleton
import Mettapedia.OSLF.Syntax.IndexedRuleFiniteProductClassification
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Whiskering

/-!
# Relative finite-limit classification of finitary indexed rule algebras

The finite-list skeleton makes the operational context category small. This
module compares independently specified indexed rule algebras with the
existing relative finite-limit presentation in sets. The comparison retains
constructor and premise positions through the small-context equivalence.
Binding and equation models vary in the larger authored classifier and are
not identified with this fixed-family component.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Mettapedia.OSLF.Binding.IndexedRuleRelativeLexClassification

open CategoryTheory
open CategoryTheory.Limits
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts
open Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton
open Mettapedia.OSLF.CartesianContextModels

variable {Judgment : Type}
variable (P : IndexedPolynomial.{0, 0, 0, 0}
  Unit (fun _ => Judgment))

/-- Product-preserving interpretations of the full finite-context category. -/
def fullProductProperty : ObjectProperty (Context P ⥤ Type) :=
  fun F => PreservesFiniteProducts F

abbrev FullProductModels := (fullProductProperty P).FullSubcategory

/-- Package a product interpretation as an object of the corresponding
full subcategory, without altering its functor or natural maps. -/
noncomputable def packageProductInterpretations :
    ProductInterpretation.{0,0,0} P ⥤ FullProductModels P where
  obj X := ⟨X.functor, X.preserves⟩
  map := fun {X Y} f => by
    change (X.functor ⟶ Y.functor) at f
    exact ObjectProperty.homMk f
  map_id _ := by
    apply ObjectProperty.hom_ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    rfl

/-- Read the same data back into the independent interpretation structure. -/
noncomputable def unpackProductInterpretations :
    FullProductModels P ⥤ ProductInterpretation.{0,0,0} P where
  obj X := ⟨X.1, X.2⟩
  map := fun {X Y} f => by
    exact f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Packaging does not change the mathematical category of product
interpretations; it only makes a full-subcategory restriction available. -/
instance : (packageProductInterpretations P).Faithful where
  map_injective := fun equal => by
    have exactMap := congrArg InducedCategory.Hom.hom equal
    exact exactMap

instance : (packageProductInterpretations P).Full where
  map_surjective := fun f => ⟨f.hom, by
    apply ObjectProperty.hom_ext
    rfl⟩

instance : (packageProductInterpretations P).EssSurj where
  mem_essImage X := by
    refine ⟨⟨X.1, X.2⟩, ⟨?_⟩⟩
    have equal : (packageProductInterpretations P).obj ⟨X.1, X.2⟩ = X := by
      apply ObjectProperty.FullSubcategory.ext
      rfl
    exact eqToIso equal

instance : (packageProductInterpretations P).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

noncomputable def packagingEquivalence :
    ProductInterpretation.{0,0,0} P ≌ FullProductModels P :=
  (packageProductInterpretations P).asEquivalence

/-- Product preservation is invariant under natural isomorphism. -/
instance : (ProductModel (ListContext P)).IsClosedUnderIsomorphisms where
  of_iso iso h := by
    have hpreserves : PreservesFiniteProducts _ := h
    letI := hpreserves
    exact ⟨fun n => preservesLimitsOfShape_of_natIso (J := Discrete (Fin n)) iso⟩

/-- A product interpretation on all finite contexts is equivalent to one
on their enumerated skeleton. The reverse direction uses the actual context
isomorphism, rather than an assumption that arbitrary finite carriers are
definitionally lists. -/
theorem productProperty_comparison :
    (ProductModel (ListContext P)).inverseImage
      (Equivalence.congrLeft (E := Type) (listEquivalence P).symm).functor =
        fullProductProperty P := by
  funext F
  apply propext
  constructor
  · intro h
    let e := listEquivalence P
    have hrestricted : PreservesFiniteProducts (e.functor ⋙ F) := by
      change PreservesFiniteProducts ((listEquivalence P).functor ⋙ F) at h
      exact h
    have hinverse : PreservesFiniteProducts e.inverse := inferInstance
    have hcomposed : PreservesFiniteProducts
        (e.inverse ⋙ (e.functor ⋙ F)) := inferInstance
    let comparison : e.inverse ⋙ (e.functor ⋙ F) ≅ F :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.counitIso F ≪≫ Functor.leftUnitor F
    exact ⟨fun n => preservesLimitsOfShape_of_natIso
      (J := Discrete (Fin n)) comparison⟩
  · intro h
    have hpreserves : PreservesFiniteProducts F := h
    letI := hpreserves
    change PreservesFiniteProducts ((listEquivalence P).functor ⋙ F)
    infer_instance

/-- Restriction along the finite-list equivalence compares all product
interpretations and all ordinary interpretation maps. -/
noncomputable def finiteListModelEquivalence :
    FullProductModels P ≌ Models (ListContext P) :=
  Equivalence.congrFullSubcategory
    (Equivalence.congrLeft (E := Type) (listEquivalence P).symm)
    (productProperty_comparison P)

/-- A finitary indexed-rule algebra determines, and is determined by, a
left-exact Set-valued interpretation of the relative finite-limit
presentation of its finite operational contexts. This is an equivalence of
categories, including ordinary rule-algebra and interpretation maps. -/
noncomputable def ruleLexSetClassification
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape)) :
    RuleAlgebraModel.{0,0,0} P ≌ LexSetSemantics (ListContext P) :=
  (((finiteProductClassification P finitePositions).trans
      (packagingEquivalence P)).trans
      (finiteListModelEquivalence P)).trans
    (cartesianModelsEquivLexSetSemantics (ListContext P))

end Mettapedia.OSLF.Binding.IndexedRuleRelativeLexClassification
