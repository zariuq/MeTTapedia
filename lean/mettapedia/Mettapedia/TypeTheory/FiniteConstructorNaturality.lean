import Mettapedia.TypeTheory.FiniteConstructorMaps
import Mathlib.CategoryTheory.Types.Basic

/-!
# Natural encoding of finite constructor data

Sort-indexed families and pointwise field maps form a category. Constructor
data and the full payload function spaces give two functors into types.
The actual constructor encoder is an injective natural transformation.
Guarded payload recovery remains the finer statement in FiniteConstructorMaps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.FiniteConstructorEncoding
open CategoryTheory
universe u s

structure Family (SortCode : Type s) where
  value : SortCode → Type u

namespace Family
variable {SortCode : Type s}
instance : Category (Family.{u} SortCode) where
  Hom source target := ∀ sort, source.value sort → target.value sort
  id _ _ value := value
  comp first second sort value := second sort (first sort value)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
end Family

variable {SortCode : Type s} (signature : Signature (SortCode := SortCode))

def dataFunctor : Family.{u} SortCode ⥤ Type u where
  obj source := Data source.value signature
  map fieldMap := ↾(mapData fieldMap signature)
  map_id source := by apply ConcreteCategory.hom_ext; intro data; exact mapData_id signature data
  map_comp first second := by apply ConcreteCategory.hom_ext; intro data; exact (mapData_comp first second signature data).symm

def payloadFunctor : Family.{u} SortCode ⥤ Type u where
  obj source := Payload source.value signature
  map fieldMap := ↾(mapPayload fieldMap signature)
  map_id source := by apply ConcreteCategory.hom_ext; intro payload; exact mapPayload_id signature payload
  map_comp first second := by apply ConcreteCategory.hom_ext; intro payload; exact (mapPayload_comp first second signature payload).symm

def encodingTransformation : dataFunctor.{u} signature ⟶ payloadFunctor signature where
  app source := ↾(encode source.value signature)
  naturality {X Y} fieldMap := by
    apply ConcreteCategory.hom_ext
    intro data
    exact (mapPayload_encode fieldMap signature data).symm

theorem encoding_injective (source : Family.{u} SortCode) :
    Function.Injective ((encodingTransformation signature).app source) := encode_injective source.value signature

theorem occurrence_preserved {source target : Family.{u} SortCode} (fieldMap : source ⟶ target)
    (data : (dataFunctor signature).obj source) :
    ((dataFunctor signature).map fieldMap data).1 = data.1 := rfl

#print axioms dataFunctor
#print axioms payloadFunctor
#print axioms encodingTransformation
#print axioms encoding_injective
end Mettapedia.TypeTheory.FiniteConstructorEncoding
