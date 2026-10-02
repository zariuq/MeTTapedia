import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Constructor references in collection algebra declarations

Renaming a generated signature must transport the unit constructor named by
its collection metadata. Flattening remains unchanged. These laws concern
metadata transport; existence and sorting of the renamed unit must still be
proved in the actual generated language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.StructuralMorphism

open Mettapedia.OSLF.MeTTaIL.Syntax

@[simp] theorem mapCollectionAlgebra_flatten (constructor : String → String)
    (algebra : CollectionAlgebra) :
    (mapCollectionAlgebra constructor algebra).flatten = algebra.flatten := rfl

@[simp] theorem mapCollectionAlgebra_unit (constructor : String → String)
    (algebra : CollectionAlgebra) :
    (mapCollectionAlgebra constructor algebra).unit = algebra.unit.map constructor := rfl

@[simp] theorem mapCollectionAlgebra_id (algebra : CollectionAlgebra) :
    mapCollectionAlgebra _root_.id algebra = algebra := by
  cases algebra
  simp [mapCollectionAlgebra]

/-- Fixing each referenced unit leaves the metadata itself unchanged. -/
theorem mapCollectionAlgebra_eq_self (constructor : String → String)
    (algebra : CollectionAlgebra)
    (fixed : ∀ unit, algebra.unit = some unit → constructor unit = unit) :
    mapCollectionAlgebra constructor algebra = algebra := by
  cases algebra with
  | mk flatten unit =>
      cases unit with
      | none => rfl
      | some name =>
          have equal := fixed name rfl
          simp [mapCollectionAlgebra, equal]

/-- Iterated signature generation transports references by the same composition. -/
theorem mapCollectionAlgebra_comp (first second : String → String)
    (algebra : CollectionAlgebra) :
    mapCollectionAlgebra second (mapCollectionAlgebra first algebra) =
      mapCollectionAlgebra (second ∘ first) algebra := by
  cases algebra
  simp [mapCollectionAlgebra, Option.map_map]

end Mettapedia.GSLT.LanguageDef.StructuralMorphism
