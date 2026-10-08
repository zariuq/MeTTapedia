import Mettapedia.TypeTheory.IndexedPolynomialAdjunction

/-!
# GSOS laws for indexed polynomial families

An arbitrary behavior endofunctor acts on the actual category of indexed
families. Each constructor argument retains its value together with its
complete behavior. A GSOS law maps this polynomial layer to behavior of
the existing free terms. The behavior functor may mix bases and indices;
no pointwise, deterministic or finiteness hypothesis is imposed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedGSOS

open _root_.CategoryTheory IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable (P : IndexedPolynomial.{u, u, u, u} Base Index)
variable (B : Family Base Index ⥤ Family Base Index)

/-- The complete source and behavior of each indexed value. -/
def sourceBehaviourFunctor : Family Base Index ⥤ Family Base Index where
  obj X := fun base index => X base index × B.obj X base index
  map mapping := fun base index => ↾(fun pair =>
    (mapping base index pair.1, B.map mapping base index pair.2))
  map_id X := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro pair
    apply Prod.ext
    · rfl
    · exact congrArg (fun arrow => arrow base index pair.2) (B.map_id X)
  map_comp before after := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro pair
    apply Prod.ext
    · rfl
    · exact congrArg (fun arrow => arrow base index pair.2) (B.map_comp before after)

/-- An actual natural law with free constructor terms as conclusions. -/
abbrev Law :=
  sourceBehaviourFunctor B ⋙ P.endofunctor ⟶
    (FreeAdjunction.monad P).toFunctor ⋙ B

/-- Covariance applies to the whole family arrow, including any other bases
or indices inspected by the behavior functor. -/
theorem map_apply_comp {X Y Z : Family Base Index} (before : X ⟶ Y) (after : Y ⟶ Z)
    (base : Base) (index : Index base) (value : B.obj X base index) :
    B.map after base index (B.map before base index value) =
      B.map (before ≫ after) base index value :=
  congrArg (fun arrow => arrow base index value) (B.map_comp before after).symm

@[simp]
theorem map_apply_identity (X : Family Base Index)
    (base : Base) (index : Index base) (value : B.obj X base index) :
    B.map (𝟙 X) base index value = value :=
  congrArg (fun arrow => arrow base index value) (B.map_id X)

end Mettapedia.TypeTheory.IndexedGSOS
