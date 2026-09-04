import Mettapedia.UniversalAlgebra.Model

/-!
# Homomorphisms of universal-algebra models

A model homomorphism preserves every operation in the selected finitary
signature.  No equation system is needed for the definition.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.Model

universe u v w x

variable {S : Signature.{u}}

/-- A homomorphism between two models of one finitary signature. -/
@[ext] structure Hom {Source : Type v} {Target : Type w}
    (source : Model S Source) (target : Model S Target) where
  toFun : Source → Target
  map_operation : ∀ operation arguments,
    toFun (source.interpret operation arguments) =
      target.interpret operation (fun position => toFun (arguments position))

namespace Hom

instance {Source : Type v} {Target : Type w}
    {source : Model S Source} {target : Model S Target} :
    CoeFun (Hom source target) (fun _homomorphism => Source → Target) :=
  ⟨Hom.toFun⟩

/-- Identity model homomorphism. -/
def id {Carrier : Type v} (model : Model S Carrier) : Hom model model where
  toFun := _root_.id
  map_operation := by intro _operation _arguments; rfl

/-- Composition of model homomorphisms. -/
def comp {First : Type v} {Second : Type w} {Third : Type x}
    {first : Model S First} {second : Model S Second}
    {third : Model S Third}
    (earlier : Hom first second) (later : Hom second third) :
    Hom first third where
  toFun value := later (earlier value)
  map_operation operation arguments := by
    rw [earlier.map_operation, later.map_operation]

@[simp] theorem id_apply {Carrier : Type v} (model : Model S Carrier)
    (value : Carrier) : id model value = value := rfl

@[simp] theorem comp_apply {First : Type v} {Second : Type w}
    {Third : Type x} {first : Model S First} {second : Model S Second}
    {third : Model S Third} (earlier : Hom first second)
    (later : Hom second third) (value : First) :
    comp earlier later value = later (earlier value) := rfl

end Hom

/-- An isomorphism of models, displayed by mutually inverse operation-
preserving homomorphisms. -/
structure Iso {Left : Type v} {Right : Type w}
    (left : Model S Left) (right : Model S Right) where
  hom : Hom left right
  inv : Hom right left
  hom_inv_id : ∀ value, inv (hom value) = value
  inv_hom_id : ∀ value, hom (inv value) = value

namespace Iso

/-- Reflexive model isomorphism. -/
def refl {Carrier : Type v} (model : Model S Carrier) : Iso model model where
  hom := Hom.id model
  inv := Hom.id model
  hom_inv_id := by intro _value; rfl
  inv_hom_id := by intro _value; rfl

/-- Symmetry of model isomorphism. -/
def symm {Left : Type v} {Right : Type w}
    {left : Model S Left} {right : Model S Right}
    (isomorphism : Iso left right) : Iso right left where
  hom := isomorphism.inv
  inv := isomorphism.hom
  hom_inv_id := isomorphism.inv_hom_id
  inv_hom_id := isomorphism.hom_inv_id

end Iso

end Mettapedia.UniversalAlgebra.Model
