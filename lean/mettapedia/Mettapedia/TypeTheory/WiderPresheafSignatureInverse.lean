import Mettapedia.TypeTheory.WiderPresheafSignatureEquivalence

/-!
# Constructed inverse dependent signatures

The reverse position equivalence is formed from the supplied forward
signature and its actual shape inverse. Endpoint casts and restriction
coherence are proved explicitly. No reverse signature, operation law or
tree inverse is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.WiderPresheafSignatureEquivalence

open CategoryTheory WiderPresheafDependentFunctions

universe u v w z h k
variable {E : Type v} [Category.{u} E]
variable {shape : E ⥤ Type w} {nextShape : E ⥤ Type h}
variable {position : shape.Elements ⥤ Type z} {nextPosition : nextShape.Elements ⥤ Type k}
variable (signature : Signature (shape := shape) (nextShape := nextShape)
  (position := position) (nextPosition := nextPosition))

theorem inverse_shape_natural {first second : E} (step : first ⟶ second) (label : nextShape.obj first) :
    (signature.shapes second).symm (nextShape.map step label) =
      shape.map step ((signature.shapes first).symm label) := by
  apply (signature.shapes second).injective
  exact ((signature.shapes second).apply_symm_apply _).trans
    ((congrArg (nextShape.map step) ((signature.shapes first).apply_symm_apply label)).symm.trans
      (signature.shape_natural step ((signature.shapes first).symm label)).symm)

theorem inverse_position_value_heq (point : E) (label : nextShape.obj point)
    (value : nextPosition.obj ⟨point, label⟩) :
    HEq (signature.positions point ((signature.shapes point).symm label)
      ((positionsAtNew signature point label).symm value)) value :=
  (positionsAtNew_heq signature point label ((positionsAtNew signature point label).symm value)).symm.trans
    (heq_of_eq ((positionsAtNew signature point label).apply_symm_apply value))

theorem positions_injective_heq {point : E} {first second : shape.obj point}
    (same : first = second) (left : position.obj ⟨point, first⟩) (right : position.obj ⟨point, second⟩)
    (images : HEq (signature.positions point first left) (signature.positions point second right)) : HEq left right := by
  cases same
  exact heq_of_eq ((signature.positions point first).injective (eq_of_heq images))

set_option maxHeartbeats 1000000 in
theorem inverse_position_natural {first second : E} (step : first ⟶ second) (label : nextShape.obj first)
    (value : nextPosition.obj ⟨first, label⟩) :
    HEq ((positionsAtNew signature second (nextShape.map step label)).symm
      (nextPosition.map (argumentMap nextShape step label) value))
      (position.map (argumentMap shape step ((signature.shapes first).symm label))
        ((positionsAtNew signature first label).symm value)) := by
  apply positions_injective_heq signature (inverse_shape_natural signature step label)
  have firstValue := inverse_position_value_heq signature first label value
  have targetValue := inverse_position_value_heq signature second (nextShape.map step label)
    (nextPosition.map (argumentMap nextShape step label) value)
  have forward := signature.position_natural step ((signature.shapes first).symm label)
    ((positionsAtNew signature first label).symm value)
  have sources : (⟨first, signature.shapes first ((signature.shapes first).symm label)⟩ : nextShape.Elements) =
      ⟨first, label⟩ := Sigma.ext rfl (heq_of_eq ((signature.shapes first).apply_symm_apply label))
  have targets : (⟨second, nextShape.map step (signature.shapes first ((signature.shapes first).symm label))⟩ :
      nextShape.Elements) = ⟨second, nextShape.map step label⟩ :=
    Sigma.ext rfl (heq_of_eq (congrArg (nextShape.map step) ((signature.shapes first).apply_symm_apply label)))
  have arrows := ContextualSmallFamilyUniverse.elementsArrow_heq sources targets
    (argumentMap nextShape step (signature.shapes first ((signature.shapes first).symm label)))
    (argumentMap nextShape step label) HEq.rfl
  have moved := ContextualSmallFamilyUniverse.familyMap_heq nextPosition sources targets _ _ arrows _ _ firstValue
  exact targetValue.trans (forward.trans moved).symm

def Signature.symm : Signature (shape := nextShape) (nextShape := shape)
    (position := nextPosition) (nextPosition := position) where
  shapes point := (signature.shapes point).symm
  shape_natural := inverse_shape_natural signature
  positions point label := (positionsAtNew signature point label).symm
  position_natural := inverse_position_natural signature

end Mettapedia.TypeTheory.WiderPresheafSignatureEquivalence
