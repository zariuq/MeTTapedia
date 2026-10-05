import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSignature
import Mettapedia.TypeTheory.WiderPresheafSignatureInverse

/-!
# Actual inverse full contextual W signature transport

The reverse dependent signature is constructed from the forward shape and
position equivalences. Both raw tree maps use indexed structural recursion
over all future arrows and positions. Position casts and the inverse laws
are proved from those authored signature data; neither a W inverse nor a
decoder is supplied.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSignatureEquivalence

open CategoryTheory
open Mettapedia.TypeTheory
open ContextualWTypes (RawTree Position NaturalTree)

universe u
variable {D : Type u} [Category.{u} D]
variable {shape nextShape : D ⥤ Type u}
variable {position : shape.Elements ⥤ Type u} {nextPosition : nextShape.Elements ⥤ Type u}

def toWider (signature : ContextualWSignature.Signature (shape := shape) (nextShape := nextShape)
    (position := position) (nextPosition := nextPosition)) :
    WiderPresheafSignatureEquivalence.Signature (shape := shape) (nextShape := nextShape)
      (position := position) (nextPosition := nextPosition) :=
  ⟨signature.shapes, signature.shape_natural, signature.positions, signature.position_natural⟩

def fromWider (signature : WiderPresheafSignatureEquivalence.Signature (shape := shape) (nextShape := nextShape)
    (position := position) (nextPosition := nextPosition)) :
    ContextualWSignature.Signature (shape := shape) (nextShape := nextShape)
      (position := position) (nextPosition := nextPosition) :=
  ⟨signature.shapes, signature.shape_natural, signature.positions, signature.position_natural⟩

variable (signature : ContextualWSignature.Signature (shape := shape) (nextShape := nextShape)
  (position := position) (nextPosition := nextPosition))

def inverseSignature : ContextualWSignature.Signature (shape := nextShape) (nextShape := shape)
    (position := nextPosition) (nextPosition := position) :=
  fromWider (toWider signature).symm

theorem inverse_forward_position {first second : D} (label : shape.obj first) (step : first ⟶ second)
    (branch : Position shape position label step) :
    HEq (ContextualWSignature.forwardPosition (inverseSignature signature) (signature.shapes first label) step
        (ContextualWSignature.forwardPosition signature label step branch)) branch := by
  have labels : ((toWider signature).shapes second).symm (nextShape.map step (signature.shapes first label)) =
      shape.map step label :=
    (congrArg ((signature.shapes second).symm) (signature.shape_natural step label).symm).trans
      ((signature.shapes second).symm_apply_apply (shape.map step label))
  have inverseValue := WiderPresheafSignatureEquivalence.inverse_position_value_heq (toWider signature)
    second (nextShape.map step (signature.shapes first label))
    (ContextualWSignature.forwardPosition signature label step branch)
  have forwardValue := ContextualWSignature.forwardPosition_heq signature label step branch
  have reflected := WiderPresheafSignatureEquivalence.positions_injective_heq (toWider signature)
    labels _ branch (inverseValue.trans forwardValue)
  exact (ContextualWSignature.forwardPosition_heq (inverseSignature signature)
    (signature.shapes first label) step (ContextualWSignature.forwardPosition signature label step branch)).trans reflected

theorem double_inverse_position {first second : D} (label : shape.obj first) (step : first ⟶ second)
    (branch : Position shape position ((signature.shapes first).symm (signature.shapes first label)) step) :
    HEq ((ContextualWSignature.forwardPosition signature label step).symm
      ((ContextualWSignature.forwardPosition (inverseSignature signature) (signature.shapes first label) step).symm branch))
      branch := by
  let original := (ContextualWSignature.forwardPosition signature label step).symm
    ((ContextualWSignature.forwardPosition (inverseSignature signature) (signature.shapes first label) step).symm branch)
  have restored : ContextualWSignature.forwardPosition (inverseSignature signature) (signature.shapes first label) step
      (ContextualWSignature.forwardPosition signature label step original) = branch := by
    rw [show ContextualWSignature.forwardPosition signature label step original =
      (ContextualWSignature.forwardPosition (inverseSignature signature) (signature.shapes first label) step).symm branch from
        (ContextualWSignature.forwardPosition signature label step).apply_symm_apply _]
    exact (ContextualWSignature.forwardPosition (inverseSignature signature) (signature.shapes first label) step).apply_symm_apply branch
  exact ((heq_of_eq restored).symm.trans (inverse_forward_position signature label step original)).symm

theorem inverse_forward_raw {point : D} (tree : RawTree shape position point) :
    ContextualWSignature.mapRaw (inverseSignature signature) (ContextualWSignature.mapRaw signature tree) = tree := by
  induction tree with
  | @sup point label children earlier =>
    apply RawTree.sup_eq_of_cast ((signature.shapes point).symm_apply_apply label)
    intro next arrow branch
    refine (earlier next arrow _).trans ?_
    exact RawTree.children_eq label children rfl _ _
      ((double_inverse_position signature label arrow branch).trans (cast_heq _ _).symm)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSignatureEquivalence
