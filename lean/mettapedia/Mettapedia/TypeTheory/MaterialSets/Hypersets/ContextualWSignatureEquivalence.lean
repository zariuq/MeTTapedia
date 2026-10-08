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

theorem forward_inverse_position {first second : D} (label : nextShape.obj first) (step : first ⟶ second)
    (branch : Position nextShape nextPosition label step) :
    HEq (ContextualWSignature.forwardPosition signature ((signature.shapes first).symm label) step
      (ContextualWSignature.forwardPosition (inverseSignature signature) label step branch)) branch := by
  obtain ⟨original, rfl⟩ := (signature.shapes first).surjective label
  let oldBranch := (ContextualWSignature.forwardPosition signature original step).symm branch
  have restored := inverse_forward_position signature original step oldBranch
  have actualBack : HEq
      (ContextualWSignature.forwardPosition (inverseSignature signature) (signature.shapes first original) step branch)
      oldBranch := by
    exact (heq_of_eq (congrArg
      (ContextualWSignature.forwardPosition (inverseSignature signature) (signature.shapes first original) step)
      ((ContextualWSignature.forwardPosition signature original step).apply_symm_apply branch))).symm.trans restored
  exact (ContextualWSignature.forwardPosition_labels_heq signature
    ((signature.shapes first).symm_apply_apply original) step _ oldBranch actualBack).trans
      (heq_of_eq ((ContextualWSignature.forwardPosition signature original step).apply_symm_apply branch))

theorem double_inverse_position_right {first second : D} (label : nextShape.obj first) (step : first ⟶ second)
    (branch : Position nextShape nextPosition (signature.shapes first ((signature.shapes first).symm label)) step) :
    HEq ((ContextualWSignature.forwardPosition (inverseSignature signature) label step).symm
      ((ContextualWSignature.forwardPosition signature ((signature.shapes first).symm label) step).symm branch))
      branch := by
  let original := (ContextualWSignature.forwardPosition (inverseSignature signature) label step).symm
    ((ContextualWSignature.forwardPosition signature ((signature.shapes first).symm label) step).symm branch)
  have restored : ContextualWSignature.forwardPosition signature ((signature.shapes first).symm label) step
      (ContextualWSignature.forwardPosition (inverseSignature signature) label step original) = branch := by
    rw [show ContextualWSignature.forwardPosition (inverseSignature signature) label step original =
      (ContextualWSignature.forwardPosition signature ((signature.shapes first).symm label) step).symm branch from
        (ContextualWSignature.forwardPosition (inverseSignature signature) label step).apply_symm_apply _]
    exact (ContextualWSignature.forwardPosition signature ((signature.shapes first).symm label) step).apply_symm_apply branch
  exact ((heq_of_eq restored).symm.trans (forward_inverse_position signature label step original)).symm

theorem forward_inverse_raw {point : D} (tree : RawTree nextShape nextPosition point) :
    ContextualWSignature.mapRaw signature (ContextualWSignature.mapRaw (inverseSignature signature) tree) = tree := by
  induction tree with
  | @sup point label children earlier =>
    apply RawTree.sup_eq_of_cast ((signature.shapes point).apply_symm_apply label)
    intro next arrow branch
    refine (earlier next arrow _).trans ?_
    exact RawTree.children_eq label children rfl _ _
      ((double_inverse_position_right signature label arrow branch).trans (cast_heq _ _).symm)

noncomputable def naturalEquiv (point : D) :
    NaturalTree shape position point ≃ NaturalTree nextShape nextPosition point where
  toFun := ContextualWSignature.mapNatural signature
  invFun := ContextualWSignature.mapNatural (inverseSignature signature)
  left_inv tree := Subtype.ext (inverse_forward_raw signature tree.val)
  right_inv tree := Subtype.ext (forward_inverse_raw signature tree.val)

theorem natural_forward_restrict {first second : D} (step : first ⟶ second)
    (tree : NaturalTree shape position first) :
    naturalEquiv signature second ((ContextualWTypes.family shape position).map step tree) =
      (ContextualWTypes.family nextShape nextPosition).map step (naturalEquiv signature first tree) :=
  ContextualWSignature.mapNatural_restrict signature step tree

theorem natural_inverse_restrict {first second : D} (step : first ⟶ second)
    (tree : NaturalTree nextShape nextPosition first) :
    (naturalEquiv signature second).symm ((ContextualWTypes.family nextShape nextPosition).map step tree) =
      (ContextualWTypes.family shape position).map step ((naturalEquiv signature first).symm tree) :=
  ContextualWSignature.mapNatural_restrict (inverseSignature signature) step tree

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSignatureEquivalence
