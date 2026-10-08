import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedTerms
import Mathlib.CategoryTheory.Category.ULift

/-!
# Generated indexed values over an independently supplied presheaf map

In the category of presheaves, original-arrow fibre values over a represented
world correspond to actual pointwise fibre values. Both roundtrips use the
Yoneda equivalence: evaluation retains the complete original value, and
encoding reconstructs its whole coherent future section.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations.PresheafReadout

open _root_.CategoryTheory Opposite

universe u
variable {W : Type u} [Category.{u} W]

noncomputable section

abbrev Base (W : Type u) [Category.{u} W] := AsSmall.{u} (Wᵒᵖ ⥤ Type u)
abbrev worldObject (world : W) : Base W := ⟨yoneda.obj world⟩

def indexed {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target) : ArrowSymbol (Base W) :=
  ⟨⟨source⟩, ⟨target⟩, ⟨observation⟩⟩

def argument {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    (world : W) (value : target.obj (op world)) :
    (objectScope (indexed observation).target).1.obj (op (worldObject world)) :=
  (objectNameInverse (indexed observation).target).app (op (worldObject world))
    ⟨yonedaEquiv.symm value⟩

abbrev NativeFibre {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    (world : W) (value : target.obj (op world)) :=
  (fibreMeaning (indexed observation)).decoded.obj
    ⟨op (worldObject world), argument observation world value⟩

def decodePoint {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    (world : W) (value : target.obj (op world)) (supplied : NativeFibre observation world value) :
    {original : source.obj (op world) | observation.app (op world) original = value} := by
  let original := decode (indexed observation) (op (worldObject world))
    (argument observation world value) supplied
  refine ⟨yonedaEquiv original.val.down, ?_⟩
  have commuting : original.val.down ≫ observation = yonedaEquiv.symm value :=
    congrArg ULift.down original.property
  have read := congrArg (fun arrow : yoneda.obj world ⟶ target => yonedaEquiv arrow) commuting
  exact (yonedaEquiv_comp original.val.down observation).symm.trans
    (read.trans (yonedaEquiv.apply_symm_apply value))

def encodePoint {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    (world : W) (value : target.obj (op world))
    (original : source.obj (op world)) (commuting : observation.app (op world) original = value) :
    NativeFibre observation world value :=
  encode (indexed observation) (op (worldObject world))
    (argument observation world value) ⟨yonedaEquiv.symm original⟩ (by
      apply ULift.ext
      exact (yonedaEquiv_symm_naturality_right world observation original).trans
        (congrArg yonedaEquiv.symm commuting))

theorem decode_encode {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    (world : W) (value : target.obj (op world)) (original : source.obj (op world))
    (commuting : observation.app (op world) original = value) :
    decodePoint observation world value (encodePoint observation world value original commuting) =
      ⟨original, commuting⟩ := by
  apply Subtype.ext
  exact yonedaEquiv.apply_symm_apply original

theorem encode_decode {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    (world : W) (value : target.obj (op world)) (supplied : NativeFibre observation world value) :
    encodePoint observation world value (decodePoint observation world value supplied).val
      (decodePoint observation world value supplied).property = supplied := by
  apply Subtype.ext
  apply ULift.ext
  exact yonedaEquiv.symm_apply_apply supplied.val.down

def pointFibreEquiv {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    (world : W) (value : target.obj (op world)) :
    NativeFibre observation world value ≃
      {original : source.obj (op world) | observation.app (op world) original = value} where
  toFun := decodePoint observation world value
  invFun := fun original => encodePoint observation world value original.val original.property
  left_inv := encode_decode observation world value
  right_inv := fun original => decode_encode observation world value original.val original.property

theorem complete_section_recovery {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    (world : W) (value : target.obj (op world)) (supplied : NativeFibre observation world value) :
    (decode (indexed observation) (op (worldObject world)) (argument observation world value)
      supplied).val.down = yonedaEquiv.symm (decodePoint observation world value supplied).val :=
  (yonedaEquiv.symm_apply_apply supplied.val.down).symm

theorem complete_future_readout {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    (world future : W) (before : future ⟶ world) (value : target.obj (op world))
    (supplied : NativeFibre observation world value) :
    ((decode (indexed observation) (op (worldObject world)) (argument observation world value)
      supplied).val.down.app (op future)) before =
        source.map before.op (decodePoint observation world value supplied).val := by
  rw [complete_section_recovery]
  exact yonedaEquiv_symm_app_apply _ _ _

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations.PresheafReadout
