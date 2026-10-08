import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedPresheafReadout

/-!
# Actual native restriction of generated presheaf-world fibres

An observation-world arrow induces an original arrow between the represented
world presheaves. The generated argument and dependent fibre restrict along
that exact arrow. Their decoded values follow the original presheaf action;
encoding a whole source value commutes with this native restriction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations.PresheafReadout

open _root_.CategoryTheory Opposite

universe u
variable {W : Type u} [Category.{u} W]

noncomputable section

def worldArrow {world future : W} (before : future ⟶ world) :
    worldObject future ⟶ worldObject world := ⟨yoneda.map before⟩

theorem argument_restriction {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    {world future : W} (before : future ⟶ world) (value : target.obj (op world)) :
    (objectScope (indexed observation).target).1.map (worldArrow before).op
        (argument observation world value) =
      argument observation future (target.map before.op value) := by
  change (⟨PUnit.unit, ⟨yoneda.map before ≫ yonedaEquiv.symm value⟩⟩ :
    (objectScope (indexed observation).target).1.obj (op (worldObject future))) =
      ⟨PUnit.unit, ⟨yonedaEquiv.symm (target.map before.op value)⟩⟩
  exact congrArg (fun arrow : yoneda.obj future ⟶ target =>
    (⟨PUnit.unit, ⟨arrow⟩⟩ :
      (objectScope (indexed observation).target).1.obj (op (worldObject future))))
        (yonedaEquiv_symm_naturality_left before target value)

def restrict {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    {world future : W} (before : future ⟶ world) (value : target.obj (op world))
    (supplied : NativeFibre observation world value) :
    NativeFibre observation future (target.map before.op value) :=
  (fibreMeaning (indexed observation)).decoded.map
    (CategoryOfElements.homMk (F := (objectScope (indexed observation).target).1)
      ⟨op (worldObject world), argument observation world value⟩
      ⟨op (worldObject future), argument observation future (target.map before.op value)⟩
      (worldArrow before).op (argument_restriction observation before value)) supplied

theorem restrict_decode {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    {world future : W} (before : future ⟶ world) (value : target.obj (op world))
    (supplied : NativeFibre observation world value) :
    (decodePoint observation future (target.map before.op value)
      (restrict observation before value supplied)).val =
        source.map before.op (decodePoint observation world value supplied).val := by
  change yonedaEquiv (yoneda.map before ≫ supplied.val.down) =
    source.map before.op (yonedaEquiv supplied.val.down)
  exact (yonedaEquiv_naturality supplied.val.down before).symm

theorem restrict_encode {source target : Wᵒᵖ ⥤ Type u} (observation : source ⟶ target)
    {world future : W} (before : future ⟶ world) (value : target.obj (op world))
    (original : source.obj (op world)) (commutes : observation.app (op world) original = value) :
    restrict observation before value (encodePoint observation world value original commutes) =
      encodePoint observation future (target.map before.op value) (source.map before.op original)
        ((observation.naturality_apply before.op original).trans
          (congrArg (fun value => target.map before.op value) commutes)) := by
  apply (pointFibreEquiv observation future (target.map before.op value)).injective
  apply Subtype.ext
  change (decodePoint observation future (target.map before.op value)
      (restrict observation before value (encodePoint observation world value original commutes))).val =
    (decodePoint observation future (target.map before.op value)
      (encodePoint observation future (target.map before.op value) (source.map before.op original) _)).val
  rw [restrict_decode]
  rw [decode_encode, decode_encode]

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations.PresheafReadout
