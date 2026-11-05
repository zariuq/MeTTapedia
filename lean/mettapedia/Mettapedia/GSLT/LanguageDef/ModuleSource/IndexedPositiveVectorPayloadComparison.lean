import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorPayloadLowering

/-!
# Comparison with the existing Boolean Vector interpretation

This comparison is restricted to the Boolean specialization. It transports
the explicitly lifted natural fields and Unit indices, and preserves actual
constructor shapes and recursive-position fibres. No comparison between
Boolean payloads and an arbitrary payload carrier is postulated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering

open Mettapedia.TypeTheory
open IndexedPolynomial.Description
open IndexedPositiveContainer

namespace BoolComparison

def toShape : {context : List DataSort} → {names : List String} →
    (code : Code context names) → (environment : Env (VectorPayload.value Bool) context) →
    (index : (VectorPayload.interface Bool).Index) →
    IndexedPositiveContainer.Code.Shape (code.eraseWithPayload Bool) environment index →
    IndexedPositiveContainer.Code.Shape code.erase
      (VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)
  | _, _, .result, _, _, shape => ⟨⟨congrArg ULift.down shape.down.down⟩⟩
  | context, _, .data name .payload fresh rest, environment, index, shape => by
      change (Σ item : Bool, IndexedPositiveContainer.Code.Shape
        (rest.eraseWithPayload Bool) (item, environment) index) at shape
      change Σ item : Bool, IndexedPositiveContainer.Code.Shape rest.erase
        (item, VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)
      exact ⟨shape.1, toShape rest (shape.1, environment) index shape.2⟩
  | context, _, .data name .length fresh rest, environment, index, shape => by
      change (Σ length : ULift Nat, IndexedPositiveContainer.Code.Shape
        (rest.eraseWithPayload Bool) (length, environment) index) at shape
      change Σ length : Nat, IndexedPositiveContainer.Code.Shape rest.erase
        (length, VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)
      exact ⟨shape.1.down, toShape rest (shape.1, environment) index shape.2⟩
  | _, _, .recursive name rest, environment, index, shape => toShape rest environment index shape
  | context, _, .vector name length rest, environment, index, shape => by
      change (Σ _ : Unit, IndexedPositiveContainer.Code.Shape (rest.eraseWithPayload Bool) environment index) at shape
      change Σ _ : Unit, IndexedPositiveContainer.Code.Shape rest.erase
        (VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)
      exact ⟨shape.1, toShape rest environment index shape.2⟩

def fromShape : {context : List DataSort} → {names : List String} →
    (code : Code context names) → (environment : Env (VectorPayload.value Bool) context) →
    (index : (VectorPayload.interface Bool).Index) →
    IndexedPositiveContainer.Code.Shape code.erase
      (VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index) →
    IndexedPositiveContainer.Code.Shape (code.eraseWithPayload Bool) environment index
  | _, _, .result, _, _, shape => ⟨⟨congrArg ULift.up shape.down.down⟩⟩
  | context, _, .data name .payload fresh rest, environment, index, shape => by
      change (Σ item : Bool, IndexedPositiveContainer.Code.Shape rest.erase
        (item, VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)) at shape
      change Σ item : Bool, IndexedPositiveContainer.Code.Shape (rest.eraseWithPayload Bool)
        (item, environment) index
      exact ⟨shape.1, fromShape rest (shape.1, environment) index shape.2⟩
  | context, _, .data name .length fresh rest, environment, index, shape => by
      change (Σ length : Nat, IndexedPositiveContainer.Code.Shape rest.erase
        (length, VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)) at shape
      change Σ length : ULift Nat, IndexedPositiveContainer.Code.Shape (rest.eraseWithPayload Bool)
        (length, environment) index
      exact ⟨⟨shape.1⟩, fromShape rest (⟨shape.1⟩, environment) index shape.2⟩
  | _, _, .recursive name rest, environment, index, shape => fromShape rest environment index shape
  | context, _, .vector name length rest, environment, index, shape => by
      change (Σ _ : Unit, IndexedPositiveContainer.Code.Shape rest.erase
        (VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)) at shape
      change Σ _ : Unit, IndexedPositiveContainer.Code.Shape (rest.eraseWithPayload Bool) environment index
      exact ⟨shape.1, fromShape rest environment index shape.2⟩

theorem from_to : {context : List DataSort} → {names : List String} →
    (code : Code context names) → (environment : Env (VectorPayload.value Bool) context) →
    (index : (VectorPayload.interface Bool).Index) →
    (shape : IndexedPositiveContainer.Code.Shape (code.eraseWithPayload Bool) environment index) →
    fromShape code environment index (toShape code environment index shape) = shape
  | _, _, .result, environment, index, shape => by
      change @Eq (ULift (PLift ((ULift.up () : ULift Unit) = index))) _ _
      exact Subsingleton.elim _ _
  | _, _, .data name .payload fresh rest, environment, index, shape => by
      change (Σ item : Bool, IndexedPositiveContainer.Code.Shape
        (rest.eraseWithPayload Bool) (item, environment) index) at shape
      rcases shape with ⟨item, shape⟩
      exact congrArg (Sigma.mk item) (from_to rest (item, environment) index shape)
  | _, _, .data name .length fresh rest, environment, index, shape => by
      change (Σ length : ULift Nat, IndexedPositiveContainer.Code.Shape
        (rest.eraseWithPayload Bool) (length, environment) index) at shape
      rcases shape with ⟨⟨length⟩, shape⟩
      exact congrArg (Sigma.mk (ULift.up length)) (from_to rest (⟨length⟩, environment) index shape)
  | _, _, .recursive name rest, environment, index, shape => from_to rest environment index shape
  | _, _, .vector name length rest, environment, index, shape => by
      change (Σ _ : Unit, IndexedPositiveContainer.Code.Shape (rest.eraseWithPayload Bool) environment index) at shape
      rcases shape with ⟨vectorShape, shape⟩
      exact congrArg (Sigma.mk vectorShape) (from_to rest environment index shape)

theorem to_from : {context : List DataSort} → {names : List String} →
    (code : Code context names) → (environment : Env (VectorPayload.value Bool) context) →
    (index : (VectorPayload.interface Bool).Index) →
    (shape : IndexedPositiveContainer.Code.Shape code.erase
      (VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)) →
    toShape code environment index (fromShape code environment index shape) = shape
  | _, _, .result, environment, index, shape => by
      change @Eq (ULift (PLift (() = index.down))) _ _
      exact Subsingleton.elim _ _
  | context, _, .data name .payload fresh rest, environment, index, shape => by
      change (Σ item : Bool, IndexedPositiveContainer.Code.Shape rest.erase
        (item, VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)) at shape
      rcases shape with ⟨item, shape⟩
      exact congrArg (Sigma.mk item) (to_from rest (item, environment) index shape)
  | context, _, .data name .length fresh rest, environment, index, shape => by
      change (Σ length : Nat, IndexedPositiveContainer.Code.Shape rest.erase
        (length, VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)) at shape
      rcases shape with ⟨length, shape⟩
      exact congrArg (Sigma.mk length) (to_from rest (⟨length⟩, environment) index shape)
  | _, _, .recursive name rest, environment, index, shape => to_from rest environment index shape
  | context, _, .vector name length rest, environment, index, shape => by
      change (Σ _ : Unit, IndexedPositiveContainer.Code.Shape rest.erase
        (VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)) at shape
      rcases shape with ⟨vectorShape, shape⟩
      exact congrArg (Sigma.mk vectorShape) (to_from rest environment index shape)

def shapeEquiv {context : List DataSort} {names : List String} (code : Code context names)
    (environment : Env (VectorPayload.value Bool) context)
    (index : (VectorPayload.interface Bool).Index) :
    IndexedPositiveContainer.Code.Shape (code.eraseWithPayload Bool) environment index ≃
      IndexedPositiveContainer.Code.Shape code.erase
        (VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index) where
  toFun := toShape code environment index
  invFun := fromShape code environment index
  left_inv := from_to code environment index
  right_inv := to_from code environment index

def positionEquiv : {context : List DataSort} → {names : List String} →
    (code : Code context names) → {environment : Env (VectorPayload.value Bool) context} →
    {index : (VectorPayload.interface Bool).Index} →
    (shape : IndexedPositiveContainer.Code.Shape (code.eraseWithPayload Bool) environment index) →
    IndexedPositiveContainer.Code.Position (code.eraseWithPayload Bool) shape ≃
      IndexedPositiveContainer.Code.Position code.erase (toShape code environment index shape)
  | _, _, .result, _, _, _ => Equiv.refl _
  | _, _, .data name .payload fresh rest, environment, index, shape => by
      change (Σ item : Bool, IndexedPositiveContainer.Code.Shape
        (rest.eraseWithPayload Bool) (item, environment) index) at shape
      exact positionEquiv rest shape.2
  | _, _, .data name .length fresh rest, environment, index, shape => by
      change (Σ length : ULift Nat, IndexedPositiveContainer.Code.Shape
        (rest.eraseWithPayload Bool) (length, environment) index) at shape
      exact positionEquiv rest shape.2
  | _, _, .recursive name rest, _, _, shape => Equiv.optionCongr (positionEquiv rest shape)
  | _, _, .vector name length rest, environment, index, shape => by
      change (Σ _ : Unit, IndexedPositiveContainer.Code.Shape (rest.eraseWithPayload Bool) environment index) at shape
      exact Equiv.sumCongr
        (Equiv.cast (congrArg Fin (VectorPayload.evalLength_bool length environment).symm))
        (positionEquiv rest shape.2)

theorem next_preserved {context : List DataSort} {names : List String}
    (code : Code context names) {environment : Env (VectorPayload.value Bool) context}
    {index : (VectorPayload.interface Bool).Index}
    (shape : IndexedPositiveContainer.Code.Shape (code.eraseWithPayload Bool) environment index)
    (position : IndexedPositiveContainer.Code.Position (code.eraseWithPayload Bool) shape) :
    IndexedPositiveContainer.Code.next (I := VectorControl.interface) code.erase (toShape code environment index shape)
        (positionEquiv code shape position) =
      VectorPayload.boolIndexEquiv
        (IndexedPositiveContainer.Code.next (code.eraseWithPayload Bool) shape position) :=
  by
    change (_ : Unit) = _
    exact Subsingleton.elim _ _

/-- Pull back the old interpretation along the explicit Boolean environment
and index equivalences. This construction is used only for comparison. -/
def legacyPolynomial {context : List DataSort} {names : List String}
    (code : Code context names) :
    IndexedPolynomial (Env (VectorPayload.value Bool) context)
      (fun _ => (VectorPayload.interface Bool).Index) where
  Shape := fun environment index => IndexedPositiveContainer.Code.Shape code.erase
    (VectorPayload.boolEnvEquiv context environment) (VectorPayload.boolIndexEquiv index)
  Position := fun shape => IndexedPositiveContainer.Code.Position code.erase shape
  next := fun shape position => ⟨IndexedPositiveContainer.Code.next code.erase shape position⟩

def signatureEquiv {context : List DataSort} {names : List String}
    (code : Code context names) :
    IndexedPolynomial.SignatureEquiv
      (IndexedPositiveContainer.Code.polynomial (code.eraseWithPayload Bool))
      (legacyPolynomial code) where
  shape := shapeEquiv code
  position := positionEquiv code
  next_preserved := by
    intro environment index shape position
    exact congrArg (fun item : Unit => (ULift.up item : ULift Unit))
      (next_preserved code shape position)

#print axioms shapeEquiv
#print axioms positionEquiv
#print axioms next_preserved
#print axioms signatureEquiv

end BoolComparison
end Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering
