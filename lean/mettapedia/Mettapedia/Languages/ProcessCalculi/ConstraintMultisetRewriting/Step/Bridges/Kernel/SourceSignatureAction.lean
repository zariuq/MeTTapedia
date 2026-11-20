import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceNameAction
import Mettapedia.Languages.HOLLight.DefinitionAdapters

/-!
# Signature extension under provenance-aware name bijections

The actual declaration lookup functions are conjugated by the source-syntax
action. Adding constants or type operators commutes with this construction,
and formation and freshness are reflected as well as preserved. This does
not by itself discharge type-definition existence or parameter-order checks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceSignatureAction

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open SignatureFormation SourceNameAction

@[simp] theorem symm_symm (names : Names) : names.symm.symm = names := by
  cases names
  rfl

theorem type_forward_inverse (names : Names) (value : Ty) :
    mapType names (mapType names.symm value) = value := by
  simpa only [symm_symm] using type_roundtrip names.symm value

theorem operator_forward_inverse (names : Names) (value : TypeOp) :
    mapOperator names (mapOperator names.symm value) = value := by
  simpa only [symm_symm] using operator_roundtrip names.symm value

theorem constant_forward_inverse (names : Names) (value : Const) :
    mapConstant names (mapConstant names.symm value) = value := by
  simpa only [symm_symm] using constant_roundtrip names.symm value

def mapSignature (names : Names) (signature : Signature) : Signature where
  typeOperators operator := signature.typeOperators (mapOperator names.symm operator)
  constants constant := (signature.constants (mapConstant names.symm constant)).map (mapType names)

@[simp] theorem operator_lookup (names : Names) (signature : Signature) (operator : TypeOp) :
    (mapSignature names signature).typeOperators (mapOperator names operator) =
      signature.typeOperators operator := by
  simp only [mapSignature, operator_roundtrip]

@[simp] theorem constant_lookup (names : Names) (signature : Signature) (constant : Const) :
    (mapSignature names signature).constants (mapConstant names constant) =
      (signature.constants constant).map (mapType names) := by
  simp only [mapSignature, constant_roundtrip]

private theorem constant_compare_inverse (names : Names) (candidate constant : Const) :
    Const.same (mapConstant names.symm candidate) constant =
      Const.same candidate (mapConstant names constant) := by
  simpa only [constant_forward_inverse] using
    (constant_comparison names (mapConstant names.symm candidate) constant).symm

private theorem operator_compare_inverse (names : Names) (candidate operator : TypeOp) :
    TypeOp.same (mapOperator names.symm candidate) operator =
      TypeOp.same candidate (mapOperator names operator) := by
  simpa only [operator_forward_inverse] using
    (operator_comparison names (mapOperator names.symm candidate) operator).symm

theorem add_constant (names : Names) (signature : Signature) (constant : Const) (schema : Ty) :
    mapSignature names (signature.addConstant constant schema) =
      (mapSignature names signature).addConstant (mapConstant names constant) (mapType names schema) := by
  apply congrArg₂ Signature.mk
  · rfl
  · funext candidate
    simp only [mapSignature, Signature.addConstant, sharedComparison_eq, constant_compare_inverse]
    by_cases matched : Const.same candidate (mapConstant names constant) = true <;> simp [matched]

theorem add_operator (names : Names) (signature : Signature) (operator : TypeOp) (arity : Nat) :
    mapSignature names (signature.addTypeOperator operator arity) =
      (mapSignature names signature).addTypeOperator (mapOperator names operator) arity := by
  apply congrArg₂ Signature.mk
  · funext candidate
    simp only [mapSignature, Signature.addTypeOperator, sharedComparison_eq, operator_compare_inverse]
  · rfl

theorem mapped_types (names : Names) (types : List Ty) : mapTypes names types = types.map (mapType names) := by
  induction types with
  | nil => simp only [mapTypes, List.map_nil]
  | cons first rest ih => simp only [mapTypes, List.map_cons, ih]

theorem formation (names : Names) (signature : Signature) (type : Ty) :
    TypeFormed (mapSignature names signature) (mapType names type) ↔ TypeFormed signature type := by
  cases type with
  | var name => simp only [mapType, TypeFormed]
  | op operator arguments =>
      simp only [mapType, TypeFormed, mapped_types, List.length_map, operator_lookup]
      constructor
      · rintro ⟨arity, children⟩
        exact ⟨arity, fun argument member => (formation names signature argument).mp
          (children _ (List.mem_map.mpr ⟨argument, member, rfl⟩))⟩
      · rintro ⟨arity, children⟩
        refine ⟨arity, ?_⟩
        intro argument member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact (formation names signature original).mpr (children original originalMember)
termination_by sizeOf type
decreasing_by
  all_goals
    simp_wf
    first
    | have smaller := List.sizeOf_lt_of_mem (show argument ∈ arguments from member)
      omega
    | have smaller := List.sizeOf_lt_of_mem (show original ∈ arguments from originalMember)
      omega

theorem formation_check (names : Names) (signature : Signature) (type : Ty) :
    typeFormedB (mapSignature names signature) (mapType names type) = typeFormedB signature type := by
  apply Bool.eq_iff_iff.mpr
  simp only [typeFormedB_eq_true_iff, formation]

theorem constant_fresh (names : Names) (signature : Signature) (constant : Const) :
    (mapSignature names signature).constants (mapConstant names constant) = none ↔
      signature.constants constant = none := by
  rw [constant_lookup]
  simp only [Option.map_eq_none_iff]

theorem operator_fresh (names : Names) (signature : Signature) (operator : TypeOp) :
    (mapSignature names signature).typeOperators (mapOperator names operator) = none ↔
      signature.typeOperators operator = none := by rw [operator_lookup]

def mapDeclaredName (names : Names) : DefinedSymbolName → DefinedSymbolName
  | .constant name => .constant (names.constants name)
  | .typeOperator name => .typeOperator (names.operators name)

theorem declared_name_roundtrip (names : Names) (name : DefinedSymbolName) :
    mapDeclaredName names.symm (mapDeclaredName names name) = name := by
  cases name <;> simp [mapDeclaredName]

theorem declared_name_injective (names : Names) : Function.Injective (mapDeclaredName names) :=
  Function.LeftInverse.injective (declared_name_roundtrip names)

def mapNameContext (names : Names) (context : NameContext) : NameContext :=
  context.image (mapDeclaredName names)

theorem declared_member (names : Names) (context : NameContext) (name : DefinedSymbolName) :
    mapDeclaredName names name ∈ mapNameContext names context ↔ name ∈ context := by
  simp only [mapNameContext, Finset.mem_image, (declared_name_injective names).eq_iff, exists_eq_right]

theorem extend_name (names : Names) (context : NameContext) (name : DefinedSymbolName) :
    mapNameContext names (insert name context) =
      insert (mapDeclaredName names name) (mapNameContext names context) := by
  simp only [mapNameContext, Finset.image_insert]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceSignatureAction
