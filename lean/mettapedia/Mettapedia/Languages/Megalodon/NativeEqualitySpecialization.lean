import Mettapedia.Languages.Megalodon.HenkinTermTypeSubstitution
import Mettapedia.Languages.Megalodon.HenkinEqualityInterpretation

/-!
# A native polymorphic equality declaration and its checked instances

The prefix declaration uses the preamble's binary-relation definition. Native
type application specializes that definition, while the intrinsic interpretation
uses the existing HOL type substitution. The declaration's native typing,
definition unfolding, generic reflexivity proof and model meaning are separate
claims. The native definition and reflexivity proof need no object-theory set
or choice axiom and no dependent object types. Their Lean metatheoretic axiom
footprints are printed separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeEqualitySpecialization

open MathdataKernel HenkinTermInterpretation HenkinEqualityInterpretation
open Mettapedia.Logic.HOL

/-- The prefix-polymorphic declaration type, not an intrinsic HOL type. -/
def equalityType : Tp := .all (.arr (.var 0) (.arr (.var 0) .prop))

def equalityDefinition : Tm := .typeLam (nativeEquality (.var 0))

/-- A native library declaration with its actual definition payload. -/
def equalityDeclaration : TermDecl :=
  ⟨"eq", equalityType, some equalityDefinition⟩

def equalityEnvironment : Environment where
  terms := [equalityDeclaration]

theorem equality_type_formed : equalityType.polyWellFormed 0 = true := by decide

/-- The native definition checks without assuming its declared result type. -/
theorem nativeEquality_type (environment : Environment) (depth : Nat) (context : List Tp)
    (type : Tp) (formed : type.plainWellFormed depth = true) :
    inferTerm environment depth context (nativeEquality type) =
      some (.arr type (.arr type .prop)) := by
  simp [nativeEquality, inferTerm, formed, Tp.plainWellFormed]

theorem equality_definition_type :
    inferTerm equalityEnvironment 0 [] equalityDefinition = some equalityType := by
  simp only [equalityDefinition, inferTerm, List.map_nil]
  rw [nativeEquality_type _ _ _ _ (by decide)]
  rfl

theorem nativeEquality_typeInstantiateAt (depth : Nat) (replacement type : Tp) :
    Tm.typeInstantiateAt depth replacement (nativeEquality type) =
      nativeEquality (Tp.instantiateAt depth replacement type) := by
  simp [nativeEquality, Tm.typeInstantiateAt, Tp.instantiateAt]

theorem equality_body_specialization (type : Tp) :
    Tm.typeInstantiate type (nativeEquality (.var 0)) = nativeEquality type := by
  simp [Tm.typeInstantiate, nativeEquality_typeInstantiateAt,
    Tp.instantiateAt, Tp.shift_zero]

/-- Every well-formed plain type is a valid instance of the same declaration. -/
theorem equality_instance_type (depth : Nat) (context : List Tp)
    (type : Tp) (formed : type.plainWellFormed depth = true) :
    inferTerm equalityEnvironment depth context (.typeApp (.named "eq") type) =
      some (.arr type (.arr type .prop)) := by
  simp [inferTerm, formed, equalityEnvironment, Environment.lookupTerm?, lookupTermList?,
    equalityDeclaration, equalityType, Tp.instantiate, Tp.instantiateAt, Tp.shift_zero]

/-- Definition unfolding and native type beta reduction recover exactly the
monomorphic definition, rather than only an equal type or truth value. -/
theorem equality_instance_normalize (type : Tp) :
    normalize equalityEnvironment 4 (.typeApp (.named "eq") type) =
      some (nativeEquality type) := by
  simp [normalize, deltaNormalize, equalityEnvironment, Environment.lookupTerm?,
    lookupTermList?, equalityDeclaration, equalityDefinition, Tm.normalize,
    Tm.normalizeOne, nativeEquality, Tm.typeInstantiate, Tm.typeInstantiateAt,
    Tp.instantiateAt, Tp.shift_zero]

/-- The intrinsic interpretation of that exact normalized native instance. -/
theorem normalized_instance_interpretation (type : Ty Base) :
    normalize equalityEnvironment 4 (.typeApp (.named "eq") (reifyType type)) =
      erase (equality (Const := Constant equalityEnvironment) (Γ := []) type) := by
  rw [equality_instance_normalize, erase_equality]

theorem equality_constants_closed {type : Ty Base}
    (constant : Constant equalityEnvironment type) :
    (reifyType type).plainWellFormed 0 = true := by
  apply constant.closed_of_polyLookups
  · intro name declaration lookup
    simp only [equalityEnvironment, Environment.lookupTerm?, lookupTermList?] at lookup
    split at lookup
    · cases lookup
      exact equality_type_formed
    · cases lookup
  · intro index type lookup
    simp [equalityEnvironment] at lookup

/-- The actual closed library supplies the constant map; no translation
of a declaration's name or hidden assumption about its type is supplied. -/
def equalityConstants (type : Ty Base) {a : Ty Base} (constant : Constant equalityEnvironment a) :
    Constant equalityEnvironment (Ty.substitute (instantiationSubstitution 0 type) a) :=
  constant.specializeClosed 0 type (equality_constants_closed constant)

/-- The same native instance is obtained by specializing the intrinsic
schematic body with the generic term-specialization theorem. The concrete
library discharges all constant-map and symbol-preservation obligations. -/
theorem schematic_instance_erasure (type : Ty Base) :
    erase (mapTypes (instantiationSubstitution 0 type) (equalityConstants type)
      (equality (Γ := []) (.base (.inl 0)))) =
      normalize equalityEnvironment 4 (.typeApp (.named "eq") (reifyType type)) := by
  rw [erase_mapTypes_typeInstantiateAt 0 type (equalityConstants type)
    (fun constant => Constant.erase_specializeClosed 0 type constant
      (equality_constants_closed constant)), erase_equality]
  simp only [Option.map_some, reifyType, equality_instance_normalize]
  exact congrArg some (equality_body_specialization (reifyType type))

/-- The independently checked native instance and its intrinsic semantic
meaning meet at exact syntax. The model assumption is extensional congruence,
not full domains or an assumption that the native kernel is globally sound. -/
theorem equality_instance_correct
    (M : HenkinModel Base (Constant equalityEnvironment)) (respects : M.FunctionsRespectEqv)
    (depth : Nat) (type : Ty Base) (formed : (reifyType type).plainWellFormed depth = true)
    (left right : Ty.denote M.Carrier type)
    (left_admitted : M.adm type left) (right_admitted : M.adm type right) :
    inferTerm equalityEnvironment depth [] (.typeApp (.named "eq") (reifyType type)) =
        some (.arr (reifyType type) (.arr (reifyType type) .prop)) ∧
      normalize equalityEnvironment 4 (.typeApp (.named "eq") (reifyType type)) =
        erase (equality (Const := Constant equalityEnvironment) (Γ := []) type) ∧
      ((M.denote (equality (Γ := []) type) (fun v => nomatch v) left right).down ↔
        M.Eqv type left right) :=
  ⟨equality_instance_type depth [] (reifyType type) formed, normalized_instance_interpretation type,
    relationEquality_iff_eqv M respects left_admitted right_admitted⟩

/-- Reflexivity in expanded equality syntax, with no assumed equality rule. -/
def reflexivityBody (type : Tp) : Tm :=
  .all type (.all (.arr type (.arr type .prop))
    (.imp (.app (.app (.db 0) (.db 1)) (.db 1))
      (.app (.app (.db 0) (.db 1)) (.db 1))))

def reflexivityProof : Pf :=
  .typeLam (.termLam (.var 0) (.termLam (.arr (.var 0) (.arr (.var 0) .prop))
    (.proofLam (.app (.app (.db 0) (.db 1)) (.db 1)) (.hyp 0))))

theorem generic_reflexivity_accepted_at_fuel (fuel : Nat) :
    inferProof equalityEnvironment fuel 0 [] [] reflexivityProof =
      some (.typeAll (reflexivityBody (.var 0))) := by
  cases fuel <;>
    simp [reflexivityProof, reflexivityBody, inferProof, inferTerm, Tp.plainWellFormed,
      normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne]

theorem generic_reflexivity_accepted :
    inferProof equalityEnvironment 0 0 [] [] reflexivityProof =
      some (.typeAll (reflexivityBody (.var 0))) :=
  generic_reflexivity_accepted_at_fuel 0

theorem reflexivityBody_typeInstantiate (type : Tp) :
    Tm.typeInstantiate type (reflexivityBody (.var 0)) = reflexivityBody type := by
  simp [reflexivityBody, Tm.typeInstantiate, Tm.typeInstantiateAt,
    Tp.instantiateAt, Tp.shift_zero]

/-- One actual native proof can be instantiated, rather than independently
postulating a reflexivity theorem at each type. -/
theorem specialized_reflexivity_accepted (type : Tp) :
    inferProof equalityEnvironment 0 0 [] [] (.typeApp reflexivityProof type) =
      some (reflexivityBody type) := by
  simp [inferProof, generic_reflexivity_accepted, reflexivityBody_typeInstantiate]

/-- Formation remains independent: the raw proof type-application constructor
does not itself check its replacement. Valid native instances require this law. -/
theorem reflexivity_instance_formed (depth : Nat) (type : Tp)
    (formed : type.plainWellFormed depth = true) :
    checkProposition equalityEnvironment depth [] (reflexivityBody type) = true := by
  simp [checkProposition, reflexivityBody, inferTerm, formed, Tp.plainWellFormed]

/-- The ordinary source-level theorem states reflexivity using the library
name, not a separately postulated equality predicate. -/
def reflexivityStatement (type : Tp) : Tm :=
  .all type (.app (.app (.typeApp (.named "eq") type) (.db 0)) (.db 0))

theorem reflexivity_statement_normalize (type : Tp) :
    normalize equalityEnvironment 8 (reflexivityStatement type) =
      some (reflexivityBody type) := by
  simp [reflexivityStatement, normalize, deltaNormalize, equalityEnvironment,
    Environment.lookupTerm?, lookupTermList?, equalityDeclaration, equalityDefinition,
    nativeEquality, Tm.normalize, Tm.normalizeOne, Tm.typeInstantiate, Tm.typeInstantiateAt,
    Tm.instantiate, Tm.instantiateAt, Tm.shift, Tp.instantiateAt,
    Tp.shift_zero, reflexivityBody]

/-- Real source-level checking and independent formation both hold for each
closed plain instance of the single generic equality proof. -/
theorem reflexivity_statement_checked (type : Tp)
    (formed : type.plainWellFormed 0 = true) :
    checkProposition equalityEnvironment 0 [] (reflexivityStatement type) = true ∧
      checkProof equalityEnvironment 8 0 [] [] (.typeApp reflexivityProof type)
        (reflexivityStatement type) = true := by
  constructor
  · simp [reflexivityStatement, checkProposition, inferTerm, formed,
      equalityEnvironment, Environment.lookupTerm?, lookupTermList?, equalityDeclaration,
      equalityType, Tp.instantiate, Tp.instantiateAt, Tp.shift_zero]
  · simp [checkProof, reflexivity_statement_normalize, checkNormalizedProof,
      inferProof, generic_reflexivity_accepted_at_fuel, reflexivityBody_typeInstantiate]

/-- Native term specialization rejects a prefix type in a plain type slot. -/
theorem prefix_type_argument_rejected :
    inferTerm equalityEnvironment 0 [] (.typeApp (.named "eq") (.all .prop)) = none := by
  decide

/-- Changing only the apparent result type cannot specialize a library name. -/
theorem unspecialized_name_not_monomorphic :
    inferTerm equalityEnvironment 0 [] (.named "eq") ≠
      some (.arr .prop (.arr .prop .prop)) := by decide

/-- A correct generic proof instantiated at the wrong type does not prove
the requested instance. -/
theorem wrong_reflexivity_instance_rejected :
    checkProof equalityEnvironment 8 0 [] [] (.typeApp reflexivityProof (.base 0))
      (reflexivityStatement .prop) = false := by
  simp [checkProof, reflexivity_statement_normalize, checkNormalizedProof,
    inferProof, generic_reflexivity_accepted_at_fuel, reflexivityBody_typeInstantiate]
  decide

#print axioms equality_definition_type
#print axioms equality_instance_type
#print axioms equality_instance_normalize
#print axioms normalized_instance_interpretation
#print axioms schematic_instance_erasure
#print axioms equality_instance_correct
#print axioms generic_reflexivity_accepted
#print axioms specialized_reflexivity_accepted
#print axioms reflexivity_instance_formed
#print axioms reflexivity_statement_checked
#print axioms prefix_type_argument_rejected
#print axioms wrong_reflexivity_instance_rejected

end Mettapedia.Languages.Megalodon.NativeEqualitySpecialization
