import Mettapedia.Languages.Megalodon.HenkinTermSubstitution
import Mettapedia.Languages.Megalodon.MathdataTypeFormation

/-!
# Native type specialization of intrinsic HOL terms

Capture-avoiding native type substitution agrees with type substitution in the
intrinsic interpretation. The result concerns actual native term syntax, not
only inferred types. Constants keep their names and lookup provenance; their
types must be stable or supplied by a compatible target environment. Closed
monomorphic declarations give a canonical stable instance, even in a library
that also contains prefix-polymorphic declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTermInterpretation

open MathdataKernel
open Mettapedia.Logic.HOL

/-- Weakening free type variables, without changing declared base names. -/
def shiftSubstitution (cutoff amount : Nat) : Base → Ty Base
  | .inl index => .base (.inl (if index < cutoff then index else index + amount))
  | .inr index => .base (.inr index)

theorem reifyType_shiftSubstitution (cutoff amount : Nat) (type : Ty Base) :
    reifyType (Ty.substitute (shiftSubstitution cutoff amount) type) =
      Tp.shift cutoff amount (reifyType type) := by
  induction type with
  | prop => rfl
  | base index =>
      cases index with
      | inl index => by_cases h : index < cutoff <;>
          simp [Ty.substitute, shiftSubstitution, reifyType, Tp.shift, h]
      | inr index => rfl
  | arr domain codomain ihd ihc => simp [reifyType, Tp.shift, ihd, ihc]

/-- Remove one free type-variable position, shifting the replacement past
the positions below it. This is the native substitution's type-level action. -/
def instantiationSubstitution (depth : Nat) (replacement : Ty Base) : Base → Ty Base
  | .inl index =>
      if index < depth then .base (.inl index)
      else if index = depth then Ty.substitute (shiftSubstitution 0 depth) replacement
      else .base (.inl (index - 1))
  | .inr index => .base (.inr index)

theorem reifyType_instantiationSubstitution (depth : Nat) (replacement type : Ty Base) :
    reifyType (Ty.substitute (instantiationSubstitution depth replacement) type) =
      Tp.instantiateAt depth (reifyType replacement) (reifyType type) := by
  induction type with
  | prop => rfl
  | base index =>
      cases index with
      | inl index =>
          by_cases below : index < depth
          · simp [Ty.substitute, instantiationSubstitution, reifyType, Tp.instantiateAt, below]
          · by_cases same : index = depth
            · simp [Ty.substitute, instantiationSubstitution, reifyType, Tp.instantiateAt,
                same, reifyType_shiftSubstitution]
            · simp [Ty.substitute, instantiationSubstitution, reifyType, Tp.instantiateAt,
                below, same]
      | inr index => rfl
  | arr domain codomain ihd ihc => simp [reifyType, Tp.instantiateAt, ihd, ihc]

@[simp] theorem variableIndex_mapTypes {Γ : Ctx Base} {type : Ty Base}
    (substitution : Base → Ty Base) (v : Var Γ type) :
    variableIndex (v.mapTypes substitution) = variableIndex v := by
  induction v <;> simp [Var.mapTypes, variableIndex, *]

set_option backward.isDefEq.respectTransparency false in
/-- Specialization and native erasure commute. Compatible constants must keep
the native symbol; changing a symbol is a separate signature translation. -/
theorem erase_mapTypes_typeInstantiateAt
    {source target : Environment} {Γ : Ctx Base} {type : Ty Base}
    (depth : Nat) (replacement : Ty Base)
    (constants : ∀ {a}, Constant source a →
      Constant target (Ty.substitute (instantiationSubstitution depth replacement) a))
    (symbols : ∀ {a} (constant : Constant source a),
      (constants constant).erase = constant.erase)
    (term : Term (Constant source) Γ type) :
    erase (mapTypes (instantiationSubstitution depth replacement) constants term) =
      (erase term).map (Tm.typeInstantiateAt depth (reifyType replacement)) := by
  induction term with
  | var v => simp [mapTypes, erase, Tm.typeInstantiateAt]
  | const constant =>
      simp only [mapTypes, erase, symbols, Option.map_some]
      cases constant <;> rfl
  | app function argument ihf iha | imp function argument ihf iha =>
      simp only [mapTypes, erase]
      rw [ihf, iha]
      cases erase function <;> cases erase argument <;> rfl
  | lam body ih | all body ih =>
      simp only [mapTypes, erase, reifyType_instantiationSubstitution]
      rw [ih]
      cases erase body <;> rfl
  | top | bot | and | or | not | eq | ex => rfl

/-- A closed monomorphic declaration keeps its original lookup under type
specialization; no new declaration or native symbol is generated. -/
def Constant.specializeClosed {environment : Environment} {type : Ty Base}
    (depth : Nat) (replacement : Ty Base) (constant : Constant environment type)
    (closed : (reifyType type).plainWellFormed 0 = true) :
    Constant environment (Ty.substitute (instantiationSubstitution depth replacement) type) := by
  have stable : reifyType (Ty.substitute (instantiationSubstitution depth replacement) type) =
      reifyType type := by
    rw [reifyType_instantiationSubstitution,
      Tp.instantiateAt_eq_of_plain _ _ closed (Nat.zero_le depth)]
  cases constant with
  | named name declaration lookup typed =>
      exact .named name declaration lookup (typed.trans stable.symm)
  | primitive index lookup => exact .primitive index (stable.symm ▸ lookup)

@[simp] theorem Constant.erase_specializeClosed {environment : Environment} {type : Ty Base}
    (depth : Nat) (replacement : Ty Base) (constant : Constant environment type)
    (closed : (reifyType type).plainWellFormed 0 = true) :
    (constant.specializeClosed depth replacement closed).erase = constant.erase := by
  cases constant <;> rfl

/-- A reified intrinsic type has no prefix quantifier. -/
theorem reifyType_polyWellFormed (depth : Nat) (type : Ty Base) :
    (reifyType type).polyWellFormed depth = (reifyType type).plainWellFormed depth := by
  cases type with
  | prop | arr => rfl
  | base index => cases index <;> rfl

/-- Closed prefix-polymorphic library declarations suffice: any symbol that
has a monomorphic intrinsic interpretation is then a closed plain constant. -/
theorem Constant.closed_of_polyLookups {environment : Environment} {type : Ty Base}
    (named : ∀ name declaration, environment.lookupTerm? name = some declaration →
      declaration.type.polyWellFormed 0 = true)
    (primitive : ∀ (index : Nat) (type : Tp), environment.primitives[index]? = some type →
      type.polyWellFormed 0 = true)
    (constant : Constant environment type) : (reifyType type).plainWellFormed 0 = true := by
  rw [← reifyType_polyWellFormed]
  cases constant with
  | named name declaration lookup typed => simpa [typed] using named name declaration lookup
  | primitive index lookup => exact primitive index _ lookup

/-- The generic commutation law has a same-library instance. The hypothesis
concerns representable constants, not a ban on unrelated polymorphic symbols. -/
theorem erase_mapTypes_closed {environment : Environment} {Γ : Ctx Base} {type : Ty Base}
    (closed : ∀ {a}, Constant environment a → (reifyType a).plainWellFormed 0 = true)
    (depth : Nat) (replacement : Ty Base) (term : Term (Constant environment) Γ type) :
    erase (mapTypes (instantiationSubstitution depth replacement)
      (fun constant => constant.specializeClosed depth replacement (closed constant)) term) =
      (erase term).map (Tm.typeInstantiateAt depth (reifyType replacement)) :=
  erase_mapTypes_typeInstantiateAt depth replacement _
    (fun constant => Constant.erase_specializeClosed depth replacement constant (closed constant)) term

/-- Native binder annotations remain formed after capture-avoiding type
specialization. No typing conclusion is assumed. -/
theorem plainAnnotations_typeInstantiateAt {term : Tm} {replacement : Tp} {bound depth : Nat}
    (formed : plainAnnotations (bound + 1) term = true)
    (replacement_formed : replacement.plainWellFormed (bound - depth) = true)
    (depth_le : depth ≤ bound) :
    plainAnnotations bound (Tm.typeInstantiateAt depth replacement term) = true := by
  induction term with
  | db | named | prim => rfl
  | app f a ihf iha | imp f a ihf iha =>
      simp only [plainAnnotations, Bool.and_eq_true] at formed
      simp [Tm.typeInstantiateAt, plainAnnotations, ihf formed.1, iha formed.2]
  | lam a body ih | all a body ih =>
      simp only [plainAnnotations, Bool.and_eq_true] at formed
      simp only [Tm.typeInstantiateAt, plainAnnotations, Bool.and_eq_true]
      exact ⟨Tp.plainWellFormed_instantiateAt formed.1 replacement_formed depth_le, ih formed.2⟩
  | typeApp | typeLam | typeAll => simp [plainAnnotations] at formed

/-- Specialization preserves a raw native typing judgment. Intrinsic syntax
is reconstructed from that judgment and then re-erased; it is not a supplied
well-typed target or an independently assumed simulation. -/
theorem native_infer_typeInstantiateAt {environment : Environment}
    (closed : ∀ {a}, Constant environment a → (reifyType a).plainWellFormed 0 = true)
    {context : List Tp} {term : Tm} {type : Tp} {bound depth : Nat}
    (replacement : Ty Base)
    (plainContext : ∀ type ∈ context, type.plainWellFormed (bound + 1) = true)
    (plainLookups : PlainLookups environment (bound + 1) term)
    (formed : plainAnnotations (bound + 1) term = true)
    (replacement_formed : (reifyType replacement).plainWellFormed (bound - depth) = true)
    (depth_le : depth ≤ bound)
    (accepted : inferTerm environment (bound + 1) context term = some type) :
    inferTerm environment bound
        (context.map (Tp.instantiateAt depth (reifyType replacement)))
        (Tm.typeInstantiateAt depth (reifyType replacement) term) =
      some (Tp.instantiateAt depth (reifyType replacement) type) := by
  obtain ⟨Γ, value, interpreted, context_reified, type_reified, erased⟩ :=
    interpret_native plainContext plainLookups (supported_of_plainAnnotations formed) accepted
  let specialized := mapTypes (instantiationSubstitution depth replacement)
    (fun constant => constant.specializeClosed depth replacement (closed constant)) interpreted
  have specialized_erased : erase specialized =
      some (Tm.typeInstantiateAt depth (reifyType replacement) term) := by
    rw [erase_mapTypes_closed, erased]
    rfl
  have checked := infer_of_erase specialized specialized_erased
    (plainAnnotations_typeInstantiateAt formed replacement_formed depth_le)
  have result_type : reifyType (Ty.substitute (instantiationSubstitution depth replacement) value) =
      Tp.instantiateAt depth (reifyType replacement) type := by
    rw [reifyType_instantiationSubstitution, type_reified]
  have result_context : (Γ.map (Ty.substitute (instantiationSubstitution depth replacement))).map
      reifyType = context.map (Tp.instantiateAt depth (reifyType replacement)) := by
    rw [← context_reified]
    simp only [List.map_map, Function.comp_def, reifyType_instantiationSubstitution]
  simpa only [result_type, result_context] using checked

namespace TypeSpecializationControls

/-- A library with an ordinary primitive, a closed named constant, and an
unrelated prefix-polymorphic declaration. -/
def library : Environment where
  primitives := [.arr (.base 0) (.base 0)]
  terms := [⟨"point", .base 0, none⟩,
    ⟨"identity", .all (.arr (.var 0) (.var 0)), some (.typeLam (.lam (.var 0) (.db 0)))⟩]

theorem library_named_closed : ∀ name declaration,
    library.lookupTerm? name = some declaration → declaration.type.polyWellFormed 0 = true := by
  intro name declaration lookup
  simp only [library, Environment.lookupTerm?, lookupTermList?] at lookup
  split at lookup
  · cases lookup; decide
  · split at lookup
    · cases lookup; decide
    · cases lookup

theorem library_primitive_closed : ∀ (index : Nat) (type : Tp),
    library.primitives[index]? = some type → type.polyWellFormed 0 = true := by
  intro index type lookup
  cases index <;> simp [library] at lookup
  subst type
  decide

def withConstants : Term (Constant library) []
    (.base (.inl 0) ⇒ .base (.inr 0)) :=
  .lam (.app (σ := .base (.inr 0)) (.const (.primitive 0 rfl))
    (.const (.named "point" ⟨"point", .base 0, none⟩ rfl rfl)))

/-- A compound type instance retains both primitive and named symbols,
without deleting an unrelated polymorphic library entry. -/
theorem compound_specialization_with_constants :
    erase (mapTypes (instantiationSubstitution 0 (.arr .prop .prop))
      (fun constant => constant.specializeClosed 0 (.arr .prop .prop)
        (constant.closed_of_polyLookups library_named_closed library_primitive_closed))
      withConstants) =
      some (.lam (.arr .prop .prop) (.app (.prim 0) (.named "point"))) := by
  rw [erase_mapTypes_closed]
  rfl

/-- Nonzero substitution shifts a free type variable past retained positions. -/
theorem nonzero_specialization_avoids_capture :
    Tm.typeInstantiateAt 1 (.var 0) (.lam (.var 1) (.lam (.var 0) (.db 1))) =
      .lam (.var 1) (.lam (.var 0) (.db 1)) := by decide

theorem unshifted_specialization_disagrees :
    Tm.typeInstantiateAt 1 (.var 0) (.lam (.var 1) (.lam (.var 0) (.db 1))) ≠
      .lam (.var 0) (.lam (.var 0) (.db 1)) := by decide

/-- A raw environment with a free variable in a global type is not closed. -/
def openLibrary : Environment where
  terms := [⟨"open", .var 0, none⟩]

theorem open_global_not_specialized :
    inferTerm openLibrary 1 [] (.named "open") = some (.var 0) ∧
      inferTerm openLibrary 0 [] (Tm.typeInstantiate .prop (.named "open")) ≠ some .prop := by
  decide

/-- No name-preserving total map can pretend that this open global was
specialized in the unchanged library. -/
theorem no_open_constant_specialization :
    ¬ ∃ constants : ∀ {a}, Constant openLibrary a →
        Constant openLibrary (Ty.substitute (instantiationSubstitution 0 .prop) a),
      ∀ {a} (constant : Constant openLibrary a), (constants constant).erase = constant.erase := by
  rintro ⟨constants, symbols⟩
  let constant : Constant openLibrary (.base (.inl 0)) :=
    .named "open" ⟨"open", .var 0, none⟩ rfl rfl
  have same := symbols constant
  have typed := infer_of_erase (.const (constants constant) : Term _ [] _)
    (depth := 0) (term := .named "open")
    (by simpa [erase, constant, Constant.erase] using congrArg some same) rfl
  exact open_global_not_specialized.2 typed

end TypeSpecializationControls

#print axioms reifyType_instantiationSubstitution
#print axioms erase_mapTypes_typeInstantiateAt
#print axioms Constant.erase_specializeClosed
#print axioms Constant.closed_of_polyLookups
#print axioms erase_mapTypes_closed
#print axioms plainAnnotations_typeInstantiateAt
#print axioms native_infer_typeInstantiateAt
#print axioms TypeSpecializationControls.compound_specialization_with_constants
#print axioms TypeSpecializationControls.unshifted_specialization_disagrees
#print axioms TypeSpecializationControls.no_open_constant_specialization

end Mettapedia.Languages.Megalodon.HenkinTermInterpretation
