import Mettapedia.Languages.Megalodon.EnvironmentEmbedding

/-!
# Heterogeneous Megalodon signature embeddings

`EnvironmentEmbedding` proves exact selected-theory transport when primitive
and base-type indices are fixed.  This module generalizes the same boundary to
three jointly injective maps: global names, primitive indices, and base-type
indices.  Exact target lookup agreement includes absence, so the target may
contain unrelated declarations and primitives outside the three images.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SignatureEmbedding

open Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView
open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.Languages.Megalodon.NIKNativeProof
open Mettapedia.Languages.Megalodon.SelectedTheoryProfile

/-- The structural part of a selected-theory signature map.  Type variables
and term binders are intrinsic and therefore remain unchanged. -/
structure SignatureMap where
  name : Name -> Name
  primitive : Nat -> Nat
  base : Nat -> Nat
  name_injective : Function.Injective name
  primitive_injective : Function.Injective primitive
  base_injective : Function.Injective base

namespace SignatureMap

def identity : SignatureMap where
  name := id
  primitive := id
  base := id
  name_injective := Function.injective_id
  primitive_injective := Function.injective_id
  base_injective := Function.injective_id

def comp (earlier later : SignatureMap) : SignatureMap where
  name := later.name ∘ earlier.name
  primitive := later.primitive ∘ earlier.primitive
  base := later.base ∘ earlier.base
  name_injective := later.name_injective.comp earlier.name_injective
  primitive_injective :=
    later.primitive_injective.comp earlier.primitive_injective
  base_injective := later.base_injective.comp earlier.base_injective

/-- Embed the earlier name-only environment transport into the heterogeneous
signature language. -/
def ofName (rename : Name -> Name) (injective : Function.Injective rename) :
    SignatureMap where
  name := rename
  primitive := id
  base := id
  name_injective := injective
  primitive_injective := Function.injective_id
  base_injective := Function.injective_id

@[simp] theorem ofName_name (rename : Name -> Name)
    (injective : Function.Injective rename) (name : Name) :
    (ofName rename injective).name name = rename name :=
  rfl

@[simp] theorem ofName_primitive (rename : Name -> Name)
    (injective : Function.Injective rename) (index : Nat) :
    (ofName rename injective).primitive index = index :=
  rfl

@[simp] theorem ofName_base (rename : Name -> Name)
    (injective : Function.Injective rename) (index : Nat) :
    (ofName rename injective).base index = index :=
  rfl

@[simp] theorem identity_name (name : Name) : identity.name name = name := rfl

@[simp] theorem identity_primitive (index : Nat) :
    identity.primitive index = index := rfl

@[simp] theorem identity_base (index : Nat) : identity.base index = index := rfl

end SignatureMap

/-! ## Action on native Mathdata syntax -/

def mapTp (map : SignatureMap) : Tp -> Tp
  | .var index => .var index
  | .prop => .prop
  | .base index => .base (map.base index)
  | .arr domain codomain => .arr (mapTp map domain) (mapTp map codomain)
  | .all body => .all (mapTp map body)

def mapTm (map : SignatureMap) : Tm -> Tm
  | .db index => .db index
  | .named name => .named (map.name name)
  | .prim index => .prim (map.primitive index)
  | .app function argument => .app (mapTm map function) (mapTm map argument)
  | .lam type body => .lam (mapTp map type) (mapTm map body)
  | .imp domain codomain => .imp (mapTm map domain) (mapTm map codomain)
  | .all type body => .all (mapTp map type) (mapTm map body)
  | .typeApp function type => .typeApp (mapTm map function) (mapTp map type)
  | .typeLam body => .typeLam (mapTm map body)
  | .typeAll body => .typeAll (mapTm map body)

def mapPf (map : SignatureMap) : Pf -> Pf
  | .gpa name => .gpa (map.name name)
  | .hyp index => .hyp index
  | .known name => .known (map.name name)
  | .termApp function argument =>
      .termApp (mapPf map function) (mapTm map argument)
  | .proofApp function argument =>
      .proofApp (mapPf map function) (mapPf map argument)
  | .proofLam proposition body =>
      .proofLam (mapTm map proposition) (mapPf map body)
  | .termLam type body => .termLam (mapTp map type) (mapPf map body)
  | .typeApp function type => .typeApp (mapPf map function) (mapTp map type)
  | .typeLam body => .typeLam (mapPf map body)

def mapTermDecl (map : SignatureMap) (declaration : TermDecl) : TermDecl :=
  { name := map.name declaration.name
    type := mapTp map declaration.type
    definition := declaration.definition.map (mapTm map) }

def mapKnownDecl (map : SignatureMap) (declaration : KnownDecl) : KnownDecl :=
  { name := map.name declaration.name
    proposition := mapTm map declaration.proposition }

theorem lookupTermList?_map (map : SignatureMap)
    (declarations : List TermDecl) (name : Name) :
    lookupTermList? (declarations.map (mapTermDecl map)) (map.name name) =
      (lookupTermList? declarations name).map (mapTermDecl map) := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations declarationsIH =>
      by_cases sameName : declaration.name = name
      · subst name
        simp [lookupTermList?, mapTermDecl]
      · have mappedDifferent : map.name declaration.name ≠ map.name name := by
          intro equalMapping
          exact sameName (map.name_injective equalMapping)
        simp [lookupTermList?, mapTermDecl, sameName, mappedDifferent,
          declarationsIH]

theorem lookupKnownList?_map (map : SignatureMap)
    (declarations : List KnownDecl) (name : Name) :
    lookupKnownList? (declarations.map (mapKnownDecl map)) (map.name name) =
      (lookupKnownList? declarations name).map (mapTm map) := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations declarationsIH =>
      by_cases sameName : declaration.name = name
      · subst name
        simp [lookupKnownList?, mapKnownDecl]
      · have mappedDifferent : map.name declaration.name ≠ map.name name := by
          intro equalMapping
          exact sameName (map.name_injective equalMapping)
        simp [lookupKnownList?, mapKnownDecl, sameName, mappedDifferent,
          declarationsIH]

@[simp] theorem mapTp_ofName (rename : Name -> Name)
    (injective : Function.Injective rename) (type : Tp) :
    mapTp (SignatureMap.ofName rename injective) type = type := by
  induction type <;> simp [mapTp, *]

@[simp] theorem mapTm_ofName (rename : Name -> Name)
    (injective : Function.Injective rename) (term : Tm) :
    mapTm (SignatureMap.ofName rename injective) term =
      Mettapedia.Languages.Megalodon.EnvironmentEmbedding.renameTm
        rename term := by
  induction term <;>
    simp [mapTm,
      Mettapedia.Languages.Megalodon.EnvironmentEmbedding.renameTm, *]

@[simp] theorem mapPf_ofName (rename : Name -> Name)
    (injective : Function.Injective rename) (proof : Pf) :
    mapPf (SignatureMap.ofName rename injective) proof =
      Mettapedia.Languages.Megalodon.EnvironmentEmbedding.renamePf
        rename proof := by
  induction proof <;>
    simp [mapPf,
      Mettapedia.Languages.Megalodon.EnvironmentEmbedding.renamePf, *]

@[simp] theorem mapTermDecl_ofName (rename : Name -> Name)
    (injective : Function.Injective rename) (declaration : TermDecl) :
    mapTermDecl (SignatureMap.ofName rename injective) declaration =
      Mettapedia.Languages.Megalodon.EnvironmentEmbedding.renameTermDecl
        rename declaration := by
  cases declaration with
  | mk name type definition =>
      cases definition <;>
        simp [mapTermDecl,
          Mettapedia.Languages.Megalodon.EnvironmentEmbedding.renameTermDecl]

@[simp] theorem mapTp_identity (type : Tp) :
    mapTp SignatureMap.identity type = type := by
  induction type <;> simp [mapTp, *]

@[simp] theorem mapTm_identity (term : Tm) :
    mapTm SignatureMap.identity term = term := by
  induction term <;>
    simp [mapTm, *]

@[simp] theorem mapPf_identity (proof : Pf) :
    mapPf SignatureMap.identity proof = proof := by
  induction proof <;>
    simp [mapPf, *]

theorem mapTp_comp (earlier later : SignatureMap) (type : Tp) :
    mapTp later (mapTp earlier type) =
      mapTp (earlier.comp later) type := by
  induction type <;>
    simp [mapTp, SignatureMap.comp, Function.comp_apply, *]

theorem mapTm_comp (earlier later : SignatureMap) (term : Tm) :
    mapTm later (mapTm earlier term) =
      mapTm (earlier.comp later) term := by
  induction term <;>
    simp [mapTm, mapTp_comp, SignatureMap.comp, Function.comp_apply, *]

theorem mapPf_comp (earlier later : SignatureMap) (proof : Pf) :
    mapPf later (mapPf earlier proof) =
      mapPf (earlier.comp later) proof := by
  induction proof <;>
    simp [mapPf, mapTm_comp, mapTp_comp, SignatureMap.comp,
      Function.comp_apply, *]

@[simp] theorem mapTermDecl_identity (declaration : TermDecl) :
    mapTermDecl SignatureMap.identity declaration = declaration := by
  cases declaration with
  | mk name type definition =>
      cases definition <;> simp [mapTermDecl]

@[simp] theorem mapKnownDecl_identity (declaration : KnownDecl) :
    mapKnownDecl SignatureMap.identity declaration = declaration := by
  cases declaration
  simp [mapKnownDecl]

theorem mapTermDecl_comp (earlier later : SignatureMap)
    (declaration : TermDecl) :
    mapTermDecl later (mapTermDecl earlier declaration) =
      mapTermDecl (earlier.comp later) declaration := by
  cases declaration with
  | mk name type definition =>
      cases definition <;>
        simp [mapTermDecl, mapTp_comp, mapTm_comp,
          SignatureMap.comp, Function.comp_apply]

theorem mapKnownDecl_comp (earlier later : SignatureMap)
    (declaration : KnownDecl) :
    mapKnownDecl later (mapKnownDecl earlier declaration) =
      mapKnownDecl (earlier.comp later) declaration := by
  cases declaration
  simp [mapKnownDecl, mapTm_comp, SignatureMap.comp, Function.comp_apply]

/-- Type transport reflects equality because base-type transport is
injective. -/
theorem mapTp_injective (map : SignatureMap) :
    Function.Injective (mapTp map) := by
  intro left
  induction left with
  | var index =>
      intro right
      cases right <;> simp [mapTp]
  | prop =>
      intro right
      cases right <;> simp [mapTp]
  | base index =>
      intro right
      cases right <;> simp [mapTp, map.base_injective.eq_iff]
  | arr domain codomain domainIH codomainIH =>
      intro right equalMapping
      cases right <;> simp [mapTp] at equalMapping
      case arr otherDomain otherCodomain =>
        exact congrArg₂ Tp.arr
          (domainIH equalMapping.1) (codomainIH equalMapping.2)
  | all body bodyIH =>
      intro right equalMapping
      cases right <;> simp [mapTp] at equalMapping
      case all otherBody =>
        exact congrArg Tp.all (bodyIH equalMapping)

/-- Joint injectivity of names, primitives, and base types lifts to terms. -/
theorem mapTm_injective (map : SignatureMap) :
    Function.Injective (mapTm map) := by
  intro left
  induction left with
  | db index =>
      intro right
      cases right <;> simp [mapTm]
  | named name =>
      intro right
      cases right <;> simp [mapTm, map.name_injective.eq_iff]
  | prim index =>
      intro right
      cases right <;> simp [mapTm, map.primitive_injective.eq_iff]
  | app function argument functionIH argumentIH =>
      intro right equalMapping
      cases right <;> simp [mapTm] at equalMapping
      case app otherFunction otherArgument =>
        exact congrArg₂ Tm.app
          (functionIH equalMapping.1) (argumentIH equalMapping.2)
  | lam type body bodyIH =>
      intro right equalMapping
      cases right <;> simp [mapTm] at equalMapping
      case lam otherType otherBody =>
        exact congrArg₂ Tm.lam
          (mapTp_injective map equalMapping.1) (bodyIH equalMapping.2)
  | imp domain codomain domainIH codomainIH =>
      intro right equalMapping
      cases right <;> simp [mapTm] at equalMapping
      case imp otherDomain otherCodomain =>
        exact congrArg₂ Tm.imp
          (domainIH equalMapping.1) (codomainIH equalMapping.2)
  | all type body bodyIH =>
      intro right equalMapping
      cases right <;> simp [mapTm] at equalMapping
      case all otherType otherBody =>
        exact congrArg₂ Tm.all
          (mapTp_injective map equalMapping.1) (bodyIH equalMapping.2)
  | typeApp function type functionIH =>
      intro right equalMapping
      cases right <;> simp [mapTm] at equalMapping
      case typeApp otherFunction otherType =>
        exact congrArg₂ Tm.typeApp
          (functionIH equalMapping.1)
          (mapTp_injective map equalMapping.2)
  | typeLam body bodyIH =>
      intro right equalMapping
      cases right <;> simp [mapTm] at equalMapping
      case typeLam otherBody =>
        exact congrArg Tm.typeLam (bodyIH equalMapping)
  | typeAll body bodyIH =>
      intro right equalMapping
      cases right <;> simp [mapTm] at equalMapping
      case typeAll otherBody =>
        exact congrArg Tm.typeAll (bodyIH equalMapping)

/-! ## Type-variable and term-variable operations -/

theorem mapTp_shift (map : SignatureMap) (cutoff amount : Nat) (type : Tp) :
    mapTp map (Tp.shift cutoff amount type) =
      Tp.shift cutoff amount (mapTp map type) := by
  induction type generalizing cutoff <;> simp [mapTp, Tp.shift, *]
  all_goals split <;> rfl

theorem mapTp_instantiateAt (map : SignatureMap) (depth : Nat)
    (replacement body : Tp) :
    mapTp map (Tp.instantiateAt depth replacement body) =
      Tp.instantiateAt depth (mapTp map replacement) (mapTp map body) := by
  induction body generalizing depth with
  | var index =>
      by_cases below : index < depth
      · simp [Tp.instantiateAt, mapTp, below]
      · by_cases equal : index = depth
        · simp [Tp.instantiateAt, mapTp, equal, mapTp_shift]
        · simp [Tp.instantiateAt, mapTp, below, equal]
  | prop => simp [Tp.instantiateAt, mapTp]
  | base => simp [Tp.instantiateAt, mapTp]
  | arr domain codomain domainIH codomainIH =>
      simp [Tp.instantiateAt, mapTp, domainIH, codomainIH]
  | all body bodyIH =>
      simp [Tp.instantiateAt, mapTp, bodyIH]

@[simp] theorem mapTp_instantiate (map : SignatureMap)
    (replacement body : Tp) :
    mapTp map (Tp.instantiate replacement body) =
      Tp.instantiate (mapTp map replacement) (mapTp map body) := by
  exact mapTp_instantiateAt map 0 replacement body

theorem mapTp_dropAt? (map : SignatureMap) (cutoff : Nat) (type : Tp) :
    (Tp.dropAt? cutoff type).map (mapTp map) =
      Tp.dropAt? cutoff (mapTp map type) := by
  induction type generalizing cutoff with
  | var index =>
      by_cases below : index < cutoff
      · simp [Tp.dropAt?, mapTp, below]
      · by_cases equal : index = cutoff
        · simp [Tp.dropAt?, mapTp, equal]
        · simp [Tp.dropAt?, mapTp, below, equal]
  | prop => simp [Tp.dropAt?, mapTp]
  | base => simp [Tp.dropAt?, mapTp]
  | arr domain codomain domainIH codomainIH =>
      simp only [Tp.dropAt?, mapTp]
      rw [← domainIH cutoff, ← codomainIH cutoff]
      cases Tp.dropAt? cutoff domain <;>
        cases Tp.dropAt? cutoff codomain <;> rfl
  | all body bodyIH =>
      simp only [Tp.dropAt?, mapTp]
      rw [← bodyIH (cutoff + 1)]
      cases Tp.dropAt? (cutoff + 1) body <;> rfl

theorem mapTm_shift (map : SignatureMap) (cutoff amount : Nat) (term : Tm) :
    mapTm map (Tm.shift cutoff amount term) =
      Tm.shift cutoff amount (mapTm map term) := by
  induction term generalizing cutoff <;> simp [mapTm, Tm.shift, *]
  all_goals split <;> rfl

theorem mapTm_typeShift (map : SignatureMap) (cutoff amount : Nat)
    (term : Tm) :
    mapTm map (Tm.typeShift cutoff amount term) =
      Tm.typeShift cutoff amount (mapTm map term) := by
  induction term generalizing cutoff <;>
    simp [mapTm, Tm.typeShift, mapTp_shift, *]

theorem mapTm_instantiateAt (map : SignatureMap) (depth : Nat)
    (replacement body : Tm) :
    mapTm map (Tm.instantiateAt depth replacement body) =
      Tm.instantiateAt depth (mapTm map replacement) (mapTm map body) := by
  induction body generalizing depth with
  | db index =>
      by_cases below : index < depth
      · simp [Tm.instantiateAt, mapTm, below]
      · by_cases equal : index = depth
        · simp [Tm.instantiateAt, mapTm, equal, mapTm_shift]
        · simp [Tm.instantiateAt, mapTm, below, equal]
  | named => simp [Tm.instantiateAt, mapTm]
  | prim => simp [Tm.instantiateAt, mapTm]
  | app function argument functionIH argumentIH =>
      simp [Tm.instantiateAt, mapTm, functionIH, argumentIH]
  | lam type body bodyIH =>
      simp [Tm.instantiateAt, mapTm, bodyIH]
  | imp domain codomain domainIH codomainIH =>
      simp [Tm.instantiateAt, mapTm, domainIH, codomainIH]
  | all type body bodyIH =>
      simp [Tm.instantiateAt, mapTm, bodyIH]
  | typeApp function type functionIH =>
      simp [Tm.instantiateAt, mapTm, functionIH]
  | typeLam body bodyIH =>
      simp [Tm.instantiateAt, mapTm, bodyIH]
  | typeAll body bodyIH =>
      simp [Tm.instantiateAt, mapTm, bodyIH]

@[simp] theorem mapTm_instantiate (map : SignatureMap)
    (replacement body : Tm) :
    mapTm map (Tm.instantiate replacement body) =
      Tm.instantiate (mapTm map replacement) (mapTm map body) := by
  exact mapTm_instantiateAt map 0 replacement body

theorem mapTm_typeInstantiateAt (map : SignatureMap) (depth : Nat)
    (replacement : Tp) (term : Tm) :
    mapTm map (Tm.typeInstantiateAt depth replacement term) =
      Tm.typeInstantiateAt depth (mapTp map replacement) (mapTm map term) := by
  induction term generalizing depth <;>
    simp [mapTm, Tm.typeInstantiateAt, mapTp_instantiateAt, *]

@[simp] theorem mapTm_typeInstantiate (map : SignatureMap)
    (replacement : Tp) (term : Tm) :
    mapTm map (Tm.typeInstantiate replacement term) =
      Tm.typeInstantiate (mapTp map replacement) (mapTm map term) := by
  exact mapTm_typeInstantiateAt map 0 replacement term

theorem mapTm_dropAt? (map : SignatureMap) (cutoff : Nat) (term : Tm) :
    (Tm.dropAt? cutoff term).map (mapTm map) =
      Tm.dropAt? cutoff (mapTm map term) := by
  induction term generalizing cutoff with
  | db index =>
      by_cases below : index < cutoff
      · simp [Tm.dropAt?, mapTm, below]
      · by_cases equal : index = cutoff
        · simp [Tm.dropAt?, mapTm, equal]
        · simp [Tm.dropAt?, mapTm, below, equal]
  | named => simp [Tm.dropAt?, mapTm]
  | prim => simp [Tm.dropAt?, mapTm]
  | app function argument functionIH argumentIH =>
      simp only [Tm.dropAt?, mapTm]
      rw [← functionIH cutoff, ← argumentIH cutoff]
      cases Tm.dropAt? cutoff function <;>
        cases Tm.dropAt? cutoff argument <;> rfl
  | lam type body bodyIH =>
      simp only [Tm.dropAt?, mapTm]
      rw [← bodyIH (cutoff + 1)]
      cases Tm.dropAt? (cutoff + 1) body <;> rfl
  | imp domain codomain domainIH codomainIH =>
      simp only [Tm.dropAt?, mapTm]
      rw [← domainIH cutoff, ← codomainIH cutoff]
      cases Tm.dropAt? cutoff domain <;>
        cases Tm.dropAt? cutoff codomain <;> rfl
  | all type body bodyIH =>
      simp only [Tm.dropAt?, mapTm]
      rw [← bodyIH (cutoff + 1)]
      cases Tm.dropAt? (cutoff + 1) body <;> rfl
  | typeApp function type functionIH =>
      simp only [Tm.dropAt?, mapTm]
      rw [← functionIH cutoff]
      cases Tm.dropAt? cutoff function <;> rfl
  | typeLam body bodyIH =>
      simp only [Tm.dropAt?, mapTm]
      rw [← bodyIH cutoff]
      cases Tm.dropAt? cutoff body <;> rfl
  | typeAll body bodyIH =>
      simp only [Tm.dropAt?, mapTm]
      rw [← bodyIH cutoff]
      cases Tm.dropAt? cutoff body <;> rfl

theorem mapTm_typeDropAt? (map : SignatureMap) (cutoff : Nat)
    (term : Tm) :
    (Tm.typeDropAt? cutoff term).map (mapTm map) =
      Tm.typeDropAt? cutoff (mapTm map term) := by
  induction term generalizing cutoff with
  | db => simp [Tm.typeDropAt?, mapTm]
  | named => simp [Tm.typeDropAt?, mapTm]
  | prim => simp [Tm.typeDropAt?, mapTm]
  | app function argument functionIH argumentIH =>
      simp only [Tm.typeDropAt?, mapTm]
      rw [← functionIH cutoff, ← argumentIH cutoff]
      cases Tm.typeDropAt? cutoff function <;>
        cases Tm.typeDropAt? cutoff argument <;> rfl
  | lam type body bodyIH =>
      simp only [Tm.typeDropAt?, mapTm]
      rw [← mapTp_dropAt? map cutoff type, ← bodyIH cutoff]
      cases Tp.dropAt? cutoff type <;>
        cases Tm.typeDropAt? cutoff body <;> rfl
  | imp domain codomain domainIH codomainIH =>
      simp only [Tm.typeDropAt?, mapTm]
      rw [← domainIH cutoff, ← codomainIH cutoff]
      cases Tm.typeDropAt? cutoff domain <;>
        cases Tm.typeDropAt? cutoff codomain <;> rfl
  | all type body bodyIH =>
      simp only [Tm.typeDropAt?, mapTm]
      rw [← mapTp_dropAt? map cutoff type, ← bodyIH cutoff]
      cases Tp.dropAt? cutoff type <;>
        cases Tm.typeDropAt? cutoff body <;> rfl
  | typeApp function type functionIH =>
      simp only [Tm.typeDropAt?, mapTm]
      rw [← functionIH cutoff, ← mapTp_dropAt? map cutoff type]
      cases Tm.typeDropAt? cutoff function <;>
        cases Tp.dropAt? cutoff type <;> rfl
  | typeLam body bodyIH =>
      simp only [Tm.typeDropAt?, mapTm]
      rw [← bodyIH (cutoff + 1)]
      cases Tm.typeDropAt? (cutoff + 1) body <;> rfl
  | typeAll body bodyIH =>
      simp only [Tm.typeDropAt?, mapTm]
      rw [← bodyIH (cutoff + 1)]
      cases Tm.typeDropAt? (cutoff + 1) body <;> rfl

/-! ## Formation and beta/eta normalization -/

@[simp] theorem plainWellFormed_mapTp (map : SignatureMap)
    (typeDepth : Nat) (type : Tp) :
    (mapTp map type).plainWellFormed typeDepth =
      type.plainWellFormed typeDepth := by
  induction type <;> simp [mapTp, Tp.plainWellFormed, *]

@[simp] theorem polyWellFormed_mapTp (map : SignatureMap)
    (typeDepth : Nat) (type : Tp) :
    (mapTp map type).polyWellFormed typeDepth =
      type.polyWellFormed typeDepth := by
  induction type generalizing typeDepth with
  | var index => exact plainWellFormed_mapTp map typeDepth (.var index)
  | prop => exact plainWellFormed_mapTp map typeDepth .prop
  | base index => exact plainWellFormed_mapTp map typeDepth (.base index)
  | arr domain codomain domainIH codomainIH =>
      exact plainWellFormed_mapTp map typeDepth (.arr domain codomain)
  | all body bodyIH =>
      simpa [mapTp, Tp.polyWellFormed] using bodyIH (typeDepth + 1)

def mapPass (map : SignatureMap) (result : Tm × Bool) : Tm × Bool :=
  (mapTm map result.1, result.2)

theorem normalizeOne_map (map : SignatureMap) (term : Tm) :
    Tm.normalizeOne (mapTm map term) =
      mapPass map (Tm.normalizeOne term) := by
  induction term with
  | db => rfl
  | named => rfl
  | prim => rfl
  | app function argument functionIH argumentIH =>
      cases functionPass : Tm.normalizeOne function with
      | mk functionResult functionStable =>
          cases argumentPass : Tm.normalizeOne argument with
          | mk argumentResult argumentStable =>
              have mappedFunction := functionIH
              have mappedArgument := argumentIH
              rw [functionPass] at mappedFunction
              rw [argumentPass] at mappedArgument
              cases functionResult <;>
                simp [Tm.normalizeOne, mapTm, mapPass, functionPass,
                  argumentPass, mappedFunction, mappedArgument,
                  mapTm_instantiate]
  | lam type body bodyIH =>
      cases bodyPass : Tm.normalizeOne body with
      | mk bodyResult bodyStable =>
          have mappedBody := bodyIH
          rw [bodyPass] at mappedBody
          cases bodyResult <;>
            simp [Tm.normalizeOne, mapTm, mapPass, bodyPass, mappedBody]
          case app function argument =>
            cases argument <;> try rfl
            case db index =>
              cases index with
              | zero =>
                  have dropCommutes := mapTm_dropAt? map 0 function
                  simp only [mapTm]
                  rw [← dropCommutes]
                  cases Tm.dropAt? 0 function <;> rfl
              | succ index => rfl
  | imp domain codomain domainIH codomainIH =>
      simp [Tm.normalizeOne, mapTm, mapPass, domainIH, codomainIH]
  | all type body bodyIH =>
      simp [Tm.normalizeOne, mapTm, mapPass, bodyIH]
  | typeApp function type functionIH =>
      cases functionPass : Tm.normalizeOne function with
      | mk functionResult functionStable =>
          have mappedFunction := functionIH
          rw [functionPass] at mappedFunction
          cases functionResult <;>
            simp [Tm.normalizeOne, mapTm, mapPass, functionPass,
              mappedFunction, mapTm_typeInstantiate]
  | typeLam body bodyIH =>
      cases bodyPass : Tm.normalizeOne body with
      | mk bodyResult bodyStable =>
          have mappedBody := bodyIH
          rw [bodyPass] at mappedBody
          cases bodyResult <;>
            simp [Tm.normalizeOne, mapTm, mapPass, bodyPass, mappedBody]
          case typeApp function type =>
            cases type <;> try rfl
            case var index =>
              cases index with
              | zero =>
                  have dropCommutes := mapTm_typeDropAt? map 0 function
                  change
                    (match Tm.typeDropAt? 0 (mapTm map function) with
                      | some contracted => (contracted, false)
                      | none =>
                          (.typeLam (.typeApp (mapTm map function) (.var 0)),
                            bodyStable)) =
                    mapPass map
                      (match Tm.typeDropAt? 0 function with
                        | some contracted => (contracted, false)
                        | none =>
                            (.typeLam (.typeApp function (.var 0)), bodyStable))
                  rw [← dropCommutes]
                  cases Tm.typeDropAt? 0 function <;> rfl
              | succ index => rfl
  | typeAll body bodyIH =>
      simp [Tm.normalizeOne, mapTm, mapPass, bodyIH]

theorem tmNormalize_map (map : SignatureMap) (fuel : Nat) (term : Tm) :
    Tm.normalize fuel (mapTm map term) =
      (Tm.normalize fuel term).map (mapTm map) := by
  induction fuel generalizing term with
  | zero =>
      unfold Tm.normalize
      rw [normalizeOne_map]
      cases pass : Tm.normalizeOne term with
      | mk result stable =>
          cases stable <;> simp [mapPass]
  | succ fuel fuelIH =>
      unfold Tm.normalize
      rw [normalizeOne_map]
      cases pass : Tm.normalizeOne term with
      | mk result stable =>
          cases stable
          · simp [mapPass, fuelIH]
          · simp [mapPass]

/-! ## Declaration-aware heterogeneous embeddings -/

/-- Exact selected-signature transport.  Agreement includes failed lookup,
so a target may add declarations only outside the three translated images.
This is the operational condition needed to preserve both acceptance and
rejection under bounded conversion. -/
structure Embedding (source target : Environment) where
  map : SignatureMap
  lookupPrimitive_commutes : forall index,
    target.primitives[map.primitive index]? =
      (source.primitives[index]?).map (mapTp map)
  lookupTerm_commutes : forall name,
    target.lookupTerm? (map.name name) =
      (source.lookupTerm? name).map (mapTermDecl map)
  lookupKnown_commutes : forall name,
    target.lookupKnown? (map.name name) =
      (source.lookupKnown? name).map (mapTm map)

namespace Embedding

variable {source middle target : Environment}

/-! ## Computation commutes with signature transport -/

theorem deltaNormalize_map (embedding : Embedding source target)
    (fuel : Nat) (term : Tm) :
    deltaNormalize target fuel (mapTm embedding.map term) =
      (deltaNormalize source fuel term).map (mapTm embedding.map) := by
  induction fuel generalizing term with
  | zero =>
      induction term with
      | db => simp [mapTm, deltaNormalize]
      | named name =>
          simp only [mapTm, deltaNormalize]
          rw [embedding.lookupTerm_commutes]
          cases lookup : source.lookupTerm? name with
          | none => rfl
          | some declaration =>
              cases declaration with
              | mk declarationName declarationType definition =>
                  cases definition <;> rfl
      | prim => simp [mapTm, deltaNormalize]
      | app function argument functionIH argumentIH =>
          simp only [mapTm, deltaNormalize]
          rw [functionIH, argumentIH]
          cases deltaNormalize source 0 function <;>
            cases deltaNormalize source 0 argument <;> rfl
      | lam type body bodyIH =>
          simp only [mapTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source 0 body <;> rfl
      | imp domain codomain domainIH codomainIH =>
          simp only [mapTm, deltaNormalize]
          rw [domainIH, codomainIH]
          cases deltaNormalize source 0 domain <;>
            cases deltaNormalize source 0 codomain <;> rfl
      | all type body bodyIH =>
          simp only [mapTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source 0 body <;> rfl
      | typeApp function type functionIH =>
          simp only [mapTm, deltaNormalize]
          rw [functionIH]
          cases deltaNormalize source 0 function <;> rfl
      | typeLam body bodyIH =>
          simp only [mapTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source 0 body <;> rfl
      | typeAll body bodyIH =>
          simp only [mapTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source 0 body <;> rfl
  | succ fuel fuelIH =>
      induction term with
      | db => simp [mapTm, deltaNormalize]
      | named name =>
          simp only [mapTm, deltaNormalize]
          rw [embedding.lookupTerm_commutes]
          cases lookup : source.lookupTerm? name with
          | none => rfl
          | some declaration =>
              cases declaration with
              | mk declarationName declarationType definition =>
                  cases definition with
                  | none => rfl
                  | some definition =>
                      simpa [mapTermDecl] using fuelIH definition
      | prim => simp [mapTm, deltaNormalize]
      | app function argument functionIH argumentIH =>
          simp only [mapTm, deltaNormalize]
          rw [functionIH, argumentIH]
          cases deltaNormalize source (fuel + 1) function <;>
            cases deltaNormalize source (fuel + 1) argument <;> rfl
      | lam type body bodyIH =>
          simp only [mapTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source (fuel + 1) body <;> rfl
      | imp domain codomain domainIH codomainIH =>
          simp only [mapTm, deltaNormalize]
          rw [domainIH, codomainIH]
          cases deltaNormalize source (fuel + 1) domain <;>
            cases deltaNormalize source (fuel + 1) codomain <;> rfl
      | all type body bodyIH =>
          simp only [mapTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source (fuel + 1) body <;> rfl
      | typeApp function type functionIH =>
          simp only [mapTm, deltaNormalize]
          rw [functionIH]
          cases deltaNormalize source (fuel + 1) function <;> rfl
      | typeLam body bodyIH =>
          simp only [mapTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source (fuel + 1) body <;> rfl
      | typeAll body bodyIH =>
          simp only [mapTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source (fuel + 1) body <;> rfl

/-- Full beta/eta/delta normalization, including fuel failure, is natural in
every exact heterogeneous signature embedding. -/
theorem normalize_map (embedding : Embedding source target)
    (fuel : Nat) (term : Tm) :
    MathdataKernel.normalize target fuel (mapTm embedding.map term) =
      (MathdataKernel.normalize source fuel term).map
        (mapTm embedding.map) := by
  unfold MathdataKernel.normalize
  rw [embedding.deltaNormalize_map]
  cases normalized : deltaNormalize source fuel term with
  | none => rfl
  | some deltaNormal =>
      simpa using tmNormalize_map embedding.map fuel deltaNormal

/-! ## Type synthesis and proposition formation -/

theorem mapTp_eq_prop_iff (map : SignatureMap) (type : Tp) :
    mapTp map type = .prop <-> type = .prop := by
  constructor
  · intro mapped
    exact mapTp_injective map (by simpa [mapTp] using mapped)
  · rintro rfl
    rfl

theorem map_mapTp_shift (map : SignatureMap) (cutoff amount : Nat)
    (context : List Tp) :
    (context.map (mapTp map)).map (Tp.shift cutoff amount) =
      (context.map (Tp.shift cutoff amount)).map (mapTp map) := by
  simp only [List.map_map, List.map_inj_left]
  intro type membership
  exact (mapTp_shift map cutoff amount type).symm

theorem inferTerm_map (embedding : Embedding source target)
    (typeDepth : Nat) (termContext : List Tp) (term : Tm) :
    inferTerm target typeDepth (termContext.map (mapTp embedding.map))
        (mapTm embedding.map term) =
      (inferTerm source typeDepth termContext term).map
        (mapTp embedding.map) := by
  induction term generalizing typeDepth termContext with
  | db index =>
      simp [mapTm, inferTerm]
  | named name =>
      simp only [mapTm, inferTerm]
      rw [embedding.lookupTerm_commutes]
      cases lookup : source.lookupTerm? name with
      | none => rfl
      | some declaration =>
          cases declaration
          rfl
  | prim index =>
      simp only [mapTm, inferTerm]
      exact embedding.lookupPrimitive_commutes index
  | app function argument functionIH argumentIH =>
      simp only [mapTm, inferTerm]
      rw [functionIH, argumentIH]
      cases functionResult :
          inferTerm source typeDepth termContext function with
      | none => rfl
      | some functionType =>
          cases functionType <;> try rfl
          case arr domain codomain =>
            cases argumentResult :
                inferTerm source typeDepth termContext argument with
            | none => rfl
            | some actual =>
                by_cases sameType : actual = domain
                · subst actual
                  simp [mapTp]
                · have mappedDifferent :
                      mapTp embedding.map actual ≠
                        mapTp embedding.map domain := by
                    intro equalMapping
                    exact sameType (mapTp_injective embedding.map equalMapping)
                  simp [mapTp, sameType, mappedDifferent]
  | lam type body bodyIH =>
      simp only [mapTm, inferTerm, plainWellFormed_mapTp]
      cases wellFormed : type.plainWellFormed typeDepth with
      | false => rfl
      | true =>
          have mappedBody := bodyIH typeDepth (type :: termContext)
          simp only [List.map_cons] at mappedBody
          rw [mappedBody]
          cases bodyResult :
              inferTerm source typeDepth (type :: termContext) body <;> rfl
  | imp domain codomain domainIH codomainIH =>
      simp only [mapTm, inferTerm]
      rw [domainIH, codomainIH]
      cases domainResult : inferTerm source typeDepth termContext domain with
      | none => rfl
      | some domainType =>
          cases codomainResult :
              inferTerm source typeDepth termContext codomain with
          | none =>
              cases domainType <;> rfl
          | some codomainType =>
              cases domainType <;> cases codomainType <;> rfl
  | all type body bodyIH =>
      simp only [mapTm, inferTerm, plainWellFormed_mapTp]
      cases wellFormed : type.plainWellFormed typeDepth with
      | false => rfl
      | true =>
          have mappedBody := bodyIH typeDepth (type :: termContext)
          simp only [List.map_cons] at mappedBody
          rw [mappedBody]
          cases bodyResult :
              inferTerm source typeDepth (type :: termContext) body with
          | none => rfl
          | some bodyType =>
              cases bodyType <;> rfl
  | typeApp function type functionIH =>
      simp only [mapTm, inferTerm, plainWellFormed_mapTp]
      rw [functionIH]
      cases wellFormed : type.plainWellFormed typeDepth with
      | false => rfl
      | true =>
          cases functionResult :
              inferTerm source typeDepth termContext function with
          | none => rfl
          | some functionType =>
              cases functionType <;> try rfl
              case all body =>
                simp [mapTp, mapTp_instantiate]
  | typeLam body bodyIH =>
      simp only [mapTm, inferTerm]
      rw [map_mapTp_shift]
      rw [bodyIH]
      cases bodyResult : inferTerm source (typeDepth + 1)
          (termContext.map (Tp.shift 0 1)) body <;> rfl
  | typeAll body bodyIH =>
      rfl

theorem checkProposition_map (embedding : Embedding source target)
    (typeDepth : Nat) (termContext : List Tp) (proposition : Tm) :
    checkProposition target typeDepth
        (termContext.map (mapTp embedding.map))
        (mapTm embedding.map proposition) =
      checkProposition source typeDepth termContext proposition := by
  have inferProp : forall (depth : Nat) (context : List Tp) (term : Tm),
      decide
          (inferTerm target depth (context.map (mapTp embedding.map))
              (mapTm embedding.map term) = some .prop) =
        decide (inferTerm source depth context term = some .prop) := by
    intro depth context term
    rw [embedding.inferTerm_map]
    cases result : inferTerm source depth context term <;>
      simp [mapTp_eq_prop_iff]
  induction proposition generalizing typeDepth termContext with
  | typeAll body bodyIH =>
      simp only [mapTm, checkProposition]
      exact bodyIH (typeDepth + 1) []
  | db index =>
      simp only [mapTm, checkProposition]
      exact inferProp typeDepth termContext (.db index)
  | named name =>
      simp only [mapTm, checkProposition]
      exact inferProp typeDepth termContext (.named name)
  | prim index =>
      simp only [mapTm, checkProposition]
      exact inferProp typeDepth termContext (.prim index)
  | app function argument functionIH argumentIH =>
      simp only [mapTm, checkProposition]
      exact inferProp typeDepth termContext (.app function argument)
  | lam type body bodyIH =>
      simp only [mapTm, checkProposition]
      exact inferProp typeDepth termContext (.lam type body)
  | imp domain codomain domainIH codomainIH =>
      simp only [mapTm, checkProposition]
      exact inferProp typeDepth termContext (.imp domain codomain)
  | all type body bodyIH =>
      simp only [mapTm, checkProposition]
      exact inferProp typeDepth termContext (.all type body)
  | typeApp function type functionIH =>
      simp only [mapTm, checkProposition]
      exact inferProp typeDepth termContext (.typeApp function type)
  | typeLam body bodyIH =>
      simp only [mapTm, checkProposition]
      exact inferProp typeDepth termContext (.typeLam body)

/-! ## Native proof synthesis and checking -/

theorem map_mapTm_shift (map : SignatureMap) (cutoff amount : Nat)
    (context : List Tm) :
    (context.map (mapTm map)).map (Tm.shift cutoff amount) =
      (context.map (Tm.shift cutoff amount)).map (mapTm map) := by
  simp only [List.map_map, List.map_inj_left]
  intro proposition membership
  exact (mapTm_shift map cutoff amount proposition).symm

theorem inferProof_map (embedding : Embedding source target)
    (fuel typeDepth : Nat) (termContext : List Tp)
    (proofContext : List Tm) (proof : Pf) :
    inferProof target fuel typeDepth
        (termContext.map (mapTp embedding.map))
        (proofContext.map (mapTm embedding.map))
        (mapPf embedding.map proof) =
      (inferProof source fuel typeDepth termContext proofContext proof).map
        (mapTm embedding.map) := by
  induction proof generalizing typeDepth termContext proofContext with
  | gpa name => rfl
  | hyp index =>
      simp [mapPf, inferProof]
  | known name =>
      simp only [mapPf, inferProof]
      rw [embedding.lookupKnown_commutes]
      cases lookup : source.lookupKnown? name with
      | none => rfl
      | some proposition =>
          simpa using embedding.normalize_map fuel proposition
  | termApp function argument functionIH =>
      simp only [mapPf, inferProof]
      rw [functionIH, embedding.inferTerm_map,
        embedding.deltaNormalize_map]
      cases functionResult :
          inferProof source fuel typeDepth termContext proofContext function with
      | none => rfl
      | some proposition =>
          cases proposition <;> try simp [mapTm]
          case all domain body =>
            cases actualLookup :
                inferTerm source typeDepth termContext argument with
            | none => simp
            | some actualType =>
                by_cases sameType : actualType = domain
                · subst actualType
                  simp
                  cases argumentResult :
                      deltaNormalize source fuel argument with
                  | none => simp
                  | some normalizedArgument =>
                      simp only [Option.map_some, Option.bind_some]
                      rw [← mapTm_instantiate]
                      simpa using embedding.normalize_map fuel
                        (Tm.instantiate normalizedArgument body)
                · have mappedDifferent :
                      mapTp embedding.map actualType ≠
                        mapTp embedding.map domain := by
                    intro equalMapping
                    exact sameType
                      (mapTp_injective embedding.map equalMapping)
                  simp [sameType, mappedDifferent]
  | proofApp function argument functionIH argumentIH =>
      simp only [mapPf, inferProof]
      rw [functionIH, argumentIH]
      cases functionResult :
          inferProof source fuel typeDepth termContext proofContext function with
      | none => rfl
      | some proposition =>
          cases proposition <;> try simp [mapTm]
          case imp domain codomain =>
            cases argumentResult :
                inferProof source fuel typeDepth termContext proofContext argument with
            | none => simp
            | some actual =>
                by_cases sameProposition : actual = domain
                · subst actual
                  simp
                · have mappedDifferent :
                      mapTm embedding.map actual ≠
                        mapTm embedding.map domain := by
                    intro equalMapping
                    exact sameProposition
                      (mapTm_injective embedding.map equalMapping)
                  simp [sameProposition, mappedDifferent]
  | proofLam proposition body bodyIH =>
      simp only [mapPf, inferProof]
      rw [embedding.inferTerm_map, embedding.normalize_map]
      cases propositionType : inferTerm source typeDepth termContext proposition with
      | none => rfl
      | some type =>
          cases type <;> try simp [mapTp]
          case prop =>
            cases normalization : MathdataKernel.normalize source fuel proposition with
            | none => rfl
            | some normalized =>
                simp only [Option.map_some]
                have mappedBody :=
                  bodyIH typeDepth termContext (normalized :: proofContext)
                simp only [List.map_cons] at mappedBody
                simp [mappedBody]
                cases bodyResult : inferProof source fuel typeDepth termContext
                    (normalized :: proofContext) body <;> rfl
  | termLam type body bodyIH =>
      simp only [mapPf, inferProof, plainWellFormed_mapTp]
      cases wellFormed : type.plainWellFormed typeDepth with
      | false => simp
      | true =>
          rw [map_mapTm_shift]
          have mappedBody :=
            bodyIH typeDepth (type :: termContext)
              (proofContext.map (Tm.shift 0 1))
          simp only [List.map_cons] at mappedBody
          rw [mappedBody]
          cases bodyResult : inferProof source fuel typeDepth
              (type :: termContext) (proofContext.map (Tm.shift 0 1)) body <;>
            rfl
  | typeApp function type functionIH =>
      simp only [mapPf, inferProof]
      rw [functionIH]
      cases functionResult :
          inferProof source fuel typeDepth termContext proofContext function with
      | none => rfl
      | some proposition =>
          cases proposition <;> try rfl
          case typeAll body =>
            simp [mapTm, mapTm_typeInstantiate]
  | typeLam body bodyIH =>
      cases termContext with
      | nil =>
          cases proofContext with
          | nil =>
              simp only [mapPf, List.map_nil, inferProof,
                List.isEmpty_nil, Bool.true_and, ↓reduceIte]
              have mappedBody := bodyIH (typeDepth + 1) [] []
              simp only [List.map_nil] at mappedBody
              rw [mappedBody]
              cases bodyResult : inferProof source fuel (typeDepth + 1)
                  [] [] body <;> rfl
          | cons proposition proofContext =>
              simp [mapPf, inferProof]
      | cons type termContext =>
          simp [mapPf, inferProof]

/-- Checking an already-normalized proposition is reflected as well as
preserved.  Joint injectivity is precisely the no-collapse premise used in
the rejecting branch. -/
theorem checkNormalizedProof_map (embedding : Embedding source target)
    (fuel typeDepth : Nat) (termContext : List Tp)
    (proofContext : List Tm) (proof : Pf) (proposition : Tm) :
    checkNormalizedProof target fuel typeDepth
        (termContext.map (mapTp embedding.map))
        (proofContext.map (mapTm embedding.map))
        (mapPf embedding.map proof) (mapTm embedding.map proposition) =
      checkNormalizedProof source fuel typeDepth termContext proofContext
        proof proposition := by
  unfold checkNormalizedProof
  rw [embedding.inferProof_map]
  cases proofResult :
      inferProof source fuel typeDepth termContext proofContext proof with
  | none => rfl
  | some inferred =>
      by_cases sameProposition : inferred = proposition
      · subst inferred
        simp
      · have mappedDifferent :
            mapTm embedding.map inferred ≠ mapTm embedding.map proposition := by
          intro equalMapping
          exact sameProposition
            (mapTm_injective embedding.map equalMapping)
        simp [sameProposition, mappedDifferent]

/-- Source-level proof checking, including normalization failure, commutes
exactly with heterogeneous selected-signature transport. -/
theorem checkProof_map (embedding : Embedding source target)
    (fuel typeDepth : Nat) (termContext : List Tp)
    (proofContext : List Tm) (proof : Pf) (proposition : Tm) :
    checkProof target fuel typeDepth
        (termContext.map (mapTp embedding.map))
        (proofContext.map (mapTm embedding.map))
        (mapPf embedding.map proof) (mapTm embedding.map proposition) =
      checkProof source fuel typeDepth termContext proofContext proof
        proposition := by
  unfold checkProof
  rw [embedding.normalize_map]
  cases normalization : MathdataKernel.normalize source fuel proposition with
  | none => rfl
  | some normalized =>
      exact embedding.checkNormalizedProof_map fuel typeDepth termContext
        proofContext proof normalized

/-! ## Induced selected-theory and NIK views -/

def mapProfileClaim (embedding : Embedding source target)
    (claim : ProfileClaim) : ProfileClaim where
  fuel := claim.fuel
  typeDepth := claim.typeDepth
  termContext := claim.termContext.map (mapTp embedding.map)
  proofContext := claim.proofContext.map (mapTm embedding.map)
  proposition := mapTm embedding.map claim.proposition

@[simp] theorem mapProfileClaim_fuel (embedding : Embedding source target)
    (claim : ProfileClaim) :
    (embedding.mapProfileClaim claim).fuel = claim.fuel :=
  rfl

@[simp] theorem mapProfileClaim_termContext
    (embedding : Embedding source target) (claim : ProfileClaim) :
    (embedding.mapProfileClaim claim).termContext =
      claim.termContext.map (mapTp embedding.map) :=
  rfl

@[simp] theorem mapProfileClaim_proposition
    (embedding : Embedding source target) (claim : ProfileClaim) :
    (embedding.mapProfileClaim claim).proposition =
      mapTm embedding.map claim.proposition :=
  rfl

/-- An exact heterogeneous signature embedding is a proof-carrying NIK view.
The map changes the selected theory's primitive and base-type indices without
changing the native Boolean judgment. -/
def authorityView (embedding : Embedding source target) :
    AuthorityView contract source target where
  mapClaim := embedding.mapProfileClaim
  mapCertificate := mapPf embedding.map
  check_commutes := by
    intro claim proof
    change
      checkProof target claim.fuel claim.typeDepth
          (claim.termContext.map (mapTp embedding.map))
          (claim.proofContext.map (mapTm embedding.map))
          (mapPf embedding.map proof)
          (mapTm embedding.map claim.proposition) =
        checkProof source claim.fuel claim.typeDepth claim.termContext
          claim.proofContext proof claim.proposition
    exact embedding.checkProof_map claim.fuel claim.typeDepth
      claim.termContext claim.proofContext proof claim.proposition
  meaning_preserved := by
    intro claim theoremhood
    change ProfileClaim at claim
    change NativeTheoremScope source claim at theoremhood
    change NativeTheoremScope target (embedding.mapProfileClaim claim)
    unfold NativeTheoremScope at theoremhood ⊢
    obtain ⟨proof, judged⟩ := theoremhood
    refine ⟨mapPf embedding.map proof, ?_⟩
    unfold Judges at judged ⊢
    simp only [attach, mapProfileClaim] at judged ⊢
    obtain ⟨normal, propositionNormalizes, proofSynthesizes⟩ := judged
    refine ⟨mapTm embedding.map normal, ?_, ?_⟩
    · rw [embedding.normalize_map, propositionNormalizes]
      rfl
    · rw [embedding.inferProof_map, proofSynthesizes]
      rfl

def theoryView (embedding : Embedding source target) :
    TheoryView theory source target :=
  embedding.authorityView.toTheoryView

def operationalView (embedding : Embedding source target) :=
  embedding.authorityView.toCoveredTranslation

@[simp] theorem authorityView_mapClaim (embedding : Embedding source target)
    (claim : ProfileClaim) :
    embedding.authorityView.mapClaim claim = embedding.mapProfileClaim claim :=
  rfl

@[simp] theorem authorityView_mapCertificate
    (embedding : Embedding source target) (proof : Pf) :
    embedding.authorityView.mapCertificate proof = mapPf embedding.map proof :=
  rfl

/-! ## Compatibility with the name-only first rung -/

/-- The earlier name-only environment embedding is a literal special case,
not a competing translation API. -/
def ofEnvironmentEmbedding
    (embedding :
      Mettapedia.Languages.Megalodon.EnvironmentEmbedding.Embedding
        source target) : Embedding source target where
  map := SignatureMap.ofName embedding.mapName embedding.name_injective
  lookupPrimitive_commutes := by
    intro index
    rw [embedding.primitives_eq]
    cases lookup : source.primitives[index]? <;> simp [lookup]
  lookupTerm_commutes := by
    intro name
    change target.lookupTerm? (embedding.mapName name) = _
    rw [embedding.lookupTerm_commutes]
    cases source.lookupTerm? name <;> simp
  lookupKnown_commutes := by
    intro name
    change target.lookupKnown? (embedding.mapName name) = _
    rw [embedding.lookupKnown_commutes]
    cases source.lookupKnown? name <;> simp

theorem ofEnvironmentEmbedding_mapProfileClaim
    (embedding :
      Mettapedia.Languages.Megalodon.EnvironmentEmbedding.Embedding
        source target)
    (claim : ProfileClaim) :
    (ofEnvironmentEmbedding embedding).mapProfileClaim claim =
      embedding.mapProfileClaim claim := by
  have typeIdentity :
      mapTp (SignatureMap.ofName embedding.mapName
        embedding.name_injective) = id :=
    funext (mapTp_ofName embedding.mapName embedding.name_injective)
  have termRenaming :
      mapTm (SignatureMap.ofName embedding.mapName
        embedding.name_injective) =
        Mettapedia.Languages.Megalodon.EnvironmentEmbedding.renameTm
          embedding.mapName :=
    funext (mapTm_ofName embedding.mapName embedding.name_injective)
  cases claim
  simp [mapProfileClaim, ofEnvironmentEmbedding,
    Mettapedia.Languages.Megalodon.EnvironmentEmbedding.Embedding.mapProfileClaim,
    typeIdentity, termRenaming]

/-! ## Identity and composition -/

def identity (environment : Environment) : Embedding environment environment where
  map := SignatureMap.identity
  lookupPrimitive_commutes := by
    intro index
    cases lookup : environment.primitives[index]? <;> simp [lookup]
  lookupTerm_commutes := by
    intro name
    cases lookup : environment.lookupTerm? name <;> simp [lookup]
  lookupKnown_commutes := by
    intro name
    cases lookup : environment.lookupKnown? name <;> simp [lookup]

def comp (earlier : Embedding source middle)
    (later : Embedding middle target) : Embedding source target where
  map := earlier.map.comp later.map
  lookupPrimitive_commutes := by
    intro index
    change target.primitives[later.map.primitive
        (earlier.map.primitive index)]? = _
    rw [later.lookupPrimitive_commutes, earlier.lookupPrimitive_commutes]
    cases lookup : source.primitives[index]? <;>
      simp [mapTp_comp]
  lookupTerm_commutes := by
    intro name
    change target.lookupTerm? (later.map.name (earlier.map.name name)) = _
    rw [later.lookupTerm_commutes, earlier.lookupTerm_commutes]
    cases lookup : source.lookupTerm? name <;>
      simp [mapTermDecl_comp]
  lookupKnown_commutes := by
    intro name
    change target.lookupKnown? (later.map.name (earlier.map.name name)) = _
    rw [later.lookupKnown_commutes, earlier.lookupKnown_commutes]
    cases lookup : source.lookupKnown? name <;>
      simp [mapTm_comp]

theorem mapProfileClaim_comp (earlier : Embedding source middle)
    (later : Embedding middle target) (claim : ProfileClaim) :
    (comp earlier later).mapProfileClaim claim =
      later.mapProfileClaim (earlier.mapProfileClaim claim) := by
  cases claim
  simp [mapProfileClaim, comp, List.map_map, mapTp_comp, mapTm_comp]

theorem mapPf_comp_embedding (earlier : Embedding source middle)
    (later : Embedding middle target) (proof : Pf) :
    mapPf (comp earlier later).map proof =
      mapPf later.map (mapPf earlier.map proof) := by
  simpa [comp] using (mapPf_comp earlier.map later.map proof).symm

theorem mapProfileClaim_identity (environment : Environment)
    (claim : ProfileClaim) :
    (identity environment).mapProfileClaim claim = claim := by
  have typeIdentity : mapTp SignatureMap.identity = id :=
    funext mapTp_identity
  have termIdentity : mapTm SignatureMap.identity = id :=
    funext mapTm_identity
  cases claim
  simp [mapProfileClaim, identity, typeIdentity, termIdentity]

end Embedding

/-! ## Joint name/primitive/base transport canaries -/

namespace Canary

def prefixName (name : Name) : Name :=
  "signature/" ++ name

theorem prefixName_injective : Function.Injective prefixName := by
  intro first second equalNames
  exact (String.append_right_inj "signature/").mp equalNames

theorem prefixName_ne_empty (name : Name) : prefixName name ≠ "" := by
  intro emptyName
  have equalLengths := congrArg String.length emptyName
  simp [prefixName] at equalLengths

/-- A genuinely heterogeneous map: every selected-signature address space is
shifted, while intrinsic binders remain unchanged. -/
def signatureMap : SignatureMap where
  name := prefixName
  primitive := Nat.succ
  base := Nat.succ
  name_injective := prefixName_injective
  primitive_injective := by
    intro first second equalSuccessors
    exact Nat.succ.inj equalSuccessors
  base_injective := by
    intro first second equalSuccessors
    exact Nat.succ.inj equalSuccessors

def predicateType : Tp :=
  .arr (.base 0) .prop

def namedAtom : Tm :=
  .app (.named "p") (.db 0)

def primitiveAtom : Tm :=
  .app (.prim 0) (.db 0)

/-- The quantified proposition depends simultaneously on a global term name,
a primitive index, and a base-type index. -/
def domain : Tm :=
  .all (.base 0) (.imp namedAtom primitiveAtom)

def goal : Tm :=
  .imp domain domain

def proof : Pf :=
  .proofLam domain
    (.termLam (.base 0) (.termApp (.hyp 0) (.db 0)))

def sourceEnvironment : Environment :=
  { primitives := [predicateType]
    terms := [{ name := "p", type := predicateType }] }

def outsideTerm : TermDecl :=
  { name := "", type := .prop }

def outsideKnown : KnownDecl :=
  { name := "", proposition := .imp (.named "outside") (.named "outside") }

def targetEnvironment : Environment :=
  { primitives := [.prop, mapTp signatureMap predicateType]
    terms := outsideTerm ::
      sourceEnvironment.terms.map (mapTermDecl signatureMap)
    known := [outsideKnown] }

def heterogeneousEmbedding :
    Embedding sourceEnvironment targetEnvironment where
  map := signatureMap
  lookupPrimitive_commutes := by
    intro index
    cases index <;>
      simp [sourceEnvironment, targetEnvironment, predicateType,
        signatureMap, mapTp]
  lookupTerm_commutes := by
    intro name
    have outsideImage : ("" : Name) ≠ signatureMap.name name :=
      (prefixName_ne_empty name).symm
    change
      lookupTermList?
          (outsideTerm ::
            sourceEnvironment.terms.map (mapTermDecl signatureMap))
          (signatureMap.name name) =
        (lookupTermList? sourceEnvironment.terms name).map
          (mapTermDecl signatureMap)
    simp only [lookupTermList?]
    rw [if_neg (by simpa [outsideTerm] using outsideImage)]
    exact lookupTermList?_map signatureMap sourceEnvironment.terms name
  lookupKnown_commutes := by
    intro name
    have outsideImage : ("" : Name) ≠ signatureMap.name name :=
      (prefixName_ne_empty name).symm
    simp [targetEnvironment, sourceEnvironment, outsideKnown,
      Environment.lookupKnown?, lookupKnownList?, outsideImage]

/-- Baseline positive control in the source selected theory. -/
theorem source_accepts :
    checkProof sourceEnvironment 16 0 [] [] proof goal = true := by
  simp [sourceEnvironment, proof, goal, domain, namedAtom, primitiveAtom,
    predicateType, checkProof, checkNormalizedProof, inferProof,
    inferTerm, MathdataKernel.normalize, deltaNormalize,
    Tm.normalize, Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?,
    Tm.shift, Tm.instantiate, Tm.instantiateAt, Tp.plainWellFormed]

/-- Positive control: one real native proof replays after all three signature
address spaces move, not merely after a name relabeling. -/
theorem transported_accepts :
    checkProof targetEnvironment 16 0 [] []
        (mapPf signatureMap proof) (mapTm signatureMap goal) = true := by
  calc
    checkProof targetEnvironment 16 0 [] []
        (mapPf signatureMap proof) (mapTm signatureMap goal) =
      checkProof sourceEnvironment 16 0 [] [] proof goal := by
        simpa [heterogeneousEmbedding] using
          heterogeneousEmbedding.checkProof_map 16 0 [] [] proof goal
    _ = true := source_accepts

def sourceClaim : ProfileClaim where
  fuel := 16
  typeDepth := 0
  termContext := []
  proofContext := []
  proposition := goal

theorem source_profile_accepts :
    (contract.checker sourceEnvironment).check sourceClaim proof = true := by
  exact source_accepts

/-- The same positive control through NIK's selected-theory authority waist. -/
theorem transported_profile_accepts :
    (contract.checker targetEnvironment).check
        (heterogeneousEmbedding.mapProfileClaim sourceClaim)
        (mapPf signatureMap proof) = true := by
  calc
    (contract.checker targetEnvironment).check
        (heterogeneousEmbedding.mapProfileClaim sourceClaim)
        (mapPf signatureMap proof) =
      (contract.checker sourceEnvironment).check sourceClaim proof := by
        simpa [heterogeneousEmbedding] using
          heterogeneousEmbedding.authorityView.check_commutes sourceClaim proof
    _ = true := source_profile_accepts

/-- The target genuinely contains unrelated authority outside the translated
global-name image. -/
theorem target_has_outside_term :
    targetEnvironment.lookupTerm? "" = some outsideTerm := by
  rfl

/-- Corrupt exactly the mapped primitive slot while retaining the mapped
declarations. -/
def wrongPrimitiveEnvironment : Environment :=
  { targetEnvironment with primitives := [.prop, .prop] }

/-- Negative behavioral control: the mapped proof is rejected when the
primitive table lies about the translated predicate's type. -/
theorem wrong_primitive_rejects :
    checkProof wrongPrimitiveEnvironment 16 0 [] []
        (mapPf signatureMap proof) (mapTm signatureMap goal) = false := by
  simp [wrongPrimitiveEnvironment, targetEnvironment, sourceEnvironment,
    outsideTerm, signatureMap, prefixName, mapPf, mapTm, mapTp, mapTermDecl,
    proof, goal, domain, namedAtom, primitiveAtom, predicateType, checkProof,
    checkNormalizedProof, inferProof, inferTerm,
    MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Environment.lookupTerm?, lookupTermList?, Tm.shift, Tm.instantiate,
    Tm.instantiateAt, Tp.plainWellFormed]

/-- Negative structural control: the corrupted environment cannot possess an
embedding with the prescribed signature map.  Thus the canary is enforced by
the interface itself, not merely noticed by one proof. -/
theorem no_embedding_with_wrong_primitive :
    ¬ (exists embedding :
        Embedding sourceEnvironment wrongPrimitiveEnvironment,
      embedding.map = signatureMap) := by
  rintro ⟨embedding, sameMap⟩
  have primitiveAgreement := embedding.lookupPrimitive_commutes 0
  rw [sameMap] at primitiveAgreement
  simp [sourceEnvironment, wrongPrimitiveEnvironment, targetEnvironment,
    predicateType, signatureMap, mapTp] at primitiveAgreement

#print axioms source_accepts
#print axioms transported_accepts
#print axioms transported_profile_accepts
#print axioms wrong_primitive_rejects
#print axioms no_embedding_with_wrong_primitive
#print axioms Embedding.checkProof_map
#print axioms Embedding.authorityView
#print axioms Embedding.mapProfileClaim_comp

end Canary

end Mettapedia.Languages.Megalodon.SignatureEmbedding
