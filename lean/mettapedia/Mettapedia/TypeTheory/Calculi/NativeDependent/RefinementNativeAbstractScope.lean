import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementModelScope
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModel
import Mettapedia.TypeTheory.PresheafNativePredicateModel

/-!
# Native mixed scopes as actual local-model scopes

Both presentations retain the entire sequence of dependent data and predicate
assumption binders. The comparison traverses those sequences in both
directions, retains their actual contexts and dependent variable sections,
and compares guarded argument assembly through its factorization property.
No interpreter agreement is assumed by the scope comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open ContextualModelTelescopes NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C]

namespace NativeAbstractScope

abbrev GenericData (n : Nat) (P : Cᵒᵖ ⥤ Type u) :=
  ContextualPredicateModelScopes.ScopeData (NativeModel C)
    (PresheafNativePredicateModel.model C).doctrine
    (PresheafNativePredicateModel.model C).assumptions n P

abbrev GenericScope (n : Nat) :=
  Abstract.ModelScope (NativeModel C) (PresheafNativePredicateModel.model C) n

/-- Retain every supplied data and assumption binder, with its exact context. -/
noncomputable def toGenericData : {n : Nat} → {P : Cᵒᵖ ⥤ Type u} →
    ScopeData C n P → GenericData n P
  | _, _, .nil => .nil
  | _, _, .snoc previous type => .snoc (toGenericData previous) type
  | _, _, .assume previous predicate => .assume (toGenericData previous) predicate

/-- The native instance has exactly the same two context constructors. -/
noncomputable def toNativeData : {n : Nat} → {P : Cᵒᵖ ⥤ Type u} →
    GenericData (C := C) n P → ScopeData C n P
  | _, _, .nil => .nil
  | _, _, .snoc previous type => .snoc (toNativeData previous) type
  | _, _, .assume previous predicate => .assume (toNativeData previous) predicate

@[simp] theorem toNative_toGeneric : {n : Nat} → {P : Cᵒᵖ ⥤ Type u} →
    (data : ScopeData C n P) → toNativeData (toGenericData data) = data
  | _, _, .nil => rfl
  | _, _, .snoc previous type => by
      simp only [toGenericData, toNativeData, toNative_toGeneric]
  | _, _, .assume previous predicate => by
      simp only [toGenericData, toNativeData, toNative_toGeneric]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem toGeneric_toNative : {n : Nat} → {P : Cᵒᵖ ⥤ Type u} →
    (data : GenericData (C := C) n P) → toGenericData (toNativeData data) = data
  | _, _, .nil => rfl
  | _, _, .snoc previous type => by
      exact congrArg (fun spine =>
        ContextualPredicateModelScopes.ScopeData.snoc spine type) (toGeneric_toNative previous)
  | _, _, .assume previous predicate => by
      exact congrArg (fun spine =>
        ContextualPredicateModelScopes.ScopeData.assume spine predicate) (toGeneric_toNative previous)

noncomputable def toGeneric {n : Nat} (scope : Scope C n) : GenericScope (C := C) n :=
  ⟨scope.1, toGenericData scope.2⟩

noncomputable def toNative {n : Nat} (scope : GenericScope (C := C) n) : Scope C n :=
  ⟨scope.1, toNativeData scope.2⟩

@[simp] theorem toNative_toGeneric_scope {n : Nat} (scope : Scope C n) :
    toNative (toGeneric scope) = scope := by
  cases scope with
  | mk context data => simp only [toGeneric, toNative, toNative_toGeneric]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem toGeneric_toNative_scope {n : Nat} (scope : GenericScope (C := C) n) :
    toGeneric (toNative scope) = scope := by
  cases scope with
  | mk context data =>
      exact congrArg (fun spine => Sigma.mk context spine) (toGeneric_toNative data)

noncomputable def scopeEquiv (n : Nat) : Scope C n ≃ GenericScope (C := C) n where
  toFun := toGeneric
  invFun := toNative
  left_inv := toNative_toGeneric_scope
  right_inv := toGeneric_toNative_scope

@[simp] theorem toGeneric_nil : toGeneric (Scope.nil C) =
    ContextualPredicateModelScopes.Scope.nil (NativeModel C)
      (PresheafNativePredicateModel.model C).doctrine
      (PresheafNativePredicateModel.model C).assumptions := rfl

@[simp] theorem toGeneric_snoc {n : Nat} (scope : Scope C n) (type : NativeType scope.1) :
    toGeneric (scope.snoc type) = (toGeneric scope).snoc type := rfl

@[simp] theorem toGeneric_assume {n : Nat} (scope : Scope C n) (predicate : Subfunctor scope.1) :
    toGeneric (scope.assume predicate) = (toGeneric scope).assume predicate := rfl

@[simp] theorem lookup_compare : {n : Nat} → {P : Cᵒᵖ ⥤ Type u} →
    (data : ScopeData C n P) → (index : Fin n) →
      (toGenericData data).lookup index = data.lookup index
  | _, _, .nil, index => Fin.elim0 index
  | _, _, .snoc previous type, index => by
      cases index using Fin.cases with
      | zero => rfl
      | succ index =>
          change ((toGenericData previous).lookup index).substitute
              ((NativeModel C).toCwf.wk type) =
            (previous.lookup index).substitute ((NativeModel C).toCwf.wk type)
          rw [lookup_compare]
  | _, _, .assume previous predicate, index => by
      change ((toGenericData previous).lookup index).substitute predicate.ι =
        (previous.lookup index).substitute predicate.ι
      rw [lookup_compare]

@[simp] theorem components_compare {n : Nat} {P Q : Cᵒᵖ ⥤ Type u}
    (data : ScopeData C n P) (substitution : Q ⟶ P) (index : Fin n) :
    (toGenericData data).components substitution index = data.components substitution index := by
  change ((toGenericData data).lookup index).substitute substitution =
    (data.lookup index).substitute substitution
  rw [lookup_compare]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison concerns actual complete guarded maps, including every
assumption restriction, rather than successful data checks alone. -/
theorem assembly_compare {n : Nat} {P Q : Cᵒᵖ ⥤ Type u}
    (data : ScopeData C n P) (supplied : Fin n → Option (NativeValue Q)) :
    (toGenericData data).assemble? supplied = data.assemble? supplied := by
  have reads : ∀ substitution : Q ⟶ P,
      (toGenericData data).assemble? supplied = some substitution ↔
        data.assemble? supplied = some substitution := by
    intro substitution
    rw [ContextualPredicateModelScopes.ScopeData.assemble?_eq_some_iff,
      ScopeData.assemble?_eq_some_iff]
    simp only [components_compare]
  cases nativeRead : data.assemble? supplied with
  | none =>
      cases genericRead : (toGenericData data).assemble? supplied with
      | none => rfl
      | some substitution =>
          have impossible := (reads substitution).mp genericRead
          rw [nativeRead] at impossible
          cases impossible
  | some substitution => exact (reads substitution).mpr nativeRead

end NativeAbstractScope

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
