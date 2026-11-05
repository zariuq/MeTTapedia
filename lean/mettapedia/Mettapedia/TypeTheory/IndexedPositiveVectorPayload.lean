import Mettapedia.TypeTheory.IndexedPositiveContainer

/-!
# Payload-parametric interpretation of the indexed Vector fragment

The length language and registered Vector container are unchanged. Payload
values may inhabit any universe. The common interface universe requires
explicit lifts of natural data and the otherwise unindexed family index.
Transport changes payload values and preserves every length expression.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPositiveContainer.VectorPayload

open IndexedPolynomial.Description

universe u v w

abbrev DataSort := VectorControl.DataSort
abbrev LengthExpr := VectorControl.LengthExpr

def value (Payload : Type u) : DataSort → Type u
  | .payload => Payload
  | .length => ULift.{u, 0} Nat

def interface (Payload : Type u) : Interface.{u} where
  SortCode := DataSort
  Value := value Payload
  Index := ULift.{u, 0} Unit
  IndexExpr := fun _ => Unit
  evalIndex := fun _ _ => ⟨()⟩

def evalLength (Payload : Type u) : {context : List DataSort} →
    LengthExpr context → Env (value Payload) context → Nat
  | _, .here, environment => environment.1.down
  | _, .there prior, environment => evalLength Payload prior environment.2

def entry (Payload : Type u) : Entry (interface Payload) where
  Output := Nat
  OutputExpr := LengthExpr
  evalOutput := evalLength Payload
  container := IndexedContainer.Examples.vector

def registry (Payload : Type u) : Registry (interface Payload) where
  lookup name := if name = "Vector" then some (entry Payload) else none

def orderedFinitary (Payload : Type u) : (registry Payload).OrderedFinitary where
  containerOrdered := by
    intro name foundEntry found
    by_cases same : name = "Vector"
    · subst name
      simp [registry] at found
      subst foundEntry
      exact IndexedContainer.Examples.vectorOrderedFinitary
    · simp [registry, same] at found

def finitary (Payload : Type u) : (registry Payload).Finitary :=
  (orderedFinitary Payload).toFinitary

def mapValue {A : Type u} {B : Type v} (mapping : A → B) :
    (sort : DataSort) → value A sort → value B sort
  | .payload, item => mapping item
  | .length, length => ⟨length.down⟩

def mapEnv {A : Type u} {B : Type v} (mapping : A → B) :
    {context : List DataSort} → Env (value A) context → Env (value B) context
  | [], _ => PUnit.unit
  | sort :: _, environment =>
      (mapValue mapping sort environment.1, mapEnv mapping environment.2)

@[simp] theorem evalLength_map {A : Type u} {B : Type v} (mapping : A → B)
    {context : List DataSort} (expression : LengthExpr context)
    (environment : Env (value A) context) :
    evalLength B expression (mapEnv mapping environment) =
      evalLength A expression environment := by
  induction expression with
  | here => rfl
  | there prior ih => exact ih environment.2

@[simp] theorem mapValue_id {A : Type u} (sort : DataSort)
    (item : value A sort) : mapValue id sort item = item := by
  cases sort with
  | payload => rfl
  | length => cases item; rfl

@[simp] theorem mapValue_comp {A : Type u} {B : Type v} {C : Type w}
    (first : A → B) (second : B → C) (sort : DataSort)
    (item : value A sort) :
    mapValue second sort (mapValue first sort item) =
      mapValue (second ∘ first) sort item := by
  cases sort <;> rfl

@[simp] theorem mapEnv_id {A : Type u} {context : List DataSort}
    (environment : Env (value A) context) : mapEnv id environment = environment := by
  induction context with
  | nil => cases environment; rfl
  | cons sort rest ih =>
      cases environment with
      | mk item prior => simp only [mapEnv, mapValue_id, ih]; rfl

@[simp] theorem mapEnv_comp {A : Type u} {B : Type v} {C : Type w}
    (first : A → B) (second : B → C) {context : List DataSort}
    (environment : Env (value A) context) :
    mapEnv second (mapEnv first environment) =
      mapEnv (second ∘ first) environment := by
  induction context with
  | nil => rfl
  | cons sort rest ih =>
      cases environment with
      | mk item prior => simp only [mapEnv, mapValue_comp, ih]; rfl

def envEquiv {A : Type u} {B : Type v} (comparison : A ≃ B)
    (context : List DataSort) : Env (value A) context ≃ Env (value B) context where
  toFun := mapEnv comparison
  invFun := mapEnv comparison.symm
  left_inv := by
    intro environment
    rw [mapEnv_comp]
    have inverse : comparison.symm ∘ comparison = id := funext comparison.left_inv
    rw [inverse, mapEnv_id]
  right_inv := by
    intro environment
    rw [mapEnv_comp]
    have inverse : comparison ∘ comparison.symm = id := funext comparison.right_inv
    rw [inverse, mapEnv_id]

def indexEquiv (A : Type u) (B : Type v) :
    (interface A).Index ≃ (interface B).Index where
  toFun := fun index => ⟨index.down⟩
  invFun := fun index => ⟨index.down⟩
  left_inv := fun index => by cases index; rfl
  right_inv := fun index => by cases index; rfl

@[simp] theorem evalIndex_map {A : Type u} {B : Type v} (mapping : A → B)
    {context : List DataSort} (expression : Unit)
    (environment : Env (value A) context) :
    (interface B).evalIndex expression (mapEnv mapping environment) =
      indexEquiv A B ((interface A).evalIndex expression environment) := rfl

/-- The old Boolean interface has unlifted naturals and family indices. -/
def boolValueEquiv : (sort : DataSort) → value Bool sort ≃ VectorControl.value sort
  | .payload => Equiv.refl Bool
  | .length => Equiv.ulift

def boolEnvEquiv : (context : List DataSort) →
    Env (value Bool) context ≃ Env VectorControl.value context
  | [] => Equiv.refl PUnit
  | sort :: rest => Equiv.prodCongr (boolValueEquiv sort) (boolEnvEquiv rest)

def boolIndexEquiv : (interface Bool).Index ≃ VectorControl.interface.Index :=
  Equiv.ulift

@[simp] theorem evalLength_bool {context : List DataSort}
    (expression : LengthExpr context) (environment : Env (value Bool) context) :
    VectorControl.evalLength expression (boolEnvEquiv context environment) =
      evalLength Bool expression environment := by
  induction expression with
  | here => rfl
  | there prior ih => exact ih environment.2

#print axioms evalLength_map
#print axioms mapEnv_id
#print axioms mapEnv_comp
#print axioms envEquiv
#print axioms evalLength_bool

end Mettapedia.TypeTheory.IndexedPositiveContainer.VectorPayload
