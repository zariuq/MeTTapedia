import Mettapedia.TypeTheory.IndexedPositiveContainer
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Erasure

/-!
# Annotated source types for indexed positive descriptions

The existing description supplies the original data, recursive and registered
fields. Source binders retain their dependent annotations. Index syntax and
registered field/bundle syntax have their own scoped substitution laws;
constructor and method generation follow the description's actual order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Presentation TypedEquality.Annotated

universe u
variable {I : Interface.{u}} {registry : Registry I} {Head : Type}

abbrev TermEnvironment (I : Interface.{u}) (Head : Type) (n : Nat) (context : List I.SortCode) :=
  Env (fun _ => CTm Head n) context

def mapEnvironment {SortCode : Type} {n m : Nat} (mapping : CTm Head n → CTm Head m) :
    {context : List SortCode} → Env (fun _ => CTm Head n) context → Env (fun _ => CTm Head m) context
  | [], _ => PUnit.unit
  | _ :: _, environment => (mapping environment.1, mapEnvironment mapping environment.2)

def weakenEnvironment {SortCode : Type} {n : Nat} {context : List SortCode} (environment : Env (fun _ => CTm Head n) context) :
    Env (fun _ => CTm Head (n + 1)) context := mapEnvironment (CTm.rename wk) environment

theorem mapEnvironment_comp {SortCode : Type} {n m k : Nat} (first : CTm Head n → CTm Head m) (second : CTm Head m → CTm Head k)
    {context : List SortCode} (environment : Env (fun _ => CTm Head n) context) :
    mapEnvironment second (mapEnvironment first environment) = mapEnvironment (fun term => second (first term)) environment := by
  induction context with
  | nil => rfl
  | cons _ _ previous => exact congrArg (Prod.mk _) (previous environment.2)

theorem weakenEnvironment_substitute {SortCode : Type} {n m : Nat} (images : CSub Head n m)
    {context : List SortCode} (environment : Env (fun _ => CTm Head n) context) :
    mapEnvironment (CTm.subst (CTm.liftSub images)) (weakenEnvironment environment) =
      weakenEnvironment (mapEnvironment (CTm.subst images) environment) := by
  induction context with
  | nil => rfl
  | cons _ _ previous =>
      simpa only [weakenEnvironment, mapEnvironment, CTm.subst_liftSub_wk] using
        congrArg (Prod.mk (CTm.rename wk (environment.1.subst images))) (previous environment.2)

structure IndexSyntax (I : Interface.{u}) (Head : Type) where
  term : {context : List I.SortCode} → {n : Nat} → I.IndexExpr context →
    TermEnvironment I Head n context → CTm Head n
  substitute : ∀ {context n m} (expression : I.IndexExpr context)
    (environment : TermEnvironment I Head n context) (images : CSub Head n m),
    (term expression environment).subst images = term expression (mapEnvironment (CTm.subst images) environment)

inductive Indexing (I : Interface.{u}) (Head : Type) where
  | indexed (indices : IndexSyntax I Head)
  | unindexed (unique : Subsingleton I.Index)

def Indexing.familyAt (indexing : Indexing I Head) {context : List I.SortCode} {n : Nat}
    (family : CTm Head n) (expression : I.IndexExpr context) (environment : TermEnvironment I Head n context) : CTm Head n :=
  match indexing with
  | .indexed indices => .app family (indices.term expression environment)
  | .unindexed _ => family

theorem Indexing.familyAt_substitute (indexing : Indexing I Head) {context : List I.SortCode} {n m : Nat}
    (family : CTm Head n) (expression : I.IndexExpr context) (environment : TermEnvironment I Head n context)
    (images : CSub Head n m) :
    (indexing.familyAt family expression environment).subst images =
      indexing.familyAt (family.subst images) expression (mapEnvironment (CTm.subst images) environment) := by
  cases indexing with
  | indexed indices => simp only [familyAt, CTm.subst, indices.substitute]
  | unindexed _ => rfl

structure RegistrySyntax (I : Interface.{u}) (registry : Registry I) (Head : Type) where
  fieldType : ∀ {context : List I.SortCode} {n : Nat} (name : String) (entry : Entry I),
    registry.lookup name = some entry → entry.OutputExpr context → TermEnvironment I Head n context → CTm Head n → CTm Head n
  bundleType : ∀ {context : List I.SortCode} {n : Nat} (name : String) (entry : Entry I),
    registry.lookup name = some entry → entry.OutputExpr context → TermEnvironment I Head n context →
      CTm Head n → CTm Head n → CTm Head n → CTm Head n
  fieldType_substitute : ∀ {context n m} name entry registered (output : entry.OutputExpr context)
    (environment : TermEnvironment I Head n context) (element : CTm Head n) (images : CSub Head n m),
    (fieldType name entry registered output environment element).subst images =
      fieldType name entry registered output (mapEnvironment (CTm.subst images) environment) (element.subst images)
  bundleType_substitute : ∀ {context n m} name entry registered (output : entry.OutputExpr context)
    (environment : TermEnvironment I Head n context) (element predicate field : CTm Head n) (images : CSub Head n m),
    (bundleType name entry registered output environment element predicate field).subst images =
      bundleType name entry registered output (mapEnvironment (CTm.subst images) environment)
        (element.subst images) (predicate.subst images) (field.subst images)

structure TypeSyntax (I : Interface.{u}) (Head : Type) (n : Nat) where
  dataType : I.SortCode → CTm Head n
  family : CTm Head n
  constructor : String → CTm Head n

def TypeSyntax.map {n m : Nat} (mapping : CTm Head n → CTm Head m) (types : TypeSyntax I Head n) : TypeSyntax I Head m :=
  ⟨fun sort => mapping (types.dataType sort), mapping types.family, fun name => mapping (types.constructor name)⟩

def TypeSyntax.weaken {n : Nat} (types : TypeSyntax I Head n) : TypeSyntax I Head (n + 1) := types.map (CTm.rename wk)

theorem TypeSyntax.weaken_substitute {n m : Nat} (images : CSub Head n m) (types : TypeSyntax I Head n) :
    types.weaken.map (CTm.subst (CTm.liftSub images)) = (types.map (CTm.subst images)).weaken := by
  cases types
  simp only [weaken, map, CTm.subst_liftSub_wk]

def constructorType (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head) :
    {parameters : Nat} → {context : List I.SortCode} → Code I registry parameters context →
    {n : Nat} → TypeSyntax I Head n → TermEnvironment I Head n context → CTm Head n
  | _, _, .result expression, _, types, environment => indexing.familyAt types.family expression environment
  | _, _, .data sort rest, _, types, environment =>
      .pi (types.dataType sort) (constructorType indexing containers rest types.weaken (.var 0, weakenEnvironment environment))
  | _, _, .recursive expression rest, _, types, environment =>
      .pi (indexing.familyAt types.family expression environment)
        (constructorType indexing containers rest types.weaken (weakenEnvironment environment))
  | _, _, .nested name entry registered output childIndex rest, _, types, environment =>
      .pi (containers.fieldType name entry registered output environment (indexing.familyAt types.family childIndex environment))
        (constructorType indexing containers rest types.weaken (weakenEnvironment environment))

def fieldCount {parameters : Nat} : {context : List I.SortCode} → Code I registry parameters context → Nat
  | _, .result _ => 0
  | _, .data _ rest => fieldCount rest + 1
  | _, .recursive _ rest => fieldCount rest + 1
  | _, .nested _ _ _ _ _ rest => fieldCount rest + 1

def fieldContext (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head) :
    {parameters : Nat} → {context : List I.SortCode} → Code I registry parameters context →
    {n : Nat} → CCtx Head n → TypeSyntax I Head n → TermEnvironment I Head n context → (Σ size, CCtx Head size)
  | _, _, .result _, n, ambient, _, _ => ⟨n, ambient⟩
  | _, _, .data sort rest, _, ambient, types, environment =>
      fieldContext indexing containers rest (.snoc ambient (types.dataType sort)) types.weaken (.var 0, weakenEnvironment environment)
  | _, _, .recursive expression rest, _, ambient, types, environment =>
      fieldContext indexing containers rest (.snoc ambient (indexing.familyAt types.family expression environment))
        types.weaken (weakenEnvironment environment)
  | _, _, .nested name entry registered output childIndex rest, _, ambient, types, environment =>
      fieldContext indexing containers rest
        (.snoc ambient (containers.fieldType name entry registered output environment (indexing.familyAt types.family childIndex environment)))
        types.weaken (weakenEnvironment environment)

theorem fieldContext_size (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {n : Nat} (ambient : CCtx Head n) (types : TypeSyntax I Head n) (environment : TermEnvironment I Head n context) :
    (fieldContext indexing containers code ambient types environment).1 = n + fieldCount code := by
  induction code generalizing n with
  | result _ => simp only [fieldContext, fieldCount, Nat.add_zero]
  | data _ _ previous => simp only [fieldContext, previous, fieldCount]; omega
  | recursive _ _ previous => simp only [fieldContext, previous, fieldCount]; omega
  | nested _ _ _ _ _ _ previous => simp only [fieldContext, previous, fieldCount]; omega

theorem constructorType_substitute (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {n m : Nat} (types : TypeSyntax I Head n) (environment : TermEnvironment I Head n context) (images : CSub Head n m) :
    (constructorType indexing containers code types environment).subst images =
      constructorType indexing containers code (types.map (CTm.subst images)) (mapEnvironment (CTm.subst images) environment) := by
  induction code generalizing n m with
  | result expression =>
      simpa only [constructorType, TypeSyntax.map] using
        indexing.familyAt_substitute types.family expression environment images
  | data _ rest previous =>
      simp only [constructorType, CTm.subst, TypeSyntax.map]
      congr 1
      simpa only [mapEnvironment, CTm.subst, CTm.liftSub, Fin.cases_zero, weakenEnvironment_substitute,
        TypeSyntax.weaken, TypeSyntax.map, CTm.subst_liftSub_wk] using
        previous types.weaken (.var 0, weakenEnvironment environment) (CTm.liftSub images)
  | recursive _ rest previous =>
      simp only [constructorType, CTm.subst, indexing.familyAt_substitute, TypeSyntax.map]
      congr 1
      simpa only [weakenEnvironment_substitute, TypeSyntax.weaken, TypeSyntax.map, CTm.subst_liftSub_wk] using
        previous types.weaken (weakenEnvironment environment) (CTm.liftSub images)
  | nested _ _ _ _ _ rest previous =>
      simp only [constructorType, CTm.subst, containers.fieldType_substitute, indexing.familyAt_substitute, TypeSyntax.map]
      congr 1
      simpa only [weakenEnvironment_substitute, TypeSyntax.weaken, TypeSyntax.map, CTm.subst_liftSub_wk] using
        previous types.weaken (weakenEnvironment environment) (CTm.liftSub images)

def hypotheses {n : Nat} : List (CTm Head n) → CTm Head n → CTm Head n
  | [], result => result
  | first :: rest, result => .pi first (hypotheses (rest.map (CTm.rename wk)) (result.rename wk))
termination_by pending _ => pending.length

def methodBody (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head) :
    {parameters : Nat} → {context : List I.SortCode} → Code I registry parameters context →
    {n : Nat} → TypeSyntax I Head n → TermEnvironment I Head n context → CTm Head n → CTm Head n → List (CTm Head n) → CTm Head n
  | _, _, .result expression, _, _, environment, motive, constructor, pending =>
      hypotheses pending (.app (indexing.familyAt motive expression environment) constructor)
  | _, _, .data sort rest, _, types, environment, motive, constructor, pending =>
      .pi (types.dataType sort) (methodBody indexing containers rest types.weaken (.var 0, weakenEnvironment environment)
        (motive.rename wk) (.app (constructor.rename wk) (.var 0)) (pending.map (CTm.rename wk)))
  | _, _, .recursive expression rest, _, types, environment, motive, constructor, pending =>
      .pi (indexing.familyAt types.family expression environment)
        (methodBody indexing containers rest types.weaken (weakenEnvironment environment)
          (motive.rename wk) (.app (constructor.rename wk) (.var 0))
          (pending.map (CTm.rename wk) ++ [ .app (indexing.familyAt (motive.rename wk) expression (weakenEnvironment environment)) (.var 0)]))
  | _, _, .nested name entry registered output childIndex rest, _, types, environment, motive, constructor, pending =>
      .pi (containers.fieldType name entry registered output environment (indexing.familyAt types.family childIndex environment))
        (methodBody indexing containers rest types.weaken (weakenEnvironment environment)
          (motive.rename wk) (.app (constructor.rename wk) (.var 0))
          (pending.map (CTm.rename wk) ++ [containers.bundleType name entry registered output (weakenEnvironment environment)
            (indexing.familyAt (types.family.rename wk) childIndex (weakenEnvironment environment))
            (indexing.familyAt (motive.rename wk) childIndex (weakenEnvironment environment)) (.var 0)]))

#print axioms constructorType_substitute

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated
