import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotatedSyntax
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.TelescopeAbstractions

/-!
# Annotated constructor formation from primitive declaration contracts

Only data types, the recursive family, admitted source index expressions
and registered field-type operations are primitive inputs. The whole
constructor type is derived by recursion over its original description.
The level model supplies product joins, allowing distinct data universes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Presentation TypedEquality.Annotated
open TypedEquality.Normalization (LevelModel)

universe u
variable {I : Interface.{u}} {registry : Registry I} {Head L : Type}
    {R : Rules Head} {P : ChurchRules R}

def EnvironmentTyped {SortCode : Type} {n : Nat} (ambient : CCtx Head n) (dataTypes : SortCode → CTm Head n) :
    {context : List SortCode} → Env (fun _ => CTm Head n) context → Prop
  | [], _ => True
  | sort :: _, environment => CTyped P ambient environment.1 (dataTypes sort) ∧ EnvironmentTyped ambient dataTypes environment.2

theorem EnvironmentTyped.weaken {SortCode : Type} {n : Nat} {ambient : CCtx Head n} {dataTypes : SortCode → CTm Head n}
    {context : List SortCode} {environment : Env (fun _ => CTm Head n) context}
    (typed : EnvironmentTyped (P := P) ambient dataTypes environment) (domain : CTm Head n) :
    EnvironmentTyped (P := P) (.snoc ambient domain) (fun sort => (dataTypes sort).rename wk) (weakenEnvironment environment) := by
  induction context with
  | nil => trivial
  | cons _ _ previous => exact ⟨typed.1.weaken, previous typed.2⟩

def Indexing.Domain (indexing : Indexing I Head) (n : Nat) : Type :=
  match indexing with
  | .indexed _ => CTm Head n
  | .unindexed _ => PUnit

def Indexing.familyKind (indexing : Indexing I Head) {n : Nat} (domain : indexing.Domain n) (level : Head) : CTm Head n :=
  match indexing with
  | .indexed _ => .pi domain (.head level)
  | .unindexed _ => .head level

abbrev IndexPredicate (I : Interface.{u}) := {context : List I.SortCode} → I.IndexExpr context → Prop

def IndicesAdmitted (admitted : IndexPredicate I) {parameters : Nat} :
    {context : List I.SortCode} → Code I registry parameters context → Prop
  | _, .result expression => admitted expression
  | _, .data _ rest => IndicesAdmitted admitted rest
  | _, .recursive expression rest => admitted expression ∧ IndicesAdmitted admitted rest
  | _, .nested _ _ _ _ expression rest => admitted expression ∧ IndicesAdmitted admitted rest

def IndexTypingOn (admitted : IndexPredicate I) {n : Nat} (ambient : CCtx Head n)
    (types : TypeSyntax I Head n) (indexing : Indexing I Head) (domain : indexing.Domain n) : Prop :=
  match indexing with
  | .unindexed _ => True
  | .indexed indices => ∀ {m : Nat} {target : CCtx Head m} (images : CSub Head n m),
      CSubstMor P ambient target images → ∀ {context : List I.SortCode} (expression : I.IndexExpr context),
      admitted expression → ∀ (environment : TermEnvironment I Head m context),
      EnvironmentTyped (P := P) target (fun sort => (types.dataType sort).subst images) environment →
        CTyped P target (indices.term expression environment) (domain.subst images)

structure ConstructorPrimitives {n : Nat} (ambient : CCtx Head n) (types : TypeSyntax I Head n)
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (domain : indexing.Domain n) (level : Head) (admitted : IndexPredicate I) : Prop where
  isUniverse : R.isUniverse level
  data : ∀ sort, CIsType P ambient (types.dataType sort)
  family : CTyped P ambient types.family (indexing.familyKind domain level)
  indices : IndexTypingOn (P := P) admitted ambient types indexing domain
  container : ∀ {m : Nat} {target : CCtx Head m} (images : CSub Head n m),
    CSubstMor P ambient target images → ∀ {context : List I.SortCode} name entry
      (registered : registry.lookup name = some entry) (output : entry.OutputExpr context)
      (environment : TermEnvironment I Head m context),
      EnvironmentTyped (P := P) target (fun sort => (types.dataType sort).subst images) environment →
      ∀ element, CTyped P target element (.head level) →
        CIsType P target (containers.fieldType name entry registered output environment element)

private theorem type_substitute {n m : Nat} {ambient : CCtx Head n} {target : CCtx Head m}
    {source : CTm Head n} (formed : CIsType P ambient source) (images : CSub Head n m)
    (morphism : CSubstMor P ambient target images) : CIsType P target (source.subst images) := by
  obtain ⟨level, allowed, typed⟩ := formed
  exact ⟨level, allowed, typed.substitute morphism⟩

theorem ConstructorPrimitives.familyAt_typed {n : Nat} {ambient : CCtx Head n} {types : TypeSyntax I Head n}
    {indexing : Indexing I Head} {containers : RegistrySyntax I registry Head}
    {domain : indexing.Domain n} {level : Head} {admitted : IndexPredicate I}
    (primitives : ConstructorPrimitives (P := P) ambient types indexing containers domain level admitted)
    {m : Nat} {target : CCtx Head m} (images : CSub Head n m) (morphism : CSubstMor P ambient target images)
    {context : List I.SortCode} (expression : I.IndexExpr context) (accepted : admitted expression)
    (environment : TermEnvironment I Head m context)
    (typed : EnvironmentTyped (P := P) target (fun sort => (types.dataType sort).subst images) environment) :
    CTyped P target (indexing.familyAt (types.family.subst images) expression environment) (.head level) := by
  cases indexing with
  | unindexed _ => exact primitives.family.substitute morphism
  | indexed indices =>
      have family := primitives.family.substitute morphism
      have argument := primitives.indices images morphism expression accepted environment typed
      exact CDerivable.appElim family argument

private theorem mappedTypes_weaken {n m : Nat} (types : TypeSyntax I Head n) (images : CSub Head n m) :
    (types.map (CTm.subst images)).weaken = types.map (CTm.subst (fun index => (images index).rename wk)) := by
  cases types
  simp only [TypeSyntax.weaken, TypeSyntax.map, CTm.rename_subst]

theorem constructorType_formed [UniverseLevel.LevelOrder L] (levels : LevelModel R L)
    {n : Nat} {ambient : CCtx Head n} {types : TypeSyntax I Head n}
    {indexing : Indexing I Head} {containers : RegistrySyntax I registry Head}
    {domain : indexing.Domain n} {level : Head} {admitted : IndexPredicate I}
    (primitives : ConstructorPrimitives (P := P) ambient types indexing containers domain level admitted)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (accepted : IndicesAdmitted admitted code) {m : Nat} {target : CCtx Head m}
    (images : CSub Head n m) (morphism : CSubstMor P ambient target images)
    (environment : TermEnvironment I Head m context)
    (typed : EnvironmentTyped (P := P) target (fun sort => (types.dataType sort).subst images) environment) :
    CIsType P target (constructorType indexing containers code (types.map (CTm.subst images)) environment) := by
  induction code generalizing m with
  | result expression =>
      simpa only [constructorType, TypeSyntax.map] using
        (show CIsType P target (indexing.familyAt (types.family.subst images) expression environment) from
          ⟨level, primitives.isUniverse, primitives.familyAt_typed images morphism expression accepted environment typed⟩)
  | data sort rest previous =>
      have field := type_substitute (primitives.data sort) images morphism
      rw [constructorType]
      apply CIsType.pi levels field
      rw [mappedTypes_weaken]
      apply previous accepted (fun index => (images index).rename wk)
        (by intro index; simpa only [CTm.rename_subst] using (morphism index).weaken)
        (.var 0, weakenEnvironment environment)
      constructor
      · simpa only [CCtx.lookup_snoc_zero, CTm.rename_subst] using
          (CDerivable.var (P := P) (Γ := .snoc target ((types.dataType sort).subst images)) (0 : Fin (m + 1)))
      · simpa only [CTm.rename_subst] using typed.weaken ((types.dataType sort).subst images)
  | recursive expression rest previous =>
      have field := primitives.familyAt_typed images morphism expression accepted.1 environment typed
      rw [constructorType]
      apply CIsType.pi levels ⟨level, primitives.isUniverse, field⟩
      rw [mappedTypes_weaken]
      apply previous accepted.2 (fun index => (images index).rename wk)
        (by intro index; simpa only [CTm.rename_subst] using (morphism index).weaken) (weakenEnvironment environment)
      simpa only [CTm.rename_subst] using typed.weaken (indexing.familyAt (types.family.subst images) expression environment)
  | nested name entry registered output childIndex rest previous =>
      have element := primitives.familyAt_typed images morphism childIndex accepted.1 environment typed
      have field := primitives.container images morphism name entry registered output environment typed _ element
      rw [constructorType]
      apply CIsType.pi levels field
      rw [mappedTypes_weaken]
      apply previous accepted.2 (fun index => (images index).rename wk)
        (by intro index; simpa only [CTm.rename_subst] using (morphism index).weaken) (weakenEnvironment environment)
      simpa only [CTm.rename_subst] using typed.weaken
        (containers.fieldType name entry registered output environment (indexing.familyAt (types.family.subst images) childIndex environment))

#print axioms constructorType_formed

theorem fieldContext_formed (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {n : Nat} (ambient : CCtx Head n) (types : TypeSyntax I Head n) (environment : TermEnvironment I Head n context)
    (formed : CCtxFormed P ambient) (constructorFormed : CIsType P ambient (constructorType indexing containers code types environment)) :
    CCtxFormed P (fieldContext indexing containers code ambient types environment).2 := by
  induction code generalizing n with
  | result _ => rw [fieldContext]; exact formed
  | data _ _ previous =>
      rw [constructorType] at constructorFormed
      rw [fieldContext]
      exact previous _ _ _ (.snoc formed constructorFormed.pi_parts.1) constructorFormed.pi_parts.2
  | recursive _ _ previous =>
      rw [constructorType] at constructorFormed
      rw [fieldContext]
      exact previous _ _ _ (.snoc formed constructorFormed.pi_parts.1) constructorFormed.pi_parts.2
  | nested _ _ _ _ _ _ previous =>
      rw [constructorType] at constructorFormed
      rw [fieldContext]
      exact previous _ _ _ (.snoc formed constructorFormed.pi_parts.1) constructorFormed.pi_parts.2

theorem constructorContext_formed [UniverseLevel.LevelOrder L] (levels : LevelModel R L)
    {n : Nat} {ambient : CCtx Head n} {types : TypeSyntax I Head n}
    {indexing : Indexing I Head} {containers : RegistrySyntax I registry Head}
    {domain : indexing.Domain n} {level : Head} {admitted : IndexPredicate I}
    (primitives : ConstructorPrimitives (P := P) ambient types indexing containers domain level admitted)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (accepted : IndicesAdmitted admitted code) {m : Nat} {target : CCtx Head m}
    (formed : CCtxFormed P target) (images : CSub Head n m) (morphism : CSubstMor P ambient target images)
    (environment : TermEnvironment I Head m context)
    (typed : EnvironmentTyped (P := P) target (fun sort => (types.dataType sort).subst images) environment) :
    CCtxFormed P (fieldContext indexing containers code target (types.map (CTm.subst images)) environment).2 :=
  fieldContext_formed indexing containers code target (types.map (CTm.subst images)) environment formed
    (constructorType_formed levels primitives code accepted images morphism environment typed)

#print axioms constructorContext_formed

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated
