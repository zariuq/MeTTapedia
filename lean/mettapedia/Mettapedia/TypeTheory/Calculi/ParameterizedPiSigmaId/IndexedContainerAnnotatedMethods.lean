import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotatedFormation

/-!
# Formation of annotated dependent methods for positive descriptions

The actual motive and constructor are typed inputs. Direct fields contribute
their dependent motive type; registered fields contribute the complete bundle
type through a primitive registered operation. The full generated method is
derived over the original Code, with no whole-method formation premise.
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

def Indexing.mapDomain (indexing : Indexing I Head) {n m : Nat} (mapping : CTm Head n → CTm Head m)
    (domain : indexing.Domain n) : indexing.Domain m :=
  match indexing with
  | .indexed _ => mapping domain
  | .unindexed _ => PUnit.unit

def motiveType (indexing : Indexing I Head) {n : Nat}
    (family : CTm Head n) (domain : indexing.Domain n) (resultLevel : Head) : CTm Head n :=
  match indexing with
  | .indexed _ => .pi domain (.pi (.app (family.rename wk) (.var 0)) (.head resultLevel))
  | .unindexed _ => .pi family (.head resultLevel)

theorem motiveType_weaken (indexing : Indexing I Head) {n : Nat}
    (family : CTm Head n) (domain : indexing.Domain n) (resultLevel : Head) :
    (motiveType indexing family domain resultLevel).rename wk =
      motiveType indexing (family.rename wk) (indexing.mapDomain (CTm.rename wk) domain) resultLevel := by
  cases indexing with
  | unindexed _ => rfl
  | indexed _ =>
      simp only [motiveType, Indexing.mapDomain, CTm.rename, CTm.rename_comp, liftRen, wk, Fin.cases_zero]
      rfl

theorem mappedDomain_weaken (indexing : Indexing I Head) {n m : Nat}
    (domain : indexing.Domain n) (images : CSub Head n m) :
    indexing.mapDomain (CTm.rename wk) (indexing.mapDomain (CTm.subst images) domain) =
      indexing.mapDomain (CTm.subst (fun index => (images index).rename wk)) domain := by
  cases indexing with
  | indexed _ => exact CTm.rename_subst _ _ _
  | unindexed _ => rfl

private theorem substituteVariables {n m : Nat} (rho : Ren n m) :
    CTm.subst (fun index => CTm.var (rho index)) = (CTm.rename rho : CTm Head n → CTm Head m) := by
  funext term
  simpa only [CTm.subst_ids, CTm.ids, CTm.rename] using
    (CTm.rename_subst rho CTm.ids term).symm

theorem Indexing.familyAt_weaken (indexing : Indexing I Head) {context : List I.SortCode} {n : Nat}
    (family : CTm Head n) (expression : I.IndexExpr context) (environment : TermEnvironment I Head n context) :
    (indexing.familyAt family expression environment).rename wk =
      indexing.familyAt (family.rename wk) expression (weakenEnvironment environment) := by
  simpa only [substituteVariables, weakenEnvironment] using
    indexing.familyAt_substitute family expression environment (fun index => .var (wk index))

theorem RegistrySyntax.fieldType_weaken (containers : RegistrySyntax I registry Head)
    {context : List I.SortCode} {n : Nat} name entry registered (output : entry.OutputExpr context)
    (environment : TermEnvironment I Head n context) (element : CTm Head n) :
    (containers.fieldType name entry registered output environment element).rename wk =
      containers.fieldType name entry registered output (weakenEnvironment environment) (element.rename wk) := by
  simpa only [substituteVariables, weakenEnvironment] using
    containers.fieldType_substitute name entry registered output environment element (fun index => .var (wk index))

theorem ConstructorPrimitives.predicateAt_typed {n : Nat} {ambient : CCtx Head n} {types : TypeSyntax I Head n}
    {indexing : Indexing I Head} {containers : RegistrySyntax I registry Head}
    {domain : indexing.Domain n} {level resultLevel : Head} {admitted : IndexPredicate I}
    (primitives : ConstructorPrimitives (P := P) ambient types indexing containers domain level admitted)
    {m : Nat} {target : CCtx Head m} (images : CSub Head n m) (morphism : CSubstMor P ambient target images)
    {context : List I.SortCode} (expression : I.IndexExpr context) (accepted : admitted expression)
    (environment : TermEnvironment I Head m context)
    (typed : EnvironmentTyped (P := P) target (fun sort => (types.dataType sort).subst images) environment)
    (motive : CTm Head m)
    (motiveTyped : CTyped P target motive
      (motiveType indexing (types.family.subst images) (indexing.mapDomain (CTm.subst images) domain) resultLevel)) :
    CTyped P target (indexing.familyAt motive expression environment)
      (.pi (indexing.familyAt (types.family.subst images) expression environment) (.head resultLevel)) := by
  cases indexing with
  | unindexed _ => exact motiveTyped
  | indexed indices =>
      have index := primitives.indices images morphism expression accepted environment typed
      have applied := CDerivable.appElim motiveTyped index
      have cancel : CTm.subst (indices.term expression environment).subst0
          ((types.family.subst images).rename wk) = types.family.subst images :=
        CTm.inst0_rename_wk (indices.term expression environment) (types.family.subst images)
      simpa only [motiveType, Indexing.mapDomain, Indexing.familyAt, CTm.inst0, CTm.subst,
        cancel, CTm.subst0, Fin.cases_zero] using applied

structure MethodPrimitives {n : Nat} (ambient : CCtx Head n) (types : TypeSyntax I Head n)
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (domain : indexing.Domain n) (level resultLevel : Head) (admitted : IndexPredicate I) : Prop
    extends ConstructorPrimitives (P := P) ambient types indexing containers domain level admitted where
  resultUniverse : R.isUniverse resultLevel
  bundle : ∀ {m : Nat} {target : CCtx Head m} (images : CSub Head n m),
    CSubstMor P ambient target images → ∀ {context : List I.SortCode} name entry
      (registered : registry.lookup name = some entry) (output : entry.OutputExpr context)
      (environment : TermEnvironment I Head m context),
      EnvironmentTyped (P := P) target (fun sort => (types.dataType sort).subst images) environment →
      ∀ element predicate field, CTyped P target element (.head level) →
        CTyped P target predicate (.pi element (.head resultLevel)) →
        CTyped P target field (containers.fieldType name entry registered output environment element) →
        CIsType P target (containers.bundleType name entry registered output environment element predicate field)

private theorem type_substitute {n m : Nat} {ambient : CCtx Head n} {target : CCtx Head m}
    {source : CTm Head n} (formed : CIsType P ambient source) (images : CSub Head n m)
    (morphism : CSubstMor P ambient target images) : CIsType P target (source.subst images) := by
  obtain ⟨level, allowed, typed⟩ := formed
  exact ⟨level, allowed, typed.substitute morphism⟩

private theorem mappedTypes_weaken {n m : Nat} (types : TypeSyntax I Head n) (images : CSub Head n m) :
    (types.map (CTm.subst images)).weaken = types.map (CTm.subst (fun index => (images index).rename wk)) := by
  cases types
  simp only [TypeSyntax.weaken, TypeSyntax.map, CTm.rename_subst]

theorem hypotheses_formed [UniverseLevel.LevelOrder L] (levels : LevelModel R L)
    {n : Nat} {ambient : CCtx Head n} (pending : List (CTm Head n)) (result : CTm Head n)
    (inputs : ∀ type ∈ pending, CIsType P ambient type) (output : CIsType P ambient result) :
    CIsType P ambient (hypotheses pending result) := by
  cases pending with
  | nil => simpa only [hypotheses] using output
  | cons first rest =>
      rw [hypotheses]
      apply CIsType.pi levels (inputs first (by simp))
      apply hypotheses_formed levels (rest.map (CTm.rename wk)) (result.rename wk)
      · intro type inside
        obtain ⟨previous, member, rfl⟩ := List.mem_map.mp inside
        exact (inputs previous (List.mem_cons_of_mem first member)).rename (CCtxRen.wk ambient first)
      · exact output.rename (CCtxRen.wk ambient first)
termination_by pending.length
decreasing_by simp_all

private theorem constructor_apply {n : Nat} {ambient : CCtx Head n} {constructor A : CTm Head n} {B : CTm Head (n + 1)}
    (typed : CTyped P ambient constructor (.pi A B)) :
    CTyped P (.snoc ambient A) (.app (constructor.rename wk) (.var 0)) B := by
  have applied := CDerivable.appElim typed.weaken (CDerivable.var (P := P) (Γ := .snoc ambient A) 0)
  simpa only [CTm.rename, CTm.inst0_var_rename_liftRen_wk] using applied

theorem methodBody_formed [UniverseLevel.LevelOrder L] (levels : LevelModel R L)
    {n : Nat} {ambient : CCtx Head n} {types : TypeSyntax I Head n}
    {indexing : Indexing I Head} {containers : RegistrySyntax I registry Head}
    {domain : indexing.Domain n} {level resultLevel : Head} {admitted : IndexPredicate I}
    (primitives : MethodPrimitives (P := P) ambient types indexing containers domain level resultLevel admitted)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (accepted : IndicesAdmitted admitted code) {m : Nat} {target : CCtx Head m}
    (images : CSub Head n m) (morphism : CSubstMor P ambient target images)
    (environment : TermEnvironment I Head m context)
    (typed : EnvironmentTyped (P := P) target (fun sort => (types.dataType sort).subst images) environment)
    (motive constructor : CTm Head m) (pending : List (CTm Head m))
    (motiveTyped : CTyped P target motive
      (motiveType indexing (types.family.subst images) (indexing.mapDomain (CTm.subst images) domain) resultLevel))
    (constructorTyped : CTyped P target constructor (constructorType indexing containers code (types.map (CTm.subst images)) environment))
    (pendingTyped : ∀ type ∈ pending, CIsType P target type) :
    CIsType P target (methodBody indexing containers code (types.map (CTm.subst images)) environment motive constructor pending) := by
  induction code generalizing m with
  | result expression =>
      simp only [constructorType, TypeSyntax.map] at constructorTyped
      rw [methodBody]
      apply hypotheses_formed levels pending
      · exact pendingTyped
      · have predicate := primitives.toConstructorPrimitives.predicateAt_typed images morphism expression accepted environment typed motive motiveTyped
        exact ⟨resultLevel, primitives.resultUniverse, .appElim predicate constructorTyped⟩
  | data sort rest previous =>
      have field := type_substitute (primitives.data sort) images morphism
      simp only [constructorType, TypeSyntax.map] at constructorTyped
      have remaining := constructor_apply constructorTyped
      rw [methodBody]
      apply CIsType.pi levels field
      rw [mappedTypes_weaken]
      apply previous accepted (fun index => (images index).rename wk)
        (by intro index; simpa only [CTm.rename_subst] using (morphism index).weaken) (.var 0, weakenEnvironment environment)
      · constructor
        · simpa only [CCtx.lookup_snoc_zero, CTm.rename_subst] using
            (CDerivable.var (P := P) (Γ := .snoc target ((types.dataType sort).subst images)) (0 : Fin (m + 1)))
        · simpa only [CTm.rename_subst] using typed.weaken ((types.dataType sort).subst images)
      · simpa only [motiveType_weaken, mappedDomain_weaken, CTm.rename_subst] using
          (motiveTyped.weaken (E := (types.dataType sort).subst images))
      · simpa only [TypeSyntax.weaken, TypeSyntax.map, CTm.rename_subst] using remaining
      · intro type inside
        obtain ⟨original, member, rfl⟩ := List.mem_map.mp inside
        exact (pendingTyped original member).rename (CCtxRen.wk _ _)
  | recursive expression rest previous =>
      let fieldType := indexing.familyAt (types.family.subst images) expression environment
      have field := primitives.toConstructorPrimitives.familyAt_typed images morphism expression accepted.1 environment typed
      simp only [constructorType, TypeSyntax.map] at constructorTyped
      have remaining := constructor_apply constructorTyped
      rw [methodBody]
      apply CIsType.pi levels ⟨level, primitives.isUniverse, field⟩
      rw [mappedTypes_weaken]
      apply previous accepted.2 (fun index => (images index).rename wk)
        (by intro index; simpa only [CTm.rename_subst] using (morphism index).weaken) (weakenEnvironment environment)
      · simpa only [CTm.rename_subst] using typed.weaken fieldType
      · simpa only [motiveType_weaken, mappedDomain_weaken, CTm.rename_subst] using (motiveTyped.weaken (E := fieldType))
      · simpa only [TypeSyntax.weaken, TypeSyntax.map, CTm.rename_subst] using remaining
      · intro type inside
        rcases List.mem_append.mp inside with old | fresh
        · obtain ⟨original, member, rfl⟩ := List.mem_map.mp old
          exact (pendingTyped original member).rename (CCtxRen.wk _ _)
        · simp only [List.mem_singleton] at fresh
          subst type
          have raised : EnvironmentTyped (P := P) (.snoc target fieldType)
              (fun sort => (types.dataType sort).subst (fun index => (images index).rename wk))
              (weakenEnvironment environment) := by simpa only [CTm.rename_subst] using typed.weaken fieldType
          have predicate := primitives.toConstructorPrimitives.predicateAt_typed
            (fun index => (images index).rename wk)
            (by intro index; simpa only [CTm.rename_subst] using (morphism index).weaken)
            expression accepted.1 (weakenEnvironment environment) raised (motive.rename wk)
            (by simpa only [motiveType_weaken, mappedDomain_weaken, CTm.rename_subst] using (motiveTyped.weaken (E := fieldType)))
          have child : CTyped P (.snoc target fieldType) (.var 0)
              (indexing.familyAt (types.family.subst (fun index => (images index).rename wk)) expression (weakenEnvironment environment)) := by
            simpa only [fieldType, CCtx.lookup_snoc_zero, Indexing.familyAt_weaken, CTm.rename_subst] using
              (CDerivable.var (P := P) (Γ := .snoc target fieldType) 0)
          exact ⟨resultLevel, primitives.resultUniverse, .appElim predicate child⟩
  | nested name entry registered output childIndex rest previous =>
      have element := primitives.toConstructorPrimitives.familyAt_typed images morphism childIndex accepted.1 environment typed
      let fieldType := containers.fieldType name entry registered output environment (indexing.familyAt (types.family.subst images) childIndex environment)
      have field := primitives.container images morphism name entry registered output environment typed _ element
      simp only [constructorType, TypeSyntax.map] at constructorTyped
      have remaining := constructor_apply constructorTyped
      rw [methodBody]
      apply CIsType.pi levels field
      rw [mappedTypes_weaken]
      apply previous accepted.2 (fun index => (images index).rename wk)
        (by intro index; simpa only [CTm.rename_subst] using (morphism index).weaken) (weakenEnvironment environment)
      · simpa only [CTm.rename_subst] using typed.weaken fieldType
      · simpa only [motiveType_weaken, mappedDomain_weaken, CTm.rename_subst] using (motiveTyped.weaken (E := fieldType))
      · simpa only [TypeSyntax.weaken, TypeSyntax.map, CTm.rename_subst] using remaining
      · intro type inside
        rcases List.mem_append.mp inside with old | fresh
        · obtain ⟨original, member, rfl⟩ := List.mem_map.mp old
          exact (pendingTyped original member).rename (CCtxRen.wk _ _)
        · simp only [List.mem_singleton] at fresh
          subst type
          have raised : EnvironmentTyped (P := P) (.snoc target fieldType)
              (fun sort => (types.dataType sort).subst (fun index => (images index).rename wk))
              (weakenEnvironment environment) := by simpa only [CTm.rename_subst] using typed.weaken fieldType
          apply primitives.bundle (fun index => (images index).rename wk)
            (by intro index; simpa only [CTm.rename_subst] using (morphism index).weaken)
            name entry registered output (weakenEnvironment environment) raised
          · simpa only [TypeSyntax.map, CTm.rename_subst] using primitives.toConstructorPrimitives.familyAt_typed
              (fun index => (images index).rename wk)
              (by intro index; simpa only [CTm.rename_subst] using (morphism index).weaken)
              childIndex accepted.1 (weakenEnvironment environment) raised
          · simpa only [TypeSyntax.map, CTm.rename_subst] using primitives.toConstructorPrimitives.predicateAt_typed
              (fun index => (images index).rename wk)
              (by intro index; simpa only [CTm.rename_subst] using (morphism index).weaken)
              childIndex accepted.1 (weakenEnvironment environment) raised (motive.rename wk)
              (by simpa only [motiveType_weaken, mappedDomain_weaken, CTm.rename_subst] using (motiveTyped.weaken (E := fieldType)))
          · simpa only [fieldType, CCtx.lookup_snoc_zero, RegistrySyntax.fieldType_weaken,
              Indexing.familyAt_weaken, TypeSyntax.map, CTm.rename_subst] using
              (CDerivable.var (P := P) (Γ := .snoc target fieldType) 0)

#print axioms methodBody_formed

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated
