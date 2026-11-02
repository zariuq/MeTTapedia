import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotatedMethods

/-!
# Complete source contexts for constructor methods

Every original field is introduced before the queued induction hypotheses.
The context follows the same description and queue as the method type. Its
formation follows by opening the derived dependent products, including all
registered bundle domains.
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

def hypothesesContext {n : Nat} (ambient : CCtx Head n) (pending : List (CTm Head n)) :
    Σ size, CCtx Head size :=
  match pending with
  | [] => ⟨n, ambient⟩
  | first :: rest => hypothesesContext (.snoc ambient first) (rest.map (CTm.rename wk))
termination_by pending.length

theorem hypothesesContext_size {n : Nat} (ambient : CCtx Head n) (pending : List (CTm Head n)) :
    (hypothesesContext ambient pending).1 = n + pending.length := by
  cases pending with
  | nil => simp only [hypothesesContext, List.length_nil, Nat.add_zero]
  | cons first rest =>
      rw [hypothesesContext, hypothesesContext_size]
      simp only [List.length_map, List.length_cons]
      omega
termination_by pending.length
decreasing_by simp_all

theorem hypothesesContext_formed {n : Nat} (ambient : CCtx Head n) (pending : List (CTm Head n))
    (result : CTm Head n) (contextFormed : CCtxFormed P ambient)
    (formed : CIsType P ambient (hypotheses pending result)) :
    CCtxFormed P (hypothesesContext ambient pending).2 := by
  cases pending with
  | nil => rw [hypothesesContext]; exact contextFormed
  | cons first rest =>
      rw [hypothesesContext]
      rw [hypotheses] at formed
      exact hypothesesContext_formed (.snoc ambient first) (rest.map (CTm.rename wk))
        (result.rename wk) (.snoc contextFormed formed.pi_parts.1) formed.pi_parts.2
termination_by pending.length
decreasing_by simp_all

def hypothesisCount {parameters : Nat} : {context : List I.SortCode} → Code I registry parameters context → Nat
  | _, .result _ => 0
  | _, .data _ rest => hypothesisCount rest
  | _, .recursive _ rest => hypothesisCount rest + 1
  | _, .nested _ _ _ _ _ rest => hypothesisCount rest + 1

def methodContext (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head) :
    {parameters : Nat} → {context : List I.SortCode} → Code I registry parameters context →
    {n : Nat} → CCtx Head n → TypeSyntax I Head n → TermEnvironment I Head n context →
      CTm Head n → CTm Head n → List (CTm Head n) → Σ size, CCtx Head size
  | _, _, .result _, _, ambient, _, _, _, _, pending => hypothesesContext ambient pending
  | _, _, .data sort rest, _, ambient, types, environment, motive, constructor, pending =>
      methodContext indexing containers rest (.snoc ambient (types.dataType sort)) types.weaken
        (.var 0, weakenEnvironment environment) (motive.rename wk) (.app (constructor.rename wk) (.var 0))
        (pending.map (CTm.rename wk))
  | _, _, .recursive expression rest, _, ambient, types, environment, motive, constructor, pending =>
      methodContext indexing containers rest
        (.snoc ambient (indexing.familyAt types.family expression environment)) types.weaken
        (weakenEnvironment environment) (motive.rename wk) (.app (constructor.rename wk) (.var 0))
        (pending.map (CTm.rename wk) ++
          [.app (indexing.familyAt (motive.rename wk) expression (weakenEnvironment environment)) (.var 0)])
  | _, _, .nested name entry registered output childIndex rest, _, ambient, types, environment, motive, constructor, pending =>
      methodContext indexing containers rest
        (.snoc ambient (containers.fieldType name entry registered output environment
          (indexing.familyAt types.family childIndex environment))) types.weaken
        (weakenEnvironment environment) (motive.rename wk) (.app (constructor.rename wk) (.var 0))
        (pending.map (CTm.rename wk) ++
          [containers.bundleType name entry registered output (weakenEnvironment environment)
            (indexing.familyAt (types.family.rename wk) childIndex (weakenEnvironment environment))
            (indexing.familyAt (motive.rename wk) childIndex (weakenEnvironment environment)) (.var 0)])

theorem methodContext_size (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {n : Nat} (ambient : CCtx Head n) (types : TypeSyntax I Head n) (environment : TermEnvironment I Head n context)
    (motive constructor : CTm Head n) (pending : List (CTm Head n)) :
    (methodContext indexing containers code ambient types environment motive constructor pending).1 =
      n + fieldCount code + pending.length + hypothesisCount code := by
  induction code generalizing n with
  | result _ => simp only [methodContext, hypothesesContext_size, fieldCount, hypothesisCount, Nat.add_zero]
  | data _ _ previous =>
      simp only [methodContext, previous, fieldCount, hypothesisCount, List.length_map]
      omega
  | recursive _ _ previous =>
      simp only [methodContext, previous, fieldCount, hypothesisCount, List.length_append, List.length_map,
        List.length_cons, List.length_nil]
      omega
  | nested _ _ _ _ _ _ previous =>
      simp only [methodContext, previous, fieldCount, hypothesisCount, List.length_append, List.length_map,
        List.length_cons, List.length_nil]
      omega

theorem methodContext_formedFromBody (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {n : Nat} (ambient : CCtx Head n) (types : TypeSyntax I Head n) (environment : TermEnvironment I Head n context)
    (motive constructor : CTm Head n) (pending : List (CTm Head n)) (contextFormed : CCtxFormed P ambient)
    (formed : CIsType P ambient (methodBody indexing containers code types environment motive constructor pending)) :
    CCtxFormed P (methodContext indexing containers code ambient types environment motive constructor pending).2 := by
  induction code generalizing n with
  | result expression =>
      rw [methodContext]
      rw [methodBody] at formed
      exact hypothesesContext_formed ambient pending _ contextFormed formed
  | data _ _ previous =>
      rw [methodContext]
      rw [methodBody] at formed
      exact previous _ _ _ _ _ _ (.snoc contextFormed formed.pi_parts.1) formed.pi_parts.2
  | recursive _ _ previous =>
      rw [methodContext]
      rw [methodBody] at formed
      exact previous _ _ _ _ _ _ (.snoc contextFormed formed.pi_parts.1) formed.pi_parts.2
  | nested _ _ _ _ _ _ previous =>
      rw [methodContext]
      rw [methodBody] at formed
      exact previous _ _ _ _ _ _ (.snoc contextFormed formed.pi_parts.1) formed.pi_parts.2

theorem methodContext_formed [UniverseLevel.LevelOrder L] (levels : LevelModel R L)
    {n : Nat} {ambient : CCtx Head n} {types : TypeSyntax I Head n}
    {indexing : Indexing I Head} {containers : RegistrySyntax I registry Head}
    {domain : indexing.Domain n} {level resultLevel : Head} {admitted : IndexPredicate I}
    (primitives : MethodPrimitives (P := P) ambient types indexing containers domain level resultLevel admitted)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (accepted : IndicesAdmitted admitted code) {m : Nat} {target : CCtx Head m}
    (formed : CCtxFormed P target) (images : CSub Head n m) (morphism : CSubstMor P ambient target images)
    (environment : TermEnvironment I Head m context)
    (typed : EnvironmentTyped (P := P) target (fun sort => (types.dataType sort).subst images) environment)
    (motive constructor : CTm Head m) (pending : List (CTm Head m))
    (motiveTyped : CTyped P target motive
      (motiveType indexing (types.family.subst images) (indexing.mapDomain (CTm.subst images) domain) resultLevel))
    (constructorTyped : CTyped P target constructor
      (constructorType indexing containers code (types.map (CTm.subst images)) environment))
    (pendingTyped : ∀ type ∈ pending, CIsType P target type) :
    CCtxFormed P (methodContext indexing containers code target (types.map (CTm.subst images))
      environment motive constructor pending).2 :=
  methodContext_formedFromBody indexing containers code _ _ _ _ _ _ formed
    (methodBody_formed levels primitives code accepted images morphism environment typed
      motive constructor pending motiveTyped constructorTyped pendingTyped)

#print axioms methodContext_formed
#print axioms methodContext_size

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated
