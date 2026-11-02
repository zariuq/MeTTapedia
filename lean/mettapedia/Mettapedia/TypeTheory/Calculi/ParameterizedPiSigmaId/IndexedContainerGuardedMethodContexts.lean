import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotatedMethodContexts
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerGuardedContexts

/-!
# Reading every field and queued induction hypothesis

A carrier profile fixes the original field carriers and the carriers of direct
and registered hypotheses. The source method context comes from the actual
description. The existing reader checks its complete telescope; it may refuse
a profile that cannot interpret a generated domain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated

open Mettapedia.Logic
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open TypedEquality.Normalization (LevelModel)

universe u v w
variable {I : Interface.{u}} {registry : Registry I} {Head L : Type}
    {Base : Type v} {Const : HOL.Ty Base → Type w}
    {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}

structure MethodCarriers (I : Interface.{u}) (registry : Registry I) (Base : Type v)
    extends FieldCarriers I registry Base where
  directHypothesis : HOL.Ty Base
  nestedHypothesis : (name : String) → (entry : Entry I) → registry.lookup name = some entry → HOL.Ty Base

def MethodCarriers.context (carriers : MethodCarriers I registry Base) {parameters : Nat} :
    {context : List I.SortCode} → Code I registry parameters context → HOL.Ctx Base → HOL.Ctx Base → HOL.Ctx Base
  | _, .result _, ambient, pending => pending.reverse ++ ambient
  | _, .data sort rest, ambient, pending => carriers.context rest (carriers.data sort :: ambient) pending
  | _, .recursive _ rest, ambient, pending =>
      carriers.context rest (carriers.recursive :: ambient) (pending ++ [carriers.directHypothesis])
  | _, .nested name entry registered _ _ rest, ambient, pending =>
      carriers.context rest (carriers.nested name entry registered :: ambient)
        (pending ++ [carriers.nestedHypothesis name entry registered])

theorem MethodCarriers.context_length (carriers : MethodCarriers I registry Base) {parameters : Nat}
    {context : List I.SortCode} (code : Code I registry parameters context) (ambient pending : HOL.Ctx Base) :
    (carriers.context code ambient pending).length =
      ambient.length + fieldCount code + pending.length + hypothesisCount code := by
  induction code generalizing ambient pending with
  | result _ => simp only [MethodCarriers.context, fieldCount, hypothesisCount,
      List.length_append, List.length_reverse, Nat.add_zero]; omega
  | data _ _ previous =>
      simp only [MethodCarriers.context, previous, fieldCount, hypothesisCount, List.length_cons]
      omega
  | recursive _ _ previous =>
      simp only [MethodCarriers.context, previous, fieldCount, hypothesisCount, List.length_cons,
        List.length_append, List.length_nil]
      omega
  | nested _ _ _ _ _ _ previous =>
      simp only [MethodCarriers.context, previous, fieldCount, hypothesisCount, List.length_cons,
        List.length_append, List.length_nil]
      omega

def generatedMethodSource (carriers : MethodCarriers I registry Base) (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {Γ : HOL.Ctx Base} (ambient : CCtx Head Γ.length)
    (types : TypeSyntax I Head Γ.length) (environment : TermEnvironment I Head Γ.length context)
    (motive constructor : CTm Head Γ.length) (pending : List (CTm Head Γ.length))
    (pendingCarriers : HOL.Ctx Base) (sameLength : pending.length = pendingCarriers.length) :
    CCtx Head (carriers.context code Γ pendingCarriers).length :=
  let same := (methodContext_size indexing containers code ambient types environment motive constructor pending).trans
    ((congrArg (fun length => Γ.length + fieldCount code + length + hypothesisCount code) sameLength).trans
      (carriers.context_length code Γ pendingCarriers).symm)
  same ▸ (methodContext indexing containers code ambient types environment motive constructor pending).2

private theorem castContext_formed {n m : Nat} (same : n = m) (context : CCtx Head n)
    (formed : CCtxFormed P context) : CCtxFormed P (same ▸ context) := by
  cases same
  exact formed

theorem generatedMethodSource_formed [UniverseLevel.LevelOrder L] (levels : LevelModel R L)
    (carriers : MethodCarriers I registry Base) {n : Nat} {ambient : CCtx Head n} {types : TypeSyntax I Head n}
    {indexing : Indexing I Head} {containers : RegistrySyntax I registry Head}
    {domain : indexing.Domain n} {level resultLevel : Head} {admitted : IndexPredicate I}
    (primitives : MethodPrimitives (P := P) ambient types indexing containers domain level resultLevel admitted)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (accepted : IndicesAdmitted admitted code) {Γ : HOL.Ctx Base} (target : CCtx Head Γ.length)
    (formed : CCtxFormed P target) (images : CSub Head n Γ.length) (morphism : CSubstMor P ambient target images)
    (environment : TermEnvironment I Head Γ.length context)
    (typed : EnvironmentTyped (P := P) target (fun sort => (types.dataType sort).subst images) environment)
    (motive constructor : CTm Head Γ.length) (pending : List (CTm Head Γ.length))
    (motiveTyped : CTyped P target motive
      (motiveType indexing (types.family.subst images) (indexing.mapDomain (CTm.subst images) domain) resultLevel))
    (constructorTyped : CTyped P target constructor
      (constructorType indexing containers code (types.map (CTm.subst images)) environment))
    (pendingTyped : ∀ type ∈ pending, CIsType P target type)
    (pendingCarriers : HOL.Ctx Base) (sameLength : pending.length = pendingCarriers.length) :
    CCtxFormed P (generatedMethodSource carriers indexing containers code target (types.map (CTm.subst images))
      environment motive constructor pending pendingCarriers sameLength) :=
  castContext_formed _ _ (methodContext_formed levels primitives code accepted formed images morphism environment typed
    motive constructor pending motiveTyped constructorTyped pendingTyped)

/-- Compute the predicate telescope of a generated, independently formed method
context. Source formation and predicate readability are separate evidence. -/
def readMethodContext? [DecidableEq Base] (carriers : MethodCarriers I registry Base)
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {Γ : HOL.Ctx Base} (ambient : CCtx Head Γ.length) (types : TypeSyntax I Head Γ.length)
    (environment : TermEnvironment I Head Γ.length context) (motive constructor : CTm Head Γ.length)
    (pending : List (CTm Head Γ.length)) (pendingCarriers : HOL.Ctx Base)
    (sameLength : pending.length = pendingCarriers.length)
    (formed : CCtxFormed P (generatedMethodSource carriers indexing containers code ambient types environment
      motive constructor pending pendingCarriers sameLength)) :
    Option (GuardedContext P lex (carriers.context code Γ pendingCarriers)) :=
  let source := generatedMethodSource carriers indexing containers code ambient types environment
    motive constructor pending pendingCarriers sameLength
  (Reader.readContext? lex (carriers.context code Γ pendingCarriers) source).map fun reading =>
    ⟨source, reading.val, formed, reading.property⟩

theorem readMethodContext?_source [DecidableEq Base] (carriers : MethodCarriers I registry Base)
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {Γ : HOL.Ctx Base} (ambient : CCtx Head Γ.length) (types : TypeSyntax I Head Γ.length)
    (environment : TermEnvironment I Head Γ.length context) (motive constructor : CTm Head Γ.length)
    (pending : List (CTm Head Γ.length)) (pendingCarriers : HOL.Ctx Base)
    (sameLength : pending.length = pendingCarriers.length)
    (formed : CCtxFormed P (generatedMethodSource carriers indexing containers code ambient types environment
      motive constructor pending pendingCarriers sameLength))
    (output : GuardedContext P lex (carriers.context code Γ pendingCarriers))
    (accepted : readMethodContext? carriers indexing containers code ambient types environment
      motive constructor pending pendingCarriers sameLength formed = some output) :
    output.source = generatedMethodSource carriers indexing containers code ambient types environment
      motive constructor pending pendingCarriers sameLength := by
  unfold readMethodContext? at accepted
  cases reading : Reader.readContext? lex (carriers.context code Γ pendingCarriers)
      (generatedMethodSource carriers indexing containers code ambient types environment
        motive constructor pending pendingCarriers sameLength) with
  | none => simp only [reading, Option.map_none] at accepted; contradiction
  | some value =>
      simp only [reading, Option.map_some] at accepted
      cases Option.some.inj accepted
      rfl

theorem readMethodContext?_isSome_iff [DecidableEq Base] (carriers : MethodCarriers I registry Base)
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {Γ : HOL.Ctx Base} (ambient : CCtx Head Γ.length) (types : TypeSyntax I Head Γ.length)
    (environment : TermEnvironment I Head Γ.length context) (motive constructor : CTm Head Γ.length)
    (pending : List (CTm Head Γ.length)) (pendingCarriers : HOL.Ctx Base)
    (sameLength : pending.length = pendingCarriers.length)
    (formed : CCtxFormed P (generatedMethodSource carriers indexing containers code ambient types environment
      motive constructor pending pendingCarriers sameLength)) :
    (readMethodContext? (lex := lex) carriers indexing containers code ambient types environment
      motive constructor pending pendingCarriers sameLength formed).isSome = true ↔
      ∃ telescope, ContextReads lex (generatedMethodSource carriers indexing containers code ambient types environment
        motive constructor pending pendingCarriers sameLength) telescope := by
  unfold readMethodContext?
  dsimp only
  constructor
  · intro accepted
    cases reading : Reader.readContext? lex (carriers.context code Γ pendingCarriers)
        (generatedMethodSource carriers indexing containers code ambient types environment
          motive constructor pending pendingCarriers sameLength) with
    | none => simp only [reading, Option.map_none, Option.isSome_none, Bool.false_eq_true] at accepted
    | some value => exact ⟨value.val, value.property⟩
  · rintro ⟨telescope, reading⟩
    rw [Reader.readContext_complete reading]
    rfl

#print axioms generatedMethodSource_formed
#print axioms readMethodContext?_isSome_iff

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated
