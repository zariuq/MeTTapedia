import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotatedFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateFormation

/-!
# Checked guarded contexts for generated constructor fields

The description and a declared carrier profile determine the complete source
field context. Its source formation is derived from primitive contracts.
The existing context reader computes every predicate guard and refuses a
carrier or lexical mismatch. This is a selected fixed-carrier reading, not
an interpretation of arbitrary universe-valued source families.
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

structure FieldCarriers (I : Interface.{u}) (registry : Registry I) (Base : Type v) where
  data : I.SortCode → HOL.Ty Base
  recursive : HOL.Ty Base
  nested : (name : String) → (entry : Entry I) → registry.lookup name = some entry → HOL.Ty Base

def FieldCarriers.context (carriers : FieldCarriers I registry Base) {parameters : Nat} :
    {context : List I.SortCode} → Code I registry parameters context → HOL.Ctx Base → HOL.Ctx Base
  | _, .result _, ambient => ambient
  | _, .data sort rest, ambient => carriers.context rest (carriers.data sort :: ambient)
  | _, .recursive _ rest, ambient => carriers.context rest (carriers.recursive :: ambient)
  | _, .nested name entry registered _ _ rest, ambient => carriers.context rest (carriers.nested name entry registered :: ambient)

theorem FieldCarriers.context_length (carriers : FieldCarriers I registry Base) {parameters : Nat}
    {context : List I.SortCode} (code : Code I registry parameters context) (ambient : HOL.Ctx Base) :
    (carriers.context code ambient).length = ambient.length + fieldCount code := by
  induction code generalizing ambient with
  | result _ => simp only [FieldCarriers.context, fieldCount, Nat.add_zero]
  | data _ _ previous => simp only [FieldCarriers.context, previous, fieldCount, List.length_cons]; omega
  | recursive _ _ previous => simp only [FieldCarriers.context, previous, fieldCount, List.length_cons]; omega
  | nested _ _ _ _ _ _ previous => simp only [FieldCarriers.context, previous, fieldCount, List.length_cons]; omega

def generatedSource (carriers : FieldCarriers I registry Base) (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {Γ : HOL.Ctx Base} (ambient : CCtx Head Γ.length)
    (types : TypeSyntax I Head Γ.length) (environment : TermEnvironment I Head Γ.length context) :
    CCtx Head (carriers.context code Γ).length :=
  let same := (fieldContext_size indexing containers code ambient types environment).trans
    (carriers.context_length code Γ).symm
  same ▸ (fieldContext indexing containers code ambient types environment).2

private theorem castContext_formed {n m : Nat} (same : n = m) (context : CCtx Head n)
    (formed : CCtxFormed P context) : CCtxFormed P (same ▸ context) := by
  cases same
  exact formed

theorem generatedSource_formed [UniverseLevel.LevelOrder L] (levels : LevelModel R L)
    (carriers : FieldCarriers I registry Base) {n : Nat} {ambient : CCtx Head n} {types : TypeSyntax I Head n}
    {indexing : Indexing I Head} {containers : RegistrySyntax I registry Head}
    {domain : indexing.Domain n} {level : Head} {admitted : IndexPredicate I}
    (primitives : ConstructorPrimitives (P := P) ambient types indexing containers domain level admitted)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (accepted : IndicesAdmitted admitted code) {Γ : HOL.Ctx Base} (target : GuardedContext P lex Γ)
    (images : CSub Head n Γ.length) (morphism : CSubstMor P ambient target.source images)
    (environment : TermEnvironment I Head Γ.length context)
    (typed : EnvironmentTyped (P := P) target.source (fun sort => (types.dataType sort).subst images) environment) :
    CCtxFormed P (generatedSource carriers indexing containers code target.source (types.map (CTm.subst images)) environment) :=
  castContext_formed _ _ (constructorContext_formed levels primitives code accepted target.formed images morphism environment typed)

def guardedContext? [DecidableEq Base] [UniverseLevel.LevelOrder L] (levels : LevelModel R L)
    (carriers : FieldCarriers I registry Base) {n : Nat} {ambient : CCtx Head n} {types : TypeSyntax I Head n}
    {indexing : Indexing I Head} {containers : RegistrySyntax I registry Head}
    {domain : indexing.Domain n} {level : Head} {admitted : IndexPredicate I}
    (primitives : ConstructorPrimitives (P := P) ambient types indexing containers domain level admitted)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (accepted : IndicesAdmitted admitted code) {Γ : HOL.Ctx Base} (target : GuardedContext P lex Γ)
    (images : CSub Head n Γ.length) (morphism : CSubstMor P ambient target.source images)
    (environment : TermEnvironment I Head Γ.length context)
    (typed : EnvironmentTyped (P := P) target.source (fun sort => (types.dataType sort).subst images) environment) :
    Option (GuardedContext P lex (carriers.context code Γ)) :=
  let source := generatedSource carriers indexing containers code target.source (types.map (CTm.subst images)) environment
  (Reader.readContext? lex (carriers.context code Γ) source).map fun read =>
    ⟨source, read.val, generatedSource_formed levels carriers primitives code accepted target images morphism environment typed, read.property⟩

theorem guardedContext?_source [DecidableEq Base] [UniverseLevel.LevelOrder L] (levels : LevelModel R L)
    (carriers : FieldCarriers I registry Base) {n : Nat} {ambient : CCtx Head n} {types : TypeSyntax I Head n}
    {indexing : Indexing I Head} {containers : RegistrySyntax I registry Head}
    {domain : indexing.Domain n} {level : Head} {admitted : IndexPredicate I}
    (primitives : ConstructorPrimitives (P := P) ambient types indexing containers domain level admitted)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (accepted : IndicesAdmitted admitted code) {Γ : HOL.Ctx Base} (target : GuardedContext P lex Γ)
    (images : CSub Head n Γ.length) (morphism : CSubstMor P ambient target.source images)
    (environment : TermEnvironment I Head Γ.length context)
    (typed : EnvironmentTyped (P := P) target.source (fun sort => (types.dataType sort).subst images) environment)
    (output : GuardedContext P lex (carriers.context code Γ))
    (acceptedReading : guardedContext? levels carriers primitives code accepted target images morphism environment typed = some output) :
    output.source = generatedSource carriers indexing containers code target.source (types.map (CTm.subst images)) environment := by
  unfold guardedContext? at acceptedReading
  cases read : Reader.readContext? lex (carriers.context code Γ)
      (generatedSource carriers indexing containers code target.source (types.map (CTm.subst images)) environment) with
  | none => simp only [read, Option.map_none] at acceptedReading; contradiction
  | some value =>
      simp only [read, Option.map_some] at acceptedReading
      cases Option.some.inj acceptedReading
      rfl

theorem guardedContext?_isSome_iff [DecidableEq Base] [UniverseLevel.LevelOrder L] (levels : LevelModel R L)
    (carriers : FieldCarriers I registry Base) {n : Nat} {ambient : CCtx Head n} {types : TypeSyntax I Head n}
    {indexing : Indexing I Head} {containers : RegistrySyntax I registry Head}
    {domain : indexing.Domain n} {level : Head} {admitted : IndexPredicate I}
    (primitives : ConstructorPrimitives (P := P) ambient types indexing containers domain level admitted)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (accepted : IndicesAdmitted admitted code) {Γ : HOL.Ctx Base} (target : GuardedContext P lex Γ)
    (images : CSub Head n Γ.length) (morphism : CSubstMor P ambient target.source images)
    (environment : TermEnvironment I Head Γ.length context)
    (typed : EnvironmentTyped (P := P) target.source (fun sort => (types.dataType sort).subst images) environment) :
    (guardedContext? levels carriers primitives code accepted target images morphism environment typed).isSome = true ↔
      ∃ telescope, ContextReads lex
        (generatedSource carriers indexing containers code target.source (types.map (CTm.subst images)) environment) telescope := by
  unfold guardedContext?
  dsimp only
  constructor
  · intro acceptedReading
    cases read : Reader.readContext? lex (carriers.context code Γ)
        (generatedSource carriers indexing containers code target.source (types.map (CTm.subst images)) environment) with
    | none => simp only [read, Option.map_none, Option.isSome_none, Bool.false_eq_true] at acceptedReading
    | some value => exact ⟨value.val, value.property⟩
  · rintro ⟨telescope, reading⟩
    rw [Reader.readContext_complete reading]
    rfl

#print axioms generatedSource_formed
#print axioms guardedContext?_source
#print axioms guardedContext?_isSome_iff

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated
