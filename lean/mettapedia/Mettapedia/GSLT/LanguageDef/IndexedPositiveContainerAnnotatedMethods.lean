import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestMethodSpecialization
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Erasure
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedApplicationSpines

/-!
# Annotated traversal of original constructor-method fields

The traversal opens one dependent product for each original field, including
recursive and registered nested fields. Erasure agrees with the existing
declaration-generated specialization. The residual annotated type retains
the queued induction hypotheses and final motive in their source order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerAnnotatedMethods

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated
open IndexedPositiveContainerGuestTypes IndexedPositiveContainerGuestPlans
open IndexedPositiveContainerGuestMethodSpecialization

universe u
variable {I : Interface.{u}} {registry : Registry I} {Head : Type}

def instantiateFields {parameters : Nat} : {context : List I.SortCode} →
    (code : Code I registry parameters context) → {n : Nat} →
    (Fin (fieldCount code) → CTm Head n) → CTm Head n → Option (CTm Head n)
  | _, .result _, _, _, type => some type
  | _, .data _ rest, _, fields, .pi _ body =>
      instantiateFields rest (fun i => fields i.succ) (CTm.inst0 (fields ⟨0, by simp [fieldCount]⟩) body)
  | _, .recursive _ rest, _, fields, .pi _ body =>
      instantiateFields rest (fun i => fields i.succ) (CTm.inst0 (fields ⟨0, by simp [fieldCount]⟩) body)
  | _, .nested _ _ _ _ _ rest, _, fields, .pi _ body =>
      instantiateFields rest (fun i => fields i.succ) (CTm.inst0 (fields ⟨0, by simp [fieldCount]⟩) body)
  | _, _, _, _, _ => none

def applyFields {parameters : Nat} : {context : List I.SortCode} →
    (code : Code I registry parameters context) → {n : Nat} →
    (Fin (fieldCount code) → CTm Head n) → CTm Head n → CTm Head n
  | _, .result _, _, _, function => function
  | _, .data _ rest, _, fields, function =>
      applyFields rest (fun i => fields i.succ) (.app function (fields ⟨0, by simp [fieldCount]⟩))
  | _, .recursive _ rest, _, fields, function =>
      applyFields rest (fun i => fields i.succ) (.app function (fields ⟨0, by simp [fieldCount]⟩))
  | _, .nested _ _ _ _ _ rest, _, fields, function =>
      applyFields rest (fun i => fields i.succ) (.app function (fields ⟨0, by simp [fieldCount]⟩))

theorem instantiateFields_erase {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat}
    (fields : Fin (fieldCount code) → CTm Head n) (type : CTm Head n) :
    (instantiateFields code fields type).map CTm.erase =
      IndexedPositiveContainerGuestMethodSpecialization.instantiateFields code (fun i => (fields i).erase) type.erase := by
  induction code generalizing n with
  | result index => rfl
  | data sort rest previous =>
      cases type <;> simp only [instantiateFields, CTm.erase,
        IndexedPositiveContainerGuestMethodSpecialization.instantiateFields, Option.map_none]
      rename_i domain body
      simpa only [CTm.erase_inst0] using previous (fun i => fields i.succ)
        (CTm.inst0 (fields ⟨0, by simp [fieldCount]⟩) body)
  | recursive index rest previous =>
      cases type <;> simp only [instantiateFields, CTm.erase,
        IndexedPositiveContainerGuestMethodSpecialization.instantiateFields, Option.map_none]
      rename_i domain body
      simpa only [CTm.erase_inst0] using previous (fun i => fields i.succ)
        (CTm.inst0 (fields ⟨0, by simp [fieldCount]⟩) body)
  | nested name entry registered output index rest previous =>
      cases type <;> simp only [instantiateFields, CTm.erase,
        IndexedPositiveContainerGuestMethodSpecialization.instantiateFields, Option.map_none]
      rename_i domain body
      simpa only [CTm.erase_inst0] using previous (fun i => fields i.succ)
        (CTm.inst0 (fields ⟨0, by simp [fieldCount]⟩) body)

theorem applyFields_erase {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat}
    (fields : Fin (fieldCount code) → CTm Head n) (function : CTm Head n) :
    (applyFields code fields function).erase =
      IndexedPositiveContainerGuestMethodSpecialization.applyFields code (fun i => (fields i).erase) function.erase := by
  induction code generalizing n function with
  | result _ => rfl
  | data _ _ previous => exact previous _ _
  | recursive _ _ previous => exact previous _ _
  | nested _ _ _ _ _ _ previous => exact previous _ _

theorem applyFields_eq_appSpine {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat}
    (fields : Fin (fieldCount code) → CTm Head n) (function : CTm Head n) :
    applyFields code fields function = CTm.appSpine function (List.ofFn fields) := by
  induction code generalizing n function with
  | result _ => rfl
  | data _ _ previous =>
      simpa only [applyFields, fieldCount, List.ofFn_succ, CTm.appSpine, List.foldl_cons, Fin.mk_zero] using
        previous (fun i => fields i.succ) (.app function (fields ⟨0, by simp [fieldCount]⟩))
  | recursive _ _ previous =>
      simpa only [applyFields, fieldCount, List.ofFn_succ, CTm.appSpine, List.foldl_cons, Fin.mk_zero] using
        previous (fun i => fields i.succ) (.app function (fields ⟨0, by simp [fieldCount]⟩))
  | nested _ _ _ _ _ _ previous =>
      simpa only [applyFields, fieldCount, List.ofFn_succ, CTm.appSpine, List.foldl_cons, Fin.mk_zero] using
        previous (fun i => fields i.succ) (.app function (fields ⟨0, by simp [fieldCount]⟩))

theorem instantiateFields_eq_products {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat}
    (fields : Fin (fieldCount code) → CTm Head n) (type : CTm Head n) :
    instantiateFields code fields type = AnnotatedPredicateReading.instantiateProducts (List.ofFn fields) type := by
  induction code generalizing n with
  | result _ => rfl
  | data _ _ previous =>
      cases type <;> simp only [instantiateFields, fieldCount, List.ofFn_succ, AnnotatedPredicateReading.instantiateProducts]
      exact previous _ _
  | recursive _ _ previous =>
      cases type <;> simp only [instantiateFields, fieldCount, List.ofFn_succ, AnnotatedPredicateReading.instantiateProducts]
      exact previous _ _
  | nested _ _ _ _ _ _ previous =>
      cases type <;> simp only [instantiateFields, fieldCount, List.ofFn_succ, AnnotatedPredicateReading.instantiateProducts]
      exact previous _ _

theorem instantiateFields_of_erasure {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat}
    (fields : Fin (fieldCount code) → CTm Head n) (type : CTm Head n) (residual : Tm Head n)
    (accepted : IndexedPositiveContainerGuestMethodSpecialization.instantiateFields code
      (fun i => (fields i).erase) type.erase = some residual) :
    ∃ remaining, instantiateFields code fields type = some remaining ∧ remaining.erase = residual := by
  have agreement := instantiateFields_erase code fields type
  cases produced : instantiateFields code fields type with
  | none => simp only [produced, Option.map_none, accepted] at agreement; contradiction
  | some remaining =>
      refine ⟨remaining, rfl, ?_⟩
      exact Option.some.inj (by simpa only [produced, Option.map_some, accepted] using agreement)

theorem methodBody_specialize (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context) {n : Nat}
    (types : TypeSyntax I Head n) (environment : IndexedInductive.Guest.TermEnv I Head n context)
    (motive constructor : Tm Head n) (pending : List (Tm Head n))
    (fields : Fin (fieldCount code) → CTm Head n) (type : CTm Head n)
    (original : type.erase = IndexedPositiveContainerGuestTypes.methodBody indexing containers code types environment motive constructor pending) :
    ∃ remaining, instantiateFields code fields type = some remaining ∧
      remaining.erase = hypotheses (pending ++ hypothesisTypes indexing containers code types environment motive (fun i => (fields i).erase))
        (conclusion indexing code environment motive constructor (fun i => (fields i).erase)) := by
  apply instantiateFields_of_erasure code fields type
  rw [original]
  exact IndexedPositiveContainerGuestMethodSpecialization.methodBody_specialize indexing containers code types environment
    motive constructor pending (fun i => (fields i).erase)

section Realization

open Mettapedia.Logic AnnotatedPredicateReading
universe v w
variable {Base : Type v} {Const : HOL.Ty Base → Type w}
    {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}
    {Γ : HOL.Ctx Base} {roots : List (HOL.ClosedFormula Const)}
    {guardedContext : GuardedContext P lex Γ}

/-- The field traversal changes the source index while retaining exactly the
proof constructed by the generic dependent application spine. -/
def realizeFields [DecidableEq Base] {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context)
    (fields : Fin (fieldCount code) → CTm Head Γ.length)
    {source residual function : CTm Head Γ.length} {carrier residualCarrier : HOL.Ty Base}
    (supplied : SuppliedArguments roots guardedContext (List.ofFn fields) source carrier residual residualCarrier)
    (functionValue : GuardedRealizer roots guardedContext function source carrier) :
    GuardedRealizer roots guardedContext (applyFields code fields function) residual residualCarrier :=
  let applied := supplied.apply functionValue
  { applied with
    typed := (applyFields_eq_appSpine code fields function).symm ▸ applied.typed
    termRead := (applyFields_eq_appSpine code fields function).symm ▸ applied.termRead }

theorem realizeFields_free [DecidableEq Base] {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context)
    (fields : Fin (fieldCount code) → CTm Head Γ.length)
    {source residual function : CTm Head Γ.length} {carrier residualCarrier : HOL.Ty Base}
    (supplied : SuppliedArguments roots guardedContext (List.ofFn fields) source carrier residual residualCarrier)
    (functionValue : GuardedRealizer roots guardedContext function source carrier)
    (suppliedFree : supplied.Free) (functionFree : functionValue.Free) :
    (realizeFields code fields supplied functionValue).Free :=
  supplied.apply_free functionValue suppliedFree functionFree

theorem suppliedFields_residual (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (types : TypeSyntax I Head Γ.length)
    (environment : IndexedInductive.Guest.TermEnv I Head Γ.length context)
    (motive constructor : Tm Head Γ.length) (pending : List (Tm Head Γ.length))
    (fields : Fin (fieldCount code) → CTm Head Γ.length)
    {source residual : CTm Head Γ.length} {carrier residualCarrier : HOL.Ty Base}
    (supplied : SuppliedArguments roots guardedContext (List.ofFn fields) source carrier residual residualCarrier)
    (original : source.erase = IndexedPositiveContainerGuestTypes.methodBody indexing containers
      code types environment motive constructor pending) :
    residual.erase = hypotheses
      (pending ++ hypothesisTypes indexing containers code types environment motive (fun i => (fields i).erase))
      (conclusion indexing code environment motive constructor (fun i => (fields i).erase)) := by
  obtain ⟨remaining, specialized, exactType⟩ :=
    methodBody_specialize indexing containers code types environment motive constructor pending fields source original
  have same : residual = remaining := Option.some.inj
    (supplied.instantiate.symm.trans ((instantiateFields_eq_products code fields source).symm.trans specialized))
  exact same ▸ exactType

/-- Both phases use the same guarded context and root occurrences. Nested
fields contribute one complete induction-bundle argument in the second phase. -/
def realizeMethod [DecidableEq Base] {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context)
    (fields : Fin (fieldCount code) → CTm Head Γ.length)
    {source residual result function : CTm Head Γ.length}
    {carrier residualCarrier resultCarrier : HOL.Ty Base}
    (fieldValues : SuppliedArguments roots guardedContext (List.ofFn fields) source carrier residual residualCarrier)
    {inductionArguments : List (CTm Head Γ.length)}
    (inductionValues : SuppliedArguments roots guardedContext inductionArguments residual residualCarrier result resultCarrier)
    (functionValue : GuardedRealizer roots guardedContext function source carrier) :
    GuardedRealizer roots guardedContext
      (CTm.appSpine (applyFields code fields function) inductionArguments) result resultCarrier :=
  inductionValues.apply (realizeFields code fields fieldValues functionValue)

theorem realizeMethod_free [DecidableEq Base] {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context)
    (fields : Fin (fieldCount code) → CTm Head Γ.length)
    {source residual result function : CTm Head Γ.length}
    {carrier residualCarrier resultCarrier : HOL.Ty Base}
    (fieldValues : SuppliedArguments roots guardedContext (List.ofFn fields) source carrier residual residualCarrier)
    {inductionArguments : List (CTm Head Γ.length)}
    (inductionValues : SuppliedArguments roots guardedContext inductionArguments residual residualCarrier result resultCarrier)
    (functionValue : GuardedRealizer roots guardedContext function source carrier)
    (fieldsFree : fieldValues.Free) (inductionFree : inductionValues.Free) (functionFree : functionValue.Free) :
    (realizeMethod code fields fieldValues inductionValues functionValue).Free :=
  inductionValues.apply_free _ inductionFree (realizeFields_free code fields fieldValues functionValue fieldsFree functionFree)

theorem suppliedMethod_result (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (types : TypeSyntax I Head Γ.length)
    (environment : IndexedInductive.Guest.TermEnv I Head Γ.length context)
    (motive constructor : Tm Head Γ.length) (pending : List (Tm Head Γ.length))
    (fields : Fin (fieldCount code) → CTm Head Γ.length)
    {source residual result : CTm Head Γ.length} {carrier residualCarrier resultCarrier : HOL.Ty Base}
    (fieldValues : SuppliedArguments roots guardedContext (List.ofFn fields) source carrier residual residualCarrier)
    {inductionArguments : List (CTm Head Γ.length)}
    (inductionValues : SuppliedArguments roots guardedContext inductionArguments residual residualCarrier result resultCarrier)
    (original : source.erase = IndexedPositiveContainerGuestTypes.methodBody indexing containers
      code types environment motive constructor pending)
    (complete : inductionArguments.length = pending.length +
      (hypothesisTypes indexing containers code types environment motive (fun i => (fields i).erase)).length) :
    result.erase = conclusion indexing code environment motive constructor (fun i => (fields i).erase) := by
  apply inductionValues.residual_of_curried
    (pending ++ hypothesisTypes indexing containers code types environment motive (fun i => (fields i).erase))
  · exact suppliedFields_residual indexing containers code types environment motive constructor pending fields fieldValues original
  · simpa only [List.length_append] using complete

end Realization

#print axioms instantiateFields_erase
#print axioms methodBody_specialize
#print axioms realizeMethod_free
#print axioms suppliedMethod_result

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerAnnotatedMethods
