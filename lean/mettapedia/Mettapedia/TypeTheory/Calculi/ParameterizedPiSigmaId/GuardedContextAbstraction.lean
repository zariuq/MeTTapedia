import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateRealizability

/-!
# Closing a guarded realizer over its original telescope

Each binder becomes a dependent source product and a native function argument.
The existing single-binder abstraction discharges its precise predicate guard;
closed root assumptions remain. Empty predicates are allowed. This constructs
a function of the original inputs, without asserting that those inputs exist.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading

open Mettapedia.Logic
open Presentation TypedEquality.Annotated
open TypedEquality.Impredicative.Domain (lamsCtx pisCtx)
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
    {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}

def telescopeCarrier : HOL.Ctx Base → HOL.Ty Base → HOL.Ty Base
  | [], result => result
  | domain :: context, result => telescopeCarrier context (domain ⇒ result)

namespace GuardedContext

def empty (P : ChurchRules R) (lex : LexicalReading Head Base Const) : GuardedContext P lex [] :=
  ⟨.nil, .nil, .nil, .nil⟩

end GuardedContext

namespace GuardedRealizer

def abstractContext {L : Type} [UniverseLevel.LevelOrder L]
    (levels : TypedEquality.Normalization.LevelModel R L)
    {Γ : HOL.Ctx Base} (context : GuardedContext P lex Γ)
    {source type : CTm Head Γ.length} {carrier : HOL.Ty Base}
    {roots : List (HOL.ClosedFormula Const)}
    (realizer : GuardedRealizer roots context source type carrier) :
    GuardedRealizer roots (GuardedContext.empty P lex) (lamsCtx context.source source)
      (pisCtx context.source type) (telescopeCarrier Γ carrier) := by
  cases Γ with
  | nil =>
      rcases context with ⟨sourceContext, telescope, formed, reading⟩
      cases sourceContext
      cases telescope
      exact realizer
  | cons domain previous =>
      rcases context with ⟨sourceContext, telescope, formed, reading⟩
      cases sourceContext with
      | snoc sourceContext A =>
          cases telescope with
          | snoc telescope predicate =>
              have priorFormed : CCtxFormed P sourceContext := by cases formed; assumption
              have domainFormed : CIsType P sourceContext A := by cases formed; assumption
              have priorReading : ContextReads lex sourceContext telescope := by cases reading; assumption
              have domainReading : Reads lex A predicate := by cases reading; assumption
              let prior : GuardedContext P lex previous := ⟨sourceContext, telescope, priorFormed, priorReading⟩
              have body : GuardedRealizer roots (prior.snoc predicate domainReading domainFormed) source type carrier := realizer
              let abstracted := abstraction levels predicate domainReading domainFormed
                (body.typed.isType levels (prior.snoc predicate domainReading domainFormed).formed) body
              exact abstractContext levels prior abstracted
termination_by Γ.length
decreasing_by simp_all

theorem abstractContext_free {L : Type} [UniverseLevel.LevelOrder L]
    (levels : TypedEquality.Normalization.LevelModel R L)
    {Γ : HOL.Ctx Base} (context : GuardedContext P lex Γ)
    {source type : CTm Head Γ.length} {carrier : HOL.Ty Base}
    {roots : List (HOL.ClosedFormula Const)}
    (realizer : GuardedRealizer roots context source type carrier) (free : realizer.Free) :
    (abstractContext levels context realizer).Free := by
  induction Γ generalizing carrier with
  | nil =>
      rcases context with ⟨sourceContext, telescope, formed, reading⟩
      cases sourceContext
      cases telescope
      simpa only [abstractContext] using free
  | cons domain previous ih =>
      rcases context with ⟨sourceContext, telescope, formed, reading⟩
      cases sourceContext with
      | snoc sourceContext A =>
          cases telescope with
          | snoc telescope predicate =>
              unfold abstractContext
              apply ih
              exact abstraction_free levels predicate _ _ _ _ free

#print axioms abstractContext
#print axioms abstractContext_free

end GuardedRealizer
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
