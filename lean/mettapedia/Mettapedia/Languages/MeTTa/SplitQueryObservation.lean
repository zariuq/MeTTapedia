import Mettapedia.Languages.MeTTa.TermView

/-!
# Borrowed fields of an application

A split application owns its rigid head and borrows independently scoped
fields. Its observer exposes the constructor without forcing the fields.
Observation commutes with forcing, and matching equal constructors can pass
their field equations directly to the existing unifier. The latter preserves
the complete optional substitution, including alias constraints and failure.

These are semantic laws. The C trail, frame refresh and suspension ownership
remain separate implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SplitQueryObservation

open Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation
open Mettapedia.GSLT.LanguageDef.DelayedSourceBindingCompilation
open Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra
open TermViewCompilation

variable {Owner Revision Occurrence Plan : Type}

inductive Value (Owner Revision Occurrence Plan : Type) where
  | cursor (value : Cursor Owner Revision Occurrence Plan)
  | application (head : List UInt8)
      (fields : List (Cursor Owner Revision Occurrence Plan))

def openTermsOfList : List OpenTerm → OpenTerms
  | [] => .nil
  | value :: rest => .cons value (openTermsOfList rest)

@[simp] theorem openTermsToList_ofList (values : List OpenTerm) :
    openTermsToList (openTermsOfList values) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [openTermsOfList, openTermsToList, ih]

def denote : Value Owner Revision Occurrence Plan → OpenTerm
  | .cursor value => value.denote
  | .application head fields =>
      .application head (openTermsOfList (fields.map Cursor.denote))

def out : Value Owner Revision Occurrence Plan →
    TermLayer (Value Owner Revision Occurrence Plan)
  | .cursor value => (Cursor.out value).map Value.cursor
  | .application head fields => .application head (fields.map Value.cursor)

theorem out_exact (value : Value Owner Revision Occurrence Plan) :
    (out value).map denote = outOpen (denote value) := by
  cases value with
  | cursor value =>
      simpa [out, denote, TermLayer.map_comp, Function.comp_def] using
        Cursor.out_exact value
  | application head fields =>
      simp [out, denote, TermLayer.map, outOpen, Function.comp_def]

theorem traversal_exact (fuel : Nat)
    (work : List (Equation (Value Owner Revision Occurrence Plan))) :
    (run out fuel work).map denote = run outOpen fuel (mapEquations denote work) :=
  run_natural out outOpen denote out_exact fuel work

/-- Constructor decomposition schedules every field equation in order in one
unifier invocation. It does not solve each field with a fresh substitution. -/
theorem unify_fields_exact (fuel arity : Nat) (head : List UInt8)
    (left right : Fin arity → Cursor Owner Revision Occurrence Plan)
    (rest : List OpenEquation) :
    Mettapedia.Logic.LP.unifyFuel (fuel + 1)
      ((.app (⟨head, arity⟩ : OpenFunctionSymbol)
          (fun i => encodeOpenTerm (left i).denote),
        .app (⟨head, arity⟩ : OpenFunctionSymbol)
          (fun i => encodeOpenTerm (right i).denote)) :: rest) =
      Mettapedia.Logic.LP.unifyFuel fuel
        (Mettapedia.Logic.LP.finPairsToList
          (fun i => encodeOpenTerm (left i).denote)
          (fun i => encodeOpenTerm (right i).denote) ++ rest) := by
  simp [Mettapedia.Logic.LP.unifyFuel]

-- Independent field solutions would accept x=a and x=b separately. A shared
-- worklist correctly rejects their conjunction, while duplicate constraints
-- remain compatible.
private def x : Mettapedia.Logic.LP.Term openSignature := .var ⟨7, 1⟩
private def a : Mettapedia.Logic.LP.Term openSignature := .const (.integer 1)
private def b : Mettapedia.Logic.LP.Term openSignature := .const (.integer 2)

example : (Mettapedia.Logic.LP.unifyFuel 8 [(x, a), (x, a)]).isSome = true := by
  decide

example : Mettapedia.Logic.LP.unifyFuel 8 [(x, a), (x, b)] = none := by
  decide

end Mettapedia.Languages.MeTTa.SplitQueryObservation
