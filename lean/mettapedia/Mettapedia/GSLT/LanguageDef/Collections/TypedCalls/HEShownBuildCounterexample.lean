import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStructuralBoundary

/-!
# A positive application typing count does not justify a shown constructor

The native typed-build boundary tests whether the constructed expression has
at least one typing. Its shown-range clause reads the constructor operator's
single declared range. An expression-subject annotation can satisfy the first
test even when the constructor arguments fail that function declaration.

These controls use the existing HE applicability checker and evaluator. The
two Boolean predicates isolate the relevant native clauses; they are not a
replacement evaluator or a correctness assumption about its body.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEShownBuildCounterexample

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE
open CompletedDelivery

def declaration (subject type_ : Atom) : Atom := .expression [.symbol ":", subject, type_]
def equation (lhs rhs : Atom) : Atom := .expression [.symbol "=", lhs, rhs]
def range : Atom := .symbol "OpenShownRange"
def signature : Atom := arrowType [.var "t", .var "t"] range
def built : Atom := .expression [.symbol "OpenShownBox", .grounded (.int 1), .grounded (.string "wrong-field")]
def call : Atom := .expression [.symbol "shown-open-body"]
def alternate : Atom := .symbol "AlternateRange"

def source : Space := Space.ofList
  [declaration (.symbol "OpenShownBox") signature,
   declaration built alternate,
   declaration (.symbol "shown-open-body") (arrowType [] range),
   equation call built]

/-- The TYPED_BUILD shown-range clause observes only this operator row. -/
def headShows (space : Space) (head : String) (expected : Atom) : Bool :=
  atomVariables expected == [] &&
    match getAtomTypes space (.symbol head) with
    | [type_] => getFunctionRetType type_ == some expected
    | _ => false

/-- Direct expression rows contribute a positive typing count independently
of the constructor's applicability. This does not confuse the historical
source lookup's Undefined fallback with a native nonempty count. -/
def hasExpressionTyping (space : Space) (value : Atom) : Bool := !(getAnnotatedTypes space value).isEmpty

theorem open_formals_closed_range :
    atomVariables signature = ["t", "t"] ∧ atomVariables range = [] := by decide

theorem operator_declaration_is_unique : getAtomTypes source (.symbol "OpenShownBox") = [signature] := by decide

theorem shown_clause_accepts : headShows source "OpenShownBox" range = true := by decide

theorem positive_count_comes_from_expression_row :
    getAtomTypes source built = [alternate] ∧ hasExpressionTyping source built = true := by decide

theorem constructor_has_no_equation :
    HEConstructorAdmission.headAbsent source "OpenShownBox" = true := by decide

theorem applicability_is_error :
    (checkIfFunctionTypeIsApplicable built signature range source Bindings.empty 64).isLeft = true := by
  decide +kernel

theorem actual_applicability_rejects :
    ¬∃ bindings, checkIfFunctionTypeIsApplicable built signature range source Bindings.empty 64 = .inr bindings := by
  rintro ⟨bindings, accepted⟩
  have error := applicability_is_error
  rw [accepted] at error
  cases error

theorem actual_source_does_not_return_the_built_value :
    evalAtom source GroundedDispatch.none call Atom.undefinedType Bindings.empty 128 ≠ [(built, Bindings.empty)] := by
  decide +kernel

def sourceError : Atom := mkError built (.badArgType 2 (.var "t") (.symbol "String"))

/-- This source profile prints the written formal in its diagnostic; the
current native canonical route prints its Number instance. Both reject. -/
theorem actual_source_returns_error :
    evalAtom source GroundedDispatch.none call Atom.undefinedType Bindings.empty 128 =
      [(sourceError, Bindings.empty)] := by decide +kernel

theorem applicability_rejects_at_every_larger_budget (extra : Nat) :
    checkIfFunctionTypeIsApplicable built signature range source Bindings.empty (64 + extra) =
      .inl [sourceError] := by
  rw [functionTypeCovered_stable built signature range source Bindings.empty
    64 extra (lookup := rawTypeLookup source) (by decide +kernel)]
  decide +kernel

theorem classifier_and_count_do_not_earn_source_acceptance :
    headShows source "OpenShownBox" range = true ∧ hasExpressionTyping source built = true ∧
    ¬∃ bindings, checkIfFunctionTypeIsApplicable built signature range source Bindings.empty 64 = .inr bindings :=
  ⟨shown_clause_accepts, positive_count_comes_from_expression_row.2, actual_applicability_rejects⟩

def goodBuilt : Atom := .expression [.symbol "OpenShownBox", .grounded (.int 1), .grounded (.int 2)]
def goodSource : Space := Space.ofList
  [declaration (.symbol "OpenShownBox") signature,
   declaration (.symbol "shown-open-body") (arrowType [] range),
   equation call goodBuilt]

theorem legitimate_open_constructor_returns_value :
    (evalAtom goodSource GroundedDispatch.none call Atom.undefinedType Bindings.empty 128).map Prod.fst = [goodBuilt] := by
  decide +kernel

def selfAnnotatedSource : Space := Space.ofList
  [declaration (.symbol "OpenShownBox") signature,
   declaration built range,
   declaration (.symbol "shown-open-body") (arrowType [] range),
   equation call built]

/-- Looking for the owed range among the built expression's typings still
does not establish its constructor arguments' applicability. -/
theorem even_owed_typing_does_not_establish_applicability :
    getAtomTypes selfAnnotatedSource built = [range] ∧
    (checkIfFunctionTypeIsApplicable built signature range selfAnnotatedSource Bindings.empty 64).isLeft = true := by
  decide +kernel

theorem self_annotation_does_not_repair_the_source_program :
    evalAtom selfAnnotatedSource GroundedDispatch.none call Atom.undefinedType Bindings.empty 128 =
      [(sourceError, Bindings.empty)] := by decide +kernel

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEShownBuildCounterexample
