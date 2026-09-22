import Mettapedia.OSLF.Framework.WMCalculusLanguageDef

/-!
# Certified relation-provider boundary for guarded WM forgetting

An authored `outsideScope` premise receives rows from `RelationEnv`. This
module gives a reusable finite-handle provider whose Boolean decision comes
with a proof that accepted rows are semantically outside. It changes neither
the WM language nor the generic premise evaluator. A backend supplies its
own handle values and proves the decision procedure's soundness.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef

set_option autoImplicit false

structure HandleTable (Scope Query : Type) where
  scopes : List (Pattern × Scope)
  queries : List (Pattern × Query)

/-- Finite handle lookup is deterministic: the first matching row wins. -/
def lookupHandle {Value : Type} :
    List (Pattern × Value) → Pattern → Option Value
  | [], _ => none
  | (handle, value) :: rest, requested =>
      if handle = requested then some value else lookupHandle rest requested

/-- An external Boolean check may be incomplete, but every accepted answer
must be a proof-supported semantic outside-scope fact. -/
structure CheckedProvider (Scope Query : Type)
    (inScope : Scope → Query → Prop) where
  handles : HandleTable Scope Query
  outside : Scope → Query → Bool
  outside_sound : ∀ scope query, outside scope query = true → ¬ inScope scope query

def rows {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope) :
    String → List Pattern → List (List Pattern)
  | "outsideScope", [scopeHandle, queryHandle] =>
      match lookupHandle provider.handles.scopes scopeHandle,
        lookupHandle provider.handles.queries queryHandle with
      | some scope, some query =>
          if provider.outside scope query then
            [[scopeHandle, queryHandle]] else []
      | _, _ => []
  | _, _ => []

def relationEnv {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope) : RelationEnv where
  tuples := rows provider

theorem rows_mem_iff {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope)
    (scopeHandle queryHandle : Pattern) :
    [scopeHandle, queryHandle] ∈
        rows provider "outsideScope" [scopeHandle, queryHandle] ↔
      ∃ scope query,
        lookupHandle provider.handles.scopes scopeHandle = some scope ∧
        lookupHandle provider.handles.queries queryHandle = some query ∧
        provider.outside scope query = true := by
  cases hs : lookupHandle provider.handles.scopes scopeHandle with
  | none => simp [rows, hs]
  | some scope =>
      cases hq : lookupHandle provider.handles.queries queryHandle with
      | none => simp [rows, hs, hq]
      | some query =>
          cases hcheck : provider.outside scope query <;>
            simp [rows, hs, hq, hcheck]

theorem rows_row_eq {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope)
    (scopeHandle queryHandle : Pattern) (row : List Pattern)
    (returned : row ∈ rows provider "outsideScope"
      [scopeHandle, queryHandle]) :
    row = [scopeHandle, queryHandle] := by
  cases hs : lookupHandle provider.handles.scopes scopeHandle with
  | none => simp [rows, hs] at returned
  | some scope =>
      cases hq : lookupHandle provider.handles.queries queryHandle with
      | none => simp [rows, hs, hq] at returned
      | some query =>
          cases hcheck : provider.outside scope query with
          | false => simp [rows, hs, hq, hcheck] at returned
          | true =>
              simp [rows, hs, hq, hcheck] at returned
              exact returned

theorem returned_row_implies_outside
    {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope)
    (scopeHandle queryHandle : Pattern) (scope : Scope) (query : Query)
    (scopeDecode : lookupHandle provider.handles.scopes scopeHandle = some scope)
    (queryDecode : lookupHandle provider.handles.queries queryHandle = some query)
    (returned : [scopeHandle, queryHandle] ∈
      (relationEnv provider).tuples "outsideScope" [scopeHandle, queryHandle]) :
    ¬ inScope scope query := by
  obtain ⟨decodedScope, decodedQuery, hs, hq, accepted⟩ :=
    (rows_mem_iff provider scopeHandle queryHandle).mp returned
  have scopeEq : decodedScope = scope := by
    rw [scopeDecode] at hs
    exact (Option.some.inj hs).symm
  have queryEq : decodedQuery = query := by
    rw [queryDecode] at hq
    exact (Option.some.inj hq).symm
  subst decodedScope
  subst decodedQuery
  exact provider.outside_sound scope query accepted

/-- The premise evaluator does not weaken the checked-provider contract:
when its rule variables are already bound, any successful result is backed
by an accepted provider row and hence a semantic outside-scope fact. -/
theorem premise_success_implies_outside
    {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope)
    (lang : LanguageDef)
    (scopeHandle worldHandle queryHandle : Pattern)
    (scope : Scope) (query : Query)
    (scopeDecode : lookupHandle provider.handles.scopes scopeHandle = some scope)
    (queryDecode : lookupHandle provider.handles.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      applyPremisesWithEnv (relationEnv provider) lang
        ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    ¬ inScope scope query := by
  have returned : [scopeHandle, queryHandle] ∈
      (relationEnv provider).tuples "outsideScope"
        [scopeHandle, queryHandle] := by
    simp [applyPremisesWithEnv, ruleForgetOutsideGuarded,
      premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      mergeBindings, applyBindings] at success
    obtain ⟨row, rowMember, _⟩ := success
    have rowEq := rows_row_eq provider scopeHandle queryHandle row rowMember
    simpa only [rowEq] using rowMember
  exact returned_row_implies_outside provider scopeHandle queryHandle
    scope query scopeDecode queryDecode returned

#print axioms rows_mem_iff
#print axioms rows_row_eq
#print axioms returned_row_implies_outside
#print axioms premise_success_implies_outside

end Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider
