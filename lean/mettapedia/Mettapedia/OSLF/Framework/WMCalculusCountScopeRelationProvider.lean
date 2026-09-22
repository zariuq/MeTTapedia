import Mettapedia.OSLF.Framework.WMCalculusBNBridge
import Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
import Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
import Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider

/-!
# A checked outside-scope relation provider for the counting WM reading

The authored forgetting rule asks an external `RelationEnv` whether a query is
outside a scope. A finite table associates opaque source handles with the
counting reading's scope and query values. The provider returns a row only
after decoding both handles and checking the scope predicate. Its soundness is
relative to that explicit handle table; the table is not an interpretation of
all raw patterns or a new constructor grammar.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef

set_option autoImplicit false

/-- This backend instantiates the reusable checked-provider interface; it
does not define a second relation or matching semantics. -/
abbrev HandleTable :=
  WMCalculusCheckedScopeRelationProvider.HandleTable CountScope String

def lookupScope (entries : List (Pattern × CountScope)) (handle : Pattern) :
    Option CountScope :=
  WMCalculusCheckedScopeRelationProvider.lookupHandle entries handle

def lookupQuery (entries : List (Pattern × String)) (handle : Pattern) :
    Option String :=
  WMCalculusCheckedScopeRelationProvider.lookupHandle entries handle

def checkedProvider (table : HandleTable) :
    WMCalculusCheckedScopeRelationProvider.CheckedProvider
      CountScope String countingCombined.inScope where
  handles := table
  outside := fun scope query => !(scope query)
  outside_sound := by
    intro scope query accepted
    change ¬ scope query = true
    cases hscope : scope query <;> simp_all

def outsideRows (table : HandleTable) : String → List Pattern → List (List Pattern) :=
  WMCalculusCheckedScopeRelationProvider.rows (checkedProvider table)

def relationEnv (table : HandleTable) : RelationEnv :=
  WMCalculusCheckedScopeRelationProvider.relationEnv (checkedProvider table)

/-- A successful provider row licenses the concrete reading's forgetting
law for the represented values. This is the semantic guard certificate. -/
theorem returned_row_preserves_counted_query (table : HandleTable)
    (scopeHandle queryHandle : Pattern)
    (scope : CountScope) (query : String) (state : CountState)
    (scopeDecode : lookupScope table.scopes scopeHandle = some scope)
    (queryDecode : lookupQuery table.queries queryHandle = some query)
    (returned : [scopeHandle, queryHandle] ∈
      (relationEnv table).tuples "outsideScope" [scopeHandle, queryHandle]) :
    countingCombined.core.extract (countingCombined.forget scope state) query =
      countingCombined.core.extract state query := by
  apply countingCombined.forgetOutside
  exact WMCalculusCheckedScopeRelationProvider.returned_row_implies_outside
    (checkedProvider table) scopeHandle queryHandle scope query
    scopeDecode queryDecode returned

/-- A successful guarded step and its counting-model preservation arise from
the same checked provider answer. The theorem is restricted to decoded
handles and this authored root rule; contextual closure remains separate. -/
theorem guarded_forget_step_and_sound (table : HandleTable)
    (scopeHandle worldHandle queryHandle : Pattern)
    (scope : CountScope) (query : String) (state : CountState)
    (scopeDecode : lookupScope table.scopes scopeHandle = some scope)
    (queryDecode : lookupQuery table.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      applyPremisesWithEnv (relationEnv table)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    langReducesUsing (relationEnv table)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        (pExtract (pForget scopeHandle worldHandle) queryHandle)
        (pExtract worldHandle queryHandle) ∧
      countingCombined.core.extract (countingCombined.forget scope state) query =
        countingCombined.core.extract state query := by
  constructor
  · exact Mettapedia.OSLF.Framework.WMCalculusBNBridge.guarded_forget_of_dsep
      combinedVertex (Or.inl rfl) (relationEnv table)
      scopeHandle worldHandle queryHandle success
  · apply countingCombined.forgetOutside
    exact WMCalculusCheckedScopeRelationProvider.premise_success_implies_outside
      (checkedProvider table) (wmExtVertexLanguageDefGuarded combinedVertex)
      scopeHandle worldHandle queryHandle scope query
      scopeDecode queryDecode success

/-! ## Executable boundary checks on an explicit handle table -/

def scopeHandle : Pattern := .fvar "scope:X"
def insideHandle : Pattern := .fvar "query:x"
def outsideHandle : Pattern := .fvar "query:y"
def worldHandle : Pattern := .fvar "world:W"

def singletonX : CountScope := fun query => query == "x"

def demoTable : HandleTable where
  scopes := [(scopeHandle, singletonX)]
  queries := [(insideHandle, "x"), (outsideHandle, "y")]

private def handleTypeContext : FreeTypeContext :=
  FreeTypeContext.ofList
    [("scope:X", .base "Scope"), ("world:W", .base "State"),
      ("query:x", .base "Query"), ("query:y", .base "Query")]

/-- The provider's positive operational test inhabits the authored typed
WM syntax; the handles are variables with explicit sorts, not new formers. -/
theorem outside_source_typed :
    HasType (wmExtVertexLanguageDefGuarded combinedVertex)
      handleTypeContext []
      (pExtract (pForget scopeHandle worldHandle) outsideHandle)
      (.base "BinaryEvidence") := by
  exact (checkHasType_eq_true_iff (by decide +kernel)).1 (by decide +kernel)

theorem outside_target_typed :
    HasType (wmExtVertexLanguageDefGuarded combinedVertex)
      handleTypeContext []
      (pExtract worldHandle outsideHandle)
      (.base "BinaryEvidence") := by
  exact (checkHasType_eq_true_iff (by decide +kernel)).1 (by decide +kernel)

theorem outside_row_returned :
    (relationEnv demoTable).tuples "outsideScope"
      [scopeHandle, outsideHandle] = [[scopeHandle, outsideHandle]] := by
  decide +kernel

theorem outside_premise_accepted :
    [("q", outsideHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      applyPremisesWithEnv (relationEnv demoTable)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", outsideHandle), ("W", worldHandle), ("S", scopeHandle)] := by
  decide +kernel

theorem inside_row_rejected :
    (relationEnv demoTable).tuples "outsideScope"
      [scopeHandle, insideHandle] = [] := by
  decide +kernel

theorem inside_premise_rejected :
    applyPremisesWithEnv (relationEnv demoTable)
      (wmExtVertexLanguageDefGuarded combinedVertex)
      ruleForgetOutsideGuarded.premises
      [("q", insideHandle), ("W", worldHandle), ("S", scopeHandle)] = [] := by
  decide +kernel

theorem unknown_row_rejected :
    (relationEnv demoTable).tuples "outsideScope"
      [scopeHandle, .fvar "query:unknown"] = [] := by
  decide +kernel

theorem unknown_premise_rejected :
    applyPremisesWithEnv (relationEnv demoTable)
      (wmExtVertexLanguageDefGuarded combinedVertex)
      ruleForgetOutsideGuarded.premises
      [("q", .fvar "query:unknown"), ("W", worldHandle),
        ("S", scopeHandle)] = [] := by
  decide +kernel

/-- The exact provider answer makes the existing authored guarded rule fire;
the semantic preservation theorem above proves what this answer means for
the counting reading. -/
theorem outside_guard_fires :
    langReducesUsing (relationEnv demoTable)
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (pExtract (pForget scopeHandle worldHandle) outsideHandle)
      (pExtract worldHandle outsideHandle) := by
  apply Mettapedia.OSLF.Framework.WMCalculusBNBridge.guarded_forget_of_dsep
    combinedVertex (Or.inl rfl) (relationEnv demoTable)
    scopeHandle worldHandle outsideHandle
  exact outside_premise_accepted

/-- A supported outside-scope rewrite leaves every counting state unchanged
at the represented query value. -/
theorem outside_guard_preserves_count (state : CountState) :
    countingCombined.core.extract
      (countingCombined.forget singletonX state) "y" =
      countingCombined.core.extract state "y" := by
  apply returned_row_preserves_counted_query demoTable scopeHandle outsideHandle
    singletonX "y" state
  · rfl
  · rfl
  · rw [outside_row_returned]
    simp

/-- The rejected inside-scope case really can change an observation. -/
theorem inside_guard_would_change_count :
    countingCombined.core.extract
        (countingCombined.forget singletonX (countingCore.world "x")) "x" ≠
      countingCombined.core.extract (countingCore.world "x") "x" := by
  decide +kernel

#print axioms returned_row_preserves_counted_query
#print axioms guarded_forget_step_and_sound
#print axioms outside_guard_fires
#print axioms outside_premise_accepted
#print axioms outside_guard_preserves_count
#print axioms inside_guard_would_change_count
#print axioms inside_premise_rejected
#print axioms unknown_premise_rejected
#print axioms outside_source_typed
#print axioms outside_target_typed

end Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider
