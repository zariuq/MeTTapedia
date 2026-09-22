import Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider
import Mettapedia.OSLF.Framework.WMCalculusNativeCapability

/-!
# Checked scope decisions as native supported-answer capabilities

A semantic scope filters queries independently of the current state. This is
an instance of the existing WM capability interface over the core reading.
Successful checked `outsideScope` premises therefore select actual members
of its dependent answer graph. The graph remains in the established core-WM
presheaf category; this does not identify the combined guarded language with
the core language or interpret arbitrary raw patterns.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCheckedScopeNativeCapability

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusNativeAnswers
open Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider
open Mettapedia.GSLT.Topos

set_option autoImplicit false

private abbrev CoreLanguage : LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

/-- Holding a scope fixed, its outside queries form an extensional WM
capability: no state distinction can change whether the query is supported. -/
def outsideCapability {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (scope : Scope) : WMCapability reading.core where
  supports := fun _ query => ¬ reading.inScope scope query
  respectsAgree := by
    intro first second query agreement
    rfl

/-- Successful checked premise execution provides support in the existing
native capability, for every current state. -/
theorem checked_premise_supports {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : WMCalculusCheckedScopeRelationProvider.CheckedProvider
      Scope Query reading.inScope)
    (lang : LanguageDef)
    (scopeHandle worldHandle queryHandle : Pattern)
    (scope : Scope) (query : Query) (state : State)
    (scopeDecode : WMCalculusCheckedScopeRelationProvider.lookupHandle
      provider.handles.scopes scopeHandle = some scope)
    (queryDecode : WMCalculusCheckedScopeRelationProvider.lookupHandle
      provider.handles.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
        (WMCalculusCheckedScopeRelationProvider.relationEnv provider) lang
        ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    (outsideCapability reading scope).supports state query :=
  WMCalculusCheckedScopeRelationProvider.premise_success_implies_outside
    provider lang scopeHandle worldHandle queryHandle scope query
    scopeDecode queryDecode success

/-- The checked runtime answer inhabits the existing dependent evidence
graph at every core-language presheaf stage. -/
theorem checked_premise_native_answer {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : WMCalculusCheckedScopeRelationProvider.CheckedProvider
      Scope Query reading.inScope)
    (lang : LanguageDef)
    (scopeHandle worldHandle queryHandle : Pattern)
    (scope : Scope) (query : Query) (state : State)
    (scopeDecode : WMCalculusCheckedScopeRelationProvider.lookupHandle
      provider.handles.scopes scopeHandle = some scope)
    (queryDecode : WMCalculusCheckedScopeRelationProvider.lookupHandle
      provider.handles.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
        (WMCalculusCheckedScopeRelationProvider.relationEnv provider) lang
        ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)])
    (X : Opposite (ConstructorObj CoreLanguage)) :
    ((state, query), reading.core.extract state query) ∈
      (supportedGraph (outsideCapability reading scope)).obj X := by
  exact ⟨checked_premise_supports reading provider lang
      scopeHandle worldHandle queryHandle scope query state
      scopeDecode queryDecode success, rfl⟩

/-- The checked answer also lies over the exact Σ-image of supported
requests. This reuses the existing dependent comprehension theorem. -/
theorem checked_premise_sigma_support {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : WMCalculusCheckedScopeRelationProvider.CheckedProvider
      Scope Query reading.inScope)
    (lang : LanguageDef)
    (scopeHandle worldHandle queryHandle : Pattern)
    (scope : Scope) (query : Query) (state : State)
    (scopeDecode : WMCalculusCheckedScopeRelationProvider.lookupHandle
      provider.handles.scopes scopeHandle = some scope)
    (queryDecode : WMCalculusCheckedScopeRelationProvider.lookupHandle
      provider.handles.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
        (WMCalculusCheckedScopeRelationProvider.relationEnv provider) lang
        ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)])
    (X : Opposite (ConstructorObj CoreLanguage)) :
    (state, query) ∈
      ((presheafChangeOfBase (ConstructorObj CoreLanguage)).directImage
        (answerProjection State Query Ev)
        (supportedGraph (outsideCapability reading scope))).obj X := by
  rw [supportedGraph_sigma_exact]
  exact checked_premise_supports reading provider lang
    scopeHandle worldHandle queryHandle scope query state
    scopeDecode queryDecode success

theorem counting_outside_supported :
    (outsideCapability countingCombined singletonX).supports
      (countingCore.world "x") "y" := by
  change ¬ singletonX "y" = true
  decide +kernel

theorem counting_inside_unsupported :
    ¬ (outsideCapability countingCombined singletonX).supports
      (countingCore.world "x") "x" := by
  change ¬ ¬ singletonX "x" = true
  decide +kernel

/-- The concrete accepted premise yields a real dependent answer witness,
not only a parametric implication about hypothetical provider success. -/
theorem counting_provider_native_answer
    (X : Opposite (ConstructorObj CoreLanguage)) :
    ((countingCore.world "x", "y"),
      countingCombined.core.extract (countingCore.world "x") "y") ∈
      (supportedGraph (outsideCapability countingCombined singletonX)).obj X := by
  apply checked_premise_native_answer countingCombined
    (checkedProvider demoTable)
    (wmExtVertexLanguageDefGuarded combinedVertex)
    scopeHandle worldHandle outsideHandle
    singletonX "y" (countingCore.world "x")
  · rfl
  · rfl
  · exact outside_premise_accepted

theorem counting_provider_sigma_support
    (X : Opposite (ConstructorObj CoreLanguage)) :
    (countingCore.world "x", "y") ∈
      ((presheafChangeOfBase (ConstructorObj CoreLanguage)).directImage
        (answerProjection CountState String Nat)
        (supportedGraph (outsideCapability countingCombined singletonX))).obj X := by
  apply checked_premise_sigma_support countingCombined
    (checkedProvider demoTable)
    (wmExtVertexLanguageDefGuarded combinedVertex)
    scopeHandle worldHandle outsideHandle
    singletonX "y" (countingCore.world "x")
  · rfl
  · rfl
  · exact outside_premise_accepted

/-- This native dependent family is genuinely selective, not the total WM
answer graph with a new name. -/
theorem counting_scope_support_not_top
    (X : Opposite (ConstructorObj CoreLanguage)) :
    supportPredicate (outsideCapability countingCombined singletonX) ≠ ⊤ := by
  exact supportPredicate_ne_top_of_unsupported
    (outsideCapability countingCombined singletonX) X
    (countingCore.world "x") "x" counting_inside_unsupported

#print axioms outsideCapability
#print axioms checked_premise_supports
#print axioms checked_premise_native_answer
#print axioms checked_premise_sigma_support
#print axioms counting_scope_support_not_top
#print axioms counting_provider_native_answer
#print axioms counting_provider_sigma_support

end Mettapedia.OSLF.Framework.WMCalculusCheckedScopeNativeCapability
