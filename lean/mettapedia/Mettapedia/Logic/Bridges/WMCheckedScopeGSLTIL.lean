import Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
import Mettapedia.OSLF.Framework.WMCalculusCheckedScopeNativeCapability

/-!
# Checked WM guards as proof-relevant relational answers

A successful authored `outsideScope` premise produces a capability receipt in
the existing relational internal language. The receipt retains both the scope
certificate and the exact extracted answer. Rejected in-scope requests have no
receipt, so this partial interface cannot be represented by a total answer
function. The connection is through decoded semantic values; it does not
identify the guarded WM language with the core WM language.
-/


set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMCheckedScopeGSLTIL

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider
open Mettapedia.OSLF.Framework.WMCalculusCheckedScopeNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
open Mettapedia.GSLT.RelationPresentation

/-- Premise success retains a support proof and the *actual* WM answer in the
relational fibre, rather than discarding the guard as a Boolean side effect. -/
theorem checked_premise_receipt {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider
      Scope Query reading.inScope)
    (lang : LanguageDef)
    (scopeHandle worldHandle queryHandle : Pattern)
    (scope : Scope) (query : Query) (state : State)
    (scopeDecode : lookupHandle
      provider.handles.scopes scopeHandle = some scope)
    (queryDecode : lookupHandle
      provider.handles.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
        (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv provider) lang
        ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    Nonempty ((capabilityAnswerRelation (outsideCapability reading scope)).evidence
      (state, query) (reading.core.extract state query)) := by
  exact ⟨⟨checked_premise_supports reading provider lang
    scopeHandle worldHandle queryHandle scope query state
    scopeDecode queryDecode success, rfl⟩⟩

/-- The counting provider's accepted outside query has a concrete relational
answer receipt, not merely a possible one conditional on a hypothetical row. -/
theorem counting_outside_receipt :
    Nonempty ((capabilityAnswerRelation
      (outsideCapability countingCombined singletonX)).evidence
        (countingCore.world "x", "y")
        (countingCombined.core.extract (countingCore.world "x") "y")) := by
  apply checked_premise_receipt countingCombined (checkedProvider demoTable)
    (wmExtVertexLanguageDefGuarded combinedVertex)
    scopeHandle worldHandle outsideHandle singletonX "y"
    (countingCore.world "x")
  · rfl
  · rfl
  · exact outside_premise_accepted

/-- The in-scope query has no receipt at any putative answer. -/
theorem counting_inside_no_receipt (answer : Nat) :
    ¬ Nonempty ((capabilityAnswerRelation
      (outsideCapability countingCombined singletonX)).evidence
        (countingCore.world "x", "x") answer) := by
  exact no_receipt_of_unsupported
    (outsideCapability countingCombined singletonX)
    (countingCore.world "x", "x")
    counting_inside_unsupported answer

/-- The in-scope counterexample prevents treating the checked provider as a
total functional GSLT-IL representation. -/
theorem counting_scope_not_totally_representable :
    ¬ Nonempty (Mettapedia.GSLT.RelationPresentation.Rel.Representation
      (capabilityAnswerRelation
        (outsideCapability countingCombined singletonX))) := by
  intro represented
  have allSupported :=
    (representable_iff_all_supported
      (outsideCapability countingCombined singletonX)).1 represented
  exact counting_inside_unsupported
    (allSupported (countingCore.world "x", "x"))

#print axioms checked_premise_receipt
#print axioms counting_outside_receipt
#print axioms counting_inside_no_receipt
#print axioms counting_scope_not_totally_representable

end Mettapedia.Logic.Bridges.WMCheckedScopeGSLTIL
