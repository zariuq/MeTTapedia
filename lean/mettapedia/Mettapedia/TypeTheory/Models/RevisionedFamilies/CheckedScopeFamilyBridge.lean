import Mettapedia.Logic.Bridges.WMCheckedScopeGSLTIL
import Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityPiRepresentability
import Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
import Mettapedia.OSLF.Framework.WMCalculusGuardedExecutableOccurrence
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
import Mettapedia.GSLT.LanguageDef.MultiRewriteSchematic

/-!
# Checked WM guards in Prime's observable dependent families

An actual accepted `outsideScope` premise inhabits the existing observable
receipt family of the world-model capability. The same counting backend has
an in-scope request with no inhabitant, so neither a total dependent answer
section nor a total functional representation is licensed. This is an
external semantic capability over the staged families families CwF; no authored
Prime former or computation rule is added here.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedScopeFamilyBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
open Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider
open Mettapedia.OSLF.Framework.WMCalculusCheckedScopeNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusGuardedExecutableOccurrence
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.PremiseAwareOccurrence
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Logic.Bridges.WMCheckedScopeGSLTIL
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
open Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
open Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityPiRepresentability
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
open Mettapedia.GSLT.LanguageDef.MultiRewriteExtension
open Mettapedia.GSLT.LanguageDef.MultiRewriteSchematic

/-- A checked guard yields a dependent receipt over the observable state
class, retaining the support proof and the exact extracted evidence. -/
theorem checked_premise_observable_receipt {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    (lang : LanguageDef)
    (scopeHandle worldHandle queryHandle : Pattern)
    (scope : Scope) (query : Query) (state : State)
    (scopeDecode : lookupHandle provider.handles.scopes scopeHandle = some scope)
    (queryDecode : lookupHandle provider.handles.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
        (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
          provider) lang ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    Nonempty (observableReceiptFamily (outsideCapability reading scope)
      (reading.core.extract state query)
      (classOf reading.core state, query)) := by
  obtain ⟨receipt⟩ := checked_premise_receipt reading provider lang
    scopeHandle worldHandle queryHandle scope query state
    scopeDecode queryDecode success
  exact ⟨(rawReceiptEquiv (outsideCapability reading scope)
    (state, query) (reading.core.extract state query)) receipt⟩

/-- One actual checked premise simultaneously licenses the canonical OSLF
step, validates the reading's guarded observation equation, and inhabits the
corresponding dependent answer fibre. The handles are related to semantic
values only by the explicit decoding hypotheses. -/
theorem checked_guard_operational_family_coherence
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    (scopeHandle worldHandle queryHandle : Pattern)
    (scope : Scope) (query : Query) (state : State)
    (scopeDecode : lookupHandle provider.handles.scopes scopeHandle = some scope)
    (queryDecode : lookupHandle provider.handles.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
        (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
          provider)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    langSemanticReducesUsing
        (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
          provider)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        (pExtract (pForget scopeHandle worldHandle) queryHandle)
        (pExtract worldHandle queryHandle) ∧
      reading.core.extract (reading.forget scope state) query =
        reading.core.extract state query ∧
      Nonempty (observableReceiptFamily (outsideCapability reading scope)
        (reading.core.extract state query)
        (classOf reading.core state, query)) := by
  have supported := checked_premise_supports reading provider
    (wmExtVertexLanguageDefGuarded combinedVertex)
    scopeHandle worldHandle queryHandle scope query state
    scopeDecode queryDecode success
  refine ⟨forgetOutside_raw_of_guard
      (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
        provider)
      scopeHandle worldHandle queryHandle success,
    reading.forgetOutside supported, ?_⟩
  exact checked_premise_observable_receipt reading provider
    (wmExtVertexLanguageDefGuarded combinedVertex)
    scopeHandle worldHandle queryHandle scope query state
    scopeDecode queryDecode success

/-- The same accepted provider row is visible as a finite-fuel executable
occurrence with the authored rule name, reaches the exact OSLF target type,
and inhabits Prime's observable answer fibre. -/
theorem checked_guard_executable_native_prime_coherence
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    (scopeHandle worldHandle queryHandle : Pattern)
    (scope : Scope) (query : Query) (state : State)
    (scopeDecode : lookupHandle provider.handles.scopes scopeHandle = some scope)
    (queryDecode : lookupHandle provider.handles.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
        (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
          provider)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    ∃ occurrence ∈ rewriteAtOccurrences
        (engineBasePremises
          (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
            provider))
        (wmExtVertexLanguageDefGuarded combinedVertex) 1
        (pExtract (pForget scopeHandle worldHandle) queryHandle),
      occurrence.target = pExtract worldHandle queryHandle ∧
      occurrence.ruleName = "WM_ForgetOutside_Guarded" ∧
      langDiamondUsing
        (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
          provider)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        (equationClassNativeType
          (S := langGSLTUsing
            (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
              provider)
            (wmExtVertexLanguageDefGuarded combinedVertex))
          (pExtract worldHandle queryHandle)).pred
        (pExtract (pForget scopeHandle worldHandle) queryHandle) ∧
      Nonempty (observableReceiptFamily (outsideCapability reading scope)
        (reading.core.extract state query)
        (classOf reading.core state, query)) := by
  obtain ⟨occurrence, member, target, ruleName⟩ :=
    checked_forget_named_occurrence
      (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
        provider)
      scopeHandle worldHandle queryHandle success
  have diamond : langDiamondUsing
      (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
        provider)
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (equationClassNativeType
        (S := langGSLTUsing
          (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
            provider)
          (wmExtVertexLanguageDefGuarded combinedVertex))
        (pExtract worldHandle queryHandle)).pred
      (pExtract (pForget scopeHandle worldHandle) queryHandle) := by
    apply (langDiamondUsing_spec
      (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
        provider)
      (wmExtVertexLanguageDefGuarded combinedVertex) _ _).2
    refine ⟨pExtract worldHandle queryHandle,
      forgetOutside_raw_of_guard
        (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
          provider)
        scopeHandle worldHandle queryHandle success, ?_⟩
    exact (langGSLTUsing
      (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
        provider)
      (wmExtVertexLanguageDefGuarded combinedVertex)).equations.iseqv.refl _
  exact ⟨occurrence, member, target, ruleName,
    diamond,
    checked_premise_observable_receipt reading provider
      (wmExtVertexLanguageDefGuarded combinedVertex)
      scopeHandle worldHandle queryHandle scope query state
      scopeDecode queryDecode success⟩

/-- The checked guarded step inhabits the generated OSLF diamond of the
contractum's exact equation-class native type. This records the target of
the operational observation, not merely existence of some reduction. -/
theorem checked_guard_target_native_diamond
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    (scopeHandle worldHandle queryHandle : Pattern)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
        (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
          provider)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    langDiamondUsing
      (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
        provider)
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (equationClassNativeType
        (S := langGSLTUsing
          (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
            provider)
          (wmExtVertexLanguageDefGuarded combinedVertex))
        (pExtract worldHandle queryHandle)).pred
      (pExtract (pForget scopeHandle worldHandle) queryHandle) := by
  apply (langDiamondUsing_spec
    (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
      provider)
    (wmExtVertexLanguageDefGuarded combinedVertex) _ _).2
  refine ⟨pExtract worldHandle queryHandle,
    forgetOutside_raw_of_guard
      (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
        provider)
      scopeHandle worldHandle queryHandle success, ?_⟩
  exact (langGSLTUsing
    (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
      provider)
    (wmExtVertexLanguageDefGuarded combinedVertex)).equations.iseqv.refl _

/-- The same checked unary action survives admission of arbitrary atomic
n-ary joins, provided that library contributes no competing unary
declaration. The resulting window step and dependent receipt come from the
same premise success, not from a literal-pattern multi-rewrite shortcut. -/
theorem checked_guard_schematic_window_and_receipt
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    (library : AdmittedLibrary) (nonUnary : NoUnaryDeclarations library)
    (scopeHandle worldHandle queryHandle : Pattern)
    (scope : Scope) (query : Query) (state : State)
    (scopeDecode : lookupHandle provider.handles.scopes scopeHandle = some scope)
    (queryDecode : lookupHandle provider.handles.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
        (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
          provider)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    (schematicGSLTUsing
        (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
          provider)
        (wmExtVertexLanguageDefGuarded combinedVertex) library).Step
      [pExtract (pForget scopeHandle worldHandle) queryHandle]
      [pExtract worldHandle queryHandle] ∧
    Nonempty (observableReceiptFamily (outsideCapability reading scope)
      (reading.core.extract state query)
      (classOf reading.core state, query)) := by
  obtain ⟨canonicalStep, _, receipt⟩ :=
    checked_guard_operational_family_coherence reading provider
      scopeHandle worldHandle queryHandle scope query state
      scopeDecode queryDecode success
  exact ⟨(singleton_step_iff
    (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
      provider)
    (wmExtVertexLanguageDefGuarded combinedVertex) library nonUnary _ _).2
      canonicalStep, receipt⟩

/-- The checked outside-scope result can execute under one authored Combine
context. Its semantic evidence is unchanged under that context, and the
same provider row still inhabits Prime's observable receipt family. -/
theorem checked_guard_combine_context_and_receipt
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    (scopeHandle worldHandle queryHandle otherTerm : Pattern)
    (scope : Scope) (query : Query) (state : State) (otherEvidence : Ev)
    (scopeDecode : lookupHandle provider.handles.scopes scopeHandle = some scope)
    (queryDecode : lookupHandle provider.handles.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
        (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
          provider)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    (∃ occurrence ∈ rewriteAtOccurrences
        (engineBasePremises
          (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
            provider))
        (wmExtVertexLanguageDefGuardedWithCong combinedVertex) 2
        (pCombine (pExtract (pForget scopeHandle worldHandle) queryHandle)
          otherTerm),
      occurrence.target = pCombine (pExtract worldHandle queryHandle)
        otherTerm ∧ occurrence.ruleName = "WM_CombineCongLeft") ∧
      reading.core.combine
          (reading.core.extract (reading.forget scope state) query)
          otherEvidence =
        reading.core.combine (reading.core.extract state query)
          otherEvidence ∧
      Nonempty (observableReceiptFamily (outsideCapability reading scope)
        (reading.core.extract state query)
        (classOf reading.core state, query)) := by
  obtain ⟨_, sameEvidence, receipt⟩ :=
    checked_guard_operational_family_coherence reading provider
      scopeHandle worldHandle queryHandle scope query state
      scopeDecode queryDecode success
  exact ⟨checked_forget_under_combine_left_occurs
      (Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider.relationEnv
        provider)
      scopeHandle worldHandle queryHandle otherTerm success,
    congrArg (fun evidence => reading.core.combine evidence otherEvidence)
      sameEvidence,
    receipt⟩

/-- A concrete accepted provider row inhabits Extensional dependent
family, via the retained GSLT-IL certificate. -/
theorem counting_outside_family_inhabited :
    Nonempty (observableReceiptFamily
      (outsideCapability countingCombined singletonX)
      (countingCombined.core.extract (countingCore.world "x") "y")
      (classOf countingCombined.core (countingCore.world "x"), "y")) := by
  apply checked_premise_observable_receipt countingCombined
    (checkedProvider demoTable)
    (wmExtVertexLanguageDefGuarded combinedVertex)
    scopeHandle worldHandle outsideHandle singletonX "y"
    (countingCore.world "x")
  · rfl
  · rfl
  · exact outside_premise_accepted

/-- For the concrete counting backend, the same accepted provider result
drives operational reduction, semantic preservation, and a Prime-family
receipt for every world state. -/
theorem counting_guard_operational_family_coherence (state : CountState) :
    langSemanticReducesUsing
        (Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider.relationEnv
          demoTable)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        (pExtract (pForget scopeHandle worldHandle) outsideHandle)
        (pExtract worldHandle outsideHandle) ∧
      countingCombined.core.extract
          (countingCombined.forget singletonX state) "y" =
        countingCombined.core.extract state "y" ∧
      Nonempty (observableReceiptFamily
        (outsideCapability countingCombined singletonX)
        (countingCombined.core.extract state "y")
        (classOf countingCombined.core state, "y")) := by
  apply checked_guard_operational_family_coherence countingCombined
    (checkedProvider demoTable) scopeHandle worldHandle outsideHandle
    singletonX "y" state
  · rfl
  · rfl
  · exact outside_premise_accepted

/-- The concrete counting provider reaches its exact target equation class
in the generated OSLF modality. -/
theorem counting_guard_target_native_diamond :
    langDiamondUsing
      (Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider.relationEnv
        demoTable)
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (equationClassNativeType
        (S := langGSLTUsing
          (Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider.relationEnv
            demoTable)
          (wmExtVertexLanguageDefGuarded combinedVertex))
        (pExtract worldHandle outsideHandle)).pred
      (pExtract (pForget scopeHandle worldHandle) outsideHandle) := by
  exact checked_guard_target_native_diamond countingCombined
    (checkedProvider demoTable) scopeHandle worldHandle outsideHandle
    outside_premise_accepted

/-- The in-scope counterexample is empty in the dependent family at every
putative answer; quotienting the state does not erase the failed guard. -/
theorem counting_inside_family_empty (answer : Nat) :
    ¬ Nonempty (observableReceiptFamily
      (outsideCapability countingCombined singletonX) answer
      (classOf countingCombined.core (countingCore.world "x"), "x")) := by
  rintro ⟨receipt⟩
  exact counting_inside_no_receipt answer
    ⟨(rawReceiptEquiv (outsideCapability countingCombined singletonX)
      (countingCore.world "x", "x") answer).symm receipt⟩

/-- The checked outside query also has a route from actual authored *core*
WM state and query terms to the retained relational answer receipt. -/
theorem counting_outside_named_chain :
    Nonempty ((termCapabilityChain
      (outsideCapability countingCombined singletonX)).evidence
      (.state "x", .query "y")
      (countingCombined.core.extract (countingCore.world "x") "y")) := by
  obtain ⟨receipt⟩ := counting_outside_family_inhabited
  refine ⟨(termChainReceiptEquiv
    (outsideCapability countingCombined singletonX)
    (.state "x", .query "y") _).symm ?_⟩
  exact receipt

/-- Naming the inside query in core WM syntax does not make its partial
capability total or create an answer receipt. -/
theorem counting_inside_named_chain_empty (answer : Nat) :
    ¬ Nonempty ((termCapabilityChain
      (outsideCapability countingCombined singletonX)).evidence
      (.state "x", .query "x") answer) := by
  rintro ⟨receipt⟩
  apply counting_inside_family_empty answer
  refine ⟨?_⟩
  exact (termChainReceiptEquiv
    (outsideCapability countingCombined singletonX)
    (.state "x", .query "x") answer) receipt

/-- A successful local query does not create a global dependent answer term:
the same capability rejects an in-scope request. -/
theorem counting_scope_no_total_receipt_pi :
    ¬ Nonempty (allObservableReceiptPi
      (outsideCapability countingCombined singletonX) PUnit.unit) := by
  intro total
  exact counting_scope_not_totally_representable
    ((receiptPi_iff_semanticRepresentation
      (outsideCapability countingCombined singletonX)).mp total)

#print axioms checked_premise_observable_receipt
#print axioms checked_guard_operational_family_coherence
#print axioms checked_guard_executable_native_prime_coherence
#print axioms checked_guard_target_native_diamond
#print axioms checked_guard_schematic_window_and_receipt
#print axioms checked_guard_combine_context_and_receipt
#print axioms counting_outside_family_inhabited
#print axioms counting_guard_operational_family_coherence
#print axioms counting_guard_target_native_diamond
#print axioms counting_inside_family_empty
#print axioms counting_outside_named_chain
#print axioms counting_inside_named_chain_empty
#print axioms counting_scope_no_total_receipt_pi

end Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedScopeFamilyBridge
