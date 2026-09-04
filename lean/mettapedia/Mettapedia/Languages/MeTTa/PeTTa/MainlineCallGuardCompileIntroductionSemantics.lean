import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileOccurrenceInstantiation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileFormationSemantics
import Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroductionSemantics

/-!
# Guarded introduction semantics for the cold PeTTa call guard

Every selected call-guard occurrence is an authored rewrite root.  Its rely
telescope is therefore empty, while its endpoint variables and exact ordered
guard row remain explicit.  This module proves introduction soundness at that
boundary.

One source match, one retained guard-context witness, and typing of the
structurally reconstructed target produce membership in the independently
defined occurrence-indexed modal former.  Generated derivability and checker
acceptance do not occur in this construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileIntroductionSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ContextualInferenceSemantics
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.ContextualFamilyApplication
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroductionSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceInstantiation
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedFormationSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileGuardedContextSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileOccurrenceInstantiation

/-- One exact selected star/box occurrence of the cold compiler. -/
abbrev Occurrence :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

/-- All selected call-guard occurrences are roots and hence have no rely
variables. -/
theorem selected_bindings_eq_nil (slot : Occurrence) :
    bindingsAt demand slot = [] := by
  rw [bindingsAt, typingAt_eq_rootTyping]
  exact rootTyping_bindings_eq_nil _

/-- The left endpoint of every selected cold transition lies in the exact
matching fragment. -/
theorem root_left_isMatchCorrect
    (index : Fin coldSource.language.rewrites.length) :
    Pattern.isMatchCorrect (rootTyping index).site.rewrite.left = true := by
  fin_cases index <;> decide +kernel

/-- A genuine root activation reconstructs its source state from the one
matcher environment carried by that activation. -/
theorem activation_focus_eq_before
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) :
    applyBindings environment.bindings (typingAt demand slot).site.focus =
      before := by
  have matched := environment.matched
  rw [matchPatternForRule_eq_syntactic] at matched
  have reconstructed := matchPattern_correct matched (by
    rw [typingAt_eq_rootTyping]
    exact root_left_isMatchCorrect _)
  have focusEq : (typingAt demand slot).site.focus =
      (typingAt demand slot).site.rewrite.left := by
    rw [typingAt_eq_rootTyping]
    simp [rootTyping, DisplayedRewriteSite.root,
      DisplayedRewriteSite.rewrite]
  rw [focusEq]
  exact reconstructed

/-- Filling a selected root context does not add a surrounding constructor.
The impossible rely row contributes no binding. -/
theorem displayedSource_eq_focus (slot : Occurrence)
    (values : RelyRow (typingAt demand slot)) (focus : Pattern) :
    displayedSource (typingAt demand slot) values focus = focus := by
  have contextHole : (typingAt demand slot).site.context = .hole := by
    rw [typingAt_eq_rootTyping]
    rfl
  exact displayedSource_of_context_eq_hole _ _ _ contextHole

/-- Every rely row at a selected root has the unique empty ordered list view. -/
theorem rowList_eq_nil (slot : Occurrence)
    (values : RelyRow (typingAt demand slot)) :
    rowList values = [] := by
  apply List.eq_nil_of_length_eq_zero
  have empty : DisplayedContextProfile.bindings (typingAt demand slot) = [] :=
    selected_bindings_eq_nil slot
  simpa [rowList, List.length_ofFn] using congrArg List.length empty

/-- The open semantic modal former corresponding to one selected root and a
chosen result family.  The syntactic star/box profile remains in the indexed
occurrence; it does not select behavioral direction. -/
def rootFormer (slot : Occurrence) (resultFamily : Pattern) :
    ModalFormer (occurrenceAt demand slot) where
  relyTypes := (schemaFormationView demand slot).relyTypes
  resultFamily := resultFamily

/-- A selected root has no rely typing obligations. -/
theorem rootRelyValuesTyped (model : CarrierModel) (slot : Occurrence)
    (values : RelyRow (typingAt demand slot)) :
    RelyValuesTyped model (typingAt demand slot)
      (rootFormer slot (.fvar "result-family")).relyTypes values := by
  intro index
  have empty : DisplayedContextProfile.bindings (typingAt demand slot) = [] :=
    selected_bindings_eq_nil slot
  have lengthZero :
      (DisplayedContextProfile.bindings (typingAt demand slot)).length = 0 :=
    by simpa using congrArg List.length empty
  have impossible := index.isLt
  omega

/-! ## Exact generated-row selection -/

/-- Every selected cold occurrence retrieves the exact guarded introduction
row emitted by the shared generator.  This connects the source-indexed
semantic family below to the rule the generic checker actually selects. -/
theorem generated_introductionRule_lookup (slot : Occurrence) :
    generated.1.lookupRule?
        (ContextualInference.lowerRule
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
            guardProfile slot)).id =
      some (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot)) := by
  apply lookupRule?_eq_some_of_mem generated
  exact introductionRule_mem_definition demand supportSeparated guardProfile slot

/-- The generated introduction row has a name-unique formal vector, inherited
from the generator-family admission rather than recomputed from the completed
flat calculus. -/
theorem generated_introductionFormalNames_nodup (slot : Occurrence) :
    ((SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
      guardProfile slot).metavariables.map Prod.fst).Nodup := by
  simpa [SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule,
    SelectedNativeTypeSourceIndexedIntroduction.inferMetavariables]
    using (occurrenceAdmission slot).introduction.occurrenceNamesNodup

/-- Every private endpoint coordinate is present in the generated
introduction row.  The source-bound premise is proved once for the authored
cold language and transported through the generic retained-context theorem. -/
theorem generated_introductionEndpoint_declared (slot : Occurrence) :
    ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot).metavariables := by
  exact introductionRule_declares_endpoint guardProfile slot
    (selected_endpoint_sourceBound slot)

/-- Any checker application selecting one generated introduction row
reconstructs one proof-relevant checker/source endpoint bridge.  The bridge
retains the actual decoded checker binding row and pointwise equality to the
single source endpoint environment; it cannot be assembled from unrelated
rule applications. -/
theorem generated_introductionApplication_endpoint
    (slot : Occurrence) {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (ruleId : ruleInstance.ruleId =
      (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot)).id)
    (application : RuleApplication generated ruleInstance premises conclusion) :
    Nonempty
      (CheckerEndpointInstantiation demand slot
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot).metavariables ruleInstance.arguments) := by
  rcases application with
    ⟨rule, lookup, argumentsValid, _sideConditionsValid,
      _premisesInstantiate, _conclusionInstantiates⟩
  let expected := ContextualInference.lowerRule
    (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
      guardProfile slot)
  have lookupActual : generated.1.lookupRule? expected.id = some rule := by
    simpa [expected, ruleId] using lookup
  have lookupExpected : generated.1.lookupRule? expected.id = some expected := by
    simpa [expected] using generated_introductionRule_lookup slot
  have ruleEq : rule = expected :=
    Option.some.inj (lookupActual.symm.trans lookupExpected)
  subst rule
  simpa [expected, ContextualInference.lowerRule] using
    (CheckerEndpointInstantiation.exists_of_arguments
      expected.metavariables ruleInstance.arguments argumentsValid
      (by simpa [expected, ContextualInference.lowerRule] using
        generated_introductionFormalNames_nodup slot)
      (by simpa [expected, ContextualInference.lowerRule] using
        generated_introductionEndpoint_declared slot))

/-- The coherent source endpoint reconstructed from an actual generated
introduction application agrees pointwise with the checker's own positional
lookup.  This is the exact value equation consumed by the grounded variable
context semantics; it does not inspect the rule's conclusion or any reference
executor. -/
theorem generated_introductionApplication_endpoint_lookup
    (slot : Occurrence) {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (ruleId : ruleInstance.ruleId =
      (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot)).id)
    (application : RuleApplication generated ruleInstance premises conclusion) :
    ∃ instantiation :
        CheckerEndpointInstantiation demand slot
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
            guardProfile slot).metavariables ruleInstance.arguments,
      ∀ name ∈ endpointVariableNames demand slot,
        Bindings.lookup instantiation.endpoint.bindings name =
          lookupArgumentAt?
            (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
              guardProfile slot).metavariables
            ruleInstance.arguments (renameVariable demand slot name) 0 := by
  obtain ⟨instantiation⟩ :=
    generated_introductionApplication_endpoint slot ruleId application
  refine ⟨instantiation, ?_⟩
  intro name member
  exact instantiation.lookupArgument
    (generated_introductionFormalNames_nodup slot)
    (generated_introductionEndpoint_declared slot) member

/-- An actual application of the generated M-Intro row determines one
authentic source matcher activation.  The construction follows the exact
stored rule and actual checker arguments; it does not inspect child proofs or
the rule conclusion. -/
theorem generated_introductionApplication_activation
    (slot : Occurrence) {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (ruleId : ruleInstance.ruleId =
      (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot)).id)
    (application : RuleApplication generated ruleInstance premises conclusion) :
    Nonempty
      (CheckerActivation slot
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot).metavariables ruleInstance.arguments) := by
  obtain ⟨instantiation⟩ :=
    generated_introductionApplication_endpoint slot ruleId application
  exact CheckerActivation.exists_of_endpoint slot _ _ instantiation

/-- Guard-retaining M-Intro is semantically sound for every selected PeTTa
root.  Its conclusion receives a genuine exact-occurrence witness from the
same activation whose ordered guard evidence remains in the conclusion
context. -/
theorem guardedIntroduction_family_sound
    (model : CarrierModel) (slot : Occurrence) {before : Pattern}
    (environment : ActivationEnvironment slot before)
    (guardSupport :
      ContextSatisfies (guardModel slot before) environment
        (guardedConclusionRelationContext guardProfile slot))
    (resultFamily : Pattern)
    (bodyTyped :
      model.Typed (typingAt demand slot).rewriteType
        (applyBindingsForRule language
          (typingAt demand slot).site.rewrite environment.bindings)
        resultFamily) :
    (rootFormer slot resultFamily).Member model relationEnv
      (applyBindings environment.bindings (typingAt demand slot).site.focus) := by
  refine ⟨supportSeparated slot, ?_⟩
  intro values _valuesTyped
  let after := applyBindingsForRule language
    (typingAt demand slot).site.rewrite environment.bindings
  refine ⟨after, resultFamily, ?_, ?_, bodyTyped⟩
  · change OccursAt relationEnv (typingAt demand slot)
      (displayedSource (typingAt demand slot) values
        (applyBindings environment.bindings
          (typingAt demand slot).site.focus)) after
    rw [displayedSource_eq_focus,
      activation_focus_eq_before environment]
    exact
      (guardedSupportOccursAt_iff_occurrenceMeaning slot before after).mp
        ⟨environment, guardSupport, rfl⟩
  · change Denotes resultFamily (rowList values) resultFamily
    rw [show rowList values = [] from rowList_eq_nil slot values]
    exact ⟨resultFamily, rfl, rfl⟩

/-- Crown application-level soundness theorem for generated M-Intro.  One
actual checker application exposes a semantic realizer at its own endpoint
assignment: independent truth of the exact ordered guard row and independent
typing of the reconstructed target yield membership in the displayed modal
former.

The checker supplies only the coherent valuation and authentic source match.
It supplies neither guard truth nor target typing, and the generated calculus
does not define the modal meaning. -/
theorem generated_introductionApplication_semanticRealizer
    (model : CarrierModel) (slot : Occurrence)
    {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (ruleId : ruleInstance.ruleId =
      (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot)).id)
    (application : RuleApplication generated ruleInstance premises conclusion) :
    ∃ activation : CheckerActivation slot
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot).metavariables ruleInstance.arguments,
      GroundMeanings guardProfile relationEnv slot
          activation.instantiation.endpoint.bindings →
        ∀ resultFamily : Pattern,
          model.Typed (typingAt demand slot).rewriteType
              (applyBindingsForRule language
                (typingAt demand slot).site.rewrite
                activation.instantiation.endpoint.bindings)
              resultFamily →
            (rootFormer slot resultFamily).Member model relationEnv
              (applyBindings activation.instantiation.endpoint.bindings
                (typingAt demand slot).site.rewrite.left) := by
  obtain ⟨activation⟩ :=
    generated_introductionApplication_activation slot ruleId application
  refine ⟨activation, ?_⟩
  intro endpointMeanings resultFamily endpointBodyTyped
  have environmentMeanings :
      GroundMeanings guardProfile relationEnv slot
        activation.environment.bindings :=
    (CheckerActivation.groundMeanings_iff slot activation).mp endpointMeanings
  have guardSupport :
      ContextSatisfies
        (guardModel slot
          (applyBindings activation.instantiation.endpoint.bindings
            (typingAt demand slot).site.rewrite.left))
        activation.environment
        (guardedConclusionRelationContext guardProfile slot) :=
    (guardContextSatisfies_iff_groundMeanings activation.environment).mpr
      environmentMeanings
  have environmentBodyTyped :
      model.Typed (typingAt demand slot).rewriteType
        (applyBindingsForRule language
          (typingAt demand slot).site.rewrite activation.environment.bindings)
        resultFamily := by
    rw [← CheckerActivation.targetForRule_eq slot activation]
    exact endpointBodyTyped
  have member := guardedIntroduction_family_sound model slot
    activation.environment guardSupport resultFamily environmentBodyTyped
  rw [activation_focus_eq_before activation.environment] at member
  exact member

/-! ## Negative control -/

/-- Without the retained guard context, matching and target typing alone do
not manufacture the exact occurrence evidence required by modal membership. -/
theorem no_guard_support_no_occurrence
    (slot : Occurrence) (before after : Pattern)
    (blocked : ∀ environment : ActivationEnvironment slot before,
      ¬ ContextSatisfies (guardModel slot before) environment
        (guardedConclusionRelationContext guardProfile slot)) :
    ¬ GuardedSupportOccursAt slot before after := by
  rintro ⟨environment, support, _target⟩
  exact blocked environment support

/-! ## Discriminating controls -/

/-- A deliberately permissive carrier model isolates occurrence support as
the load-bearing coordinate of modal introduction. -/
def permissiveCarrierModel : CarrierModel where
  universeObject := fun _carrier code =>
    .apply (match code with | .star => "star" | .box => "box") []
  Typed := fun _carrier _term _type => True
  starTypedBox := by simp

/-- Positive control: one genuinely supported guarded source activation
inhabits the exact occurrence-indexed modal former. -/
theorem guardedSupport_gives_modal_member
    (slot : Occurrence) (before after resultFamily : Pattern)
    (supported : GuardedSupportOccursAt slot before after) :
    (rootFormer slot resultFamily).Member permissiveCarrierModel relationEnv
      before := by
  rcases supported with ⟨environment, guardSupport, targetEq⟩
  have member := guardedIntroduction_family_sound permissiveCarrierModel slot
    environment guardSupport resultFamily (by trivial)
  rw [activation_focus_eq_before environment] at member
  exact member

/-- Regression canary for the root displayed-context boundary: even an
explicit substitution node supplied as runtime data remains untouched. -/
theorem root_displayedSource_preserves_explicit_substitution
    (slot : Occurrence) (values : RelyRow (typingAt demand slot))
    (body replacement : Pattern) :
    displayedSource (typingAt demand slot) values (.subst body replacement) =
      .subst body replacement :=
  displayedSource_eq_focus slot values _

#print axioms selected_bindings_eq_nil
#print axioms root_left_isMatchCorrect
#print axioms activation_focus_eq_before
#print axioms displayedSource_eq_focus
#print axioms rowList_eq_nil
#print axioms generated_introductionRule_lookup
#print axioms generated_introductionFormalNames_nodup
#print axioms generated_introductionEndpoint_declared
#print axioms generated_introductionApplication_endpoint
#print axioms generated_introductionApplication_endpoint_lookup
#print axioms generated_introductionApplication_activation
#print axioms guardedIntroduction_family_sound
#print axioms generated_introductionApplication_semanticRealizer
#print axioms no_guard_support_no_occurrence
#print axioms guardedSupport_gives_modal_member
#print axioms root_displayedSource_preserves_explicit_substitution

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileIntroductionSemantics
