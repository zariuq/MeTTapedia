import Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceInstantiation
import Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredVariableClaim
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileGuardedContextSemantics

/-!
# Occurrence-local checker instantiation for the cold PeTTa call guard

One guarded activation already owns the source match and its exact ordered
premise evidence.  This module proves that the same activation also supplies
the complete endpoint-variable environment required by generated checker
schemas.

The generic instantiation bridge knows only how to rename a covered finite
support and compile it into positional checker arguments.  PeTTa contributes
the separate source-language fact that every variable in a cold transition's
right endpoint is already supplied by its left endpoint.  Consequently one
argument vector instantiates the authored source, target, and focus patterns
without consulting a transition result or generated derivability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileOccurrenceInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CanonicalWire
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim
open Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceInstantiation
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceMatchBinding
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseProfile
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseClaim
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileBindingCoverage
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileGuardedContextSemantics

/-- One exact selected star/box occurrence of the cold compiler. -/
abbrev Occurrence :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

/-- Every right-endpoint variable of a cold compiler transition is supplied
by that transition's left endpoint.  The generic validator permits a premise
to produce a right variable; the PeTTa premise profile proves more strongly
that every such premise argument was itself source-bound. -/
theorem selected_right_sourceBound (slot : Occurrence) :
    ∀ name ∈ (typingAt demand slot).site.rewrite.right.freeFvarNames,
      name ∈ (typingAt demand slot).site.rewrite.left.freeFvarNames := by
  rw [typingAt_eq_rootTyping]
  intro name rightMember
  have rewriteMember :
      (rootTyping (rootIndexAt slot)).site.rewrite ∈ language.rewrites := by
    change language.rewrites[rootIndexAt slot] ∈ language.rewrites
    exact List.get_mem language.rewrites (rootIndexAt slot)
  have rightEraseMember :
      name ∈ (LanguageDef.patternFvarNames []
        (rootTyping (rootIndexAt slot)).site.rewrite.right).eraseDups := by
    rw [List.mem_eraseDups]
    simpa [patternFvarNames_nil] using rightMember
  have bound :=
    (transition_certificate _ rewriteMember).rightBound name rightEraseMember
  rw [patternFvarNames_nil] at bound
  rcases List.mem_append.mp bound with leftMember | premiseProduced
  · exact leftMember
  · rw [List.mem_flatMap] at premiseProduced
    obtain ⟨premise, premiseMember, nameProduced⟩ := premiseProduced
    obtain ⟨relation, arguments, premiseEq, argumentsBound⟩ :=
      rootPremises_sourceBound (rootIndexAt slot) premise premiseMember
    subst premise
    simp only [LanguageDef.premiseProducedFvarNames] at nameProduced
    rw [List.mem_flatMap] at nameProduced
    obtain ⟨argument, argumentMember, nameMember⟩ := nameProduced
    obtain ⟨sourceName, argumentEq, sourceMember⟩ :=
      argumentsBound argument argumentMember
    subst argument
    have nameEq : name = sourceName := by
      simpa [Pattern.freeFvarNames] using nameMember
    subst name
    exact sourceMember

/-- The complete endpoint support of every selected cold occurrence is
source-bound.  This is PeTTa-specific and is intentionally not assumed by the
generic occurrence-instantiation interface. -/
theorem selected_endpoint_sourceBound (slot : Occurrence) :
    ∀ name ∈ endpointVariableNames demand slot,
      name ∈ (typingAt demand slot).site.rewrite.left.freeFvarNames := by
  intro name member
  rw [mem_endpointVariableNames_iff] at member
  exact member.elim id (selected_right_sourceBound slot name)

/-- A coherent guarded activation yields the value-only endpoint environment
used by the generated checker.  Premise truth is neither added nor forgotten:
it remains in the enclosing activation while this projection carries values. -/
def activationEndpointInstantiation
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) :
    EndpointInstantiation demand slot where
  bindings := environment.bindings
  covers := by
    intro name member
    have hole : patternHoleSkeleton
        (typingAt demand slot).site.rewrite.left = true := by
      rw [typingAt_eq_rootTyping]
      exact root_left_holeSkeleton _
    have matched := environment.matched
    rw [matchPatternForRule_eq_syntactic] at matched
    exact matchPattern_holeSkeleton_covers hole environment.bindings matched
      name (selected_endpoint_sourceBound slot name member)

@[simp] theorem activationEndpointInstantiation_bindings
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) :
    (activationEndpointInstantiation environment).bindings =
      environment.bindings :=
  rfl

mutual

/-- Canonical first-order pattern shape plus complete free-variable coverage
constructs the proof-facing source/checker fragment without evaluating a
large `contains` expression. -/
theorem bindingSchemaFragment_of_patternSupported
    {formals : List (String × Nat)} {pattern : Pattern}
    (supported : patternSupported pattern = true)
    (covered : ∀ name ∈ pattern.freeFvarNames, (name, 0) ∈ formals) :
    BindingSchemaFragment formals pattern := by
  cases pattern with
  | bvar index => simp [patternSupported] at supported
  | fvar name =>
      exact .fvar (covered name (by simp [Pattern.freeFvarNames]))
  | apply constructor arguments =>
      exact .apply (bindingSchemasFragment_of_patternListSupported
        (by simpa [patternSupported] using supported)
        (fun name member => covered name (by
          simpa [Pattern.freeFvarNames] using member)))
  | lambda binder body => simp [patternSupported] at supported
  | multiLambda arity binders body => simp [patternSupported] at supported
  | subst body replacement => simp [patternSupported] at supported
  | collection collectionType elements rest =>
      simp [patternSupported] at supported

/-- List form of `bindingSchemaFragment_of_patternSupported`. -/
theorem bindingSchemasFragment_of_patternListSupported
    {formals : List (String × Nat)} {patterns : List Pattern}
    (supported : patternListSupported patterns = true)
    (covered : ∀ name ∈ patterns.flatMap Pattern.freeFvarNames,
      (name, 0) ∈ formals) :
    BindingSchemasFragment formals patterns := by
  cases patterns with
  | nil => exact .nil
  | cons head tail =>
      have parts : patternSupported head = true ∧
          patternListSupported tail = true := by
        simpa [patternListSupported] using supported
      exact .cons
        (bindingSchemaFragment_of_patternSupported parts.1
          (fun name member => covered name (by simp [member])))
        (bindingSchemasFragment_of_patternListSupported parts.2
          (fun name member => covered name (by simp [member])))

end

/-- Endpoint formals contain exactly the occurrence's endpoint names at
depth zero. -/
@[simp] theorem mem_endpointFormals_iff (slot : Occurrence) (name : String) :
    (name, 0) ∈ endpointFormals demand slot ↔
      name ∈ endpointVariableNames demand slot := by
  simp [endpointFormals]

/-- The exact argument row of every selected relation premise lies in the
source/checker instantiation fragment.  This is derived from the authored
source-boundness proof, so no generated claim or relation result contributes
to the fragment certificate. -/
theorem selected_sourceView_arguments_fragment (slot : Occurrence)
    (premise : Fin (viewsAt premiseProfile slot).length) :
    BindingSchemasFragment (endpointFormals demand slot)
      (sourceView premiseProfile slot premise).arguments := by
  have sourceBound := selected_view_sourceBound slot
    (sourceView premiseProfile slot premise) (List.get_mem _ premise)
  have fragmentOfSourceBound :
      ∀ patterns : List Pattern,
        (∀ argument ∈ patterns,
          SelectedNativeTypeBoundRelationPremise.ArgumentSourceBound
            (typingAt demand slot).site.rewrite argument) →
        BindingSchemasFragment (endpointFormals demand slot) patterns := by
    intro patterns
    induction patterns with
    | nil =>
        intro _bound
        exact .nil
    | cons argument arguments inductionHypothesis =>
        intro bound
        obtain ⟨name, argumentExact, sourceMember⟩ :=
          bound argument (by simp)
        subst argument
        apply BindingSchemasFragment.cons
        · apply BindingSchemaFragment.fvar
          rw [mem_endpointFormals_iff, mem_endpointVariableNames_iff]
          exact Or.inl sourceMember
        · exact inductionHypothesis fun other member =>
            bound other (by simp [member])
  exact fragmentOfSourceBound _ sourceBound

/-- One checker/source endpoint bridge grounds an authored premise claim
exactly at its own source binding environment.  The premise coordinate,
argument order, and duplicate argument occurrences are all preserved. -/
theorem CheckerEndpointInstantiation.instantiate_authoredClaim
    {slot : Occurrence} {formals : List (String × Nat)}
    {arguments : List Pattern}
    (instantiation :
      CheckerEndpointInstantiation demand slot formals arguments)
    (namesNodup : (formals.map Prod.fst).Nodup)
    (declared : ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈ formals)
    (premise : Fin (viewsAt premiseProfile slot).length) :
    instantiateSchema? formals arguments
        (authoredClaim premiseProfile slot premise) =
      some (groundedView premiseProfile slot premise
        instantiation.endpoint.bindings).encode := by
  have argumentsExact := instantiation.instantiate_authoredPatterns
    namesNodup declared (selected_sourceView_arguments_fragment slot premise)
  have argumentsExactAt :
      instantiateSchemasAt? formals arguments 0
          ((sourceView premiseProfile slot premise).arguments.map
            (authoredPattern demand slot)) =
        some ((sourceView premiseProfile slot premise).arguments.map
          (applyBindings instantiation.endpoint.bindings)) := by
    simpa only [instantiateSchemas?] using argumentsExact
  simp [authoredClaim, claim, authoredArguments, groundedView, View.encode,
    instantiateSchema?, instantiateSchemaAt?, argumentsExactAt]

/-- One checker/source endpoint bridge also grounds an exact authored-variable
claim at its own occurrence and binding coordinate.  Unlike an ordinary
carrier claim, the resulting constructor head retains the binding position;
two same-carrier endpoint values therefore cannot exchange evidence. -/
theorem CheckerEndpointInstantiation.instantiate_authoredVariableClaim
    {slot : Occurrence} {formals : List (String × Nat)}
    {arguments : List Pattern}
    (instantiation :
      CheckerEndpointInstantiation demand slot formals arguments)
    (namesNodup : (formals.map Prod.fst).Nodup)
    (declared : ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈ formals)
    (binding : Fin (authoredBindings demand slot).length) :
    instantiateSchema? formals arguments
        (SelectedNativeTypeAuthoredVariableClaim.authoredClaim
          demand slot binding) =
      some
        (SelectedNativeTypeAuthoredVariableClaim.groundedView
          demand slot binding instantiation.endpoint.bindings).encode := by
  have bindingNameMember :
      (SelectedNativeTypeAuthoredVariableClaim.sourceBinding
          demand slot binding).1 ∈ endpointVariableNames demand slot := by
    rw [← authoredBindingNames_of_endpointSourceBound demand slot
      (selected_endpoint_sourceBound slot)]
    exact List.mem_map.mpr ⟨_, List.get_mem _ binding, rfl⟩
  have fragment : BindingSchemaFragment (endpointFormals demand slot)
      (.fvar
        (SelectedNativeTypeAuthoredVariableClaim.sourceBinding
          demand slot binding).1) :=
    .fvar ((mem_endpointFormals_iff slot _).2 bindingNameMember)
  have valueExact := instantiation.instantiate_authoredPattern
    namesNodup declared fragment
  have valueExactAt :
      instantiateSchemaAt? formals arguments 0
          (.fvar (renameVariable demand slot
            (SelectedNativeTypeAuthoredVariableClaim.sourceBinding
              demand slot binding).1)) =
        some (applyBindings instantiation.endpoint.bindings
          (.fvar
            (SelectedNativeTypeAuthoredVariableClaim.sourceBinding
              demand slot binding).1)) := by
    simpa [instantiateSchema?, authoredPattern, Pattern.renameFVars] using
      valueExact
  have valuesExactAt :
      instantiateSchemasAt? formals arguments 0
          [.fvar (renameVariable demand slot
            (SelectedNativeTypeAuthoredVariableClaim.sourceBinding
              demand slot binding).1)] =
        some [applyBindings instantiation.endpoint.bindings
          (.fvar
            (SelectedNativeTypeAuthoredVariableClaim.sourceBinding
              demand slot binding).1)] := by
    simp [instantiateSchemasAt?, valueExactAt]
  simp [SelectedNativeTypeAuthoredVariableClaim.authoredClaim,
    SelectedNativeTypeAuthoredVariableClaim.claim,
    SelectedNativeTypeAuthoredVariableClaim.groundedView,
    SelectedNativeTypeAuthoredVariableClaim.View.encode,
    instantiateSchema?, instantiateSchemaAt?, valuesExactAt]

private theorem instantiatesListAt_of_forall₂
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schemas results : List Pattern}
    (pointwise : List.Forall₂
      (InstantiatesAt formals arguments depth) schemas results) :
    InstantiatesListAt formals arguments depth schemas results := by
  induction pointwise with
  | nil => exact .nil depth
  | cons head tail inductionHypothesis =>
      exact .cons head inductionHypothesis

/-- One checker/source endpoint bridge grounds the complete authored-variable
row position by position, preserving its exact order and multiplicity. -/
theorem CheckerEndpointInstantiation.instantiate_authoredVariableClaims
    {slot : Occurrence} {formals : List (String × Nat)}
    {arguments : List Pattern}
    (instantiation :
      CheckerEndpointInstantiation demand slot formals arguments)
    (namesNodup : (formals.map Prod.fst).Nodup)
    (declared : ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈ formals) :
    instantiateSchemas? formals arguments
        (SelectedNativeTypeAuthoredVariableClaim.authoredClaims demand slot) =
      some (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
        demand slot instantiation.endpoint.bindings) := by
  apply instantiateSchemasAt?_complete
  apply instantiatesListAt_of_forall₂
  apply List.forall₂_of_length_eq_of_get
  · simp [SelectedNativeTypeAuthoredVariableClaim.authoredClaims,
      SelectedNativeTypeAuthoredVariableClaim.groundedClaims]
  · intro index sourceBound targetBound
    let binding : Fin (authoredBindings demand slot).length :=
      ⟨index, by
        simpa [SelectedNativeTypeAuthoredVariableClaim.authoredClaims]
          using sourceBound⟩
    have exact :=
      Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileOccurrenceInstantiation.CheckerEndpointInstantiation.instantiate_authoredVariableClaim
        instantiation namesNodup declared binding
    apply instantiateSchemaAt?_sound
    simpa [instantiateSchema?,
      SelectedNativeTypeAuthoredVariableClaim.authoredClaims,
      SelectedNativeTypeAuthoredVariableClaim.groundedClaims, binding] using exact

/-- The same endpoint bridge grounds the complete ordered guard row.  The
result is computed from the source-derived premise profile and the one shared
endpoint environment; no relation answer is introduced here. -/
theorem CheckerEndpointInstantiation.instantiate_authoredGuardClaims
    {slot : Occurrence} {formals : List (String × Nat)}
    {arguments : List Pattern}
    (instantiation :
      CheckerEndpointInstantiation demand slot formals arguments)
    (namesNodup : (formals.map Prod.fst).Nodup)
    (declared : ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈ formals) :
    instantiateSchemas? formals arguments
        (authoredClaims premiseProfile slot) =
      some (SelectedNativeTypeBoundRelationClaim.groundedClaims
        premiseProfile slot instantiation.endpoint.bindings) := by
  apply instantiateSchemasAt?_complete
  apply instantiatesListAt_of_forall₂
  apply List.forall₂_of_length_eq_of_get
  · simp [authoredClaims,
      SelectedNativeTypeBoundRelationClaim.groundedClaims]
  · intro index sourceBound targetBound
    let premise : Fin (viewsAt premiseProfile slot).length :=
      ⟨index, by simpa [authoredClaims] using sourceBound⟩
    have exact :=
      Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileOccurrenceInstantiation.CheckerEndpointInstantiation.instantiate_authoredClaim
        instantiation namesNodup declared premise
    apply instantiateSchemaAt?_sound
    simpa [instantiateSchema?, authoredClaims,
      SelectedNativeTypeBoundRelationClaim.groundedClaims, premise] using exact

/-- Grounding is independent of the proof object used to certify successful
source-premise decoding.  Any profile for the same demand computes the same
authored row and receives the exact checker grounding theorem. -/
theorem CheckerEndpointInstantiation.instantiate_authoredGuardClaimsFor
    {slot : Occurrence} {formals : List (String × Nat)}
    {arguments : List Pattern}
    (instantiation :
      CheckerEndpointInstantiation demand slot formals arguments)
    (profile : SelectedNativeTypeBoundRelationClaim.Profile demand)
    (namesNodup : (formals.map Prod.fst).Nodup)
    (declared : ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈ formals) :
    instantiateSchemas? formals arguments
        (authoredClaims profile slot) =
      some (SelectedNativeTypeBoundRelationClaim.groundedClaims
        profile slot instantiation.endpoint.bindings) := by
  have profileExact : profile = premiseProfile := Subsingleton.elim _ _
  subst profile
  exact
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileOccurrenceInstantiation.CheckerEndpointInstantiation.instantiate_authoredGuardClaims
      instantiation namesNodup declared

/-- Each authored cold source has canonical first-order shape.  This finite
source fact is checked once at the fifteen roots. -/
theorem root_source_patternSupported
    (index : Fin coldSource.language.rewrites.length) :
    patternSupported (rootTyping index).site.rewrite.left = true := by
  fin_cases index <;> decide +kernel

/-- Each authored cold target has canonical first-order shape. -/
theorem root_target_patternSupported
    (index : Fin coldSource.language.rewrites.length) :
    patternSupported (rootTyping index).site.rewrite.right = true := by
  fin_cases index <;> decide +kernel

/-- Authored cold sources lie in the exact first-order source/checker
instantiation fragment. -/
theorem selected_source_fragment (slot : Occurrence) :
    BindingSchemaFragment (endpointFormals demand slot)
      (typingAt demand slot).site.rewrite.left := by
  apply bindingSchemaFragment_of_patternSupported
  · rw [typingAt_eq_rootTyping]
    exact root_source_patternSupported (rootIndexAt slot)
  · intro name member
    rw [mem_endpointFormals_iff, mem_endpointVariableNames_iff]
    exact Or.inl member

/-- Authored cold targets lie in the exact first-order source/checker
instantiation fragment. -/
theorem selected_target_fragment (slot : Occurrence) :
    BindingSchemaFragment (endpointFormals demand slot)
      (typingAt demand slot).site.rewrite.right := by
  apply bindingSchemaFragment_of_patternSupported
  · rw [typingAt_eq_rootTyping]
    exact root_target_patternSupported (rootIndexAt slot)
  · intro name member
    rw [mem_endpointFormals_iff, mem_endpointVariableNames_iff]
    exact Or.inr member

/-- Root focus is the authored source and inherits its first-order fragment
evidence without a third finite proof pass. -/
theorem selected_focus_fragment (slot : Occurrence) :
    BindingSchemaFragment (endpointFormals demand slot)
      (typingAt demand slot).site.focus := by
  have focusEq : (typingAt demand slot).site.focus =
      (typingAt demand slot).site.rewrite.left := by
    rw [typingAt_eq_rootTyping]
    simp [rootTyping, DisplayedRewriteSite.root,
      DisplayedRewriteSite.rewrite]
  rw [focusEq]
  exact selected_source_fragment slot

/-- One shared positional argument vector derived from the activation's
source bindings. -/
noncomputable def checkerArguments
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) : List Pattern :=
  Classical.choose
    (activationEndpointInstantiation environment).checkerArguments_exists

@[simp] theorem checkerArguments_exact
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) :
    argumentsOfBindings? (authoredMetavariables demand slot)
        (activationEndpointInstantiation environment).renamedBindings =
      some (checkerArguments environment) :=
  Classical.choose_spec
    (activationEndpointInstantiation environment).checkerArguments_exists

/-- The common argument vector reconstructs the exact authored source. -/
theorem instantiate_authoredSource
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) :
    instantiateSchema? (authoredMetavariables demand slot)
        (checkerArguments environment) (authoredSource demand slot) =
      some (applyBindings environment.bindings
        (typingAt demand slot).site.rewrite.left) := by
  simpa [authoredSource, activationEndpointInstantiation] using
    (activationEndpointInstantiation environment).instantiate_authoredPattern_of_arguments
      (checkerArguments_exact environment) (selected_source_fragment slot)

/-- The same common argument vector reconstructs the exact authored target. -/
theorem instantiate_authoredTarget
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) :
    instantiateSchema? (authoredMetavariables demand slot)
        (checkerArguments environment) (authoredTarget demand slot) =
      some (applyBindings environment.bindings
        (typingAt demand slot).site.rewrite.right) := by
  simpa [authoredTarget, activationEndpointInstantiation] using
    (activationEndpointInstantiation environment).instantiate_authoredPattern_of_arguments
      (checkerArguments_exact environment) (selected_target_fragment slot)

/-- The target equation agrees with the cold language's actual rule-aware
substitution operation, which is syntactic for this authored language. -/
theorem instantiate_authoredTarget_eq_ruleTarget
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) :
    instantiateSchema? (authoredMetavariables demand slot)
        (checkerArguments environment) (authoredTarget demand slot) =
      some (applyBindingsForRule language
        (typingAt demand slot).site.rewrite environment.bindings) := by
  rw [applyBindingsForRule_eq_syntactic]
  exact instantiate_authoredTarget environment

/-- The same common argument vector reconstructs the displayed focus. -/
theorem instantiate_authoredFocus
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) :
    instantiateSchema? (authoredMetavariables demand slot)
        (checkerArguments environment) (authoredFocus demand slot) =
      some (applyBindings environment.bindings
        (typingAt demand slot).site.focus) := by
  simpa [authoredFocus, activationEndpointInstantiation] using
    (activationEndpointInstantiation environment).instantiate_authoredPattern_of_arguments
      (checkerArguments_exact environment) (selected_focus_fragment slot)

/-- Crown coherence statement: source, target, and focus are instantiated by
one and the same checker argument vector derived from one activation. -/
theorem common_checker_instantiation
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) :
    argumentsOfBindings? (authoredMetavariables demand slot)
        (activationEndpointInstantiation environment).renamedBindings =
        some (checkerArguments environment) ∧
      instantiateSchema? (authoredMetavariables demand slot)
          (checkerArguments environment) (authoredSource demand slot) =
        some (applyBindings environment.bindings
          (typingAt demand slot).site.rewrite.left) ∧
      instantiateSchema? (authoredMetavariables demand slot)
          (checkerArguments environment) (authoredTarget demand slot) =
        some (applyBindingsForRule language
          (typingAt demand slot).site.rewrite environment.bindings) ∧
      instantiateSchema? (authoredMetavariables demand slot)
          (checkerArguments environment) (authoredFocus demand slot) =
        some (applyBindings environment.bindings
          (typingAt demand slot).site.focus) := by
  exact ⟨checkerArguments_exact environment,
    instantiate_authoredSource environment,
    instantiate_authoredTarget_eq_ruleTarget environment,
    instantiate_authoredFocus environment⟩

/-! ## Checker-derived source activation -/

/-- On every selected cold source, the skeleton occurrence inventory is the
ordinary free-variable inventory.  This finite source fact is what lets a
checker endpoint assignment be replayed through the authentic source
matcher. -/
theorem selected_source_occurrenceNames_eq_freeFvarNames
    (slot : Occurrence) :
    patternOccurrenceNames
        (typingAt demand slot).site.rewrite.left =
      (typingAt demand slot).site.rewrite.left.freeFvarNames := by
  apply patternOccurrenceNames_eq_freeFvarNames_of_holeSkeleton
  rw [typingAt_eq_rootTyping]
  exact root_left_holeSkeleton _

/-- Every selected cold target is an ambient-hole skeleton. -/
theorem root_target_holeSkeleton
    (index : Fin coldSource.language.rewrites.length) :
    patternHoleSkeleton (rootTyping index).site.rewrite.right = true := by
  fin_cases index <;> decide +kernel

/-- Target skeleton occurrences are exactly its free variables. -/
theorem selected_target_occurrenceNames_eq_freeFvarNames
    (slot : Occurrence) :
    patternOccurrenceNames
        (typingAt demand slot).site.rewrite.right =
      (typingAt demand slot).site.rewrite.right.freeFvarNames := by
  apply patternOccurrenceNames_eq_freeFvarNames_of_holeSkeleton
  rw [typingAt_eq_rootTyping]
  exact root_target_holeSkeleton _

/-- A value-only endpoint environment extracted from checker arguments
determines a genuine match of the authored source against its own instance.
The matcher may choose a different binding-list order, so the theorem records
the exact lookup agreement instead of asserting list equality. -/
theorem endpointActivation_exists (slot : Occurrence)
    (endpoint : EndpointInstantiation demand slot) :
    ∃ environment : ActivationEnvironment slot
        (applyBindings endpoint.bindings
          (typingAt demand slot).site.rewrite.left),
      bindingsAgreeWith endpoint.bindings environment.bindings := by
  have hole : patternHoleSkeleton
      (typingAt demand slot).site.rewrite.left = true := by
    rw [typingAt_eq_rootTyping]
    exact root_left_holeSkeleton _
  have covered : ∀ name ∈ patternOccurrenceNames
      (typingAt demand slot).site.rewrite.left,
      (Bindings.lookup endpoint.bindings name).isSome := by
    intro name member
    apply endpoint.covers name
    rw [mem_endpointVariableNames_iff]
    exact Or.inl (by
      rw [← selected_source_occurrenceNames_eq_freeFvarNames slot]
      exact member)
  obtain ⟨bindings, matched, agrees, _matcherCovers⟩ :=
    matchPattern_own_instance hole covered
  let before := applyBindings endpoint.bindings
    (typingAt demand slot).site.rewrite.left
  have matchedForRule : bindings ∈
      matchPatternForRule language (typingAt demand slot).site.rewrite
        before := by
    rw [matchPatternForRule_eq_syntactic]
    exact matched
  have bound : ∀ view ∈ viewsAt premiseProfile slot,
      SelectedNativeTypeBoundRelationEvidence.BoundArguments view bindings := by
    intro view member
    exact BoundArguments.ofSourceBound
      (selected_view_sourceBound slot view member)
      (matchPattern_holeSkeleton_covers hole bindings matched)
  exact ⟨{ bindings := bindings,
            matched := matchedForRule,
            bound := bound }, agrees⟩

/-- One actual checker/source endpoint bridge therefore contains one genuine
source activation.  All later guard and target evidence can be indexed by
this single record rather than chosen independently. -/
structure CheckerActivation (slot : Occurrence)
    (formals : List (String × Nat)) (arguments : List Pattern) where
  instantiation : CheckerEndpointInstantiation demand slot formals arguments
  environment : ActivationEnvironment slot
    (applyBindings instantiation.endpoint.bindings
      (typingAt demand slot).site.rewrite.left)
  agrees : bindingsAgreeWith instantiation.endpoint.bindings
    environment.bindings

/-- Every coherent checker endpoint instantiation extends to one coherent
checker activation. -/
theorem CheckerActivation.exists_of_endpoint
    (slot : Occurrence) (formals : List (String × Nat))
    (arguments : List Pattern)
    (instantiation :
      CheckerEndpointInstantiation demand slot formals arguments) :
    Nonempty (CheckerActivation slot formals arguments) := by
  obtain ⟨environment, agrees⟩ :=
    endpointActivation_exists slot instantiation.endpoint
  exact ⟨⟨instantiation, environment, agrees⟩⟩

/-- Every source variable receives the same value in the checker's endpoint
assignment and in the authentic matcher environment reconstructed from it.
The matcher binding list may have a different order; only observable lookup
is identified. -/
theorem CheckerActivation.source_lookup_eq (slot : Occurrence)
    {formals : List (String × Nat)} {arguments : List Pattern}
    (activation : CheckerActivation slot formals arguments)
    {name : String}
    (member :
      name ∈ (typingAt demand slot).site.rewrite.left.freeFvarNames) :
    Bindings.lookup activation.instantiation.endpoint.bindings name =
      Bindings.lookup activation.environment.bindings name := by
  have sourceHole : patternHoleSkeleton
      (typingAt demand slot).site.rewrite.left = true := by
    rw [typingAt_eq_rootTyping]
    exact root_left_holeSkeleton _
  have matched := activation.environment.matched
  rw [matchPatternForRule_eq_syntactic] at matched
  have environmentCovered := matchPattern_holeSkeleton_covers sourceHole
    activation.environment.bindings matched name member
  obtain ⟨value, environmentLookup⟩ :=
    Option.isSome_iff_exists.mp environmentCovered
  have endpointLookup :
      Bindings.lookup activation.instantiation.endpoint.bindings name =
        some value :=
    bindingsAgreeWith_lookup activation.agrees environmentLookup
  exact endpointLookup.trans environmentLookup.symm

/-- Ground truth of the complete ordered guard row is invariant under the
checker-to-matcher reconstruction.  The proof follows each authored argument
occurrence, so order and duplicate arguments are retained. -/
theorem CheckerActivation.groundMeanings_iff (slot : Occurrence)
    {formals : List (String × Nat)} {arguments : List Pattern}
    (activation : CheckerActivation slot formals arguments) :
    GroundMeanings premiseProfile relationEnv slot
        activation.instantiation.endpoint.bindings ↔
      GroundMeanings premiseProfile relationEnv slot
        activation.environment.bindings := by
  have argumentsEq : ∀ premise : Fin (viewsAt premiseProfile slot).length,
      (sourceView premiseProfile slot premise).arguments.map
          (applyBindings activation.instantiation.endpoint.bindings) =
        (sourceView premiseProfile slot premise).arguments.map
          (applyBindings activation.environment.bindings) := by
    intro premise
    apply List.map_congr_left
    intro argument argumentMember
    obtain ⟨name, rfl, sourceMember⟩ :=
      selected_view_sourceBound slot
        (sourceView premiseProfile slot premise)
        (List.get_mem _ premise) argument argumentMember
    have sourceHole : patternHoleSkeleton
        (typingAt demand slot).site.rewrite.left = true := by
      rw [typingAt_eq_rootTyping]
      exact root_left_holeSkeleton _
    have matched := activation.environment.matched
    rw [matchPatternForRule_eq_syntactic] at matched
    obtain ⟨value, environmentLookup⟩ := Option.isSome_iff_exists.mp
      (matchPattern_holeSkeleton_covers sourceHole
        activation.environment.bindings matched name sourceMember)
    have endpointLookup :
        Bindings.lookup activation.instantiation.endpoint.bindings name =
          some value := by
      rw [CheckerActivation.source_lookup_eq slot activation sourceMember]
      exact environmentLookup
    rw [applyBindings_fvar_eq_of_lookup endpointLookup,
      applyBindings_fvar_eq_of_lookup environmentLookup]
  constructor <;> intro meanings premise
  · simpa [GroundMeanings, groundedView, View.Meaning,
      argumentsEq premise] using meanings premise
  · simpa [GroundMeanings, groundedView, View.Meaning,
      argumentsEq premise] using meanings premise

/-- The checker's endpoint assignment and its reconstructed matcher
activation instantiate the authored target identically. -/
theorem CheckerActivation.target_eq (slot : Occurrence)
    {formals : List (String × Nat)} {arguments : List Pattern}
    (activation : CheckerActivation slot formals arguments) :
    applyBindings activation.instantiation.endpoint.bindings
        (typingAt demand slot).site.rewrite.right =
      applyBindings activation.environment.bindings
        (typingAt demand slot).site.rewrite.right := by
  apply applyBindings_agree
  · rw [typingAt_eq_rootTyping]
    exact root_target_holeSkeleton _
  · intro name member
    have targetName :
        name ∈ (typingAt demand slot).site.rewrite.right.freeFvarNames := by
      rw [← selected_target_occurrenceNames_eq_freeFvarNames slot]
      exact member
    have sourceName := selected_right_sourceBound slot name targetName
    have environmentCovered :
        (Bindings.lookup activation.environment.bindings name).isSome := by
      have sourceHole : patternHoleSkeleton
          (typingAt demand slot).site.rewrite.left = true := by
        rw [typingAt_eq_rootTyping]
        exact root_left_holeSkeleton _
      exact matchPattern_holeSkeleton_covers sourceHole
        activation.environment.bindings activation.environment.matched
        name sourceName
    obtain ⟨value, environmentLookup⟩ :=
      Option.isSome_iff_exists.mp environmentCovered
    have endpointLookup :
        Bindings.lookup activation.instantiation.endpoint.bindings name =
          some value :=
      bindingsAgreeWith_lookup activation.agrees environmentLookup
    exact endpointLookup.trans environmentLookup.symm

/-- Rule-aware target reconstruction is likewise invariant between the
checker endpoint and the authentic matcher environment. -/
theorem CheckerActivation.targetForRule_eq (slot : Occurrence)
    {formals : List (String × Nat)} {arguments : List Pattern}
    (activation : CheckerActivation slot formals arguments) :
    applyBindingsForRule language (typingAt demand slot).site.rewrite
        activation.instantiation.endpoint.bindings =
      applyBindingsForRule language (typingAt demand slot).site.rewrite
        activation.environment.bindings := by
  simpa only [applyBindingsForRule_eq_syntactic] using activation.target_eq

/-! ## Negative control -/

/-- A binding row missing any endpoint value cannot be presented as a
complete occurrence instantiation. -/
theorem no_endpointInstantiation_of_missing
    (slot : Occurrence) (bindings : Bindings) (name : String)
    (member : name ∈ endpointVariableNames demand slot)
    (missing : ¬ (Bindings.lookup bindings name).isSome) :
    ¬ ∃ instantiation : EndpointInstantiation demand slot,
        instantiation.bindings = bindings := by
  rintro ⟨instantiation, rfl⟩
  exact missing (instantiation.covers name member)

#print axioms selected_right_sourceBound
#print axioms selected_endpoint_sourceBound
#print axioms CheckerEndpointInstantiation.instantiate_authoredVariableClaim
#print axioms CheckerEndpointInstantiation.instantiate_authoredVariableClaims
#print axioms CheckerEndpointInstantiation.instantiate_authoredGuardClaims
#print axioms CheckerEndpointInstantiation.instantiate_authoredGuardClaimsFor
#print axioms activationEndpointInstantiation
#print axioms selected_source_fragment
#print axioms selected_target_fragment
#print axioms selected_focus_fragment
#print axioms instantiate_authoredSource
#print axioms instantiate_authoredTarget_eq_ruleTarget
#print axioms instantiate_authoredFocus
#print axioms common_checker_instantiation
#print axioms selected_source_occurrenceNames_eq_freeFvarNames
#print axioms root_target_holeSkeleton
#print axioms selected_target_occurrenceNames_eq_freeFvarNames
#print axioms endpointActivation_exists
#print axioms CheckerActivation.exists_of_endpoint
#print axioms CheckerActivation.source_lookup_eq
#print axioms CheckerActivation.groundMeanings_iff
#print axioms CheckerActivation.target_eq
#print axioms CheckerActivation.targetForRule_eq
#print axioms no_endpointInstantiation_of_missing

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileOccurrenceInstantiation
