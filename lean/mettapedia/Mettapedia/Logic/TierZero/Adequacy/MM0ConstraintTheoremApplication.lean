import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintParameters
import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingRuleLibrary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestResolution

/-!
# MM0 theorem requests activate through their actual source metadata

This compatibility profile retains the source theorem templates and their
sorting-and-support computation. The computed Boolean becomes an ordinary
constraint equality check. Its truth is recovered from an actual valid firing,
rather than supplied as an independent admission assertion.

The proof observation is resolved at an actual model of the retained equation
store. This is not a raw-state equivalence or the complete MM0 corpus adequacy
theorem. Per-formal contextual admission, catalog activation and theorem-space
authority remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintTheoremApplication

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport
open MM0Rewriting

def falseHead : Head := .judgment "condition:false"
def trueHead : Head := .judgment "condition:true"

theorem boolean_heads_distinct : falseHead ≠ trueHead := by decide

/-- The source metadata is the real theorem request and admission computation.
It contains no submitted proof object or derivability callback. -/
def recipe (signature : TermSignature) (target : Context) (name : String)
    (declaration : TheoremDecl) : RequestActivation.Recipe Nat Head Pat where
  request := theoremRequest target.length declaration.arguments.length name
  premises := declaration.hypotheses.map (proofPattern target.length)
  conclusion := proofPattern target.length declaration.conclusion
  dataCondition := fun assignment => (admitArguments signature declaration.arguments target assignment).isSome

theorem matchingRule_origin (signature : TermSignature) (target : Context) (name : String)
    (declaration : TheoremDecl) :
    (recipe signature target name declaration).matchingRule = theoremRule signature target name declaration := rfl

theorem source_template_scope (signature : TermSignature) (target : Context) (name : String)
    (declaration : TheoremDecl) (pattern : Pat)
    (member : pattern ∈ (recipe signature target name declaration).request ::
      (recipe signature target name declaration).premises ++ [(recipe signature target name declaration).conclusion]) :
    pattern.scope = target.length := by
  simp only [recipe, List.mem_cons, List.mem_append, List.mem_map] at member
  rcases member with (rfl | ⟨expression, _, rfl⟩) | (rfl | impossible)
  · rfl
  · rfl
  · rfl
  · cases impossible

theorem templates_fixed (signature : TermSignature) (target : Context) (name : String)
    (declaration : TheoremDecl) (assignment : Subst Nat Tm) :
    ∀ pattern ∈ (recipe signature target name declaration).request ::
      (recipe signature target name declaration).premises ++ [(recipe signature target name declaration).conclusion],
      ∀ value, ContextualPatterns.layer.inst assignment pattern = some value →
        FixedMatching.Fixed (MM0ConstraintParameters.action target) value := by
  intro pattern member value instantiated
  apply ABTProtectedParameters.fixed_of_supported
  have supported := ContextualPatterns.Pattern.inst_supported instantiated
  rw [source_template_scope signature target name declaration pattern member] at supported
  exact supported

theorem bounded_arguments_bind_only_the_request (signature : TermSignature) (target : Context)
    (name : String) (declaration : TheoremDecl) (values : List Tm) :
    GuardedMultisetRewriting.BindsOnlyGathers ContextualPatterns.layer
      (recipe signature target name declaration).matchingRule
      (RequestActivation.boundedAssignment declaration.arguments.length values) := by
  apply RequestActivation.boundedAssignment_binds
  intro index inside
  exact theoremRequest_contains_formal target.length declaration.arguments.length name index inside

/-- A valid activation entails the original finite admission computation,
including its sorting and dependency predicates. -/
theorem firing_admits {O : Type*} [DecidableEq O]
    (signature : TermSignature) (target : Context) (name : String) (declaration : TheoremDecl)
    (assignment : Subst Nat Tm) {rule : RuleInstance Tm} {label : O → Tm}
    {before : Configuration Tm O} {picked : Selection O}
    (computed : RequestActivation.activate ContextualPatterns.layer falseHead trueHead
      (recipe signature target name declaration) assignment = some rule)
    (valid : picked.Valid (MM0ConstraintParameters.action target) label rule before) :
    ∃ arguments, Substitution.Admissible signature declaration.arguments target arguments ∧
      ∀ index < declaration.arguments.length, assignment index = expressionAssignment target arguments index := by
  have checked := RequestActivation.condition_of_valid ContextualPatterns.layer falseHead trueHead
    boolean_heads_distinct target.length (recipe signature target name declaration) assignment computed valid
  change (admitArguments signature declaration.arguments target assignment).isSome = true at checked
  obtain ⟨arguments, admitted⟩ := Option.isSome_iff_exists.mp checked
  exact ⟨arguments, (admitArguments_iff signature declaration.arguments target assignment arguments).mp admitted⟩

theorem resolved_source_step {O : Type*} [DecidableEq O]
    (signature : TermSignature) (target : Context) (name : String) (declaration : TheoremDecl)
    (assignment : Subst Nat Tm) {rule : RuleInstance Tm} {label : O → Tm}
    {before : Configuration Tm O} {picked : Selection O}
    (computed : RequestActivation.activate ContextualPatterns.layer falseHead trueHead
      (recipe signature target name declaration) assignment = some rule)
    (bindings : GuardedMultisetRewriting.BindsOnlyGathers ContextualPatterns.layer
      (theoremRule signature target name declaration) assignment)
    (valid : picked.Valid (MM0ConstraintParameters.action target) label rule before)
    (candidate : ABTProtectedParameters.Assignment Head target.length)
    (models : (MM0ConstraintParameters.action target).Models candidate (picked.problem label rule before)) :
    GuardedMultisetRewriting.Step ContextualPatterns.layer (theoremRule signature target name declaration)
      (labels (fun occurrence => (MM0ConstraintParameters.action target).apply candidate (label occurrence)) before.present)
      (labels (fun occurrence => (MM0ConstraintParameters.action target).apply candidate (label occurrence))
        (picked.result label rule before).present) :=
  RequestResolution.resolved_step_of_valid ContextualPatterns.layer rfl falseHead trueHead
    boolean_heads_distinct target.length (recipe signature target name declaration) assignment computed bindings
    (templates_fixed signature target name declaration assignment) valid candidate models

/-- The CMR firing preserves the independent MM0 judgment invariant, observed
at one actual solution of its full retained constraint store. -/
theorem firing_preserves {O : Type*} [DecidableEq O]
    {sorts : SortSignature} {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {target : Context} {hypotheses : List Preterm}
    (formed : Context.WellFormed sorts target) (name : String)
    {index : Nat} {declaration : TheoremDecl} (known : theorems index = some declaration)
    (admitted : declaration.Admissible sorts signature) (assignment : Subst Nat Tm)
    {rule : RuleInstance Tm} {label : O → Tm} {before : Configuration Tm O} {picked : Selection O}
    (computed : RequestActivation.activate ContextualPatterns.layer falseHead trueHead
      (recipe signature target name declaration) assignment = some rule)
    (bindings : GuardedMultisetRewriting.BindsOnlyGathers ContextualPatterns.layer
      (theoremRule signature target name declaration) assignment)
    (valid : picked.Valid (MM0ConstraintParameters.action target) label rule before)
    (candidate : ABTProtectedParameters.Assignment Head target.length)
    (models : (MM0ConstraintParameters.action target).Models candidate (picked.problem label rule before))
    (incoming : ∀ value ∈ labels (fun occurrence =>
      (MM0ConstraintParameters.action target).apply candidate (label occurrence)) before.present,
      ValidValue signature definitions theorems target hypotheses value) :
    ∀ value ∈ labels (fun occurrence => (MM0ConstraintParameters.action target).apply candidate (label occurrence))
      (picked.result label rule before).present,
      ValidValue signature definitions theorems target hypotheses value :=
  theoremRule_preserves formed name known admitted incoming
    (resolved_source_step signature target name declaration assignment computed bindings valid candidate models)

end Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintTheoremApplication
