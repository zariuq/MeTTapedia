import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingArguments
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.RequestSteps
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualSharedStep

/-!
# MM0 theorem application is an ordinary guarded rewriting step

The request binds all declaration arguments. Hypotheses are retained reads,
the conclusion is a contextual template, and argument admission is the
previously verified finite sorting-and-support check. The step runs the common
matcher and graft; there is no guest proof interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport

def formals (arity : Nat) : List Preterm := (List.range arity).map Preterm.var

def proofValue (context : Context) (expression : Preterm) : Tm :=
  judgment "pf" [encode context expression]

def proofPattern (width : Nat) (expression : Preterm) : Pat := judgmentPattern width "pf" [expression]

theorem proofValue_injective (context : Context) : Function.Injective (proofValue context) := by
  intro left right same
  have equal := judgment_injective "pf" same
  exact encode_injective context (List.cons.inj equal).1

def requestTag (name : String) : String := "request:" ++ name

def requestValue (name : String) (arguments : List Tm) : Tm := judgment (requestTag name) arguments

theorem requestTag_ne_proof (name : String) : requestTag name ≠ "pf" := by
  intro equal
  have lengths := congrArg String.length equal
  simp only [requestTag, String.length_append] at lengths
  have prefixLength : "request:".length = 8 := rfl
  have targetLength : "pf".length = 2 := rfl
  omega

theorem requestTag_ne_conversion (name : String) : requestTag name ≠ "cv" := by
  intro equal
  have lengths := congrArg String.length equal
  simp only [requestTag, String.length_append] at lengths
  have prefixLength : "request:".length = 8 := rfl
  have targetLength : "cv".length = 2 := rfl
  omega

theorem requestValue_ne_proof (name : String) (arguments : List Tm) (target : Context) (expression : Preterm) :
    requestValue name arguments ≠ proofValue target expression := by
  intro equal
  have tags : requestTag name = "pf" := Head.judgment.inj (Term.node.inj equal).1
  exact requestTag_ne_proof name tags

def theoremRequest (width arity : Nat) (name : String) : Pat :=
  judgmentPattern width (requestTag name) (formals arity)

def theoremRule (signature : TermSignature) (target : Context) (name : String) (declaration : TheoremDecl) :
    Rule Nat Tm Pat :=
  requestRule (theoremRequest target.length declaration.arguments.length name)
    (declaration.hypotheses.map (proofPattern target.length))
    (proofPattern target.length declaration.conclusion)
    (fun assignment => (admitArguments signature declaration.arguments target assignment).isSome)

theorem theoremRule_input (signature : TermSignature) (target : Context) (name : String) (declaration : TheoremDecl) :
    ContextualPatterns.RuleInput (theoremRule signature target name declaration) := by
  constructor
  · intro pattern member
    simp only [theoremRule, requestRule, List.singleton_append, List.mem_cons, List.mem_map] at member
    rcases member with rfl | ⟨expression, _, rfl⟩
    · exact judgmentPattern_input _ _ _
    · exact judgmentPattern_input _ _ _
  · intro check member
    have same : check = ⟨theoremRequest target.length declaration.arguments.length name,
        fun assignment _ => (admitArguments signature declaration.arguments target assignment).isSome = true⟩ := by
      simpa [theoremRule, requestRule] using member
    subst check
    exact judgmentPattern_input _ _ _

theorem formals_substitute (arguments : List Preterm) :
    Substitution.substituteList (Substitution.ofList arguments) (formals arguments.length) = some arguments := by
  apply (Substitution.substituteList_eq_some_iff _ _ _).mpr
  apply List.forall₂_of_length_eq_of_get
  · simp [formals]
  · intro index leftInside rightInside
    simp only [formals, List.get_eq_getElem, List.getElem_map, List.getElem_range]
    exact .var (List.getElem?_eq_getElem rightInside)

theorem proofPattern_instantiation (context : Context) (arguments : List Preterm)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt context.length (encode context argument) = true)
    (expression : Preterm) :
    (proofPattern context.length expression).inst (expressionAssignment context arguments) =
      (expression.substitute (Substitution.ofList arguments)).map (proofValue context) := by
  rw [proofPattern, judgmentPattern_instantiation context arguments context.length scopedArguments]
  cases result : expression.substitute (Substitution.ofList arguments) <;>
    simp [Substitution.substituteList, result, proofValue]

theorem proofPatterns_match (context : Context) (arguments : List Preterm)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt context.length (encode context argument) = true)
    {expressions results : List Preterm}
    (substituted : List.Forall₂ (Preterm.Substitutes (Substitution.ofList arguments)) expressions results) :
    List.Forall₂ (ContextualPatterns.layer.Solves (expressionAssignment context arguments))
      (expressions.map (proofPattern context.length)) (results.map (proofValue context)) := by
  induction substituted with
  | nil => exact .nil
  | cons head tail ih =>
      apply List.Forall₂.cons
      · apply (ContextualPatterns.solves_iff _ _ _).mpr
        rw [proofPattern_instantiation context arguments scopedArguments, head.eval]
        rfl
      · exact ih

theorem theoremRequest_instantiation (context : Context) (arguments : List Preterm)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt context.length (encode context argument) = true)
    (name : String) :
    (theoremRequest context.length arguments.length name).inst (expressionAssignment context arguments) =
      some (requestValue name (arguments.map (encode context))) := by
  rw [theoremRequest, judgmentPattern_instantiation context arguments context.length scopedArguments,
    formals_substitute]
  rfl

private theorem expressionFields_contains (width : Nat) {expressions : List Preterm} {expression : Preterm}
    (member : expression ∈ expressions) :
    (expressionTree width expression).vars ⊆ (expressionFields width expressions).vars := by
  induction expressions with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Finset.subset_union_left
      · exact (ih member).trans Finset.subset_union_right

theorem theoremRequest_contains_formal (width arity : Nat) (name : String) (index : Nat) (inside : index < arity) :
    index ∈ (theoremRequest width arity name).vars := by
  apply Finset.mem_image.mpr
  refine ⟨ambientSlot width index, ?_, rfl⟩
  apply expressionFields_contains width (expression := .var index)
    (List.mem_map.mpr ⟨index, List.mem_range.mpr inside, rfl⟩)
  simp [expressionTree, TreePat.vars]

theorem theoremRule_binds (signature : TermSignature) (target : Context) (name : String) (declaration : TheoremDecl)
    (arguments : List Preterm) (lengths : arguments.length = declaration.arguments.length) :
    BindsOnlyGathers ContextualPatterns.layer (theoremRule signature target name declaration)
      (expressionAssignment target arguments) := by
  intro index outside
  have notInside : ¬index < arguments.length := by
    intro inside
    exact outside (theoremRequest target.length declaration.arguments.length name)
      (by simp [theoremRule, requestRule])
      (theoremRequest_contains_formal _ _ _ _ (lengths ▸ inside))
  simp [expressionAssignment, List.getElem?_eq_none (Nat.le_of_not_lt notInside)]

/-- Every admissible MM0 theorem instance fires by the existing guarded rewriting step.
The surrounding state may contain only one copy of a repeated hypothesis. -/
theorem theoremRule_complete {sorts : SortSignature} {signature : TermSignature} {target : Context}
    (formed : Context.WellFormed sorts target) (name : String) (declaration : TheoremDecl)
    {arguments : List Preterm} {instance_ : TheoremInstance}
    (instantiated : declaration.Instantiates signature target arguments instance_)
    (state : Multiset Tm)
    (premisesPresent : ∀ expression ∈ instance_.hypotheses, proofValue target expression ∈ state) :
    Step ContextualPatterns.layer (theoremRule signature target name declaration)
      ({requestValue name (arguments.map (encode target))} + state)
      (state + {proofValue target instance_.conclusion}) := by
  have scopedArguments := admitted_arguments_supported formed instantiated.admissible
  apply requestRule_step (assignment := expressionAssignment target arguments)
    (selected := instance_.hypotheses.map (proofValue target))
  · exact theoremRule_binds signature target name declaration arguments instantiated.admissible.length_eq
  · apply (ContextualPatterns.solves_iff _ _ _).mpr
    rw [← instantiated.admissible.length_eq]
    exact theoremRequest_instantiation target arguments scopedArguments name
  · exact proofPatterns_match target arguments scopedArguments instantiated.hypotheses
  · intro value member
    obtain ⟨expression, expressionMember, rfl⟩ := List.mem_map.mp member
    exact premisesPresent expression expressionMember
  · have admitted := (admitArguments_iff signature declaration.arguments target _ arguments).mpr
      ⟨instantiated.admissible, fun _ _ => rfl⟩
    rw [admitted]
    rfl
  · change (proofPattern target.length declaration.conclusion).inst _ = _
    rw [proofPattern_instantiation target arguments scopedArguments, instantiated.conclusion.eval]
    rfl

theorem proofPattern_reflect (target : Context) (arguments : List Preterm) (arity : Nat)
    (assignment : Subst Nat Tm)
    (columns : ∀ index < arity, assignment index = expressionAssignment target arguments index)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt target.length (encode target argument) = true)
    {expression : Preterm} (bounded : expression.VarsBelow arity) {value : Tm}
    (matched : ContextualPatterns.layer.Solves assignment (proofPattern target.length expression) value) :
    ∃ result, Preterm.Substitutes (Substitution.ofList arguments) expression result ∧
      value = proofValue target result := by
  have localInstance : (proofPattern target.length expression).inst assignment =
      (proofPattern target.length expression).inst (expressionAssignment target arguments) := by
    apply ContextualPatterns.Pattern.inst_local
    intro index member
    exact columns index (judgmentPattern_vars_below target.length arity "pf" [expression]
      (by simpa using bounded) index member)
  have applied := (ContextualPatterns.solves_iff _ _ _).mp matched
  rw [localInstance, proofPattern_instantiation target arguments scopedArguments] at applied
  obtain ⟨result, substituted, same⟩ := Option.map_eq_some_iff.mp applied
  exact ⟨result, Preterm.substitute_sound substituted, same.symm⟩

theorem proofPatterns_reflect {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} (target : Context) (hypotheses arguments : List Preterm)
    (arity : Nat) (assignment : Subst Nat Tm)
    (columns : ∀ index < arity, assignment index = expressionAssignment target arguments index)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt target.length (encode target argument) = true)
    (expressions : List Preterm) (selected : List Tm)
    (bounded : ∀ expression ∈ expressions, expression.VarsBelow arity)
    (matched : List.Forall₂ (ContextualPatterns.layer.Solves assignment)
      (expressions.map (proofPattern target.length)) selected)
    (valid : ∀ value ∈ selected, ∀ expression, value = proofValue target expression →
      Derives signature definitions theorems target hypotheses expression) :
    ∃ results, List.Forall₂ (Preterm.Substitutes (Substitution.ofList arguments)) expressions results ∧
      DerivesList signature definitions theorems target hypotheses results := by
  induction expressions generalizing selected with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons expression expressions ih =>
      cases matched with
      | @cons _ value _ values head tail =>
          obtain ⟨result, substituted, same⟩ := proofPattern_reflect target arguments arity assignment
            columns scopedArguments (bounded expression (by simp)) head
          obtain ⟨results, substitutedTail, derivedTail⟩ := ih values
            (fun e member => bounded e (by simp [member])) tail
            (fun v member e equal => valid v (by simp [member]) e equal)
          exact ⟨result :: results, .cons substituted substitutedTail,
            .cons (valid value (by simp) result same) derivedTail⟩

/-- New proof values produced by the actual step have independent MM0 derivations.
The incoming theorem-space invariant supplies the retained hypotheses. -/
theorem theoremRule_sound {sorts : SortSignature} {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature} {target : Context}
    (formed : Context.WellFormed sorts target) (hypotheses : List Preterm)
    (name : String) {index : Nat} {declaration : TheoremDecl}
    (known : theorems index = some declaration)
    (boundedConclusion : declaration.conclusion.VarsBelow declaration.arguments.length)
    (boundedHypotheses : ∀ expression ∈ declaration.hypotheses,
      expression.VarsBelow declaration.arguments.length)
    {before after : Multiset Tm}
    (valid : ∀ expression, proofValue target expression ∈ before →
      Derives signature definitions theorems target hypotheses expression)
    (step : Step ContextualPatterns.layer (theoremRule signature target name declaration) before after) :
    ∀ expression, proofValue target expression ∈ after →
      Derives signature definitions theorems target hypotheses expression := by
  obtain ⟨assignment, frame, taken, kept, made, _, _, reads, source, checks, outputs, destination⟩ := step
  have checked := checks
    ⟨theoremRequest target.length declaration.arguments.length name,
      fun assignment _ => (admitArguments signature declaration.arguments target assignment).isSome = true⟩
    (by simp [theoremRule, requestRule])
  obtain ⟨arguments, admitted⟩ := Option.isSome_iff_exists.mp checked
  obtain ⟨admissible, columns⟩ := (admitArguments_iff _ _ _ _ _).mp admitted
  have scopedArguments := admitted_arguments_supported formed admissible
  obtain ⟨selected, matched, _, present⟩ := reads
  obtain ⟨results, substitutedHypotheses, derivedHypotheses⟩ := proofPatterns_reflect
    target hypotheses arguments declaration.arguments.length assignment columns scopedArguments
    declaration.hypotheses selected boundedHypotheses matched (by
      intro value member expression same
      apply valid expression
      rw [source, ← same]
      exact Multiset.mem_add.mpr (Or.inr (present value member)))
  have madeOne : ∃ value, (proofPattern target.length declaration.conclusion).inst assignment = some value ∧
      made = [value] := by
    change [(proofPattern target.length declaration.conclusion)].mapM
      (fun p => p.inst assignment) = some made at outputs
    cases output : (proofPattern target.length declaration.conclusion).inst assignment with
    | none => simp [output] at outputs
    | some value =>
        have same : [value] = made := by simpa [output] using outputs
        exact ⟨value, rfl, same.symm⟩
  obtain ⟨value, output, rfl⟩ := madeOne
  obtain ⟨result, substitutedConclusion, valueSame⟩ := proofPattern_reflect target arguments
    declaration.arguments.length assignment columns scopedArguments boundedConclusion
    ((ContextualPatterns.solves_iff _ _ _).mpr output)
  have derived : Derives signature definitions theorems target hypotheses result :=
    .theoremApp (instantiation := ⟨results, result⟩) known
      ⟨admissible, substitutedHypotheses, substitutedConclusion⟩ derivedHypotheses
  intro expression member
  rw [destination] at member
  rcases Multiset.mem_add.mp member with retained | fresh
  · apply valid expression
    rw [source]
    rcases Multiset.mem_add.mp retained with framed | keptMember
    · exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl framed)))
    · exact Multiset.mem_add.mpr (Or.inr keptMember)
  · have equal : proofValue target expression = proofValue target result := by
      simpa [valueSame] using fresh
    exact (proofValue_injective target equal).symm ▸ derived

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
