import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingTheoremApplication

/-!
# Shared argument admission for MM0 inference schemes

The authoring combinator returns an ordinary guarded rewriting rule. Its arguments are
bound by a request, its premises are ordinary patterns, and its single result
is an ordinary template. Local inference soundness is proved separately for
each MM0 constructor.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport

def argumentRule (signature : TermSignature) (target formal : Context) (name : String)
    (premises : List Pat) (conclusion : Pat) : Rule Nat Tm Pat :=
  requestRule (theoremRequest target.length formal.length name) premises conclusion
    (fun assignment => (admitArguments signature formal target assignment).isSome)

theorem argumentRule_binds (signature : TermSignature) (target formal : Context) (name : String)
    (premises : List Pat) (conclusion : Pat) (arguments : List Preterm)
    (lengths : arguments.length = formal.length) :
    BindsOnlyGathers ContextualPatterns.layer (argumentRule signature target formal name premises conclusion)
      (expressionAssignment target arguments) := by
  intro index outside
  have notInside : ¬index < arguments.length := by
    intro inside
    exact outside (theoremRequest target.length formal.length name)
      (by simp [argumentRule, requestRule])
      (theoremRequest_contains_formal _ _ _ _ (lengths ▸ inside))
  simp [expressionAssignment, List.getElem?_eq_none (Nat.le_of_not_lt notInside)]

theorem argumentRule_complete {sorts : SortSignature} {signature : TermSignature} {target formal : Context}
    (formed : Context.WellFormed sorts target) (name : String) (premises : List Pat) (conclusion : Pat)
    {arguments : List Preterm} (admitted : Substitution.Admissible signature formal target arguments)
    (selected : List Tm) (result : Tm) (state : Multiset Tm)
    (matched : List.Forall₂ (ContextualPatterns.layer.Solves (expressionAssignment target arguments)) premises selected)
    (present : ∀ value ∈ selected, value ∈ state)
    (output : conclusion.inst (expressionAssignment target arguments) = some result) :
    Step ContextualPatterns.layer (argumentRule signature target formal name premises conclusion)
      ({requestValue name (arguments.map (encode target))} + state) (state + {result}) := by
  apply requestRule_step (assignment := expressionAssignment target arguments) (selected := selected)
  · exact argumentRule_binds signature target formal name premises conclusion arguments admitted.length_eq
  · apply (ContextualPatterns.solves_iff _ _ _).mpr
    rw [← admitted.length_eq]
    exact theoremRequest_instantiation target arguments (admitted_arguments_supported formed admitted) name
  · exact matched
  · exact present
  · rw [(admitArguments_iff _ _ _ _ _).mpr ⟨admitted, fun _ _ => rfl⟩]
    rfl
  · exact output

theorem pattern_inst_columns {target : Context} {arguments : List Preterm} {arity : Nat}
    {assignment : Subst Nat Tm}
    (columns : ∀ index < arity, assignment index = expressionAssignment target arguments index)
    (pattern : Pat) (bounded : ∀ index ∈ pattern.vars, index < arity) :
    pattern.inst assignment = pattern.inst (expressionAssignment target arguments) :=
  ContextualPatterns.Pattern.inst_local _ _ _ (fun index member => columns index (bounded index member))

/-- A finite tuple recovered from the request suffices for every bounded
judgment template, including variables repeated between different premises. -/
theorem judgment_inst_columns {target : Context} {arguments : List Preterm} {arity : Nat}
    {assignment : Subst Nat Tm}
    (columns : ∀ index < arity, assignment index = expressionAssignment target arguments index)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt target.length (encode target argument) = true)
    (tag : String) (expressions : List Preterm)
    (bounded : ∀ expression ∈ expressions, expression.VarsBelow arity) :
    (judgmentPattern target.length tag expressions).inst assignment =
      (Substitution.substituteList (Substitution.ofList arguments) expressions).map
        (fun results => judgment tag (results.map (encode target))) := by
  rw [pattern_inst_columns columns _ (judgmentPattern_vars_below _ _ _ _ bounded),
    judgmentPattern_instantiation target arguments target.length scopedArguments]

/-- Local soundness is required only on the exact, admitted object arguments.
The common calculus then propagates it to a whole store step. -/
theorem argumentRule_preserves {sorts : SortSignature} {signature : TermSignature} {target formal : Context}
    (formed : Context.WellFormed sorts target) (name : String) (premises : List Pat) (conclusion : Pat)
    (premisesBounded : ∀ pattern ∈ premises, ∀ index ∈ pattern.vars, index < formal.length)
    (conclusionBounded : ∀ index ∈ conclusion.vars, index < formal.length)
    (validValue : Tm → Prop)
    (localSound : ∀ arguments selected result,
      Substitution.Admissible signature formal target arguments →
      (∀ argument ∈ arguments, Term.supportedAt target.length (encode target argument) = true) →
      List.Forall₂ (ContextualPatterns.layer.Solves (expressionAssignment target arguments)) premises selected →
      (∀ value ∈ selected, validValue value) →
      conclusion.inst (expressionAssignment target arguments) = some result → validValue result)
    {before after : Multiset Tm} (validBefore : ∀ value ∈ before, validValue value)
    (step : Step ContextualPatterns.layer (argumentRule signature target formal name premises conclusion) before after) :
    ∀ value ∈ after, validValue value := by
  apply requestRule_preserves validValue (before := before) (after := after) _ validBefore step
  intro assignment selected result checked matched validSelected output
  obtain ⟨arguments, accepted⟩ := Option.isSome_iff_exists.mp checked
  obtain ⟨admitted, columns⟩ := (admitArguments_iff _ _ _ _ _).mp accepted
  have same (pattern : Pat) (bounded : ∀ index ∈ pattern.vars, index < formal.length) :=
    pattern_inst_columns columns pattern bounded
  refine localSound arguments selected result admitted (admitted_arguments_supported formed admitted) ?_ validSelected ?_
  · have enriched := (List.forall₂_and_left (p := fun pattern : Pat =>
        ∀ index ∈ pattern.vars, index < formal.length) premises selected).mpr ⟨premisesBounded, matched⟩
    apply enriched.imp
    intro pattern value evidence
    apply (ContextualPatterns.solves_iff _ _ _).mpr
    rw [← same pattern evidence.1]
    exact (ContextualPatterns.solves_iff _ _ _).mp evidence.2
  · change conclusion.inst assignment = some result at output
    rwa [same conclusion conclusionBounded] at output

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
