import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingArgumentRules

/-!
# Native MM0 rules with constructor-specific data conditions

Theorem substitution has independence conditions that constructor application
does not. This combinator keeps finite argument recovery common while allowing
each inference scheme to supply its own executable data check. Logical
soundness must still be proved for that particular scheme.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport

def checkedArguments (target : Context) (arity : Nat) (check : List Preterm → Bool)
    (assignment : Subst Nat Tm) : Option (List Preterm) := do
  let arguments ← readArguments target arity assignment
  if check arguments then some arguments else none

theorem checkedArguments_iff (target : Context) (arity : Nat) (check : List Preterm → Bool)
    (assignment : Subst Nat Tm) (arguments : List Preterm) :
    checkedArguments target arity check assignment = some arguments ↔
      arguments.length = arity ∧ check arguments = true ∧
      ∀ index < arity, assignment index = expressionAssignment target arguments index := by
  unfold checkedArguments
  cases read : readArguments target arity assignment with
  | none =>
      simp only [Option.bind_eq_bind, Option.bind_none, reduceCtorEq, false_iff]
      rintro ⟨count, _, columns⟩
      have success := (readArguments_iff _ _ _ _).mpr ⟨count, columns⟩
      rw [read] at success
      cases success
  | some values =>
      have facts := (readArguments_iff _ _ _ _).mp read
      change (if check values = true then some values else none) = some arguments ↔ _
      constructor
      · intro accepted
        split at accepted
        · cases accepted
          exact ⟨facts.1, ‹check arguments = true›, facts.2⟩
        · cases accepted
      · rintro ⟨count, checked, columns⟩
        have success := (readArguments_iff _ _ _ _).mpr ⟨count, columns⟩
        have same : values = arguments := Option.some.inj (read.symm.trans success)
        subst values
        exact if_pos checked

def guardedArgumentRule (target : Context) (arity : Nat) (name : String)
    (check : List Preterm → Bool) (premises : List Pat) (conclusion : Pat) : Rule Nat Tm Pat :=
  requestRule (theoremRequest target.length arity name) premises conclusion
    (fun assignment => (checkedArguments target arity check assignment).isSome)

theorem guardedArgumentRule_complete (target : Context) (arity : Nat) (name : String)
    (check : List Preterm → Bool) (premises : List Pat) (conclusion : Pat)
    {arguments : List Preterm} (count : arguments.length = arity) (checked : check arguments = true)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt target.length (encode target argument) = true)
    (selected : List Tm) (result : Tm) (state : Multiset Tm)
    (matched : List.Forall₂ (ContextualPatterns.layer.Solves (expressionAssignment target arguments)) premises selected)
    (present : ∀ value ∈ selected, value ∈ state)
    (output : conclusion.inst (expressionAssignment target arguments) = some result) :
    Step ContextualPatterns.layer (guardedArgumentRule target arity name check premises conclusion)
      ({requestValue name (arguments.map (encode target))} + state) (state + {result}) := by
  apply requestRule_step (assignment := expressionAssignment target arguments) (selected := selected)
  · intro index outside
    have notInside : ¬index < arguments.length := by
      intro inside
      exact outside (theoremRequest target.length arity name)
        (by simp [requestRule])
        (theoremRequest_contains_formal _ _ _ _ (count ▸ inside))
    simp [expressionAssignment, List.getElem?_eq_none (Nat.le_of_not_lt notInside)]
  · apply (ContextualPatterns.solves_iff _ _ _).mpr
    rw [← count]
    exact theoremRequest_instantiation target arguments scopedArguments name
  · exact matched
  · exact present
  · rw [(checkedArguments_iff _ _ _ _ _).mpr ⟨count, checked, fun _ _ => rfl⟩]
    rfl
  · exact output

theorem guardedArgumentRule_preserves (target : Context) (arity : Nat) (name : String)
    (check : List Preterm → Bool) (premises : List Pat) (conclusion : Pat)
    (premisesBounded : ∀ pattern ∈ premises, ∀ index ∈ pattern.vars, index < arity)
    (conclusionBounded : ∀ index ∈ conclusion.vars, index < arity)
    (validValue : Tm → Prop)
    (localSound : ∀ arguments selected result, arguments.length = arity → check arguments = true →
      List.Forall₂ (ContextualPatterns.layer.Solves (expressionAssignment target arguments)) premises selected →
      (∀ value ∈ selected, validValue value) →
      conclusion.inst (expressionAssignment target arguments) = some result → validValue result)
    {before after : Multiset Tm} (validBefore : ∀ value ∈ before, validValue value)
    (step : Step ContextualPatterns.layer (guardedArgumentRule target arity name check premises conclusion) before after) :
    ∀ value ∈ after, validValue value := by
  apply requestRule_preserves validValue (before := before) (after := after) _ validBefore step
  intro assignment selected result checked matched validSelected output
  obtain ⟨arguments, accepted⟩ := Option.isSome_iff_exists.mp checked
  obtain ⟨count, checkedData, columns⟩ := (checkedArguments_iff _ _ _ _ _).mp accepted
  refine localSound arguments selected result count checkedData ?_ validSelected ?_
  · have enriched := (List.forall₂_and_left (p := fun pattern : Pat =>
        ∀ index ∈ pattern.vars, index < arity) premises selected).mpr ⟨premisesBounded, matched⟩
    apply enriched.imp
    intro pattern value evidence
    apply (ContextualPatterns.solves_iff _ _ _).mpr
    rw [← pattern_inst_columns columns pattern evidence.1]
    exact (ContextualPatterns.solves_iff _ _ _).mp evidence.2
  · change conclusion.inst assignment = some result at output
    rwa [pattern_inst_columns columns conclusion conclusionBounded] at output

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
