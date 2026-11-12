import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaContinuationContexts

/-!
# Candidate derived forms and their PeTTa source expansion

Both concrete presentations retain these operation roles. Literal results are
quoted so a callable-looking value is not accidentally executed. Count expands
to collection followed by size; chain is the candidate's relational binding
spelling. Neither choice changes HE or PeTTa's public syntax.

This module defines a source expansion, not a separate evaluator. Context laws
consume the actual independent PeTTa source judgment. Whole-family operational
adequacy of the candidate language remains a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms

open OSLFCore (Atom)

inductive Code where
  | value (term : Atom)
  | read (space pattern : Atom) (body : Code)
  | add (space term : Atom)
  | remove (space pattern : Atom)
  | transform (space sources template : Atom) (destination : Option Atom)
  | first (body : Code)
  | collect (body : Code)
  | choice (alternatives : List Code)
  | bind (pattern : Atom) (value body : Code)
  | chain (name : String) (value body : Code)
  | count (body : Code)
  | fold (step : Atom) (generator seed : Code)
  | cases (value : Code) (branches : List (Atom × Code))
  | empty
  deriving Repr

private theorem second_smaller {A B : Type} [SizeOf A] [SizeOf B]
    (items : List (A × B)) (item : A × B) (member : item ∈ items) : sizeOf item.2 < sizeOf items := by
  have bound := List.sizeOf_lt_of_mem member
  rcases item with ⟨left, right⟩
  simp only [Prod.mk.sizeOf_spec] at bound
  change sizeOf right < sizeOf items
  omega

def Code.toPeTTa : Code → Atom
  | .value term => .expression [.symbol "quote", term]
  | .read space pattern body => .expression [.symbol "match", space, pattern, body.toPeTTa]
  | .add space term => .expression [.symbol "add-atom", space, term]
  | .remove space pattern => .expression [.symbol "remove-atom", space, pattern]
  | .transform space sources template destination =>
      .expression ([.symbol "transform", space, sources, template] ++ destination.toList)
  | .first body => .expression [.symbol "once", body.toPeTTa]
  | .collect body => .expression [.symbol "collapse", body.toPeTTa]
  | .choice alternatives => .expression [.symbol "superpose", .expression (alternatives.map Code.toPeTTa)]
  | .bind pattern initializer body => .expression [.symbol "let", pattern, initializer.toPeTTa, body.toPeTTa]
  | .chain name initializer body => .expression [.symbol "let", .var name, initializer.toPeTTa, body.toPeTTa]
  | .count body => .expression [.symbol "size-atom", .expression [.symbol "collapse", body.toPeTTa]]
  | .fold step generator seed => .expression [.symbol "foldall", step, generator.toPeTTa, seed.toPeTTa]
  | .cases subject branches => .expression [.symbol "case", subject.toPeTTa,
      .expression (branches.map fun branch => .expression [branch.1, branch.2.toPeTTa])]
  | .empty => .expression [.symbol "empty"]
termination_by code => sizeOf code
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact Nat.lt_trans (List.sizeOf_lt_of_mem ‹_ ∈ _›) (by omega)
    | exact Nat.lt_trans (second_smaller _ _ ‹_ ∈ _›) (by omega)

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open ContextualTransform.PeTTaContexts

theorem value_remains_data (registry : SpaceSemantics.Program) (base : Unifying.Configuration)
    (bindings : Subst) (term : Atom) :
    Unifying.step registry (atExpression base bindings (Code.value term).toPeTTa) =
      some { base with control := .returned [⟨Unifying.resolve bindings term, bindings⟩] } := by
  simpa only [Code.toPeTTa] using
    ContextualTransform.PeTTaActivation.quote_is_value registry base bindings term

/-- A real initializer derivation connects the expanded candidate binding
to the actual continuation, retaining the reached state and branch binding. -/
theorem binding_reaches_body (registry : SpaceSemantics.Program)
    (before after : Unifying.Configuration) (incoming produced bound : Subst)
    (pattern value : Atom) (initializer body : Code)
    (initialized : Relation.ReflTransGen (Unifying.Transition registry)
      (atExpression { before with frames := [] } incoming initializer.toPeTTa)
      { after with control := .returned [⟨value, produced⟩], frames := [] })
    (matched : Unifying.unifyBinding produced pattern value = .ok bound) :
    Relation.ReflTransGen (Unifying.Transition registry)
      (atExpression before incoming (Code.bind pattern initializer body).toPeTTa)
      (atExpression { after with frames := .sequence [] [] :: before.frames } bound body.toPeTTa) := by
  simpa only [Code.toPeTTa] using
    ContextualTransform.PeTTaBindingContexts.initializer_then_body registry before after incoming produced bound
      pattern initializer.toPeTTa body.toPeTTa value initialized matched

theorem collection_preserves_source_completion (registry : SpaceSemantics.Program)
    (before after : Unifying.Configuration) (bindings : Subst) (body : Code)
    (answers : List Unifying.Answer)
    (computed : Relation.ReflTransGen (Unifying.Transition registry)
      (atExpression { before with frames := [] } bindings body.toPeTTa)
      { after with control := .returned answers, frames := [] }) :
    Relation.ReflTransGen (Unifying.Transition registry)
      (atExpression before bindings (Code.collect body).toPeTTa)
      { after with
        control := .returned [⟨.expression (Unifying.copies after.uses answers), bindings⟩]
        frames := before.frames
        uses := after.uses + answers.length } := by
  simpa only [Code.toPeTTa] using
    ContextualTransform.PeTTaContinuationContexts.operand_then_collection registry before after bindings
      body.toPeTTa answers computed

theorem count_enters_its_collection (registry : SpaceSemantics.Program)
    (base : Unifying.Configuration) (bindings : Subst) (body : Code) (fuel : Nat) :
    Unifying.run registry (2 + fuel) (atExpression base bindings (Code.count body).toPeTTa) =
      Unifying.run registry fuel
        (atExpression { base with frames := .argument (.function "size-atom") [] [] 0 :: base.frames }
          bindings (Code.collect body).toPeTTa) := by
  simpa only [Code.toPeTTa, ContextualTransform.PeTTaApplicationContexts.Site.cost,
    ContextualTransform.PeTTaApplicationContexts.Site.plug] using
    ContextualTransform.PeTTaApplicationContexts.site_run registry
      (.call "size-atom" []) base bindings (Code.collect body).toPeTTa _ rfl fuel

theorem count_is_not_first :
    (Code.count (.choice [.value (.symbol "a"), .value (.symbol "b")])).toPeTTa ≠
      (Code.first (.choice [.value (.symbol "a"), .value (.symbol "b")])).toPeTTa := by
  simp only [Code.toPeTTa]
  decide

end Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms
