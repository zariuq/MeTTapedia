import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationParserControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationControls

/-! # From selected scalar parses to actual constraint-store events

The lexical alternatives of the boundary control denote different stores.
Elaboration reads the chosen CST and constructs a source-indexed candidate;
the existing prepared-effect interpreter still decides preparation, permission
and the resulting store. Neither a parse nor its ambiguity selection grants
execution permission.

CST spans and physical origins remain in the checked parse. This particular
operational observation erases spans and interprets the declared state labels.
It is a boundary interpretation, not yet the internal term/binder grammar.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.ParsedExecution

open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Controls
  (Store effect permission encoding decisions storePattern queries source prepares)
open Parser.Controls (profile input forest tree selectEmpty selectTold)

def elaborate : CST → Option Store
  | .node "Request" _ _ [
      .node "EmptyState" _ _ [.terminal [83] _ _],
      .node "Move" _ _ [.terminal [77] _ _]] => some []
  | .node "Request" _ _ [
      .node "AlreadyTold" _ _ [.terminal [83] _ _],
      .node "Move" _ _ [.terminal [77] _ _]] => some [(true, false)]
  | _ => none

theorem store_execution_iff (before after : Store) :
    atState (storePattern after) ∈
      rewriteStepWithPremisesUsing queries.relations language (source before) ↔
      Nonempty (effect.Event permission before after) := by
  change atState (encoding.state.view (sort := ()) after) ∈
    rewriteStepWithPremisesUsing (effectQueries effect permission encoding decisions).relations language
      (request (encoding.state.view (sort := ()) before)
        (encoding.firing.view (sort := ()) ⟨before, ()⟩)) ↔ _
  rw [execution_iff_event]
  exact ⟨fun ⟨event, _⟩ => ⟨event⟩, fun ⟨event⟩ => ⟨event, Subsingleton.elim _ _⟩⟩

def Execute (keep : CST → Bool) (parsed : CST) (after : Store) : Prop :=
  Parser.Selected keep forest profile input parsed ∧
    ∃ before, elaborate parsed = some before ∧
      atState (storePattern after) ∈
        rewriteStepWithPremisesUsing queries.relations language (source before)

/-- Preservation and reflection pass through the actual source grammar,
checked forest, declared ambiguity policy and effect interpreter. -/
theorem execute_iff_event (keep : CST → Bool) (parsed : CST) (after : Store) :
    Execute keep parsed after ↔
      Nonempty (Parser.Source profile input parsed) ∧ keep parsed = true ∧
        ∃ before, elaborate parsed = some before ∧ Nonempty (effect.Event permission before after) := by
  simp only [Execute, Parser.selected_iff _ _ _ _ Parser.Controls.forest_complete,
    store_execution_iff, and_assoc]

theorem empty_parse_executes : Execute selectEmpty (tree false) [(true, false)] := by
  rw [execute_iff_event]
  exact ⟨Parser.Controls.both_source_parses false, rfl, [], rfl,
    ⟨⟨(), prepares [] (), by simp [permission], rfl⟩⟩⟩

theorem told_parse_is_not_execution_permission : ¬ ∃ after, Execute selectTold (tree true) after := by
  rintro ⟨after, execution⟩
  obtain ⟨_, _, before, lowered, ⟨event⟩⟩ := (execute_iff_event _ _ _).mp execution
  have same : before = [(true, false)] := (Option.some.inj lowered).symm
  subst before
  exact event.permitted (List.mem_singleton_self _)

theorem interpretation_of_ambiguity_changes_answers :
    Execute selectEmpty (tree false) [(true, false)] ∧
      ¬ ∃ after, Execute selectTold (tree true) after :=
  ⟨empty_parse_executes, told_parse_is_not_execution_permission⟩

/-- The two parses are real and distinct. No function can recover both from
their shared spelling without an additional declared disambiguation choice. -/
theorem ambiguous_spelling_has_no_two_sided_single_parser :
    ¬ ∃ parse : List Nat → Option CST,
      parse input = some (tree false) ∧ parse input = some (tree true) := by
  rintro ⟨parse, first, second⟩
  exact Parser.Controls.distinct_trees (Option.some.inj (first.symm.trans second))

/-- A state label alone cannot forge the source-indexed candidate. -/
theorem missing_firing_is_not_elaborated :
    elaborate (.node "Request" 0 5 [
      .node "EmptyState" 4 5 [.terminal [83] 4 5]]) = none := rfl

theorem forged_lexical_payload_is_not_elaborated :
    elaborate (.node "Request" 0 6 [
      .node "EmptyState" 4 5 [.terminal [84] 4 5],
      .node "Move" 5 6 [.terminal [77] 5 6]]) = none := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.ParsedExecution
