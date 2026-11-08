import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCaseExecution
import Mettapedia.Languages.MeTTa.PeTTa.DestinationSequenceSource
import Mettapedia.Languages.MeTTa.PeTTa.DestinationMatchSource

/-!
# Return recipes of the owned occurrence source profile

This source grammar follows the return positions of let, sequential let,
conditional, failure and query templates. It is not a body evaluator, and
its recognition alone is not a value theorem: a leaf recipe must still be
interpreted by the source's value rules in the reached record. Native plan
classification and constructor-pattern leaves remain separate connections.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnSyntax

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination

inductive Returns (recipe : Atom) : Atom → Prop where
  | leaf : Returns recipe recipe
  | empty : Returns recipe (.expression [.symbol "empty"])
  | emptyChoice : Returns recipe (.expression [.symbol "superpose", .expression []])
  | binding (pattern producer : Atom) {body : Atom} : Returns recipe body →
      Returns recipe (.expression [.symbol "let", pattern, producer, body])
  | sequential (pairs : List Atom) {body : Atom} : Returns recipe body →
      Returns recipe (.expression [.symbol "let*", .expression pairs, body])
  | conditional (condition : Atom) {yes no : Atom} : Returns recipe yes → Returns recipe no →
      Returns recipe (.expression [.symbol "if", condition, yes, no])
  | conditionalAbsent (condition : Atom) {yes : Atom} : Returns recipe yes →
      Returns recipe (.expression [.symbol "if", condition, yes])
  | query (space pattern : Atom) {body : Atom} : Returns recipe body →
      Returns recipe (.expression [.symbol "match", space, pattern, body])

def checksSurfaceReturn (recipe : Atom) : Nat → Atom → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      if expression == recipe then true else
      match expression with
      | .expression [.symbol "empty"]
      | .expression [.symbol "superpose", .expression []] => true
      | .expression [.symbol "let", _, _, body]
      | .expression [.symbol "let*", .expression _, body]
      | .expression [.symbol "match", _, _, body] => checksSurfaceReturn recipe fuel body
      | .expression [.symbol "if", _, yes, no] =>
          checksSurfaceReturn recipe fuel yes && checksSurfaceReturn recipe fuel no
      | .expression [.symbol "if", _, yes] => checksSurfaceReturn recipe fuel yes
      | _ => false

theorem checksSurfaceReturn_sound (recipe : Atom) (fuel : Nat) : ∀ expression,
    checksSurfaceReturn recipe fuel expression = true → Returns recipe expression := by
  induction fuel with
  | zero => intro expression accepted; cases accepted
  | succ fuel ih =>
      intro expression accepted
      simp only [checksSurfaceReturn] at accepted
      split at accepted
      · have same : expression = recipe := by simpa using ‹(expression == recipe) = true›
        subst expression
        exact .leaf
      · split at accepted
        · exact .empty
        · exact .emptyChoice
        · exact .binding _ _ (ih _ accepted)
        · exact .sequential _ (ih _ accepted)
        · exact .query _ _ (ih _ accepted)
        · have branches := Bool.and_eq_true_iff.mp accepted
          exact .conditional _ (ih _ branches.1) (ih _ branches.2)
        · exact .conditionalAbsent _ (ih _ accepted)
        · cases accepted

theorem Returns.rename {recipe expression : Atom} (source : Returns recipe expression)
    (rename : String → String) :
    Returns (HE.Spec.Type.RuntimeRefinement.renameTypeVars rename recipe)
      (HE.Spec.Type.RuntimeRefinement.renameTypeVars rename expression) := by
  induction source <;>
    try simp only [HE.Spec.Type.RuntimeRefinement.renameTypeVars, List.map_cons, List.map_nil]
  case leaf => exact .leaf
  case empty => exact .empty
  case emptyChoice => exact .emptyChoice
  case binding pattern producer source ih => exact .binding _ _ ih
  case sequential pairs source ih => exact .sequential _ ih
  case conditional condition yesSource noSource yesIH noIH => exact .conditional _ yesIH noIH
  case conditionalAbsent condition source ih => exact .conditionalAbsent _ ih
  case query space pattern source ih => exact .query _ _ ih

theorem sequence_lowering_returns {recipe body : Atom} (returns : Returns recipe body) :
    ∀ pairs nested, Eval.nestedLets pairs body = some nested → Returns recipe nested := by
  intro pairs
  induction pairs with
  | nil => intro nested parsed; cases parsed; exact returns
  | cons pair rest ih =>
      intro nested parsed
      cases pair with
      | var | symbol | grounded => simp [Eval.nestedLets] at parsed
      | expression fields =>
          cases fields with
          | nil => simp [Eval.nestedLets] at parsed
          | cons pattern fields =>
              cases fields with
              | nil => simp [Eval.nestedLets] at parsed
              | cons producer fields =>
                  cases fields with
                  | cons => simp [Eval.nestedLets] at parsed
                  | nil =>
                      simp only [Eval.nestedLets] at parsed
                      obtain ⟨inside, lowered, rfl⟩ := Option.map_eq_some_iff.mp parsed
                      exact .binding pattern producer (ih inside lowered)

theorem checked_sequence_lowering (recipe body : Atom) (pairs : List Atom) (fuel : Nat)
    (checked : checksSurfaceReturn recipe fuel body = true)
    (admitted : SequenceSource.bindingPairs pairs = true) :
    ∃ nested, Eval.nestedLets pairs body = some nested ∧ Returns recipe nested := by
  obtain ⟨nested, lowered⟩ := (SequenceSource.bindingPairs_iff_lowering pairs body).mp admitted
  exact ⟨nested, lowered, sequence_lowering_returns (checksSurfaceReturn_sound recipe fuel body checked) pairs nested lowered⟩

/-- Every actual selected query occurrence schedules the original return
recipe's body. The complete frontier, not a chosen output list, earns this. -/
theorem query_frontier_returns {recipe : Atom} {control : Control} {pattern body destination : Atom}
    {older : List Goal} {start : Nat} {rows : List Atom} {selected : List (Nat × Control)}
    (returns : Returns recipe body)
    (source : QueryFrontier control pattern body destination older start rows selected) :
    ∀ chosen ∈ selected, ∃ child, Returns recipe child ∧
      chosen.2.goals = .evaluate child destination :: older := by
  intro chosen present
  exact ⟨body, returns, MatchSource.selected_template_is_original_recipe source chosen present⟩

theorem selected_case_returns {recipe : Atom} {bindings : Equations} {key : Atom}
    {cases : SpaceSemantics.Cases} {choice : ScopedCaseSelection.Choice}
    (bodies : ∀ branch ∈ cases, Returns recipe branch.2)
    (selected : ScopedCaseSelection.Selection bindings key 0 cases (some choice)) :
    Returns recipe choice.body :=
  ScopedCaseSelection.selected_body_property (Returns recipe) bodies selected

namespace Controls

private def protectedRecipe : Atom := .var "protected"

theorem nested_missing_else_query_is_recognized :
    checksSurfaceReturn protectedRecipe 4
      (.expression [.symbol "let*", .expression [.expression [.var "ignored", .symbol "effect"]],
        .expression [.symbol "if", .symbol "condition",
          .expression [.symbol "match", .symbol "&self", .var "row", protectedRecipe]]]) = true := by decide +kernel

theorem one_bad_return_arm_is_rejected :
    checksSurfaceReturn protectedRecipe 3
      (.expression [.symbol "if", .symbol "condition", protectedRecipe, .grounded (.int 9)]) = false := by decide +kernel

theorem malformed_sequence_recognition_is_not_lowering :
    checksSurfaceReturn protectedRecipe 2
      (.expression [.symbol "let*", .expression [.expression [.var "broken"]], protectedRecipe]) = true ∧
      SequenceSource.bindingPairs [.expression [.var "broken"]] = false := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnSyntax
