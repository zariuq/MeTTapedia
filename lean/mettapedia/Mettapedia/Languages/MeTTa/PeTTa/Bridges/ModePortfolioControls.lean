import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeAggregationPortfolio

/-! Raw-input refusal and observation controls for a renamed mode region. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModePortfolioControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics MeTTaIL.WireKit ModeFoldSource ModeAggregationPortfolio

def names : Names := ⟨"previous", "run-size", "winner", "best-size", "incoming"⟩
def body : Atom :=
  apply "if" [apply "==" [.var names.item, .var names.current],
    .expression [.var names.current, apply "+" [.var names.count, number 1], .var names.best, .var names.bestCount],
    apply "if" [apply ">" [.var names.count, .var names.bestCount],
      .expression [.var names.item, number 1, .var names.current, .var names.count],
      .expression [.var names.item, number 1, .var names.best, .var names.bestCount]]]
def program : Program := {equations := [⟨"choose-vote", arguments names, body⟩], declarations := []}
def code : Code := ⟨"choose-vote", names,
  apply "if" [apply "<" [.var names.bestCount, .var names.count], .var names.current, .var names.best]⟩

theorem sorted_naturals_are_admitted :
    (prepare .finalValue program code ([1, 1, 2, 2].map number)).isSome = true := by decide +kernel

theorem empty_natural_input_is_admitted :
    (prepare .finalValue program code []).isSome = true := by decide +kernel

theorem unsorted_votes_are_not_silently_sorted :
    (prepare .finalValue program code ([1, 2, 2, 1, 1].map number)).isNone = true := by decide +kernel

theorem boolean_vote_is_not_number_one :
    (prepare .finalValue program code [Effects.boolean true]).isNone = true := by decide +kernel

theorem foreign_and_negative_values_decline :
    (prepare .finalValue program code [.symbol "abc"]).isNone = true ∧
    (prepare .finalValue program code [integer (-1)]).isNone = true := by decide +kernel

theorem prefix_and_page_observers_decline :
    (prepare .accumulatorPrefixes program code ([1, 2].map number)).isNone = true ∧
    (prepare .sourcePages program code ([1, 2].map number)).isNone = true := by decide +kernel

theorem refused_boolean_returns_the_same_source_input :
    enter .finalValue program code [Effects.boolean true] = .reference [Effects.boolean true] := by
  apply refusal_keeps_actual_inputs
  exact Option.isNone_iff_eq_none.mp boolean_vote_is_not_number_one

def withUnrelated : Program :=
  {program with
    equations := program.equations ++ [⟨"unrelated", [.var "z"], .var "z"⟩]
    declarations := [.expression [.symbol ":", .symbol "unrelated", .symbol "Atom"]]}

theorem unrelated_equation_and_declaration_do_not_invalidate_schema :
    (prepare .finalValue withUnrelated code ([1, 2].map number)).isSome = true := by decide +kernel

def overlapping : Program := {program with equations := program.equations ++ program.equations}

theorem an_additional_callback_equation_is_not_ignored :
    (prepare .finalValue overlapping code ([1, 2].map number)).isNone = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModePortfolioControls
