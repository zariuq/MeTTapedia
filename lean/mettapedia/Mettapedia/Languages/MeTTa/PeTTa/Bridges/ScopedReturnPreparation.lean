import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnObligation

/-!
# Return obligations earned by actual source preparation

The local component handles let, conditional and ordinary match preparation.
Sequential-let entry and scoped failure are consumed by their existing outer
source owners; the local exclusions below state that dispatch fact, not a
restriction imposed on admitted programs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnPreparation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ScopedReturnSyntax (Returns)
open ScopedReturnObligation (Pending)

theorem match_arguments_are_source_recipes (program : SpaceSemantics.Program)
    (space pattern body first second third : Atom) :
    callArguments program "match" [space, pattern, body] [first, second, third] =
      ([.evaluate space first], [first, pattern, body]) := by
  simp [callArguments, Eval.argumentIsRaw, StdLib.known, StdLib.rawArgument]

/-- Actual raw preparation retains a recognized variable-return obligation.
This does not predict a value or assume a complete run. -/
theorem prepared_variable_return (program : SpaceSemantics.Program) (control next : Control)
    (name : String) (expression destination : Atom) (older : List Goal)
    (returns : Returns (.var name) expression)
    (ordinary : Source.scopedForm expression = false)
    (notSequence : ∀ pairs body, expression ≠ .expression [.symbol "let*", .expression pairs, body])
    (prepared : Source.Prepared .eagerValue program control destination older expression next) :
    Pending (.var name) destination next.goals := by
  rw [← prepared.execution]
  cases returns with
  | leaf => exact .equation older
  | empty => cases ordinary
  | emptyChoice => cases ordinary
  | @binding pattern producer body returns =>
      exact ScopedReturnObligation.binding_preparation returns program pattern producer (.var (freshName control 0)) older
  | @sequential pairs body returns => exact False.elim (notSequence pairs body rfl)
  | @conditional condition yes no yesReturn noReturn =>
      exact ScopedReturnObligation.conditional_preparation yesReturn noReturn condition (.var (freshName control 0)) older
  | @conditionalAbsent condition yes yesReturn =>
      exact ScopedReturnObligation.conditional_absent_preparation yesReturn condition (.var (freshName control 0)) older
  | @query space pattern body returns =>
      have arguments := match_arguments_are_source_recipes program space pattern body
        (.var (freshName control 0)) (.var (freshName control 1)) (.var (freshName control 2))
      have selected : callable program "match" = true := by simp [callable, StdLib.known]
      simpa [prepare, selected, freshSlots, List.range_succ, arguments, replace] using
        (Pending.readyQuery (.var (freshName control 0)) pattern body older returns).prepend_evaluation
          space (.var (freshName control 0))

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnPreparation
