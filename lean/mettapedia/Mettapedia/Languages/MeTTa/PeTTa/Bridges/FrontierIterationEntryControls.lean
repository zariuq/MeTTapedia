import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierDriverControls

/-! Driver-body recognition, demand changes and source-loader arity boundaries. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationEntry.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics
open WeightedFrontierDriverControls (program driverNames driverEquation phase driverConfig graph initial final)
open KeyedImprovementSource (number)

theorem actual_driver_is_prepared : (prepare program "sssp" driverNames phase).isSome = true := by decide +kernel

def worker := driverConfig.worker program "improve"

def candidate := classify .completedResult "improvement" program "sssp" driverNames phase worker
  (WeightedFrontierDriver.phase_returns driverConfig program "improve") 3 [number 0] 0

theorem completed_observer_is_classified : candidate.isSome = true := by decide +kernel

def plan := candidate.get (by decide +kernel)

theorem classified_driver_keeps_state_and_round_counter :
    plan.attempt (initial graph) = .committed (PureCallPortfolio.complete (final graph) (number 2)) := by kernel_reflexivity

theorem exact_page_observer_refuses :
    (classify .exactPage "improvement" program "sssp" driverNames phase worker
      (WeightedFrontierDriver.phase_returns driverConfig program "improve") 3 [number 0] 0).isNone = true := rfl

def changedBody : Program := {program with equations :=
  [KeyedImprovementSource.Controls.equation, {driverEquation with body := number 99}]}

theorem familiar_name_with_changed_body_refuses : (prepare changedBody "sssp" driverNames phase).isNone = true := by decide +kernel

def rawCounter : Program := {program with declarations :=
  [.expression [.symbol ":", .symbol "sssp", .expression [.symbol "->", .symbol "Tuple", .symbol "Atom", .symbol "Number"]]]}

theorem changed_counter_demand_refuses : (prepare rawCounter "sssp" driverNames phase).isNone = true := by decide +kernel

def extra : Equation := ⟨"sssp", driverEquation.arguments, number 99⟩

theorem productive_extra_equation_refuses :
    (prepare {program with equations := program.equations ++ [extra]} "sssp" driverNames phase).isNone = true := by decide +kernel

def wrongArity : Equation := ⟨"sssp", [], .expression [.symbol "println!", .symbol "unreachable"]⟩

theorem mixed_driver_arities_require_reference :
    (prepare {program with equations := wrongArity :: program.equations} "sssp" driverNames phase).isNone = true := by decide +kernel

def renamed : Program := {program with equations := [KeyedImprovementSource.Controls.equation,
  equation "rounds-renamed" driverNames phase]}

theorem function_name_is_not_the_regime_identifier :
    (prepare renamed "rounds-renamed" driverNames phase).isSome = true := by decide +kernel

theorem missing_driver_refuses :
    (prepare {program with equations := [KeyedImprovementSource.Controls.equation]} "sssp" driverNames phase).isNone = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationEntry.Controls
