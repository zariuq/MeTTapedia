import Mettapedia.Logic.PLNWorldModelExperiment

/-!
# WM Experiment Regression Fixture

Concrete finite fixture for the experiment-channel WM layer:

- one strong channel
- one weak channel obtained by garbling (`weak = κ ∘ strong`)
- one query predicate on weak observations
- theorem-level check that the Blackwell wrapper yields WM consequence.
-/

namespace Mettapedia.Logic.PLNWorldModelExperimentRegression

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelExperiment
open scoped ENNReal

inductive Hypothesis where
  | h0 | h1 | h2
  deriving DecidableEq, Repr

inductive Obs where
  | o0 | o1 | o2
  deriving DecidableEq, Repr

/-- Strong channel keeps all three outcomes distinguishable. -/
def strongChannel : ExperimentChannel Hypothesis Obs where
  run
    | .h0 => .o0
    | .h1 => .o1
    | .h2 => .o2

/-- Garbling map that merges `o2` into `o1`. -/
def garble : Obs → Obs
  | .o0 => .o0
  | .o1 => .o1
  | .o2 => .o1

/-- Weak channel obtained by post-processing `strongChannel` with `garble`. -/
def weakChannel : ExperimentChannel Hypothesis Obs where
  run θ := garble (strongChannel.run θ)

theorem weak_factors_through_strong :
    BlackwellFactorsThrough strongChannel weakChannel garble := by
  intro θ
  cases θ <;> rfl

/-- Observation event used in the fixture query. -/
def isObs1 : Obs → Prop := fun o => o = .o1

abbrev weakQuery : ExperimentQuery Hypothesis Obs :=
  queryOf weakChannel isObs1

abbrev strongPullbackQuery : ExperimentQuery Hypothesis Obs :=
  pullbackQuery strongChannel garble isObs1

/-- Finite hypothesis-state fixture (four samples, one duplicated hypothesis). -/
def fixtureState : Multiset Hypothesis :=
  ({Hypothesis.h0} : Multiset Hypothesis) +
  ({Hypothesis.h1} : Multiset Hypothesis) +
  ({Hypothesis.h2} : Multiset Hypothesis) +
  ({Hypothesis.h2} : Multiset Hypothesis)

/-- Concrete theorem: Blackwell-style pullback gives exact WM strength equality
on the finite fixture state. -/
theorem fixture_strength_eq_blackwell_pullback :
    WorldModel.queryStrength (State := Multiset Hypothesis) (Query := ExperimentQuery Hypothesis Obs)
      fixtureState weakQuery =
    WorldModel.queryStrength (State := Multiset Hypothesis) (Query := ExperimentQuery Hypothesis Obs)
      fixtureState strongPullbackQuery := by
  exact
    queryStrength_eq_of_blackwellFactor
      strongChannel weakChannel garble weak_factors_through_strong isObs1 fixtureState

/-- Consequence-rule fixture built from the concrete Blackwell factorization witness. -/
def fixtureBlackwellRule :
    WMConsequenceRule (Multiset Hypothesis) (ExperimentQuery Hypothesis Obs) :=
  wmConsequenceRule_of_blackwellFactor strongChannel weakChannel garble isObs1

/-- Regression endpoint: applying the Blackwell rule on the fixture state yields
the expected WM consequence inequality. -/
theorem fixture_rule_apply_strength_le :
    WorldModel.queryStrength (State := Multiset Hypothesis) (Query := ExperimentQuery Hypothesis Obs)
      fixtureState weakQuery ≤
    WorldModel.queryStrength (State := Multiset Hypothesis) (Query := ExperimentQuery Hypothesis Obs)
      fixtureState strongPullbackQuery := by
  exact
    WMConsequenceRule.apply
      (r := fixtureBlackwellRule)
      (W := fixtureState)
      weak_factors_through_strong
      (WMJudgment.trivial fixtureState)

end Mettapedia.Logic.PLNWorldModelExperimentRegression
