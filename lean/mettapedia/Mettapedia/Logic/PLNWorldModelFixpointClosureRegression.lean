import Mettapedia.Logic.PLNWorldModelFixpointClosure
import Mettapedia.Logic.PLNWorldModelExperimentRegression

/-!
# WM Fixpoint Closure Regression Fixture

Concrete finite fixture for Hyperseed-style closure dynamics on WM consequence
rules:

- positive: Blackwell-derived rule adds a new query to least closure;
- negative: with no rules, closure collapses to seed (no new query).
-/

namespace Mettapedia.Logic.PLNWorldModelFixpointClosureRegression

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open Mettapedia.Logic.PLNWorldModelExperiment
open Mettapedia.Logic.PLNWorldModelExperimentRegression
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

abbrev FState := Multiset Hypothesis
abbrev FQuery := ExperimentQuery Hypothesis Obs

abbrev fixtureRuleOn : WMConsequenceRuleOn FState FQuery :=
  WMConsequenceRuleOn.ofGlobal fixtureBlackwellRule

def fixtureRules : RuleSet FState FQuery := { fixtureRuleOn }

def fixtureSeed : Set FQuery := { weakQuery }

def fixtureEmptyRules : RuleSet FState FQuery := (∅ : Set (WMConsequenceRuleOn FState FQuery))

theorem fixture_pullback_not_in_seed :
    strongPullbackQuery ∉ fixtureSeed := by
  intro hmem
  have hEq : strongPullbackQuery = weakQuery := by
    simpa [fixtureSeed] using hmem
  have hCh : strongChannel = weakChannel := by
    simpa [strongPullbackQuery, weakQuery, pullbackQuery, queryOf] using
      congrArg ExperimentQuery.channel hEq
  have hRun := congrArg (fun c : ExperimentChannel Hypothesis Obs => c.run Hypothesis.h2) hCh
  simp [strongChannel, weakChannel, garble] at hRun

theorem fixture_pullback_in_leastClosure :
    strongPullbackQuery ∈ leastRuleClosure fixtureRules fixtureState fixtureSeed := by
  have hprem :
      weakQuery ∈ leastRuleClosure fixtureRules fixtureState fixtureSeed :=
    seed_subset_leastRuleClosure (R := fixtureRules) (W := fixtureState) (seed := fixtureSeed)
      (by simp [fixtureSeed])
  have hrule : fixtureRuleOn ∈ fixtureRules := by
    simp [fixtureRules]
  have hside : fixtureRuleOn.side fixtureState := by
    simpa [fixtureRuleOn, WMConsequenceRuleOn.ofGlobal] using weak_factors_through_strong
  have hconc :=
    leastRuleClosure_rule_closed (R := fixtureRules) (W := fixtureState) (seed := fixtureSeed)
      (r := fixtureRuleOn) hrule hside (by simpa [fixtureRuleOn, WMConsequenceRuleOn.ofGlobal] using hprem)
  simpa [fixtureRuleOn, WMConsequenceRuleOn.ofGlobal] using hconc

theorem fixture_pullback_threshold_from_seed :
    let τ :=
      BinaryWorldModel.queryStrength (State := FState) (Query := FQuery)
        fixtureState weakQuery
    τ ≤
      BinaryWorldModel.queryStrength (State := FState) (Query := FQuery)
        fixtureState strongPullbackQuery := by
  intro τ
  have hSeedValid :
      thresholdValid (State := FState) (Query := FQuery)
        fixtureState τ fixtureSeed := by
    intro q hq
    have hEq : q = weakQuery := by
      simpa [fixtureSeed] using hq
    subst hEq
    exact le_rfl
  have hClosureValid :=
    leastRuleClosure_thresholdValid (State := FState) (Query := FQuery)
      (R := fixtureRules) (W := fixtureState) (seed := fixtureSeed) (τ := τ) hSeedValid
  exact hClosureValid strongPullbackQuery fixture_pullback_in_leastClosure

theorem fixture_emptyRules_closure_eq_seed :
    leastRuleClosure fixtureEmptyRules fixtureState fixtureSeed = fixtureSeed := by
  apply Set.Subset.antisymm
  · exact
      leastRuleClosure_least_of_seed_and_rules
        (R := fixtureEmptyRules) (W := fixtureState) (seed := fixtureSeed)
        (S := fixtureSeed)
        (by intro q hq; exact hq)
        (by intro r hr; cases hr)
  · exact seed_subset_leastRuleClosure (R := fixtureEmptyRules) (W := fixtureState) (seed := fixtureSeed)

theorem fixture_pullback_not_in_emptyRules_closure :
    strongPullbackQuery ∉ leastRuleClosure fixtureEmptyRules fixtureState fixtureSeed := by
  rw [fixture_emptyRules_closure_eq_seed]
  exact fixture_pullback_not_in_seed

/-! ## Explicit bounded-time stabilization fixture -/

abbrev BState := Mettapedia.Logic.EvidenceQuantale.BinaryEvidence
abbrev BQuery := Bool

noncomputable instance : EvidenceType BState := inferInstance

/-- Query-indexed evidence is state-only for the finite Bool fixture. -/
noncomputable instance : BinaryWorldModel BState BQuery where
  evidence := fun W _q => W
  evidence_add := by
    intro W₁ W₂ _q
    rfl

def boolRules : RuleSet BState BQuery := (∅ : Set (WMConsequenceRuleOn BState BQuery))
def boolSeed : Set BQuery := { true }
noncomputable def boolState : BState := 0

theorem fixture_bool_bounded_time_stabilization (m : ℕ) (hm : Fintype.card BQuery ≤ m) :
    immediateIter (State := BState) (Query := BQuery) boolRules boolState boolSeed m =
      immediateIter (State := BState) (Query := BQuery) boolRules boolState boolSeed
        (Fintype.card BQuery) := by
  exact
    immediateIter_eq_card_of_ge_card_of_finite
      (State := BState) (Query := BQuery)
      (R := boolRules) (W := boolState) (seed := boolSeed) m hm

theorem fixture_bool_stable_at_card :
    immediateIter (State := BState) (Query := BQuery) boolRules boolState boolSeed
        (Fintype.card BQuery) =
      immediateIter (State := BState) (Query := BQuery) boolRules boolState boolSeed
        (Fintype.card BQuery + 1) := by
  exact
    immediateIter_stable_at_card_of_finite
      (State := BState) (Query := BQuery)
      (R := boolRules) (W := boolState) (seed := boolSeed)

end Mettapedia.Logic.PLNWorldModelFixpointClosureRegression
