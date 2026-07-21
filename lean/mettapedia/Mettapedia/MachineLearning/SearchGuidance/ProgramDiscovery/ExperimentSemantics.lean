import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.Accounting
import Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperiment
import Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperimentStochastic

/-!
# Bounded synthesis experiment semantics

Estimands are defined before estimators.  Deterministic paired effects require
only matched run declarations.  Population inference is a separate layer and
requires an explicit sampling law; two observed worlds alone do not identify
unseen-world effects.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

open Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperiment
open Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperimentStochastic

universe uS uD uW uA uP uT

/-- Every bounded run declares the state, task distribution, world label, arm,
and finite search budget supplied to the experiment channel. -/
structure RunSpec
    (ModelState : Type uS) (TaskDistribution : Type uD)
    (World : Type uW) (Arm : Type uA) where
  modelState : ModelState
  taskDistribution : TaskDistribution
  world : World
  arm : Arm
  budget : ℕ

abbrev DeterministicSynthesisRun
    (ModelState : Type uS) (TaskDistribution : Type uD)
    (World : Type uW) (Arm : Type uA)
    (Program : Type uP) (Target : Type uT) :=
  ExperimentChannel
    (RunSpec ModelState TaskDistribution World Arm)
    (SolveRelation Program Target)

abbrev StochasticSynthesisRun
    (ModelState : Type uS) (TaskDistribution : Type uD)
    (World : Type uW) (Arm : Type uA)
    (Program : Type uP) (Target : Type uT) :=
  StochasticChannel
    (RunSpec ModelState TaskDistribution World Arm)
    (SolveRelation Program Target)

def deterministicSynthesisChannel
    {ModelState : Type uS} {TaskDistribution : Type uD}
    {World : Type uW} {Arm : Type uA}
    {Program : Type uP} {Target : Type uT}
    (run : RunSpec ModelState TaskDistribution World Arm →
      SolveRelation Program Target) :
    DeterministicSynthesisRun ModelState TaskDistribution World Arm Program Target :=
  ⟨run⟩

/-- A paired comparison carries the design facts needed for a within-world
effect: same task distribution, world, and budget. -/
structure PairedRun
    (ModelState : Type uS) (TaskDistribution : Type uD)
    (World : Type uW) (Arm : Type uA) where
  control : RunSpec ModelState TaskDistribution World Arm
  treatment : RunSpec ModelState TaskDistribution World Arm
  sameTask : control.taskDistribution = treatment.taskDistribution
  sameWorld : control.world = treatment.world
  sameBudget : control.budget = treatment.budget

/-- Signed paired effect for any declared finite-relation score. -/
def pairedWithinWorldEffect
    {ModelState : Type uS} {TaskDistribution : Type uD}
    {World : Type uW} {Arm : Type uA}
    {Program : Type uP} {Target : Type uT}
    (score : SolveRelation Program Target → ℕ)
    (channel : DeterministicSynthesisRun ModelState TaskDistribution World Arm Program Target)
    (pair : PairedRun ModelState TaskDistribution World Arm) : ℤ :=
  (score (channel.run pair.treatment) : ℤ) -
    (score (channel.run pair.control) : ℤ)

/-- Cross-world average of two already-paired effects. -/
def twoWorldAveragePairedEffect (first second : ℤ) : ℚ :=
  ((first : ℚ) + (second : ℚ)) / 2

/-- Relabeling the two worlds cannot alter their averaged paired effect. -/
theorem twoWorldAveragePairedEffect_relabel
    (first second : ℤ) :
    twoWorldAveragePairedEffect first second =
      twoWorldAveragePairedEffect second first := by
  unfold twoWorldAveragePairedEffect
  ring

/-- Signed longitudinal increment.  A negative increment is possible for a
single bounded search even though the cumulative relation itself is monotone. -/
def generationIncrement
    {Program : Type uP} {Target : Type uT}
    (score : SolveRelation Program Target → ℕ)
    (previous current : SolveRelation Program Target) : ℤ :=
  (score current : ℤ) - (score previous : ℤ)

/-- Retention/refind is only named after the comparison records the identical
search-budget obligation. -/
structure BudgetMatchedRefind
    (Program : Type uP) (Target : Type uT) where
  previous : SolveRelation Program Target
  rerun : SolveRelation Program Target
  previousBudget : ℕ
  rerunBudget : ℕ
  sameBudget : previousBudget = rerunBudget

def refindRate
    {Program : Type uP} {Target : Type uT}
    [DecidableEq Program] [DecidableEq Target]
    (comparison : BudgetMatchedRefind Program Target) : ℚ :=
  if comparison.previous.card = 0 then 0 else
    ((comparison.previous ∩ comparison.rerun).card : ℚ) /
      comparison.previous.card

/-- Difference-in-differences: whether changing update rule has a different
effect under the second architecture. -/
def architectureUpdateInteraction
    (architectureOneBaseline architectureOneUpdate
      architectureTwoBaseline architectureTwoUpdate : ℕ) : ℤ :=
  ((architectureTwoUpdate : ℤ) - architectureTwoBaseline) -
    ((architectureOneUpdate : ℤ) - architectureOneBaseline)

def portfolioMarginalEffect
    {Program : Type uP} {Target : Type uT}
    [DecidableEq Program] [DecidableEq Target]
    (base addition : SolveRelation Program Target) : ℤ :=
  marginalTargetContribution base addition

/-- Swapping architecture names negates, rather than preserves, the
interaction contrast.  This records the orientation convention explicitly. -/
theorem architectureUpdateInteraction_swap_architectures
    (a₀ a₁ b₀ b₁ : ℕ) :
    architectureUpdateInteraction b₀ b₁ a₀ a₁ =
      -architectureUpdateInteraction a₀ a₁ b₀ b₁ := by
  unfold architectureUpdateInteraction
  omega

/-! ## Population scope boundary -/

/-- A genuine two-draw IID design supplies a marginal world law and the
factorized pair law.  Without such a value, no population claim is licensed by
the deterministic estimands above. -/
structure IIDTwoWorldDesign (World : Type uW) where
  marginal : PMF World
  pairLaw : PMF (World × World)
  pairLaw_factorizes :
    pairLaw = marginal.bind (fun first ↦ marginal.map (fun second ↦ (first, second)))

/-- Agreement on two observed worlds does not determine behavior in a third
world.  This finite no-go is the assumption boundary behind every population
statement about the two-world campaign. -/
theorem two_world_effects_do_not_identify_unseen_world
    (first second : ℤ) :
    ∃ effectsA effectsB : ℕ → ℤ,
      effectsA 0 = first ∧ effectsB 0 = first ∧
      effectsA 1 = second ∧ effectsB 1 = second ∧
      effectsA 2 ≠ effectsB 2 := by
  let effectsA : ℕ → ℤ := fun world ↦
    if world = 0 then first else if world = 1 then second else 0
  let effectsB : ℕ → ℤ := fun world ↦
    if world = 0 then first else if world = 1 then second else 1
  refine ⟨effectsA, effectsB, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [effectsA, effectsB]

/-- A population confidence statement is packaged only together with its
declared sampling design.  The proposition is not manufactured from two
deterministic effects. -/
structure PopulationInferenceClaim (World : Type uW) where
  design : IIDTwoWorldDesign World
  pointEstimate : ℚ
  confidenceStatement : Prop

/-! ## Small design fixtures -/

namespace ExperimentFixtures

inductive Arm where
  | control
  | treatment
  deriving DecidableEq

def runSpec (world : Bool) (arm : Arm) : RunSpec Unit Unit Bool Arm where
  modelState := ()
  taskDistribution := ()
  world := world
  arm := arm
  budget := 10

def paired (world : Bool) : PairedRun Unit Unit Bool Arm where
  control := runSpec world .control
  treatment := runSpec world .treatment
  sameTask := rfl
  sameWorld := rfl
  sameBudget := rfl

def fixtureRun : DeterministicSynthesisRun Unit Unit Bool Arm
    AccountingFixtures.Program AccountingFixtures.Target :=
  deterministicSynthesisChannel fun spec ↦
    match spec.arm with
    | .control => AccountingFixtures.spreadPrograms
    | .treatment => AccountingFixtures.spreadPrograms ∪
        AccountingFixtures.complementaryArm

theorem paired_target_effect_fixture :
    pairedWithinWorldEffect targetCoverage fixtureRun (paired false) = 2 := by
  decide +kernel

theorem interaction_fixture :
    architectureUpdateInteraction 10 11 10 14 = 3 := by
  decide +kernel

def refindFixture : BudgetMatchedRefind
    AccountingFixtures.Program AccountingFixtures.Target where
  previous := AccountingFixtures.spreadPrograms
  rerun := {(.p0, .t0)}
  previousBudget := 20
  rerunBudget := 20
  sameBudget := rfl

theorem refind_rate_fixture : refindRate refindFixture = 1 / 2 := by
  have hprevious : AccountingFixtures.spreadPrograms.card = 2 := by
    decide +kernel
  have hintersection :
      (AccountingFixtures.spreadPrograms ∩
        {(.p0, .t0)}).card = 1 := by
    decide +kernel
  unfold refindRate
  simp only [refindFixture]
  rw [if_neg (by omega : AccountingFixtures.spreadPrograms.card ≠ 0)]
  norm_num [hintersection, hprevious]

end ExperimentFixtures

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
