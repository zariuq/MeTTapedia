import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.Accounting
import Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperiment
import Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperimentStochastic

/-!
# Paired-design estimands for bounded search

Estimands are defined before estimators.  A paired comparison fixes task,
world, and budget, so the within-pair signed effect is well defined; a
difference-in-differences contrast records its orientation; and population
inference requires an explicit sampling law --- agreement of two observed
worlds does not determine an unseen world.
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

/-! ## Identification under an additive seed nuisance -/

/-- An explicit response model in which initialization contributes an additive
nuisance shared by the control and treatment run with that seed. -/
structure AdditiveSeedResponse (Seed : Type*) where
  baseline : ℝ
  seedNuisance : Seed → ℝ
  treatmentEffect : ℝ

def controlResponse
    {Seed : Type*} (model : AdditiveSeedResponse Seed) (seed : Seed) : ℝ :=
  model.baseline + model.seedNuisance seed

def treatmentResponse
    {Seed : Type*} (model : AdditiveSeedResponse Seed) (seed : Seed) : ℝ :=
  model.baseline + model.seedNuisance seed + model.treatmentEffect

def pairedContrast
    {Seed : Type*} (model : AdditiveSeedResponse Seed) (seed : Seed) : ℝ :=
  treatmentResponse model seed - controlResponse model seed

/-- Pairing cancels the additive seed nuisance exactly. -/
theorem pairedContrast_eq_treatmentEffect
    {Seed : Type*} (model : AdditiveSeedResponse Seed) (seed : Seed) :
    pairedContrast model seed = model.treatmentEffect := by
  simp only [pairedContrast, treatmentResponse, controlResponse]
  ring

/-- Equal paired responses at one seed identify the treatment effect in the
additive nuisance model. -/
theorem treatmentEffect_eq_of_eq_pairedResponses
    {Seed : Type*} (first second : AdditiveSeedResponse Seed) (seed : Seed)
    (hcontrol : controlResponse first seed = controlResponse second seed)
    (htreatment : treatmentResponse first seed = treatmentResponse second seed) :
    first.treatmentEffect = second.treatmentEffect := by
  calc
    first.treatmentEffect = pairedContrast first seed :=
      (pairedContrast_eq_treatmentEffect first seed).symm
    _ = pairedContrast second seed := by
      simp only [pairedContrast, htreatment, hcontrol]
    _ = second.treatmentEffect := pairedContrast_eq_treatmentEffect second seed

/-- A two-seed family used to expose the unpaired identification failure. -/
def unpairedResponseFamily (observed effect : ℝ) : AdditiveSeedResponse Bool where
  baseline := 0
  seedNuisance := fun seed ↦ if seed then observed - effect else 0
  treatmentEffect := effect

@[simp]
theorem controlResponse_unpairedResponseFamily_false
    (observed effect : ℝ) :
    controlResponse (unpairedResponseFamily observed effect) false = 0 := by
  simp [controlResponse, unpairedResponseFamily]

@[simp]
theorem treatmentResponse_unpairedResponseFamily_true
    (observed effect : ℝ) :
    treatmentResponse (unpairedResponseFamily observed effect) true = observed := by
  simp [treatmentResponse, unpairedResponseFamily]

/-- One control observation at one seed and one treatment observation at a
different seed do not identify the treatment effect, even in the additive
nuisance model. -/
theorem exists_eq_unpairedResponses_ne_treatmentEffect
    (observed effectA effectB : ℝ) (hne : effectA ≠ effectB) :
    ∃ first second : AdditiveSeedResponse Bool,
      controlResponse first false = controlResponse second false ∧
      treatmentResponse first true = treatmentResponse second true ∧
      first.treatmentEffect ≠ second.treatmentEffect := by
  refine ⟨unpairedResponseFamily observed effectA,
    unpairedResponseFamily observed effectB, ?_, ?_, ?_⟩
  · simp
  · simp
  · simpa [unpairedResponseFamily] using hne

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

/-- The interaction is zero exactly when the update-rule contrast is the same
under both architectures.  This is the additive/no-synergy boundary for a
two-by-two design. -/
theorem architectureUpdateInteraction_eq_zero_iff
    (a₀ a₁ b₀ b₁ : ℕ) :
    architectureUpdateInteraction a₀ a₁ b₀ b₁ = 0 ↔
      (b₁ : ℤ) - b₀ = (a₁ : ℤ) - a₀ := by
  unfold architectureUpdateInteraction
  omega

/-- Additive architecture and update contributions have no interaction. -/
theorem architectureUpdateInteraction_additive_eq_zero
    (baseline architectureEffect updateEffect : ℕ) :
    architectureUpdateInteraction
        baseline (baseline + updateEffect)
        (baseline + architectureEffect)
        (baseline + architectureEffect + updateEffect) = 0 := by
  unfold architectureUpdateInteraction
  omega

/-- Three cells of a two-by-two design never identify its interaction: two
possible values for the missing fourth cell give different contrasts while
leaving every observed cell fixed. -/
theorem three_cells_do_not_identify_architectureUpdateInteraction
    (a₀ a₁ b₀ : ℕ) :
    ∃ firstCompletion secondCompletion : ℕ,
      architectureUpdateInteraction a₀ a₁ b₀ firstCompletion ≠
        architectureUpdateInteraction a₀ a₁ b₀ secondCompletion := by
  exact ⟨0, 1, by unfold architectureUpdateInteraction; omega⟩

/-- A positive interaction fixture: the update adds one solve under the first
architecture and four under the second, for a difference-in-differences of
three. -/
theorem architectureUpdateInteraction_positive_example :
    architectureUpdateInteraction 10 11 10 14 = 3 := by
  norm_num [architectureUpdateInteraction]

/-- Equal update gains give the negative/no-interaction fixture. -/
theorem architectureUpdateInteraction_zero_example :
    architectureUpdateInteraction 10 12 13 15 = 0 := by
  norm_num [architectureUpdateInteraction]

/-! ## Population scope boundary -/

/-- A genuine two-draw IID design supplies a marginal world law and the
factorized pair law.  Without such a value, no population claim is licensed by
the deterministic estimands above. -/
structure IIDTwoWorldDesign (World : Type uW) where
  marginal : PMF World
  pairLaw : PMF (World × World)
  pairLaw_factorizes :
    pairLaw = marginal.bind (fun first ↦ marginal.map (fun second ↦ (first, second)))

/-- Agreement with an arbitrary response function on a finite observed set
does not determine the response at any specified unobserved point. -/
theorem exists_eqOn_finset_ne_at
    {World Effect : Type*} [DecidableEq World]
    (observed : Finset World) (values : World → Effect)
    (unseen : World) (hunseen : unseen ∉ observed)
    (outsideA outsideB : Effect) (hne : outsideA ≠ outsideB) :
    ∃ effectsA effectsB : World → Effect,
      Set.EqOn effectsA values (↑observed : Set World) ∧
      Set.EqOn effectsB values (↑observed : Set World) ∧
      effectsA unseen ≠ effectsB unseen := by
  let effectsA : World → Effect := fun world ↦
    if world ∈ observed then values world else outsideA
  let effectsB : World → Effect := fun world ↦
    if world ∈ observed then values world else outsideB
  refine ⟨effectsA, effectsB, ?_, ?_, ?_⟩
  · intro world hworld
    simp only [Finset.mem_coe] at hworld
    simp [effectsA, hworld]
  · intro world hworld
    simp only [Finset.mem_coe] at hworld
    simp [effectsB, hworld]
  · simpa [effectsA, effectsB, hunseen] using hne

/-- Agreement on two observed worlds does not determine behavior in a third
world.  This finite no-go is the assumption boundary behind every population
statement about the two-world campaign. -/
theorem exists_agree_on_pair_ne_at_third
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

#print axioms pairedContrast_eq_treatmentEffect
#print axioms treatmentEffect_eq_of_eq_pairedResponses
#print axioms exists_eq_unpairedResponses_ne_treatmentEffect
#print axioms architectureUpdateInteraction_eq_zero_iff
#print axioms architectureUpdateInteraction_additive_eq_zero
#print axioms three_cells_do_not_identify_architectureUpdateInteraction
#print axioms architectureUpdateInteraction_positive_example
#print axioms architectureUpdateInteraction_zero_example
#print axioms exists_eqOn_finset_ne_at

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
