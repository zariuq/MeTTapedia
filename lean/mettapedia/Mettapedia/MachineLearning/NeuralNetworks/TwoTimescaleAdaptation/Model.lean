import Mathlib.Tactic

/-!
# Two-timescale adaptation: state/weight reachability

This file gives the architecture-agnostic linear-effect model for fast state
and periodic weight consolidation.  The output space may itself be a space of
input-indexed functions, so the model does not assume attention, a KV cache,
or any particular neural architecture.

The central distinction is between two independently checkable images:

* the image of `fastEffect`, which determines which shifts runtime state can
  express; and
* the image of `slowEffect`, which determines which shifts a weight update can
  retain after the fast state is reset.

The concrete two-dimensional fixtures make both failures non-vacuous.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation

/-! ## Common linear-effect model -/

/-- A two-timescale model at the level of readout effects.  `Output` can be an
entire response function, not merely one scalar prediction. -/
structure LinearEffectModel
    (Slow Fast Output : Type*)
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    [AddCommMonoid Output] [Module ℝ Output] where
  slowEffect : Slow →ₗ[ℝ] Output
  fastEffect : Fast →ₗ[ℝ] Output

section Model

variable {Slow Fast Output : Type*}
  [AddCommMonoid Slow] [Module ℝ Slow]
  [AddCommMonoid Fast] [Module ℝ Fast]
  [AddCommMonoid Output] [Module ℝ Output] [IsLeftCancelAdd Output]

/-- Readout effect before consolidation: frozen-weight effect plus fast state. -/
noncomputable def adaptedReadout
    (model : LinearEffectModel Slow Fast Output)
    (slow : Slow) (fast : Fast) : Output :=
  model.slowEffect slow + model.fastEffect fast

/-- Consolidation adds a weight delta and resets the bounded fast state. -/
noncomputable def consolidateByDelta
    (slow : Slow) (delta : Slow) : Slow × Fast :=
  (slow + delta, 0)

/-- Readout from an explicit pair of slow parameters and fast state. -/
noncomputable def pairedReadout
    (model : LinearEffectModel Slow Fast Output)
    (state : Slow × Fast) : Output :=
  model.slowEffect state.1 + model.fastEffect state.2

/-- A concrete consolidation is faithful when resetting the fast state leaves
the complete readout effect unchanged. -/
def FaithfulConsolidation
    (model : LinearEffectModel Slow Fast Output)
    (slow : Slow) (fast : Fast) (delta : Slow) : Prop :=
  pairedReadout model (consolidateByDelta (Fast := Fast) slow delta) =
    adaptedReadout model slow fast

/-- Exact operational criterion for one proposed weight delta. -/
theorem faithfulConsolidation_iff_effect_eq
    (model : LinearEffectModel Slow Fast Output)
    (slow : Slow) (fast : Fast) (delta : Slow) :
    FaithfulConsolidation model slow fast delta ↔
      model.slowEffect delta = model.fastEffect fast := by
  simp only [FaithfulConsolidation, pairedReadout, consolidateByDelta,
    adaptedReadout, map_add, map_zero, add_zero]
  constructor <;> intro h
  · exact add_left_cancel h
  · exact congrArg (model.slowEffect slow + ·) h

/-- T1 span/image crown: some faithful consolidation exists exactly when the
fast state's effect lies in the reachable image of weight updates. -/
theorem exists_faithfulConsolidation_iff_mem_range
    (model : LinearEffectModel Slow Fast Output)
    (slow : Slow) (fast : Fast) :
    (∃ delta : Slow, FaithfulConsolidation model slow fast delta) ↔
      model.fastEffect fast ∈ LinearMap.range model.slowEffect := by
  constructor
  · rintro ⟨delta, hfaithful⟩
    exact ⟨delta, (faithfulConsolidation_iff_effect_eq
      model slow fast delta).1 hfaithful⟩
  · rintro ⟨delta, hdelta⟩
    exact ⟨delta, (faithfulConsolidation_iff_effect_eq
      model slow fast delta).2 hdelta⟩

end Model

/-! ## Finite squared prediction error -/

/-- Squared coordinate error for finite-dimensional readout effects. -/
noncomputable def effectSquaredError
    {Index : Type*} [Fintype Index]
    (predicted required : Index → ℝ) : ℝ :=
  ∑ i, (predicted i - required i) ^ 2

theorem effectSquaredError_nonneg
    {Index : Type*} [Fintype Index]
    (predicted required : Index → ℝ) :
    0 ≤ effectSquaredError predicted required := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem effectSquaredError_eq_zero_of_eq
    {Index : Type*} [Fintype Index]
    {predicted required : Index → ℝ} (h : predicted = required) :
    effectSquaredError predicted required = 0 := by
  subst predicted
  simp [effectSquaredError]

/-! ## T1: a genuinely lossy consolidation fixture -/

/-- Embed one slow degree of freedom into the first of two output axes. -/
noncomputable def firstAxisMap :
    (Fin 1 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun value index := if index = 0 then value 0 else 0
  map_add' left right := by
    funext index
    fin_cases index <;> simp
  map_smul' scalar value := by
    funext index
    fin_cases index <;> simp

/-- Slow weights can change only the first axis; fast state can express both. -/
noncomputable def slowAxisFastFullModel :
    LinearEffectModel (Fin 1 → ℝ) (Fin 2 → ℝ) (Fin 2 → ℝ) where
  slowEffect := firstAxisMap
  fastEffect := LinearMap.id

/-- A fast-state effect transverse to the reachable weight-update image. -/
noncomputable def secondAxisEffect : Fin 2 → ℝ :=
  fun index => if index = 1 then 1 else 0

/-- Every attempted weight delta has loss `delta² + 1` on the transverse
fixture.  Thus the irreducible loss is an exact unit, not merely nonzero. -/
theorem slowAxis_consolidationLoss_exact (delta : Fin 1 → ℝ) :
    effectSquaredError (firstAxisMap delta) secondAxisEffect =
      (delta 0) ^ 2 + 1 := by
  simp [effectSquaredError, firstAxisMap, secondAxisEffect,
    Fin.sum_univ_two]

theorem slowAxis_consolidationLoss_at_least_one (delta : Fin 1 → ℝ) :
    1 ≤ effectSquaredError (firstAxisMap delta) secondAxisEffect := by
  rw [slowAxis_consolidationLoss_exact]
  nlinarith [sq_nonneg (delta 0)]

theorem slowAxis_consolidationLoss_minimum_exact :
    effectSquaredError (firstAxisMap (0 : Fin 1 → ℝ)) secondAxisEffect = 1 := by
  rw [slowAxis_consolidationLoss_exact]
  simp

/-- Negative faithfulness fixture: the second-axis state cannot be burned into
first-axis-only weights. -/
theorem secondAxisEffect_not_weightReachable :
    secondAxisEffect ∉ LinearMap.range slowAxisFastFullModel.slowEffect := by
  rintro ⟨delta, hdelta⟩
  have hcoordinate := congrFun hdelta (1 : Fin 2)
  norm_num [slowAxisFastFullModel, firstAxisMap, secondAxisEffect] at hcoordinate

theorem secondAxisEffect_no_faithfulConsolidation (slow : Fin 1 → ℝ) :
    ¬ ∃ delta : Fin 1 → ℝ,
      FaithfulConsolidation slowAxisFastFullModel slow secondAxisEffect delta := by
  rw [exists_faithfulConsolidation_iff_mem_range]
  exact secondAxisEffect_not_weightReachable

/-! ## T7: pure-state sufficiency and its exact complement -/

/-- A task stream is stationary at `required` when every period asks for the
same complete readout effect. -/
def IsStationaryTask {Output : Type*}
    (task : ℕ → Output) (required : Output) : Prop :=
  ∀ period, task period = required

/-- Pure fast-state adaptation can serve the requested effect exactly while
remaining within its declared evidence capacity. -/
def PureFastStateCanServe
    {Slow Fast Output : Type*}
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    [AddCommMonoid Output] [Module ℝ Output]
    (model : LinearEffectModel Slow Fast Output)
    (capacity load : ℕ) (required : Output) : Prop :=
  load ≤ capacity ∧ required ∈ LinearMap.range model.fastEffect

/-- The complete pure-fast regime additionally requires a stationary task. -/
def PureFastStateRegime
    {Slow Fast Output : Type*}
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    [AddCommMonoid Output] [Module ℝ Output]
    (model : LinearEffectModel Slow Fast Output)
    (capacity load : ℕ) (task : ℕ → Output) (required : Output) : Prop :=
  IsStationaryTask task required ∧
    PureFastStateCanServe model capacity load required

/-- Independent operational pressure for leaving pure fast state: either its
bounded evidence store is overloaded or the requested effect is unreachable. -/
def ConsolidationPressure
    {Slow Fast Output : Type*}
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    [AddCommMonoid Output] [Module ℝ Output]
    (model : LinearEffectModel Slow Fast Output)
    (capacity load : ℕ) (required : Output) : Prop :=
  capacity < load ∨ required ∉ LinearMap.range model.fastEffect

/-- Exact strategic boundary, including nonstationarity as a separate reason
that the declared pure-state regime can fail. -/
theorem not_pureFastStateRegime_iff
    {Slow Fast Output : Type*}
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    [AddCommMonoid Output] [Module ℝ Output]
    (model : LinearEffectModel Slow Fast Output)
    (capacity load : ℕ) (task : ℕ → Output) (required : Output) :
    ¬ PureFastStateRegime model capacity load task required ↔
      ¬ IsStationaryTask task required ∨
        ConsolidationPressure model capacity load required := by
  simp only [PureFastStateRegime, PureFastStateCanServe,
    ConsolidationPressure, not_and_or, not_le]

/-- Under the mission's stationary-task hypothesis, the complement is exactly
capacity overflow or failure of fast-state reachability. -/
theorem stationary_not_pureFastStateRegime_iff_pressure
    {Slow Fast Output : Type*}
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    [AddCommMonoid Output] [Module ℝ Output]
    (model : LinearEffectModel Slow Fast Output)
    (capacity load : ℕ) (task : ℕ → Output) (required : Output)
    (hstationary : IsStationaryTask task required) :
    ¬ PureFastStateRegime model capacity load task required ↔
      ConsolidationPressure model capacity load required := by
  rw [not_pureFastStateRegime_iff]
  simp [hstationary]

/-- Exact weight-side capability, intentionally distinct from pressure to
consolidate: pressure need not imply that weights can represent the shift. -/
def WeightConsolidationCanServe
    {Slow Fast Output : Type*}
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    [AddCommMonoid Output] [Module ℝ Output]
    (model : LinearEffectModel Slow Fast Output) (required : Output) : Prop :=
  required ∈ LinearMap.range model.slowEffect

/-- Operational necessity with feasibility: some weight delta realizes the
required shift, while every exact fast-state realization would be over
capacity.  If no fast realization exists, the second clause holds
non-vacuously through the first weight-reachability clause. -/
def FeasibleWeightConsolidationNecessary
    {Slow Fast Output : Type*}
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    [AddCommMonoid Output] [Module ℝ Output]
    (model : LinearEffectModel Slow Fast Output)
    (capacity load : ℕ) (required : Output) : Prop :=
  (∃ delta : Slow, model.slowEffect delta = required) ∧
    ∀ fast : Fast, model.fastEffect fast = required → capacity < load

/-- T7 necessity/sufficiency crown: feasible weight consolidation is
operationally necessary exactly when weights can express the shift and either
the evidence load exceeds capacity or fast state cannot express the shift. -/
theorem feasibleWeightConsolidationNecessary_iff
    {Slow Fast Output : Type*}
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    [AddCommMonoid Output] [Module ℝ Output]
    (model : LinearEffectModel Slow Fast Output)
    (capacity load : ℕ) (required : Output) :
    FeasibleWeightConsolidationNecessary model capacity load required ↔
      WeightConsolidationCanServe model required ∧
        ConsolidationPressure model capacity load required := by
  constructor
  · rintro ⟨hweight, hfastInvalid⟩
    refine ⟨hweight, ?_⟩
    by_cases hover : capacity < load
    · exact Or.inl hover
    · right
      rintro ⟨fast, hfast⟩
      exact hover (hfastInvalid fast hfast)
  · rintro ⟨hweight, hover | hunreachable⟩
    · exact ⟨hweight, fun _fast _hfast => hover⟩
    · refine ⟨hweight, ?_⟩
      intro fast hfast
      exact False.elim (hunreachable ⟨fast, hfast⟩)

/-- Pure fast-state prediction loss. -/
noncomputable def pureFastObjective
    {Slow Fast : Type*} {Index : Type*}
    [Fintype Index]
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    (model : LinearEffectModel Slow Fast (Index → ℝ))
    (required : Index → ℝ) (fast : Fast) : ℝ :=
  effectSquaredError (model.fastEffect fast) required

/-- Consolidated prediction loss plus the declared positive update cost. -/
noncomputable def consolidatedObjective
    {Slow Fast : Type*} {Index : Type*}
    [Fintype Index]
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    (model : LinearEffectModel Slow Fast (Index → ℝ))
    (required : Index → ℝ) (delta : Slow) (updateCost : ℝ) : ℝ :=
  effectSquaredError (model.slowEffect delta) required + updateCost

/-- T7 positive direction: in the stationary, within-capacity reachable
regime, pure fast state attains zero prediction error.  Any equally faithful
weight consolidation has the same zero prediction error but strictly larger
cost when updates cost something. -/
theorem pureFastState_strictly_cheaper_than_faithful_consolidation
    {Slow Fast : Type*} {Index : Type*}
    [Fintype Index]
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    (model : LinearEffectModel Slow Fast (Index → ℝ))
    (capacity load : ℕ) (task : ℕ → (Index → ℝ))
    (required : Index → ℝ) (updateCost : ℝ)
    (hregime : PureFastStateRegime model capacity load task required)
    (hcost : 0 < updateCost) :
    ∃ fast : Fast,
      model.fastEffect fast = required ∧
      pureFastObjective model required fast = 0 ∧
      ∀ delta : Slow, model.slowEffect delta = required →
        effectSquaredError (model.fastEffect fast) required =
            effectSquaredError (model.slowEffect delta) required ∧
          pureFastObjective model required fast <
            consolidatedObjective model required delta updateCost := by
  obtain ⟨fast, hfast⟩ := hregime.2.2
  refine ⟨fast, hfast, ?_, ?_⟩
  · exact effectSquaredError_eq_zero_of_eq hfast
  · intro delta hdelta
    have hfastZero := effectSquaredError_eq_zero_of_eq hfast
    have hslowZero := effectSquaredError_eq_zero_of_eq hdelta
    constructor
    · rw [hfastZero, hslowZero]
    · simp [pureFastObjective, consolidatedObjective, hfastZero, hslowZero, hcost]

/-! ## T7 positive and negative fixtures -/

noncomputable def identityEffectModel (Index : Type*) :
    LinearEffectModel (Index → ℝ) (Index → ℝ) (Index → ℝ) where
  slowEffect := LinearMap.id
  fastEffect := LinearMap.id

noncomputable def unitScalarEffect : Fin 1 → ℝ := fun _ => 1

noncomputable def constantUnitTask : ℕ → (Fin 1 → ℝ) := fun _ => unitScalarEffect

theorem constantUnitTask_stationary :
    IsStationaryTask constantUnitTask unitScalarEffect := by
  intro period
  rfl

theorem identityEffect_pureFast_positiveFixture :
    PureFastStateRegime (identityEffectModel (Fin 1)) 10 5
      constantUnitTask unitScalarEffect := by
  refine ⟨constantUnitTask_stationary, by norm_num, ?_⟩
  exact ⟨unitScalarEffect, rfl⟩

theorem identityEffect_consolidation_adds_cost_fixture :
    ∃ fast : Fin 1 → ℝ,
      pureFastObjective (identityEffectModel (Fin 1)) unitScalarEffect fast = 0 ∧
      ∀ delta : Fin 1 → ℝ,
        (identityEffectModel (Fin 1)).slowEffect delta = unitScalarEffect →
          pureFastObjective (identityEffectModel (Fin 1)) unitScalarEffect fast <
            consolidatedObjective (identityEffectModel (Fin 1))
              unitScalarEffect delta 3 := by
  obtain ⟨fast, _hfast, hzero, hcomparison⟩ :=
    pureFastState_strictly_cheaper_than_faithful_consolidation
      (identityEffectModel (Fin 1)) 10 5 constantUnitTask unitScalarEffect 3
      identityEffect_pureFast_positiveFixture (by norm_num)
  exact ⟨fast, hzero, fun delta hdelta => (hcomparison delta hdelta).2⟩

/-- Opposite reachability fixture: fast state has only the first axis, while
weight consolidation can express both axes. -/
noncomputable def fastAxisSlowFullModel :
    LinearEffectModel (Fin 2 → ℝ) (Fin 1 → ℝ) (Fin 2 → ℝ) where
  slowEffect := LinearMap.id
  fastEffect := firstAxisMap

noncomputable def constantSecondAxisTask : ℕ → (Fin 2 → ℝ) := fun _ => secondAxisEffect

theorem secondAxis_fast_unreachable_weight_reachable_fixture :
    ConsolidationPressure fastAxisSlowFullModel 10 5 secondAxisEffect ∧
      WeightConsolidationCanServe fastAxisSlowFullModel secondAxisEffect := by
  constructor
  · right
    rintro ⟨fast, hfast⟩
    have hcoordinate := congrFun hfast (1 : Fin 2)
    norm_num [fastAxisSlowFullModel, firstAxisMap, secondAxisEffect] at hcoordinate
  · exact ⟨secondAxisEffect, rfl⟩

theorem secondAxis_feasibleConsolidationNecessary_fixture :
    FeasibleWeightConsolidationNecessary
      fastAxisSlowFullModel 10 5 secondAxisEffect := by
  rw [feasibleWeightConsolidationNecessary_iff]
  exact secondAxis_fast_unreachable_weight_reachable_fixture.symm

/-- Capacity alone can force the complement even when the effect is reachable. -/
theorem identityEffect_overCapacity_fixture :
    ConsolidationPressure (identityEffectModel (Fin 1)) 3 4 unitScalarEffect ∧
      WeightConsolidationCanServe (identityEffectModel (Fin 1)) unitScalarEffect := by
  exact ⟨Or.inl (by norm_num), ⟨unitScalarEffect, rfl⟩⟩

theorem identityEffect_overCapacity_requiresConsolidation_fixture :
    FeasibleWeightConsolidationNecessary
      (identityEffectModel (Fin 1)) 3 4 unitScalarEffect := by
  rw [feasibleWeightConsolidationNecessary_iff]
  exact identityEffect_overCapacity_fixture.symm

/-- Negative boundary: pressure to leave fast state does not manufacture a
weight solution.  Here neither the fast nor slow first-axis image contains
the required second-axis effect. -/
noncomputable def bothAxisLimitedModel :
    LinearEffectModel (Fin 1 → ℝ) (Fin 1 → ℝ) (Fin 2 → ℝ) where
  slowEffect := firstAxisMap
  fastEffect := firstAxisMap

theorem consolidationPressure_not_enough_without_weightReachability :
    ConsolidationPressure bothAxisLimitedModel 10 5 secondAxisEffect ∧
      ¬ WeightConsolidationCanServe bothAxisLimitedModel secondAxisEffect := by
  constructor
  · right
    rintro ⟨fast, hfast⟩
    have hcoordinate := congrFun hfast (1 : Fin 2)
    norm_num [bothAxisLimitedModel, firstAxisMap, secondAxisEffect] at hcoordinate
  · rintro ⟨slow, hslow⟩
    have hcoordinate := congrFun hslow (1 : Fin 2)
    norm_num [bothAxisLimitedModel, firstAxisMap, secondAxisEffect] at hcoordinate

#print axioms exists_faithfulConsolidation_iff_mem_range
#print axioms slowAxis_consolidationLoss_at_least_one
#print axioms stationary_not_pureFastStateRegime_iff_pressure
#print axioms feasibleWeightConsolidationNecessary_iff
#print axioms pureFastState_strictly_cheaper_than_faithful_consolidation
#print axioms consolidationPressure_not_enough_without_weightReachability

end Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
