import Mettapedia.ProbabilityTheory.StochasticInference.Finite
import Mathlib.Algebra.BigOperators.Field

/-!
# Marginal, interval, and model mixture readouts

Bounds follow from event inclusion and nonnegative joint weights.
Mixtures combine query mass and evidence mass in the same units before
normalization. A finite-model prior can be normalized separately from its
likelihood history, which is important for unnormalized factor models.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference

open Mettapedia.ProbabilityTheory.BayesianNetworks
open ExecutableFactorTable ScopedFactorReadout

variable {n : Nat} {domains : Fin n → Nat} {Id : Type*}

namespace State

/-- A marginal includes one entry for each value of the requested variable. -/
def marginal? (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (v : Fin n) : Option (Array ℚ) :=
  let total := mass positive schedule state.tables
  if 0 < total then
    some (Array.ofFn fun value : Fin (domains v) =>
      (mass positive schedule (state.tables ++ [(Event.equalTo positive v value).table])) / total)
  else none

theorem marginal_entry (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (v : Fin n) (values : Array ℚ)
    (answer : state.marginal? positive schedule v = some values)
    (value : Fin (domains v)) :
    values[value.val]? = state.probability? positive schedule (Event.equalTo positive v value) := by
  unfold marginal? at answer
  dsimp only at answer
  split at answer
  · rename_i support
    have same := Option.some.inj answer
    subst values
    simp [probability?, probabilityMasses, expectationMasses, Masses.posterior?, support, value.isLt]
  · contradiction

theorem event_mass_mono (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (lower upper : Event domains)
    (included : ∀ x, lower.holds positive x = true → upper.holds positive x = true) :
    (state.probabilityMasses positive schedule lower).joint ≤
      (state.probabilityMasses positive schedule upper).joint := by
  rw [probabilityMasses_exact, probabilityMasses_exact]
  apply Finset.sum_le_sum
  intro x _
  by_cases inside : lower.holds positive x = true
  · simp [inside, included x inside]
  · rw [if_neg inside]
    split
    · exact state.unnormalized_nonneg positive x
    · exact le_rfl

end State

/-- A completed proof region and a certified overapproximation of the event. -/
structure EventBounds (positive : ∀ v, 0 < domains v) (claim : Event domains) where
  lower : Event domains
  upper : Event domains
  lower_sound : ∀ x, lower.holds positive x = true → claim.holds positive x = true
  upper_sound : ∀ x, claim.holds positive x = true → upper.holds positive x = true

namespace EventBounds

variable {positive : ∀ v, 0 < domains v} {claim : Event domains}

def read? (bounds : EventBounds positive claim) (state : State Id domains)
    (schedule : Schedule n) : Option (ℚ × ℚ) :=
  let z := mass positive schedule state.tables
  if 0 < z then
    some ((state.probabilityMasses positive schedule bounds.lower).joint / z,
      (state.probabilityMasses positive schedule bounds.upper).joint / z)
  else none

theorem sound (bounds : EventBounds positive claim) (state : State Id domains)
    (schedule : Schedule n) (low high value : ℚ)
    (answer : bounds.read? state schedule = some (low, high))
    (exact : state.probability? positive schedule claim = some value) :
    low ≤ value ∧ value ≤ high := by
  unfold read? at answer
  dsimp only at answer
  split at answer
  · rename_i support
    injection answer with interval
    obtain ⟨lower_eq, upper_eq⟩ := Prod.mk.inj interval
    subst low
    subst high
    have normalized : (state.probabilityMasses positive schedule claim).joint /
        mass positive schedule state.tables = value := by
      simpa [State.probability?, State.probabilityMasses, State.expectationMasses,
        Masses.posterior?, support] using exact
    rw [← normalized]
    exact ⟨div_le_div_of_nonneg_right (state.event_mass_mono positive schedule bounds.lower claim
      bounds.lower_sound) support.le,
      div_le_div_of_nonneg_right (state.event_mass_mono positive schedule claim bounds.upper
        bounds.upper_sound) support.le⟩
  · contradiction

end EventBounds

def weightedSum (components : List (ℚ × Masses)) : Masses :=
  ⟨(components.map (fun (w, m) => w * m.joint)).sum,
    (components.map (fun (w, m) => w * m.evidence)).sum⟩

/-- Convert a potential model's masses into units of its normalized prior
before mixing it with other candidate models. -/
def State.normalizedPriorMasses? (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (event : Event domains) : Option Masses :=
  let priorMass := mass positive schedule (state.base.map Potential.table)
  let result := state.probabilityMasses positive schedule event
  if 0 < priorMass then some ⟨result.joint / priorMass, result.evidence / priorMass⟩ else none

/-- The prior partition function calibrates a component's joint likelihood.
Different candidates must interpret observation densities in common units. -/
theorem State.normalizedPriorMasses_exact (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (event : Event domains)
    (supported : 0 < mass positive schedule (state.base.map Potential.table)) :
    let law := fun x => state.unnormalized positive x /
      mass positive schedule (state.base.map Potential.table)
    state.normalizedPriorMasses? positive schedule event =
      some ⟨∑ x, if event.holds positive x then law x else 0, ∑ x, law x⟩ := by
  dsimp only
  rw [State.normalizedPriorMasses?]
  rw [if_pos supported, state.probabilityMasses_exact]
  congr 2
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    split <;> simp_all
  · exact Finset.sum_div _ _ _

/-- Candidate models on the same assignment space, with declared prior
weights. Relative weights suffice for a conditional query. -/
structure Candidate (Id : Type*) (domains : Fin n → Nat) where
  state : State Id domains
  weight : ℚ
  weight_nonneg : 0 ≤ weight

private def Candidate.scored (model : Candidate Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (event : Event domains) : Option (ℚ × Masses) :=
  (model.state.normalizedPriorMasses? positive schedule event).map (fun result => (model.weight, result))

def mixtureMasses? (models : List (Candidate Id domains)) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (event : Event domains) : Option Masses :=
  (models.mapM (m := Option) (fun model => model.scored positive schedule event)).map weightedSum

theorem weightedSum_exact {X : Type*} [Fintype X]
    (components : List (ℚ × (X → ℚ))) (query : X → Bool) :
    weightedSum (components.map (fun (w, law) =>
      (w, ⟨∑ x, if query x then law x else 0, ∑ x, law x⟩))) =
      ⟨∑ x, if query x then (components.map fun (w, law) => w * law x).sum else 0,
        ∑ x, (components.map fun (w, law) => w * law x).sum⟩ := by
  induction components with
  | nil => simp [weightedSum]
  | cons entry rest ih =>
    obtain ⟨weight, law⟩ := entry
    have joint := congrArg Masses.joint ih
    have evidence := congrArg Masses.evidence ih
    simp only [weightedSum, List.map_cons, List.sum_cons] at joint evidence ⊢
    rw [joint, evidence, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : query x = true <;> simp [h]

theorem mixtureMasses_exact (models : List (Candidate Id domains)) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (event : Event domains)
    (supported : ∀ model ∈ models, 0 < mass positive schedule (model.state.base.map Potential.table)) :
    let worldWeight := fun x => (models.map (fun model => model.weight *
      (model.state.unnormalized positive x / mass positive schedule
        (model.state.base.map Potential.table)))).sum
    mixtureMasses? models positive schedule event =
      some ⟨∑ x, if event.holds positive x then worldWeight x else 0, ∑ x, worldWeight x⟩ := by
  let law (model : Candidate Id domains) (x : Config domains) :=
    model.state.unnormalized positive x / mass positive schedule (model.state.base.map Potential.table)
  let pairs := fun (model : Candidate Id domains) =>
    (model.weight, (⟨∑ x, if event.holds positive x then law model x else 0,
      ∑ x, law model x⟩ : Masses))
  have evaluated :
      models.mapM (fun model => model.scored positive schedule event) = some (models.map pairs) := by
    induction models with
    | nil => rfl
    | cons first rest ih =>
      rw [List.mapM_cons, ih (fun model member => supported model (by simp [member]))]
      simp [Candidate.scored, first.state.normalizedPriorMasses_exact positive schedule event
        (supported first (by simp)), pairs, law]
  have exactSum := weightedSum_exact (models.map (fun model => (model.weight, law model)))
    (event.holds positive)
  rw [mixtureMasses?, evaluated]
  simpa [List.map_map, Function.comp_def, pairs, law] using
    congrArg some exactSum

end Mettapedia.ProbabilityTheory.StochasticInference
