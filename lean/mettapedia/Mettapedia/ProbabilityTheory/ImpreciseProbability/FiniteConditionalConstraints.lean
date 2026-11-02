import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
import Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets
import Mettapedia.ProbabilityTheory.FiniteEventMass
import Mettapedia.ProbabilityTheory.MassSemantics

/-!+# Finite conditional constraints and their credal models

Intervals have rational endpoints; models are real-valued finite probability
distributions. Conditional constraints are homogeneous inequalities on event
masses. Their satisfaction does not require positive conditioning mass, whereas
a numerical conditional answer does. These are simultaneous constraints, not
an exception-handling or preferential default semantics.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.FiniteConditionalConstraints

open scoped BigOperators ENNReal
open ProjectiveCredal PrecisePrevision FiniteEventMass

abbrev Distribution (Ω : Type*) [Fintype Ω] := PrecisePrevision.FiniteWeights Ω
abbrev Event (Ω : Type*) := Ω → Bool

structure Constraint (Ω : Type*) where
  event : Event Ω
  condition : Event Ω
  lower : ℚ
  upper : ℚ
  nonneg : 0 ≤ lower
  ordered : lower ≤ upper
  bounded : upper ≤ 1

abbrev KnowledgeBase (Ω : Type*) := List (Constraint Ω)

variable {Ω : Type*} [Fintype Ω]

def Constraint.Holds (constraint : Constraint Ω) (weight : Ω → ℝ) : Prop :=
  (constraint.lower : ℝ) * mass weight constraint.condition ≤
      mass weight (fun w => constraint.event w && constraint.condition w) ∧
    mass weight (fun w => constraint.event w && constraint.condition w) ≤
      (constraint.upper : ℝ) * mass weight constraint.condition

def Satisfies (base : KnowledgeBase Ω) (weight : Ω → ℝ) : Prop :=
  ∀ constraint ∈ base, constraint.Holds weight

def models (base : KnowledgeBase Ω) : Set (Distribution Ω) := {p | Satisfies base p.weight}

def Consistent (base : KnowledgeBase Ω) : Prop := (models base).Nonempty

theorem mass_scale (weight : Ω → ℝ) (scale : ℝ) (event : Event Ω) :
    mass (fun w => scale * weight w) event = scale * mass weight event := by
  simp [mass, Finset.mul_sum, mul_ite]

theorem Constraint.holds_scale (constraint : Constraint Ω) (weight : Ω → ℝ)
    (scale : ℝ) (positive : 0 < scale) :
    constraint.Holds (fun w => scale * weight w) ↔ constraint.Holds weight := by
  simp only [Constraint.Holds, mass_scale]
  rw [mul_left_comm (constraint.lower : ℝ) scale, mul_left_comm (constraint.upper : ℝ) scale]
  exact and_congr (mul_le_mul_iff_right₀ positive) (mul_le_mul_iff_right₀ positive)

theorem satisfies_scale (base : KnowledgeBase Ω) (weight : Ω → ℝ) (scale : ℝ) (positive : 0 < scale) :
    Satisfies base (fun w => scale * weight w) ↔ Satisfies base weight := by
  simp only [Satisfies, Constraint.holds_scale _ _ _ positive]

theorem intersection_mass_le (weight : Ω → ℝ) (nonnegative : ∀ w, 0 ≤ weight w)
    (event condition : Event Ω) :
    mass weight (fun w => event w && condition w) ≤ mass weight condition :=
  FiniteEventMass.mono weight nonnegative (fun _ h => (Bool.and_eq_true_iff.mp h).2)

theorem intersection_mass_zero (weight : Ω → ℝ) (nonnegative : ∀ w, 0 ≤ weight w)
    (event condition : Event Ω) (zero : mass weight condition = 0) :
    mass weight (fun w => event w && condition w) = 0 :=
  le_antisymm (zero ▸ intersection_mass_le weight nonnegative event condition)
    (nonneg weight nonnegative _)

theorem Constraint.holds_of_zero (constraint : Constraint Ω) (p : Distribution Ω)
    (zero : mass p.weight constraint.condition = 0) : constraint.Holds p.weight := by
  simp [Constraint.Holds, zero, intersection_mass_zero p.weight p.nonneg _ _ zero]

noncomputable def conditionalValue (p : Distribution Ω) (event condition : Event Ω) : ℝ :=
  mass p.weight (fun w => event w && condition w) / mass p.weight condition

theorem conditionalValue_mem_unit (p : Distribution Ω) (event condition : Event Ω)
    (positive : 0 < mass p.weight condition) : conditionalValue p event condition ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨div_nonneg (nonneg p.weight p.nonneg _) positive.le,
    (div_le_one positive).mpr (intersection_mass_le p.weight p.nonneg event condition)⟩

theorem Constraint.holds_iff_conditional (constraint : Constraint Ω) (p : Distribution Ω)
    (positive : 0 < mass p.weight constraint.condition) :
    constraint.Holds p.weight ↔ conditionalValue p constraint.event constraint.condition ∈
      Set.Icc (constraint.lower : ℝ) (constraint.upper : ℝ) := by
  simp only [Constraint.Holds, conditionalValue, Set.mem_Icc]
  exact and_congr (le_div_iff₀ positive).symm (div_le_iff₀ positive).symm

/-- Use the existing optional mass readout; no zero-denominator numerical answer is invented. -/
noncomputable def conditionalMass (p : Distribution Ω) (condition : Event Ω) : MassSemantics (Event Ω) where
  queryMass event := ENNReal.ofReal (mass p.weight (fun w => event w && condition w))
  totalMass := ENNReal.ofReal (mass p.weight condition)
  queryMass_le_total event := ENNReal.ofReal_le_ofReal (intersection_mass_le p.weight p.nonneg event condition)
  totalMass_ne_top := ENNReal.ofReal_ne_top

noncomputable def conditionalReadout (p : Distribution Ω) (event condition : Event Ω) : Option ℝ≥0∞ :=
  (conditionalMass p condition).query event

theorem conditionalReadout_none_iff (p : Distribution Ω) (event condition : Event Ω) :
    conditionalReadout p event condition = none ↔ mass p.weight condition = 0 := by
  have nonnegative := nonneg p.weight p.nonneg condition
  simp only [conditionalReadout, MassSemantics.query, conditionalMass, ite_eq_left_iff,
    reduceCtorEq, imp_false, not_not, ENNReal.ofReal_eq_zero]
  exact ⟨fun h => le_antisymm h nonnegative, fun h => h.le⟩

theorem conditionalReadout_positive (p : Distribution Ω) (event condition : Event Ω)
    (positive : 0 < mass p.weight condition) :
    conditionalReadout p event condition = some (ENNReal.ofReal (conditionalValue p event condition)) := by
  simp [conditionalReadout, MassSemantics.query, MassSemantics.queryProb, conditionalMass,
    ENNReal.ofReal_ne_zero_iff.mpr positive, conditionalValue, ENNReal.ofReal_div_of_pos positive]

/-- A point-valued probabilistic assertion, with no confidence coordinate. -/
def pointConstraint (event condition : Event Ω) (value : ℚ) (nonnegative : 0 ≤ value) (bounded : value ≤ 1) :
    Constraint Ω := ⟨event, condition, value, value, nonnegative, le_rfl, bounded⟩

theorem pointConstraint_iff (p : Distribution Ω) (event condition : Event Ω) (value : ℚ)
    (nonnegative : 0 ≤ value) (bounded : value ≤ 1) (positive : 0 < mass p.weight condition) :
    (pointConstraint event condition value nonnegative bounded).Holds p.weight ↔
      conditionalValue p event condition = (value : ℝ) := by
  rw [Constraint.holds_iff_conditional _ p positive]
  exact le_antisymm_iff.symm.trans (by simp [pointConstraint, eq_comm])

/-! ## Scaled feasible tables: retain all worlds, including those outside the condition -/

def ScaledFeasible (base : KnowledgeBase Ω) (condition : Event Ω) (weight : Ω → ℝ) : Prop :=
  (∀ w, 0 ≤ weight w) ∧ Satisfies base weight ∧ mass weight condition = 1

theorem scale_model (base : KnowledgeBase Ω) (p : Distribution Ω) (member : p ∈ models base)
    (condition : Event Ω) (positive : 0 < mass p.weight condition) :
    ScaledFeasible base condition (fun w => (mass p.weight condition)⁻¹ * p.weight w) := by
  refine ⟨fun w => mul_nonneg (inv_nonneg.mpr positive.le) (p.nonneg w), ?_, ?_⟩
  · exact (satisfies_scale base p.weight _ (inv_pos.mpr positive)).mpr member
  · rw [mass_scale, inv_mul_cancel₀ positive.ne']

theorem scaled_total_positive {base : KnowledgeBase Ω} {condition : Event Ω} {weight : Ω → ℝ}
    (feasible : ScaledFeasible base condition weight) : 0 < ∑ w, weight w := by
  have bound : mass weight condition ≤ ∑ w, weight w := by
    unfold mass
    exact Finset.sum_le_sum fun w _ => by split_ifs <;> simp [feasible.1 w]
  linarith [feasible.2.2]

noncomputable def normalizedScaled {base : KnowledgeBase Ω} {condition : Event Ω} {weight : Ω → ℝ}
    (feasible : ScaledFeasible base condition weight) : Distribution Ω where
  weight w := (∑ w, weight w)⁻¹ * weight w
  nonneg w := mul_nonneg (inv_nonneg.mpr (scaled_total_positive feasible).le) (feasible.1 w)
  total := by rw [← Finset.mul_sum, inv_mul_cancel₀ (scaled_total_positive feasible).ne']

theorem normalizedScaled_model {base : KnowledgeBase Ω} {condition : Event Ω} {weight : Ω → ℝ}
    (feasible : ScaledFeasible base condition weight) : normalizedScaled feasible ∈ models base :=
  (satisfies_scale base weight _ (inv_pos.mpr (scaled_total_positive feasible))).mpr feasible.2.1

theorem normalizedScaled_support {base : KnowledgeBase Ω} {condition : Event Ω} {weight : Ω → ℝ}
    (feasible : ScaledFeasible base condition weight) : 0 < mass (normalizedScaled feasible).weight condition := by
  change 0 < mass (fun w => (∑ w, weight w)⁻¹ * weight w) condition
  rw [mass_scale, feasible.2.2, mul_one]
  exact inv_pos.mpr (scaled_total_positive feasible)

theorem normalizedScaled_conditional {base : KnowledgeBase Ω} {condition : Event Ω} {weight : Ω → ℝ}
    (feasible : ScaledFeasible base condition weight) (event : Event Ω) :
    conditionalValue (normalizedScaled feasible) event condition = mass weight (fun w => event w && condition w) := by
  unfold conditionalValue
  change mass (fun w => (∑ w, weight w)⁻¹ * weight w) _ / mass (fun w => (∑ w, weight w)⁻¹ * weight w) _ = _
  rw [mass_scale, mass_scale, feasible.2.2, mul_one]
  exact mul_div_cancel_left₀ _ (inv_ne_zero (scaled_total_positive feasible).ne')

def queryValues (base : KnowledgeBase Ω) (event condition : Event Ω) : Set ℝ :=
  {value | ∃ p ∈ models base, 0 < mass p.weight condition ∧ conditionalValue p event condition = value}

theorem queryValues_scaled (base : KnowledgeBase Ω) (event condition : Event Ω) (value : ℝ) :
    value ∈ queryValues base event condition ↔
      ∃ weight, ScaledFeasible base condition weight ∧ mass weight (fun w => event w && condition w) = value := by
  constructor
  · rintro ⟨p, member, positive, equal⟩
    refine ⟨_, scale_model base p member condition positive, ?_⟩
    rw [mass_scale]
    simpa only [conditionalValue, div_eq_mul_inv, mul_comm] using equal
  · rintro ⟨weight, feasible, equal⟩
    exact ⟨normalizedScaled feasible, normalizedScaled_model feasible, normalizedScaled_support feasible,
      (normalizedScaled_conditional feasible event).trans equal⟩

theorem queryValues_subset_unit (base : KnowledgeBase Ω) (event condition : Event Ω) :
    queryValues base event condition ⊆ Set.Icc (0 : ℝ) 1 := by
  rintro _ ⟨p, _, positive, rfl⟩
  exact conditionalValue_mem_unit p event condition positive

/-! ## The same models as a compact convex credal set -/

def eventGamble (event : Event Ω) : Gamble Ω := fun w => if event w then 1 else 0

theorem prevision_event (p : Distribution Ω) (event : Event Ω) :
    p.toPrecisePrevision (eventGamble event) = mass p.weight event := by
  simp [FiniteWeights.toPrecisePrevision_apply, eventGamble, mass, mul_ite]

def credalModels (base : KnowledgeBase Ω) : CredalPrevisionSet Ω :=
  {P | ∀ c ∈ base, (c.lower : ℝ) * P (eventGamble c.condition) ≤
        P (eventGamble (fun w => c.event w && c.condition w)) ∧
      P (eventGamble (fun w => c.event w && c.condition w)) ≤
        (c.upper : ℝ) * P (eventGamble c.condition)}

theorem toPrevision_model_iff (base : KnowledgeBase Ω) (p : Distribution Ω) :
    p.toPrecisePrevision ∈ credalModels base ↔ p ∈ models base := by
  simp only [credalModels, models, Set.mem_ofPred_eq, Satisfies, Constraint.Holds, prevision_event]

theorem credalModels_eq_image (base : KnowledgeBase Ω) :
    credalModels base = FiniteWeights.toPrecisePrevision '' models base := by
  classical
  ext P
  constructor
  · intro hP
    refine ⟨FiniteWeights.ofPrecisePrevision P, ?_, FiniteWeights.toPrecisePrevision_ofPrecisePrevision P⟩
    rw [← toPrevision_model_iff, FiniteWeights.toPrecisePrevision_ofPrecisePrevision]
    exact hP
  · rintro ⟨p, hp, rfl⟩
    exact (toPrevision_model_iff base p).mpr hp

theorem credalModels_nonempty_iff (base : KnowledgeBase Ω) :
    (credalModels base).Nonempty ↔ Consistent base := by
  rw [credalModels_eq_image, Set.image_nonempty]
  rfl

omit [Fintype Ω] in
theorem credalModels_convex (base : KnowledgeBase Ω) : (credalModels base).IsConvex := by
  intro P hP Q hQ t ht0 ht1 c member
  have hp := hP c member
  have hq := hQ c member
  change (c.lower : ℝ) * (t * P (eventGamble c.condition) + (1-t) * Q (eventGamble c.condition)) ≤
      t * P (eventGamble (fun w => c.event w && c.condition w)) +
        (1-t) * Q (eventGamble (fun w => c.event w && c.condition w)) ∧
    t * P (eventGamble (fun w => c.event w && c.condition w)) +
        (1-t) * Q (eventGamble (fun w => c.event w && c.condition w)) ≤
      (c.upper : ℝ) * (t * P (eventGamble c.condition) + (1-t) * Q (eventGamble c.condition))
  constructor
  · nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hp.1), mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hq.1)]
  · nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hp.2), mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hq.2)]

noncomputable section Topology

variable [DecidableEq Ω]
local instance : TopologicalSpace (PrecisePrevision Ω) := FiniteWeights.finiteEvaluationTopology

theorem credalModels_closed (base : KnowledgeBase Ω) : IsClosed (credalModels base) := by
  change IsClosed {P | ∀ c ∈ base, _}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro _
  exact (isClosed_le (continuous_const.mul (FiniteWeights.eval_continuous _))
    (FiniteWeights.eval_continuous _)).inter
      (isClosed_le (FiniteWeights.eval_continuous _)
        (continuous_const.mul (FiniteWeights.eval_continuous _)))

theorem credalModels_compact (base : KnowledgeBase Ω) : IsCompact (credalModels base) :=
  FiniteWeights.finiteEvaluationTopology_isCompact_of_isClosed _ (credalModels_closed base)

/-- Unconditional envelopes use the existing compact-credal attainment theorem. -/
theorem event_lower_attained (base : KnowledgeBase Ω) (consistent : Consistent base) (event : Event Ω) :
    ∃ p ∈ models base, mass p.weight event = lowerEnvelope (credalModels base) (eventGamble event) := by
  obtain ⟨P, member, attained⟩ := lowerEnvelope_exists_mem_eq_of_isCompact _ (credalModels_compact base)
    ((credalModels_nonempty_iff base).mpr consistent) _ (FiniteWeights.eval_continuous _).continuousOn
  rw [credalModels_eq_image] at member
  obtain ⟨p, member, rfl⟩ := member
  exact ⟨p, member, (prevision_event p event).symm.trans attained⟩

theorem event_upper_attained (base : KnowledgeBase Ω) (consistent : Consistent base) (event : Event Ω) :
    ∃ p ∈ models base, mass p.weight event = upperEnvelope (credalModels base) (eventGamble event) := by
  obtain ⟨P, member, attained⟩ := upperEnvelope_exists_mem_eq_of_isCompact _ (credalModels_compact base)
    ((credalModels_nonempty_iff base).mpr consistent) _ (FiniteWeights.eval_continuous _).continuousOn
  rw [credalModels_eq_image] at member
  obtain ⟨p, member, rfl⟩ := member
  exact ⟨p, member, (prevision_event p event).symm.trans attained⟩

end Topology

/-- A posterior is an observation of a model, not necessarily another model of the original base. -/
noncomputable def conditioned (p : Distribution Ω) (condition : Event Ω) (positive : 0 < mass p.weight condition) :
    Distribution Ω where
  weight w := if condition w then p.weight w / mass p.weight condition else 0
  nonneg w := by split_ifs <;> simp [div_nonneg (p.nonneg w) positive.le]
  total := by
    have numerator : (∑ w, if condition w then p.weight w / mass p.weight condition else 0) =
        mass p.weight condition / mass p.weight condition := by
      simp [mass, Finset.sum_div, ite_div]
    rw [numerator, div_self positive.ne']

theorem conditioned_event (p : Distribution Ω) (event condition : Event Ω)
    (positive : 0 < mass p.weight condition) :
    mass (conditioned p condition positive).weight event = conditionalValue p event condition := by
  simp only [mass, conditioned, conditionalValue, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  by_cases he : event w = true <;> by_cases hc : condition w = true <;> simp [he, hc]

def posteriorCredalModels (base : KnowledgeBase Ω) (condition : Event Ω) : CredalPrevisionSet Ω :=
  {P | ∃ p ∈ models base, ∃ positive : 0 < mass p.weight condition,
    (conditioned p condition positive).toPrecisePrevision = P}

theorem posterior_values (base : KnowledgeBase Ω) (event condition : Event Ω) :
    (fun P : PrecisePrevision Ω => P (eventGamble event)) '' posteriorCredalModels base condition =
      queryValues base event condition := by
  ext value
  constructor
  · rintro ⟨P, ⟨p, member, positive, rfl⟩, equal⟩
    exact ⟨p, member, positive, by simpa only [prevision_event, conditioned_event] using equal⟩
  · rintro ⟨p, member, positive, equal⟩
    exact ⟨_, ⟨p, member, positive, rfl⟩, by simpa only [prevision_event, conditioned_event] using equal⟩

end Mettapedia.ProbabilityTheory.ImpreciseProbability.FiniteConditionalConstraints
