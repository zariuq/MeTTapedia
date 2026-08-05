import Mathlib

/-!
# Localized task arithmetic

Ortiz-Jimenez et al., *Task Arithmetic in the Tangent Space*
(arXiv:2305.12827), Proposition 2 and Proposition 3, identify spatial
localization of active kernel eigenfunctions as the mechanism that prevents
task interference.  Proposition 3 makes localization necessary when the
nonzero eigenfunctions remain linearly independent on every task domain.

This file isolates the finite algebraic content of those results.  A task is a
finite linear combination of features.  `WeightedTaskArithmetic` asks for
exact noninterference for every vector of task weights, not only the all-ones
sum.  The main results are:

* active-feature localization implies weighted task arithmetic on pairwise
  disjoint domains;
* weighted task arithmetic is exactly equivalent to vanishing cross-task
  effects;
* under local linear independence of the nonzero feature restrictions and a
  disjoint cover by task domains, weighted task arithmetic is equivalent to
  active-feature localization.

The last theorem is the finite, scalar-valued counterpart of Proposition 3.
The local-independence hypothesis is represented both in the source's usual
`LinearIndependent` form and by the coefficient-separation property used in
the proof.

Executable fixtures cover three boundaries.  Coordinate features on two
singleton domains satisfy exact task arithmetic.  Nonlocalized features can
still satisfy it by cancellation when local independence fails.  Removing
that cancellation produces genuine cross-task interference.

No theorem identifies trained neural features with kernel eigenfunctions or
claims approximate noninterference for finite-precision models.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace LocalizedTaskArithmetic

noncomputable section

open scoped BigOperators

variable {Task Point Feature : Type*}

/-- The function represented for one task by finite feature coefficients. -/
def representedTask [Fintype Feature]
    (coefficient : Task → Feature → ℝ)
    (featureValue : Feature → Point → ℝ)
    (task : Task) (point : Point) : ℝ :=
  ∑ feature, coefficient task feature * featureValue feature point

/-- A weighted sum of all represented task effects. -/
def combinedTask [Fintype Task] [Fintype Feature]
    (coefficient : Task → Feature → ℝ)
    (featureValue : Feature → Point → ℝ)
    (weight : Task → ℝ) (point : Point) : ℝ :=
  ∑ task, weight task * representedTask coefficient featureValue task point

/-- The weight vector selecting exactly one task. -/
def unitWeight [DecidableEq Task] (selected : Task) : Task → ℝ :=
  fun task => if task = selected then 1 else 0

/-- Distinct task domains have no common point. -/
def PairwiseDisjointTaskDomains
    (domain : Task → Set Point) : Prop :=
  ∀ ⦃first second : Task⦄, first ≠ second →
    ∀ ⦃point : Point⦄, point ∈ domain first → point ∉ domain second

/-- Every point under consideration belongs to some task domain. -/
def TaskDomainsCover
    (domain : Task → Set Point) : Prop :=
  ∀ point, ∃ task, point ∈ domain task

/-- Every feature with a nonzero coefficient for a task vanishes outside that
task's domain. -/
def ActiveFeaturesLocalized
    (domain : Task → Set Point)
    (coefficient : Task → Feature → ℝ)
    (featureValue : Feature → Point → ℝ) : Prop :=
  ∀ ⦃task feature⦄, coefficient task feature ≠ 0 →
    ∀ ⦃point⦄, point ∉ domain task → featureValue feature point = 0

/-- Relative localization only asks an active feature to vanish on the other
declared task domains. -/
def ActiveFeaturesRelativelyLocalized
    (domain : Task → Set Point)
    (coefficient : Task → Feature → ℝ)
    (featureValue : Feature → Point → ℝ) : Prop :=
  ∀ ⦃task feature⦄, coefficient task feature ≠ 0 →
    ∀ ⦃other⦄, task ≠ other →
      ∀ ⦃point⦄, point ∈ domain other → featureValue feature point = 0

/-- The represented effect of one task vanishes on every other task domain. -/
def NoCrossTaskInterference [Fintype Feature]
    (domain : Task → Set Point)
    (coefficient : Task → Feature → ℝ)
    (featureValue : Feature → Point → ℝ) : Prop :=
  ∀ ⦃task other⦄, task ≠ other →
    ∀ ⦃point⦄, point ∈ domain other →
      representedTask coefficient featureValue task point = 0

/-- Exact task arithmetic for every vector of mixing weights.  On a point in
`domain task`, the combined edit has exactly the selected task's weighted
effect. -/
def WeightedTaskArithmetic [Fintype Task] [Fintype Feature]
    (domain : Task → Set Point)
    (coefficient : Task → Feature → ℝ)
    (featureValue : Feature → Point → ℝ) : Prop :=
  ∀ (weight : Task → ℝ) (task : Task) (point : Point),
    point ∈ domain task →
      combinedTask coefficient featureValue weight point =
        weight task * representedTask coefficient featureValue task point

/-- Features that are nonzero somewhere on one domain. -/
abbrev NonzeroFeatureOn
    (domain : Task → Set Point)
    (featureValue : Feature → Point → ℝ)
    (task : Task) :=
  { feature : Feature //
      ∃ point, point ∈ domain task ∧ featureValue feature point ≠ 0 }

/-- Restrict one nonzero feature to a task domain. -/
def restrictedFeature
    (domain : Task → Set Point)
    (featureValue : Feature → Point → ℝ)
    (task : Task) :
    NonzeroFeatureOn domain featureValue task →
      ({ point // point ∈ domain task } → ℝ) :=
  fun feature point => featureValue feature.1 point.1

/-- The source's "zero or linearly independent on each domain" hypothesis:
after omitting restrictions that are identically zero, the remaining feature
restrictions are linearly independent. -/
def LocallyIndependentOrZero
    (domain : Task → Set Point)
    (featureValue : Feature → Point → ℝ) : Prop :=
  ∀ task,
    LinearIndependent ℝ (restrictedFeature domain featureValue task)

/-- Coefficient form of local independence.  A feature combination that
vanishes on a domain can have a nonzero coefficient only on features whose
restriction to that domain is zero. -/
def LocalCoefficientSeparation [Fintype Feature]
    (domain : Task → Set Point)
    (featureValue : Feature → Point → ℝ) : Prop :=
  ∀ (task : Task) (coefficient : Feature → ℝ),
    (∀ point, point ∈ domain task →
      ∑ feature, coefficient feature * featureValue feature point = 0) →
    ∀ feature, coefficient feature ≠ 0 →
      ∀ point, point ∈ domain task → featureValue feature point = 0

@[simp] theorem combinedTask_unitWeight
    [Fintype Task] [DecidableEq Task] [Fintype Feature]
    (coefficient : Task → Feature → ℝ)
    (featureValue : Feature → Point → ℝ)
    (selected : Task) (point : Point) :
    combinedTask coefficient featureValue (unitWeight selected) point =
      representedTask coefficient featureValue selected point := by
  simp [combinedTask, unitWeight]

/-- A localized active representation vanishes outside its own domain. -/
theorem representedTask_eq_zero_of_outside
    [Fintype Feature]
    {domain : Task → Set Point}
    {coefficient : Task → Feature → ℝ}
    {featureValue : Feature → Point → ℝ}
    (hLocalized :
      ActiveFeaturesLocalized domain coefficient featureValue)
    {task : Task} {point : Point}
    (hOutside : point ∉ domain task) :
    representedTask coefficient featureValue task point = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro feature _
  by_cases hCoefficient : coefficient task feature = 0
  · simp [hCoefficient]
  · rw [hLocalized hCoefficient hOutside]
    simp

/-- Weighted task arithmetic is exactly the observable statement that each
task effect vanishes on every other task domain. -/
theorem weightedTaskArithmetic_iff_noCrossTaskInterference
    [Fintype Task] [DecidableEq Task] [Fintype Feature]
    {domain : Task → Set Point}
    {coefficient : Task → Feature → ℝ}
    {featureValue : Feature → Point → ℝ} :
    WeightedTaskArithmetic domain coefficient featureValue ↔
      NoCrossTaskInterference domain coefficient featureValue := by
  constructor
  · intro hArithmetic task other hDifferent point hPoint
    have hSelected :=
      hArithmetic (unitWeight task) other point hPoint
    rw [combinedTask_unitWeight] at hSelected
    simpa [unitWeight, hDifferent.symm] using hSelected
  · intro hNoCross weight task point hPoint
    classical
    unfold combinedTask
    apply Finset.sum_eq_single task
    · intro other _ hDifferent
      rw [hNoCross hDifferent hPoint]
      simp
    · simp

/-- Relative localization is already sufficient for zero cross-task
interference. -/
theorem relativelyLocalized_noCrossTaskInterference
    [Fintype Feature]
    {domain : Task → Set Point}
    {coefficient : Task → Feature → ℝ}
    {featureValue : Feature → Point → ℝ}
    (hLocalized :
      ActiveFeaturesRelativelyLocalized domain coefficient featureValue) :
    NoCrossTaskInterference domain coefficient featureValue := by
  intro task other hDifferent point hPoint
  classical
  apply Finset.sum_eq_zero
  intro feature _
  by_cases hCoefficient : coefficient task feature = 0
  · simp [hCoefficient]
  · rw [hLocalized hCoefficient hDifferent hPoint]
    simp

/-- Proposition 2's finite algebraic core, strengthened from an all-ones sum
to every vector of task weights. -/
theorem localizedActiveFeatures_weightedTaskArithmetic
    [Fintype Task] [DecidableEq Task] [Fintype Feature]
    {domain : Task → Set Point}
    {coefficient : Task → Feature → ℝ}
    {featureValue : Feature → Point → ℝ}
    (hDisjoint : PairwiseDisjointTaskDomains domain)
    (hLocalized :
      ActiveFeaturesLocalized domain coefficient featureValue) :
    WeightedTaskArithmetic domain coefficient featureValue := by
  rw [weightedTaskArithmetic_iff_noCrossTaskInterference]
  intro task other hDifferent point hPoint
  apply representedTask_eq_zero_of_outside hLocalized
  exact hDisjoint hDifferent.symm hPoint

/-- Absolute localization and relative localization agree when the pairwise
disjoint task domains cover the entire point type. -/
theorem activeFeaturesLocalized_iff_relativelyLocalized
    {domain : Task → Set Point}
    {coefficient : Task → Feature → ℝ}
    {featureValue : Feature → Point → ℝ}
    (hDisjoint : PairwiseDisjointTaskDomains domain)
    (hCover : TaskDomainsCover domain) :
    ActiveFeaturesLocalized domain coefficient featureValue ↔
      ActiveFeaturesRelativelyLocalized domain coefficient featureValue := by
  constructor
  · intro hLocalized task feature hCoefficient other hDifferent point hPoint
    exact hLocalized hCoefficient (hDisjoint hDifferent.symm hPoint)
  · intro hLocalized task feature hCoefficient point hOutside
    obtain ⟨other, hPoint⟩ := hCover point
    have hDifferent : task ≠ other := by
      intro hEqual
      subst other
      exact hOutside hPoint
    exact hLocalized hCoefficient hDifferent hPoint

/-- Ordinary linear independence after deleting zero restrictions implies
the coefficient-separation formulation used by the converse theorem. -/
theorem locallyIndependentOrZero_localCoefficientSeparation
    [Fintype Feature]
    {domain : Task → Set Point}
    {featureValue : Feature → Point → ℝ}
    (hIndependent : LocallyIndependentOrZero domain featureValue) :
    LocalCoefficientSeparation domain featureValue := by
  classical
  intro task coefficient hCombination feature hCoefficient point hPoint
  by_contra hFeature
  have hFeatureNonzero :
      feature ∈ { candidate |
        ∃ sample, sample ∈ domain task ∧
          featureValue candidate sample ≠ 0 } :=
    ⟨point, hPoint, hFeature⟩
  have hLinearCombination :
      ∑ candidate : NonzeroFeatureOn domain featureValue task,
          coefficient candidate.1 •
            restrictedFeature domain featureValue task candidate = 0 := by
    funext sample
    simp only [Pi.zero_apply, Finset.sum_apply]
    let summand : Feature → ℝ :=
      fun candidate =>
        coefficient candidate * featureValue candidate sample.1
    have hComplement :
        (∑ candidate : { candidate // ¬
            ∃ witness, witness ∈ domain task ∧
              featureValue candidate witness ≠ 0 },
          summand candidate.1) = 0 := by
      apply Finset.sum_eq_zero
      intro candidate _
      have hZero : featureValue candidate.1 sample.1 = 0 := by
        by_contra hNonzero
        exact candidate.2 ⟨sample.1, sample.2, hNonzero⟩
      simp [summand, hZero]
    have hPartition :=
      Fintype.sum_subtype_add_sum_subtype
        (fun candidate =>
          ∃ witness, witness ∈ domain task ∧
            featureValue candidate witness ≠ 0)
        summand
    have hFull : (∑ candidate, summand candidate) = 0 := by
      simpa [summand] using hCombination sample.1 sample.2
    rw [hComplement, add_zero, hFull] at hPartition
    simpa [NonzeroFeatureOn, restrictedFeature, summand] using hPartition
  have hZeroCoefficient :=
    (Fintype.linearIndependent_iff.mp (hIndependent task))
      (fun candidate => coefficient candidate.1)
      hLinearCombination
      ⟨feature, hFeatureNonzero⟩
  exact hCoefficient hZeroCoefficient

/-- Under local coefficient separation, weighted task arithmetic forces every
active feature to vanish on every other declared domain. -/
theorem weightedTaskArithmetic_relativeLocalization
    [Fintype Task] [DecidableEq Task] [Fintype Feature]
    {domain : Task → Set Point}
    {coefficient : Task → Feature → ℝ}
    {featureValue : Feature → Point → ℝ}
    (hSeparated : LocalCoefficientSeparation domain featureValue)
    (hArithmetic :
      WeightedTaskArithmetic domain coefficient featureValue) :
    ActiveFeaturesRelativelyLocalized domain coefficient featureValue := by
  rw [weightedTaskArithmetic_iff_noCrossTaskInterference] at hArithmetic
  intro task feature hCoefficient other hDifferent point hPoint
  apply hSeparated other (coefficient task)
  · intro sample hSample
    exact hArithmetic hDifferent hSample
  · exact hCoefficient
  · exact hPoint

/-- With local coefficient separation, relative feature localization is
equivalent to exact weighted task arithmetic. -/
theorem weightedTaskArithmetic_iff_relativeLocalization
    [Fintype Task] [DecidableEq Task] [Fintype Feature]
    {domain : Task → Set Point}
    {coefficient : Task → Feature → ℝ}
    {featureValue : Feature → Point → ℝ}
    (hSeparated : LocalCoefficientSeparation domain featureValue) :
    WeightedTaskArithmetic domain coefficient featureValue ↔
      ActiveFeaturesRelativelyLocalized domain coefficient featureValue := by
  constructor
  · exact weightedTaskArithmetic_relativeLocalization hSeparated
  · intro hLocalized
    rw [weightedTaskArithmetic_iff_noCrossTaskInterference]
    exact relativelyLocalized_noCrossTaskInterference hLocalized

/-- Finite scalar counterpart of Proposition 3.  On a disjoint domain cover,
local linear independence of the nonzero restrictions makes active-feature
localization necessary and sufficient for exact task arithmetic. -/
theorem weightedTaskArithmetic_iff_activeFeaturesLocalized
    [Fintype Task] [DecidableEq Task] [Fintype Feature]
    {domain : Task → Set Point}
    {coefficient : Task → Feature → ℝ}
    {featureValue : Feature → Point → ℝ}
    (hDisjoint : PairwiseDisjointTaskDomains domain)
    (hCover : TaskDomainsCover domain)
    (hIndependent : LocallyIndependentOrZero domain featureValue) :
    WeightedTaskArithmetic domain coefficient featureValue ↔
      ActiveFeaturesLocalized domain coefficient featureValue := by
  rw [weightedTaskArithmetic_iff_relativeLocalization
    (locallyIndependentOrZero_localCoefficientSeparation hIndependent)]
  exact (activeFeaturesLocalized_iff_relativelyLocalized
    hDisjoint hCover).symm

/-! ## Executable positive and negative fixtures -/

def twoPointDomain (task : Bool) : Set Bool :=
  { point | point = task }

def coordinateFeature (feature point : Bool) : ℝ :=
  if point = feature then 1 else 0

def coordinateCoefficient (task feature : Bool) : ℝ :=
  if feature = task then (if task then 3 else 2) else 0

theorem twoPointDomains_disjoint :
    PairwiseDisjointTaskDomains twoPointDomain := by
  intro first second hDifferent point hFirst hSecond
  simp only [twoPointDomain, Set.mem_setOf_eq] at hFirst hSecond
  exact hDifferent (hFirst.symm.trans hSecond)

theorem twoPointDomains_cover :
    TaskDomainsCover twoPointDomain := by
  intro point
  exact ⟨point, rfl⟩

theorem coordinateFeatures_localized :
    ActiveFeaturesLocalized
      twoPointDomain coordinateCoefficient coordinateFeature := by
  intro task feature hCoefficient point hOutside
  cases task <;> cases feature <;> cases point <;>
    simp [coordinateCoefficient, coordinateFeature, twoPointDomain] at *

theorem coordinateFeatures_locallyIndependentOrZero :
    LocallyIndependentOrZero twoPointDomain coordinateFeature := by
  intro task
  classical
  letI : Subsingleton
      (NonzeroFeatureOn twoPointDomain coordinateFeature task) := by
    constructor
    intro first second
    apply Subtype.ext
    rcases first with ⟨first, hFirst⟩
    rcases second with ⟨second, hSecond⟩
    cases task <;> cases first <;> cases second <;>
      simp [twoPointDomain, coordinateFeature] at hFirst hSecond ⊢
  rw [linearIndependent_subsingleton_index_iff]
  intro feature hZero
  have hAtOwn :=
    congrFun hZero
      (⟨task, rfl⟩ : { point // point ∈ twoPointDomain task })
  rcases feature with ⟨feature, hFeature⟩
  cases task <;> cases feature <;>
    simp [restrictedFeature, coordinateFeature, twoPointDomain] at hFeature hAtOwn

/-- Positive fixture: the two independent coordinate tasks compose exactly
for every pair of mixing weights. -/
theorem coordinateFeatures_weightedTaskArithmetic :
    WeightedTaskArithmetic
      twoPointDomain coordinateCoefficient coordinateFeature :=
  localizedActiveFeatures_weightedTaskArithmetic
    twoPointDomains_disjoint coordinateFeatures_localized

/-- The positive fixture also exercises the Proposition 3 equivalence, rather
than only its sufficient direction. -/
theorem coordinateFeatures_localization_iff_taskArithmetic :
    WeightedTaskArithmetic
        twoPointDomain coordinateCoefficient coordinateFeature ↔
      ActiveFeaturesLocalized
        twoPointDomain coordinateCoefficient coordinateFeature :=
  weightedTaskArithmetic_iff_activeFeaturesLocalized
    twoPointDomains_disjoint twoPointDomains_cover
      coordinateFeatures_locallyIndependentOrZero

/-- Two features that are individually nonlocalized but cancel on the other
domain. -/
def cancellingFeature (feature point : Bool) : ℝ :=
  if feature then (if point then 1 else 0) else 1

def cancellingCoefficient (task feature : Bool) : ℝ :=
  if task then 0 else if feature then -1 else 1

theorem cancellingRepresentation_noCrossTaskInterference :
    NoCrossTaskInterference
      twoPointDomain cancellingCoefficient cancellingFeature := by
  intro task other hDifferent point hPoint
  cases task <;> cases other <;> cases point <;>
    simp [representedTask, cancellingCoefficient, cancellingFeature,
      twoPointDomain] at *

/-- Cancellation preserves task arithmetic even though active features are
not localized.  This is the source's boundary when local independence is
absent. -/
theorem cancellingRepresentation_taskArithmetic_not_localized :
    WeightedTaskArithmetic
        twoPointDomain cancellingCoefficient cancellingFeature ∧
      ¬ ActiveFeaturesLocalized
        twoPointDomain cancellingCoefficient cancellingFeature := by
  constructor
  · rw [weightedTaskArithmetic_iff_noCrossTaskInterference]
    exact cancellingRepresentation_noCrossTaskInterference
  · intro hLocalized
    have hContradiction :=
      hLocalized (task := false) (feature := false)
        (by norm_num [cancellingCoefficient])
        (point := true)
        (by simp [twoPointDomain])
    norm_num [cancellingFeature] at hContradiction

/-- The cancellation fixture violates the load-bearing local coefficient
separation hypothesis. -/
theorem cancellingFeatures_not_locallySeparated :
    ¬ LocalCoefficientSeparation twoPointDomain cancellingFeature := by
  intro hSeparated
  have hCombination :
      ∀ point, point ∈ twoPointDomain true →
        ∑ feature, cancellingCoefficient false feature *
          cancellingFeature feature point = 0 := by
    intro point hPoint
    cases point <;>
      simp [twoPointDomain, cancellingCoefficient, cancellingFeature] at *
  have hContradiction :=
    hSeparated true (cancellingCoefficient false) hCombination false
      (by norm_num [cancellingCoefficient]) true
      (by simp [twoPointDomain])
  norm_num [cancellingFeature] at hContradiction

/-- Removing the cancelling coefficient exposes a concrete cross-task
interference failure. -/
def interferingCoefficient (task feature : Bool) : ℝ :=
  if task then 0 else if feature then 0 else 1

theorem nonlocalized_without_cancellation_fails_taskArithmetic :
    ¬ WeightedTaskArithmetic
      twoPointDomain interferingCoefficient cancellingFeature := by
  intro hArithmetic
  have hAtOther :=
    hArithmetic (unitWeight false) true true
      (by simp [twoPointDomain])
  norm_num [combinedTask, representedTask, unitWeight,
    interferingCoefficient, cancellingFeature] at hAtOther

#print axioms combinedTask_unitWeight
#print axioms representedTask_eq_zero_of_outside
#print axioms weightedTaskArithmetic_iff_noCrossTaskInterference
#print axioms relativelyLocalized_noCrossTaskInterference
#print axioms localizedActiveFeatures_weightedTaskArithmetic
#print axioms activeFeaturesLocalized_iff_relativelyLocalized
#print axioms locallyIndependentOrZero_localCoefficientSeparation
#print axioms weightedTaskArithmetic_relativeLocalization
#print axioms weightedTaskArithmetic_iff_relativeLocalization
#print axioms weightedTaskArithmetic_iff_activeFeaturesLocalized
#print axioms coordinateFeatures_locallyIndependentOrZero
#print axioms coordinateFeatures_weightedTaskArithmetic
#print axioms coordinateFeatures_localization_iff_taskArithmetic
#print axioms cancellingRepresentation_taskArithmetic_not_localized
#print axioms cancellingFeatures_not_locallySeparated
#print axioms nonlocalized_without_cancellation_fails_taskArithmetic

end

end LocalizedTaskArithmetic

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
