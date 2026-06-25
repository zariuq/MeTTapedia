import Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
import Mettapedia.Algebra.QuantaleWeakness

/-!
# Distinctions as a Source of Credal Width

This module connects the finite distinction/partition layer with the PLN
credal-envelope layer.  The bridge is deliberately small: an observation
setoid says which states the observer has not distinguished, and the induced
credal set contains all probability distributions supported on the observed
equivalence class.

The Bool canary proves the intended reading.  If `false` and `true` are not
distinguished, the truth-indicator gamble has strict credal width.  If the
observation distinguishes them and the observed state is `true`, the same
gamble collapses to a point.
-/

namespace Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge

open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
open Mettapedia.Algebra.QuantaleWeakness

variable {Ω : Type*} [Fintype Ω]

/-! ## Distinction gambles on pair-space -/

/-- The unit gamble that asks whether an ordered pair crosses a setoid
distinction.  This is the pair-space observable for the generic bridge: a
credal set over `Ω × Ω` can have width on the distinction event even when a
single displayed truth value hides that structure. -/
noncomputable def setoidDistinctionGamble
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (r : Setoid Ω) [DecidableRel r.r] :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble (Ω × Ω) :=
  fun p => if p ∈ setoidDistinctionSet r then (1 : ℝ) else 0

/-- The pair-space distinction observable is unit-valued. -/
theorem setoidDistinctionGamble_in_unit
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (r : Setoid Ω) [DecidableRel r.r] :
    ∀ p, setoidDistinctionGamble r p ∈ Set.Icc (0 : ℝ) 1 := by
  intro p
  unfold setoidDistinctionGamble
  split <;> norm_num

/-- Generic guardrail: when a credal set over pair-space is nonempty and the
distinction-observable image is bounded, the resulting distinction width is a
genuine unit interval coordinate.  Substantive applications must still prove
non-determination or endpoint witnesses for the chosen credal set. -/
theorem setoidDistinctionEnvelopeWidth_in_unit
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (r : Setoid Ω) [DecidableRel r.r]
    (C : CredalPrevisionSet (Ω × Ω)) (hC : C.Nonempty)
    (hBddBelow :
      BddBelow ((fun P : PrecisePrevision (Ω × Ω) =>
        P (setoidDistinctionGamble r)) '' C))
    (hBddAbove :
      BddAbove ((fun P : PrecisePrevision (Ω × Ω) =>
        P (setoidDistinctionGamble r)) '' C)) :
    credalEnvelopeWidth C (setoidDistinctionGamble r) ∈ Set.Icc (0 : ℝ) 1 :=
  credalEnvelopeWidth_in_unit_of_unit C (setoidDistinctionGamble r)
    hC hBddBelow hBddAbove (setoidDistinctionGamble_in_unit r)

theorem setoidDistinctionEnvelopeWidth_pos_of_not_determines
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (r : Setoid Ω) [DecidableRel r.r]
    (C : CredalPrevisionSet (Ω × Ω))
    (hBddBelow :
      BddBelow ((fun P : PrecisePrevision (Ω × Ω) =>
        P (setoidDistinctionGamble r)) '' C))
    (hBddAbove :
      BddAbove ((fun P : PrecisePrevision (Ω × Ω) =>
        P (setoidDistinctionGamble r)) '' C))
    (hNotDet : ¬ credalSetDetermines C (setoidDistinctionGamble r)) :
    0 < credalEnvelopeWidth C (setoidDistinctionGamble r) :=
  credalEnvelopeWidth_pos_of_strictWidth C (setoidDistinctionGamble r)
    hBddBelow hBddAbove
    ((credalSetHasStrictWidth_iff_not_determines C
      (setoidDistinctionGamble r)).2 hNotDet)

theorem setoidDistinctionEnvelopeWidth_eq_zero_of_determines
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (r : Setoid Ω) [DecidableRel r.r]
    (C : CredalPrevisionSet (Ω × Ω)) (hC : C.Nonempty)
    (hBddBelow :
      BddBelow ((fun P : PrecisePrevision (Ω × Ω) =>
        P (setoidDistinctionGamble r)) '' C))
    (hBddAbove :
      BddAbove ((fun P : PrecisePrevision (Ω × Ω) =>
        P (setoidDistinctionGamble r)) '' C))
    {P : PrecisePrevision (Ω × Ω)} (hP : P ∈ C)
    (hDet : credalSetDetermines C (setoidDistinctionGamble r)) :
    credalEnvelopeWidth C (setoidDistinctionGamble r) = 0 :=
  credalEnvelopeWidth_eq_zero_of_credalSetDetermines C
    (setoidDistinctionGamble r) hC hBddBelow hBddAbove hP hDet

/-! ## Observation setoids induce credal sets -/

/-- The credal set induced by observing only the `r`-equivalence class of
`ω₀`: every compatible distribution must put zero mass outside that class, but
may distribute mass arbitrarily inside it. -/
def observationCredalSet (r : Setoid Ω) (ω₀ : Ω) : CredalSetFinite Ω :=
  fun P => ∀ ω, ¬ r.r ω ω₀ → P.prob ω = 0

/-- A probability distribution supported at the observed state is always
compatible with the observation setoid. -/
theorem pointMass_mem_observationCredalSet
    (r : Setoid Ω) (ω₀ : Ω) (P : ProbDist Ω)
    (hP : ∀ ω, ω ≠ ω₀ → P.prob ω = 0) :
    P ∈ observationCredalSet r ω₀ := by
  intro ω hNotRel
  exact hP ω (fun hEq => hNotRel (hEq ▸ r.refl' ω₀))

section GenericObservationBridge

variable [DecidableEq Ω]

/-- The singleton query for a state, reusing the finite-weight atomic indicator
already defined in the credal library. -/
abbrev indicatorGamble (ω₀ : Ω) : Gamble Ω :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble
    (Ω := Ω) ω₀

/-- The Dirac distribution concentrated at one finite state. -/
noncomputable def pointMassDist (ω₀ : Ω) : ProbDist Ω where
  prob ω := if ω = ω₀ then 1 else 0
  non_neg := by
    intro ω
    by_cases h : ω = ω₀ <;> simp [h]
  sum_one := by
    classical
    simp

@[simp] theorem pointMassDist_prob_self (ω₀ : Ω) :
    (pointMassDist ω₀).prob ω₀ = 1 := by
  simp [pointMassDist]

@[simp] theorem pointMassDist_prob_of_ne {ω₀ ω : Ω} (h : ω ≠ ω₀) :
    (pointMassDist ω₀).prob ω = 0 := by
  simp [pointMassDist, h]

/-- The state-concentrated distribution is always compatible with observing its
own equivalence class. -/
theorem pointMassDist_mem_observationCredalSet_self
    (r : Setoid Ω) (ω₀ : Ω) :
    pointMassDist ω₀ ∈ observationCredalSet r ω₀ := by
  apply pointMass_mem_observationCredalSet r ω₀ (pointMassDist ω₀)
  intro ω hω
  simp [pointMassDist, hω]

/-- Any state related to the observation anchor yields a compatible point mass:
the observation only fixes the equivalence class, not the exact state within
it. -/
theorem pointMassDist_mem_observationCredalSet_of_related
    (r : Setoid Ω) {ω₀ ω₁ : Ω} (hRel : r.r ω₁ ω₀) :
    pointMassDist ω₁ ∈ observationCredalSet r ω₀ := by
  intro ω hNotRel
  by_cases hω : ω = ω₁
  · subst hω
    exact False.elim (hNotRel hRel)
  · simp [pointMassDist, hω]

omit [Fintype Ω] in
@[simp] theorem indicatorGamble_in_unit (ω₀ ω : Ω) :
    indicatorGamble ω₀ ω ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : ω = ω₀
  · simp [indicatorGamble,
      Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble, h]
  · simp [indicatorGamble,
      Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble, h]

@[simp] theorem expectedValue_pointMassDist_indicatorGamble_self (ω₀ : Ω) :
    expectedValue (pointMassDist ω₀) (indicatorGamble ω₀) = 1 := by
  classical
  simp [expectedValue, pointMassDist, indicatorGamble,
    Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble]

@[simp] theorem expectedValue_pointMassDist_indicatorGamble_of_ne
    {ω₀ ω₁ : Ω} (h : ω₁ ≠ ω₀) :
    expectedValue (pointMassDist ω₁) (indicatorGamble ω₀) = 0 := by
  classical
  have h' : ω₀ ≠ ω₁ := Ne.symm h
  simp [expectedValue, pointMassDist, indicatorGamble,
    Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble, h']

/-- If the observation class around `ω₀` contains a genuinely distinct state
`ω₁`, then the singleton query for `ω₀` has genuine credal width: compatible
point masses disagree on it. -/
theorem observationCredalSet_indicatorGamble_has_strict_width_of_related_ne
    (r : Setoid Ω) {ω₀ ω₁ : Ω}
    (hRel : r.r ω₁ ω₀) (hNe : ω₁ ≠ ω₀) :
    lowerProb (observationCredalSet r ω₀) (indicatorGamble ω₀) <
      upperProb (observationCredalSet r ω₀) (indicatorGamble ω₀) := by
  refine interval_from_disagreement
    (pointMassDist ω₁) (pointMassDist ω₀) (indicatorGamble ω₀) ?_
    (observationCredalSet r ω₀)
    (pointMassDist_mem_observationCredalSet_of_related r hRel)
    (pointMassDist_mem_observationCredalSet_self r ω₀) ?_ ?_
  · simp [hNe]
  · refine ⟨0, ?_⟩
    rintro x ⟨P, _hP, rfl⟩
    exact expectedValue_nonneg_of_nonnegative P (indicatorGamble ω₀)
      (fun ω => (indicatorGamble_in_unit ω₀ ω).1)
  · refine ⟨1, ?_⟩
    rintro x ⟨P, _hP, rfl⟩
    exact expectedValue_le_one_of_le_one P (indicatorGamble ω₀)
      (fun ω => (indicatorGamble_in_unit ω₀ ω).2)

/-- If observing the `r`-class of `ω₀` already pins down a singleton class,
the singleton query for `ω₀` collapses to a point value. -/
theorem observationCredalSet_indicatorGamble_forces_expectedValue_one
    (r : Setoid Ω) (ω₀ : Ω)
    (hClass : ∀ ω, r.r ω ω₀ → ω = ω₀)
    (P : ProbDist Ω)
    (hP : P ∈ observationCredalSet r ω₀) :
    expectedValue P (indicatorGamble ω₀) = 1 := by
  have hOutsideZero : ∀ ω, ω ≠ ω₀ → P.prob ω = 0 := by
    intro ω hNe
    apply hP ω
    intro hRel
    exact hNe (hClass ω hRel)
  have hmass : P.prob ω₀ = 1 := by
    have hsum' : ∑ ω : Ω, P.prob ω = P.prob ω₀ := by
      simpa using
        (Finset.sum_eq_single (s := (Finset.univ : Finset Ω)) (f := fun ω => P.prob ω) ω₀
          (fun b _ hb => hOutsideZero b hb)
          (fun hω₀ => (hω₀ (Finset.mem_univ ω₀)).elim))
    linarith [P.sum_one, hsum']
  classical
  simpa [expectedValue, indicatorGamble,
    Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble] using hmass

/-- A singleton observation class yields a collapsed lower/upper envelope on
the corresponding singleton query. -/
theorem observationCredalSet_indicatorGamble_collapses_of_class_subsingleton
    (r : Setoid Ω) (ω₀ : Ω)
    (hClass : ∀ ω, r.r ω ω₀ → ω = ω₀) :
    lowerProb (observationCredalSet r ω₀) (indicatorGamble ω₀) =
      upperProb (observationCredalSet r ω₀) (indicatorGamble ω₀) := by
  have hImage :
      Set.image (fun P => expectedValue P (indicatorGamble ω₀))
          (observationCredalSet r ω₀) =
        ({1} : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨P, hP, rfl⟩
      simp [observationCredalSet_indicatorGamble_forces_expectedValue_one r ω₀ hClass P hP]
    · intro hx
      have hx1 : x = 1 := by simpa using hx
      subst x
      exact ⟨pointMassDist ω₀, pointMassDist_mem_observationCredalSet_self r ω₀, by simp⟩
  unfold lowerProb upperProb
  rw [hImage]
  simp

end GenericObservationBridge

/-! ## Bool canary: coarse vs sharp distinctions -/

abbrev boolCoarseObservation : Setoid Bool := indiscreteSetoid' Bool

abbrev boolSharpObservation : Setoid Bool := discreteSetoid' Bool

/-- The Bool distribution assigning all mass to `false`. -/
def boolFalsePointMass : ProbDist Bool where
  prob b := if b then 0 else 1
  non_neg := by intro b; cases b <;> norm_num
  sum_one := by simp

/-- The Bool distribution assigning all mass to `true`. -/
def boolTruePointMass : ProbDist Bool where
  prob b := if b then 1 else 0
  non_neg := by intro b; cases b <;> norm_num
  sum_one := by simp

/-- The unit gamble asking whether the Bool state is `true`. -/
def boolTruthGamble : Gamble Bool := fun b => if b then 1 else 0

@[simp] theorem boolTruthGamble_in_unit :
    ∀ b, boolTruthGamble b ∈ Set.Icc (0 : ℝ) 1 := by
  intro b
  cases b <;> norm_num [boolTruthGamble]

/-- Coarse observation makes the two Bool states indistinguishable. -/
theorem bool_false_true_not_distinguished_coarse :
    (false, true) ∉ setoidDistinctionSet boolCoarseObservation := by
  simp [setoidDistinctionSet]
  trivial

/-- Sharp observation distinguishes the two Bool states. -/
theorem bool_false_true_distinguished_sharp :
    (false, true) ∈ setoidDistinctionSet boolSharpObservation := by
  simp [setoidDistinctionSet]
  intro h
  cases h

/-- Under the coarse observation, both extreme Bool distributions remain
compatible with observing `true`. -/
theorem bool_extremes_mem_coarseObservation :
    boolFalsePointMass ∈ observationCredalSet boolCoarseObservation true ∧
      boolTruePointMass ∈ observationCredalSet boolCoarseObservation true := by
  constructor <;>
    intro ω hNotRel <;>
    exact False.elim (hNotRel trivial)

@[simp] theorem expectedValue_boolFalse_truth :
    expectedValue boolFalsePointMass boolTruthGamble = 0 := by
  simp [expectedValue, boolFalsePointMass, boolTruthGamble]

@[simp] theorem expectedValue_boolTrue_truth :
    expectedValue boolTruePointMass boolTruthGamble = 1 := by
  simp [expectedValue, boolTruePointMass, boolTruthGamble]

/-- If the observer has not distinguished `false` from `true`, the truth query
has genuine credal width: two compatible distributions disagree on it. -/
theorem coarseObservation_boolTruth_has_strict_width :
    lowerProb (observationCredalSet boolCoarseObservation true) boolTruthGamble <
      upperProb (observationCredalSet boolCoarseObservation true) boolTruthGamble := by
  rcases bool_extremes_mem_coarseObservation with ⟨hFalse, hTrue⟩
  refine interval_from_disagreement
    boolFalsePointMass boolTruePointMass boolTruthGamble ?_ _
    hFalse hTrue ?_ ?_
  · simp
  · refine ⟨0, ?_⟩
    rintro x ⟨P, _hP, rfl⟩
    exact expectedValue_nonneg_of_nonnegative P boolTruthGamble
      (by intro b; cases b <;> norm_num [boolTruthGamble])
  · refine ⟨1, ?_⟩
    rintro x ⟨P, _hP, rfl⟩
    exact expectedValue_le_one_of_le_one P boolTruthGamble
      (by intro b; cases b <;> norm_num [boolTruthGamble])

/-- The `true` point mass is compatible with sharp observation at `true`. -/
theorem boolTruePointMass_mem_sharpTrueObservation :
    boolTruePointMass ∈ observationCredalSet boolSharpObservation true := by
  intro b hNotRel
  cases b
  · simp [boolTruePointMass]
  · exact False.elim (hNotRel (by decide))

/-- Sharp observation at `true` fixes the expectation of the truth-indicator
gamble, even before packaging the compatible distributions as a singleton. -/
theorem sharpTrueObservation_forces_truth_expectedValue
    (P : ProbDist Bool)
    (hP : P ∈ observationCredalSet boolSharpObservation true) :
    expectedValue P boolTruthGamble = 1 := by
  have hfalse : P.prob false = 0 :=
    hP false (by
      intro h
      cases h)
  have hsum := P.sum_one
  simpa [expectedValue, boolTruthGamble, hfalse] using hsum

/-- Once the observation distinguishes the two states and the observed state is
`true`, the truth query collapses to a point-valued credal envelope. -/
theorem sharpTrueObservation_boolTruth_collapses :
    lowerProb (observationCredalSet boolSharpObservation true) boolTruthGamble =
      upperProb (observationCredalSet boolSharpObservation true) boolTruthGamble := by
  have hImage :
      Set.image (fun P => expectedValue P boolTruthGamble)
          (observationCredalSet boolSharpObservation true) =
        ({1} : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨P, hP, rfl⟩
      simp [sharpTrueObservation_forces_truth_expectedValue P hP]
    · intro hx
      have hx1 : x = 1 := by simpa using hx
      subst x
      exact ⟨boolTruePointMass, boolTruePointMass_mem_sharpTrueObservation, by simp⟩
  unfold lowerProb upperProb
  rw [hImage]
  simp

/-- The compact canary for the distinction/credal bridge: unresolved
distinctions produce width, while resolving the relevant distinction collapses
the same query. -/
theorem distinctionResolution_boolTruth_profile :
    (false, true) ∉ setoidDistinctionSet boolCoarseObservation ∧
      lowerProb (observationCredalSet boolCoarseObservation true) boolTruthGamble <
        upperProb (observationCredalSet boolCoarseObservation true) boolTruthGamble ∧
      (false, true) ∈ setoidDistinctionSet boolSharpObservation ∧
      lowerProb (observationCredalSet boolSharpObservation true) boolTruthGamble =
        upperProb (observationCredalSet boolSharpObservation true) boolTruthGamble :=
  ⟨bool_false_true_not_distinguished_coarse,
    coarseObservation_boolTruth_has_strict_width,
    bool_false_true_distinguished_sharp,
    sharpTrueObservation_boolTruth_collapses⟩

end Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge
