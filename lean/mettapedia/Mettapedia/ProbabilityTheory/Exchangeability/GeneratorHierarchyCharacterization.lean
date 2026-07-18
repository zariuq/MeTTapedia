import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiCrossRowFactorization
import Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSuccessorDictionary
import Mettapedia.ProbabilityTheory.HiddenMarkovModels.FiniteHiddenMarkovObservedInference

/-!
# Generator Hierarchy Characterization

Collapse and separation facts for finite-token generator laws.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.Exchangeability

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open Mettapedia.UniversalAI.UniversalPrediction
open Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard
open Mettapedia.ProbabilityTheory.HiddenMarkovModels.FiniteHiddenMarkovModel
open Mettapedia.ProbabilityTheory.HiddenMarkovModels.FiniteHiddenMarkovObservedInference

universe u

variable {k : ℕ}

/-! ## A. Law-level collapse of Markov-mixture towers -/

structure GiryTowerLevel where
  carrier : Type u
  measurableSpace : MeasurableSpace carrier

namespace GiryTowerLevel

def succ (X : GiryTowerLevel.{u}) : GiryTowerLevel.{u} :=
  { carrier := @Measure X.carrier X.measurableSpace
    measurableSpace := by
      letI : MeasurableSpace X.carrier := X.measurableSpace
      infer_instance }

end GiryTowerLevel

def giryTowerLevel (α : Type u) [m : MeasurableSpace α] :
    ℕ → GiryTowerLevel.{u}
  | 0 => ⟨α, m⟩
  | Nat.succ n => GiryTowerLevel.succ (giryTowerLevel α n)

/-- A Giry tower with `n` measure layers over `α`. -/
abbrev GiryTower (α : Type u) [MeasurableSpace α] (n : ℕ) : Type u :=
  (giryTowerLevel α n).carrier

instance instMeasurableSpaceGiryTower
    (α : Type u) [MeasurableSpace α] (n : ℕ) :
    MeasurableSpace (GiryTower α n) :=
  (giryTowerLevel α n).measurableSpace

/-- Collapse an `(n+1)`-level Giry tower to a base measure. -/
def iterJoin (α : Type u) [MeasurableSpace α] :
    (n : ℕ) → GiryTower α (n + 1) → Measure α
  | 0, μ => μ
  | Nat.succ n, P =>
      Measure.join (Measure.map (iterJoin α n)
        (show Measure (GiryTower α (n + 1)) from P))

theorem measurable_iterJoin (α : Type u) [MeasurableSpace α] :
    ∀ n : ℕ, Measurable (iterJoin α n)
  | 0 => by
      change Measurable (fun μ : Measure α => μ)
      exact measurable_id
  | Nat.succ n => by
      change Measurable
        (fun P : Measure (GiryTower α (n + 1)) =>
          Measure.join (Measure.map (iterJoin α n) P))
      exact Measure.measurable_join.comp
        (Measure.measurable_map _ (measurable_iterJoin α n))

/-- Recursive probability predicate for an `(n+1)`-level Giry tower. -/
def IsProbabilityGiryTower (α : Type u) [MeasurableSpace α] :
    (n : ℕ) → GiryTower α (n + 1) → Prop
  | 0, μ => IsProbabilityMeasure μ
  | Nat.succ n, P =>
      IsProbabilityMeasure
          (show Measure (GiryTower α (n + 1)) from P) ∧
        ∀ᵐ τ ∂(show Measure (GiryTower α (n + 1)) from P),
          IsProbabilityGiryTower α n τ

private theorem measurableSet_isProbabilityMeasure
    (α : Type u) [MeasurableSpace α] :
    MeasurableSet {μ : Measure α | IsProbabilityMeasure μ} := by
  suffices {μ : Measure α | IsProbabilityMeasure μ} =
      (fun μ : Measure α => μ Set.univ) ⁻¹' {1} by
    rw [this]
    exact Measure.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)
  ext μ
  exact isProbabilityMeasure_iff

theorem iterJoin_isProbability (α : Type u) [MeasurableSpace α] :
    ∀ (n : ℕ) (P : GiryTower α (n + 1)),
      IsProbabilityGiryTower α n P → IsProbabilityMeasure (iterJoin α n P)
  | 0, μ, hμ => hμ
  | Nat.succ n, P, hP => by
      change IsProbabilityMeasure
          (show Measure (GiryTower α (n + 1)) from P) ∧
        (∀ᵐ τ ∂(show Measure (GiryTower α (n + 1)) from P),
          IsProbabilityGiryTower α n τ) at hP
      let Pμ : Measure (GiryTower α (n + 1)) := P
      rcases hP with ⟨hOuter, hFiber⟩
      let f : GiryTower α (n + 1) → Measure α := iterJoin α n
      have hf_meas : Measurable f := measurable_iterJoin α n
      haveI : IsProbabilityMeasure Pμ := hOuter
      haveI : IsProbabilityMeasure (Measure.map f Pμ) :=
        Measure.isProbabilityMeasure_map hf_meas.aemeasurable
      have hFiberBase_source :
          ∀ᵐ τ ∂Pμ, IsProbabilityMeasure (f τ) :=
        hFiber.mono fun τ hτ =>
          iterJoin_isProbability α n τ hτ
      have hFiberBase :
          ∀ᵐ μ ∂Measure.map f Pμ, IsProbabilityMeasure μ := by
        rw [ae_map_iff hf_meas.aemeasurable
          (measurableSet_isProbabilityMeasure α)]
        exact hFiberBase_source
      simpa [iterJoin, f, Pμ] using MeasureTheory.isProbabilityMeasure_join hFiberBase

/-- The tower-level word law obtained by integrating through every measure layer. -/
def towerWordLaw (xs : List (Fin k)) :
    (n : ℕ) → GiryTower (MarkovParam k) (n + 1) → ℝ≥0∞
  | 0, μ => ∫⁻ θ, wordProb (k := k) θ xs ∂μ
  | Nat.succ n, P => ∫⁻ τ, towerWordLaw xs n τ ∂P

/-- Iterated Giry mixtures of Markov parameters collapse to their single joined
law. This is a law-level statement only: it does not identify computational
descriptions, search costs, or generator syntax. -/
theorem levelTower_collapse
    (xs : List (Fin k)) :
    ∀ (n : ℕ) (P : GiryTower (MarkovParam k) (n + 1)),
      IsProbabilityGiryTower (MarkovParam k) n P →
        towerWordLaw (k := k) xs n P =
          ∫⁻ θ, wordProb (k := k) θ xs
            ∂(iterJoin (MarkovParam k) n P)
  | 0, μ, _ => rfl
  | Nat.succ n, P, hP => by
      dsimp [towerWordLaw, iterJoin]
      have hword :
          AEMeasurable (fun θ : MarkovParam k => wordProb (k := k) θ xs)
            (Measure.join (Measure.map (iterJoin (MarkovParam k) n) P)) :=
        (measurable_wordProb (k := k) xs).aemeasurable
      rw [Measure.lintegral_join hword]
      have hF :
          Measurable
            (fun μ : Measure (MarkovParam k) =>
              ∫⁻ θ, wordProb (k := k) θ xs ∂μ) :=
        Measure.measurable_lintegral (measurable_wordProb (k := k) xs)
      rw [lintegral_map hF (measurable_iterJoin (MarkovParam k) n)]
      refine lintegral_congr_ae ?_
      exact (And.right hP).mono fun τ hτ =>
        levelTower_collapse xs n τ hτ

/-- Mixtures of Markov mixtures are Markov mixtures, with collapse operator
given by Giry join. -/
def markovMixture_join
    {μ : FiniteAlphabet.PrefixMeasure (Fin k)}
    (P : Measure (Measure (MarkovParam k)))
    [IsProbabilityMeasure P]
    (hP : ∀ᵐ ν ∂P, IsProbabilityMeasure ν)
    (hμ :
      ∀ xs : List (Fin k),
        μ xs = ∫⁻ ν, ∫⁻ θ, wordProb (k := k) θ xs ∂ν ∂P) :
    MarkovMixture k μ := by
  refine ⟨P.join, ?_, ?_⟩
  · exact MeasureTheory.isProbabilityMeasure_join hP
  · intro xs
    calc
      μ xs = ∫⁻ ν, ∫⁻ θ, wordProb (k := k) θ xs ∂ν ∂P := hμ xs
      _ = ∫⁻ θ, wordProb (k := k) θ xs ∂P.join := by
        exact (Measure.lintegral_join
          (m := P)
          (f := fun θ : MarkovParam k => wordProb (k := k) θ xs)
          ((measurable_wordProb (k := k) xs).aemeasurable)).symm

private theorem join_add {α : Type*} [MeasurableSpace α]
    (m n : Measure (Measure α)) :
    (m + n).join = m.join + n.join := by
  ext s hs
  simp [Measure.join_apply, hs, lintegral_add_measure]

def twoByTwoMixtureOfMixtures
    (θ₀₀ θ₀₁ θ₁₀ θ₁₁ : MarkovParam 2) :
    Measure (Measure (MarkovParam 2)) :=
  (1 / 2 : ℝ≥0∞) •
      Measure.dirac
        ((1 / 2 : ℝ≥0∞) • Measure.dirac θ₀₀ +
          (1 / 2 : ℝ≥0∞) • Measure.dirac θ₀₁) +
    (1 / 2 : ℝ≥0∞) •
      Measure.dirac
        ((1 / 2 : ℝ≥0∞) • Measure.dirac θ₁₀ +
          (1 / 2 : ℝ≥0∞) • Measure.dirac θ₁₁)

theorem twoByTwoMixtureOfMixtures_join
    (θ₀₀ θ₀₁ θ₁₀ θ₁₁ : MarkovParam 2) :
    (twoByTwoMixtureOfMixtures θ₀₀ θ₀₁ θ₁₀ θ₁₁).join =
      (1 / 4 : ℝ≥0∞) • Measure.dirac θ₀₀ +
        (1 / 4 : ℝ≥0∞) • Measure.dirac θ₀₁ +
        (1 / 4 : ℝ≥0∞) • Measure.dirac θ₁₀ +
        (1 / 4 : ℝ≥0∞) • Measure.dirac θ₁₁ := by
  have hquarter :
      ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) = (4 : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.mul_inv]
    norm_num
    · simp
    · simp
  rw [twoByTwoMixtureOfMixtures, join_add]
  simp [Measure.join_smul, Measure.join_dirac, smul_add, smul_smul,
    one_div, hquarter, add_assoc]

/-- Equal laws need not identify external descriptions of those laws. -/
theorem same_law_distinct_tags
    (ν : Measure (MarkovParam k)) :
    ((ν, false) : Measure (MarkovParam k) × Bool).1 =
        ((ν, true) : Measure (MarkovParam k) × Bool).1 ∧
      ((ν, false) : Measure (MarkovParam k) × Bool) ≠ (ν, true) := by
  constructor
  · rfl
  · intro h
    exact Bool.noConfusion (congrArg Prod.snd h)

/-! ## B. HMM laws strictly exceed first-order Markov mixtures -/

private theorem sum_fin_fun_succ
    {β M : Type*} [Fintype β] [AddCommMonoid M]
    {n : ℕ} (f : (Fin (n + 1) → β) → M) :
    (∑ g : Fin (n + 1) → β, f g) =
      ∑ a : β, ∑ t : Fin n → β, f (Fin.cons a t) := by
  let e : β × (Fin n → β) ≃ (Fin (n + 1) → β) :=
    Fin.consEquiv (fun _ : Fin (n + 1) => β)
  calc
    (∑ g : Fin (n + 1) → β, f g) =
        ∑ p : β × (Fin n → β), f (e p) := by
      exact Fintype.sum_equiv e.symm f
        (fun p : β × (Fin n → β) => f (e p)) (by
          intro g
          exact congrArg f (Equiv.apply_symm_apply e g).symm)
    _ = ∑ a : β, ∑ t : Fin n → β, f (Fin.cons a t) := by
      rw [Fintype.sum_prod_type]
      rfl

private theorem fin2_half_sum :
    (∑ _x : Fin 2, (1 / 2 : ℝ≥0∞)) = 1 := by
  rw [Fin.sum_univ_two]
  simp only [one_div]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by simp)

private def fairPMF2 : PMF (Fin 2) :=
  PMF.ofFintype (fun _ : Fin 2 => (1 / 2 : ℝ≥0∞)) fin2_half_sum

private def fairPM2 : ProbabilityMeasure (Fin 2) :=
  ⟨fairPMF2.toMeasure, by infer_instance⟩

private def diracPM2 (a : Fin 2) : ProbabilityMeasure (Fin 2) :=
  ⟨Measure.dirac a, Measure.dirac.isProbabilityMeasure⟩

@[simp] private theorem fairPM2_toMeasure_singleton (y : Fin 2) :
    ((fairPM2 : Measure (Fin 2)) (Set.singleton y)) =
      (1 / 2 : ℝ≥0∞) := by
  change fairPMF2.toMeasure ({y} : Set (Fin 2)) = (1 / 2 : ℝ≥0∞)
  rw [PMF.toMeasure_apply_singleton fairPMF2 y (measurableSet_singleton y)]
  simp [fairPMF2]

@[simp] private theorem diracPM2_toMeasure_singleton (a y : Fin 2) :
    ((diracPM2 a : Measure (Fin 2)) (Set.singleton y)) =
      if a = y then 1 else 0 := by
  change (Measure.dirac a ({y} : Set (Fin 2))) =
    if a = y then 1 else 0
  rw [Measure.dirac_apply]
  by_cases h : a = y
  · subst h
    rw [Set.indicator_of_mem]
    · simp
    · exact Set.mem_singleton a
  · have hmem : a ∉ ({y} : Set (Fin 2)) := by
      intro hm
      exact h (Set.mem_singleton_iff.mp hm)
    rw [Set.indicator_of_notMem hmem]
    simp [h]

private def alternatingHMM : FiniteHMMParam 2 2 where
  latentParam :=
    { init := diracPM2 0
      trans := fun
        | 0 => diracPM2 1
        | 1 => diracPM2 0 }
  emission := fun
    | 0 => fairPM2
    | 1 => diracPM2 0

private theorem alternatingHMM_forward_A_zero :
    forwardMessage alternatingHMM [0, 0, 1, 0] 0 = 0 := by
  simp only [forwardMessage, List.length_cons, List.length_nil,
    Nat.reduceAdd]
  simp only [sum_fin_fun_succ, Fin.sum_univ_two]
  simp [alternatingHMM, emissionProb, initProb, stepProb,
    observationWeight, wordProb, wordProbNN, wordProbAux]

private theorem alternatingHMM_forward_A_one :
    forwardMessage alternatingHMM [0, 0, 1, 0] 1 =
      (1 / 4 : ℝ≥0∞) := by
  simp only [forwardMessage, List.length_cons, List.length_nil,
    Nat.reduceAdd]
  simp only [sum_fin_fun_succ, Fin.sum_univ_two]
  simp [alternatingHMM, emissionProb, initProb, stepProb,
    observationWeight, wordProb, wordProbNN, wordProbAux, one_div]
  rw [← ENNReal.mul_inv]
  norm_num
  · simp
  · simp

private theorem alternatingHMM_observed_A :
    observedWordProb alternatingHMM [0, 0, 1, 0] =
      (1 / 4 : ℝ≥0∞) := by
  rw [observedWordProb_eq_sum_forwardMessage]
  rw [Fin.sum_univ_two]
  rw [alternatingHMM_forward_A_zero, alternatingHMM_forward_A_one]
  simp

private theorem alternatingHMM_observed_B :
    observedWordProb alternatingHMM [0, 1, 0, 0] = 0 := by
  rw [observedWordProb_eq_sum_forwardMessage]
  rw [Fin.sum_univ_two]
  · simp only [forwardMessage, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    simp only [sum_fin_fun_succ, Fin.sum_univ_two]
    simp [alternatingHMM, emissionProb, initProb, stepProb,
      observationWeight, wordProb, wordProbNN, wordProbAux]

private def hmmWitnessA : List (Fin 2) := [0, 0, 1, 0]
private def hmmWitnessB : List (Fin 2) := [0, 1, 0, 0]

private theorem wordProb_hmmWitness_eq (θ : MarkovParam 2) :
    wordProb (k := 2) θ hmmWitnessA =
      wordProb (k := 2) θ hmmWitnessB := by
  simp [hmmWitnessA, hmmWitnessB, wordProb, wordProbNN, wordProbAux,
    mul_left_comm, mul_comm]

private theorem markovMixture_hmmWitness_eq
    {μ : FiniteAlphabet.PrefixMeasure (Fin 2)}
    (M : MarkovMixture 2 μ) :
    μ hmmWitnessA = μ hmmWitnessB := by
  rw [M.represents hmmWitnessA, M.represents hmmWitnessB]
  exact lintegral_congr_ae (Filter.Eventually.of_forall fun θ =>
    wordProb_hmmWitness_eq θ)

theorem exists_hmm_law_not_markovMixture :
    ∃ θ : FiniteHMMParam 2 2,
      ¬ ∃ μ : FiniteAlphabet.PrefixMeasure (Fin 2),
        ∃ _M : MarkovMixture 2 μ,
          ∀ xs, μ xs = observedWordProb θ xs := by
  refine ⟨alternatingHMM, ?_⟩
  rintro ⟨μ, M, hμ⟩
  have hmix := markovMixture_hmmWitness_eq M
  have hobs : observedWordProb alternatingHMM hmmWitnessA =
      observedWordProb alternatingHMM hmmWitnessB := by
    calc
      observedWordProb alternatingHMM hmmWitnessA =
          μ hmmWitnessA := (hμ hmmWitnessA).symm
      _ = μ hmmWitnessB := hmix
      _ = observedWordProb alternatingHMM hmmWitnessB := hμ hmmWitnessB
  rw [hmmWitnessA, hmmWitnessB, alternatingHMM_observed_A,
    alternatingHMM_observed_B] at hobs
  have hnonzero : (1 / 4 : ℝ≥0∞) ≠ 0 := by
    rw [one_div]
    exact ENNReal.inv_ne_zero.mpr (by simp)
  exact hnonzero hobs

def degenerateCopyHMM (θ : MarkovParam 2) : FiniteHMMParam 2 2 where
  latentParam := θ
  emission := fun x => diracPM2 x

private theorem degenerateCopyHMM_observationWeight
    (θ : MarkovParam 2) :
    ∀ xs ys : List (Fin 2),
      observationWeight (degenerateCopyHMM θ) xs ys =
        if xs = ys then 1 else 0
  | [], [] => by
      simp [observationWeight]
  | [], _y :: _ys => by
      simp [observationWeight]
  | _x :: _xs, [] => by
      simp [observationWeight]
  | x :: xs, y :: ys => by
      by_cases hxy : x = y
      · subst hxy
        simp [observationWeight, degenerateCopyHMM, emissionProb]
        exact degenerateCopyHMM_observationWeight θ xs ys
      · have hlist : x :: xs ≠ y :: ys := by
          intro h
          exact hxy (List.cons.inj h).1
        simp [observationWeight, degenerateCopyHMM, emissionProb, hxy,
          hlist]

theorem degenerateCopyHMM_observedWordProb
    (θ : MarkovParam 2) (xs : List (Fin 2)) :
    observedWordProb (degenerateCopyHMM θ) xs =
      wordProb (k := 2) θ xs := by
  unfold observedWordProb
  rw [Fintype.sum_eq_single (a := xs.get)]
  · rw [List.ofFn_get]
    have hweight :
        observationWeight (degenerateCopyHMM θ) xs xs = 1 := by
      simpa using degenerateCopyHMM_observationWeight θ xs xs
    rw [hweight]
    simp [degenerateCopyHMM]
  · intro f hf
    have hlist : List.ofFn f ≠ xs := by
      intro h
      apply hf
      have h' : List.ofFn f = List.ofFn xs.get := by
        simpa [List.ofFn_get] using h
      exact List.ofFn_injective h'
    have hweight :
        observationWeight (degenerateCopyHMM θ) (List.ofFn f) xs = 0 := by
      simpa [hlist] using
        degenerateCopyHMM_observationWeight θ (List.ofFn f) xs
    rw [hweight]
    simp

end Mettapedia.ProbabilityTheory.Exchangeability
