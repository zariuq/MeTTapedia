import Mettapedia.CategoryTheory.DeFinettiMarkovGiryBridge
import Mettapedia.Logic.FiniteHiddenMarkovModel
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Finite Hidden Markov Models at the de Finetti Boundary

This file packages the finite-state/finitely-emitting HMM surface in the same
spirit as the Borel-side Markov bridge:

* the latent parameter law is a Borel probability measure on `MarkovParam`;
* the emission kernel is kept explicit and fixed;
* the observed finite-word law is obtained by integrating the proved
  `observedWordProb` coordinates.

We deliberately stay at the honest prefix-law level here. A measurable kernel
on the full HMM parameter space is future work.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open MeasureTheory
open Mettapedia.Logic
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.Logic.FiniteHiddenMarkovModel
open scoped BigOperators ENNReal NNReal

variable {latent obs : ℕ}
variable {emission : Fin latent → ProbabilityMeasure (Fin obs)}
variable {μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin obs)}

local instance : MeasurableSpace (MarkovParam latent) := MarkovParam.borelMS (k := latent)
local instance : BorelSpace (MarkovParam latent) := ⟨rfl⟩

/-- Borel measurability of the finite-word HMM observation law as a function of
the latent Markov parameter, with the emission kernel held fixed. -/
theorem measurable_observedWordProb_borel
    (emission : Fin latent → ProbabilityMeasure (Fin obs))
    (ys : List (Fin obs)) :
    Measurable
      (fun θ : MarkovParam latent =>
        observedWordProb (latent := latent) (obs := obs)
          ⟨θ, emission⟩ ys) := by
  classical
  unfold observedWordProb
  refine Finset.measurable_sum Finset.univ ?_
  intro xs _
  have hweight :
      ∀ us : List (Fin latent), ∀ vs : List (Fin obs),
        Measurable
          (fun θ : MarkovParam latent =>
            observationWeight (latent := latent) (obs := obs) ⟨θ, emission⟩ us vs) := by
    intro us
    induction us with
    | nil =>
        intro vs
        cases vs <;> simp [FiniteHiddenMarkovModel.observationWeight]
    | cons u us ih =>
        intro vs
        cases vs with
        | nil =>
            simp [FiniteHiddenMarkovModel.observationWeight]
        | cons v vs =>
            simpa [FiniteHiddenMarkovModel.observationWeight,
              FiniteHiddenMarkovModel.emissionProb] using
              measurable_const.mul (ih vs)
  exact
    (measurable_wordProb_borel (k := latent) (List.ofFn xs)).mul
      (hweight (List.ofFn xs) ys)

/-- Observed-word weight induced by a Borel law on latent Markov parameters and
a fixed emission kernel. -/
def observedWordWeightViaProbMarkov
    (emission : Fin latent → ProbabilityMeasure (Fin obs))
    (π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov latent)
    (ys : List (Fin obs)) : ℝ≥0∞ :=
  ∫⁻ θ : MarkovParam latent,
    observedWordProb (latent := latent) (obs := obs) ⟨θ, emission⟩ ys
      ∂(π : Measure (MarkovParam latent))

/-- Honest Borel-side observed-word factorization for finite HMMs. -/
def CategoricalBorelFiniteHMMFactorization
    (latent obs : ℕ)
    (emission : Fin latent → ProbabilityMeasure (Fin obs))
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin obs)) : Prop :=
  ∃ π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov latent,
    ∀ ys : List (Fin obs),
      μ ys = observedWordWeightViaProbMarkov (latent := latent) (obs := obs) emission π ys

/-- Public Borel-side finite-HMM mixture witness. -/
structure BorelFiniteHMMMixture
    (latent obs : ℕ)
    (emission : Fin latent → ProbabilityMeasure (Fin obs))
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin obs)) where
  mixingLaw : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov latent
  represents :
    ∀ ys : List (Fin obs),
      μ ys = observedWordWeightViaProbMarkov (latent := latent) (obs := obs) emission mixingLaw ys

namespace BorelFiniteHMMMixture

/-- Any public Borel-side finite-HMM mixture witness yields the corresponding
factorization package. -/
theorem categoricalBorelFiniteHMMFactorization_of_borelFiniteHMMMixture
    (M : BorelFiniteHMMMixture latent obs emission μ) :
    CategoricalBorelFiniteHMMFactorization latent obs emission μ :=
  ⟨M.mixingLaw, M.represents⟩

/-- Consumer API: recover a public finite-HMM mixture witness from the
factorization package. -/
noncomputable def ofCategoricalBorelFactorization
    (hfac : CategoricalBorelFiniteHMMFactorization latent obs emission μ) :
    BorelFiniteHMMMixture latent obs emission μ := by
  exact ⟨Classical.choose hfac, Classical.choose_spec hfac⟩

/-- The public finite-HMM mixture witness is equivalent to the Borel observed
word factorization package. -/
theorem categoricalBorelFiniteHMMFactorization_iff_nonempty_borelFiniteHMMMixture :
    CategoricalBorelFiniteHMMFactorization latent obs emission μ ↔
      Nonempty (BorelFiniteHMMMixture latent obs emission μ) := by
  constructor
  · intro hfac
    exact ⟨ofCategoricalBorelFactorization
      (latent := latent) (obs := obs) (emission := emission) (μ := μ) hfac⟩
  · rintro ⟨M⟩
    exact categoricalBorelFiniteHMMFactorization_of_borelFiniteHMMMixture
      (latent := latent) (obs := obs) (emission := emission) (μ := μ) M

end BorelFiniteHMMMixture

/-- A fixed finite HMM is recovered by the Dirac law concentrated at its latent
Markov parameter. -/
theorem observedWordWeightViaProbMarkov_dirac_eq_observedWordProb
    (θ : FiniteHMMParam latent obs) (ys : List (Fin obs)) :
    observedWordWeightViaProbMarkov (latent := latent) (obs := obs)
        θ.emission (MeasureTheory.diracProba θ.latentParam) ys =
      observedWordProb (latent := latent) (obs := obs) θ ys := by
  unfold observedWordWeightViaProbMarkov
  change
    ∫⁻ θ' : MarkovParam latent,
        observedWordProb (latent := latent) (obs := obs) ⟨θ', θ.emission⟩ ys
          ∂(Measure.dirac θ.latentParam) =
      observedWordProb (latent := latent) (obs := obs) θ ys
  rw [lintegral_dirac]

/-- Dirac witness: every fixed finite HMM gives a degenerate Borel factorization
by concentrating the latent Markov law at its own parameter. This is the honest
trivial direction, not a mixture characterization theorem. -/
theorem borelFiniteHMMFactorization_diracWitness
    (θ : FiniteHMMParam latent obs) :
    ∃ π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov latent,
      ∀ ys : List (Fin obs),
        observedSequenceMeasure (latent := latent) (obs := obs) θ
            (MarkovDeFinettiRecurrence.cylinder (k := obs) ys) =
          observedWordWeightViaProbMarkov (latent := latent) (obs := obs) θ.emission π ys := by
  refine ⟨MeasureTheory.diracProba θ.latentParam, ?_⟩
  intro ys
  rw [observedWordWeightViaProbMarkov_dirac_eq_observedWordProb (latent := latent) (obs := obs) θ ys]
  exact observedSequenceMeasure_cylinder_eq_observedWordProb (latent := latent) (obs := obs) θ ys

/-- Legacy alias for the Dirac witness theorem. The stronger finite-HMM mixture
image theorem remains future work. -/
@[deprecated borelFiniteHMMFactorization_diracWitness (since := "2026-04-16")]
theorem exists_borelFiniteHMMFactorization_of_param
    (θ : FiniteHMMParam latent obs) :
    ∃ π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov latent,
      ∀ ys : List (Fin obs),
        observedSequenceMeasure (latent := latent) (obs := obs) θ
            (MarkovDeFinettiRecurrence.cylinder (k := obs) ys) =
          observedWordWeightViaProbMarkov (latent := latent) (obs := obs) θ.emission π ys :=
  borelFiniteHMMFactorization_diracWitness (latent := latent) (obs := obs) θ

section BinaryExamples

local instance : MeasurableSpace (MarkovParam 2) := MarkovParam.borelMS (k := 2)
local instance : BorelSpace (MarkovParam 2) := ⟨rfl⟩

private theorem diracProba_singleton_eval (x y : Fin 2) :
    MeasureTheory.diracProba x (Set.singleton y) = if x = y then 1 else 0 := by
  change
    ((((MeasureTheory.diracProba x : ProbabilityMeasure (Fin 2)) : Measure (Fin 2))
      (Set.singleton y)).toNNReal = if x = y then 1 else 0)
  rw [MeasureTheory.diracProba_toMeasure_apply]
  by_cases h : x = y
  · subst h
    rw [Set.indicator_of_mem (by exact Set.mem_singleton _)]
    simp
  · rw [Set.indicator_of_notMem]
    · simp [h]
    · exact fun hx => h hx

/-- Simple binary latent chain that starts at `0` and always stays at `0`. -/
noncomputable def binaryAbsorbingZeroLatent : MarkovParam 2 where
  init := MeasureTheory.diracProba (0 : Fin 2)
  trans _ := MeasureTheory.diracProba (0 : Fin 2)

/-- Deterministic copy-style emission kernel on the binary alphabet. -/
noncomputable def binaryCopyEmission : Fin 2 → ProbabilityMeasure (Fin 2)
  | 0 => MeasureTheory.diracProba (0 : Fin 2)
  | 1 => MeasureTheory.diracProba (1 : Fin 2)

/-- Concrete binary finite HMM whose observation process is the constant-zero
sequence. -/
noncomputable def binaryCopyHMM : FiniteHMMParam 2 2 where
  latentParam := binaryAbsorbingZeroLatent
  emission := binaryCopyEmission

@[simp] theorem binaryAbsorbingZeroLatent_initProb_zero :
    initProb (k := 2) binaryAbsorbingZeroLatent 0 = 1 := by
  simpa [binaryAbsorbingZeroLatent, initProb] using diracProba_singleton_eval 0 0

@[simp] theorem binaryAbsorbingZeroLatent_initProb_one :
    initProb (k := 2) binaryAbsorbingZeroLatent 1 = 0 := by
  simpa [binaryAbsorbingZeroLatent, initProb] using diracProba_singleton_eval 0 1

@[simp] theorem binaryAbsorbingZeroLatent_stepProb_zero_zero :
    stepProb (k := 2) binaryAbsorbingZeroLatent 0 0 = 1 := by
  simpa [binaryAbsorbingZeroLatent, stepProb] using diracProba_singleton_eval 0 0

@[simp] theorem binaryAbsorbingZeroLatent_stepProb_zero_one :
    stepProb (k := 2) binaryAbsorbingZeroLatent 0 1 = 0 := by
  simpa [binaryAbsorbingZeroLatent, stepProb] using diracProba_singleton_eval 0 1

@[simp] theorem binaryAbsorbingZeroLatent_stepProb_one_zero :
    stepProb (k := 2) binaryAbsorbingZeroLatent 1 0 = 1 := by
  simpa [binaryAbsorbingZeroLatent, stepProb] using diracProba_singleton_eval 0 0

@[simp] theorem binaryAbsorbingZeroLatent_stepProb_one_one :
    stepProb (k := 2) binaryAbsorbingZeroLatent 1 1 = 0 := by
  simpa [binaryAbsorbingZeroLatent, stepProb] using diracProba_singleton_eval 0 1

@[simp] theorem binaryCopyEmissionProb_zero_zero :
    emissionProb (latent := 2) (obs := 2) binaryCopyHMM 0 0 = 1 := by
  simpa [binaryCopyHMM, binaryCopyEmission, emissionProb] using diracProba_singleton_eval 0 0

@[simp] theorem binaryCopyEmissionProb_zero_one :
    emissionProb (latent := 2) (obs := 2) binaryCopyHMM 0 1 = 0 := by
  simpa [binaryCopyHMM, binaryCopyEmission, emissionProb] using diracProba_singleton_eval 0 1

@[simp] theorem binaryCopyEmissionProb_one_zero :
    emissionProb (latent := 2) (obs := 2) binaryCopyHMM 1 0 = 0 := by
  simpa [binaryCopyHMM, binaryCopyEmission, emissionProb] using diracProba_singleton_eval 1 0

@[simp] theorem binaryCopyEmissionProb_one_one :
    emissionProb (latent := 2) (obs := 2) binaryCopyHMM 1 1 = 1 := by
  simpa [binaryCopyHMM, binaryCopyEmission, emissionProb] using diracProba_singleton_eval 1 1

@[simp] theorem binaryAbsorbingZeroLatent_wordProb_singleton_zero :
    wordProb (k := 2) binaryAbsorbingZeroLatent ([0] : List (Fin 2)) = 1 := by
  simp [MarkovDeFinettiHard.wordProb, MarkovDeFinettiHard.wordProbNN,
    MarkovDeFinettiHard.wordProbAux]

@[simp] theorem binaryAbsorbingZeroLatent_wordProb_singleton_one :
    wordProb (k := 2) binaryAbsorbingZeroLatent ([1] : List (Fin 2)) = 0 := by
  simp [MarkovDeFinettiHard.wordProb, MarkovDeFinettiHard.wordProbNN,
    MarkovDeFinettiHard.wordProbAux]

@[simp] theorem binaryCopyHMM_observationWeight_singleton_00 :
    observationWeight (latent := 2) (obs := 2) binaryCopyHMM
      ([0] : List (Fin 2)) ([0] : List (Fin 2)) = 1 := by
  simp [FiniteHiddenMarkovModel.observationWeight]

@[simp] theorem binaryCopyHMM_observationWeight_singleton_10 :
    observationWeight (latent := 2) (obs := 2) binaryCopyHMM
      ([1] : List (Fin 2)) ([0] : List (Fin 2)) = 0 := by
  simp [FiniteHiddenMarkovModel.observationWeight]

@[simp] theorem binaryCopyHMM_observationWeight_singleton_01 :
    observationWeight (latent := 2) (obs := 2) binaryCopyHMM
      ([0] : List (Fin 2)) ([1] : List (Fin 2)) = 0 := by
  simp [FiniteHiddenMarkovModel.observationWeight]

@[simp] theorem binaryCopyHMM_observationWeight_singleton_11 :
    observationWeight (latent := 2) (obs := 2) binaryCopyHMM
      ([1] : List (Fin 2)) ([1] : List (Fin 2)) = 1 := by
  simp [FiniteHiddenMarkovModel.observationWeight]

/-- Concrete regression example: the binary copy HMM assigns probability `1` to
the observed word `[0]`. -/
theorem binaryCopyHMM_observedCylinder_0 :
    observedSequenceMeasure (latent := 2) (obs := 2) binaryCopyHMM
        (MarkovDeFinettiRecurrence.cylinder (k := 2) ([0] : List (Fin 2))) = 1 := by
  classical
  rw [observedSequenceMeasure_cylinder_eq_observedWordProb (latent := 2) (obs := 2) binaryCopyHMM]
  let F : (Fin 1 → Fin 2) → ℝ≥0∞ := fun x =>
    wordProb (k := 2) binaryAbsorbingZeroLatent (List.ofFn x) *
      observationWeight (latent := 2) (obs := 2) binaryCopyHMM (List.ofFn x)
        ([0] : List (Fin 2))
  change ∑ x : Fin 1 → Fin 2, F x = 1
  let e : (Fin 1 → Fin 2) ≃ Fin 2 := {
    toFun := fun x => x 0
    invFun := fun a _ => a
    left_inv := by
      intro x
      funext i
      fin_cases i
      rfl
    right_inv := by
      intro a
      rfl }
  have hF : ∀ x, F x = (fun a : Fin 2 => F (fun _ => a)) (e x) := by
    intro x
    have hx : x = (fun _ => x 0) := by
      funext i
      fin_cases i
      rfl
    change F x = F (fun _ => e x)
    simpa [e] using congrArg F hx
  rw [Fintype.sum_equiv e F (fun a : Fin 2 => F (fun _ => a)) hF, Fin.sum_univ_two]
  simp [F]

/-- Concrete regression example: the same binary copy HMM assigns probability
`0` to the observed word `[1]`. -/
theorem binaryCopyHMM_observedCylinder_1 :
    observedSequenceMeasure (latent := 2) (obs := 2) binaryCopyHMM
        (MarkovDeFinettiRecurrence.cylinder (k := 2) ([1] : List (Fin 2))) = 0 := by
  classical
  rw [observedSequenceMeasure_cylinder_eq_observedWordProb (latent := 2) (obs := 2) binaryCopyHMM]
  let F : (Fin 1 → Fin 2) → ℝ≥0∞ := fun x =>
    wordProb (k := 2) binaryAbsorbingZeroLatent (List.ofFn x) *
      observationWeight (latent := 2) (obs := 2) binaryCopyHMM (List.ofFn x)
        ([1] : List (Fin 2))
  change ∑ x : Fin 1 → Fin 2, F x = 0
  let e : (Fin 1 → Fin 2) ≃ Fin 2 := {
    toFun := fun x => x 0
    invFun := fun a _ => a
    left_inv := by
      intro x
      funext i
      fin_cases i
      rfl
    right_inv := by
      intro a
      rfl }
  have hF : ∀ x, F x = (fun a : Fin 2 => F (fun _ => a)) (e x) := by
    intro x
    have hx : x = (fun _ => x 0) := by
      funext i
      fin_cases i
      rfl
    change F x = F (fun _ => e x)
    simpa [e] using congrArg F hx
  rw [Fintype.sum_equiv e F (fun a : Fin 2 => F (fun _ => a)) hF, Fin.sum_univ_two]
  simp [F]

end BinaryExamples

/-- Prefix-measure surface carried by a fixed latent Markov parameter and a
fixed emission kernel, defined from the observed sequence law on cylinders. -/
noncomputable def observedCylinderPrefixMeasure
    (emission : Fin latent → ProbabilityMeasure (Fin obs))
    (θ : MarkovParam latent) :
    Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin obs) where
  toFun ys :=
    observedSequenceMeasure (latent := latent) (obs := obs) ⟨θ, emission⟩
      (MarkovDeFinettiRecurrence.cylinder (k := obs) ys)
  root_eq_one' := by
    haveI :
        IsProbabilityMeasure
          (observedSequenceMeasure (latent := latent) (obs := obs) ⟨θ, emission⟩) :=
      observedSequenceMeasure_isProbability (latent := latent) (obs := obs) ⟨θ, emission⟩
    rw [show MarkovDeFinettiRecurrence.cylinder (k := obs) [] = Set.univ by
      ext ω
      simp [MarkovDeFinettiRecurrence.cylinder]]
    exact measure_univ
  additive' := by
    classical
    intro x
    have hpart :
        MarkovDeFinettiRecurrence.cylinder (k := obs) x =
          ⋃ a ∈ (Finset.univ : Finset (Fin obs)),
            MarkovDeFinettiRecurrence.cylinder (k := obs) (x ++ [a]) := by
      ext ω
      constructor
      · intro hω
        refine Set.mem_iUnion.mpr ⟨ω x.length, ?_⟩
        refine Set.mem_iUnion.mpr ⟨by simp, ?_⟩
        refine Set.mem_iInter.mpr ?_
        intro j
        by_cases hj : j.1 < x.length
        · have hmem := Set.mem_iInter.mp hω ⟨j.1, hj⟩
          simpa [List.get_eq_getElem, hj] using hmem
        · have hjEq : j.1 = x.length := by
            have hge : x.length ≤ j.1 := Nat.le_of_not_lt hj
            have hlt : j.1 < x.length + 1 := by simpa using j.2
            omega
          simp [hjEq]
      · intro hω
        rcases Set.mem_iUnion.mp hω with ⟨a, hω⟩
        rcases Set.mem_iUnion.mp hω with ⟨_, ha⟩
        refine Set.mem_iInter.mpr ?_
        intro j
        have hmem := Set.mem_iInter.mp ha ⟨j.1, by simp⟩
        simpa [List.get_eq_getElem, List.getElem_append, j.2] using hmem
    have hmeas :
        ∀ a ∈ (Finset.univ : Finset (Fin obs)),
          MeasurableSet (MarkovDeFinettiRecurrence.cylinder (k := obs) (x ++ [a])) := by
      intro a _
      exact measurableSet_cylinder (obs := obs) (x ++ [a])
    have hdisj :
        ∀ a ∈ (Finset.univ : Finset (Fin obs)),
          ∀ b ∈ (Finset.univ : Finset (Fin obs)), a ≠ b →
            Disjoint
              (MarkovDeFinettiRecurrence.cylinder (k := obs) (x ++ [a]))
              (MarkovDeFinettiRecurrence.cylinder (k := obs) (x ++ [b])) := by
      intro a _ b _ hab
      refine Set.disjoint_left.2 ?_
      intro ω ha hb
      have ha' := Set.mem_iInter.mp ha ⟨x.length, by simp⟩
      have hb' := Set.mem_iInter.mp hb ⟨x.length, by simp⟩
      have hxa : ω x.length = a := by
        simpa [List.get_eq_getElem] using ha'
      have hxb : ω x.length = b := by
        simpa [List.get_eq_getElem] using hb'
      exact hab (hxa.symm.trans hxb)
    calc
      (∑ a : Fin obs,
          observedSequenceMeasure (latent := latent) (obs := obs) ⟨θ, emission⟩
            (MarkovDeFinettiRecurrence.cylinder (k := obs) (x ++ [a]))) =
        Finset.sum (Finset.univ : Finset (Fin obs)) (fun a : Fin obs =>
          observedSequenceMeasure (latent := latent) (obs := obs) ⟨θ, emission⟩
            (MarkovDeFinettiRecurrence.cylinder (k := obs) (x ++ [a]))) := by
              simp
      _ =
        observedSequenceMeasure (latent := latent) (obs := obs) ⟨θ, emission⟩
          (⋃ a ∈ (Finset.univ : Finset (Fin obs)),
            MarkovDeFinettiRecurrence.cylinder (k := obs) (x ++ [a])) := by
              symm
              exact measure_biUnion_finset
                (μ := observedSequenceMeasure (latent := latent) (obs := obs) ⟨θ, emission⟩)
                (s := Finset.univ)
                (f := fun a : Fin obs =>
                  MarkovDeFinettiRecurrence.cylinder (k := obs) (x ++ [a]))
                hdisj
                hmeas
      _ =
        observedSequenceMeasure (latent := latent) (obs := obs) ⟨θ, emission⟩
          (MarkovDeFinettiRecurrence.cylinder (k := obs) x) := by
              rw [hpart]

section FiniteDiscreteMixtures

variable {n : ℕ}

local instance instFiniteHMMFiniteDiscreteMixtureIndexMeasurableSpace :
    MeasurableSpace (Fin n) := ⊤
local instance instFiniteHMMFiniteDiscreteMixtureIndexMeasurableSingletonClass :
    MeasurableSingletonClass (Fin n) := ⟨fun _ => by simp⟩

/-- Finite discrete law on latent Markov parameters with a fixed emission
kernel. -/
noncomputable def finiteHMMLatentMixingLaw
    (w : Fin n → ℝ≥0∞) (hw : ∑ i : Fin n, w i = 1)
    (Θ : Fin n → MarkovParam latent) :
    Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov latent :=
  let p : PMF (Fin n) := PMF.ofFintype w (by simpa using hw)
  let μ : ProbabilityMeasure (Fin n) := ⟨p.toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩
  let g : Fin n → MarkovParam latent := fun i => Θ i
  let hg : Measurable g := measurable_of_finite g
  μ.map hg.aemeasurable

/-- The observed-word weight of the encoded finite discrete latent mixture is
exactly the weighted sum of the component observed-word probabilities. -/
theorem observedWordWeightViaProbMarkov_eq_finiteDiracMixture
    (emission : Fin latent → ProbabilityMeasure (Fin obs))
    (w : Fin n → ℝ≥0∞) (hw : ∑ i : Fin n, w i = 1)
    (Θ : Fin n → MarkovParam latent)
    (ys : List (Fin obs)) :
    observedWordWeightViaProbMarkov (latent := latent) (obs := obs)
        emission (finiteHMMLatentMixingLaw (latent := latent) w hw Θ) ys =
      ∑ i : Fin n, w i * observedWordProb (latent := latent) (obs := obs) ⟨Θ i, emission⟩ ys := by
  classical
  let p : PMF (Fin n) := PMF.ofFintype w (by simpa using hw)
  let μ : ProbabilityMeasure (Fin n) := ⟨p.toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩
  let g : Fin n → MarkovParam latent := fun i => Θ i
  let hg : Measurable g := measurable_of_finite g
  unfold observedWordWeightViaProbMarkov
  dsimp [finiteHMMLatentMixingLaw]
  have hobsMeas :
      Measurable
        (fun θ : MarkovParam latent =>
          observedWordProb (latent := latent) (obs := obs) ⟨θ, emission⟩ ys) :=
    measurable_observedWordProb_borel (latent := latent) (obs := obs) emission ys
  have hobsAemeas :
      AEMeasurable
        (fun θ : MarkovParam latent =>
          observedWordProb (latent := latent) (obs := obs) ⟨θ, emission⟩ ys)
        (((finiteHMMLatentMixingLaw (latent := latent) w hw Θ) :
            Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov latent) :
          Measure (MarkovParam latent)) :=
    hobsMeas.aemeasurable
  have hmap := MeasureTheory.lintegral_map'
      (μ := (μ : Measure (Fin n)))
      (f := fun θ : MarkovParam latent =>
        observedWordProb (latent := latent) (obs := obs) ⟨θ, emission⟩ ys)
      (g := g)
      hobsAemeas
      hg.aemeasurable
  calc
    ∫⁻ θ : MarkovParam latent,
        observedWordProb (latent := latent) (obs := obs) ⟨θ, emission⟩ ys
          ∂(((finiteHMMLatentMixingLaw (latent := latent) w hw Θ) :
              Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov latent) :
            Measure (MarkovParam latent)) =
      ∫⁻ i : Fin n,
        observedWordProb (latent := latent) (obs := obs) ⟨g i, emission⟩ ys
          ∂(μ : Measure (Fin n)) := by
            simpa [finiteHMMLatentMixingLaw, p, μ, g, hg] using hmap
    _ =
      ∑ i : Fin n,
        ((μ : Measure (Fin n)) {i}) *
          observedWordProb (latent := latent) (obs := obs) ⟨g i, emission⟩ ys := by
            rw [MeasureTheory.lintegral_fintype
              (μ := (μ : Measure (Fin n)))
              (f := fun i : Fin n =>
                observedWordProb (latent := latent) (obs := obs) ⟨g i, emission⟩ ys)]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [mul_comm]
    _ =
      ∑ i : Fin n, w i * observedWordProb (latent := latent) (obs := obs) ⟨Θ i, emission⟩ ys := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hsingleton :
            ((μ : Measure (Fin n)) {i}) = w i := by
          dsimp [μ, p]
          rw [PMF.toMeasure_apply_singleton (p := PMF.ofFintype w (by simpa using hw))
            i (MeasurableSet.singleton i)]
          simp [PMF.ofFintype]
        rw [hsingleton]

/-- Finite discrete mixtures of latent Markov parameters yield an honest finite
HMM factorization package for the fixed emission kernel. -/
theorem categoricalBorelFiniteHMMFactorization_of_finiteDiscreteMixture
    (emission : Fin latent → ProbabilityMeasure (Fin obs))
    (w : Fin n → ℝ≥0∞) (hw : ∑ i : Fin n, w i = 1)
    (Θ : Fin n → MarkovParam latent) :
    CategoricalBorelFiniteHMMFactorization latent obs emission
      (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.xiPrefixMeasure
        (ν := fun i : Fin n => observedCylinderPrefixMeasure (latent := latent) (obs := obs) emission (Θ i))
        (w := w)
        (hw := by simpa [tsum_fintype] using hw)) := by
  refine ⟨finiteHMMLatentMixingLaw (latent := latent) w hw Θ, ?_⟩
  intro ys
  unfold Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.xiPrefixMeasure
    Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.xiFun
  simp only [Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure.toSemimeasure_apply]
  calc
    ∑' i : Fin n,
        w i *
          observedCylinderPrefixMeasure (latent := latent) (obs := obs) emission (Θ i) ys =
      ∑ i : Fin n,
        w i *
          observedSequenceMeasure (latent := latent) (obs := obs) ⟨Θ i, emission⟩
            (MarkovDeFinettiRecurrence.cylinder (k := obs) ys) := by
              simp [observedCylinderPrefixMeasure, tsum_fintype]
    _ =
      ∑ i : Fin n,
        w i * observedWordProb (latent := latent) (obs := obs) ⟨Θ i, emission⟩ ys := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [observedSequenceMeasure_cylinder_eq_observedWordProb
            (latent := latent) (obs := obs) ⟨Θ i, emission⟩ ys]
    _ =
      observedWordWeightViaProbMarkov (latent := latent) (obs := obs)
        emission (finiteHMMLatentMixingLaw (latent := latent) w hw Θ) ys := by
            symm
            exact observedWordWeightViaProbMarkov_eq_finiteDiracMixture
              (latent := latent) (obs := obs) emission w hw Θ ys

end FiniteDiscreteMixtures

end Mettapedia.CategoryTheory
