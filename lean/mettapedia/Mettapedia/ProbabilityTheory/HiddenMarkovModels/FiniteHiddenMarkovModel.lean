import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHardBase
import Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence
import Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSequenceKernel

/-!
# Finite Hidden Markov Models

This file gives a clean finite-state/finitely-emitting HMM surface:
* a latent finite Markov parameter,
* a finite emission kernel,
* finite-word observation probabilities obtained by summing over latent words.

We deliberately stop before Baum-Welch or continuous-state infrastructure.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.HiddenMarkovModels

open scoped BigOperators NNReal ENNReal
open Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard
open Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSequenceKernel
open MeasureTheory
open _root_.ProbabilityTheory

namespace FiniteHiddenMarkovModel

variable {latent obs : ℕ}

/-- Finite hidden Markov model with a latent finite-state chain and a finite
emission kernel. -/
structure FiniteHMMParam (latent obs : ℕ) where
  latentParam : MarkovParam latent
  emission : Fin latent → ProbabilityMeasure (Fin obs)

/-- Finite paired latent/observation state. -/
abbrev PairState (latent obs : ℕ) := Fin latent × Fin obs

/-- Encoded paired state for reuse of the ordinary finite `MarkovParam` API. -/
abbrev EncodedPairState (latent obs : ℕ) := Fin (Fintype.card (PairState latent obs))

/-- Emission probability of observing `y` from latent state `x`. -/
def emissionProb (θ : FiniteHMMParam latent obs) (x : Fin latent) (y : Fin obs) : ℝ≥0 :=
  θ.emission x (Set.singleton y)

/-- The emission PMF from latent state `x`. -/
noncomputable def emissionPMF (θ : FiniteHMMParam latent obs) (x : Fin latent) : PMF (Fin obs) :=
  ((θ.emission x : Measure (Fin obs)).toPMF)

/-- One-step paired PMF: sample the next latent state, then emit an observation
from that latent state. -/
noncomputable def pairedStepPMF
    (θ : FiniteHMMParam latent obs) (z : PairState latent obs) : PMF (PairState latent obs) :=
  ((θ.latentParam.trans z.1 : Measure (Fin latent)).toPMF).bind
    (fun x' => (emissionPMF (latent := latent) (obs := obs) θ x').map (fun y => (x', y)))

/-- Initial paired PMF. -/
noncomputable def pairedInitPMF (θ : FiniteHMMParam latent obs) : PMF (PairState latent obs) :=
  ((θ.latentParam.init : Measure (Fin latent)).toPMF).bind
    (fun x => (emissionPMF (latent := latent) (obs := obs) θ x).map (fun y => (x, y)))

/-- Paired-state Markov parameter whose observation projection is the HMM
observation process. -/
noncomputable def pairedMarkovParam (θ : FiniteHMMParam latent obs) :
    MarkovParam (Fintype.card (PairState latent obs)) where
  init :=
    ⟨((pairedInitPMF (latent := latent) (obs := obs) θ).map
        (Fintype.equivFin (PairState latent obs))).toMeasure, by infer_instance⟩
  trans z :=
    ⟨((pairedStepPMF (latent := latent) (obs := obs) θ
        ((Fintype.equivFin (PairState latent obs)).symm z)).map
        (Fintype.equivFin (PairState latent obs))).toMeasure, by infer_instance⟩

/-- Sequence law on paired latent/observation states. -/
noncomputable def pairedSequenceMeasure (θ : FiniteHMMParam latent obs) :
    Measure (ℕ → EncodedPairState latent obs) :=
  markovSequenceMeasure (k := Fintype.card (PairState latent obs))
    (pairedMarkovParam (latent := latent) (obs := obs) θ)

/-- Forget the latent coordinate and keep only the observation sequence. -/
def observationSequenceOfPairedTrajectory :
    (ℕ → EncodedPairState latent obs) → ℕ → Fin obs :=
  fun ω n => ((Fintype.equivFin (PairState latent obs)).symm (ω n)).2

theorem measurable_observationSequenceOfPairedTrajectory :
    Measurable (observationSequenceOfPairedTrajectory (latent := latent) (obs := obs)) := by
  unfold observationSequenceOfPairedTrajectory
  fun_prop

/-- Observed sequence law of the finite HMM, obtained by projecting the paired
sequence law to the observation coordinate. -/
noncomputable def observedSequenceMeasure (θ : FiniteHMMParam latent obs) :
    Measure (ℕ → Fin obs) :=
  (pairedSequenceMeasure (latent := latent) (obs := obs) θ).map
    (observationSequenceOfPairedTrajectory (latent := latent) (obs := obs))

instance observedSequenceMeasure_isProbability (θ : FiniteHMMParam latent obs) :
    IsProbabilityMeasure (observedSequenceMeasure (latent := latent) (obs := obs) θ) := by
  unfold observedSequenceMeasure
  haveI :
      IsProbabilityMeasure (pairedSequenceMeasure (latent := latent) (obs := obs) θ) :=
    Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSequenceKernel.markovSequenceMeasure_isProbability
      (k := Fintype.card (PairState latent obs))
      (θ := pairedMarkovParam (latent := latent) (obs := obs) θ)
  exact Measure.isProbabilityMeasure_map
    (measurable_observationSequenceOfPairedTrajectory (latent := latent) (obs := obs)).aemeasurable

@[simp] theorem emissionPMF_apply_eq
    (θ : FiniteHMMParam latent obs) (x : Fin latent) (y : Fin obs) :
    emissionPMF (latent := latent) (obs := obs) θ x y = ((θ.emission x) {y} : ℝ≥0∞) := by
  rw [emissionPMF, Measure.toPMF_apply]
  simp

@[simp] theorem mappedEmissionPMF_apply
    (θ : FiniteHMMParam latent obs)
    (x x' : Fin latent) (y : Fin obs) :
    (PMF.map (fun y0 => (x', y0)) (emissionPMF (latent := latent) (obs := obs) θ x'))
        (x, y) =
      if x = x' then ((θ.emission x') {y} : ℝ≥0∞) else 0 := by
  by_cases hxx' : x = x'
  · subst hxx'
    rw [← PMF.toMeasure_apply_singleton
      (p := (emissionPMF (latent := latent) (obs := obs) θ x).map (fun y0 => (x, y0)))
      (a := (x, y)) (h := measurableSet_singleton _)]
    rw [PMF.toMeasure_map_apply
      (f := fun y0 => (x, y0))
      (p := emissionPMF (latent := latent) (obs := obs) θ x)
      (s := ({(x, y)} : Set (PairState latent obs)))
      (by fun_prop) (measurableSet_singleton _)]
    have hpre :
        (fun y0 : Fin obs => (x, y0)) ⁻¹' ({(x, y)} : Set (PairState latent obs)) = {y} := by
      ext y0
      simp
    rw [hpre, PMF.toMeasure_apply_singleton
      (p := emissionPMF (latent := latent) (obs := obs) θ x)
      (a := y) (h := measurableSet_singleton _)]
    simp [emissionPMF_apply_eq]
  · rw [← PMF.toMeasure_apply_singleton
      (p := (emissionPMF (latent := latent) (obs := obs) θ x').map (fun y0 => (x', y0)))
      (a := (x, y)) (h := measurableSet_singleton _)]
    rw [PMF.toMeasure_map_apply
      (f := fun y0 => (x', y0))
      (p := emissionPMF (latent := latent) (obs := obs) θ x')
      (s := ({(x, y)} : Set (PairState latent obs)))
      (by fun_prop) (measurableSet_singleton _)]
    have hpre :
        (fun y0 : Fin obs => (x', y0)) ⁻¹' ({(x, y)} : Set (PairState latent obs)) = ∅ := by
      ext y0
      constructor
      · intro hy0
        have : x' = x := by
          simpa using congrArg Prod.fst hy0
        exact False.elim (hxx' this.symm)
      · intro hy0
        cases hy0
    rw [hpre]
    simp [if_neg hxx']

@[simp] theorem pairedInitPMF_apply
    (θ : FiniteHMMParam latent obs) (x : Fin latent) (y : Fin obs) :
    pairedInitPMF (latent := latent) (obs := obs) θ (x, y) =
      ((θ.latentParam.init {x} : ℝ≥0∞) * ((θ.emission x) {y} : ℝ≥0∞)) := by
  rw [pairedInitPMF, PMF.bind_apply]
  rw [tsum_eq_single x]
  · rw [mappedEmissionPMF_apply (θ := θ) (x := x) (x' := x) (y := y)]
    simp [Measure.toPMF_apply]
  · intro a ha
    rw [mappedEmissionPMF_apply (θ := θ) (x := x) (x' := a) (y := y)]
    simp [if_neg (Ne.symm ha), Measure.toPMF_apply]

@[simp] theorem pairedStepPMF_apply
    (θ : FiniteHMMParam latent obs)
    (x x' : Fin latent) (y y' : Fin obs) :
    pairedStepPMF (latent := latent) (obs := obs) θ (x, y) (x', y') =
      (((θ.latentParam.trans x) {x'} : ℝ≥0∞) * ((θ.emission x') {y'} : ℝ≥0∞)) := by
  rw [pairedStepPMF, PMF.bind_apply]
  rw [tsum_eq_single x']
  · rw [mappedEmissionPMF_apply (θ := θ) (x := x') (x' := x') (y := y')]
    simp [Measure.toPMF_apply]
  · intro a ha
    rw [mappedEmissionPMF_apply (θ := θ) (x := x') (x' := a) (y := y')]
    simp [if_neg (Ne.symm ha), Measure.toPMF_apply]

@[simp] theorem pairedInitProb_eq
    (θ : FiniteHMMParam latent obs) (x : Fin latent) (y : Fin obs) :
    initProb (k := Fintype.card (PairState latent obs))
      (pairedMarkovParam (latent := latent) (obs := obs) θ)
      ((Fintype.equivFin (PairState latent obs)) (x, y)) =
      initProb (k := latent) θ.latentParam x * emissionProb θ x y := by
  apply ENNReal.coe_injective
  rw [initProb]
  have hmap := PMF.toMeasure_map_apply
    (f := Fintype.equivFin (PairState latent obs))
    (p := pairedInitPMF (latent := latent) (obs := obs) θ)
    (s := ({(Fintype.equivFin (PairState latent obs)) (x, y)} : Set (EncodedPairState latent obs)))
    (by fun_prop) (measurableSet_singleton _)
  have hpre :
      (Fintype.equivFin (PairState latent obs)) ⁻¹'
          ({(Fintype.equivFin (PairState latent obs)) (x, y)} :
            Set (EncodedPairState latent obs)) = {(x, y)} := by
    ext z
    simp
  rw [hpre] at hmap
  calc
    (((pairedMarkovParam (latent := latent) (obs := obs) θ).init
        ({(Fintype.equivFin (PairState latent obs)) (x, y)} :
          Set (EncodedPairState latent obs)) : ℝ≥0∞)) =
        (((PMF.map (Fintype.equivFin (PairState latent obs))
          (pairedInitPMF (latent := latent) (obs := obs) θ)).toMeasure
            ({(Fintype.equivFin (PairState latent obs)) (x, y)} :
              Set (EncodedPairState latent obs)) : ℝ≥0∞)) := by
          simp [pairedMarkovParam]
    _ =
        (((pairedInitPMF (latent := latent) (obs := obs) θ).toMeasure {(x, y)} : ℝ≥0∞)) := by
          exact hmap
    _ = pairedInitPMF (latent := latent) (obs := obs) θ (x, y) := by
          rw [PMF.toMeasure_apply_singleton
            (p := pairedInitPMF (latent := latent) (obs := obs) θ)
            (a := (x, y)) (h := measurableSet_singleton _)]
    _ = ((θ.latentParam.init {x} : ℝ≥0∞) * ((θ.emission x) {y} : ℝ≥0∞)) :=
          pairedInitPMF_apply (latent := latent) (obs := obs) θ x y
    _ = ((initProb (k := latent) θ.latentParam x * emissionProb θ x y : ℝ≥0) : ℝ≥0∞) := by
          rfl

@[simp] theorem pairedStepProb_eq
    (θ : FiniteHMMParam latent obs)
    (x x' : Fin latent) (y y' : Fin obs) :
    stepProb (k := Fintype.card (PairState latent obs))
      (pairedMarkovParam (latent := latent) (obs := obs) θ)
      ((Fintype.equivFin (PairState latent obs)) (x, y))
      ((Fintype.equivFin (PairState latent obs)) (x', y')) =
      stepProb (k := latent) θ.latentParam x x' * emissionProb θ x' y' := by
  apply ENNReal.coe_injective
  rw [stepProb]
  have hmap := PMF.toMeasure_map_apply
    (f := Fintype.equivFin (PairState latent obs))
    (p := pairedStepPMF (latent := latent) (obs := obs) θ (x, y))
    (s := ({(Fintype.equivFin (PairState latent obs)) (x', y')} :
      Set (EncodedPairState latent obs)))
    (by fun_prop) (measurableSet_singleton _)
  have hpre :
      (Fintype.equivFin (PairState latent obs)) ⁻¹'
          ({(Fintype.equivFin (PairState latent obs)) (x', y')} :
            Set (EncodedPairState latent obs)) = {(x', y')} := by
    ext z
    simp
  rw [hpre] at hmap
  calc
    ((((pairedMarkovParam (latent := latent) (obs := obs) θ).trans
        ((Fintype.equivFin (PairState latent obs)) (x, y)))
        ({(Fintype.equivFin (PairState latent obs)) (x', y')} :
          Set (EncodedPairState latent obs)) : ℝ≥0∞)) =
        (((PMF.map (Fintype.equivFin (PairState latent obs))
          (pairedStepPMF (latent := latent) (obs := obs) θ (x, y))).toMeasure
            ({(Fintype.equivFin (PairState latent obs)) (x', y')} :
              Set (EncodedPairState latent obs)) : ℝ≥0∞)) := by
          simp [pairedMarkovParam]
    _ =
        (((pairedStepPMF (latent := latent) (obs := obs) θ (x, y)).toMeasure {(x', y')} :
          ℝ≥0∞)) := by
          exact hmap
    _ = pairedStepPMF (latent := latent) (obs := obs) θ (x, y) (x', y') := by
          rw [PMF.toMeasure_apply_singleton
            (p := pairedStepPMF (latent := latent) (obs := obs) θ (x, y))
            (a := (x', y')) (h := measurableSet_singleton _)]
    _ =
        (((θ.latentParam.trans x) {x'} : ℝ≥0∞) * ((θ.emission x') {y'} : ℝ≥0∞)) :=
          pairedStepPMF_apply (latent := latent) (obs := obs) θ x x' y y'
    _ = ((stepProb (k := latent) θ.latentParam x x' * emissionProb θ x' y' : ℝ≥0) : ℝ≥0∞) := by
          rfl

/-- The first `n` paired states of a trajectory. -/
def pairedPrefixMap (n : ℕ) :
    (ℕ → EncodedPairState latent obs) → Fin n → EncodedPairState latent obs :=
  fun ω i => ω i

theorem measurable_pairedPrefixMap (n : ℕ) :
    Measurable (pairedPrefixMap (latent := latent) (obs := obs) n) := by
  unfold pairedPrefixMap
  fun_prop

theorem pairedPrefixMap_preimage_singleton_eq_cylinder_ofFn
    {n : ℕ} (p : Fin n → EncodedPairState latent obs) :
    pairedPrefixMap (latent := latent) (obs := obs) n ⁻¹' {p} =
      Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder
        (k := Fintype.card (PairState latent obs)) (List.ofFn p) := by
  ext ω
  constructor
  · intro hω
    have hω' : pairedPrefixMap (latent := latent) (obs := obs) n ω = p := by
      simpa [pairedPrefixMap] using hω
    refine Set.mem_iInter.mpr ?_
    intro i
    have hi :=
      congrArg
        (fun f : Fin n → EncodedPairState latent obs =>
          f (Fin.cast (by simp) i)) hω'
    calc
      ω i.1 = p (Fin.cast (by simp) i) := by
        simpa [pairedPrefixMap] using hi
      _ = (List.ofFn p)[i.1] := by
        simpa using (List.get_ofFn p i).symm
  · intro hω
    have hω' :
        pairedPrefixMap (latent := latent) (obs := obs) n ω = p := by
      funext i
      have hi := Set.mem_iInter.mp hω (Fin.cast (by simp) i)
      calc
        ω i.1 = (List.ofFn p)[i.1] := hi
        _ = p i := by
          exact List.get_ofFn p (Fin.cast (by simp) i)
    simpa [pairedPrefixMap] using hω'

/-- The paired-state prefix obtained by combining a latent prefix with a fixed
observation word. -/
def pairedWordOfLatentPrefix (ys : List (Fin obs)) :
    (Fin ys.length → Fin latent) → (Fin ys.length → EncodedPairState latent obs) :=
  fun xs i => (Fintype.equivFin (PairState latent obs)) (xs i, ys.get i)

theorem pairedWordOfLatentPrefix_injective (ys : List (Fin obs)) :
    Function.Injective (pairedWordOfLatentPrefix (latent := latent) (obs := obs) ys) := by
  intro xs₁ xs₂ hxs
  funext i
  have hi := congrArg (fun f : Fin ys.length → EncodedPairState latent obs => f i) hxs
  exact congrArg Prod.fst ((Fintype.equivFin (PairState latent obs)).injective hi)

/-- Finite set of paired prefixes whose observation projection is the fixed word
`ys`. -/
def matchingPairedPrefixFinset (ys : List (Fin obs)) :
    Finset (Fin ys.length → EncodedPairState latent obs) :=
  Finset.univ.image (pairedWordOfLatentPrefix (latent := latent) (obs := obs) ys)

theorem preimage_observedCylinder_eq_preimage_matchingPairedPrefixFinset
    (ys : List (Fin obs)) :
    (observationSequenceOfPairedTrajectory (latent := latent) (obs := obs) ⁻¹'
        Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder (k := obs) ys) =
      pairedPrefixMap (latent := latent) (obs := obs) ys.length ⁻¹'
        (matchingPairedPrefixFinset (latent := latent) (obs := obs) ys : Set _) := by
  ext ω
  constructor
  · intro hω
    refine Finset.mem_image.mpr ?_
    refine ⟨fun i => ((Fintype.equivFin (PairState latent obs)).symm (ω i)).1, Finset.mem_univ _, ?_⟩
    ext i
    have hi : ((Fintype.equivFin (PairState latent obs)).symm (ω i)).2 = ys.get i := by
      exact Set.mem_iInter.mp hω i
    have hpair :
        (((Fintype.equivFin (PairState latent obs)).symm (ω i)).1, ys.get i) =
          ((Fintype.equivFin (PairState latent obs)).symm (ω i)) := by
      apply Prod.ext
      · rfl
      · simpa [observationSequenceOfPairedTrajectory] using hi.symm
    simpa [pairedWordOfLatentPrefix, pairedPrefixMap] using
      congrArg Fin.val (congrArg (Fintype.equivFin (PairState latent obs)) hpair)
  · intro hω
    rcases Finset.mem_image.mp hω with ⟨xs, -, hxs⟩
    refine Set.mem_iInter.mpr ?_
    intro i
    have hi := congrArg (fun f : Fin ys.length → EncodedPairState latent obs => f i) hxs
    have hpair :
        (xs i, ys.get i) = ((Fintype.equivFin (PairState latent obs)).symm (ω i)) := by
      exact (Fintype.equivFin (PairState latent obs)).injective <| by
        simpa [pairedWordOfLatentPrefix, pairedPrefixMap] using hi
    simpa [observationSequenceOfPairedTrajectory] using (congrArg Prod.snd hpair).symm

/-- Observation likelihood along one latent word. -/
def observationWeight :
    FiniteHMMParam latent obs → List (Fin latent) → List (Fin obs) → ℝ≥0∞
  | _, [], [] => 1
  | θ, x :: xs, y :: ys =>
      (emissionProb θ x y : ℝ≥0∞) * observationWeight θ xs ys
  | _, _, _ => 0

/-- Finite-word observation probability, obtained by summing over all latent
words of the same length. -/
def observedWordProb (θ : FiniteHMMParam latent obs) (ys : List (Fin obs)) : ℝ≥0∞ :=
  ∑ xs : Fin ys.length → Fin latent,
    wordProb (k := latent) θ.latentParam (List.ofFn xs) *
      observationWeight θ (List.ofFn xs) ys

@[simp] theorem observationWeight_nil (θ : FiniteHMMParam latent obs) :
    observationWeight θ [] [] = 1 := rfl

@[simp] theorem observationWeight_cons
    (θ : FiniteHMMParam latent obs)
    (x : Fin latent) (xs : List (Fin latent))
    (y : Fin obs) (ys : List (Fin obs)) :
    observationWeight θ (x :: xs) (y :: ys) =
      (emissionProb θ x y : ℝ≥0∞) * observationWeight θ xs ys := rfl

@[simp] theorem observationWeight_length_mismatch_left
    (θ : FiniteHMMParam latent obs) (x : Fin latent) (xs : List (Fin latent)) :
    observationWeight θ (x :: xs) [] = 0 := rfl

@[simp] theorem observationWeight_length_mismatch_right
    (θ : FiniteHMMParam latent obs) (y : Fin obs) (ys : List (Fin obs)) :
    observationWeight θ [] (y :: ys) = 0 := rfl

@[simp] theorem observedWordProb_nil (θ : FiniteHMMParam latent obs) :
    observedWordProb θ [] = 1 := by
  classical
  simp [observedWordProb, wordProb, wordProbNN]

theorem measurableSet_cylinder (ys : List (Fin obs)) :
    MeasurableSet (Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder (k := obs) ys) := by
  unfold Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder
  refine MeasurableSet.iInter ?_
  intro i
  exact (measurable_pi_apply i.1) (measurableSet_singleton _)

@[simp] theorem ofFn_pairedWordOfLatentPrefix
    {n : ℕ} (ys : Fin n → Fin obs) (xs : Fin n → Fin latent) :
    List.ofFn
        (pairedWordOfLatentPrefix (latent := latent) (obs := obs) (List.ofFn ys)
          (fun i => xs (Fin.cast (by simp) i))) =
      List.ofFn (fun i => (Fintype.equivFin (PairState latent obs)) (xs i, ys i)) := by
  apply List.ext_get
  · simp
  · intro i hi₁ hi₂
    rw [List.get_ofFn, List.get_ofFn]
    simp [pairedWordOfLatentPrefix]

theorem pairedWordProbAux_eq
    (θ : FiniteHMMParam latent obs) :
    ∀ n (x : Fin latent) (y : Fin obs)
      (xs : Fin n → Fin latent) (ys : Fin n → Fin obs),
      (wordProbAux (k := Fintype.card (PairState latent obs))
        (pairedMarkovParam (latent := latent) (obs := obs) θ)
        ((Fintype.equivFin (PairState latent obs)) (x, y))
        (List.ofFn (fun i => (Fintype.equivFin (PairState latent obs)) (xs i, ys i))) : ℝ≥0∞) =
      (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
        observationWeight θ (List.ofFn xs) (List.ofFn ys)
  | 0, x, y, xs, ys => by
      simp [Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.wordProbAux]
  | n + 1, x, y, xs, ys => by
      let x₀ : Fin latent := xs 0
      let y₀ : Fin obs := ys 0
      let xsTail : Fin n → Fin latent := fun i => xs i.succ
      let ysTail : Fin n → Fin obs := fun i => ys i.succ
      have hpair :
          List.ofFn (fun i : Fin (n + 1) =>
            (Fintype.equivFin (PairState latent obs)) (xs i, ys i)) =
            (Fintype.equivFin (PairState latent obs)) (x₀, y₀) ::
              List.ofFn (fun i : Fin n =>
                (Fintype.equivFin (PairState latent obs)) (xsTail i, ysTail i)) := by
        have hcons :
            Fin.cons ((Fintype.equivFin (PairState latent obs)) (x₀, y₀))
              (fun i : Fin n =>
                (Fintype.equivFin (PairState latent obs)) (xsTail i, ysTail i)) =
              (fun i : Fin (n + 1) =>
                (Fintype.equivFin (PairState latent obs)) (xs i, ys i)) := by
          ext i
          cases i using Fin.cases <;> rfl
        calc
          List.ofFn (fun i : Fin (n + 1) =>
              (Fintype.equivFin (PairState latent obs)) (xs i, ys i)) =
              List.ofFn (Fin.cons ((Fintype.equivFin (PairState latent obs)) (x₀, y₀))
                (fun i : Fin n =>
                  (Fintype.equivFin (PairState latent obs)) (xsTail i, ysTail i))) := by
                    rw [hcons]
          _ = (Fintype.equivFin (PairState latent obs)) (x₀, y₀) ::
                List.ofFn (fun i : Fin n =>
                  (Fintype.equivFin (PairState latent obs)) (xsTail i, ysTail i)) :=
                List.ofFn_cons
                  ((Fintype.equivFin (PairState latent obs)) (x₀, y₀))
                  (fun i : Fin n =>
                    (Fintype.equivFin (PairState latent obs)) (xsTail i, ysTail i))
      have hxs :
          List.ofFn xs = x₀ :: List.ofFn xsTail := by
        have hcons : Fin.cons x₀ xsTail = xs := by
          ext i
          cases i using Fin.cases <;> rfl
        calc
          List.ofFn xs = List.ofFn (Fin.cons x₀ xsTail) := by rw [← hcons]
          _ = x₀ :: List.ofFn xsTail := List.ofFn_cons x₀ xsTail
      have hys :
          List.ofFn ys = y₀ :: List.ofFn ysTail := by
        have hcons : Fin.cons y₀ ysTail = ys := by
          ext i
          cases i using Fin.cases <;> rfl
        calc
          List.ofFn ys = List.ofFn (Fin.cons y₀ ysTail) := by rw [← hcons]
          _ = y₀ :: List.ofFn ysTail := List.ofFn_cons y₀ ysTail
      have hstep :
          ((stepProb (k := Fintype.card (PairState latent obs))
              (pairedMarkovParam (latent := latent) (obs := obs) θ)
              ((Fintype.equivFin (PairState latent obs)) (x, y))
              ((Fintype.equivFin (PairState latent obs)) (x₀, y₀)) : ℝ≥0∞)) =
            (stepProb (k := latent) θ.latentParam x x₀ : ℝ≥0∞) *
              (emissionProb θ x₀ y₀ : ℝ≥0∞) := by
        exact_mod_cast
          pairedStepProb_eq (latent := latent) (obs := obs) θ x x₀ y y₀
      rw [hpair, hxs, hys]
      simp [Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.wordProbAux, observationWeight_cons,
        pairedWordProbAux_eq (θ := θ) n x₀ y₀ xsTail ysTail,
        x₀, y₀, xsTail, ysTail, mul_assoc, mul_left_comm, mul_comm]

theorem pairedWordProb_eq
    (θ : FiniteHMMParam latent obs) :
    ∀ n (xs : Fin n → Fin latent) (ys : Fin n → Fin obs),
      wordProb (k := Fintype.card (PairState latent obs))
        (pairedMarkovParam (latent := latent) (obs := obs) θ)
        (List.ofFn (fun i => (Fintype.equivFin (PairState latent obs)) (xs i, ys i))) =
      wordProb (k := latent) θ.latentParam (List.ofFn xs) *
        observationWeight θ (List.ofFn xs) (List.ofFn ys)
  | 0, xs, ys => by
      simp [Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.wordProb,
        Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.wordProbNN]
  | n + 1, xs, ys => by
      let x₀ : Fin latent := xs 0
      let y₀ : Fin obs := ys 0
      let xsTail : Fin n → Fin latent := fun i => xs i.succ
      let ysTail : Fin n → Fin obs := fun i => ys i.succ
      have hpair :
          List.ofFn (fun i : Fin (n + 1) =>
            (Fintype.equivFin (PairState latent obs)) (xs i, ys i)) =
            (Fintype.equivFin (PairState latent obs)) (x₀, y₀) ::
              List.ofFn (fun i : Fin n =>
                (Fintype.equivFin (PairState latent obs)) (xsTail i, ysTail i)) := by
        have hcons :
            Fin.cons ((Fintype.equivFin (PairState latent obs)) (x₀, y₀))
              (fun i : Fin n =>
                (Fintype.equivFin (PairState latent obs)) (xsTail i, ysTail i)) =
              (fun i : Fin (n + 1) =>
                (Fintype.equivFin (PairState latent obs)) (xs i, ys i)) := by
          ext i
          cases i using Fin.cases <;> rfl
        calc
          List.ofFn (fun i : Fin (n + 1) =>
              (Fintype.equivFin (PairState latent obs)) (xs i, ys i)) =
              List.ofFn (Fin.cons ((Fintype.equivFin (PairState latent obs)) (x₀, y₀))
                (fun i : Fin n =>
                  (Fintype.equivFin (PairState latent obs)) (xsTail i, ysTail i))) := by
                    rw [hcons]
          _ = (Fintype.equivFin (PairState latent obs)) (x₀, y₀) ::
                List.ofFn (fun i : Fin n =>
                  (Fintype.equivFin (PairState latent obs)) (xsTail i, ysTail i)) :=
                List.ofFn_cons
                  ((Fintype.equivFin (PairState latent obs)) (x₀, y₀))
                  (fun i : Fin n =>
                    (Fintype.equivFin (PairState latent obs)) (xsTail i, ysTail i))
      have hxs :
          List.ofFn xs = x₀ :: List.ofFn xsTail := by
        have hcons : Fin.cons x₀ xsTail = xs := by
          ext i
          cases i using Fin.cases <;> rfl
        calc
          List.ofFn xs = List.ofFn (Fin.cons x₀ xsTail) := by rw [← hcons]
          _ = x₀ :: List.ofFn xsTail := List.ofFn_cons x₀ xsTail
      have hys :
          List.ofFn ys = y₀ :: List.ofFn ysTail := by
        have hcons : Fin.cons y₀ ysTail = ys := by
          ext i
          cases i using Fin.cases <;> rfl
        calc
          List.ofFn ys = List.ofFn (Fin.cons y₀ ysTail) := by rw [← hcons]
          _ = y₀ :: List.ofFn ysTail := List.ofFn_cons y₀ ysTail
      have hinit :
          ((initProb (k := Fintype.card (PairState latent obs))
              (pairedMarkovParam (latent := latent) (obs := obs) θ)
              ((Fintype.equivFin (PairState latent obs)) (x₀, y₀)) : ℝ≥0∞)) =
            (initProb (k := latent) θ.latentParam x₀ : ℝ≥0∞) *
              (emissionProb θ x₀ y₀ : ℝ≥0∞) := by
        exact_mod_cast pairedInitProb_eq (latent := latent) (obs := obs) θ x₀ y₀
      rw [hpair, hxs, hys]
      simp [Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.wordProb,
        Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.wordProbNN,
        observationWeight_cons, pairedWordProbAux_eq (θ := θ) n x₀ y₀ xsTail ysTail,
        x₀, y₀, xsTail, ysTail, mul_assoc, mul_left_comm, mul_comm]

theorem observedSequenceMeasure_cylinder_eq_observedWordProb
    (θ : FiniteHMMParam latent obs) :
    ∀ ys : List (Fin obs),
      observedSequenceMeasure (latent := latent) (obs := obs) θ
          (Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder (k := obs) ys) =
        observedWordProb θ ys := by
  classical
  refine List.ofFnRec ?_
  intro n ys
  let s :=
    matchingPairedPrefixFinset (latent := latent) (obs := obs) (List.ofFn ys)
  rw [observedSequenceMeasure, Measure.map_apply
    (measurable_observationSequenceOfPairedTrajectory (latent := latent) (obs := obs))
    (measurableSet_cylinder (obs := obs) (List.ofFn ys))]
  rw [preimage_observedCylinder_eq_preimage_matchingPairedPrefixFinset
    (latent := latent) (obs := obs) (List.ofFn ys)]
  rw [← sum_measure_preimage_singleton
    (μ := pairedSequenceMeasure (latent := latent) (obs := obs) θ)
    (s := s) (f := pairedPrefixMap (latent := latent) (obs := obs) (List.ofFn ys).length)]
  · trans
      ∑ p ∈ s,
        wordProb (k := Fintype.card (PairState latent obs))
          (pairedMarkovParam (latent := latent) (obs := obs) θ) (List.ofFn p)
    · apply Finset.sum_congr rfl
      intro p hp
      rw [pairedPrefixMap_preimage_singleton_eq_cylinder_ofFn (latent := latent) (obs := obs) p]
      rw [pairedSequenceMeasure]
      exact
        Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSequenceKernel.markovSequenceMeasure_cylinder_eq_wordProb
          (k := Fintype.card (PairState latent obs))
          (θ := pairedMarkovParam (latent := latent) (obs := obs) θ)
          (List.ofFn p)
    · unfold s matchingPairedPrefixFinset
      rw [Finset.sum_image]
      · trans
          ∑ xs : Fin (List.ofFn ys).length → Fin latent,
            wordProb (k := latent) θ.latentParam (List.ofFn xs) *
              observationWeight θ (List.ofFn xs) (List.ofFn ys)
        · refine Finset.sum_congr rfl ?_
          intro xs hx
          have hpairList :
              List.ofFn (pairedWordOfLatentPrefix (latent := latent) (obs := obs) (List.ofFn ys) xs) =
                List.ofFn (fun i =>
                  (Fintype.equivFin (PairState latent obs))
                    (xs i, ys (Fin.cast (by simp) i))) := by
            apply List.ext_get
            · simp
            · intro i hi₁ hi₂
              rw [List.get_ofFn, List.get_ofFn]
              simp [pairedWordOfLatentPrefix]
          calc
            wordProb (k := Fintype.card (PairState latent obs))
                (pairedMarkovParam (latent := latent) (obs := obs) θ)
                (List.ofFn
                  (pairedWordOfLatentPrefix (latent := latent) (obs := obs) (List.ofFn ys) xs)) =
              wordProb (k := Fintype.card (PairState latent obs))
                (pairedMarkovParam (latent := latent) (obs := obs) θ)
                (List.ofFn
                  (fun i =>
                    (Fintype.equivFin (PairState latent obs))
                      (xs i, ys (Fin.cast (by simp) i)))) := by
                    exact congrArg
                      (wordProb (k := Fintype.card (PairState latent obs))
                        (pairedMarkovParam (latent := latent) (obs := obs) θ))
                      hpairList
            _ =
              wordProb (k := latent) θ.latentParam (List.ofFn xs) *
                observationWeight θ (List.ofFn xs) (List.ofFn ys) := by
                  simpa using
                    pairedWordProb_eq (latent := latent) (obs := obs) θ
                      (List.ofFn ys).length xs (fun i => ys (Fin.cast (by simp) i))
        · simp [observedWordProb]
      · intro xs _ x's _ hxxs
        exact pairedWordOfLatentPrefix_injective
          (latent := latent) (obs := obs) (List.ofFn ys) hxxs
  · intro p hp
    exact (measurable_pairedPrefixMap (latent := latent) (obs := obs) (List.ofFn ys).length)
      (measurableSet_singleton p)

/-- The emission kernel as an explicit finite kernel. This is the honest HMM
surface we need before any learning/inference algorithmics. -/
noncomputable def emissionKernel (θ : FiniteHMMParam latent obs) :
    Kernel (Fin latent) (Fin obs) :=
  Kernel.ofFunOfCountable (fun x => (θ.emission x : Measure (Fin obs)))

instance emissionKernel_isMarkov (θ : FiniteHMMParam latent obs) :
    IsMarkovKernel (emissionKernel θ) := by
  refine ⟨?_⟩
  intro x
  change IsProbabilityMeasure (((θ.emission x : ProbabilityMeasure (Fin obs)) : Measure (Fin obs)))
  infer_instance

end FiniteHiddenMarkovModel

end Mettapedia.ProbabilityTheory.HiddenMarkovModels
