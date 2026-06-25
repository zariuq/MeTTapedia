import Mettapedia.CategoryTheory.DeFinettiMarkovGiryBridge
import Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHigherOrder
import Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Higher-Order Markov Bridge to the Borel/Giry Layer

This file lifts the proved higher-order raw-cylinder theorem into the existing
Borel `ProbMarkov` bridge by reducing order-`m` chains to ordinary first-order
chains on finite context states.

We keep the boundary explicit:

* the mediator lives on ordinary Borel `MarkovParam` objects for encoded
  contexts;
* the higher-order raw-word law is recovered by evaluating those context-state
  mediators on the canonical context path of the raw word;
* no measurable-space structure on `HigherOrderMarkovParam` itself is claimed
  here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open MeasureTheory
open Mettapedia.ProbabilityTheory.Exchangeability
open Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard
open Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHigherOrder
open Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet
open scoped BigOperators ENNReal NNReal

variable {k m : ℕ} [Fact (0 < m)]
variable {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)}

/-- The ordinary finite Markov state count obtained by encoding length-`m`
contexts over `Fin k`. -/
abbrev HigherOrderContextCard (k m : ℕ) : ℕ :=
  Fintype.card (Context k m)

local instance instMeasurableSpaceHigherOrderContextParam :
    MeasurableSpace (MarkovParam (HigherOrderContextCard k m)) :=
  MarkovParam.borelMS (k := HigherOrderContextCard k m)
local instance instBorelSpaceHigherOrderContextParam :
    BorelSpace (MarkovParam (HigherOrderContextCard k m)) := ⟨rfl⟩

/-- The encoded context path associated to a long raw word. -/
def higherOrderEncodedContextWord
    (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    List (Fin (HigherOrderContextCard k m)) :=
  (contextPathOfWord (k := k) (m := m) xs hxs).map
    (Fintype.equivFin (Context k m))

/-- Borel/Giry long-word weight of a raw word, computed by integrating the
ordinary context-state sequence kernel over a Borel probability law on encoded
context-state Markov parameters. -/
def higherOrderLongWordWeightViaProbMarkov
    (π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m))
    (xs : List (Fin k)) (hxs : m ≤ xs.length) : ℝ≥0∞ :=
  borelMarkovCylinderWeightViaProbMarkov (k := HigherOrderContextCard k m) π
    (higherOrderEncodedContextWord (k := k) (m := m) xs hxs)

section WeightLemmas

variable {k m : ℕ}

/-- The higher-order Borel/Giry long-word weight is exactly the ordinary moment
map on the encoded context path. -/
theorem higherOrderLongWordWeightViaProbMarkov_eq_momentMapWord
    (π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m))
    (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    higherOrderLongWordWeightViaProbMarkov (k := k) (m := m) π xs hxs =
      Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.momentMapWord
        (k := HigherOrderContextCard k m)
        (higherOrderEncodedContextWord (k := k) (m := m) xs hxs) π :=
  borelMarkovCylinderWeightViaProbMarkov_eq_momentMapWord
    (k := HigherOrderContextCard k m) π
    (higherOrderEncodedContextWord (k := k) (m := m) xs hxs)

end WeightLemmas

/-- Honest Borel-side higher-order factorization: a prefix law on raw words is
recovered on all words of length at least `m` by integrating the ordinary
context-state cylinder weights over a Borel law on encoded context-state
parameters. -/
def CategoricalBorelHigherOrderLongWordFactorization
    (k m : ℕ) [Fact (0 < m)]
    (μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m),
    ∀ xs : List (Fin k), ∀ hxs : m ≤ xs.length,
      μ xs = higherOrderLongWordWeightViaProbMarkov (k := k) (m := m) π xs hxs

/-- Public Borel-side mixture object for the higher-order long-word surface. -/
structure BorelHigherOrderLongWordMixture
    (k m : ℕ) [Fact (0 < m)]
    (μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) where
  mixingLaw : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m)
  represents :
    ∀ xs : List (Fin k), ∀ hxs : m ≤ xs.length,
      μ xs = higherOrderLongWordWeightViaProbMarkov (k := k) (m := m) mixingLaw xs hxs

namespace BorelHigherOrderLongWordMixture

/-- Any higher-order Borel-side mixture witness yields the corresponding
long-word factorization package. -/
theorem categoricalBorelHigherOrderLongWordFactorization_of_borelHigherOrderLongWordMixture
    (M : BorelHigherOrderLongWordMixture k m μ) :
    CategoricalBorelHigherOrderLongWordFactorization k m μ :=
  ⟨M.mixingLaw, M.represents⟩

/-- Consumer API: build the higher-order Borel mixture witness from the
factorization package. -/
noncomputable def ofCategoricalBorelFactorization
    (hfac : CategoricalBorelHigherOrderLongWordFactorization k m μ) :
    BorelHigherOrderLongWordMixture k m μ := by
  exact ⟨Classical.choose hfac, Classical.choose_spec hfac⟩

/-- The higher-order Borel long-word factorization package is equivalent to
having the public higher-order Borel mixture witness. -/
theorem categoricalBorelHigherOrderLongWordFactorization_iff_nonempty_borelHigherOrderLongWordMixture :
    CategoricalBorelHigherOrderLongWordFactorization k m μ ↔
      Nonempty (BorelHigherOrderLongWordMixture k m μ) := by
  constructor
  · intro hfac
    exact ⟨ofCategoricalBorelFactorization (k := k) (m := m) (μ := μ) hfac⟩
  · rintro ⟨M⟩
    exact
      categoricalBorelHigherOrderLongWordFactorization_of_borelHigherOrderLongWordMixture
        (k := k) (m := m) (μ := μ) M

end BorelHigherOrderLongWordMixture

section DiracFactorization

variable {k m : ℕ}

/-- The higher-order raw long-word law of a fixed parameter is recovered by the
Dirac Borel law concentrated at its reduced context-state Markov parameter. -/
theorem higherOrderLongWordWeightViaProbMarkov_dirac_eq_longWordProb
    (θ : HigherOrderMarkovParam k m) (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    higherOrderLongWordWeightViaProbMarkov (k := k) (m := m)
        ((MeasureTheory.diracProba
          (toMarkovParam (k := k) (m := m) θ)) :
            Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov
              (HigherOrderContextCard k m))
        xs hxs =
      longWordProb (k := k) (m := m) θ xs hxs := by
  rw [higherOrderLongWordWeightViaProbMarkov_eq_momentMapWord (k := k) (m := m)
    (π := ((MeasureTheory.diracProba
      (toMarkovParam (k := k) (m := m) θ)) :
        Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov
          (HigherOrderContextCard k m))) xs hxs]
  rw [Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.momentMapWord]
  change
    ∫⁻ θ' : MarkovParam (HigherOrderContextCard k m),
        MarkovDeFinettiHard.wordProb θ' (higherOrderEncodedContextWord (k := k) (m := m) xs hxs)
          ∂(Measure.dirac (toMarkovParam (k := k) (m := m) θ)) =
      longWordProb (k := k) (m := m) θ xs hxs
  rw [lintegral_dirac]
  simp [higherOrderEncodedContextWord, longWordProb, contextWordProb]

end DiracFactorization

/-- Dirac witness: every fixed higher-order parameter gives a degenerate Borel
long-word factorization by concentrating the law at its reduced context-state
Markov parameter. This is the honest trivial direction, not a full de Finetti
mixture theorem. -/
theorem borelHigherOrderLongWordFactorization_diracWitness
    (θ : HigherOrderMarkovParam k m) :
    ∃ π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m),
      ∀ xs : List (Fin k), ∀ hxs : m ≤ xs.length,
        higherOrderSequenceMeasure (k := k) (m := m) θ
            (MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
          higherOrderLongWordWeightViaProbMarkov (k := k) (m := m) π xs hxs := by
  refine ⟨((MeasureTheory.diracProba
    (toMarkovParam (k := k) (m := m) θ)) :
      Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov
        (HigherOrderContextCard k m)), ?_⟩
  intro xs hxs
  rw [higherOrderLongWordWeightViaProbMarkov_dirac_eq_longWordProb
    (k := k) (m := m) θ xs hxs]
  exact higherOrderSequenceMeasure_cylinder_eq_longWordProb
    (k := k) (m := m) θ xs hxs

/-- Legacy alias for the Dirac witness theorem. The stronger de Finetti-facing
image theorem remains future work. -/
@[deprecated borelHigherOrderLongWordFactorization_diracWitness (since := "2026-04-16")]
theorem exists_borelHigherOrderLongWordFactorization_of_param
    (θ : HigherOrderMarkovParam k m) :
    ∃ π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m),
      ∀ xs : List (Fin k), ∀ hxs : m ≤ xs.length,
        higherOrderSequenceMeasure (k := k) (m := m) θ
            (MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
          higherOrderLongWordWeightViaProbMarkov (k := k) (m := m) π xs hxs :=
  borelHigherOrderLongWordFactorization_diracWitness (k := k) (m := m) θ

section FiniteDiscreteMixtures

variable {n : ℕ}

local instance instHigherOrderFiniteDiscreteMixtureIndexMeasurableSpace :
    MeasurableSpace (Fin n) := ⊤
local instance instHigherOrderFiniteDiscreteMixtureIndexMeasurableSingletonClass :
    MeasurableSingletonClass (Fin n) := ⟨fun _ => by simp⟩

/-- Prefix-measure surface carried by a genuine higher-order parameter, defined
by its raw sequence law on cylinders. -/
noncomputable def higherOrderCylinderPrefixMeasure
    (θ : HigherOrderMarkovParam k m) :
    PrefixMeasure (Fin k) where
  toFun xs :=
    higherOrderSequenceMeasure (k := k) (m := m) θ
      (MarkovDeFinettiRecurrence.cylinder (k := k) xs)
  root_eq_one' := by
    haveI :
        IsProbabilityMeasure
          (higherOrderSequenceMeasure (k := k) (m := m) θ) := by
      unfold MarkovDeFinettiHigherOrder.higherOrderSequenceMeasure
      haveI :
          IsProbabilityMeasure
            (MarkovDeFinettiHigherOrder.contextSequenceMeasure (k := k) (m := m) θ) := by
        unfold MarkovDeFinettiHigherOrder.contextSequenceMeasure
        haveI :
            IsProbabilityMeasure
              (MarkovDeFinettiHigherOrder.encodedContextSequenceMeasure (k := k) (m := m) θ) :=
          MarkovDeFinettiSequenceKernel.markovSequenceMeasure_isProbability
            (k := Fintype.card (Context k m))
            (θ := toMarkovParam (k := k) (m := m) θ)
        exact Measure.isProbabilityMeasure_map
          (MarkovDeFinettiHigherOrder.measurable_decodeContextSeq (k := k) (m := m)).aemeasurable
      exact Measure.isProbabilityMeasure_map
        (MarkovDeFinettiHigherOrder.measurable_symbolSequenceOfContextTrajectory
          (k := k) (m := m)).aemeasurable
    rw [show MarkovDeFinettiRecurrence.cylinder (k := k) [] = Set.univ by
      ext ω
      simp [MarkovDeFinettiRecurrence.cylinder]]
    exact (measure_univ : higherOrderSequenceMeasure (k := k) (m := m) θ Set.univ = 1)
  additive' := by
    classical
    intro x
    have hpart :
        MarkovDeFinettiRecurrence.cylinder (k := k) x =
          ⋃ a ∈ (Finset.univ : Finset (Fin k)),
            MarkovDeFinettiRecurrence.cylinder (k := k) (x ++ [a]) := by
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
            have hlt : j.1 < x.length + 1 := by
              simpa using j.2
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
        ∀ a ∈ (Finset.univ : Finset (Fin k)),
          MeasurableSet (MarkovDeFinettiRecurrence.cylinder (k := k) (x ++ [a])) := by
      intro a _
      exact measurableSet_markovCylinder (k := k) (x ++ [a])
    have hdisj :
        ∀ a ∈ (Finset.univ : Finset (Fin k)),
          ∀ b ∈ (Finset.univ : Finset (Fin k)), a ≠ b →
            Disjoint
              (MarkovDeFinettiRecurrence.cylinder (k := k) (x ++ [a]))
              (MarkovDeFinettiRecurrence.cylinder (k := k) (x ++ [b])) := by
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
      (∑ a : Fin k,
          higherOrderSequenceMeasure (k := k) (m := m) θ
            (MarkovDeFinettiRecurrence.cylinder (k := k) (x ++ [a]))) =
        Finset.sum (Finset.univ : Finset (Fin k)) (fun a : Fin k =>
          higherOrderSequenceMeasure (k := k) (m := m) θ
            (MarkovDeFinettiRecurrence.cylinder (k := k) (x ++ [a]))) := by
              simp
      _ =
        higherOrderSequenceMeasure (k := k) (m := m) θ
          (⋃ a ∈ (Finset.univ : Finset (Fin k)),
            MarkovDeFinettiRecurrence.cylinder (k := k) (x ++ [a])) := by
              symm
              exact measure_biUnion_finset (μ := higherOrderSequenceMeasure (k := k) (m := m) θ)
                (s := Finset.univ)
                (f := fun a : Fin k =>
                  MarkovDeFinettiRecurrence.cylinder (k := k) (x ++ [a]))
                hdisj
                hmeas
      _ =
        higherOrderSequenceMeasure (k := k) (m := m) θ
          (MarkovDeFinettiRecurrence.cylinder (k := k) x) := by
              rw [hpart]

/-- Finite discrete law on higher-order parameters, pushed forward to the
encoded context-state parameter space. This is the first honest non-Dirac
mixture surface for the higher-order bridge. -/
noncomputable def finiteHigherOrderEncodedMixingLaw
    (w : Fin n → ℝ≥0∞) (hw : ∑ i : Fin n, w i = 1)
    (Θ : Fin n → HigherOrderMarkovParam k m) :
    Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m) :=
  let p : PMF (Fin n) := PMF.ofFintype w (by simpa using hw)
  let μ : ProbabilityMeasure (Fin n) := ⟨p.toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩
  let g : Fin n → MarkovParam (HigherOrderContextCard k m) :=
    fun i => toMarkovParam (k := k) (m := m) (Θ i)
  let hg : Measurable g := measurable_of_finite g
  μ.map hg.aemeasurable

/-- The long-word weight of the encoded finite discrete mixture is exactly the
weighted sum of the component higher-order long-word probabilities. -/
theorem higherOrderLongWordWeightViaProbMarkov_eq_finiteDiracMixture
    (w : Fin n → ℝ≥0∞) (hw : ∑ i : Fin n, w i = 1)
    (Θ : Fin n → HigherOrderMarkovParam k m)
    (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    higherOrderLongWordWeightViaProbMarkov (k := k) (m := m)
        (finiteHigherOrderEncodedMixingLaw (k := k) (m := m) w hw Θ) xs hxs =
      ∑ i : Fin n, w i * longWordProb (k := k) (m := m) (Θ i) xs hxs := by
  classical
  let _hmpos : 0 < m := Fact.out
  let p : PMF (Fin n) := PMF.ofFintype w (by simpa using hw)
  let μ : ProbabilityMeasure (Fin n) := ⟨p.toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩
  let g : Fin n → MarkovParam (HigherOrderContextCard k m) :=
    fun i => toMarkovParam (k := k) (m := m) (Θ i)
  let hg : Measurable g := measurable_of_finite g
  rw [higherOrderLongWordWeightViaProbMarkov_eq_momentMapWord (k := k) (m := m)
    (π := finiteHigherOrderEncodedMixingLaw (k := k) (m := m) w hw Θ) xs hxs]
  dsimp [finiteHigherOrderEncodedMixingLaw]
  rw [Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.momentMapWord]
  have hwordMeas :
      Measurable
        (fun θ : MarkovParam (HigherOrderContextCard k m) =>
          MarkovDeFinettiHard.wordProb θ
            (higherOrderEncodedContextWord (k := k) (m := m) xs hxs)) :=
    by
      simpa using
        (measurable_wordProb_borel
          (k := HigherOrderContextCard k m)
          (higherOrderEncodedContextWord (k := k) (m := m) xs hxs))
  have hwordAemeas :
      AEMeasurable
        (fun θ : MarkovParam (HigherOrderContextCard k m) =>
          MarkovDeFinettiHard.wordProb θ
            (higherOrderEncodedContextWord (k := k) (m := m) xs hxs))
        (((finiteHigherOrderEncodedMixingLaw (k := k) (m := m) w hw Θ) :
            Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m)) :
          Measure (MarkovParam (HigherOrderContextCard k m))) :=
    hwordMeas.aemeasurable
  have hmap := MeasureTheory.lintegral_map'
      (μ := (μ : Measure (Fin n)))
      (f := fun θ : MarkovParam (HigherOrderContextCard k m) =>
        MarkovDeFinettiHard.wordProb θ
          (higherOrderEncodedContextWord (k := k) (m := m) xs hxs))
      (g := g)
      hwordAemeas
      hg.aemeasurable
  calc
    ∫⁻ θ : MarkovParam (HigherOrderContextCard k m),
        MarkovDeFinettiHard.wordProb θ
          (higherOrderEncodedContextWord (k := k) (m := m) xs hxs)
          ∂(((finiteHigherOrderEncodedMixingLaw (k := k) (m := m) w hw Θ) :
              Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m)) :
            Measure (MarkovParam (HigherOrderContextCard k m))) =
      ∫⁻ i : Fin n,
        MarkovDeFinettiHard.wordProb (g i)
          (higherOrderEncodedContextWord (k := k) (m := m) xs hxs)
          ∂(μ : Measure (Fin n)) := by
            simpa [finiteHigherOrderEncodedMixingLaw, p, μ, g, hg] using hmap
    _ =
      ∑ i : Fin n,
        ((μ : Measure (Fin n)) {i}) *
          MarkovDeFinettiHard.wordProb (g i)
            (higherOrderEncodedContextWord (k := k) (m := m) xs hxs) := by
              rw [MeasureTheory.lintegral_fintype
                (μ := (μ : Measure (Fin n)))
                (f := fun i : Fin n =>
                  MarkovDeFinettiHard.wordProb (g i)
                    (higherOrderEncodedContextWord (k := k) (m := m) xs hxs))]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [mul_comm]
    _ =
      ∑ i : Fin n, w i * longWordProb (k := k) (m := m) (Θ i) xs hxs := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hsingleton :
            ((μ : Measure (Fin n)) {i}) = w i := by
          dsimp [μ, p]
          rw [PMF.toMeasure_apply_singleton (p := PMF.ofFintype w (by simpa using hw))
            i (MeasurableSet.singleton i)]
          simp [PMF.ofFintype]
        rw [hsingleton]
        simp [g, higherOrderEncodedContextWord, longWordProb, contextWordProb]

/-- Finite discrete higher-order mixtures yield an honest higher-order long-word
factorization package, not just a Dirac witness. -/
theorem categoricalBorelHigherOrderLongWordFactorization_of_finiteDiscreteMixture
    (w : Fin n → ℝ≥0∞) (hw : ∑ i : Fin n, w i = 1)
    (Θ : Fin n → HigherOrderMarkovParam k m) :
    CategoricalBorelHigherOrderLongWordFactorization k m
      (xiPrefixMeasure
        (ν := fun i : Fin n => higherOrderCylinderPrefixMeasure (k := k) (m := m) (Θ i))
        (w := w)
        (hw := by
          simpa [tsum_fintype] using hw)
      ) := by
  refine ⟨finiteHigherOrderEncodedMixingLaw (k := k) (m := m) w hw Θ, ?_⟩
  intro xs hxs
  unfold xiPrefixMeasure xiFun
  simp only [PrefixMeasure.toSemimeasure_apply]
  calc
    ∑' i : Fin n, w i * higherOrderCylinderPrefixMeasure (k := k) (m := m) (Θ i) xs =
        ∑ i : Fin n, w i *
          higherOrderSequenceMeasure (k := k) (m := m) (Θ i)
            (MarkovDeFinettiRecurrence.cylinder (k := k) xs) := by
              simp [higherOrderCylinderPrefixMeasure, tsum_fintype]
    _ =
        ∑ i : Fin n, w i * longWordProb (k := k) (m := m) (Θ i) xs hxs := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [higherOrderSequenceMeasure_cylinder_eq_longWordProb
                (k := k) (m := m) (Θ i) xs hxs]
    _ =
        higherOrderLongWordWeightViaProbMarkov (k := k) (m := m)
          (finiteHigherOrderEncodedMixingLaw (k := k) (m := m) w hw Θ) xs hxs := by
              symm
              exact higherOrderLongWordWeightViaProbMarkov_eq_finiteDiracMixture
                (k := k) (m := m) w hw Θ xs hxs

end FiniteDiscreteMixtures

end Mettapedia.CategoryTheory
