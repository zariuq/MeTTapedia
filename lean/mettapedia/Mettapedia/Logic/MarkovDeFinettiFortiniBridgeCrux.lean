import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCore

/-!
# Markov de Finetti Fortini Bridge: Crux Layer (Internal)

This module contains internal proof plumbing, staging interfaces, and
compatibility surfaces accumulated during the Fortini development.

For canonical theorem work, import:
`Mettapedia.Logic.MarkovDeFinettiFortiniBridge`
or `Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCanonical`.
-/

noncomputable section

namespace Mettapedia.Logic

open MeasureTheory
open Filter
open scoped BigOperators

namespace MarkovDeFinettiHard

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovExchangeability
open Mettapedia.Logic.MarkovDeFinettiRecurrence

variable {k : ℕ}

def rowKernelStepProd
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (ω : ℕ → Fin k) : List (Fin k) → ENNReal
  | [] => 1
  | [_] => 1
  | a :: b :: xs =>
      (rowKernel a (rowSuccessorVisitProcess (k := k) a ω) ({b} : Set (Fin k))) *
        rowKernelStepProd rowKernel ω (b :: xs)

/-- AE-measurability of `rowKernelStepProd` on path space from singleton-eval
AE-measurability for the row-kernel family. -/
lemma aemeasurable_rowKernelStepProd
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i)) :
    ∀ xs : List (Fin k),
      AEMeasurable (fun ω : ℕ → Fin k => rowKernelStepProd (k := k) rowKernel ω xs) P := by
  intro xs
  induction xs with
  | nil =>
      simp [rowKernelStepProd]
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [rowKernelStepProd]
      | cons b tail =>
          have hfactor :
              AEMeasurable
                (fun ω : ℕ → Fin k =>
                  (rowKernel a (rowSuccessorVisitProcess (k := k) a ω) : Measure (Fin k))
                    ({b} : Set (Fin k))) P :=
            (hEval a b).comp_measurable (measurable_rowSuccessorVisitProcess (k := k) a)
          have htail :
              AEMeasurable
                (fun ω : ℕ → Fin k =>
                  rowKernelStepProd (k := k) rowKernel ω (b :: tail)) P := by
            simpa using ih
          simpa [rowKernelStepProd] using hfactor.mul htail

/-- The step-product is uniformly bounded by `1`. -/
lemma rowKernelStepProd_le_one
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (ω : ℕ → Fin k) :
    ∀ xs : List (Fin k), rowKernelStepProd (k := k) rowKernel ω xs ≤ 1 := by
  intro xs
  induction xs with
  | nil =>
      simp [rowKernelStepProd]
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [rowKernelStepProd]
      | cons b tail =>
          have hfactor :
              (rowKernel a (rowSuccessorVisitProcess (k := k) a ω) : Measure (Fin k))
                ({b} : Set (Fin k)) ≤ 1 := by
            calc
              (rowKernel a (rowSuccessorVisitProcess (k := k) a ω) : Measure (Fin k))
                  ({b} : Set (Fin k))
                  ≤
                (rowKernel a (rowSuccessorVisitProcess (k := k) a ω) : Measure (Fin k))
                  Set.univ :=
                    measure_mono (Set.subset_univ _)
              _ = 1 := by simp
          have htail :
              rowKernelStepProd (k := k) rowKernel ω (b :: tail) ≤ 1 := by
            simpa using ih
          calc
            rowKernelStepProd (k := k) rowKernel ω (a :: b :: tail)
                =
              (rowKernel a (rowSuccessorVisitProcess (k := k) a ω) : Measure (Fin k))
                  ({b} : Set (Fin k)) *
                  rowKernelStepProd (k := k) rowKernel ω (b :: tail) := by
                    simp [rowKernelStepProd]
            _ 
                ≤ 1 * 1 := by
                    exact mul_le_mul' hfactor htail
            _ = 1 := by simp

/-- The real-valued step-product is integrable on any probability law. -/
lemma integrable_rowKernelStepProd_toReal
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (xs : List (Fin k)) :
    Integrable (fun ω : ℕ → Fin k => (rowKernelStepProd (k := k) rowKernel ω xs).toReal) P := by
  have hmeas :
      AEMeasurable
        (fun ω : ℕ → Fin k => (rowKernelStepProd (k := k) rowKernel ω xs).toReal) P :=
    (aemeasurable_rowKernelStepProd (k := k) P rowKernel hEval xs).ennreal_toReal
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
  refine ae_of_all P ?_
  intro ω
  have hnonneg : 0 ≤ (rowKernelStepProd (k := k) rowKernel ω xs).toReal :=
    ENNReal.toReal_nonneg
  have hle :
      (rowKernelStepProd (k := k) rowKernel ω xs).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (by simpa using rowKernelStepProd_le_one (k := k) rowKernel ω xs)
  simp [Real.norm_eq_abs, abs_of_nonneg hnonneg, hle]

/-- AE-measurability of the start-indicator integrand form used in cross-anchor
identities. -/
lemma aemeasurable_startIndicator_rowKernelStepProd
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (a : Fin k) (xs : List (Fin k)) :
    AEMeasurable
      (fun ω : ℕ → Fin k =>
        if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω xs else 0) P := by
  have hprod :
      AEMeasurable
        (fun ω : ℕ → Fin k => rowKernelStepProd (k := k) rowKernel ω xs) P :=
    aemeasurable_rowKernelStepProd (k := k) P rowKernel hEval xs
  have hind :
      AEMeasurable
        ({ω : ℕ → Fin k | ω 0 = a}.indicator
          (fun ω : ℕ → Fin k => rowKernelStepProd (k := k) rowKernel ω xs)) P :=
    hprod.indicator (show MeasurableSet {ω : ℕ → Fin k | ω 0 = a} from by
      change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' Set.singleton a)
      exact (measurable_pi_apply 0) (MeasurableSet.singleton a))
  refine hind.congr ?_
  filter_upwards with ω
  by_cases hω : ω 0 = a <;> simp [Set.indicator, hω]

/-- Rewrite the start-indicator step-product integral as an integral over the
start-restricted law. -/
lemma lintegral_startIndicator_rowKernelStepProd_eq_restrict
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k)) :
    ∫⁻ ω,
      (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0) ∂P
      =
    ∫⁻ ω, rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs)
      ∂(P.restrict {ω : ℕ → Fin k | ω 0 = a}) := by
  let s : Set (ℕ → Fin k) := {ω : ℕ → Fin k | ω 0 = a}
  have hs : MeasurableSet s := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' Set.singleton a)
    exact (measurable_pi_apply 0) (MeasurableSet.singleton a)
  calc
    ∫⁻ ω,
      (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0) ∂P
        = ∫⁻ ω, s.indicator
            (fun ω => rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs)) ω ∂P := by
              refine lintegral_congr_ae ?_
              filter_upwards with ω
              by_cases hω : ω 0 = a <;> simp [s, Set.indicator, hω]
    _ = ∫⁻ ω in s, rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) ∂P := by
          exact lintegral_indicator hs _
    _ =
      ∫⁻ ω, rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs)
        ∂(P.restrict {ω : ℕ → Fin k | ω 0 = a}) := by
          simp [s]

/-- Restricted-space form of the cons decomposition for start-indicator
step-product integrals. -/
lemma lintegral_startIndicator_rowKernelStepProd_cons_eq_restrict
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k)) :
    ∫⁻ ω,
      (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0) ∂P
      =
    ∫⁻ ω,
      (rowKernel a (rowSuccessorVisitProcess (k := k) a ω) : Measure (Fin k)) ({b} : Set (Fin k)) *
        rowKernelStepProd (k := k) rowKernel ω (b :: xs)
      ∂(P.restrict {ω : ℕ → Fin k | ω 0 = a}) := by
  calc
    ∫⁻ ω,
      (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0) ∂P
        =
      ∫⁻ ω, rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs)
        ∂(P.restrict {ω : ℕ → Fin k | ω 0 = a}) :=
      lintegral_startIndicator_rowKernelStepProd_eq_restrict (k := k) P rowKernel a b xs
    _ =
      ∫⁻ ω,
        (rowKernel a (rowSuccessorVisitProcess (k := k) a ω) : Measure (Fin k)) ({b} : Set (Fin k)) *
          rowKernelStepProd (k := k) rowKernel ω (b :: xs)
        ∂(P.restrict {ω : ℕ → Fin k | ω 0 = a}) := by
          refine lintegral_congr_ae ?_
          filter_upwards with ω
          simp [rowKernelStepProd]

/-- Cross-anchor product identity (explicit integrand form).

This is the *missing joint-law hypothesis*: it asserts that for every finite
prefix `xs` of length ≥ 2, the cylinder probability under `P` equals the
integral of the row-kernel product with the explicit start-state indicator.

This isolates the true mathematical crux: cross-anchor conditional independence. -/
def CrossAnchorProductIdentity
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) : Prop :=
  ∀ (a b : Fin k) (xs : List (Fin k)),
    P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: xs)) =
      ∫⁻ ω,
        (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)
        ∂P

/-- P-level cylinder-wordProb mixing identity for prefixes of length ≥ 2.

This captures the cross-anchor conditional independence of row processes:
the cylinder probability under P equals the integral of wordProb evaluated
at the rowKernelToMarkovParam construction.

**Mathematical content**: Given the directing row kernels, the
row-successor processes across distinct anchors are conditionally independent.
This is NOT implied by per-anchor ConditionallyIID alone, which gives only
single-anchor marginals. -/
def CylinderMixingIdentity_P
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) : Prop :=
  ∀ (xs : List (Fin k)), xs.length ≥ 2 →
    P (MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
      ∫⁻ ω, wordProb (k := k)
        (rowKernelToMarkovParam (k := k)
          (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
          (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) xs ∂P

/-- For a nontrivial prefix, `wordProb` at the row-kernel Markov parameter is
the start-indicator times the explicit row-kernel product. -/
lemma wordProbAux_rowKernelToMarkovParam_eq_stepProd
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (ω : ℕ → Fin k) :
    ∀ (a : Fin k) (xs : List (Fin k)),
      (wordProbAux (k := k)
          (rowKernelToMarkovParam_diracInit (k := k)
            (rowKernel := liftedRowKernelFromRowProcess (k := k) rowKernel) ω)
          a xs : ENNReal)
        =
        rowKernelStepProd (k := k) rowKernel ω (a :: xs) := by
  intro a xs
  induction xs generalizing a with
  | nil =>
    simp [wordProbAux, rowKernelStepProd]
  | cons b xs ih =>
    have ih' := ih (a := b)
    simp [wordProbAux, rowKernelStepProd,
      stepProb_rowKernelToMarkovParam_diracInit_lifted_eq, ih', Set.singleton]

lemma wordProb_rowKernelToMarkovParam_eq_indicator_stepProd
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (ω : ℕ → Fin k) (a b : Fin k) (xs : List (Fin k)) :
    wordProb (k := k)
        (rowKernelToMarkovParam (k := k)
          (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
          (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) (a :: b :: xs)
      =
      (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0) := by
  by_cases hstart : ω 0 = a
  · have hmem : a ∈ (Set.singleton a : Set (Fin k)) := Set.mem_singleton a
    have haux :=
      wordProbAux_rowKernelToMarkovParam_eq_stepProd (k := k) rowKernel ω a (b :: xs)
    -- rewrite the auxiliary lemma using the start equality
    have haux' :
        (wordProbAux (k := k)
            { init := ⟨Measure.dirac a, Measure.dirac.isProbabilityMeasure⟩
              trans := fun i => liftedRowKernelFromRowProcess (k := k) rowKernel i ω }
            a (b :: xs) : ENNReal)
          =
          rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) := by
      simpa [rowKernelToMarkovParam_diracInit, rowKernelToMarkovParam, hstart] using haux
    simp [rowKernelToMarkovParam, wordProb, wordProbNN, initProb, hstart, hmem, haux']
  · have hnotmem : ω 0 ∉ (Set.singleton a : Set (Fin k)) := by
      intro hmem
      exact hstart hmem
    simp [rowKernelToMarkovParam, wordProb, wordProbNN, initProb, hstart, hnotmem]

/-- Cross-anchor product identity implies the cylinder mixing identity. -/
theorem cylinderMixingIdentity_P_of_crossAnchorProductIdentity
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hcross : CrossAnchorProductIdentity (k := k) P rowKernel) :
    CylinderMixingIdentity_P (k := k) P rowKernel := by
  intro xs hlen
  cases xs with
  | nil => cases (Nat.not_succ_le_zero 1 hlen)
  | cons a xs =>
    cases xs with
    | nil =>
      cases (Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ hlen))
    | cons b rest =>
      specialize hcross a b rest
      refine hcross.trans ?_
      refine lintegral_congr_ae ?_
      filter_upwards with ω
      exact (wordProb_rowKernelToMarkovParam_eq_indicator_stepProd
        (k := k) rowKernel ω a b rest).symm

/-- Restricting the path-space measure only decreases each row-process law. -/
lemma rowProcessLaw_restrict_le
    (P : Measure (ℕ → Fin k)) (S : Set (ℕ → Fin k)) (i : Fin k) :
    rowProcessLaw (k := k) (P.restrict S) i ≤ rowProcessLaw (k := k) P i := by
  have hle : P.restrict S ≤ P := Measure.restrict_le_self
  have hmeas : AEMeasurable (rowSuccessorVisitProcess (k := k) i) P :=
    (measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable
  simpa [rowProcessLaw] using (Measure.map_mono_of_aemeasurable hle hmeas)

/-- Row-process law under restriction: explicit preimage form. -/
lemma rowProcessLaw_restrict_apply
    (P : Measure (ℕ → Fin k)) (S : Set (ℕ → Fin k)) (i : Fin k)
    {A : Set (ℕ → Fin k)} (hA : MeasurableSet A) :
    rowProcessLaw (k := k) (P.restrict S) i A =
      P (S ∩ (rowSuccessorVisitProcess (k := k) i) ⁻¹' A) := by
  have hmeas :
      MeasurableSet ((rowSuccessorVisitProcess (k := k) i) ⁻¹' A) :=
    (measurable_rowSuccessorVisitProcess (k := k) i) hA
  have hmap :
      rowProcessLaw (k := k) (P.restrict S) i A =
        (P.restrict S) ((rowSuccessorVisitProcess (k := k) i) ⁻¹' A) := by
    simpa [rowProcessLaw] using
      (Measure.map_apply (measurable_rowSuccessorVisitProcess (k := k) i) hA)
  have hrestrict :
      (P.restrict S) ((rowSuccessorVisitProcess (k := k) i) ⁻¹' A) =
        P (S ∩ (rowSuccessorVisitProcess (k := k) i) ⁻¹' A) := by
    simpa [Set.inter_comm] using
      (Measure.restrict_apply (μ := P) (s := S)
        (t := (rowSuccessorVisitProcess (k := k) i) ⁻¹' A) hmeas)
  exact hmap.trans hrestrict

/-- AEMeasurable row-kernel evaluations are preserved under restriction
of the path-space measure. -/
lemma aemeasurable_rowKernel_eval_of_rowProcessLaw_restrict
    (P : Measure (ℕ → Fin k)) (S : Set (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (i b : Fin k)
    (hEval :
      AEMeasurable
        (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
        (rowProcessLaw (k := k) P i)) :
    AEMeasurable
      (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
      (rowProcessLaw (k := k) (P.restrict S) i) := by
  exact hEval.mono_measure (rowProcessLaw_restrict_le (k := k) P S i)

/-- Derive `Fin 1` product-kernel AE-measurability on each start-restricted row law
from the corresponding global AE-measurability. -/
lemma hPi_restrict_of_hPi
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hPi :
      ∀ i : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) P i)) :
    ∀ (i a : Fin k),
      AEMeasurable
        (fun r : ℕ → Fin k =>
          Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i) := by
  intro i a
  exact (hPi i).mono_measure
    (rowProcessLaw_restrict_le (k := k) P {ω : ℕ → Fin k | ω 0 = a} i)

/-- Finite-state lift:
from AE-measurability of singleton evaluations, obtain AE-measurability of
evaluation on any measurable subset of `Fin k`. -/
lemma aemeasurable_rowKernel_eval_set_of_hEval_singletons
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i)) :
    ∀ i : Fin k, ∀ B : Set (Fin k), MeasurableSet B →
      AEMeasurable
        (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) B)
        (rowProcessLaw (k := k) P i) := by
  intro i B hB
  classical
  let s : Finset (Fin k) := B.toFinset
  have hs : (s : Set (Fin k)) = B := by
    simp [s]
  have hsum :
      (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) B) =
      (fun r : ℕ → Fin k =>
        ∑ b ∈ s, (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k))) := by
    funext r
    have hss :
        (∑ b ∈ s, (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          = (rowKernel i r : Measure (Fin k)) s := by
      simp [sum_measure_singleton]
    calc
      (rowKernel i r : Measure (Fin k)) B
          = (rowKernel i r : Measure (Fin k)) (s : Set (Fin k)) := by simp [hs]
      _ = ∑ b ∈ s, (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)) := hss.symm
  rw [hsum]
  exact s.aemeasurable_fun_sum (fun b hb => hEval i b)

/-- Finite-state measurable lift under completeness:
from singleton AE-measurability, obtain measurability of evaluation on any
measurable subset of `Fin k`. -/
lemma measurable_rowKernel_eval_set_of_hEval_singletons_of_complete
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hComplete : ∀ i : Fin k, (rowProcessLaw (k := k) P i).IsComplete) :
    ∀ i : Fin k, ∀ B : Set (Fin k), MeasurableSet B →
      Measurable (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) B) := by
  intro i B hB
  letI : (rowProcessLaw (k := k) P i).IsComplete := hComplete i
  have hAE :
      AEMeasurable
        (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) B)
        (rowProcessLaw (k := k) P i) :=
    aemeasurable_rowKernel_eval_set_of_hEval_singletons
      (k := k) P rowKernel hEval i B hB
  exact (aemeasurable_iff_measurable (μ := rowProcessLaw (k := k) P i)).1 hAE

/-- If all row-kernel evaluations are measurable (for measurable sets), then the
`Fin 1` product-kernel map is AE-measurable on each row-process law. This is a
clean helper to reduce explicit `hPi` assumptions once measurable-eval lemmas
are available. -/
lemma hPi_of_measurable_eval
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEvalAll :
      ∀ i : Fin k, ∀ B : Set (Fin k), MeasurableSet B →
        Measurable (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) B)) :
    ∀ i : Fin k,
      AEMeasurable
      (fun r : ℕ → Fin k =>
        Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
      (rowProcessLaw (k := k) P i) := by
  intro i
  have hpiMeas :
      Measurable
        (fun r : ℕ → Fin k =>
          Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k)))) :=
    measurable_measure_pi
      (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)))
      (fun r => by
        infer_instance)
      (hEvalAll i)
  exact hpiMeas.aemeasurable

/-- Under completeness of each row-process law, singleton AE-measurability is
enough to derive `hPi` for `Fin 1` product kernels. -/
lemma hPi_of_hEval_of_complete
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hComplete : ∀ i : Fin k, (rowProcessLaw (k := k) P i).IsComplete) :
    ∀ i : Fin k,
      AEMeasurable
        (fun r : ℕ → Fin k =>
          Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
        (rowProcessLaw (k := k) P i) := by
  exact
    hPi_of_measurable_eval (k := k) P rowKernel
      (measurable_rowKernel_eval_set_of_hEval_singletons_of_complete
        (k := k) P rowKernel hEval hComplete)

@[deprecated hPi_of_hEval_of_complete (since := "2026-03-02")]
lemma hPi_of_hEval
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hComplete : ∀ i : Fin k, (rowProcessLaw (k := k) P i).IsComplete) :
    ∀ i : Fin k,
      AEMeasurable
        (fun r : ℕ → Fin k =>
          Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
        (rowProcessLaw (k := k) P i) :=
  hPi_of_hEval_of_complete (k := k) P rowKernel hEval hComplete

/-- Equivalent `Fin 1` bind-applicability form used in pair/Cesàro computations. -/
lemma bind_apply_fin1_eq_lintegral_eval_of_hPi_restrict
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (i a b : Fin k)
    (hPi_restrict :
      AEMeasurable
        (fun r : ℕ → Fin k =>
          Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)) :
    ((rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
      (fun r => Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k)))))
        ({x : Fin 1 → Fin k | x 0 = b})
      =
    ∫⁻ r, (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k))
      ∂(rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i) := by
  have hset1_meas : MeasurableSet ({x : Fin 1 → Fin k | x 0 = b} : Set (Fin 1 → Fin k)) := by
    change MeasurableSet ((fun x : Fin 1 → Fin k => x 0) ⁻¹' Set.singleton b)
    exact (measurable_pi_apply 0) (MeasurableSet.singleton b)
  calc
    ((rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
      (fun r => Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k)))))
        ({x : Fin 1 → Fin k | x 0 = b})
        =
      ∫⁻ r,
        (Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          ({x : Fin 1 → Fin k | x 0 = b})
          ∂(rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i) := by
            exact Measure.bind_apply hset1_meas hPi_restrict
    _ =
      ∫⁻ r, (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k))
        ∂(rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i) := by
          refine lintegral_congr_ae ?_
          filter_upwards with r
          have hset :
              ({x : Fin 1 → Fin k | x 0 = b} : Set (Fin 1 → Fin k))
                = Set.univ.pi (fun _ : Fin 1 => ({b} : Set (Fin k))) := by
            ext x
            simp [Set.pi]
          simp [hset, Measure.pi_pi]

/-- Coordinate-event form of `rowProcessLaw_restrict_apply` for start-restricted
row-process laws. -/
lemma rowProcessLaw_restrict_apply_coord
    (P : Measure (ℕ → Fin k))
    (i a b : Fin k) (n : ℕ) :
    rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i
      ({r : ℕ → Fin k | r n = b})
      =
    P ({ω : ℕ → Fin k | ω 0 = a} ∩
        rowSuccessorValueEvent (k := k) i n b) := by
  have hset_meas : MeasurableSet ({r : ℕ → Fin k | r n = b} : Set (ℕ → Fin k)) := by
    change MeasurableSet ((fun r : ℕ → Fin k => r n) ⁻¹' Set.singleton b)
    exact (measurable_pi_apply n) (MeasurableSet.singleton b)
  calc
    rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i
        ({r : ℕ → Fin k | r n = b})
        =
      P ({ω : ℕ → Fin k | ω 0 = a} ∩
        (rowSuccessorVisitProcess (k := k) i) ⁻¹' ({r : ℕ → Fin k | r n = b})) := by
          simpa using
            (rowProcessLaw_restrict_apply (k := k) P {ω : ℕ → Fin k | ω 0 = a} i hset_meas)
    _ =
      P ({ω : ℕ → Fin k | ω 0 = a} ∩
        rowSuccessorValueEvent (k := k) i n b) := by
          refine congrArg (fun t => P ({ω : ℕ → Fin k | ω 0 = a} ∩ t)) ?_
          ext ω
          simp [rowSuccessorValueEvent, rowSuccessorVisitProcess, rowSuccessorAtNthVisit]

/-- Coordinate-event form of `rowProcessLaw` (unrestricted). -/
lemma rowProcessLaw_apply_coord
    (P : Measure (ℕ → Fin k))
    (i b : Fin k) (n : ℕ) :
    rowProcessLaw (k := k) P i ({r : ℕ → Fin k | r n = b})
      =
    P (rowSuccessorValueEvent (k := k) i n b) := by
  have hset_meas : MeasurableSet ({r : ℕ → Fin k | r n = b} : Set (ℕ → Fin k)) := by
    change MeasurableSet ((fun r : ℕ → Fin k => r n) ⁻¹' Set.singleton b)
    exact (measurable_pi_apply n) (MeasurableSet.singleton b)
  calc
    rowProcessLaw (k := k) P i ({r : ℕ → Fin k | r n = b})
        =
      P ((rowSuccessorVisitProcess (k := k) i) ⁻¹' ({r : ℕ → Fin k | r n = b})) := by
          simpa [rowProcessLaw] using
            (Measure.map_apply
              (μ := P)
              (f := rowSuccessorVisitProcess (k := k) i)
              (s := ({r : ℕ → Fin k | r n = b} : Set (ℕ → Fin k)))
              (measurable_rowSuccessorVisitProcess (k := k) i)
              hset_meas)
    _ = P (rowSuccessorValueEvent (k := k) i n b) := by
          refine congrArg P ?_
          ext ω
          simp [rowSuccessorValueEvent, rowSuccessorVisitProcess, rowSuccessorAtNthVisit]

/-- Convert restricted row-process lintegrals of singleton row-kernel
evaluations into start-gated path-space integrals. -/
lemma lintegral_rowKernel_eval_rowProcessLaw_restrict_eq_startIntegral
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (i a b : Fin k)
    (hEval :
      AEMeasurable
        (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
        (rowProcessLaw (k := k) P i)) :
    ∫⁻ r, (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k))
      ∂(rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
      =
    ∫⁻ ω,
      (if ω 0 = a then
        rowKernel i (rowSuccessorVisitProcess (k := k) i ω) ({b} : Set (Fin k)
        ) else 0) ∂P := by
  let s : Set (ℕ → Fin k) := {ω : ℕ → Fin k | ω 0 = a}
  let Q : Measure (ℕ → Fin k) := P.restrict s
  have hs : MeasurableSet s := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' Set.singleton a)
    exact (measurable_pi_apply 0) (MeasurableSet.singleton a)
  have hEvalQ :
      AEMeasurable
        (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
        (rowProcessLaw (k := k) Q i) := by
    simpa [Q] using
      (aemeasurable_rowKernel_eval_of_rowProcessLaw_restrict
        (k := k) P s rowKernel i b hEval)
  have hmap_int :
      ∫⁻ r, (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k))
        ∂(rowProcessLaw (k := k) Q i)
        =
      ∫⁻ ω, (rowKernel i (rowSuccessorVisitProcess (k := k) i ω) : Measure (Fin k))
        ({b} : Set (Fin k)) ∂Q := by
    simpa [rowProcessLaw] using
      (MeasureTheory.lintegral_map'
        (μ := Q)
        (f := fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
        (g := rowSuccessorVisitProcess (k := k) i)
        hEvalQ
        (measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
  calc
    ∫⁻ r, (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k))
      ∂(rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
        = ∫⁻ r, (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k))
            ∂(rowProcessLaw (k := k) Q i) := by simp [Q, s]
    _ = ∫⁻ ω, (rowKernel i (rowSuccessorVisitProcess (k := k) i ω) : Measure (Fin k))
          ({b} : Set (Fin k)) ∂Q := hmap_int
    _ = ∫⁻ ω in s, (rowKernel i (rowSuccessorVisitProcess (k := k) i ω) : Measure (Fin k))
          ({b} : Set (Fin k)) ∂P := by
            simp [Q]
    _ =
      ∫⁻ ω,
        s.indicator
          (fun ω => (rowKernel i (rowSuccessorVisitProcess (k := k) i ω) : Measure (Fin k))
            ({b} : Set (Fin k))) ω ∂P := by
          symm
          exact lintegral_indicator hs _
    _ =
      ∫⁻ ω,
        (if ω 0 = a then
          rowKernel i (rowSuccessorVisitProcess (k := k) i ω) ({b} : Set (Fin k)
          ) else 0) ∂P := by
            simp [s, Set.indicator]

/-- Global start-restricted row-successor permutation invariance for a path law. -/
def StartRestrictedRowSuccessorPermInvariant
    (P : Measure (ℕ → Fin k)) : Prop :=
  ∀ (i a b : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ),
    P ({ω : ℕ → Fin k | ω 0 = a} ∩
        rowSuccessorValueEvent (k := k) i (σ n) b)
      =
    P ({ω : ℕ → Fin k | ω 0 = a} ∩
        rowSuccessorValueEvent (k := k) i n b)

/-- If a concrete witness violates start-restricted permutation invariance,
then that invariance cannot be derivable from only `hμ` and `hExt`. -/
theorem not_derivable_startRestrictedRowSuccessorPermInvariant_of_witness
    (hWitness :
      ∃ (μ : FiniteAlphabet.PrefixMeasure (Fin 2)) (P : Measure (ℕ → Fin 2)),
        IsProbabilityMeasure P ∧
        MarkovExchangeablePrefixMeasure (k := 2) μ ∧
        (∀ xs : List (Fin 2), μ xs = P (cylinder (k := 2) xs)) ∧
        ¬ StartRestrictedRowSuccessorPermInvariant (k := 2) P) :
    ¬ (∀ (μ : FiniteAlphabet.PrefixMeasure (Fin 2)) (P : Measure (ℕ → Fin 2)),
          IsProbabilityMeasure P →
          MarkovExchangeablePrefixMeasure (k := 2) μ →
          (∀ xs : List (Fin 2), μ xs = P (cylinder (k := 2) xs)) →
          StartRestrictedRowSuccessorPermInvariant (k := 2) P) := by
  intro hDerive
  rcases hWitness with ⟨μ, P, hPprob, hμ, hExt, hNotPerm⟩
  exact hNotPerm (hDerive μ P hPprob hμ hExt)

/-- Direct pair-cylinder identity from start-restricted row-law data, without
the start-constancy / Cesàro route. -/
theorem pair_cylinder_identity_of_rowKernelData_restrict_direct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hrow_restrict_data :
      ∀ (i a : Fin k), ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
          =
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))))
    (hPi :
      ∀ i : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) P i)) :
    ∀ a b : Fin k,
      P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b]) =
        ∫⁻ ω,
          (if ω 0 = a then
            rowKernel a (rowSuccessorVisitProcess (k := k) a ω) ({b} : Set (Fin k))
          else 0) ∂P := by
  intro a b
  let Q : Measure (ℕ → Fin k) := P.restrict {ω : ℕ → Fin k | ω 0 = a}
  have hPi_restrict :
      AEMeasurable
        (fun r : ℕ → Fin k =>
          Measure.pi (fun _ : Fin 1 => (rowKernel a r : Measure (Fin k))))
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) a) := by
    exact hPi_restrict_of_hPi (k := k) P rowKernel hPi a a
  have hselMono : StrictMono (fun _ : Fin 1 => 0) := by
    intro x y hxy
    exfalso
    have hxy' : x = y := Subsingleton.elim x y
    exact (lt_irrefl _ (hxy' ▸ hxy))
  have hrow1 :=
    hrow_restrict_data a a 1 (fun _ : Fin 1 => 0) hselMono
  have hrow1_eval :
      (Measure.map (fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => 0) j))
          (rowProcessLaw (k := k) Q a)) ({x : Fin 1 → Fin k | x 0 = b})
        =
      ((rowProcessLaw (k := k) Q a).bind
        (fun r => Measure.pi (fun _ : Fin 1 => (rowKernel a r : Measure (Fin k)))))
          ({x : Fin 1 → Fin k | x 0 = b}) := by
    exact congrArg (fun M => M ({x : Fin 1 → Fin k | x 0 = b})) hrow1
  have hset1_meas : MeasurableSet ({x : Fin 1 → Fin k | x 0 = b} : Set (Fin 1 → Fin k)) := by
    change MeasurableSet ((fun x : Fin 1 → Fin k => x 0) ⁻¹' Set.singleton b)
    exact (measurable_pi_apply 0) (MeasurableSet.singleton b)
  have hleft1 :
      (Measure.map (fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => 0) j))
          (rowProcessLaw (k := k) Q a)) ({x : Fin 1 → Fin k | x 0 = b})
        =
      rowProcessLaw (k := k) Q a ({r : ℕ → Fin k | r 0 = b}) := by
    have hmeas_map :
        Measurable (fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => 0) j)) := by
      exact measurable_pi_lambda _ (fun _ : Fin 1 => measurable_pi_apply 0)
    calc
      (Measure.map (fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => 0) j))
          (rowProcessLaw (k := k) Q a)) ({x : Fin 1 → Fin k | x 0 = b})
          =
        rowProcessLaw (k := k) Q a
          ((fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => 0) j)) ⁻¹'
            ({x : Fin 1 → Fin k | x 0 = b})) := by
              simpa using
                (Measure.map_apply
                  (μ := rowProcessLaw (k := k) Q a)
                  (f := fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => 0) j))
                  (s := ({x : Fin 1 → Fin k | x 0 = b} : Set (Fin 1 → Fin k)))
                  hmeas_map hset1_meas)
      _ = rowProcessLaw (k := k) Q a ({r : ℕ → Fin k | r 0 = b}) := by
            refine congrArg (fun t => rowProcessLaw (k := k) Q a t) ?_
            ext r
            simp
  have hright1 :
      ((rowProcessLaw (k := k) Q a).bind
        (fun r => Measure.pi (fun _ : Fin 1 => (rowKernel a r : Measure (Fin k)))))
          ({x : Fin 1 → Fin k | x 0 = b})
        =
      ∫⁻ r, (rowKernel a r : Measure (Fin k)) ({b} : Set (Fin k))
        ∂(rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) a) := by
    simpa [Q] using
      (bind_apply_fin1_eq_lintegral_eval_of_hPi_restrict
        (k := k) P rowKernel a a b hPi_restrict)
  have hrow0 :
      rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) a
        ({r : ℕ → Fin k | r 0 = b})
      =
      ∫⁻ r, (rowKernel a r : Measure (Fin k)) ({b} : Set (Fin k))
        ∂(rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) a) := by
    simpa [Q] using hleft1.symm.trans (hrow1_eval.trans hright1)
  have hcoord :
      rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) a
        ({r : ℕ → Fin k | r 0 = b})
      =
      P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) a 0 b) :=
    rowProcessLaw_restrict_apply_coord (k := k) P a a b 0
  calc
    P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b])
        = P ({ω : ℕ → Fin k | ω 0 = a} ∩
            rowSuccessorValueEvent (k := k) a 0 b) := by
              simpa using
                (measure_cylinder_pair_eq_start_and_rowSuccessorZero (k := k) P a b)
    _ = rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) a
          ({r : ℕ → Fin k | r 0 = b}) := hcoord.symm
    _ =
      ∫⁻ r, (rowKernel a r : Measure (Fin k)) ({b} : Set (Fin k))
        ∂(rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) a) := hrow0
    _ =
      ∫⁻ ω,
        (if ω 0 = a then
          rowKernel a (rowSuccessorVisitProcess (k := k) a ω) ({b} : Set (Fin k))
        else 0) ∂P := by
          exact
            lintegral_rowKernel_eval_rowProcessLaw_restrict_eq_startIntegral
              (k := k) P rowKernel a a b (hEval a b)

/-- Direct length-2 cross-anchor identity from start-restricted row-law data. -/
theorem crossAnchor_lengthTwo_of_rowKernelData_restrict_direct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hrow_restrict_data :
      ∀ (i a : Fin k), ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
          =
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))))
    (hPi :
      ∀ i : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) P i)) :
    ∀ a b : Fin k,
      P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b]) =
        ∫⁻ ω,
          (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω [a, b] else 0) ∂P := by
  intro a b
  have hpair :=
    pair_cylinder_identity_of_rowKernelData_restrict_direct
      (k := k) P rowKernel hEval hrow_restrict_data hPi a b
  calc
    P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b])
        =
      ∫⁻ ω,
        (if ω 0 = a then
          rowKernel a (rowSuccessorVisitProcess (k := k) a ω) ({b} : Set (Fin k))
        else 0) ∂P := hpair
    _ =
      ∫⁻ ω,
        (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω [a, b] else 0) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards with ω
          simp [rowKernelStepProd]

/-- Full-prefix lifting interface: from the length-2 case plus one cons-step rule,
derive the complete `CrossAnchorProductIdentity` for all nontrivial prefixes. -/
theorem crossAnchorProductIdentity_of_lengthTwo_and_consStep
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hpair :
      ∀ a b : Fin k,
        P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b]) =
          ∫⁻ ω,
            (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω [a, b] else 0) ∂P)
    (hstep :
      ∀ (a b c : Fin k) (xs : List (Fin k)),
        P (MarkovDeFinettiRecurrence.cylinder (k := k) (b :: c :: xs)) =
          ∫⁻ ω,
            (if ω 0 = b then rowKernelStepProd (k := k) rowKernel ω (b :: c :: xs) else 0) ∂P
          →
        P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: c :: xs)) =
          ∫⁻ ω,
            (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: c :: xs) else 0) ∂P) :
    CrossAnchorProductIdentity (k := k) P rowKernel := by
  intro a b xs
  induction xs generalizing a b with
  | nil =>
    simpa using hpair a b
  | cons c rest ih =>
    exact hstep a b c rest (ih b c)

/-- Start-restricted row-law factorization data:
for each anchor `i` and start state `a`, finite coordinate projections of the
row process under `P.restrict {ω | ω 0 = a}` factor through `rowKernel i`. -/
def StartRestrictedRowKernelData
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) : Prop :=
  ∀ (i a : Fin k), ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
    Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
      =
    (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
      (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k))))

/-- Cross-row coherence step:
if the product identity holds for `(b :: c :: xs)`, then it extends by one
step to `(a :: b :: c :: xs)`. This is the code-level cross-row coherence law. -/
def CrossRowCoherenceStep
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) : Prop :=
  ∀ (a b c : Fin k) (xs : List (Fin k)),
    P (MarkovDeFinettiRecurrence.cylinder (k := k) (b :: c :: xs)) =
      ∫⁻ ω,
        (if ω 0 = b then rowKernelStepProd (k := k) rowKernel ω (b :: c :: xs) else 0) ∂P
      →
    P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: c :: xs)) =
      ∫⁻ ω,
        (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: c :: xs) else 0) ∂P

/-- Internal Fortini crux-data bundle used by the explicit bridge theorem. -/
def RowKernelCruxData
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) : Prop :=
  (∀ i : Fin k, ∀ b : Fin k,
      AEMeasurable
        (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
        (rowProcessLaw (k := k) P i)) ∧
  StartRestrictedRowKernelData (k := k) P rowKernel ∧
  (∀ i : Fin k,
      AEMeasurable
        (fun r : ℕ → Fin k =>
          Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
        (rowProcessLaw (k := k) P i)) ∧
  CrossRowCoherenceStep (k := k) P rowKernel

/-- Shared latent-transition coherence:
all finite-prefix cylinder probabilities are given by integrating `wordProb`
against the path-indexed latent Markov parameter induced by `rowKernel`. -/
def SharedLatentTransitionCoherence
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) : Prop :=
  ∀ xs : List (Fin k),
    P (MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
      ∫⁻ ω, wordProb (k := k)
        (rowKernelToMarkovParam (k := k)
          (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
          (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) xs ∂P

/-- Shared latent-transition coherence implies cross-anchor product identity. -/
theorem crossAnchorProductIdentity_of_sharedLatentTransitionCoherence
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hcoh : SharedLatentTransitionCoherence (k := k) P rowKernel) :
    CrossAnchorProductIdentity (k := k) P rowKernel := by
  intro a b xs
  calc
    P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: xs))
        =
      ∫⁻ ω, wordProb (k := k)
        (rowKernelToMarkovParam (k := k)
          (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
          (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) (a :: b :: xs) ∂P := by
            exact hcoh (a :: b :: xs)
    _ =
      ∫⁻ ω,
        (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards with ω
          exact (wordProb_rowKernelToMarkovParam_eq_indicator_stepProd
            (k := k) rowKernel ω a b xs)

/-- Shared latent-transition coherence implies the code-level cross-row
coherence step used by the induction combinator. -/
theorem crossRowCoherenceStep_of_sharedLatentTransitionCoherence
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hcoh : SharedLatentTransitionCoherence (k := k) P rowKernel) :
    CrossRowCoherenceStep (k := k) P rowKernel := by
  have hcross :=
    crossAnchorProductIdentity_of_sharedLatentTransitionCoherence
      (k := k) P rowKernel hcoh
  intro a b c xs _
  simpa using hcross a b (c :: xs)

/-- Build internal crux data from start-restricted row-law data and shared
latent-transition coherence. -/
theorem rowKernelCruxData_of_startData_and_sharedLatentCoherence
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hstart : StartRestrictedRowKernelData (k := k) P rowKernel)
    (hPi :
      ∀ i : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) P i))
    (hcoh : SharedLatentTransitionCoherence (k := k) P rowKernel) :
    RowKernelCruxData (k := k) P rowKernel := by
  refine ⟨hEval, hstart, hPi, ?_⟩
  exact crossRowCoherenceStep_of_sharedLatentTransitionCoherence
    (k := k) P rowKernel hcoh

/-- Recurrence extraction layer:
from `MarkovRecurrentPrefixMeasure`, obtain an extension with almost-sure
infinite returns to the dynamic start state. -/
def RecurrentExtensionData
    (μ : FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
    (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
    (∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = ω 0})

theorem recurrentExtensionData_of_markovRecurrent
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ) :
    RecurrentExtensionData (k := k) μ := by
  exact
    MarkovRecurrentPrefixMeasure.exists_extension_ae_infinite_returns_to_start
      (k := k) μ hrec

/-- Strong recurrence on a concrete path law: for every anchor state `i`, whenever
`i` is visited at least once, all visit indices exist. This mirrors the
literature's infinite-row condition without introducing a dummy state. -/
def StrongRecurrence
    (P : Measure (ℕ → Fin k)) : Prop :=
  ∀ i : Fin k, ∀ᵐ ω ∂P,
    (∃ t : ℕ, ω t = i) → ∀ n : ℕ, nthVisitTimeExists (k := k) ω i n

/-- Row-wise almost-sure infinite visits imply strong recurrence. -/
theorem strongRecurrence_of_ae_infinite_visits
    (P : Measure (ℕ → Fin k))
    (hrows : ∀ i : Fin k, ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    StrongRecurrence (k := k) P := by
  intro i
  filter_upwards [hrows i] with ω hInf
  intro _hex n
  exact nthVisitTimeExists_of_infinite_visits (k := k) ω i n hInf

/-- Extract an extension with strong recurrence from row-wise recurrence at the
prefix-law level. -/
theorem exists_extension_strongRecurrence_of_markovRowRecurrent
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      StrongRecurrence (k := k) P := by
  rcases MarkovRowRecurrentPrefixMeasure.ae_infinite_visits (k := k) μ hrow with
    ⟨P, hP, hExt, hrows⟩
  refine ⟨P, hP, hExt, ?_⟩
  exact strongRecurrence_of_ae_infinite_visits (k := k) P hrows

/-- Cross-anchor product identity from row-kernel data.

Explicit interface: requires the start-restricted invariance/row-law data and
the cons-step recursion as assumptions.
This is the canonical internal theorem path for Fortini crux closure. -/
theorem crossAnchorProductIdentity_of_rowKernelData
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hcrux : RowKernelCruxData (k := k) P rowKernel) :
    CrossAnchorProductIdentity (k := k) P rowKernel := by
  rcases hcrux with ⟨hEval, hrow_restrict_data, hPi, hstep⟩
  have hpair :
      ∀ a b : Fin k,
        P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b]) =
          ∫⁻ ω,
            (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω [a, b] else 0) ∂P :=
    crossAnchor_lengthTwo_of_rowKernelData_restrict_direct
      (k := k) P rowKernel hEval hrow_restrict_data hPi
  exact
    crossAnchorProductIdentity_of_lengthTwo_and_consStep
      (k := k) P rowKernel hpair hstep

/-- The cylinder mixing identity from row-kernel family data.

This is a structural consequence of `CrossAnchorProductIdentity`. -/
theorem cylinderMixingIdentity_P_of_rowKernelData
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hcrux : RowKernelCruxData (k := k) P rowKernel) :
    CylinderMixingIdentity_P (k := k) P rowKernel := by
  have hcross :=
    crossAnchorProductIdentity_of_rowKernelData (k := k) P rowKernel hcrux
  exact cylinderMixingIdentity_P_of_crossAnchorProductIdentity
    (k := k) P rowKernel hcross

theorem rowKernelToMarkovParamLaw_reconstruction_all_diracInit_of_lifted_rowKernel
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hθ :
      AEMeasurable
        (rowKernelToMarkovParam (k := k)
          (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
          (liftedRowKernelFromRowProcess (k := k) rowKernel)) P)
    (hCM : CylinderMixingIdentity_P (k := k) P rowKernel) :
    ∀ xs : List (Fin k),
      P (MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
        (∫⁻ θ, wordProb (k := k) θ xs
          ∂(rowKernelToMarkovParamLaw (k := k) P
            (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
            (liftedRowKernelFromRowProcess (k := k) rowKernel))) := by
  intro xs
  match xs with
  | [] =>
    exact rowKernelToMarkovParamLaw_reconstruction_nil
      (k := k) P _ (liftedRowKernelFromRowProcess (k := k) rowKernel) hθ
  | [a] =>
    exact rowKernelToMarkovParamLaw_reconstruction_singleton_diracInit
      (k := k) P (liftedRowKernelFromRowProcess (k := k) rowKernel)
      hθ a
  | x :: y :: rest =>
    have hlen : (x :: y :: rest).length ≥ 2 := by simp
    calc P (MarkovDeFinettiRecurrence.cylinder (k := k) (x :: y :: rest))
        = ∫⁻ ω, wordProb (k := k)
            (rowKernelToMarkovParam (k := k)
              (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
              (liftedRowKernelFromRowProcess (k := k) rowKernel) ω)
            (x :: y :: rest) ∂P := hCM (x :: y :: rest) hlen
      _ = ∫⁻ θ, wordProb (k := k) θ (x :: y :: rest)
            ∂(rowKernelToMarkovParamLaw (k := k) P
              (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
              (liftedRowKernelFromRowProcess (k := k) rowKernel)) := by
          symm
          exact lintegral_wordProb_rowKernelToMarkovParamLaw
            (k := k) P _
            (liftedRowKernelFromRowProcess (k := k) rowKernel)
            (x :: y :: rest) hθ

/-- Fortini bridge (internal explicit interface):
from a concrete extension `P` together with explicit row-kernel crux data,
derive the Markov mixture representation. -/
def FortiniSuccessorMatrixInvarianceTheoremInternal (k : ℕ) : Prop :=
  ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
    (∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
        RowKernelCruxData (k := k) P rowKernel) →
      ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
        ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi

/-- Backwards-compatible alias; internal theorem naming is now canonical. -/
@[deprecated FortiniSuccessorMatrixInvarianceTheoremInternal (since := "2026-03-02")]
abbrev FortiniSuccessorMatrixInvarianceTheoremExplicit (k : ℕ) : Prop :=
  FortiniSuccessorMatrixInvarianceTheoremInternal k

/-- **Proof** of the internal explicit Fortini bridge theorem. -/
theorem fortiniSuccessorMatrixInvarianceTheoremInternal_proved :
    FortiniSuccessorMatrixInvarianceTheoremInternal k := by
  intro μ ⟨P, hPprob, hExt, rowKernel, hcrux⟩
  rcases hcrux with ⟨hEval, hrow_restrict_data, hPi, hstep⟩
  letI : IsProbabilityMeasure P := hPprob
  have hθ := aemeasurable_rowKernelToMarkovParam_diracInit_lifted P rowKernel hEval
  have hCM := cylinderMixingIdentity_P_of_rowKernelData
      (k := k) P rowKernel ⟨hEval, hrow_restrict_data, hPi, hstep⟩
  have hall := rowKernelToMarkovParamLaw_reconstruction_all_diracInit_of_lifted_rowKernel
      (k := k) P rowKernel hθ hCM
  set law := rowKernelToMarkovParamLaw (k := k) P
      (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
      (liftedRowKernelFromRowProcess (k := k) rowKernel) with hlaw_def
  have hlaw_prob : IsProbabilityMeasure law :=
    Measure.isProbabilityMeasure_map (f := rowKernelToMarkovParam (k := k)
      (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
      (liftedRowKernelFromRowProcess (k := k) rowKernel)) hθ
  refine ⟨law, hlaw_prob, ?_⟩
  intro xs
  rw [hExt xs]
  exact hall xs

/-- Backwards-compatible theorem alias; internal naming is canonical. -/
@[deprecated fortiniSuccessorMatrixInvarianceTheoremInternal_proved (since := "2026-03-02")]
theorem fortiniSuccessorMatrixInvarianceTheoremExplicit_proved :
    FortiniSuccessorMatrixInvarianceTheoremInternal k :=
  fortiniSuccessorMatrixInvarianceTheoremInternal_proved (k := k)

/-- Fortini successor-matrix invariance theorem (literature-facing surface):
Markov exchangeability + recurrence imply Markov-mixture representation. -/
def FortiniSuccessorMatrixInvarianceTheorem (k : ℕ) : Prop :=
  ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
    MarkovExchangeablePrefixMeasure (k := k) μ →
    MarkovRecurrentPrefixMeasure (k := k) μ →
      ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
        ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi

/-- Row-successor matrix invariance (length ≥ 2 case):
finite-prefix cylinder probabilities agree with the latent `wordProb` integral. -/
def RowSuccessorMatrixInvariance
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) : Prop :=
  CylinderMixingIdentity_P (k := k) P rowKernel

/-- Length-≥2 row-successor-matrix invariance directly yields cross-anchor
product identity by pointwise rewriting `wordProb` into `rowKernelStepProd`
with start indicator. -/
theorem crossAnchorProductIdentity_of_rowSuccessorMatrixInvariance
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hInv : RowSuccessorMatrixInvariance (k := k) P rowKernel) :
    CrossAnchorProductIdentity (k := k) P rowKernel := by
  intro a b xs
  have hlen : (a :: b :: xs).length ≥ 2 := by simp
  calc
    P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: xs))
        =
      ∫⁻ ω, wordProb (k := k)
        (rowKernelToMarkovParam (k := k)
          (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
          (liftedRowKernelFromRowProcess (k := k) rowKernel) ω)
          (a :: b :: xs) ∂P := hInv (a :: b :: xs) hlen
    _ =
      ∫⁻ ω,
        (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards with ω
          exact (wordProb_rowKernelToMarkovParam_eq_indicator_stepProd
            (k := k) rowKernel ω a b xs)

/-- Joint partial exchangeability of the full successor matrix:
for finite selections across anchors and visit indices, independent finite
within-row permutations leave the joint law invariant. -/
def SuccessorMatrixPartialExchangeable
    (P : Measure (ℕ → Fin k)) : Prop :=
  ∀ (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (σ : Fin k → Equiv.Perm ℕ),
      Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω ((σ (anchor j)) (idx j))) P
      =
      Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) P

/-- First nontrivial fragment from successor-matrix partial exchangeability:
row-successor value events are permutation-invariant in the visit index
(without start restriction). -/
theorem rowSuccessorValueEvent_permInvariant_of_successorMatrixPE
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable P)
    (i b : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) :
    P (rowSuccessorValueEvent (k := k) i (σ n) b)
      =
    P (rowSuccessorValueEvent (k := k) i n b) := by
  classical
  let σrow : Fin k → Equiv.Perm ℕ :=
    fun j => if j = i then σ else Equiv.refl ℕ
  have hmap :
      Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin 1 =>
            rowSuccessorVisitProcess (k := k) i ω ((σrow i) n)) P
      =
      Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin 1 =>
            rowSuccessorVisitProcess (k := k) i ω n) P := by
    simpa [σrow] using
      hPE 1 (fun _ : Fin 1 => i) (fun _ : Fin 1 => n) σrow
  have hset1_meas : MeasurableSet ({x : Fin 1 → Fin k | x 0 = b} : Set (Fin 1 → Fin k)) := by
    change MeasurableSet ((fun x : Fin 1 → Fin k => x 0) ⁻¹' Set.singleton b)
    exact (measurable_pi_apply 0) (MeasurableSet.singleton b)
  have hmap_eval :
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin 1 =>
            rowSuccessorVisitProcess (k := k) i ω ((σrow i) n)) P)
          ({x : Fin 1 → Fin k | x 0 = b})
      =
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin 1 =>
            rowSuccessorVisitProcess (k := k) i ω n) P)
          ({x : Fin 1 → Fin k | x 0 = b}) := by
    exact congrArg (fun M => M ({x : Fin 1 → Fin k | x 0 = b})) hmap
  have hleft :
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin 1 =>
            rowSuccessorVisitProcess (k := k) i ω ((σrow i) n)) P)
          ({x : Fin 1 → Fin k | x 0 = b})
        =
      P (rowSuccessorValueEvent (k := k) i (σ n) b) := by
    have hmeasL :
        Measurable
          (fun ω : ℕ → Fin k =>
            fun j : Fin 1 => rowSuccessorVisitProcess (k := k) i ω ((σrow i) n)) := by
      exact measurable_pi_lambda _ (fun _ : Fin 1 =>
        (measurable_pi_apply ((σrow i) n)).comp
          (measurable_rowSuccessorVisitProcess (k := k) i))
    calc
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin 1 => rowSuccessorVisitProcess (k := k) i ω ((σrow i) n)) P)
          ({x : Fin 1 → Fin k | x 0 = b})
          =
        P
          ((fun ω : ℕ → Fin k =>
            fun j : Fin 1 => rowSuccessorVisitProcess (k := k) i ω ((σrow i) n)) ⁻¹'
              ({x : Fin 1 → Fin k | x 0 = b})) := by
                simpa using
                  (Measure.map_apply
                    (μ := P)
                    (f := fun ω : ℕ → Fin k =>
                      fun j : Fin 1 => rowSuccessorVisitProcess (k := k) i ω ((σrow i) n))
                    (s := ({x : Fin 1 → Fin k | x 0 = b} : Set (Fin 1 → Fin k)))
                    hmeasL hset1_meas)
      _ = P (rowSuccessorValueEvent (k := k) i (σ n) b) := by
            refine congrArg P ?_
            ext ω
            simp [rowSuccessorValueEvent, rowSuccessorVisitProcess, rowSuccessorAtNthVisit, σrow]
  have hright :
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin 1 =>
            rowSuccessorVisitProcess (k := k) i ω n) P)
          ({x : Fin 1 → Fin k | x 0 = b})
        =
      P (rowSuccessorValueEvent (k := k) i n b) := by
    have hmeasR :
        Measurable
          (fun ω : ℕ → Fin k =>
            fun j : Fin 1 => rowSuccessorVisitProcess (k := k) i ω n) := by
      exact measurable_pi_lambda _ (fun _ : Fin 1 =>
        (measurable_pi_apply n).comp
          (measurable_rowSuccessorVisitProcess (k := k) i))
    calc
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin 1 => rowSuccessorVisitProcess (k := k) i ω n) P)
          ({x : Fin 1 → Fin k | x 0 = b})
          =
        P
          ((fun ω : ℕ → Fin k =>
            fun j : Fin 1 => rowSuccessorVisitProcess (k := k) i ω n) ⁻¹'
              ({x : Fin 1 → Fin k | x 0 = b})) := by
                simpa using
                  (Measure.map_apply
                    (μ := P)
                    (f := fun ω : ℕ → Fin k =>
                      fun j : Fin 1 => rowSuccessorVisitProcess (k := k) i ω n)
                    (s := ({x : Fin 1 → Fin k | x 0 = b} : Set (Fin 1 → Fin k)))
                    hmeasR hset1_meas)
      _ = P (rowSuccessorValueEvent (k := k) i n b) := by
            refine congrArg P ?_
            ext ω
            simp [rowSuccessorValueEvent, rowSuccessorVisitProcess, rowSuccessorAtNthVisit]
  calc
    P (rowSuccessorValueEvent (k := k) i (σ n) b)
        = (Measure.map
            (fun ω : ℕ → Fin k =>
              fun j : Fin 1 =>
                rowSuccessorVisitProcess (k := k) i ω ((σrow i) n)) P)
            ({x : Fin 1 → Fin k | x 0 = b}) := hleft.symm
    _ = (Measure.map
            (fun ω : ℕ → Fin k =>
              fun j : Fin 1 =>
                rowSuccessorVisitProcess (k := k) i ω n) P)
            ({x : Fin 1 → Fin k | x 0 = b}) := hmap_eval
    _ = P (rowSuccessorValueEvent (k := k) i n b) := hright

/-- Canonical consequence of successor-matrix PE:
for each anchor `i`, the full row-process law is invariant under every
coordinate permutation `σ : Perm ℕ`. -/
theorem rowProcessLaw_permInvariant_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P) :
    ∀ (i : Fin k) (σ : Equiv.Perm ℕ),
      Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
        rowProcessLaw (k := k) P i := by
  intro i σ
  let ρ : Measure (ℕ → Fin k) := rowProcessLaw (k := k) P i
  have hmeas_rowPermute : Measurable (rowPermute (k := k) σ) := by
    exact measurable_pi_lambda _ (fun n => measurable_pi_apply (σ n))
  have hfin :
      ∀ n (S : Set (Fin n → Fin k)) (_hS : MeasurableSet S),
        Measure.map (Exchangeability.prefixProj (α := Fin k) n)
            (Measure.map (rowPermute (k := k) σ) ρ) S
          =
        Measure.map (Exchangeability.prefixProj (α := Fin k) n) ρ S := by
    intro n S hS
    let σrow : Fin k → Equiv.Perm ℕ := fun j => if j = i then σ else Equiv.refl ℕ
    have hPE_n :
        Measure.map
          (fun ω : ℕ → Fin k =>
            fun j : Fin n =>
              rowSuccessorVisitProcess (k := k) i ω (σ j)) P
          =
        Measure.map
          (fun ω : ℕ → Fin k =>
            fun j : Fin n =>
              rowSuccessorVisitProcess (k := k) i ω j) P := by
      simpa [σrow] using
        hPE n (fun _ : Fin n => i) (fun j : Fin n => (j : ℕ)) σrow
    have hmap_n :
        Measure.map (fun r : ℕ → Fin k => fun j : Fin n => r (σ j)) ρ
          =
        Measure.map (fun r : ℕ → Fin k => fun j : Fin n => r j) ρ := by
      unfold ρ rowProcessLaw
      calc
        Measure.map (fun r : ℕ → Fin k => fun j : Fin n => r (σ j))
            (Measure.map (rowSuccessorVisitProcess (k := k) i) P)
            =
          Measure.map
            ((fun r : ℕ → Fin k => fun j : Fin n => r (σ j)) ∘
              rowSuccessorVisitProcess (k := k) i) P := by
                simpa using
                  (Measure.map_map
                    (μ := P)
                    (g := fun r : ℕ → Fin k => fun j : Fin n => r (σ j))
                    (f := rowSuccessorVisitProcess (k := k) i)
                    (measurable_pi_lambda _ (fun j => measurable_pi_apply (σ j)))
                    (measurable_rowSuccessorVisitProcess (k := k) i))
        _ =
          Measure.map
            (fun ω : ℕ → Fin k =>
              fun j : Fin n => rowSuccessorVisitProcess (k := k) i ω j) P := by
                exact hPE_n
        _ =
          Measure.map (fun r : ℕ → Fin k => fun j : Fin n => r j)
            (Measure.map (rowSuccessorVisitProcess (k := k) i) P) := by
              exact
                (Measure.map_map
                  (μ := P)
                  (g := fun r : ℕ → Fin k => fun j : Fin n => r j)
                  (f := rowSuccessorVisitProcess (k := k) i)
                  (Exchangeability.measurable_prefixProj (α := Fin k) (n := n))
                  (measurable_rowSuccessorVisitProcess (k := k) i)).symm
      -- Convert both finite marginals to `prefixProj` form.
    have hleft :
        Measure.map (Exchangeability.prefixProj (α := Fin k) n)
            (Measure.map (rowPermute (k := k) σ) ρ)
          =
        Measure.map (fun r : ℕ → Fin k => fun j : Fin n => r (σ j)) ρ := by
      have hcomp :
          ((Exchangeability.prefixProj (α := Fin k) n) ∘ (rowPermute (k := k) σ))
            =
          (fun r : ℕ → Fin k => fun j : Fin n => r (σ j)) := by
        funext r j
        rfl
      calc
        Measure.map (Exchangeability.prefixProj (α := Fin k) n)
            (Measure.map (rowPermute (k := k) σ) ρ)
            =
          Measure.map ((Exchangeability.prefixProj (α := Fin k) n) ∘ (rowPermute (k := k) σ)) ρ := by
              simpa using
                (Measure.map_map
                  (μ := ρ)
                  (g := Exchangeability.prefixProj (α := Fin k) n)
                  (f := rowPermute (k := k) σ)
                  (Exchangeability.measurable_prefixProj (α := Fin k) (n := n))
                  hmeas_rowPermute)
        _ =
          Measure.map (fun r : ℕ → Fin k => fun j : Fin n => r (σ j)) ρ := by
            simp [hcomp]
    have hright :
        Measure.map (Exchangeability.prefixProj (α := Fin k) n) ρ
          =
        Measure.map (fun r : ℕ → Fin k => fun j : Fin n => r j) ρ := by
      rfl
    calc
      Measure.map (Exchangeability.prefixProj (α := Fin k) n)
          (Measure.map (rowPermute (k := k) σ) ρ) S
          =
        (Measure.map (fun r : ℕ → Fin k => fun j : Fin n => r (σ j)) ρ) S := by
          exact congrArg (fun M => M S) hleft
      _ =
        (Measure.map (fun r : ℕ → Fin k => fun j : Fin n => r j) ρ) S := by
          exact congrArg (fun M => M S) hmap_n
      _ =
        Measure.map (Exchangeability.prefixProj (α := Fin k) n) ρ S := by
          exact congrArg (fun M => M S) hright.symm
  haveI hρ_prob : IsProbabilityMeasure ρ := by
    unfold ρ rowProcessLaw
    exact Measure.isProbabilityMeasure_map
      ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
  haveI hρσ_prob : IsProbabilityMeasure (Measure.map (rowPermute (k := k) σ) ρ) := by
    exact Measure.isProbabilityMeasure_map hmeas_rowPermute.aemeasurable
  exact
    Exchangeability.measure_eq_of_fin_marginals_eq_prob
      (α := Fin k)
      (μ := Measure.map (rowPermute (k := k) σ) ρ)
      (ν := ρ)
      hfin

/-- Canonical PE consequence: existence of a row-kernel family carrying
row-process finite-projection factorization, singleton-eval AE-measurability,
and `Fin 1` product-kernel AE-measurability. -/
theorem exists_rowKernel_hrow_hEval_hPi_of_successorMatrixPE
    (hk : 0 < k)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P) :
    ∃ rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k),
      (∀ i : Fin k, ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) P i)
          =
        (rowProcessLaw (k := k) P i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k))))) ∧
      (∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i)) ∧
      (∀ i : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) P i)) := by
  have hpermAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i := by
    intro i σ _
    exact rowProcessLaw_permInvariant_of_successorMatrixPE (k := k) P hPE i σ
  rcases
      exists_rowKernelFamily_with_aemeasurableEvalPi_of_rowProcess_permInvariant
        (k := k) hk P hpermAll with
    ⟨rowKernel, hrow, hEval, hPi⟩
  exact ⟨rowKernel, hrow, hEval, hPi⟩

/-- Canonical PE consequence (projected payload):
existence of a row-kernel family with singleton-eval AE-measurability and
`Fin 1` product-kernel AE-measurability. -/
theorem exists_rowKernel_hEval_hPi_of_successorMatrixPE
    (hk : 0 < k)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P) :
    ∃ rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k),
      (∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i)) ∧
      (∀ i : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) P i)) := by
  rcases exists_rowKernel_hrow_hEval_hPi_of_successorMatrixPE
      (k := k) hk P hPE with ⟨rowKernel, _hrow, hEval, hPi⟩
  exact ⟨rowKernel, hEval, hPi⟩

/-- Off-diagonal start-restricted row-successor permutation invariance from
extension evidence transport at the finite-prefix carrier level. -/
theorem startRestrictedRowSuccessorPermInvariant_offDiagonal_of_extension_transport
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hCarrierTransport :
      ∀ (i b : Fin k) (n n' N : ℕ), b ≠ i →
        ∃ e :
          rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
            (fun m => if m = n then b else i) N ≃
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n'} : Finset ℕ)
              (fun m => if m = n' then b else i) N,
          ∀ xs :
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
              (fun m => if m = n then b else i) N,
            evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    ∀ (i a b : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ), b ≠ i →
      P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i (σ n) b)
        =
      P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i n b) := by
  intro i a b σ n hbi
  have hEquiv :
      ∀ N : ℕ,
        ∃ e :
          rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({σ n} : Finset ℕ)
            (fun m => if m = σ n then b else i) N ≃
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
              (fun m => if m = n then b else i) N,
          ∀ xs :
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({σ n} : Finset ℕ)
              (fun m => if m = σ n then b else i) N,
            evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 := by
    intro N
    exact hCarrierTransport i b (σ n) n N hbi
  simpa using
    (measure_start_inter_rowSuccessorValueEvent_eq_of_evidencePreservingEquiv_start
      (k := k) μ hμ P hExt i a b (σ n) n hbi hEquiv)

/-- For fixed start state and row index, the start-restricted row-successor value
events partition the start event across successor values. -/
lemma sum_start_inter_rowSuccessorValueEvent_eq_start
    (P : Measure (ℕ → Fin k))
    (i a : Fin k) (n : ℕ) :
    (∑ b : Fin k,
      P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i n b))
      =
    P ({ω : ℕ → Fin k | ω 0 = a}) := by
  let s : Set (ℕ → Fin k) := {ω : ℕ → Fin k | ω 0 = a}
  let ν : Measure (Fin k) :=
    Measure.map (fun ω : ℕ → Fin k => rowSuccessorAtNthVisit (k := k) i n ω) (P.restrict s)
  have hsum_restrict :
      (∑ b : Fin k, (P.restrict s) (rowSuccessorValueEvent (k := k) i n b))
        =
      (P.restrict s) Set.univ := by
    calc
      (∑ b : Fin k, (P.restrict s) (rowSuccessorValueEvent (k := k) i n b))
          =
        (∑ b : Fin k, ν ({b} : Set (Fin k))) := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          symm
          exact
            (Measure.map_apply
              (μ := P.restrict s)
              (f := fun ω : ℕ → Fin k => rowSuccessorAtNthVisit (k := k) i n ω)
              (s := ({b} : Set (Fin k)))
              (measurable_rowSuccessorAtNthVisit (k := k) i n)
              (MeasurableSet.singleton b))
      _ = ν Set.univ := by
        calc
          (∑ b : Fin k, ν ({b} : Set (Fin k))) = ν (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
            exact
              (sum_measure_singleton
                (μ := ν)
                (s := (Finset.univ : Finset (Fin k))))
          _ = ν Set.univ := by simp
      _ = (P.restrict s) Set.univ := by
        change
          (Measure.map (fun ω : ℕ → Fin k => rowSuccessorAtNthVisit (k := k) i n ω)
            (P.restrict s)) Set.univ = (P.restrict s) Set.univ
        exact
          (Measure.map_apply
            (μ := P.restrict s)
            (f := fun ω : ℕ → Fin k => rowSuccessorAtNthVisit (k := k) i n ω)
            (s := Set.univ)
            (measurable_rowSuccessorAtNthVisit (k := k) i n)
            MeasurableSet.univ)
  have hs_univ : (P.restrict s) Set.univ = P s := by
    rw [Measure.restrict_apply (μ := P) (s := s) (t := Set.univ) MeasurableSet.univ]
    simp
  calc
    (∑ b : Fin k,
      P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i n b))
        =
      (∑ b : Fin k, (P.restrict s) (rowSuccessorValueEvent (k := k) i n b)) := by
        refine Finset.sum_congr rfl ?_
        intro b hb
        change
          P (s ∩ rowSuccessorValueEvent (k := k) i n b)
            =
          (P.restrict s) (rowSuccessorValueEvent (k := k) i n b)
        symm
        simpa [Set.inter_comm] using
          (Measure.restrict_apply
            (μ := P)
            (s := s)
            (t := rowSuccessorValueEvent (k := k) i n b)
            (measurableSet_rowSuccessorValueEvent (k := k) i n b))
    _ = (P.restrict s) Set.univ := hsum_restrict
    _ = P s := hs_univ
    _ = P ({ω : ℕ → Fin k | ω 0 = a}) := by simp [s]

/-- Diagonal (`b = i`) start-restricted row-successor permutation invariance
follows from the off-diagonal (`b ≠ i`) invariance by finite partition of
successor values. -/
theorem startRestrictedRowSuccessorPermInvariant_diagonal_of_offDiagonal
    (P : Measure (ℕ → Fin k))
    (hP : IsProbabilityMeasure P)
    (hOff :
      ∀ (i a b : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ), b ≠ i →
        P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i (σ n) b)
          =
        P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i n b)) :
    ∀ (i a : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ),
      P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i (σ n) i)
        =
      P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i n i) := by
  letI : IsProbabilityMeasure P := hP
  intro i a σ n
  let s : Set (ℕ → Fin k) := {ω : ℕ → Fin k | ω 0 = a}
  let Sσ : ENNReal :=
    Finset.sum ((Finset.univ : Finset (Fin k)).erase i)
      (fun b : Fin k =>
        P (s ∩ rowSuccessorValueEvent (k := k) i (σ n) b))
  let Sn : ENNReal :=
    Finset.sum ((Finset.univ : Finset (Fin k)).erase i)
      (fun b : Fin k =>
        P (s ∩ rowSuccessorValueEvent (k := k) i n b))
  have hsumσ :
      (∑ b : Fin k, P (s ∩ rowSuccessorValueEvent (k := k) i (σ n) b)) = P s :=
    sum_start_inter_rowSuccessorValueEvent_eq_start (k := k) P i a (σ n)
  have hsumn :
      (∑ b : Fin k, P (s ∩ rowSuccessorValueEvent (k := k) i n b)) = P s :=
    sum_start_inter_rowSuccessorValueEvent_eq_start (k := k) P i a n
  have hsumOff : Sσ = Sn := by
    refine Finset.sum_congr rfl ?_
    intro b hb
    exact hOff i a b σ n (Finset.mem_erase.mp hb).1
  have hdecompσ :
      Sσ + P (s ∩ rowSuccessorValueEvent (k := k) i (σ n) i) = P s := by
    calc
      Sσ + P (s ∩ rowSuccessorValueEvent (k := k) i (σ n) i)
          =
        (∑ b : Fin k, P (s ∩ rowSuccessorValueEvent (k := k) i (σ n) b)) := by
          simpa [Sσ, add_comm, add_left_comm, add_assoc] using
            (Finset.sum_erase_add
              (s := (Finset.univ : Finset (Fin k)))
              (a := i)
              (f := fun b : Fin k =>
                P (s ∩ rowSuccessorValueEvent (k := k) i (σ n) b))
              (by simp : i ∈ (Finset.univ : Finset (Fin k))))
      _ = P s := hsumσ
  have hdecompn :
      Sn + P (s ∩ rowSuccessorValueEvent (k := k) i n i) = P s := by
    calc
      Sn + P (s ∩ rowSuccessorValueEvent (k := k) i n i)
          =
        (∑ b : Fin k, P (s ∩ rowSuccessorValueEvent (k := k) i n b)) := by
          simpa [Sn, add_comm, add_left_comm, add_assoc] using
            (Finset.sum_erase_add
              (s := (Finset.univ : Finset (Fin k)))
              (a := i)
              (f := fun b : Fin k =>
                P (s ∩ rowSuccessorValueEvent (k := k) i n b))
              (by simp : i ∈ (Finset.univ : Finset (Fin k))))
      _ = P s := hsumn
  have hSσ_ne_top : Sσ ≠ ⊤ := by
    unfold Sσ
    exact
      (ENNReal.sum_ne_top).2 (by
        intro b hb
        exact measure_ne_top P (s ∩ rowSuccessorValueEvent (k := k) i (σ n) b))
  have hSn_ne_top : Sn ≠ ⊤ := by
    unfold Sn
    exact
      (ENNReal.sum_ne_top).2 (by
        intro b hb
        exact measure_ne_top P (s ∩ rowSuccessorValueEvent (k := k) i n b))
  have hdiagσ :
      P (s ∩ rowSuccessorValueEvent (k := k) i (σ n) i) = P s - Sσ := by
    exact ENNReal.eq_sub_of_add_eq hSσ_ne_top (by simpa [add_comm] using hdecompσ)
  have hdiagn :
      P (s ∩ rowSuccessorValueEvent (k := k) i n i) = P s - Sn := by
    exact ENNReal.eq_sub_of_add_eq hSn_ne_top (by simpa [add_comm] using hdecompn)
  calc
    P (s ∩ rowSuccessorValueEvent (k := k) i (σ n) i) = P s - Sσ := hdiagσ
    _ = P s - Sn := by simp [hsumOff]
    _ = P (s ∩ rowSuccessorValueEvent (k := k) i n i) := hdiagn.symm

/-- Promote off-diagonal start-restricted row-successor permutation invariance
to full start-restricted invariance by filling the diagonal case. -/
theorem startRestrictedRowSuccessorPermInvariant_of_offDiagonal
    (P : Measure (ℕ → Fin k))
    (hP : IsProbabilityMeasure P)
    (hOff :
      ∀ (i a b : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ), b ≠ i →
        P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i (σ n) b)
          =
        P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i n b)) :
    StartRestrictedRowSuccessorPermInvariant (k := k) P := by
  intro i a b σ n
  by_cases hbi : b ≠ i
  · exact hOff i a b σ n hbi
  · have hbeq : b = i := not_ne_iff.mp hbi
    subst b
    exact
      startRestrictedRowSuccessorPermInvariant_diagonal_of_offDiagonal
        (k := k) P hP hOff i a σ n

/-- Merge finite-prefix extension transport with the diagonal completion step:
carrier transport assumptions for off-diagonal values are enough to obtain full
start-restricted row-successor permutation invariance. -/
theorem startRestrictedRowSuccessorPermInvariant_of_extension_transport
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hP : IsProbabilityMeasure P)
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hCarrierTransport :
      ∀ (i b : Fin k) (n n' N : ℕ), b ≠ i →
        ∃ e :
          rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
            (fun m => if m = n then b else i) N ≃
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n'} : Finset ℕ)
              (fun m => if m = n' then b else i) N,
          ∀ xs :
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
              (fun m => if m = n then b else i) N,
            evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    StartRestrictedRowSuccessorPermInvariant (k := k) P := by
  apply startRestrictedRowSuccessorPermInvariant_of_offDiagonal (k := k) P hP
  intro i a b σ n hbi
  exact
    startRestrictedRowSuccessorPermInvariant_offDiagonal_of_extension_transport
      (k := k) μ hμ P hExt hCarrierTransport i a b σ n hbi

/-- Strong-recurrence wrapper for the extension-transport route.
The transport proof itself uses only extension/cylinder transport and
probability normalization; strong recurrence can be threaded at composition
sites that require it. -/
theorem startRestrictedRowSuccessorPermInvariant_of_extension_transport_strongRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hP : IsProbabilityMeasure P)
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (_hStrong : StrongRecurrence (k := k) P)
    (hCarrierTransport :
      ∀ (i b : Fin k) (n n' N : ℕ), b ≠ i →
        ∃ e :
          rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
            (fun m => if m = n then b else i) N ≃
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n'} : Finset ℕ)
              (fun m => if m = n' then b else i) N,
          ∀ xs :
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
              (fun m => if m = n then b else i) N,
            evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    StartRestrictedRowSuccessorPermInvariant (k := k) P := by
  exact
    startRestrictedRowSuccessorPermInvariant_of_extension_transport
      (k := k) μ hμ P hP hExt hCarrierTransport

/-- Finite start-state partition of an event. -/
lemma sum_start_inter_eq_measure
    (P : Measure (ℕ → Fin k))
    (E : Set (ℕ → Fin k)) :
    (∑ a : Fin k, P ({ω : ℕ → Fin k | ω 0 = a} ∩ E)) = P E := by
  let ν : Measure (Fin k) := Measure.map (fun ω : ℕ → Fin k => ω 0) (P.restrict E)
  have hsumν : (∑ a : Fin k, ν ({a} : Set (Fin k))) = ν Set.univ := by
    calc
      (∑ a : Fin k, ν ({a} : Set (Fin k))) = ν (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
        exact
          (sum_measure_singleton (μ := ν) (s := (Finset.univ : Finset (Fin k))))
      _ = ν Set.univ := by simp
  have hνuniv : ν Set.univ = (P.restrict E) Set.univ := by
    change
      (Measure.map (fun ω : ℕ → Fin k => ω 0) (P.restrict E)) Set.univ = (P.restrict E) Set.univ
    exact
      (Measure.map_apply
        (μ := P.restrict E)
        (f := fun ω : ℕ → Fin k => ω 0)
        (s := Set.univ)
        (measurable_pi_apply 0)
        MeasurableSet.univ)
  have hrestrict_univ : (P.restrict E) Set.univ = P E := by
    rw [Measure.restrict_apply (μ := P) (s := E) (t := Set.univ) MeasurableSet.univ]
    simp
  have hνa :
      ∀ a : Fin k, ν ({a} : Set (Fin k)) = P ({ω : ℕ → Fin k | ω 0 = a} ∩ E) := by
    intro a
    have hstart_meas : MeasurableSet ({ω : ℕ → Fin k | ω 0 = a}) := by
      change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' Set.singleton a)
      exact (measurable_pi_apply 0) (MeasurableSet.singleton a)
    calc
      ν ({a} : Set (Fin k))
          =
        (P.restrict E) ((fun ω : ℕ → Fin k => ω 0) ⁻¹' ({a} : Set (Fin k))) := by
          simpa [ν] using
            (Measure.map_apply
              (μ := P.restrict E)
              (f := fun ω : ℕ → Fin k => ω 0)
              (s := ({a} : Set (Fin k)))
              (measurable_pi_apply 0)
              (MeasurableSet.singleton a))
      _ = (P.restrict E) ({ω : ℕ → Fin k | ω 0 = a}) := by rfl
      _ = P ({ω : ℕ → Fin k | ω 0 = a} ∩ E) := by
            simpa [Set.inter_comm] using
              (Measure.restrict_apply
                (μ := P)
                (s := E)
                (t := {ω : ℕ → Fin k | ω 0 = a})
                hstart_meas)
  calc
    (∑ a : Fin k, P ({ω : ℕ → Fin k | ω 0 = a} ∩ E))
        = (∑ a : Fin k, ν ({a} : Set (Fin k))) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            exact (hνa a).symm
    _ = ν Set.univ := hsumν
    _ = (P.restrict E) Set.univ := hνuniv
    _ = P E := hrestrict_univ

/-- Start-restricted row-successor permutation invariance implies the global
row-successor single-coordinate permutation invariance. -/
theorem rowSuccessorValueEvent_permInvariant_of_startRestricted
    (P : Measure (ℕ → Fin k))
    (hStart : StartRestrictedRowSuccessorPermInvariant (k := k) P)
    (i b : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) :
    P (rowSuccessorValueEvent (k := k) i (σ n) b)
      =
    P (rowSuccessorValueEvent (k := k) i n b) := by
  let Eσ : Set (ℕ → Fin k) := rowSuccessorValueEvent (k := k) i (σ n) b
  let En : Set (ℕ → Fin k) := rowSuccessorValueEvent (k := k) i n b
  have hEσ_meas : MeasurableSet Eσ := by
    simpa [Eσ] using measurableSet_rowSuccessorValueEvent (k := k) i (σ n) b
  have hEn_meas : MeasurableSet En := by
    simpa [En] using measurableSet_rowSuccessorValueEvent (k := k) i n b
  calc
    P Eσ = ∑ a : Fin k, P ({ω : ℕ → Fin k | ω 0 = a} ∩ Eσ) := by
      symm
      exact sum_start_inter_eq_measure (k := k) P Eσ
    _ = ∑ a : Fin k, P ({ω : ℕ → Fin k | ω 0 = a} ∩ En) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      simpa [Eσ, En] using hStart i a b σ n
    _ = P En := sum_start_inter_eq_measure (k := k) P En

/-- Coordinate-event row-process permutation invariance from
start-restricted row-successor permutation invariance. -/
theorem rowProcessLaw_coord_permInvariant_of_startRestricted
    (P : Measure (ℕ → Fin k))
    (hStart : StartRestrictedRowSuccessorPermInvariant (k := k) P)
    (i b : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) :
    rowProcessLaw (k := k) P i ({r : ℕ → Fin k | r (σ n) = b})
      =
    rowProcessLaw (k := k) P i ({r : ℕ → Fin k | r n = b}) := by
  calc
    rowProcessLaw (k := k) P i ({r : ℕ → Fin k | r (σ n) = b})
        = P (rowSuccessorValueEvent (k := k) i (σ n) b) := by
            exact rowProcessLaw_apply_coord (k := k) P i b (σ n)
    _ = P (rowSuccessorValueEvent (k := k) i n b) := by
          exact rowSuccessorValueEvent_permInvariant_of_startRestricted
            (k := k) P hStart i b σ n
    _ = rowProcessLaw (k := k) P i ({r : ℕ → Fin k | r n = b}) := by
          exact (rowProcessLaw_apply_coord (k := k) P i b n).symm

/-- Start-restricted row-successor permutation invariance from successor-matrix PE
on each start-restricted law. -/
theorem startRestrictedRowSuccessorPermInvariant_of_successorMatrixPE_restrict
    (P : Measure (ℕ → Fin k))
    (hPE_restrict :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a})) :
    StartRestrictedRowSuccessorPermInvariant (k := k) P := by
  intro i a b σ n
  let s : Set (ℕ → Fin k) := {ω : ℕ → Fin k | ω 0 = a}
  let Eσ : Set (ℕ → Fin k) := rowSuccessorValueEvent (k := k) i (σ n) b
  let En : Set (ℕ → Fin k) := rowSuccessorValueEvent (k := k) i n b
  have hperm_restrict : (P.restrict s) Eσ = (P.restrict s) En := by
    simpa [s, Eσ, En] using
      rowSuccessorValueEvent_permInvariant_of_successorMatrixPE
        (k := k) (P := P.restrict s) (hPE_restrict a) i b σ n
  have hEσ_meas : MeasurableSet Eσ := by
    simpa [Eσ] using measurableSet_rowSuccessorValueEvent (k := k) i (σ n) b
  have hEn_meas : MeasurableSet En := by
    simpa [En] using measurableSet_rowSuccessorValueEvent (k := k) i n b
  have hEσ_restrict : (P.restrict s) Eσ = P (s ∩ Eσ) := by
    simpa [Set.inter_comm] using
      (Measure.restrict_apply (μ := P) (s := s) (t := Eσ) hEσ_meas)
  have hEn_restrict : (P.restrict s) En = P (s ∩ En) := by
    simpa [Set.inter_comm] using
      (Measure.restrict_apply (μ := P) (s := s) (t := En) hEn_meas)
  calc
    P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i (σ n) b)
        = P (s ∩ Eσ) := by simp [s, Eσ]
    _ = (P.restrict s) Eσ := hEσ_restrict.symm
    _ = (P.restrict s) En := hperm_restrict
    _ = P (s ∩ En) := hEn_restrict
    _ = P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i n b) := by
          simp [s, En]

/-- Internal builder output on a fixed extension `P`:
`rowKernel` carries the row-evaluation measurability, start-restricted row-law
factorization, `Fin 1` product-kernel measurability, and row-successor matrix
invariance used by the bridge pipeline. -/
def BuiltRowKernelOnExtension
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) : Prop :=
  (∀ i : Fin k, ∀ b : Fin k,
      AEMeasurable
        (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
        (rowProcessLaw (k := k) P i)) ∧
  StartRestrictedRowKernelData (k := k) P rowKernel ∧
  (∀ i : Fin k,
      AEMeasurable
        (fun r : ℕ → Fin k =>
          Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
        (rowProcessLaw (k := k) P i)) ∧
  RowSuccessorMatrixInvariance (k := k) P rowKernel

/-- Constructor into `BuiltRowKernelOnExtension` from the four explicit
components used by the bridge pipeline. -/
theorem builtRowKernelOnExtension_of_components
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hstart : StartRestrictedRowKernelData (k := k) P rowKernel)
    (hPi :
      ∀ i : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) P i))
    (hInv : RowSuccessorMatrixInvariance (k := k) P rowKernel) :
    BuiltRowKernelOnExtension (k := k) P rowKernel := by
  exact ⟨hEval, hstart, hPi, hInv⟩

/-- Constructor into `BuiltRowKernelOnExtension` that derives the `Fin 1`
product-kernel AE-measurability field from singleton-evaluation AE-measurability,
under completeness of each row-process law. -/
theorem builtRowKernelOnExtension_of_components_of_complete
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hstart : StartRestrictedRowKernelData (k := k) P rowKernel)
    (hComplete : ∀ i : Fin k, (rowProcessLaw (k := k) P i).IsComplete)
    (hInv : RowSuccessorMatrixInvariance (k := k) P rowKernel) :
    BuiltRowKernelOnExtension (k := k) P rowKernel := by
  refine ⟨hEval, hstart, ?_, hInv⟩
  exact hPi_of_hEval_of_complete (k := k) P rowKernel hEval hComplete

/-- Row-successor matrix invariance upgrades to full shared latent-transition
coherence by adding the `[]` and singleton `[a]` base cases. -/
theorem sharedLatentTransitionCoherence_of_rowSuccessorMatrixInvariance
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hInv : RowSuccessorMatrixInvariance (k := k) P rowKernel) :
    SharedLatentTransitionCoherence (k := k) P rowKernel := by
  intro xs
  cases xs with
  | nil =>
    have hcylNil :
        MarkovDeFinettiRecurrence.cylinder (k := k) ([] : List (Fin k)) = Set.univ := by
      ext ω
      simp [MarkovDeFinettiRecurrence.cylinder]
    calc
      P (MarkovDeFinettiRecurrence.cylinder (k := k) [])
          = P Set.univ := by simp [hcylNil]
      _ = 1 := by simp
      _ = ∫⁻ ω, (1 : ENNReal) ∂P := by simp
      _ =
        ∫⁻ ω, wordProb (k := k)
          (rowKernelToMarkovParam (k := k)
            (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
            (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) [] ∂P := by
              simp [wordProb, wordProbNN]
  | cons a xs =>
    cases xs with
    | nil =>
      let s : Set (ℕ → Fin k) := {ω | ω 0 = a}
      let ind : (ℕ → Fin k) → ENNReal := s.indicator (fun _ => (1 : ENNReal))
      have hmeas_s : MeasurableSet s := by
        change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' Set.singleton a)
        exact (measurable_pi_apply 0) (MeasurableSet.singleton a)
      have hcyl :
          MarkovDeFinettiRecurrence.cylinder (k := k) [a] = s := by
        ext ω
        simp [MarkovDeFinettiRecurrence.cylinder, s]
      calc
        P (MarkovDeFinettiRecurrence.cylinder (k := k) [a]) = P s := by
          simp [hcyl]
        _ = ∫⁻ ω, ind ω ∂P := by
          have hlin : ∫⁻ ω, ind ω ∂P = P s := by
            exact (lintegral_indicator_one (μ := P) (s := s) hmeas_s)
          exact hlin.symm
        _ =
          ∫⁻ ω, wordProb (k := k)
            (rowKernelToMarkovParam (k := k)
              (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
              (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) [a] ∂P := by
                refine lintegral_congr_ae ?_
                filter_upwards with ω
                by_cases hω : ω 0 = a
                · have hmem : a ∈ (Set.singleton a : Set (Fin k)) := Set.mem_singleton a
                  simp [rowKernelToMarkovParam, wordProb, wordProbNN, wordProbAux, initProb, s, ind,
                    Set.indicator, hω, hmem]
                · have hmem : ω 0 ∉ (Set.singleton a : Set (Fin k)) := by
                    intro hmem'
                    exact hω hmem'
                  simp [rowKernelToMarkovParam, wordProb, wordProbNN, wordProbAux, initProb, s, ind,
                    Set.indicator, hω, hmem]
    | cons b rest =>
      exact hInv (a :: b :: rest) (by simp)

/-- Convert extension-level built row-kernel data into crux data by upgrading
row-successor matrix invariance to shared latent-transition coherence. -/
theorem rowKernelCruxData_of_builtRowKernelOnExtension
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hbuilt : BuiltRowKernelOnExtension (k := k) P rowKernel) :
    RowKernelCruxData (k := k) P rowKernel := by
  rcases hbuilt with ⟨hEval, hstart, hPi, hInv⟩
  have hcoh :
      SharedLatentTransitionCoherence (k := k) P rowKernel :=
    sharedLatentTransitionCoherence_of_rowSuccessorMatrixInvariance
      (k := k) P rowKernel hInv
  exact rowKernelCruxData_of_startData_and_sharedLatentCoherence
    (k := k) P rowKernel hEval hstart hPi hcoh

/-- Built extension-level row-kernel payload implies cross-anchor product identity. -/
theorem crossAnchorProductIdentity_of_builtRowKernelOnExtension
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hbuilt : BuiltRowKernelOnExtension (k := k) P rowKernel) :
    CrossAnchorProductIdentity (k := k) P rowKernel := by
  exact
    crossAnchorProductIdentity_of_rowKernelData
      (k := k) P rowKernel
      (rowKernelCruxData_of_builtRowKernelOnExtension
        (k := k) P rowKernel hbuilt)

/-- Built extension-level row-kernel payload implies cylinder-word mixing identity. -/
theorem cylinderMixingIdentity_P_of_builtRowKernelOnExtension
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hbuilt : BuiltRowKernelOnExtension (k := k) P rowKernel) :
    CylinderMixingIdentity_P (k := k) P rowKernel := by
  exact
    cylinderMixingIdentity_P_of_crossAnchorProductIdentity
      (k := k) P rowKernel
      (crossAnchorProductIdentity_of_builtRowKernelOnExtension
        (k := k) P rowKernel hbuilt)

/-- Extension-level reconstruction from row-kernel singleton-eval AE-measurability
and cross-anchor product identity. -/
theorem exists_markovParamLaw_of_hEval_and_crossAnchor
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hcross : CrossAnchorProductIdentity (k := k) P rowKernel) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), P (cylinder (k := k) xs) = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  have hθ :=
    aemeasurable_rowKernelToMarkovParam_diracInit_lifted P rowKernel hEval
  have hCM :=
    cylinderMixingIdentity_P_of_crossAnchorProductIdentity
      (k := k) P rowKernel hcross
  have hall :=
    rowKernelToMarkovParamLaw_reconstruction_all_diracInit_of_lifted_rowKernel
      (k := k) P rowKernel hθ hCM
  set law := rowKernelToMarkovParamLaw (k := k) P
      (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
      (liftedRowKernelFromRowProcess (k := k) rowKernel) with hlaw_def
  have hlaw_prob : IsProbabilityMeasure law :=
    Measure.isProbabilityMeasure_map (f := rowKernelToMarkovParam (k := k)
      (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
      (liftedRowKernelFromRowProcess (k := k) rowKernel)) hθ
  refine ⟨law, hlaw_prob, ?_⟩
  intro xs
  exact hall xs

/-- Extension-level reconstruction from singleton-eval AE-measurability and
row-successor-matrix invariance (without start-restricted factorization
assumptions). -/
theorem exists_markovParamLaw_of_hEval_and_rowSuccessorMatrixInvariance
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hInv : RowSuccessorMatrixInvariance (k := k) P rowKernel) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), P (cylinder (k := k) xs) = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  have hcross : CrossAnchorProductIdentity (k := k) P rowKernel :=
    crossAnchorProductIdentity_of_rowSuccessorMatrixInvariance
      (k := k) P rowKernel hInv
  exact exists_markovParamLaw_of_hEval_and_crossAnchor
    (k := k) P rowKernel hEval hcross

/-- Bridge skeleton (subgoals separated):
extract a recurrent extension `P` from recurrence, then ask for row-kernel
construction on that extension with row-successor matrix invariance; finally
upgrade to shared latent coherence. -/
def BuildRowKernelOnRecurrentExtension (k : ℕ) : Prop :=
  ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (_hP : IsProbabilityMeasure P)
    (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (_hrecAe : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = ω 0}),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
        BuiltRowKernelOnExtension (k := k) P rowKernel

/-- Canonical recurrence-level PE assumption (literature-facing):
Markov exchangeability + recurrence yield an extension `P` with successor-matrix
partial exchangeability. -/
def SuccessorMatrixPE_of_markovExchangeable_recurrent (k : ℕ) : Prop :=
  ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
    MarkovExchangeablePrefixMeasure (k := k) μ →
    MarkovRecurrentPrefixMeasure (k := k) μ →
      ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
        SuccessorMatrixPartialExchangeable (k := k) P

/-- Canonical PE→row-kernel constructor assumption (literature-facing):
from successor-matrix PE on a concrete extension `P`, construct a row-kernel
carrying the internal extension payload. -/
def ExistsBuiltRowKernel_of_successorMatrixPE (k : ℕ) : Prop :=
  ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P),
      SuccessorMatrixPartialExchangeable (k := k) P →
      ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
        BuiltRowKernelOnExtension (k := k) P rowKernel

/-- Minimal canonical PE→kernel payload for representation:
build a row-kernel with singleton-eval AE-measurability and row-successor
matrix invariance. This avoids exposing start-restricted factorization on the
public theorem surface. -/
def ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE (k : ℕ) : Prop :=
  ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P),
      SuccessorMatrixPartialExchangeable (k := k) P →
      ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
        (∀ i : Fin k, ∀ b : Fin k,
          AEMeasurable
            (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
            (rowProcessLaw (k := k) P i)) ∧
        RowSuccessorMatrixInvariance (k := k) P rowKernel

/-- Project the minimal canonical payload from the stronger built-kernel
constructor assumption. -/
theorem existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_builtRowKernel
    (hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k) :
    ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k := by
  intro P hP hPE
  rcases hBuildFromPE P hP hPE with ⟨rowKernel, hbuilt⟩
  rcases hbuilt with ⟨hEval, _hstart, _hPi, hInv⟩
  exact ⟨rowKernel, hEval, hInv⟩

@[deprecated SuccessorMatrixPE_of_markovExchangeable_recurrent (since := "2026-03-03")]
abbrev SuccessorMatrixPEBridgeTheorem (k : ℕ) : Prop :=
  SuccessorMatrixPE_of_markovExchangeable_recurrent k

@[deprecated ExistsBuiltRowKernel_of_successorMatrixPE (since := "2026-03-03")]
abbrev SuccessorMatrixPEToBuiltRowKernelOnExtension (k : ℕ) : Prop :=
  ExistsBuiltRowKernel_of_successorMatrixPE k

/-- Focused assembly theorem for the PE→builder step.
This isolates three concrete subgoals for a chosen row-kernel witness on `P`:
`hstart`, `hInv`, and payload assembly into `BuiltRowKernelOnExtension`. -/
theorem successorMatrixPEToBuiltRowKernelOnExtension_of_componentBuilders
    (hEvalPiFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)))
    (hStartFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel)
    (hInvFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowSuccessorMatrixInvariance (k := k) P rowKernel) :
    ExistsBuiltRowKernel_of_successorMatrixPE k := by
  intro P hP hPE
  rcases hEvalPiFromPE P hP hPE with ⟨rowKernel, hEval, hPi⟩
  have hstart : StartRestrictedRowKernelData (k := k) P rowKernel :=
    hStartFromPE P hP hPE rowKernel hEval hPi
  have hInv : RowSuccessorMatrixInvariance (k := k) P rowKernel :=
    hInvFromPE P hP hPE rowKernel hEval hPi
  exact ⟨rowKernel, builtRowKernelOnExtension_of_components (k := k) P rowKernel hEval hstart hPi hInv⟩

/-- Reduced PE→builder assembly: derive `hEval` and `hPi` directly from
successor-matrix PE, so only `hstart` and `hInv` remain as explicit
component assumptions. -/
theorem successorMatrixPEToBuiltRowKernelOnExtension_of_start_and_invariance
    (hk : 0 < k)
    (hStartFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel)
    (hInvFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowSuccessorMatrixInvariance (k := k) P rowKernel) :
    ExistsBuiltRowKernel_of_successorMatrixPE k := by
  apply successorMatrixPEToBuiltRowKernelOnExtension_of_componentBuilders (k := k)
  · intro P hP hPE
    letI : IsProbabilityMeasure P := hP
    exact exists_rowKernel_hEval_hPi_of_successorMatrixPE (k := k) hk P hPE
  · exact hStartFromPE
  · exact hInvFromPE

/-- Reduced-constructor assumptions imply the minimal canonical PE→kernel
payload by first building `BuiltRowKernelOnExtension` and then projecting
`hEval + RowSuccessorMatrixInvariance`. -/
theorem existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_start_and_invariance
    (hk : 0 < k)
    (hStartFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel)
    (hInvFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowSuccessorMatrixInvariance (k := k) P rowKernel) :
    ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k := by
  exact
    existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_builtRowKernel
      (k := k)
      (successorMatrixPEToBuiltRowKernelOnExtension_of_start_and_invariance
        (k := k) hk hStartFromPE hInvFromPE)

/-- Route-A local bridge on a fixed extension:
from successor-matrix partial exchangeability plus a builder assumption, obtain
an explicit row-kernel witness with cross-anchor product identity. -/
theorem exists_rowKernel_with_crossAnchor_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k)
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P) :
    ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
      BuiltRowKernelOnExtension (k := k) P rowKernel ∧
      CrossAnchorProductIdentity (k := k) P rowKernel := by
  rcases hBuildFromPE P inferInstance hPE with ⟨rowKernel, hbuilt⟩
  have hcross :
      CrossAnchorProductIdentity (k := k) P rowKernel :=
    crossAnchorProductIdentity_of_builtRowKernelOnExtension
      (k := k) P rowKernel hbuilt
  exact ⟨rowKernel, hbuilt, hcross⟩

/-- Strong-recurrence variant of the literature-facing theorem surface:
Markov exchangeability plus an extension with strong recurrence imply a Markov
mixture representation. -/
def FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence (k : ℕ) : Prop :=
  ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
    MarkovExchangeablePrefixMeasure (k := k) μ →
    (∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      StrongRecurrence (k := k) P) →
      ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
        ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi

/-- Strong-recurrence successor-matrix bridge assumption. -/
def SuccessorMatrixPE_of_markovExchangeable_strongRecurrence (k : ℕ) : Prop :=
  ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (P : Measure (ℕ → Fin k))
    (_hP : IsProbabilityMeasure P),
      MarkovExchangeablePrefixMeasure (k := k) μ →
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
      StrongRecurrence (k := k) P →
      SuccessorMatrixPartialExchangeable (k := k) P

/-- Route-A composition theorem:
if strong-recurrence Markov exchangeability yields successor-matrix PE, and PE
yields the internal row-kernel payload, then the strong-recurrence Fortini
theorem follows. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_successorMatrixPE
    (hPEStrong : SuccessorMatrixPE_of_markovExchangeable_strongRecurrence k)
    (hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  intro μ hμ hExtStrong
  rcases hExtStrong with ⟨P, hP, hExt, hStrong⟩
  have hPE : SuccessorMatrixPartialExchangeable (k := k) P :=
    hPEStrong μ P hP hμ hExt hStrong
  letI : IsProbabilityMeasure P := hP
  rcases exists_rowKernel_with_crossAnchor_of_successorMatrixPE
      (k := k) (P := P) hBuildFromPE hPE with ⟨rowKernel, hbuilt, hcross⟩
  rcases hbuilt with ⟨hEval, _, _, _⟩
  rcases exists_markovParamLaw_of_hEval_and_crossAnchor
      (k := k) (P := P) rowKernel hEval hcross with ⟨pi, hpi, hreprP⟩
  refine ⟨pi, hpi, ?_⟩
  intro xs
  rw [hExt xs]
  exact hreprP xs

/-- Strong-recurrence Route-A theorem with the minimal canonical PE→kernel
payload (`hEval + RowSuccessorMatrixInvariance`) instead of
`BuiltRowKernelOnExtension`. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_successorMatrixPE_minimal
    (hPEStrong : SuccessorMatrixPE_of_markovExchangeable_strongRecurrence k)
    (hKernelFromPE :
      ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  intro μ hμ hExtStrong
  rcases hExtStrong with ⟨P, hP, hExt, hStrong⟩
  have hPE : SuccessorMatrixPartialExchangeable (k := k) P :=
    hPEStrong μ P hP hμ hExt hStrong
  letI : IsProbabilityMeasure P := hP
  rcases hKernelFromPE P hP hPE with ⟨rowKernel, hEval, hInv⟩
  rcases exists_markovParamLaw_of_hEval_and_rowSuccessorMatrixInvariance
      (k := k) (P := P) rowKernel hEval hInv with ⟨pi, hpi, hreprP⟩
  refine ⟨pi, hpi, ?_⟩
  intro xs
  rw [hExt xs]
  exact hreprP xs

/-- Strong-recurrence Route-A theorem with reduced PE-builder assumptions:
`hEval`/`hPi` are derived from successor-matrix PE, leaving only the
start-restricted factorization and row-successor-matrix-invariance builders as
explicit downstream obligations. This isolates the honest post-PE interface for
the strong-recurrence route. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_successorMatrixPE_reduced
    (hk : 0 < k)
    (hPEStrong : SuccessorMatrixPE_of_markovExchangeable_strongRecurrence k)
    (hStartFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel)
    (hInvFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowSuccessorMatrixInvariance (k := k) P rowKernel) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  have hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k :=
    successorMatrixPEToBuiltRowKernelOnExtension_of_start_and_invariance
      (k := k) hk hStartFromPE hInvFromPE
  exact fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_successorMatrixPE
    (k := k) hPEStrong hBuildFromPE

/-- Row-wise recurrence corollary:
if we can bridge strong recurrence to successor-matrix PE and then extract the
minimal canonical PE→kernel payload, we obtain the Markov-mixture
representation directly from row-wise recurrence assumptions. -/
theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_successorMatrixPE_minimal
    (hPEStrong : SuccessorMatrixPE_of_markovExchangeable_strongRecurrence k)
    (hKernelFromPE :
      ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  rcases exists_extension_strongRecurrence_of_markovRowRecurrent (k := k) μ hrow with
    ⟨P, hP, hExt, hStrong⟩
  exact
    (fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_successorMatrixPE_minimal
      (k := k) hPEStrong hKernelFromPE) μ hμ ⟨P, hP, hExt, hStrong⟩

/- Canonical target path:
`SuccessorMatrixPE_of_markovExchangeable_recurrent` together with
`ExistsBuiltRowKernel_of_successorMatrixPE` implies the public
`FortiniSuccessorMatrixInvarianceTheorem`.
`BuildRowKernelOnRecurrentExtension` and `RecurrentLatentCoherenceBridgeTheorem`
remain internal staging interfaces. -/

/-- Assumption isolation for the recurrent builder path:
from recurrence/exchangeability we can extract an extension `P`; what remains
extra is exactly a local constructor from that extension data to a
`BuiltRowKernelOnExtension` witness. -/
theorem build_rowKernel_on_recurrent_extension
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hExtra :
      ∀ (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hrecAe : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = ω 0}),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            BuiltRowKernelOnExtension (k := k) P rowKernel) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
        BuiltRowKernelOnExtension (k := k) P rowKernel := by
  rcases recurrentExtensionData_of_markovRecurrent (k := k) μ hrec with ⟨P, hP, hExt, hrecAe⟩
  rcases hExtra P hP hExt hrecAe with ⟨rowKernel, hbuilt⟩
  exact ⟨P, hP, hExt, rowKernel, hbuilt⟩

/-- Recurrence-to-latent-coherence bridge interface:
for recurrent Markov-exchangeable prefix laws, produce an extension `P` and a
row-kernel family carrying the internal extension-level builder payload. -/
def RecurrentLatentCoherenceBridgeTheorem (k : ℕ) : Prop :=
  ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
    MarkovExchangeablePrefixMeasure (k := k) μ →
    MarkovRecurrentPrefixMeasure (k := k) μ →
      ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
        ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          BuiltRowKernelOnExtension (k := k) P rowKernel

/-- Compose successor-matrix PE bridge assumptions into the recurrent-latent
coherence bridge used by the canonical Fortini theorem path. -/
theorem recurrentLatentCoherenceBridgeTheorem_of_successorMatrixPE_bridges
    (hPEBridge : SuccessorMatrixPE_of_markovExchangeable_recurrent k)
    (hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k) :
    RecurrentLatentCoherenceBridgeTheorem k := by
  intro μ hμ hrec
  rcases hPEBridge μ hμ hrec with ⟨P, hP, hExt, hPE⟩
  rcases hBuildFromPE P hP hPE with ⟨rowKernel, hbuilt⟩
  exact ⟨P, hP, hExt, rowKernel, hbuilt⟩

theorem recurrentLatentCoherenceBridgeTheorem_proved
    (hBuildOnRecurrentExtension : BuildRowKernelOnRecurrentExtension k) :
    RecurrentLatentCoherenceBridgeTheorem k := by
  intro μ hμ hrec
  rcases recurrentExtensionData_of_markovRecurrent (k := k) μ hrec with ⟨P, hP, hExt, hrecAe⟩
  rcases hBuildOnRecurrentExtension μ hμ P hP hExt hrecAe with ⟨rowKernel, hbuilt⟩
  exact ⟨P, hP, hExt, rowKernel, hbuilt⟩

/-- Build the literature-facing Fortini theorem from a recurrence-to-latent
coherence bridge. This is the canonical public interface for this file. -/
theorem fortiniSuccessorMatrixInvarianceTheorem_of_recurrentLatentCoherenceBridge
    (hBridge : RecurrentLatentCoherenceBridgeTheorem k) :
    FortiniSuccessorMatrixInvarianceTheorem k := by
  intro μ hμ hrec
  rcases hBridge μ hμ hrec with ⟨P, hP, hExt, rowKernel, hbuilt⟩
  letI : IsProbabilityMeasure P := hP
  have hcross :
      CrossAnchorProductIdentity (k := k) P rowKernel :=
    crossAnchorProductIdentity_of_builtRowKernelOnExtension
      (k := k) P rowKernel hbuilt
  rcases hbuilt with ⟨hEval, hstart, hPi, hInv⟩
  rcases exists_markovParamLaw_of_hEval_and_crossAnchor
      (k := k) (P := P) rowKernel hEval hcross with ⟨pi, hpi, hreprP⟩
  refine ⟨pi, hpi, ?_⟩
  intro xs
  rw [hExt xs]
  exact hreprP xs

/-- Route-A composition for the literature-facing recurrence theorem:
successor-matrix bridge + builder bridge imply the public Fortini theorem.
This proof is direct and does not route through
`RecurrentLatentCoherenceBridgeTheorem`. -/
theorem fortiniSuccessorMatrixInvarianceTheorem_of_canonicalAssumptions
    (hPEBridge : SuccessorMatrixPE_of_markovExchangeable_recurrent k)
    (hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k) :
    FortiniSuccessorMatrixInvarianceTheorem k := by
  intro μ hμ hrec
  rcases hPEBridge μ hμ hrec with ⟨P, hP, hExt, hPE⟩
  letI : IsProbabilityMeasure P := hP
  rcases exists_rowKernel_with_crossAnchor_of_successorMatrixPE
      (k := k) (P := P) hBuildFromPE hPE with ⟨rowKernel, hbuilt, hcross⟩
  rcases hbuilt with ⟨hEval, _, _, _⟩
  rcases exists_markovParamLaw_of_hEval_and_crossAnchor
      (k := k) (P := P) rowKernel hEval hcross with ⟨pi, hpi, hreprP⟩
  refine ⟨pi, hpi, ?_⟩
  intro xs
  rw [hExt xs]
  exact hreprP xs

/-- Canonical recurrence theorem with minimal PE→kernel payload:
successor-matrix PE plus a row-kernel carrying `hEval` and
`RowSuccessorMatrixInvariance` yields the public Fortini representation. -/
theorem fortiniSuccessorMatrixInvarianceTheorem_of_canonicalAssumptions_minimal
    (hPEBridge : SuccessorMatrixPE_of_markovExchangeable_recurrent k)
    (hKernelFromPE :
      ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k) :
    FortiniSuccessorMatrixInvarianceTheorem k := by
  intro μ hμ hrec
  rcases hPEBridge μ hμ hrec with ⟨P, hP, hExt, hPE⟩
  letI : IsProbabilityMeasure P := hP
  rcases hKernelFromPE P hP hPE with ⟨rowKernel, hEval, hInv⟩
  rcases exists_markovParamLaw_of_hEval_and_rowSuccessorMatrixInvariance
      (k := k) (P := P) rowKernel hEval hInv with ⟨pi, hpi, hreprP⟩
  refine ⟨pi, hpi, ?_⟩
  intro xs
  rw [hExt xs]
  exact hreprP xs

/-- Canonical recurrence theorem route with reduced PE-builder assumptions:
`hEval`/`hPi` are derived from PE, leaving only start-restricted factorization
and row-successor matrix invariance constructors as explicit payload. -/
theorem fortiniSuccessorMatrixInvarianceTheorem_of_canonicalAssumptions_reduced
    (hk : 0 < k)
    (hPEBridge : SuccessorMatrixPE_of_markovExchangeable_recurrent k)
    (hStartFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel)
    (hInvFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowSuccessorMatrixInvariance (k := k) P rowKernel) :
    FortiniSuccessorMatrixInvarianceTheorem k := by
  have hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k :=
    successorMatrixPEToBuiltRowKernelOnExtension_of_start_and_invariance
      (k := k) hk hStartFromPE hInvFromPE
  exact fortiniSuccessorMatrixInvarianceTheorem_of_canonicalAssumptions
    (k := k) hPEBridge hBuildFromPE

@[deprecated fortiniSuccessorMatrixInvarianceTheorem_of_canonicalAssumptions
  (since := "2026-03-03")]
theorem fortiniSuccessorMatrixInvarianceTheorem_of_successorMatrixPE_bridges
    (hPEBridge : SuccessorMatrixPE_of_markovExchangeable_recurrent k)
    (hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k) :
    FortiniSuccessorMatrixInvarianceTheorem k :=
  fortiniSuccessorMatrixInvarianceTheorem_of_canonicalAssumptions
    (k := k) hPEBridge hBuildFromPE

/-- Unified bridge (Fortini + Solomonoff, finite alphabet):
from recurrent Markov exchangeability and a recurrent-latent-coherence bridge,
we get both:
1. Fortini's Markov-mixture representation, and
2. Solomonoff `M₂` finite-horizon log-loss regret bounds for the same prefix law. -/
theorem fortini_and_solomonoff_of_recurrentLatentCoherenceBridge
    (hBridge : RecurrentLatentCoherenceBridgeTheorem k)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hμLSC :
      Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.LowerSemicomputablePrefixMeasure
        (α := Fin k) μ) :
    (∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin k)) μ c ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin k)) n ≤
          Real.log (1 / c.toReal)) := by
  refine ⟨?_, ?_⟩
  · exact
      (fortiniSuccessorMatrixInvarianceTheorem_of_recurrentLatentCoherenceBridge
        (k := k) hBridge) μ hμ hrec
  · exact
      (markovExchangeable_summary_and_solomonoff_regret
        (k := k) (μ := μ) hμ hμLSC).2

/-- Unified canonical route (Fortini + Solomonoff, finite alphabet):
from canonical PE + row-kernel-construction assumptions we get both:
1. Fortini's Markov-mixture representation, and
2. Solomonoff `M₂` finite-horizon log-loss regret bounds. -/
theorem fortini_and_solomonoff_of_canonicalAssumptions
    (hPEBridge : SuccessorMatrixPE_of_markovExchangeable_recurrent k)
    (hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hμLSC :
      Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.LowerSemicomputablePrefixMeasure
        (α := Fin k) μ) :
    (∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin k)) μ c ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin k)) n ≤
          Real.log (1 / c.toReal)) := by
  refine ⟨?_, ?_⟩
  · exact
      (fortiniSuccessorMatrixInvarianceTheorem_of_canonicalAssumptions_minimal
        (k := k) hPEBridge
        (existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_builtRowKernel
          (k := k) hBuildFromPE)) μ hμ hrec
  · exact
      (markovExchangeable_summary_and_solomonoff_regret
        (k := k) (μ := μ) hμ hμLSC).2

/-- Unified minimal-canonical route (Fortini + Solomonoff, finite alphabet):
uses the smallest PE→kernel payload needed for representation. -/
theorem fortini_and_solomonoff_of_canonicalAssumptions_minimal
    (hPEBridge : SuccessorMatrixPE_of_markovExchangeable_recurrent k)
    (hKernelFromPE :
      ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hμLSC :
      Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.LowerSemicomputablePrefixMeasure
        (α := Fin k) μ) :
    (∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin k)) μ c ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin k)) n ≤
          Real.log (1 / c.toReal)) := by
  refine ⟨?_, ?_⟩
  · exact
      (fortiniSuccessorMatrixInvarianceTheorem_of_canonicalAssumptions_minimal
        (k := k) hPEBridge hKernelFromPE) μ hμ hrec
  · exact
      (markovExchangeable_summary_and_solomonoff_regret
        (k := k) (μ := μ) hμ hμLSC).2

/-- Unified reduced-canonical route (Fortini + Solomonoff, finite alphabet):
derive `hEval`/`hPi` from PE and keep only the start-factorization and
row-successor-matrix-invariance builders as explicit assumptions. -/
theorem fortini_and_solomonoff_of_canonicalAssumptions_reduced
    (hk : 0 < k)
    (hPEBridge : SuccessorMatrixPE_of_markovExchangeable_recurrent k)
    (hStartFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel)
    (hInvFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowSuccessorMatrixInvariance (k := k) P rowKernel)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hμLSC :
      Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.LowerSemicomputablePrefixMeasure
        (α := Fin k) μ) :
    (∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin k)) μ c ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin k)) n ≤
          Real.log (1 / c.toReal)) := by
  have hFortini : FortiniSuccessorMatrixInvarianceTheorem k :=
    fortiniSuccessorMatrixInvarianceTheorem_of_canonicalAssumptions_reduced
      (k := k) hk hPEBridge hStartFromPE hInvFromPE
  refine ⟨?_, ?_⟩
  · exact hFortini μ hμ hrec
  · exact
      (markovExchangeable_summary_and_solomonoff_regret
        (k := k) (μ := μ) hμ hμLSC).2


end MarkovDeFinettiHard
end Mettapedia.Logic
