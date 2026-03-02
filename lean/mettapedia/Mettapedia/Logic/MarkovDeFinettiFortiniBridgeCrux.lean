import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCore

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
      exact hstart (by simpa [Set.mem_singleton_iff] using hmem)
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
  intro i
  have hEvalAllMeas :
      ∀ j : Fin k, ∀ B : Set (Fin k), MeasurableSet B →
        Measurable (fun r : ℕ → Fin k => (rowKernel j r : Measure (Fin k)) B) := by
    intro j B hB
    letI : (rowProcessLaw (k := k) P j).IsComplete := hComplete j
    have hAE :
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel j r : Measure (Fin k)) B)
          (rowProcessLaw (k := k) P j) :=
      aemeasurable_rowKernel_eval_set_of_hEval_singletons
        (k := k) P rowKernel hEval j B hB
    exact (aemeasurable_iff_measurable (μ := rowProcessLaw (k := k) P j)).1 hAE
  exact hPi_of_measurable_eval (k := k) P rowKernel hEvalAllMeas i

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
            simpa [ind] using (lintegral_indicator_one (μ := P) (s := s) hmeas_s)
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
                    exact hω (by simpa [Set.mem_singleton_iff] using hmem')
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

/-- Successor-matrix bridge (recurrent-prefix level):
extract an extension and prove successor-matrix partial exchangeability. -/
def SuccessorMatrixPEBridgeTheorem (k : ℕ) : Prop :=
  ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
    MarkovExchangeablePrefixMeasure (k := k) μ →
    MarkovRecurrentPrefixMeasure (k := k) μ →
      ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
        SuccessorMatrixPartialExchangeable (k := k) P

/-- Builder adapter from successor-matrix PE to internal row-kernel payload. -/
def SuccessorMatrixPEToBuiltRowKernelOnExtension (k : ℕ) : Prop :=
  ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P),
      SuccessorMatrixPartialExchangeable (k := k) P →
      ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
        BuiltRowKernelOnExtension (k := k) P rowKernel

/-- Route-A local bridge on a fixed extension:
from successor-matrix partial exchangeability plus a builder assumption, obtain
an explicit row-kernel witness with cross-anchor product identity. -/
theorem exists_rowKernel_with_crossAnchor_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hBuildFromPE : SuccessorMatrixPEToBuiltRowKernelOnExtension k)
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
    (hBuildFromPE : SuccessorMatrixPEToBuiltRowKernelOnExtension k) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  intro μ hμ hExtStrong
  rcases hExtStrong with ⟨P, hP, hExt, hStrong⟩
  have hPE : SuccessorMatrixPartialExchangeable (k := k) P :=
    hPEStrong μ P hP hμ hExt hStrong
  letI : IsProbabilityMeasure P := hP
  rcases exists_rowKernel_with_crossAnchor_of_successorMatrixPE
      (k := k) (P := P) hBuildFromPE hPE with ⟨rowKernel, hbuilt, hcross⟩
  rcases hbuilt with ⟨hEval, hstart, hPi, hInv⟩
  rcases exists_markovParamLaw_of_hEval_and_crossAnchor
      (k := k) (P := P) rowKernel hEval hcross with ⟨pi, hpi, hreprP⟩
  refine ⟨pi, hpi, ?_⟩
  intro xs
  rw [hExt xs]
  exact hreprP xs

/-
Canonical Fortini bridge surface used in this file:

1. `BuildRowKernelOnRecurrentExtension` is the only extra constructor assumption.
2. `RecurrentLatentCoherenceBridgeTheorem` packages the literature-facing extension claim.
3. `fortiniSuccessorMatrixInvarianceTheorem_of_recurrentLatentCoherenceBridge`
   is the final public theorem path.

Current derivation gap: constructing `rowKernel` with `BuiltRowKernelOnExtension`
from recurrence/exchangeability alone.
-/

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
    (hPEBridge : SuccessorMatrixPEBridgeTheorem k)
    (hBuildFromPE : SuccessorMatrixPEToBuiltRowKernelOnExtension k) :
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
successor-matrix bridge + builder bridge imply the public Fortini theorem. -/
theorem fortiniSuccessorMatrixInvarianceTheorem_of_successorMatrixPE_bridges
    (hPEBridge : SuccessorMatrixPEBridgeTheorem k)
    (hBuildFromPE : SuccessorMatrixPEToBuiltRowKernelOnExtension k) :
    FortiniSuccessorMatrixInvarianceTheorem k := by
  have hBridge :
      RecurrentLatentCoherenceBridgeTheorem k :=
    recurrentLatentCoherenceBridgeTheorem_of_successorMatrixPE_bridges
      (k := k) hPEBridge hBuildFromPE
  exact
    fortiniSuccessorMatrixInvarianceTheorem_of_recurrentLatentCoherenceBridge
      (k := k) hBridge

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


end MarkovDeFinettiHard
end Mettapedia.Logic
