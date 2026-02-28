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

/-- Adapter for start-restricted row-kernel finite-dimensional laws.

This is a typed projection helper: if start-restricted laws are available in the
row-kernel data package, expose them in the exact shape needed by the concrete
Cesàro theorem. -/
lemma hrow_restrict_of_rowKernelData
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hrow_restrict_data :
      ∀ (i a : Fin k), ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
          =
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k))))) :
    ∀ (i a : Fin k), ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
      Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
          (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
        =
      (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
        (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))) := by
  intro i a m sel hsel
  exact hrow_restrict_data i a m sel hsel

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

/-- Start-conditioned row-successor constancy interface:
the event mass `P({ω | ω 0 = a} ∩ rowSuccessorValueEvent i n b)` is constant in `n`. -/
def StartRowSuccessorConstancy
    (P : Measure (ℕ → Fin k)) (i a b : Fin k) : Prop :=
  ∃ c : ENNReal,
    ∀ n : ℕ,
      P ({ω : ℕ → Fin k | ω 0 = a} ∩
          rowSuccessorValueEvent (k := k) i n b) = c

/-- Start-conditioned Cesàro-limit interface:
the start-gated Cesàro average of row-successor indicators converges to the
start-gated row-kernel evaluation integral. -/
def StartRowSuccessorCesaroLimit
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (i a b : Fin k) : Prop :=
  Filter.Tendsto
    (fun N : ℕ =>
      ∫⁻ ω,
        (if ω 0 = a then
          ((↑(N + 1) : ENNReal)⁻¹ *
            Finset.sum (Finset.range (N + 1))
              (fun n => rowSuccessorValueIndicator (k := k) i n b ω))
          else 0) ∂P)
    Filter.atTop
    (nhds
      (∫⁻ ω,
        (if ω 0 = a then
          rowKernel i (rowSuccessorVisitProcess (k := k) i ω) ({b} : Set (Fin k))
          else 0) ∂P))

/-- From permutation invariance of start-conditioned row-successor events, obtain
constancy in the index `n`. -/
lemma start_rowSuccessorValueEvent_const_of_permInvariant
    (P : Measure (ℕ → Fin k))
    (i a b : Fin k)
    (hperm :
      ∀ (σ : Equiv.Perm ℕ) (n : ℕ),
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            rowSuccessorValueEvent (k := k) i (σ n) b)
          =
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            rowSuccessorValueEvent (k := k) i n b)) :
    StartRowSuccessorConstancy (k := k) P i a b := by
  refine ⟨P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i 0 b), ?_⟩
  intro n
  have h0n :
      P ({ω : ℕ → Fin k | ω 0 = a} ∩
          rowSuccessorValueEvent (k := k) i 0 b)
        =
      P ({ω : ℕ → Fin k | ω 0 = a} ∩
          rowSuccessorValueEvent (k := k) i n b) := by
    simpa using hperm (Equiv.swap n 0) n
  exact h0n.symm

/-- Markov-exchangeability-facing constancy wrapper.
The derivation currently consumes an explicit start-conditioned permutation
invariance hypothesis; `hμ/hExt` are included to match the Fortini bridge
interface. -/
lemma start_rowSuccessorValueEvent_const_of_markovExch
    (P : Measure (ℕ → Fin k))
    (_μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (_hμ : MarkovExchangeablePrefixMeasure (k := k) _μ)
    (_hExt : ∀ xs : List (Fin k), _μ xs = P (cylinder (k := k) xs))
    (i a b : Fin k)
    (hperm :
      ∀ (σ : Equiv.Perm ℕ) (n : ℕ),
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            rowSuccessorValueEvent (k := k) i (σ n) b)
          =
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            rowSuccessorValueEvent (k := k) i n b)) :
    ∃ c : ENNReal,
      ∀ n : ℕ,
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            rowSuccessorValueEvent (k := k) i n b) = c := by
  simpa [StartRowSuccessorConstancy] using
    start_rowSuccessorValueEvent_const_of_permInvariant (k := k) P i a b hperm

/-- Explicit Tendsto-form wrapper for the start-conditioned Cesàro-limit input. -/
lemma tendsto_lintegral_start_cesaro_rowSuccessorIndicator_to_rowKernel
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (i a b : Fin k)
    (hlim : StartRowSuccessorCesaroLimit (k := k) P rowKernel i a b) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∫⁻ ω,
          (if ω 0 = a then
            ((↑(N + 1) : ENNReal)⁻¹ *
              Finset.sum (Finset.range (N + 1))
                (fun n => rowSuccessorValueIndicator (k := k) i n b ω))
            else 0) ∂P)
      Filter.atTop
      (nhds
        (∫⁻ ω,
          (if ω 0 = a then
            rowKernel i (rowSuccessorVisitProcess (k := k) i ω) ({b} : Set (Fin k))
            else 0) ∂P)) :=
  hlim

/-- Restricted-measure version of the explicit Tendsto-form wrapper. -/
lemma tendsto_lintegral_start_cesaro_rowSuccessorIndicator_to_rowKernel_restrict
    (P : Measure (ℕ → Fin k))
    (S : Set (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (i a b : Fin k)
    (hlim : StartRowSuccessorCesaroLimit (k := k) (P.restrict S) rowKernel i a b) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∫⁻ ω,
          (if ω 0 = a then
            ((↑(N + 1) : ENNReal)⁻¹ *
              Finset.sum (Finset.range (N + 1))
                (fun n => rowSuccessorValueIndicator (k := k) i n b ω))
            else 0) ∂(P.restrict S))
      Filter.atTop
      (nhds
        (∫⁻ ω,
          (if ω 0 = a then
            rowKernel i (rowSuccessorVisitProcess (k := k) i ω) ({b} : Set (Fin k))
            else 0) ∂(P.restrict S))) :=
  hlim

/-- Specialization from restricted measure on `univ` to unrestricted `P`. -/
lemma startRowSuccessorCesaroLimit_of_restrict_univ
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (i a b : Fin k)
    (hlim :
      StartRowSuccessorCesaroLimit (k := k) (P.restrict Set.univ) rowKernel i a b) :
    StartRowSuccessorCesaroLimit (k := k) P rowKernel i a b := by
  simpa using hlim

/-- Prefix-carrier equivalence transport:
if two truncated row-visit events have evidence-preserving equivalent finite
prefix carriers, their start-conditioned probabilities agree. -/
theorem measure_start_inter_rowVisitCylinderEventUpTo_eq_of_evidencePreservingPrefixCarrierEquiv
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i₁ i₂ : Fin k)
    (S₁ S₂ : Finset ℕ)
    (v₁ v₂ : ℕ → Fin k)
    (N : ℕ)
    (e :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N ≃
        rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N)
    (he :
      ∀ xs :
        rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N,
        evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1)
    (j : Fin k) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowVisitCylinderEventUpTo (k := k) i₁ S₁ v₁ N) =
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowVisitCylinderEventUpTo (k := k) i₂ S₂ v₂ N) := by
  calc
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowVisitCylinderEventUpTo (k := k) i₁ S₁ v₁ N)
        =
      Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N)
        (fun xs =>
          if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) := by
            simpa using
              (measure_start_inter_rowVisitCylinderEventUpTo_eq_sum_prefixCylinders
                (k := k) P i₁ S₁ v₁ N j)
    _ =
      Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N)
        (fun ys =>
          if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0) := by
            exact
              sum_cylinderProb_eq_of_extension_and_evidencePreservingEquiv_start
                (k := k) μ hμ P hExt
                (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N)
                (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N)
                e he j
    _ =
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowVisitCylinderEventUpTo (k := k) i₂ S₂ v₂ N) := by
            simpa using
              (measure_start_inter_rowVisitCylinderEventUpTo_eq_sum_prefixCylinders
                (k := k) P i₂ S₂ v₂ N j).symm

/-- Upgrade truncated-equality (`UpTo`) to full row-successor event equality
under start conditioning, for the non-`none` branch (`a ≠ i`). -/
theorem measure_start_inter_rowSuccessorValueEvent_eq_of_upTo
    (P : Measure (ℕ → Fin k))
    (i : Fin k) (n₁ n₂ : ℕ) (a j : Fin k)
    (ha : a ≠ i)
    (hupTo :
      ∀ N : ℕ,
        P ({ω : ℕ → Fin k | ω 0 = j} ∩
            rowVisitCylinderEventUpTo (k := k) i {n₁}
              (fun m => if m = n₁ then a else i) N)
          =
        P ({ω : ℕ → Fin k | ω 0 = j} ∩
            rowVisitCylinderEventUpTo (k := k) i {n₂}
              (fun m => if m = n₂ then a else i) N)) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n₁ a)
      =
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n₂ a) := by
  let sN : ℕ → Set (ℕ → Fin k) := fun N =>
    {ω : ℕ → Fin k | ω 0 = j} ∩
      rowVisitCylinderEventUpTo (k := k) i {n₁}
        (fun m => if m = n₁ then a else i) N
  let tN : ℕ → Set (ℕ → Fin k) := fun N =>
    {ω : ℕ → Fin k | ω 0 = j} ∩
      rowVisitCylinderEventUpTo (k := k) i {n₂}
        (fun m => if m = n₂ then a else i) N
  have hsMono : Monotone sN := by
    intro N M hNM
    exact Set.inter_subset_inter_right _ ((rowVisitCylinderEventUpTo_mono (k := k) i {n₁}
      (fun m => if m = n₁ then a else i)) hNM)
  have htMono : Monotone tN := by
    intro N M hNM
    exact Set.inter_subset_inter_right _ ((rowVisitCylinderEventUpTo_mono (k := k) i {n₂}
      (fun m => if m = n₂ then a else i)) hNM)
  have hsUnion :
      {ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n₁ a = ⋃ N, sN N := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨hstart, hrow⟩
      rw [rowSuccessorValueEvent_eq_iUnion_upTo_of_ne (k := k) i n₁ a ha] at hrow
      rcases Set.mem_iUnion.mp hrow with ⟨N, hN⟩
      exact Set.mem_iUnion.mpr ⟨N, ⟨hstart, hN⟩⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨N, hN⟩
      rcases hN with ⟨hstart, hrowN⟩
      refine ⟨hstart, ?_⟩
      simpa [rowSuccessorValueEvent_eq_iUnion_upTo_of_ne (k := k) i n₁ a ha] using
        (Set.mem_iUnion.mpr ⟨N, hrowN⟩)
  have htUnion :
      {ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n₂ a = ⋃ N, tN N := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨hstart, hrow⟩
      rw [rowSuccessorValueEvent_eq_iUnion_upTo_of_ne (k := k) i n₂ a ha] at hrow
      rcases Set.mem_iUnion.mp hrow with ⟨N, hN⟩
      exact Set.mem_iUnion.mpr ⟨N, ⟨hstart, hN⟩⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨N, hN⟩
      rcases hN with ⟨hstart, hrowN⟩
      refine ⟨hstart, ?_⟩
      simpa [rowSuccessorValueEvent_eq_iUnion_upTo_of_ne (k := k) i n₂ a ha] using
        (Set.mem_iUnion.mpr ⟨N, hrowN⟩)
  have hsMeasure : P (⋃ N, sN N) = ⨆ N, P (sN N) := hsMono.measure_iUnion (μ := P)
  have htMeasure : P (⋃ N, tN N) = ⨆ N, P (tN N) := htMono.measure_iUnion (μ := P)
  have hiSupEq : (⨆ N, P (sN N)) = ⨆ N, P (tN N) := by
    refine iSup_congr ?_
    intro N
    exact hupTo N
  calc
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n₁ a)
        = P (⋃ N, sN N) := by simp [hsUnion]
    _ = ⨆ N, P (sN N) := hsMeasure
    _ = ⨆ N, P (tN N) := hiSupEq
    _ = P (⋃ N, tN N) := htMeasure.symm
    _ = P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n₂ a) := by
          simp [htUnion]

/-- Start-conditioned row-successor equality from a per-`N` evidence-preserving
equivalence between the two singleton-index prefix carriers. -/
theorem measure_start_inter_rowSuccessorValueEvent_eq_of_markovExch_prefixCarrierEquiv
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (n₁ n₂ : ℕ) (a j : Fin k)
    (ha : a ≠ i)
    (hcarrier :
      ∀ N : ℕ,
        ∃ e :
          rowVisitCylinderEventUpToPrefixCarrier (k := k) i {n₁}
            (fun m => if m = n₁ then a else i) N ≃
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i {n₂}
              (fun m => if m = n₂ then a else i) N,
          ∀ xs :
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i {n₁}
              (fun m => if m = n₁ then a else i) N,
            evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n₁ a)
      =
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n₂ a) := by
  refine measure_start_inter_rowSuccessorValueEvent_eq_of_upTo
    (k := k) P i n₁ n₂ a j ha ?_
  intro N
  rcases hcarrier N with ⟨eN, heN⟩
  exact
    measure_start_inter_rowVisitCylinderEventUpTo_eq_of_evidencePreservingPrefixCarrierEquiv
      (k := k) μ hμ P hExt
      i i
      {n₁} {n₂}
      (fun m => if m = n₁ then a else i)
      (fun m => if m = n₂ then a else i)
      N eN heN j

/-- Constancy corollary (start-conditioned): if every index `n` has a
prefix-carrier evidence-preserving equivalence to index `0`, then
`P({ω | ω 0 = a} ∩ rowSuccessorValueEvent i n b)` is constant in `n`
for `b ≠ i`. -/
theorem start_rowSuccessorValueEvent_const_of_markovExch_prefixCarrierEquiv
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i a b : Fin k)
    (hb : b ≠ i)
    (hcarrier0 :
      ∀ n N : ℕ,
        ∃ e :
          rowVisitCylinderEventUpToPrefixCarrier (k := k) i {n}
            (fun m => if m = n then b else i) N ≃
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i {0}
              (fun m => if m = 0 then b else i) N,
          ∀ xs :
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i {n}
              (fun m => if m = n then b else i) N,
            evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    ∃ c : ENNReal,
      ∀ n : ℕ,
        P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i n b) = c := by
  refine ⟨P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i 0 b), ?_⟩
  intro n
  exact
    measure_start_inter_rowSuccessorValueEvent_eq_of_markovExch_prefixCarrierEquiv
      (k := k) μ hμ P hExt i n 0 b a hb
      (fun N => hcarrier0 n N)

/-- Row-kernel-data constancy bridge (corrected public interface).

Uses start-conditioned permutation invariance directly. This avoids exposing the
too-strong finite-prefix carrier equivalence shape as the main API. -/
theorem start_constancy_of_rowKernelData
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hperm :
      ∀ (i a b : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ),
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            rowSuccessorValueEvent (k := k) i (σ n) b)
          =
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            rowSuccessorValueEvent (k := k) i n b)) :
    ∀ (i a b : Fin k), StartRowSuccessorConstancy (k := k) P i a b := by
  intro i a b
  simpa [StartRowSuccessorConstancy] using
    (start_rowSuccessorValueEvent_const_of_markovExch
      (k := k) P μ hμ hExt i a b (fun σ n => hperm i a b σ n))

/-- Cesàro-limit bridge in the current row-kernel data interface.

This is a typed pass-through: once a family of start-conditioned Cesàro limits
is available in the current `StartRowSuccessorCesaroLimit` form, expose it under
the full row-kernel-data signature. -/
theorem start_cesaroLimit_of_rowKernelData
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (_hrow :
      ∀ i : Fin k, ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) P i)
          =
        (rowProcessLaw (k := k) P i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))))
    (_hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hlim :
      ∀ (i a b : Fin k), StartRowSuccessorCesaroLimit (k := k) P rowKernel i a b) :
    ∀ (i a b : Fin k), StartRowSuccessorCesaroLimit (k := k) P rowKernel i a b := by
  intro i a b
  exact hlim i a b

/-- Concrete start-conditioned Cesàro-limit theorem from row-kernel data on start-restricted laws.

This avoids the pass-through `hlim` wrapper by proving the limit directly once the
row-process finite-dimensional law (`hrow_restrict`) is available under each
start-state restriction `P.restrict {ω | ω 0 = a}`.
-/
theorem startRowSuccessorCesaroLimit_of_rowKernelData
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (_hrow :
      ∀ i : Fin k, ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) P i)
          =
        (rowProcessLaw (k := k) P i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hrow_restrict :
      ∀ (i a : Fin k), ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
          =
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))))
    (hPi_restrict :
      ∀ (i a : Fin k),
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)) :
    ∀ (i a b : Fin k), StartRowSuccessorCesaroLimit (k := k) P rowKernel i a b := by
  intro i a b
  let s : Set (ℕ → Fin k) := {ω : ℕ → Fin k | ω 0 = a}
  let Q : Measure (ℕ → Fin k) := P.restrict s
  let L : ENNReal :=
    ∫⁻ ω,
      (if ω 0 = a then
        rowKernel i (rowSuccessorVisitProcess (k := k) i ω) ({b} : Set (Fin k)
        ) else 0) ∂P
  have hs : MeasurableSet s := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' Set.singleton a)
    exact (measurable_pi_apply 0) (MeasurableSet.singleton a)
  have hpre_event :
      ∀ n : ℕ,
        rowSuccessorValueEvent (k := k) i n b
          = (rowSuccessorVisitProcess (k := k) i) ⁻¹' {r : ℕ → Fin k | r n = b} := by
    intro n
    ext ω
    simp [rowSuccessorValueEvent, rowSuccessorAtNthVisit, rowSuccessorVisitProcess]
  have hleft_event :
      ∀ n : ℕ,
        Q (rowSuccessorValueEvent (k := k) i n b) =
          rowProcessLaw (k := k) Q i ({r : ℕ → Fin k | r n = b}) := by
    intro n
    have hset_meas : MeasurableSet ({r : ℕ → Fin k | r n = b} : Set (ℕ → Fin k)) := by
      change MeasurableSet ((fun r : ℕ → Fin k => r n) ⁻¹' Set.singleton b)
      exact (measurable_pi_apply n) (MeasurableSet.singleton b)
    calc
      Q (rowSuccessorValueEvent (k := k) i n b)
          = Q ((rowSuccessorVisitProcess (k := k) i) ⁻¹' {r : ℕ → Fin k | r n = b}) := by
              simp [hpre_event n]
      _ = rowProcessLaw (k := k) Q i ({r : ℕ → Fin k | r n = b}) := by
            symm
            simpa [rowProcessLaw] using
              (Measure.map_apply (μ := Q)
                (f := rowSuccessorVisitProcess (k := k) i)
                (s := ({r : ℕ → Fin k | r n = b} : Set (ℕ → Fin k)))
                (measurable_rowSuccessorVisitProcess (k := k) i) hset_meas)
  let R : ENNReal :=
    ∫⁻ r, (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k))
      ∂(rowProcessLaw (k := k) Q i)
  have hrow_singleton :
      ∀ n : ℕ,
        rowProcessLaw (k := k) Q i ({r : ℕ → Fin k | r n = b}) = R := by
    intro n
    have hselMono : StrictMono (fun _ : Fin 1 => n) := by
      intro x y hxy
      exfalso
      have hxy' : x = y := Subsingleton.elim x y
      exact (lt_irrefl _ (hxy' ▸ hxy))
    have hrow1 :=
      hrow_restrict i a 1 (fun _ : Fin 1 => n) hselMono
    have hrow1_eval :
        (Measure.map (fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => n) j))
            (rowProcessLaw (k := k) Q i)) ({x : Fin 1 → Fin k | x 0 = b})
          =
        ((rowProcessLaw (k := k) Q i).bind
          (fun r => Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k)))))
            ({x : Fin 1 → Fin k | x 0 = b}) := by
      exact congrArg (fun M => M ({x : Fin 1 → Fin k | x 0 = b})) hrow1
    have hset1_meas : MeasurableSet ({x : Fin 1 → Fin k | x 0 = b} : Set (Fin 1 → Fin k)) := by
      change MeasurableSet ((fun x : Fin 1 → Fin k => x 0) ⁻¹' Set.singleton b)
      exact (measurable_pi_apply 0) (MeasurableSet.singleton b)
    have hleft1 :
        (Measure.map (fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => n) j))
            (rowProcessLaw (k := k) Q i)) ({x : Fin 1 → Fin k | x 0 = b})
          =
        rowProcessLaw (k := k) Q i ({r : ℕ → Fin k | r n = b}) := by
      have hmeas_map :
          Measurable (fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => n) j)) := by
        exact measurable_pi_lambda _ (fun _ : Fin 1 => measurable_pi_apply n)
      calc
        (Measure.map (fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => n) j))
            (rowProcessLaw (k := k) Q i)) ({x : Fin 1 → Fin k | x 0 = b})
            =
          rowProcessLaw (k := k) Q i
            ((fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => n) j)) ⁻¹'
              ({x : Fin 1 → Fin k | x 0 = b})) := by
                simpa using
                  (Measure.map_apply
                    (μ := rowProcessLaw (k := k) Q i)
                    (f := fun r : ℕ → Fin k => fun j : Fin 1 => r ((fun _ : Fin 1 => n) j))
                    (s := ({x : Fin 1 → Fin k | x 0 = b} : Set (Fin 1 → Fin k)))
                    hmeas_map hset1_meas)
        _ = rowProcessLaw (k := k) Q i ({r : ℕ → Fin k | r n = b}) := by
              refine congrArg (fun t => rowProcessLaw (k := k) Q i t) ?_
              ext r
              simp
    have hright1 :
        ((rowProcessLaw (k := k) Q i).bind
          (fun r => Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k)))))
            ({x : Fin 1 → Fin k | x 0 = b}) = R := by
      calc
        ((rowProcessLaw (k := k) Q i).bind
          (fun r => Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k)))))
            ({x : Fin 1 → Fin k | x 0 = b})
            =
          ∫⁻ r,
            (Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              ({x : Fin 1 → Fin k | x 0 = b}) ∂(rowProcessLaw (k := k) Q i) := by
                exact Measure.bind_apply hset1_meas (hPi_restrict i a)
        _ =
          ∫⁻ r, (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k))
            ∂(rowProcessLaw (k := k) Q i) := by
              refine lintegral_congr_ae ?_
              filter_upwards with r
              have hset :
                  ({x : Fin 1 → Fin k | x 0 = b} : Set (Fin 1 → Fin k))
                    = Set.univ.pi (fun _ : Fin 1 => ({b} : Set (Fin k))) := by
                ext x
                simp [Set.pi]
              simp [hset, Measure.pi_pi]
        _ = R := rfl
    exact hleft1.symm.trans (hrow1_eval.trans hright1)
  have hR_to_L : R = L := by
    have hEvalQ :
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) Q i) := by
      simpa [Q] using
        (aemeasurable_rowKernel_eval_of_rowProcessLaw_restrict
          (k := k) P s rowKernel i b (hEval i b))
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
      R
          = ∫⁻ ω, (rowKernel i (rowSuccessorVisitProcess (k := k) i ω) : Measure (Fin k))
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
      _ = L := by
            simp [L, s, Set.indicator]
  have hconst :
      ∀ n : ℕ,
        P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i n b) = L := by
    intro n
    calc
      P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) i n b)
          = Q (rowSuccessorValueEvent (k := k) i n b) := by
              simp [Q, s, Measure.restrict_apply, measurableSet_rowSuccessorValueEvent,
                Set.inter_comm]
      _ = rowProcessLaw (k := k) Q i ({r : ℕ → Fin k | r n = b}) := hleft_event n
      _ = R := hrow_singleton n
      _ = L := hR_to_L
  have hconstIntegral :
      ∀ N : ℕ,
        ∫⁻ ω,
          (if ω 0 = a then
            ((↑(N + 1) : ENNReal)⁻¹ *
              Finset.sum (Finset.range (N + 1))
                (fun n => rowSuccessorValueIndicator (k := k) i n b ω))
            else 0) ∂P
          = L := by
    intro N
    exact lintegral_start_cesaro_eq_const (k := k) P i a b N L hconst
  unfold StartRowSuccessorCesaroLimit
  change Tendsto
    (fun N : ℕ =>
      ∫⁻ ω,
        (if ω 0 = a then
          ((↑(N + 1) : ENNReal)⁻¹ *
            Finset.sum (Finset.range (N + 1))
              (fun n => rowSuccessorValueIndicator (k := k) i n b ω))
          else 0) ∂P)
    Filter.atTop (nhds L)
  have hEventually :
      ∀ᶠ N : ℕ in Filter.atTop,
        (fun _ : ℕ => L) N
          =
        ∫⁻ ω,
          (if ω 0 = a then
            ((↑(N + 1) : ENNReal)⁻¹ *
              Finset.sum (Finset.range (N + 1))
                (fun n => rowSuccessorValueIndicator (k := k) i n b ω))
            else 0) ∂P := by
    exact Filter.Eventually.of_forall (fun N => (hconstIntegral N).symm)
  exact (tendsto_const_nhds.congr' hEventually)

/-- Pair-cylinder identity from the two crux inputs specialized at anchor `a`:
constancy + Cesàro-limit feed directly into
`pair_identity_of_constancy_and_cesaro_limit`. -/
theorem pair_cylinder_identity_of_startConstancy_and_cesaroLimit
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k)
    (hconst : StartRowSuccessorConstancy (k := k) P a a b)
    (hlim : StartRowSuccessorCesaroLimit (k := k) P rowKernel a a b) :
    P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b]) =
      ∫⁻ ω,
        (if ω 0 = a then
          rowKernel a (rowSuccessorVisitProcess (k := k) a ω) ({b} : Set (Fin k))
          else 0) ∂P := by
  rcases hconst with ⟨c, hconstN⟩
  have hpair :
      c =
        ∫⁻ ω,
          (if ω 0 = a then
            rowKernel a (rowSuccessorVisitProcess (k := k) a ω) ({b} : Set (Fin k))
            else 0) ∂P := by
    exact pair_identity_of_constancy_and_cesaro_limit
      (k := k) P a a b c
      (∫⁻ ω,
        (if ω 0 = a then
          rowKernel a (rowSuccessorVisitProcess (k := k) a ω) ({b} : Set (Fin k))
          else 0) ∂P)
      hconstN hlim
  calc
    P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b])
        = P ({ω : ℕ → Fin k | ω 0 = a} ∩
            rowSuccessorValueEvent (k := k) a 0 b) := by
            simpa using
              (measure_cylinder_pair_eq_start_and_rowSuccessorZero (k := k) P a b)
    _ = c := by simpa using hconstN 0
    _ =
      ∫⁻ ω,
        (if ω 0 = a then
          rowKernel a (rowSuccessorVisitProcess (k := k) a ω) ({b} : Set (Fin k))
          else 0) ∂P := hpair

/-- Length-2 cross-anchor identity package from the two crux inputs on every
anchor/target pair. This is the concrete pair-cylinder output consumed by the
Fortini pipeline before lifting to longer prefixes. -/
theorem crossAnchor_lengthTwo_of_startConstancy_and_cesaroLimit
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hconst :
      ∀ a b : Fin k, StartRowSuccessorConstancy (k := k) P a a b)
    (hlim :
      ∀ a b : Fin k, StartRowSuccessorCesaroLimit (k := k) P rowKernel a a b) :
    ∀ a b : Fin k,
      P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b]) =
        ∫⁻ ω,
          (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω [a, b] else 0) ∂P := by
  intro a b
  have hpair :=
    pair_cylinder_identity_of_startConstancy_and_cesaroLimit
      (k := k) P rowKernel a b (hconst a b) (hlim a b)
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

/-- Length-2 cylinder-wordProb identity from the crux A/B inputs on all pairs. -/
theorem cylinderMixingIdentity_P_lengthTwo_of_startConstancy_and_cesaroLimit
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hconst :
      ∀ a b : Fin k, StartRowSuccessorConstancy (k := k) P a a b)
    (hlim :
      ∀ a b : Fin k, StartRowSuccessorCesaroLimit (k := k) P rowKernel a a b) :
    ∀ a b : Fin k,
      P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b]) =
        ∫⁻ ω, wordProb (k := k)
          (rowKernelToMarkovParam (k := k)
            (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
            (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) [a, b] ∂P := by
  intro a b
  have hlen2 :=
    crossAnchor_lengthTwo_of_startConstancy_and_cesaroLimit
      (k := k) P rowKernel hconst hlim a b
  calc
    P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b])
        =
      ∫⁻ ω,
        (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω [a, b] else 0) ∂P := hlen2
    _ =
      ∫⁻ ω, wordProb (k := k)
        (rowKernelToMarkovParam (k := k)
          (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
          (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) [a, b] ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards with ω
      simpa using
        (wordProb_rowKernelToMarkovParam_eq_indicator_stepProd
          (k := k) rowKernel ω a b []).symm

/-- Concrete row-data pair identity:
combine start-conditioned constancy with the concrete Cesàro-limit theorem. -/
theorem pair_cylinder_identity_of_rowKernelData_concrete
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hconst :
      ∀ a b : Fin k, StartRowSuccessorConstancy (k := k) P a a b)
    (hrow :
      ∀ i : Fin k, ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) P i)
          =
        (rowProcessLaw (k := k) P i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hrow_restrict :
      ∀ (i a : Fin k), ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
          =
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))))
    (hPi_restrict :
      ∀ (i a : Fin k),
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)) :
    ∀ a b : Fin k,
      P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b]) =
        ∫⁻ ω,
          (if ω 0 = a then
            rowKernel a (rowSuccessorVisitProcess (k := k) a ω) ({b} : Set (Fin k))
            else 0) ∂P := by
  intro a b
  have hlim :
      StartRowSuccessorCesaroLimit (k := k) P rowKernel a a b :=
    (startRowSuccessorCesaroLimit_of_rowKernelData
      (k := k) P rowKernel hrow hEval hrow_restrict hPi_restrict) a a b
  exact
    pair_cylinder_identity_of_startConstancy_and_cesaroLimit
      (k := k) P rowKernel a b (hconst a b) hlim

/-- Concrete length-2 cross-anchor identity from row data, via concrete Cesàro limits. -/
theorem crossAnchor_lengthTwo_of_rowKernelData_concrete
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hconst :
      ∀ a b : Fin k, StartRowSuccessorConstancy (k := k) P a a b)
    (hrow :
      ∀ i : Fin k, ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) P i)
          =
        (rowProcessLaw (k := k) P i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hrow_restrict :
      ∀ (i a : Fin k), ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
          =
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))))
    (hPi_restrict :
      ∀ (i a : Fin k),
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)) :
    ∀ a b : Fin k,
      P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b]) =
        ∫⁻ ω,
          (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω [a, b] else 0) ∂P := by
  have hlim :
      ∀ a b : Fin k, StartRowSuccessorCesaroLimit (k := k) P rowKernel a a b := by
    intro a b
    exact
      (startRowSuccessorCesaroLimit_of_rowKernelData
        (k := k) P rowKernel hrow hEval hrow_restrict hPi_restrict) a a b
  exact
    crossAnchor_lengthTwo_of_startConstancy_and_cesaroLimit
      (k := k) P rowKernel hconst hlim

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

/-- Cross-anchor product identity from row-kernel data.

This is the remaining Fortini crux: deriving cross-anchor conditional
independence from per-anchor ConditionallyIID data and exchangeability. -/
theorem crossAnchorProductIdentity_of_rowKernelData
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hrow :
      ∀ i : Fin k, ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) P i)
          =
        (rowProcessLaw (k := k) P i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) :
    CrossAnchorProductIdentity (k := k) P rowKernel := by
  have hstepData :
      ∃ hperm :
          ∀ (i a b : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ),
            P ({ω : ℕ → Fin k | ω 0 = a} ∩
                rowSuccessorValueEvent (k := k) i (σ n) b)
              =
            P ({ω : ℕ → Fin k | ω 0 = a} ∩
                rowSuccessorValueEvent (k := k) i n b),
        ∃ hrow_restrict_data :
          ∀ (i a : Fin k), ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
            Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
                (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
              =
            (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
              (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))),
        ∃ hPi :
            ∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i),
          (∀ (a b c : Fin k) (xs : List (Fin k)),
            P (MarkovDeFinettiRecurrence.cylinder (k := k) (b :: c :: xs)) =
              ∫⁻ ω,
                (if ω 0 = b then rowKernelStepProd (k := k) rowKernel ω (b :: c :: xs)
                  else 0) ∂P
              →
            P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: c :: xs)) =
              ∫⁻ ω,
                (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: c :: xs)
                  else 0) ∂P) := by
    -- Remaining Fortini crux:
    -- (1) derive start-conditioned permutation invariance (`hperm`),
    -- (2) derive start-restricted row finite-dimensional laws (`hrow_restrict_data`),
    -- (3) derive global Fin1 pi-measurability (`hPi`),
    -- (4) derive the cons-step recursion for longer prefixes.
    sorry
  rcases hstepData with ⟨hperm, hrow_restrict_data, hPi, hstep⟩
  have hconstAll :
      ∀ (i a b : Fin k), StartRowSuccessorConstancy (k := k) P i a b :=
    start_constancy_of_rowKernelData (k := k) μ hμ P hExt hperm
  have hconst :
      ∀ a b : Fin k, StartRowSuccessorConstancy (k := k) P a a b := by
    intro a b
    exact hconstAll a a b
  have hrow_restrict :
      ∀ (i a : Fin k), ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
          =
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))) :=
    hrow_restrict_of_rowKernelData (k := k) P rowKernel hrow_restrict_data
  have hPi_restrict :
      ∀ (i a : Fin k),
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i) :=
    hPi_restrict_of_hPi (k := k) P rowKernel hPi
  have hpair :
      ∀ a b : Fin k,
        P (MarkovDeFinettiRecurrence.cylinder (k := k) [a, b]) =
          ∫⁻ ω,
            (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω [a, b] else 0) ∂P :=
    crossAnchor_lengthTwo_of_rowKernelData_concrete
      (k := k) P rowKernel hconst hrow hEval hrow_restrict hPi_restrict
  exact
    crossAnchorProductIdentity_of_lengthTwo_and_consStep
      (k := k) P rowKernel hpair hstep

/-- The cylinder mixing identity from row-kernel family data.

This is a structural consequence of `CrossAnchorProductIdentity`. -/
theorem cylinderMixingIdentity_P_of_rowKernelData
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hrow :
      ∀ i : Fin k, ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) P i)
          =
        (rowProcessLaw (k := k) P i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k)))))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) :
    CylinderMixingIdentity_P (k := k) P rowKernel := by
  have hcross :=
    crossAnchorProductIdentity_of_rowKernelData (k := k) P rowKernel hrow hEval μ hμ hExt
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

/-- Fortini successor-matrix invariance theorem (explicit interface):
from a concrete extension `P` with row-successor invariance and row-process
permutation invariance, derive the Markov mixture representation. -/
def FortiniSuccessorMatrixInvarianceTheorem (k : ℕ) : Prop :=
  ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
    MarkovExchangeablePrefixMeasure (k := k) μ →
    (∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i)) →
      ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
        ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi

/-- **Proof** of FortiniSuccessorMatrixInvarianceTheorem.
Uses the full-prefix reconstruction chain: nil + singleton (proved) and
`CylinderMixingIdentity_P` for length ≥ 2 (sorry in
`cylinderMixingIdentity_P_of_rowKernelData`). -/
theorem fortiniSuccessorMatrixInvarianceTheorem_proved :
    FortiniSuccessorMatrixInvarianceTheorem k := by
  intro μ hμ ⟨P, hPprob, hExt, _hsv, hperm⟩
  letI : IsProbabilityMeasure P := hPprob
  by_cases hk : 0 < k
  · -- Main case: k > 0.  Extract row-kernel family with AE-measurability data.
    rcases exists_rowKernelFamily_with_aemeasurableEvalPi_of_rowProcess_permInvariant
        (k := k) hk P (hpermAll := hperm) with
      ⟨rowKernel, hrow, hEval, _hPi⟩
    -- AE-measurability of the combined map
    have hθ := aemeasurable_rowKernelToMarkovParam_diracInit_lifted P rowKernel hEval
    -- Cylinder mixing identity (uses Markov exchangeability for cross-anchor joint law)
    have hCM := cylinderMixingIdentity_P_of_rowKernelData (k := k) P rowKernel hrow hEval
        μ hμ hExt
    -- Full-prefix reconstruction
    have hall := rowKernelToMarkovParamLaw_reconstruction_all_diracInit_of_lifted_rowKernel
        (k := k) P rowKernel hθ hCM
    -- The mixing measure
    set law := rowKernelToMarkovParamLaw (k := k) P
        (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
        (liftedRowKernelFromRowProcess (k := k) rowKernel) with hlaw_def
    -- law is a probability measure (map of P by an AE-measurable function)
    have hlaw_prob : IsProbabilityMeasure law :=
      Measure.isProbabilityMeasure_map (f := rowKernelToMarkovParam (k := k)
        (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
        (liftedRowKernelFromRowProcess (k := k) rowKernel)) hθ
    refine ⟨law, hlaw_prob, ?_⟩
    intro xs
    rw [hExt xs]
    exact hall xs
  · -- k = 0: vacuous since Fin 0 is empty, ℕ → Fin 0 is empty, no probability measure.
    exfalso
    have hk0 : k = 0 := by omega
    subst hk0
    haveI : IsEmpty (ℕ → Fin 0) := isEmpty_pi.mpr ⟨0, Fin.isEmpty⟩
    have : ¬ IsProbabilityMeasure P := by
      intro h
      have h1 := h.measure_univ
      have h2 : (P : Measure (ℕ → Fin 0)) Set.univ = 0 := by
        have : (Set.univ : Set (ℕ → Fin 0)) = ∅ := Set.eq_empty_of_isEmpty _
        rw [this]
        exact measure_empty
      simp [h2] at h1
    exact this hPprob


end MarkovDeFinettiHard
end Mettapedia.Logic
