import Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiMixtureRepresentation
import Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSuccessorArrayPE
import Mettapedia.ProbabilityTheory.Exchangeability.DiaconisFreedmanFinite
import Exchangeability.DeFinetti.ViaL2.BlockAverages
import Exchangeability.DeFinetti.ViaL2.MoreL2Helpers
import Exchangeability.Probability.CondExpHelpers.Integrability

/-!
# Markov de Finetti: Cross-Row Factorization

This module starts the successor-matrix partial-exchangeability route from the
canonical row kernels to the cross-row factorization needed for the
unconditional Markov de Finetti theorem.
-/

noncomputable section

namespace Mettapedia.ProbabilityTheory.Exchangeability

open MeasureTheory
open Filter
open scoped BigOperators ENNReal

namespace MarkovDeFinettiHard

open Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSuccessorDictionary
open Mettapedia.UniversalAI.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.ProbabilityTheory.Exchangeability.MarkovExchangeability

variable {k : ℕ}

/-! ## Canonical row-kernel cell evaluations -/

/-- Singleton evaluation of the canonical row kernel, read back on path space. -/
def directingRowKernelCell
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i b : Fin k) (ω : ℕ → Fin k) : ℝ≥0∞ :=
  (directingRowKernel (k := k) P i (rowSuccessorVisitProcess (k := k) i ω) :
      Measure (Fin k)) ({b} : Set (Fin k))

/-- Real-valued singleton evaluation of the canonical row kernel. -/
def directingRowKernelCellReal
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i b : Fin k) (ω : ℕ → Fin k) : ℝ :=
  (directingRowKernelCell (k := k) P i b ω).toReal

lemma directingRowKernelCell_le_one
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i b : Fin k) (ω : ℕ → Fin k) :
    directingRowKernelCell (k := k) P i b ω ≤ 1 := by
  change
    (directingRowKernel (k := k) P i (rowSuccessorVisitProcess (k := k) i ω) :
        Measure (Fin k)) ({b} : Set (Fin k)) ≤ 1
  exact prob_le_one

lemma directingRowKernelCellReal_nonneg
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i b : Fin k) (ω : ℕ → Fin k) :
    0 ≤ directingRowKernelCellReal (k := k) P i b ω :=
  ENNReal.toReal_nonneg

lemma directingRowKernelCellReal_le_one
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i b : Fin k) (ω : ℕ → Fin k) :
    directingRowKernelCellReal (k := k) P i b ω ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (by simpa [directingRowKernelCellReal, directingRowKernelCell] using
      directingRowKernelCell_le_one (k := k) P i b ω)

lemma directingRowKernelCellReal_abs_le_one
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i b : Fin k) (ω : ℕ → Fin k) :
    |directingRowKernelCellReal (k := k) P i b ω| ≤ 1 := by
  rw [abs_of_nonneg (directingRowKernelCellReal_nonneg (k := k) P i b ω)]
  exact directingRowKernelCellReal_le_one (k := k) P i b ω

lemma measurable_directingRowKernel_eval
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i b : Fin k) :
    Measurable
      (fun r : ℕ → Fin k =>
        (directingRowKernel (k := k) P i r : Measure (Fin k)) ({b} : Set (Fin k))) := by
  let ρ : Measure (ℕ → Fin k) := rowProcessLaw (k := k) P i
  letI : Nonempty (Fin k) := ⟨i⟩
  letI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map
      ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
  simpa [ρ, directingRowKernel] using
    (Exchangeability.DeFinetti.ViaMartingale.directingMeasure_measurable_eval
      (μ := ρ)
      (X := fun n (r : ℕ → Fin k) => r n)
      (hX := fun n => measurable_pi_apply n)
      ({b} : Set (Fin k))
      (measurableSet_singleton b))

lemma aemeasurable_directingRowKernelCell
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i b : Fin k) :
    AEMeasurable (fun ω : ℕ → Fin k => directingRowKernelCell (k := k) P i b ω) P := by
  simpa only [directingRowKernelCell, Function.comp_def] using
    (measurable_directingRowKernel_eval (k := k) P i b).aemeasurable.comp_measurable
      (measurable_rowSuccessorVisitProcess (k := k) i)

lemma aemeasurable_directingRowKernelCellReal
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i b : Fin k) :
    AEMeasurable (fun ω : ℕ → Fin k => directingRowKernelCellReal (k := k) P i b ω) P :=
  (aemeasurable_directingRowKernelCell (k := k) P i b).ennreal_toReal

lemma measurable_directingRowKernelCell
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i b : Fin k) :
    Measurable (fun ω : ℕ → Fin k => directingRowKernelCell (k := k) P i b ω) := by
  simpa only [directingRowKernelCell, Function.comp_def] using
    (measurable_directingRowKernel_eval (k := k) P i b).comp
      (measurable_rowSuccessorVisitProcess (k := k) i)

lemma measurable_directingRowKernelCellReal
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i b : Fin k) :
    Measurable (fun ω : ℕ → Fin k => directingRowKernelCellReal (k := k) P i b ω) :=
  (measurable_directingRowKernelCell (k := k) P i b).ennreal_toReal

/-- Finite product of canonical row-kernel singleton evaluations on path space. -/
def directingRowKernelCellRealProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    (ω : ℕ → Fin k) : ℝ :=
  ∏ j : Fin m, directingRowKernelCellReal (k := k) P (anchor j) (value j) ω

lemma directingRowKernelCellRealProduct_nonneg
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    (ω : ℕ → Fin k) :
    0 ≤ directingRowKernelCellRealProduct (k := k) P m anchor value ω := by
  exact Finset.prod_nonneg (fun j _ =>
    directingRowKernelCellReal_nonneg (k := k) P (anchor j) (value j) ω)

lemma directingRowKernelCellRealProduct_le_one
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    (ω : ℕ → Fin k) :
    directingRowKernelCellRealProduct (k := k) P m anchor value ω ≤ 1 := by
  exact Finset.prod_le_one
    (fun j _ => directingRowKernelCellReal_nonneg (k := k) P (anchor j) (value j) ω)
    (fun j _ => directingRowKernelCellReal_le_one (k := k) P (anchor j) (value j) ω)

lemma directingRowKernelCellRealProduct_abs_le_one
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    (ω : ℕ → Fin k) :
    |directingRowKernelCellRealProduct (k := k) P m anchor value ω| ≤ 1 := by
  rw [abs_of_nonneg (directingRowKernelCellRealProduct_nonneg (k := k) P m anchor value ω)]
  exact directingRowKernelCellRealProduct_le_one (k := k) P m anchor value ω

lemma measurable_directingRowKernelCellRealProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k) :
    Measurable
      (fun ω : ℕ → Fin k =>
        directingRowKernelCellRealProduct (k := k) P m anchor value ω) := by
  simpa [directingRowKernelCellRealProduct] using
    (Finset.univ.measurable_prod
      (f := fun j : Fin m => fun ω : ℕ → Fin k =>
        directingRowKernelCellReal (k := k) P (anchor j) (value j) ω)
      (fun j _ => measurable_directingRowKernelCellReal (k := k) P (anchor j) (value j)))

lemma aemeasurable_directingRowKernelCellRealProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k) :
    AEMeasurable
      (fun ω : ℕ → Fin k =>
        directingRowKernelCellRealProduct (k := k) P m anchor value ω) P :=
  (measurable_directingRowKernelCellRealProduct (k := k) P m anchor value).aemeasurable

lemma integrable_directingRowKernelCellRealProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k) :
    Integrable
      (fun ω : ℕ → Fin k =>
        directingRowKernelCellRealProduct (k := k) P m anchor value ω) P := by
  refine Integrable.of_bound
    ((measurable_directingRowKernelCellRealProduct (k := k) P m anchor value).aestronglyMeasurable)
    1 ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs,
    abs_of_nonneg (directingRowKernelCellRealProduct_nonneg (k := k) P m anchor value ω)]
  exact directingRowKernelCellRealProduct_le_one (k := k) P m anchor value ω

/-! ## Positive and negative FLPR dictionary canaries -/

theorem flpr_exampleOne_rowsGood_preserves_transition_counts
    (a b : Fin 2) :
    transCountL (decode (0 : Fin 2) ExampleOne.rowsGood) a b =
      transCountL ExampleOne.w₀ a b := by
  fin_cases a <;> fin_cases b <;>
  decide

theorem flpr_exampleOne_rowsGood_decodes_full_length :
    (decode (0 : Fin 2) ExampleOne.rowsGood).length = 11 := by
  decide

theorem flpr_exampleOne_rowsBad_deadlocks :
    (decode (0 : Fin 2) ExampleOne.rowsBad).length = 10 := by
  decide

theorem flpr_exampleOne_rowsBad_not_full_length :
    (decode (0 : Fin 2) ExampleOne.rowsBad).length ≠ 11 := by
  decide

/-- Boundary canary for start conditioning: empty successor rows decode to
different one-letter words when the start state changes. -/
theorem flpr_empty_rows_decode_start_zero_ne_start_one :
    decode (0 : Fin 2) (fun _ : Fin 2 => []) ≠
      decode (1 : Fin 2) (fun _ : Fin 2 => []) := by
  decide

/-- Boundary canary: those different one-letter decoded words have the same
successor rows.  The row-successor array therefore does not, by itself,
remember the initial state. -/
theorem flpr_empty_rows_decode_have_same_successor_rows :
    ∀ i : Fin 2,
      rowSuccessors i (decode (0 : Fin 2) (fun _ : Fin 2 => [])) =
        rowSuccessors i (decode (1 : Fin 2) (fun _ : Fin 2 => [])) := by
  intro i
  fin_cases i <;> decide

theorem directingRowKernelCell_fin_one_eq_one
    (P : Measure (ℕ → Fin 1)) [IsProbabilityMeasure P]
    (i b : Fin 1) (ω : ℕ → Fin 1) :
    directingRowKernelCell (k := 1) P i b ω = 1 := by
  have hsingleton : ({b} : Set (Fin 1)) = Set.univ := by
    ext x
    simp [Subsingleton.elim x b]
  simp [directingRowKernelCell, hsingleton]

/-- Bounded a.e. convergence of real observables upgrades to L¹ convergence. -/
theorem tendsto_integral_abs_sub_of_ae_tendsto_bounded
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hfn_meas : ∀ n, AEStronglyMeasurable (fn n) μ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hfn_bdd : ∀ n, ∀ᵐ ω ∂μ, |fn n ω| ≤ 1)
    (hf_bdd : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => fn n ω) atTop (nhds (f ω))) :
    Tendsto (fun n => ∫ ω, |fn n ω - f ω| ∂μ) atTop (nhds 0) := by
  have hF_meas : ∀ n, AEStronglyMeasurable (fun ω => |fn n ω - f ω|) μ := by
    intro n
    simpa [Real.norm_eq_abs] using ((hfn_meas n).sub hf_meas).norm
  have hbound : ∀ n, ∀ᵐ ω ∂μ, ‖|fn n ω - f ω|‖ ≤ (2 : ℝ) := by
    intro n
    filter_upwards [hfn_bdd n, hf_bdd] with ω hfnω hfω
    have h_abs : |fn n ω - f ω| ≤ |fn n ω| + |f ω| :=
      abs_sub (fn n ω) (f ω)
    calc
      ‖|fn n ω - f ω|‖ = |fn n ω - f ω| := by simp
      _ ≤ |fn n ω| + |f ω| := h_abs
      _ ≤ 1 + 1 := add_le_add hfnω hfω
      _ = (2 : ℝ) := by norm_num
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => |fn n ω - f ω|) atTop (nhds 0) := by
    filter_upwards [hae] with ω hω
    have hsub : Tendsto (fun n => fn n ω - f ω) atTop (nhds (f ω - f ω)) :=
      hω.sub tendsto_const_nhds
    simpa using hsub.abs
  have hdc := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := μ)
    (F := fun n ω => |fn n ω - f ω|)
    (f := fun _ω => (0 : ℝ))
    (bound := fun _ω => (2 : ℝ))
    hF_meas
    (integrable_const (2 : ℝ))
    hbound
    hlim
  simpa using hdc

/-! ## Empirical row-frequency L¹ inputs -/

lemma measurable_rowSuccessorEmpiricalCount
    (i j : Fin k) (m : ℕ) :
    Measurable
      (fun ω : ℕ → Fin k =>
        rowSuccessorEmpiricalCount (k := k) i j ω m) := by
  induction m with
  | zero =>
      simp [rowSuccessorEmpiricalCount]
  | succ m ih =>
      have hcoord :
          Measurable
            (fun ω : ℕ → Fin k =>
              rowSuccessorVisitProcess (k := k) i ω m) := by
        exact (measurable_pi_apply m).comp (measurable_rowSuccessorVisitProcess (k := k) i)
      have hset :
          MeasurableSet
            {ω : ℕ → Fin k | rowSuccessorVisitProcess (k := k) i ω m = j} := by
        exact hcoord (MeasurableSet.singleton j)
      have hite :
          Measurable
            (fun ω : ℕ → Fin k =>
              if rowSuccessorVisitProcess (k := k) i ω m = j then (1 : ℕ) else 0) := by
        exact Measurable.ite hset measurable_const measurable_const
      simpa [rowSuccessorEmpiricalCount, Nat.count_succ] using ih.add hite

lemma measurable_rowSuccessorEmpiricalFreq
    (i j : Fin k) (m : ℕ) :
    Measurable
      (fun ω : ℕ → Fin k =>
        rowSuccessorEmpiricalFreq (k := k) i j ω m) := by
  have hcast : Measurable (fun n : ℕ => (n : ℝ)) :=
    measurable_of_countable _
  simpa [rowSuccessorEmpiricalFreq] using
    (hcast.comp (measurable_rowSuccessorEmpiricalCount (k := k) i j m)).div_const (m : ℝ)

lemma aestronglyMeasurable_rowSuccessorEmpiricalFreq
    (P : Measure (ℕ → Fin k))
    (i j : Fin k) (m : ℕ) :
    AEStronglyMeasurable
      (fun ω : ℕ → Fin k =>
        rowSuccessorEmpiricalFreq (k := k) i j ω m) P :=
  (measurable_rowSuccessorEmpiricalFreq (k := k) i j m).aestronglyMeasurable

lemma rowSuccessorEmpiricalFreq_nonneg
    (i j : Fin k) (ω : ℕ → Fin k) (m : ℕ) :
    0 ≤ rowSuccessorEmpiricalFreq (k := k) i j ω m := by
  unfold rowSuccessorEmpiricalFreq
  positivity

lemma rowSuccessorEmpiricalFreq_le_one
    (i j : Fin k) (ω : ℕ → Fin k) (m : ℕ) :
    rowSuccessorEmpiricalFreq (k := k) i j ω m ≤ 1 := by
  by_cases hm : m = 0
  · simp [rowSuccessorEmpiricalFreq, hm]
  · have hmpos_nat : 0 < m := Nat.pos_of_ne_zero hm
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmpos_nat
    have hcount : rowSuccessorEmpiricalCount (k := k) i j ω m ≤ m :=
      Nat.count_le _
    have hcount_real : (rowSuccessorEmpiricalCount (k := k) i j ω m : ℝ) ≤ m := by
      exact_mod_cast hcount
    unfold rowSuccessorEmpiricalFreq
    exact (div_le_one hmpos).mpr hcount_real

lemma rowSuccessorEmpiricalFreq_abs_le_one
    (i j : Fin k) (ω : ℕ → Fin k) (m : ℕ) :
    |rowSuccessorEmpiricalFreq (k := k) i j ω m| ≤ 1 := by
  rw [abs_of_nonneg (rowSuccessorEmpiricalFreq_nonneg (k := k) i j ω m)]
  exact rowSuccessorEmpiricalFreq_le_one (k := k) i j ω m

/-- Product of empirical successor frequencies for a finite row/cell read. -/
def rowSuccessorEmpiricalFreqProduct
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    (n : ℕ) (ω : ℕ → Fin k) : ℝ :=
  ∏ j : Fin m, rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n

lemma rowSuccessorEmpiricalFreqProduct_abs_le_one
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    (n : ℕ) (ω : ℕ → Fin k) :
    |rowSuccessorEmpiricalFreqProduct (k := k) m anchor value n ω| ≤ 1 := by
  rw [rowSuccessorEmpiricalFreqProduct]
  calc
    |∏ j : Fin m, rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n|
        =
      ∏ j : Fin m, |rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n| := by
        simpa using
          (Finset.abs_prod Finset.univ
            (fun j : Fin m => rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n))
    _ ≤ ∏ _j : Fin m, (1 : ℝ) := by
        exact Finset.prod_le_prod
          (fun _j _hj => abs_nonneg _)
          (fun j _hj => rowSuccessorEmpiricalFreq_abs_le_one (k := k) (anchor j) (value j) ω n)
    _ = 1 := by simp

lemma aestronglyMeasurable_rowSuccessorEmpiricalFreqProduct
    (P : Measure (ℕ → Fin k))
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    (n : ℕ) :
    AEStronglyMeasurable
      (fun ω : ℕ → Fin k =>
        rowSuccessorEmpiricalFreqProduct (k := k) m anchor value n ω) P := by
  change AEStronglyMeasurable
    (fun ω : ℕ → Fin k =>
      ∏ j : Fin m, rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n) P
  have hprod :
      AEStronglyMeasurable
        (∏ j : Fin m,
          fun ω : ℕ → Fin k =>
            rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n) P :=
    Finset.prod_induction
      (s := Finset.univ)
      (f := fun j : Fin m =>
        fun ω : ℕ → Fin k => rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n)
      (p := fun F : (ℕ → Fin k) → ℝ => AEStronglyMeasurable F P)
      (fun _ _ ha hb => ha.mul hb)
      aestronglyMeasurable_const
      (fun j _hj =>
        aestronglyMeasurable_rowSuccessorEmpiricalFreq (k := k) P (anchor j) (value j) n)
  have hEq :
      (∏ j : Fin m,
        fun ω : ℕ → Fin k =>
          rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n)
        =
      (fun ω : ℕ → Fin k =>
        ∏ j : Fin m, rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n) := by
    funext ω
    simp
  rw [← hEq]
  exact hprod

lemma integrable_rowSuccessorEmpiricalFreqProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    (n : ℕ) :
    Integrable
      (fun ω : ℕ → Fin k =>
        rowSuccessorEmpiricalFreqProduct (k := k) m anchor value n ω) P := by
  refine Integrable.of_bound
    (aestronglyMeasurable_rowSuccessorEmpiricalFreqProduct (k := k) P m anchor value n)
    1 ?_
  exact Filter.Eventually.of_forall
    (fun ω => by
      simpa [Real.norm_eq_abs] using
        rowSuccessorEmpiricalFreqProduct_abs_le_one (k := k) m anchor value n ω)

theorem rowSuccessorEmpiricalFreq_tendsto_L1_directingRowKernelCellReal_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (i b : Fin k) :
    Tendsto
      (fun m =>
        ∫ ω,
          |rowSuccessorEmpiricalFreq (k := k) i b ω m -
            directingRowKernelCellReal (k := k) P i b ω| ∂P)
      atTop (nhds 0) := by
  have hExch :
      Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
        (fun n (r : ℕ → Fin k) => r n) := by
    exact
      rowProcessLaw_exchangeable_of_perm_invariant
        (k := k) P i
        (fun σ => rowProcessLaw_permInvariant_of_successorMatrixPE
          (k := k) P hPE i σ)
  have hrow :
      ∀ᵐ r ∂rowProcessLaw (k := k) P i,
        Filter.Tendsto
          (fun m => rowProcessEmpiricalFreq (k := k) b r m)
          Filter.atTop
          (nhds (((directingRowKernel (k := k) P i r) ({b} : Set (Fin k))).toReal)) :=
    ae_tendsto_rowProcessEmpiricalFreq_to_directingRowKernel
      (k := k) (P := P) i b hExch
  have hae :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun m => rowSuccessorEmpiricalFreq (k := k) i b ω m)
          atTop
          (nhds (directingRowKernelCellReal (k := k) P i b ω)) := by
    have hpath :=
      ae_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_of_ae_tendsto_rowProcessEmpiricalFreq
        (k := k) P (directingRowKernel (k := k) P) i b hrow
    filter_upwards [hpath] with ω hω
    have htarget :
        rowKernelVisitProbReal (k := k) (directingRowKernel (k := k) P) i b ω =
          directingRowKernelCellReal (k := k) P i b ω := by
      unfold rowKernelVisitProbReal directingRowKernelCellReal directingRowKernelCell
      exact
        (ENNReal.coe_toReal
          ((directingRowKernel (k := k) P i (rowSuccessorVisitProcess (k := k) i ω))
            ({b} : Set (Fin k)))).symm
    simpa [htarget] using hω
  exact
    tendsto_integral_abs_sub_of_ae_tendsto_bounded
      (μ := P)
      (fn := fun m ω => rowSuccessorEmpiricalFreq (k := k) i b ω m)
      (f := fun ω => directingRowKernelCellReal (k := k) P i b ω)
      (fun m => aestronglyMeasurable_rowSuccessorEmpiricalFreq (k := k) P i b m)
      ((measurable_directingRowKernelCellReal (k := k) P i b).aestronglyMeasurable)
      (fun m =>
        Filter.Eventually.of_forall
          (fun ω => rowSuccessorEmpiricalFreq_abs_le_one (k := k) i b ω m))
      (Filter.Eventually.of_forall
        (fun ω => directingRowKernelCellReal_abs_le_one (k := k) P i b ω))
      hae

/-! ## Successor-matrix spreading equalities -/

/-- Finite row-successor selection map: the observable family that
`SuccessorMatrixPartialExchangeable` is entirely about. -/
def successorMatrixSelectionMap
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ) :
    (ℕ → Fin k) → Fin m → Fin k :=
  fun ω j => rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)

/-- The finite row-successor selection map is measurable. -/
lemma measurable_successorMatrixSelectionMap
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ) :
    Measurable (successorMatrixSelectionMap (k := k) m anchor idx) := by
  exact measurable_pi_lambda _ (fun j =>
    (measurable_pi_apply (idx j)).comp
      (measurable_rowSuccessorVisitProcess (k := k) (anchor j)))

/-- Bare successor-matrix PE transfers across laws with the same finite
row-successor selection marginals. This isolates what the bare PE hypothesis
can see: no initial-state coordinate is present in these pushforwards. -/
theorem successorMatrixPartialExchangeable_of_forall_selectionMap_eq
    (P Q : Measure (ℕ → Fin k))
    (hsel :
      ∀ (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ),
        Measure.map (successorMatrixSelectionMap (k := k) m anchor idx) Q =
          Measure.map (successorMatrixSelectionMap (k := k) m anchor idx) P)
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P) :
    SuccessorMatrixPartialExchangeable (k := k) Q := by
  intro m anchor idx σ
  let shiftedIdx : Fin m → ℕ := fun j => (σ (anchor j)) (idx j)
  calc
    Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω ((σ (anchor j)) (idx j))) Q
        =
      Measure.map (successorMatrixSelectionMap (k := k) m anchor shiftedIdx) Q := by
        rfl
    _ = Measure.map (successorMatrixSelectionMap (k := k) m anchor shiftedIdx) P := by
        exact hsel m anchor shiftedIdx
    _ =
      Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω ((σ (anchor j)) (idx j))) P := by
        rfl
    _ =
      Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) P := by
        exact hPE m anchor idx σ
    _ = Measure.map (successorMatrixSelectionMap (k := k) m anchor idx) P := by
        rfl
    _ = Measure.map (successorMatrixSelectionMap (k := k) m anchor idx) Q := by
        exact (hsel m anchor idx).symm
    _ =
      Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) Q := by
        rfl

/-- Dirac canary for successor-matrix PE: a point mass is SMPE exactly when the
underlying path's finite successor-selection arrays are pointwise invariant
under every row-wise visit-index permutation. -/
theorem successorMatrixPartialExchangeable_dirac_iff_pointwise
    (ω : ℕ → Fin k) :
    SuccessorMatrixPartialExchangeable (k := k) (Measure.dirac ω) ↔
      ∀ (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
        (σ : Fin k → Equiv.Perm ℕ),
        successorMatrixSelectionMap (k := k) m anchor
            (fun j => (σ (anchor j)) (idx j)) ω =
          successorMatrixSelectionMap (k := k) m anchor idx ω := by
  constructor
  · intro hPE m anchor idx σ
    have h := hPE m anchor idx σ
    have hleft_meas :
        Measurable
          (fun ω : ℕ → Fin k =>
            fun j : Fin m =>
              rowSuccessorVisitProcess (k := k) (anchor j) ω
                ((σ (anchor j)) (idx j))) := by
      exact measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply ((σ (anchor j)) (idx j))).comp
          (measurable_rowSuccessorVisitProcess (k := k) (anchor j)))
    have hright_meas :
        Measurable
          (fun ω : ℕ → Fin k =>
            fun j : Fin m =>
              rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) := by
      exact measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply (idx j)).comp
          (measurable_rowSuccessorVisitProcess (k := k) (anchor j)))
    rw [Measure.map_dirac' hleft_meas ω, Measure.map_dirac' hright_meas ω] at h
    change
      (fun j : Fin m =>
        rowSuccessorVisitProcess (k := k) (anchor j) ω
          ((σ (anchor j)) (idx j))) =
      (fun j : Fin m =>
        rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j))
    exact dirac_eq_dirac_iff.mp h
  · intro hpoint m anchor idx σ
    have hleft_meas :
        Measurable
          (fun ω : ℕ → Fin k =>
            fun j : Fin m =>
              rowSuccessorVisitProcess (k := k) (anchor j) ω
                ((σ (anchor j)) (idx j))) := by
      exact measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply ((σ (anchor j)) (idx j))).comp
          (measurable_rowSuccessorVisitProcess (k := k) (anchor j)))
    have hright_meas :
        Measurable
          (fun ω : ℕ → Fin k =>
            fun j : Fin m =>
              rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) := by
      exact measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply (idx j)).comp
          (measurable_rowSuccessorVisitProcess (k := k) (anchor j)))
    have hinline :
        (fun j : Fin m =>
          rowSuccessorVisitProcess (k := k) (anchor j) ω
            ((σ (anchor j)) (idx j))) =
        (fun j : Fin m =>
          rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) := by
      change
        successorMatrixSelectionMap (k := k) m anchor
            (fun j => (σ (anchor j)) (idx j)) ω =
          successorMatrixSelectionMap (k := k) m anchor idx ω
      exact hpoint m anchor idx σ
    rw [Measure.map_dirac' hleft_meas ω, Measure.map_dirac' hright_meas ω]
    exact congrArg Measure.dirac hinline

/-- The row-wise permutation that moves only one selected row. -/
def oneRowSpreadingPerm (i : Fin k) (τ : Equiv.Perm ℕ) :
    Fin k → Equiv.Perm ℕ :=
  fun r => if r = i then τ else Equiv.refl ℕ

@[simp] lemma oneRowSpreadingPerm_apply_self (i : Fin k) (τ : Equiv.Perm ℕ) :
    oneRowSpreadingPerm (k := k) i τ i = τ := by
  simp [oneRowSpreadingPerm]

lemma exists_nat_perm_map_injective_tuple
    {m : ℕ} {idx target : Fin m → ℕ}
    (hidx : Function.Injective idx) (htarget : Function.Injective target) :
    ∃ τ : Equiv.Perm ℕ, ∀ j : Fin m, τ (idx j) = target j :=
  Equiv.Perm.exists_extending_pair idx target hidx htarget

lemma oneRowSpreadingPerm_apply_of_ne {i r : Fin k} (τ : Equiv.Perm ℕ)
    (hri : r ≠ i) :
    oneRowSpreadingPerm (k := k) i τ r = Equiv.refl ℕ := by
  simp [oneRowSpreadingPerm, hri]

lemma oneRowSpreadingPerm_append_idx_eq
    (m r : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (i : Fin k) (τ : Equiv.Perm ℕ)
    (hfixed : ∀ q : Fin r, riderAnchor q ≠ i) :
    (fun j : Fin (m + r) =>
        (oneRowSpreadingPerm (k := k) i τ (Fin.append anchor riderAnchor j))
          (Fin.append idx riderIdx j)) =
      Fin.append
        (fun j : Fin m =>
          (oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j))
        riderIdx := by
  funext j
  induction j using Fin.addCases with
  | left j =>
      simp
  | right j =>
      simp [oneRowSpreadingPerm_apply_of_ne, hfixed j]

lemma measurable_successorMatrix_read
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ) :
    Measurable
      (fun ω : ℕ → Fin k =>
        fun j : Fin m => rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) := by
  exact measurable_pi_lambda _ (fun j =>
    (measurable_pi_apply (idx j)).comp
      (measurable_rowSuccessorVisitProcess (k := k) (anchor j)))

/-- Event that a finite successor-matrix read takes a prescribed value. -/
def successorReadEvent
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) : Set (ℕ → Fin k) :=
  {ω : ℕ → Fin k |
    ∀ j : Fin m, rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j) = value j}

lemma measurableSet_successorReadEvent
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) :
    MeasurableSet (successorReadEvent (k := k) m anchor idx value) := by
  have hset :
      successorReadEvent (k := k) m anchor idx value =
        ((fun ω : ℕ → Fin k =>
          fun j : Fin m => rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) ⁻¹'
            ({value} : Set (Fin m → Fin k))) := by
    ext ω
    simp [successorReadEvent, funext_iff]
  rw [hset]
  exact (measurable_successorMatrix_read (k := k) m anchor idx)
    (measurableSet_singleton value)

/-- Product of singleton indicators for a finite successor-matrix read. -/
def successorReadProductIndicator
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) (ω : ℕ → Fin k) : ENNReal :=
  ∏ j : Fin m,
    ({ω' : ℕ → Fin k |
      rowSuccessorVisitProcess (k := k) (anchor j) ω' (idx j) = value j}.indicator
        (fun _ => (1 : ENNReal)) ω)

/-- Real-valued product of singleton indicators for a finite successor-matrix read. -/
def successorReadProductIndicatorReal
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) (ω : ℕ → Fin k) : ℝ :=
  ∏ j : Fin m,
    ({ω' : ℕ → Fin k |
      rowSuccessorVisitProcess (k := k) (anchor j) ω' (idx j) = value j}.indicator
        (fun _ => (1 : ℝ)) ω)

lemma successorReadProductIndicator_eq_event_indicator
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) :
    (fun ω : ℕ → Fin k =>
      successorReadProductIndicator (k := k) m anchor idx value ω)
      =
    (successorReadEvent (k := k) m anchor idx value).indicator
      (fun _ => (1 : ENNReal)) := by
  classical
  funext ω
  by_cases hω :
      ∀ j : Fin m, rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j) = value j
  · simp [successorReadProductIndicator, successorReadEvent, hω]
  · have hnot : ω ∉ successorReadEvent (k := k) m anchor idx value := by
      simpa [successorReadEvent] using hω
    push Not at hω
    rcases hω with ⟨j, hj⟩
    have hfactor :
        ({ω' : ℕ → Fin k |
          rowSuccessorVisitProcess (k := k) (anchor j) ω' (idx j) = value j}.indicator
            (fun _ => (1 : ENNReal)) ω) = 0 := by
      simp [Set.indicator, hj]
    have hprod :
        successorReadProductIndicator (k := k) m anchor idx value ω = 0 := by
      rw [successorReadProductIndicator]
      exact Finset.prod_eq_zero (Finset.mem_univ j) hfactor
    rw [hprod]
    simp [Set.indicator_of_notMem hnot]

lemma successorReadProductIndicatorReal_eq_event_indicator
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) :
    (fun ω : ℕ → Fin k =>
      successorReadProductIndicatorReal (k := k) m anchor idx value ω)
      =
    (successorReadEvent (k := k) m anchor idx value).indicator
      (fun _ => (1 : ℝ)) := by
  classical
  funext ω
  by_cases hω :
      ∀ j : Fin m, rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j) = value j
  · simp [successorReadProductIndicatorReal, successorReadEvent, hω]
  · have hnot : ω ∉ successorReadEvent (k := k) m anchor idx value := by
      simpa [successorReadEvent] using hω
    push Not at hω
    rcases hω with ⟨j, hj⟩
    have hfactor :
        ({ω' : ℕ → Fin k |
          rowSuccessorVisitProcess (k := k) (anchor j) ω' (idx j) = value j}.indicator
            (fun _ => (1 : ℝ)) ω) = 0 := by
      simp [Set.indicator, hj]
    have hprod :
        successorReadProductIndicatorReal (k := k) m anchor idx value ω = 0 := by
      rw [successorReadProductIndicatorReal]
      exact Finset.prod_eq_zero (Finset.mem_univ j) hfactor
    rw [hprod]
    simp [Set.indicator_of_notMem hnot]

lemma measurable_successorReadProductIndicatorReal
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) :
    Measurable
      (fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) m anchor idx value ω) := by
  rw [successorReadProductIndicatorReal_eq_event_indicator]
  exact measurable_const.indicator
    (measurableSet_successorReadEvent (k := k) m anchor idx value)

lemma integrable_successorReadProductIndicatorReal
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) :
    Integrable
      (fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) m anchor idx value ω) P := by
  rw [successorReadProductIndicatorReal_eq_event_indicator]
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_successorReadEvent (k := k) m anchor idx value)

lemma integrable_successorReadProductIndicatorReal_of_finite
    (P : Measure (ℕ → Fin k)) [IsFiniteMeasure P]
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) :
    Integrable
      (fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) m anchor idx value ω) P := by
  rw [successorReadProductIndicatorReal_eq_event_indicator]
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_successorReadEvent (k := k) m anchor idx value)

lemma aestronglyMeasurable_successorReadProductIndicatorReal
    (P : Measure (ℕ → Fin k))
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) :
    AEStronglyMeasurable
      (fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) m anchor idx value ω) P :=
  (measurable_successorReadProductIndicatorReal (k := k) m anchor idx value).aestronglyMeasurable

lemma successorReadProductIndicatorReal_zero_or_one
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) (ω : ℕ → Fin k) :
    successorReadProductIndicatorReal (k := k) m anchor idx value ω = 0 ∨
      successorReadProductIndicatorReal (k := k) m anchor idx value ω = 1 := by
  have hfun :=
    congrFun
      (successorReadProductIndicatorReal_eq_event_indicator
        (k := k) m anchor idx value) ω
  by_cases hω : ω ∈ successorReadEvent (k := k) m anchor idx value
  · right
    simp [hfun, hω]
  · left
    simp [hfun, hω]

lemma successorReadProductIndicatorReal_nonneg
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) (ω : ℕ → Fin k) :
    0 ≤ successorReadProductIndicatorReal (k := k) m anchor idx value ω := by
  rcases successorReadProductIndicatorReal_zero_or_one
      (k := k) m anchor idx value ω with h | h <;>
    simp [h]

lemma successorReadProductIndicatorReal_le_one
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) (ω : ℕ → Fin k) :
    successorReadProductIndicatorReal (k := k) m anchor idx value ω ≤ 1 := by
  rcases successorReadProductIndicatorReal_zero_or_one
      (k := k) m anchor idx value ω with h | h <;>
    simp [h]

lemma successorReadProductIndicatorReal_abs_le_one
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) (ω : ℕ → Fin k) :
    |successorReadProductIndicatorReal (k := k) m anchor idx value ω| ≤ 1 := by
  rcases successorReadProductIndicatorReal_zero_or_one
      (k := k) m anchor idx value ω with h | h <;>
    simp [h]

lemma successorReadProductIndicatorReal_append
    (m r : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) (riderAnchor : Fin r → Fin k)
    (riderIdx : Fin r → ℕ) (riderValue : Fin r → Fin k)
    (ω : ℕ → Fin k) :
    successorReadProductIndicatorReal (k := k) (m + r)
        (Fin.append anchor riderAnchor) (Fin.append idx riderIdx)
        (Fin.append value riderValue) ω =
      successorReadProductIndicatorReal (k := k) m anchor idx value ω *
        successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω := by
  simp [successorReadProductIndicatorReal, Fin.prod_univ_add, Fin.append_left,
    Fin.append_right]

lemma successorReadEvent_append
    (m r : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) (riderAnchor : Fin r → Fin k)
    (riderIdx : Fin r → ℕ) (riderValue : Fin r → Fin k) :
    successorReadEvent (k := k) (m + r)
        (Fin.append anchor riderAnchor) (Fin.append idx riderIdx)
        (Fin.append value riderValue)
      =
    successorReadEvent (k := k) m anchor idx value ∩
      successorReadEvent (k := k) r riderAnchor riderIdx riderValue := by
  ext ω
  constructor
  · intro hω
    constructor
    · intro j
      have h := hω (Fin.castAdd r j)
      simpa [Fin.append_left] using h
    · intro j
      have h := hω (Fin.natAdd m j)
      simpa [Fin.append_right] using h
  · intro hω
    rcases hω with ⟨hleft, hright⟩
    intro j
    induction j using Fin.addCases with
    | left j =>
        simpa [Fin.append_left] using hleft j
    | right j =>
        simpa [Fin.append_right] using hright j

lemma integrable_successorReadProductIndicatorReal_mul_successorReadProductIndicatorReal
    (P : Measure (ℕ → Fin k)) [IsFiniteMeasure P]
    (m r : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) (riderAnchor : Fin r → Fin k)
    (riderIdx : Fin r → ℕ) (riderValue : Fin r → Fin k) :
    Integrable
      (fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) m anchor idx value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω) P := by
  have hfun :
      (fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) m anchor idx value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω)
        =
      fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) (m + r)
          (Fin.append anchor riderAnchor) (Fin.append idx riderIdx)
          (Fin.append value riderValue) ω := by
    funext ω
    symm
    exact successorReadProductIndicatorReal_append
      (k := k) m r anchor idx value riderAnchor riderIdx riderValue ω
  rw [hfun]
  exact integrable_successorReadProductIndicatorReal_of_finite
    (k := k) P (m + r) (Fin.append anchor riderAnchor)
    (Fin.append idx riderIdx) (Fin.append value riderValue)

lemma rowSuccessorEmpiricalCount_real_eq_fin_sum_indicator
    (n : ℕ) (i j : Fin k) (ω : ℕ → Fin k) :
    (rowSuccessorEmpiricalCount (k := k) i j ω n : ℝ) =
      ∑ t : Fin n,
        if rowSuccessorVisitProcess (k := k) i ω t.1 = j then (1 : ℝ) else 0 := by
  rw [rowSuccessorEmpiricalCount, Nat.count_eq_card_filter_range]
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ =>
    if rowSuccessorVisitProcess (k := k) i ω t = j then (1 : ℝ) else 0) n]
  rw [Finset.card_eq_sum_ones]
  simp

theorem rowSuccessorEmpiricalFreqProduct_eq_allTuple_average
    (m n : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    (ω : ℕ → Fin k) (hn : n ≠ 0) :
    rowSuccessorEmpiricalFreqProduct (k := k) m anchor value n ω =
      (1 / (n : ℝ)) ^ m *
        ∑ φ : Fin m → Fin n,
          successorReadProductIndicatorReal (k := k) m anchor (fun j => (φ j).1) value ω := by
  classical
  have hfreq : ∀ j : Fin m,
      rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n =
        (1 / (n : ℝ)) *
          ∑ t : Fin n,
            if rowSuccessorVisitProcess (k := k) (anchor j) ω t.1 = value j then
              (1 : ℝ)
            else
              0 := by
    intro j
    rw [rowSuccessorEmpiricalFreq, rowSuccessorEmpiricalCount_real_eq_fin_sum_indicator]
    field_simp [Nat.cast_ne_zero.mpr hn]
  rw [rowSuccessorEmpiricalFreqProduct]
  simp_rw [hfreq]
  rw [Finset.prod_mul_distrib]
  rw [Fin.prod_const]
  congr 1
  let f : (i : Fin m) → Fin n → ℝ :=
    fun i t =>
      if rowSuccessorVisitProcess (k := k) (anchor i) ω t.1 = value i then 1 else 0
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin m => (Finset.univ : Finset (Fin n))) (f := f)
  simpa [f, successorReadProductIndicatorReal, Set.indicator] using hprod

lemma allTuples_average_sub_injectiveTuples_average_abs_le_collisionMass
    {m n : ℕ} (hn : 0 < n) (F : (Fin m → Fin n) → ℝ)
    (hF : ∀ φ, |F φ| ≤ 1) :
    |(1 / (n : ℝ)) ^ m * Finset.univ.sum F -
      (1 / (n : ℝ)) ^ m *
        ((Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)).sum F)|
      ≤
    (1 / (n : ℝ)) ^ m *
      ((Finset.univ.filter (fun φ : Fin m → Fin n => ¬ Function.Injective φ)).card : ℝ) := by
  classical
  let c : ℝ := (1 / (n : ℝ)) ^ m
  let s : Finset (Fin m → Fin n) := Finset.univ.filter (fun φ => Function.Injective φ)
  let t : Finset (Fin m → Fin n) := Finset.univ.filter (fun φ => ¬ Function.Injective φ)
  have hc_nonneg : 0 ≤ c := by positivity
  have hsplit : Finset.univ.sum F = s.sum F + t.sum F := by
    have h :=
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin m → Fin n)))
        (p := fun φ : Fin m → Fin n => Function.Injective φ) (f := F)).symm
    simpa [s, t] using h
  have hdiff : c * Finset.univ.sum F - c * s.sum F = c * t.sum F := by
    rw [hsplit]
    ring
  rw [show (1 / (n : ℝ)) ^ m = c by rfl]
  change |c * Finset.univ.sum F - c * s.sum F| ≤ c * (t.card : ℝ)
  rw [hdiff, abs_mul, abs_of_nonneg hc_nonneg]
  apply mul_le_mul_of_nonneg_left ?_ hc_nonneg
  calc
    |t.sum F| ≤ t.sum (fun φ => |F φ|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ t.sum (fun _φ => (1 : ℝ)) := by
        exact Finset.sum_le_sum (fun φ _ => hF φ)
    _ = (t.card : ℝ) := by simp

lemma noninjectiveTupleMass_le_choose2
    (m n : ℕ) (hn : 0 < n) (hmn : m ≤ n) :
    (1 / (n : ℝ)) ^ m *
      ((Finset.univ.filter (fun φ : Fin m → Fin n => ¬ Function.Injective φ)).card : ℝ)
      ≤ ((m : ℝ) * ((m : ℝ) - 1)) / (n : ℝ) := by
  classical
  let c : ℝ := (1 / (n : ℝ)) ^ m
  let bad : Finset (Fin m → Fin n) :=
    Finset.univ.filter (fun φ : Fin m → Fin n => ¬ Function.Injective φ)
  let Z : ℝ := ∑ ψ : Fin m → Fin n, if Function.Injective ψ then c else 0
  let term : (Fin m → Fin n) → ℝ :=
    fun φ => |c - (if Function.Injective φ then c / Z else 0)|
  have hc_nonneg : 0 ≤ c := by positivity
  have hbad_sum : bad.sum term = bad.card * c := by
    calc
      bad.sum term = bad.sum (fun _φ => c) := by
        refine Finset.sum_congr rfl ?_
        intro φ hφ
        have hnot : ¬ Function.Injective φ := (Finset.mem_filter.mp hφ).2
        simp [term, hnot, abs_of_nonneg hc_nonneg]
      _ = bad.card * c := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hmass_eq :
      (1 / (n : ℝ)) ^ m * (bad.card : ℝ) = bad.sum term := by
    rw [hbad_sum]
    simp [c]
    ring
  have hsum_le : bad.sum term ≤ (Finset.univ : Finset (Fin m → Fin n)).sum term := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro φ hφ; simp)
      (by intro φ hφuniv hφbad; exact abs_nonneg _)
  have htight :=
    Mettapedia.ProbabilityTheory.Exchangeability.DiaconisFreedmanFinite.l1_iid_inj_le_choose2
      n m hn hmn
  have hterm_eq :
      ((Finset.univ : Finset (Fin m → Fin n)).sum term) =
        ∑ f : Fin m → Fin n,
          |(1 : ℝ) / (n : ℝ) ^ m -
            (if Function.Injective f then
              (1 : ℝ) / (n : ℝ) ^ m /
                (∑ g : Fin m → Fin n,
                  if Function.Injective g then (1 : ℝ) / (n : ℝ) ^ m else 0)
             else 0)| := by
    simp [term, Z, c]
  rw [hmass_eq]
  exact hsum_le.trans (by simpa [hterm_eq] using htight)

lemma noninjectiveTupleMass_tendsto_zero (m : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (1 / (n : ℝ)) ^ m *
          ((Finset.univ.filter (fun φ : Fin m → Fin n => ¬ Function.Injective φ)).card : ℝ))
      atTop (nhds 0) := by
  let mass : ℕ → ℝ := fun n =>
    (1 / (n : ℝ)) ^ m *
      ((Finset.univ.filter (fun φ : Fin m → Fin n => ¬ Function.Injective φ)).card : ℝ)
  let upper : ℕ → ℝ := fun n => ((m : ℝ) * ((m : ℝ) - 1)) / (n : ℝ)
  have hmass_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ mass n :=
    Filter.Eventually.of_forall (fun n => by
      dsimp [mass]
      positivity)
  have hmass_le : ∀ᶠ n : ℕ in atTop, mass n ≤ upper n := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨max 1 m, ?_⟩
    intro n hn
    have hnpos : 0 < n := by omega
    have hmn : m ≤ n := by omega
    exact noninjectiveTupleMass_le_choose2 m n hnpos hmn
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp [upper]
    exact tendsto_const_div_atTop_nhds_zero_nat (((m : ℝ) * ((m : ℝ) - 1)))
  simpa [mass] using squeeze_zero' hmass_nonneg hmass_le hupper

lemma injectiveTupleMass_tendsto_one (m : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (1 / (n : ℝ)) ^ m *
          ((Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ))
      atTop (nhds 1) := by
  classical
  let injMass : ℕ → ℝ := fun n =>
    (1 / (n : ℝ)) ^ m *
      ((Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)
  let badMass : ℕ → ℝ := fun n =>
    (1 / (n : ℝ)) ^ m *
      ((Finset.univ.filter (fun φ : Fin m → Fin n => ¬ Function.Injective φ)).card : ℝ)
  have heq : injMass =ᶠ[atTop] fun n => 1 - badMass n := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hnpos : 0 < n := by omega
    let injTuples : Finset (Fin m → Fin n) :=
      Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)
    let badTuples : Finset (Fin m → Fin n) :=
      Finset.univ.filter (fun φ : Fin m → Fin n => ¬ Function.Injective φ)
    have hsplit_nat : injTuples.card + badTuples.card =
        (Finset.univ : Finset (Fin m → Fin n)).card := by
      simpa [injTuples, badTuples] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin m → Fin n)))
          (p := fun φ : Fin m → Fin n => Function.Injective φ))
    have hsplit_real :
        ((Finset.univ : Finset (Fin m → Fin n)).card : ℝ) =
          (injTuples.card : ℝ) + (badTuples.card : ℝ) := by
      exact_mod_cast hsplit_nat.symm
    have huniv_card :
        (Finset.univ : Finset (Fin m → Fin n)).card = n ^ m := by
      simp
    have htotal :
        (1 / (n : ℝ)) ^ m *
          ((Finset.univ : Finset (Fin m → Fin n)).card : ℝ) = 1 := by
      rw [huniv_card, Nat.cast_pow, one_div, ← mul_pow]
      have hmul : ((n : ℝ)⁻¹) * (n : ℝ) = 1 := by
        field_simp [Nat.cast_ne_zero.mpr hnpos.ne']
      rw [hmul]
      simp
    dsimp [injMass, badMass]
    calc
      (1 / (n : ℝ)) ^ m * (injTuples.card : ℝ)
          =
        (1 / (n : ℝ)) ^ m *
            ((Finset.univ : Finset (Fin m → Fin n)).card : ℝ) -
          (1 / (n : ℝ)) ^ m * (badTuples.card : ℝ) := by
          rw [hsplit_real]
          ring
      _ = 1 - (1 / (n : ℝ)) ^ m * (badTuples.card : ℝ) := by
          rw [htotal]
  have hbad : Tendsto badMass atTop (nhds 0) := by
    simpa [badMass] using noninjectiveTupleMass_tendsto_zero m
  have hlim : Tendsto (fun n => 1 - badMass n) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hbad
  exact Filter.Tendsto.congr' heq.symm (by simpa using hlim)

lemma abs_setIntegral_injectiveTupleAverage_sub_empiricalInjectiveAverage_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {s : Set Ω} {m n : ℕ} (hmn : m ≤ n)
    (F : (Fin m → Fin n) → Ω → ℝ)
    (hF : ∀ φ ω, |F φ ω| ≤ 1) :
    |∫ ω in s,
        ((1 / ((Finset.univ.filter
            (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)) *
          ((Finset.univ.filter
            (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ => F φ ω) -
        (1 / (n : ℝ)) ^ m *
          ((Finset.univ.filter
            (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ => F φ ω)) ∂P|
      ≤
    |1 -
      (1 / (n : ℝ)) ^ m *
        ((Finset.univ.filter
          (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)| := by
  classical
  let injTuples : Finset (Fin m → Fin n) :=
    Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)
  let c : ℝ := (1 / (n : ℝ)) ^ m
  have hnonempty : injTuples.Nonempty := by
    let base : Fin m → Fin n := fun j => ⟨j.1, lt_of_lt_of_le j.isLt hmn⟩
    have hbase_inj : Function.Injective base := by
      intro a b hab
      have hval : a.1 = b.1 := by
        have hval' := congrArg Fin.val hab
        simpa [base] using hval'
      exact Fin.ext hval
    exact ⟨base, by simp [injTuples, base, hbase_inj]⟩
  have hcard_nat : injTuples.card ≠ 0 := Finset.card_ne_zero.mpr hnonempty
  have hcard_ne : (injTuples.card : ℝ) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hcard_nonneg : 0 ≤ (injTuples.card : ℝ) := by positivity
  have hcoeff :
      |(1 / (injTuples.card : ℝ)) - c| * (injTuples.card : ℝ) =
        |1 - c * (injTuples.card : ℝ)| := by
    have hmul :
        ((1 / (injTuples.card : ℝ)) - c) * (injTuples.card : ℝ) =
          1 - c * (injTuples.card : ℝ) := by
      field_simp [hcard_ne]
    calc
      |(1 / (injTuples.card : ℝ)) - c| * (injTuples.card : ℝ)
          =
        |(1 / (injTuples.card : ℝ)) - c| * |(injTuples.card : ℝ)| := by
          rw [abs_of_nonneg hcard_nonneg]
      _ = |((1 / (injTuples.card : ℝ)) - c) * (injTuples.card : ℝ)| := by
          rw [abs_mul]
      _ = |1 - c * (injTuples.card : ℝ)| := by
          rw [hmul]
  let diff : Ω → ℝ := fun ω =>
    (1 / (injTuples.card : ℝ)) * injTuples.sum (fun φ => F φ ω) -
      c * injTuples.sum (fun φ => F φ ω)
  have hpoint : ∀ ω, |diff ω| ≤ |1 - c * (injTuples.card : ℝ)| := by
    intro ω
    have hsum :
        |injTuples.sum (fun φ => F φ ω)| ≤ (injTuples.card : ℝ) := by
      calc
        |injTuples.sum (fun φ => F φ ω)|
            ≤ injTuples.sum (fun φ => |F φ ω|) := Finset.abs_sum_le_sum_abs _ _
        _ ≤ injTuples.sum (fun _φ => (1 : ℝ)) := by
            exact Finset.sum_le_sum (fun φ _ => hF φ ω)
        _ = (injTuples.card : ℝ) := by simp
    calc
      |diff ω|
          =
        |((1 / (injTuples.card : ℝ)) - c) *
          injTuples.sum (fun φ => F φ ω)| := by
          dsimp [diff]
          ring_nf
      _ =
        |(1 / (injTuples.card : ℝ)) - c| *
          |injTuples.sum (fun φ => F φ ω)| := by
          rw [abs_mul]
      _ ≤ |(1 / (injTuples.card : ℝ)) - c| * (injTuples.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = |1 - c * (injTuples.card : ℝ)| := hcoeff
  have hnorm :=
    norm_setIntegral_le_of_norm_le_const
      (μ := P) (s := s) (f := diff)
      (C := |1 - c * (injTuples.card : ℝ)|)
      (measure_lt_top P s)
      (fun ω _hω => by
        simpa [Real.norm_eq_abs] using hpoint ω)
  have hmeasure :
      |1 - c * (injTuples.card : ℝ)| * P.real s
        ≤ |1 - c * (injTuples.card : ℝ)| := by
    calc
      |1 - c * (injTuples.card : ℝ)| * P.real s
          ≤ |1 - c * (injTuples.card : ℝ)| * 1 := by
          exact mul_le_mul_of_nonneg_left measureReal_le_one (abs_nonneg _)
      _ = |1 - c * (injTuples.card : ℝ)| := by ring
  have habs :
      |∫ ω in s, diff ω ∂P| ≤ |1 - c * (injTuples.card : ℝ)| := by
    simpa [Real.norm_eq_abs] using hnorm.trans hmeasure
  simpa [diff, injTuples, c] using habs

lemma setIntegral_injectiveTupleAverage_sub_empiricalInjectiveAverage_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {s : Set Ω} (m : ℕ)
    (F : (n : ℕ) → (Fin m → Fin n) → Ω → ℝ)
    (hF : ∀ n φ ω, |F n φ ω| ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        |∫ ω in s,
          ((1 / ((Finset.univ.filter
              (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)) *
            ((Finset.univ.filter
              (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ => F n φ ω) -
          (1 / (n : ℝ)) ^ m *
            ((Finset.univ.filter
              (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ => F n φ ω)) ∂P|)
      atTop (nhds 0) := by
  let diffInt : ℕ → ℝ := fun n =>
    |∫ ω in s,
      ((1 / ((Finset.univ.filter
          (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)) *
        ((Finset.univ.filter
          (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ => F n φ ω) -
      (1 / (n : ℝ)) ^ m *
        ((Finset.univ.filter
          (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ => F n φ ω)) ∂P|
  let mass : ℕ → ℝ := fun n =>
    (1 / (n : ℝ)) ^ m *
      ((Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)
  have hdiff_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ diffInt n :=
    Filter.Eventually.of_forall (fun n => by
      dsimp [diffInt]
      positivity)
  have hdiff_le : ∀ᶠ n : ℕ in atTop, diffInt n ≤ |1 - mass n| := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨m, ?_⟩
    intro n hn
    exact abs_setIntegral_injectiveTupleAverage_sub_empiricalInjectiveAverage_le
      (P := P) (s := s) (m := m) (n := n) hn (F n) (hF n)
  have hmass : Tendsto mass atTop (nhds 1) := by
    simpa [mass] using injectiveTupleMass_tendsto_one m
  have hupper : Tendsto (fun n => |1 - mass n|) atTop (nhds 0) := by
    have hsub : Tendsto (fun n => 1 - mass n) atTop (nhds (1 - 1)) :=
      tendsto_const_nhds.sub hmass
    simpa using Filter.Tendsto.abs hsub
  simpa [diffInt] using squeeze_zero' hdiff_nonneg hdiff_le hupper

lemma allTuples_average_sub_injectiveTuples_average_tendsto_zero_of_abs_le_one
    (m : ℕ) (F : (n : ℕ) → (Fin m → Fin n) → ℝ)
    (hF : ∀ n φ, |F n φ| ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        |(1 / (n : ℝ)) ^ m * (Finset.univ.sum (F n)) -
          (1 / (n : ℝ)) ^ m *
            ((Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)).sum (F n))|)
      atTop (nhds 0) := by
  let diff : ℕ → ℝ := fun n =>
    |(1 / (n : ℝ)) ^ m * (Finset.univ.sum (F n)) -
      (1 / (n : ℝ)) ^ m *
        ((Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)).sum (F n))|
  let mass : ℕ → ℝ := fun n =>
    (1 / (n : ℝ)) ^ m *
      ((Finset.univ.filter (fun φ : Fin m → Fin n => ¬ Function.Injective φ)).card : ℝ)
  have hdiff_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ diff n :=
    Filter.Eventually.of_forall (fun n => by
      dsimp [diff]
      positivity)
  have hdiff_le : ∀ᶠ n : ℕ in atTop, diff n ≤ mass n := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hnpos : 0 < n := by omega
    exact allTuples_average_sub_injectiveTuples_average_abs_le_collisionMass
      (m := m) (n := n) hnpos (F n) (hF n)
  have hmass : Tendsto mass atTop (nhds 0) := by
    simpa [mass] using noninjectiveTupleMass_tendsto_zero m
  simpa [diff] using squeeze_zero' hdiff_nonneg hdiff_le hmass

lemma abs_setIntegral_allTuples_sub_injectiveTuples_average_mul_bounded_le_collisionMass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {s : Set Ω} (m n : ℕ) (hn : 0 < n)
    (F : (Fin m → Fin n) → Ω → ℝ) (H : Ω → ℝ)
    (hF : ∀ φ ω, |F φ ω| ≤ 1)
    (hH : ∀ ω, |H ω| ≤ 1) :
    |∫ ω in s,
        (((1 / (n : ℝ)) ^ m * (Finset.univ.sum (fun φ : Fin m → Fin n => F φ ω))) -
          ((1 / (n : ℝ)) ^ m *
            ((Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)).sum
              (fun φ => F φ ω)))) * H ω ∂P|
      ≤
    (1 / (n : ℝ)) ^ m *
      ((Finset.univ.filter (fun φ : Fin m → Fin n => ¬ Function.Injective φ)).card : ℝ) := by
  classical
  let mass : ℝ :=
    (1 / (n : ℝ)) ^ m *
      ((Finset.univ.filter (fun φ : Fin m → Fin n => ¬ Function.Injective φ)).card : ℝ)
  let diff : Ω → ℝ := fun ω =>
    (1 / (n : ℝ)) ^ m * (Finset.univ.sum (fun φ : Fin m → Fin n => F φ ω)) -
      (1 / (n : ℝ)) ^ m *
        ((Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)).sum
          (fun φ => F φ ω))
  have hmass_nonneg : 0 ≤ mass := by
    dsimp [mass]
    positivity
  have hpoint : ∀ ω, |diff ω * H ω| ≤ mass := by
    intro ω
    have hdiff :=
      allTuples_average_sub_injectiveTuples_average_abs_le_collisionMass
        (m := m) (n := n) hn (fun φ : Fin m → Fin n => F φ ω) (fun φ => hF φ ω)
    calc
      |diff ω * H ω| = |diff ω| * |H ω| := abs_mul _ _
      _ ≤ mass * 1 := by
          exact mul_le_mul hdiff (hH ω) (abs_nonneg _) hmass_nonneg
      _ = mass := by ring
  have hnorm :=
    norm_setIntegral_le_of_norm_le_const
      (μ := P) (s := s) (f := fun ω => diff ω * H ω) (C := mass)
      (measure_lt_top P s)
      (fun ω _hω => by
        simpa [Real.norm_eq_abs] using hpoint ω)
  have hmass_real : mass * P.real s ≤ mass := by
    calc
      mass * P.real s ≤ mass * 1 := by
        exact mul_le_mul_of_nonneg_left measureReal_le_one hmass_nonneg
      _ = mass := by ring
  have habs : |∫ ω in s, diff ω * H ω ∂P| ≤ mass := by
    simpa [Real.norm_eq_abs] using hnorm.trans hmass_real
  simpa [diff, mass] using habs

lemma setIntegral_allTuples_sub_injectiveTuples_average_mul_bounded_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {s : Set Ω} (m : ℕ)
    (F : (n : ℕ) → (Fin m → Fin n) → Ω → ℝ) (H : Ω → ℝ)
    (hF : ∀ n φ ω, |F n φ ω| ≤ 1)
    (hH : ∀ ω, |H ω| ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        |∫ ω in s,
          (((1 / (n : ℝ)) ^ m * (Finset.univ.sum (fun φ : Fin m → Fin n => F n φ ω))) -
            ((1 / (n : ℝ)) ^ m *
              ((Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)).sum
                (fun φ => F n φ ω)))) * H ω ∂P|)
      atTop (nhds 0) := by
  let diffInt : ℕ → ℝ := fun n =>
    |∫ ω in s,
      (((1 / (n : ℝ)) ^ m * (Finset.univ.sum (fun φ : Fin m → Fin n => F n φ ω))) -
        ((1 / (n : ℝ)) ^ m *
          ((Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)).sum
            (fun φ => F n φ ω)))) * H ω ∂P|
  let mass : ℕ → ℝ := fun n =>
    (1 / (n : ℝ)) ^ m *
      ((Finset.univ.filter (fun φ : Fin m → Fin n => ¬ Function.Injective φ)).card : ℝ)
  have hdiff_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ diffInt n :=
    Filter.Eventually.of_forall (fun n => by
      dsimp [diffInt]
      positivity)
  have hdiff_le : ∀ᶠ n : ℕ in atTop, diffInt n ≤ mass n := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hnpos : 0 < n := by omega
    exact abs_setIntegral_allTuples_sub_injectiveTuples_average_mul_bounded_le_collisionMass
      (P := P) (s := s) m n hnpos (F n) H (hF n) hH
  have hmass : Tendsto mass atTop (nhds 0) := by
    simpa [mass] using noninjectiveTupleMass_tendsto_zero m
  simpa [diffInt] using squeeze_zero' hdiff_nonneg hdiff_le hmass

theorem setIntegral_allTuples_sub_injectiveTuples_successorReadProductIndicatorReal_mul_rider_tendsto_zero
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    {s : Set (ℕ → Fin k)}
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    (r : ℕ) (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (riderValue : Fin r → Fin k) :
    Tendsto
      (fun n : ℕ =>
        |∫ ω in s,
          (((1 / (n : ℝ)) ^ m *
              (Finset.univ.sum
                (fun φ : Fin m → Fin n =>
                  successorReadProductIndicatorReal
                    (k := k) m anchor (fun j => (φ j).1) value ω))) -
            ((1 / (n : ℝ)) ^ m *
              ((Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)).sum
                (fun φ =>
                  successorReadProductIndicatorReal
                    (k := k) m anchor (fun j => (φ j).1) value ω)))) *
            successorReadProductIndicatorReal
              (k := k) r riderAnchor riderIdx riderValue ω ∂P|)
      atTop (nhds 0) := by
  exact
    setIntegral_allTuples_sub_injectiveTuples_average_mul_bounded_tendsto_zero
      (P := P) (s := s) m
      (F := fun n φ ω =>
        successorReadProductIndicatorReal
          (k := k) m anchor (fun j => (φ j).1) value ω)
      (H := fun ω =>
        successorReadProductIndicatorReal
          (k := k) r riderAnchor riderIdx riderValue ω)
      (fun n φ ω =>
        successorReadProductIndicatorReal_abs_le_one
          (k := k) m anchor (fun j => (φ j).1) value ω)
      (fun ω =>
        successorReadProductIndicatorReal_abs_le_one
          (k := k) r riderAnchor riderIdx riderValue ω)

lemma lintegral_successorReadProductIndicator_eq_measure
    (P : Measure (ℕ → Fin k))
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) :
    ∫⁻ ω, successorReadProductIndicator (k := k) m anchor idx value ω ∂P
      =
    P (successorReadEvent (k := k) m anchor idx value) := by
  rw [successorReadProductIndicator_eq_event_indicator]
  exact lintegral_indicator_one
    (μ := P)
    (s := successorReadEvent (k := k) m anchor idx value)
    (measurableSet_successorReadEvent (k := k) m anchor idx value)

lemma integral_successorReadProductIndicatorReal_eq_measure_toReal
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) :
    ∫ ω, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P
      =
    (P (successorReadEvent (k := k) m anchor idx value)).toReal := by
  rw [successorReadProductIndicatorReal_eq_event_indicator]
  have h :=
    MeasureTheory.integral_indicator_one
      (μ := P)
      (s := successorReadEvent (k := k) m anchor idx value)
      (measurableSet_successorReadEvent (k := k) m anchor idx value)
  change
    ∫ ω, (successorReadEvent (k := k) m anchor idx value).indicator
      (1 : (ℕ → Fin k) → ℝ) ω ∂P =
        (P (successorReadEvent (k := k) m anchor idx value)).toReal
  simpa [Measure.real] using h

lemma integral_successorReadProductIndicatorReal_eq_measure_toReal_of_measure
    (P : Measure (ℕ → Fin k))
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) :
    ∫ ω, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P
      =
    (P (successorReadEvent (k := k) m anchor idx value)).toReal := by
  rw [successorReadProductIndicatorReal_eq_event_indicator]
  have h :=
    MeasureTheory.integral_indicator_one
      (μ := P)
      (s := successorReadEvent (k := k) m anchor idx value)
      (measurableSet_successorReadEvent (k := k) m anchor idx value)
  change
    ∫ ω, (successorReadEvent (k := k) m anchor idx value).indicator
      (1 : (ℕ → Fin k) → ℝ) ω ∂P =
        (P (successorReadEvent (k := k) m anchor idx value)).toReal
  simpa [Measure.real] using h

lemma integral_set_successorReadProductIndicatorReal_eq_measure_inter_toReal
    (P : Measure (ℕ → Fin k))
    {s : Set (ℕ → Fin k)} (hs : MeasurableSet s)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) :
    ∫ ω in s, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P
      =
    (P (s ∩ successorReadEvent (k := k) m anchor idx value)).toReal := by
  have h :=
    integral_successorReadProductIndicatorReal_eq_measure_toReal_of_measure
      (k := k) (P := P.restrict s) m anchor idx value
  rw [Measure.restrict_apply' hs] at h
  simpa [Set.inter_comm] using h

lemma integral_set_successorReadProductIndicatorReal_mul_eq_measure_inter_inter_toReal
    (P : Measure (ℕ → Fin k))
    {s : Set (ℕ → Fin k)} (hs : MeasurableSet s)
    (m r : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k) (riderAnchor : Fin r → Fin k)
    (riderIdx : Fin r → ℕ) (riderValue : Fin r → Fin k) :
    ∫ ω in s,
        successorReadProductIndicatorReal (k := k) m anchor idx value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω ∂P
      =
    (P (s ∩
      (successorReadEvent (k := k) m anchor idx value ∩
        successorReadEvent (k := k) r riderAnchor riderIdx riderValue))).toReal := by
  have hfun :
      (fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) m anchor idx value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω)
        =
      fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) (m + r)
          (Fin.append anchor riderAnchor) (Fin.append idx riderIdx)
          (Fin.append value riderValue) ω := by
    funext ω
    symm
    exact successorReadProductIndicatorReal_append
      (k := k) m r anchor idx value riderAnchor riderIdx riderValue ω
  rw [hfun]
  rw [integral_set_successorReadProductIndicatorReal_eq_measure_inter_toReal
    (k := k) (P := P) hs]
  congr 1
  rw [successorReadEvent_append (k := k)]

lemma successorReadEvent_word_eq_preimage_wordSuccessorTuple
    (a : Fin k) (ys : List (Fin k)) :
    successorReadEvent (k := k) ys.length
        (fun j : Fin ys.length => (a :: ys).getD j.1 a)
        (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
        (wordSuccessorTuple (k := k) a ys)
      =
    (wordSuccessorTupleMap (k := k) a ys) ⁻¹'
      ({wordSuccessorTuple (k := k) a ys} : Set (Fin ys.length → Fin k)) := by
  ext ω
  simp [successorReadEvent, wordSuccessorTupleMap, rowSuccessorVisitProcess,
    funext_iff]

lemma integral_start_successorReadProductIndicatorReal_word_eq_measure_cylinder_toReal
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k)) :
    ∫ ω in {ω : ℕ → Fin k | ω 0 = a},
        successorReadProductIndicatorReal (k := k) ys.length
          (fun j : Fin ys.length => (a :: ys).getD j.1 a)
          (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
          (wordSuccessorTuple (k := k) a ys) ω ∂P
      =
    (P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: ys))).toReal := by
  have hs : MeasurableSet {ω : ℕ → Fin k | ω 0 = a} := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' ({a} : Set (Fin k)))
    exact (measurable_pi_apply 0) (MeasurableSet.singleton a)
  rw [integral_set_successorReadProductIndicatorReal_eq_measure_inter_toReal
    (k := k) (P := P) hs]
  congr 1
  rw [successorReadEvent_word_eq_preimage_wordSuccessorTuple (k := k) a ys]
  exact congrArg P
    (cylinder_cons_eq_start_inter_preimage_wordSuccessorTuple
      (k := k) a ys).symm

/-! ## Word-fiber and complement bookkeeping -/

/-- The ordered complement of a word anchor fiber: successor coordinates whose
anchor state is not `i`. -/
def wordAnchorComplementList
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) : List (Fin ys.length) :=
  (List.finRange ys.length).filter fun j =>
    (a :: ys).getD j.1 a ≠ i

lemma mem_wordAnchorComplementList_iff
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) (j : Fin ys.length) :
    j ∈ wordAnchorComplementList (k := k) a ys i ↔
      (a :: ys).getD j.1 a ≠ i := by
  simp [wordAnchorComplementList, List.mem_filter, List.mem_finRange]

lemma getElem_wordAnchorComplementList_ne_anchor
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) {n : ℕ}
    (hn : n < (wordAnchorComplementList (k := k) a ys i).length) :
    (a :: ys).getD ((wordAnchorComplementList (k := k) a ys i)[n]).1 a ≠ i := by
  simp only [wordAnchorComplementList]
  exact of_decide_eq_true
    (List.getElem_filter
      (xs := List.finRange ys.length)
      (p := fun j : Fin ys.length => (a :: ys).getD j.1 a ≠ i)
      hn)

/-- Visit indices of the selected word anchor fiber. For word fibers these are
the left-to-right visit numbers `0, ..., m-1`. -/
def wordAnchorFiberIdx
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    Fin (wordAnchorFiberList (k := k) a ys i).length → ℕ :=
  fun t => wordVisitIndex (k := k) (a :: ys) a
    ((wordAnchorFiberList (k := k) a ys i)[t]).1

/-- Target successor values on the selected word anchor fiber. -/
def wordAnchorFiberValue
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k :=
  fun t => wordSuccessorTuple (k := k) a ys
    ((wordAnchorFiberList (k := k) a ys i)[t])

lemma wordAnchorFiberIdx_eq_coe
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (t : Fin (wordAnchorFiberList (k := k) a ys i).length) :
    wordAnchorFiberIdx (k := k) a ys i t = t := by
  simpa [wordAnchorFiberIdx] using
    wordVisitIndex_getElem_wordAnchorFiberList (k := k) a ys i t

lemma wordAnchorFiberIdx_injective
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    Function.Injective (wordAnchorFiberIdx (k := k) a ys i) := by
  intro t u htu
  have ht : wordAnchorFiberIdx (k := k) a ys i t = (t : ℕ) :=
    wordAnchorFiberIdx_eq_coe (k := k) a ys i t
  have hu : wordAnchorFiberIdx (k := k) a ys i u = (u : ℕ) :=
    wordAnchorFiberIdx_eq_coe (k := k) a ys i u
  exact Fin.ext (by omega)

/-- Anchors of the complement coordinates. -/
def wordAnchorComplementAnchor
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    Fin (wordAnchorComplementList (k := k) a ys i).length → Fin k :=
  fun t => (a :: ys).getD
    ((wordAnchorComplementList (k := k) a ys i)[t]).1 a

/-- Visit indices of the complement coordinates. -/
def wordAnchorComplementIdx
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    Fin (wordAnchorComplementList (k := k) a ys i).length → ℕ :=
  fun t => wordVisitIndex (k := k) (a :: ys) a
    ((wordAnchorComplementList (k := k) a ys i)[t]).1

/-- Target successor values on the complement coordinates. -/
def wordAnchorComplementValue
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    Fin (wordAnchorComplementList (k := k) a ys i).length → Fin k :=
  fun t => wordSuccessorTuple (k := k) a ys
    ((wordAnchorComplementList (k := k) a ys i)[t])

lemma wordAnchorComplementAnchor_ne
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (t : Fin (wordAnchorComplementList (k := k) a ys i).length) :
    wordAnchorComplementAnchor (k := k) a ys i t ≠ i := by
  exact getElem_wordAnchorComplementList_ne_anchor (k := k) a ys i t.2

lemma successorReadEvent_wordFiber_inter_complement_eq_word
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    successorReadEvent (k := k) (wordAnchorFiberList (k := k) a ys i).length
        (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
        (wordAnchorFiberIdx (k := k) a ys i)
        (wordAnchorFiberValue (k := k) a ys i)
      ∩
      successorReadEvent (k := k) (wordAnchorComplementList (k := k) a ys i).length
        (wordAnchorComplementAnchor (k := k) a ys i)
        (wordAnchorComplementIdx (k := k) a ys i)
        (wordAnchorComplementValue (k := k) a ys i)
      =
    successorReadEvent (k := k) ys.length
        (fun j : Fin ys.length => (a :: ys).getD j.1 a)
        (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
        (wordSuccessorTuple (k := k) a ys) := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨hfiber, hcomp⟩
    intro j
    by_cases hj : (a :: ys).getD j.1 a = i
    · have hmem : j ∈ wordAnchorFiberList (k := k) a ys i :=
        (mem_wordAnchorFiberList_iff (k := k) a ys i j).mpr hj
      obtain ⟨t, ht⟩ := List.mem_iff_get.mp hmem
      have ht_eq : (wordAnchorFiberList (k := k) a ys i)[t] = j := ht
      have h := hfiber t
      have hrow :
          rowSuccessorVisitProcess (k := k) i ω
              (wordVisitIndex (k := k) (a :: ys) a j.1) =
            wordSuccessorTuple (k := k) a ys j := by
        simpa [wordAnchorFiberIdx, wordAnchorFiberValue, ht_eq] using h
      have hj_get : (a :: ys)[j.1] = i := by
        simpa using hj
      simpa [hj_get] using hrow
    · have hmem : j ∈ wordAnchorComplementList (k := k) a ys i :=
        (mem_wordAnchorComplementList_iff (k := k) a ys i j).mpr hj
      obtain ⟨t, ht⟩ := List.mem_iff_get.mp hmem
      have ht_eq : (wordAnchorComplementList (k := k) a ys i)[t] = j := ht
      have h := hcomp t
      simpa [wordAnchorComplementAnchor, wordAnchorComplementIdx,
        wordAnchorComplementValue, ht_eq] using h
  · intro hω
    constructor
    · intro t
      have h := hω ((wordAnchorFiberList (k := k) a ys i)[t])
      have hanchor :
          (a :: ys).getD ((wordAnchorFiberList (k := k) a ys i)[t]).1 a = i :=
        getElem_wordAnchorFiberList_eq_anchor (k := k) a ys i t.2
      have hanchor_get :
          (a :: ys)[((wordAnchorFiberList (k := k) a ys i)[t]).1] = i := by
        simpa using hanchor
      have h' :
          rowSuccessorVisitProcess (k := k)
              ((a :: ys)[((wordAnchorFiberList (k := k) a ys i)[t]).1]) ω
              (wordVisitIndex (k := k) (a :: ys) a
                ((wordAnchorFiberList (k := k) a ys i)[t]).1) =
            wordSuccessorTuple (k := k) a ys
              ((wordAnchorFiberList (k := k) a ys i)[t]) := by
        simpa using h
      rw [hanchor_get] at h'
      simpa [wordAnchorFiberIdx, wordAnchorFiberValue] using h'
    · intro t
      have h := hω ((wordAnchorComplementList (k := k) a ys i)[t])
      simpa [wordAnchorComplementAnchor, wordAnchorComplementIdx,
        wordAnchorComplementValue] using h

lemma integral_start_wordFiber_mul_complement_eq_measure_cylinder_toReal
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    ∫ ω in {ω : ℕ → Fin k | ω 0 = a},
        successorReadProductIndicatorReal
            (k := k) (wordAnchorFiberList (k := k) a ys i).length
            (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
            (wordAnchorFiberIdx (k := k) a ys i)
            (wordAnchorFiberValue (k := k) a ys i) ω *
          successorReadProductIndicatorReal
            (k := k) (wordAnchorComplementList (k := k) a ys i).length
            (wordAnchorComplementAnchor (k := k) a ys i)
            (wordAnchorComplementIdx (k := k) a ys i)
            (wordAnchorComplementValue (k := k) a ys i) ω ∂P
      =
    (P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: ys))).toReal := by
  have hs : MeasurableSet {ω : ℕ → Fin k | ω 0 = a} := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' ({a} : Set (Fin k)))
    exact (measurable_pi_apply 0) (MeasurableSet.singleton a)
  rw [integral_set_successorReadProductIndicatorReal_mul_eq_measure_inter_inter_toReal
    (k := k) (P := P) hs]
  congr 1
  rw [successorReadEvent_wordFiber_inter_complement_eq_word (k := k) a ys i,
    successorReadEvent_word_eq_preimage_wordSuccessorTuple (k := k) a ys]
  exact congrArg P
    (cylinder_cons_eq_start_inter_preimage_wordSuccessorTuple
      (k := k) a ys).symm

/-- The empirical product attached to one row's word fiber. -/
def wordRowEmpiricalProduct
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (n : ℕ) (ω : ℕ → Fin k) : ℝ :=
  rowSuccessorEmpiricalFreqProduct
    (k := k) (wordAnchorFiberList (k := k) a ys i).length
    (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
    (wordAnchorFiberValue (k := k) a ys i) n ω

/-- Product over all row-fiber empirical products for a word. -/
def wordAllRowsEmpiricalProduct
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) (ω : ℕ → Fin k) : ℝ :=
  ∏ i : Fin k, wordRowEmpiricalProduct (k := k) a ys i n ω

/-- Product over all canonical directing row-kernel evaluations for a word. -/
def wordAllRowsDirectingProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (a : Fin k) (ys : List (Fin k)) (ω : ℕ → Fin k) : ℝ :=
  ∏ i : Fin k,
    directingRowKernelCellRealProduct
      (k := k) P (wordAnchorFiberList (k := k) a ys i).length
      (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
      (wordAnchorFiberValue (k := k) a ys i) ω

/-- One row's finite tuple read, with an arbitrary map from that row's word
fiber coordinates into the first `n` visits. -/
def wordRowTupleIndicator
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) (n : ℕ)
    (φ : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n)
    (ω : ℕ → Fin k) : ℝ :=
  successorReadProductIndicatorReal
    (k := k) (wordAnchorFiberList (k := k) a ys i).length
    (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
    (fun j => (φ j).1)
    (wordAnchorFiberValue (k := k) a ys i) ω

/-- Simultaneous finite tuple read over every row fiber of a word. -/
def wordAllRowsTupleIndicator
    (a : Fin k) (ys : List (Fin k)) (n : ℕ)
    (Φ : (i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n)
    (ω : ℕ → Fin k) : ℝ :=
  ∏ i : Fin k, wordRowTupleIndicator (k := k) a ys i n (Φ i) ω

/-- Event represented by a simultaneous all-row tuple read. -/
def wordAllRowsTupleEvent
    (a : Fin k) (ys : List (Fin k)) (n : ℕ)
    (Φ : (i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) :
    Set (ℕ → Fin k) :=
  {ω |
    ∀ i : Fin k,
      ∀ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
        rowSuccessorVisitProcess (k := k) i ω (Φ i t).1 =
          wordAnchorFiberValue (k := k) a ys i t}

/-- Source-index all-row event for a word: every row fiber is read at its
original word visit index. -/
def wordAllRowsSourceEvent
    (a : Fin k) (ys : List (Fin k)) : Set (ℕ → Fin k) :=
  {ω |
    ∀ i : Fin k,
      ∀ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
        rowSuccessorVisitProcess (k := k) i ω
            (wordAnchorFiberIdx (k := k) a ys i t) =
          wordAnchorFiberValue (k := k) a ys i t}

/-- Normalizing coefficient for the all-rows empirical tuple average. -/
def wordAllRowsEmpiricalCoeff
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) : ℝ :=
  ∏ i : Fin k, (1 / (n : ℝ)) ^ (wordAnchorFiberList (k := k) a ys i).length

def wordAllRowsAllTupleAverage
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) (ω : ℕ → Fin k) : ℝ :=
  wordAllRowsEmpiricalCoeff (k := k) a ys n *
    ∑ Φ : (i : Fin k) →
        Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n,
      wordAllRowsTupleIndicator (k := k) a ys n Φ ω

theorem wordAllRowsEmpiricalProduct_eq_allRowsTuple_average
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) (ω : ℕ → Fin k)
    (hn : n ≠ 0) :
    wordAllRowsEmpiricalProduct (k := k) a ys n ω =
      wordAllRowsEmpiricalCoeff (k := k) a ys n *
        ∑ Φ : (i : Fin k) →
            Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n,
          wordAllRowsTupleIndicator (k := k) a ys n Φ ω := by
  classical
  have hrow :
      ∀ i : Fin k,
        wordRowEmpiricalProduct (k := k) a ys i n ω =
          (1 / (n : ℝ)) ^ (wordAnchorFiberList (k := k) a ys i).length *
            ∑ φ : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n,
              wordRowTupleIndicator (k := k) a ys i n φ ω := by
    intro i
    simpa [wordRowEmpiricalProduct, wordRowTupleIndicator] using
      rowSuccessorEmpiricalFreqProduct_eq_allTuple_average
        (k := k)
        (m := (wordAnchorFiberList (k := k) a ys i).length)
        (n := n)
        (anchor := fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
        (value := wordAnchorFiberValue (k := k) a ys i)
        (ω := ω) hn
  rw [wordAllRowsEmpiricalProduct]
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib]
  rw [wordAllRowsEmpiricalCoeff]
  congr 1
  let t :
      (i : Fin k) →
        Finset (Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) :=
    fun _ => Finset.univ
  let f :
      (i : Fin k) →
        (Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) → ℝ :=
    fun i φ => wordRowTupleIndicator (k := k) a ys i n φ ω
  have hprod := Finset.prod_univ_sum (t := t) (f := f)
  simpa [t, f, wordAllRowsTupleIndicator, Fintype.piFinset_univ] using hprod

lemma measurableSet_wordAllRowsTupleEvent
    (a : Fin k) (ys : List (Fin k)) (n : ℕ)
    (Φ : (i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) :
    MeasurableSet (wordAllRowsTupleEvent (k := k) a ys n Φ) := by
  rw [show wordAllRowsTupleEvent (k := k) a ys n Φ =
      ⋂ i : Fin k,
        ⋂ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
          {ω : ℕ → Fin k |
            rowSuccessorVisitProcess (k := k) i ω (Φ i t).1 =
              wordAnchorFiberValue (k := k) a ys i t} from by
        ext ω
        simp [wordAllRowsTupleEvent]]
  exact MeasurableSet.iInter fun i =>
    MeasurableSet.iInter fun t =>
      (measurable_pi_apply (Φ i t).1).comp
        (measurable_rowSuccessorVisitProcess (k := k) i)
        (measurableSet_singleton (wordAnchorFiberValue (k := k) a ys i t))

lemma wordAllRowsTupleIndicator_eq_event_indicator
    (a : Fin k) (ys : List (Fin k)) (n : ℕ)
    (Φ : (i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) :
    (fun ω : ℕ → Fin k => wordAllRowsTupleIndicator (k := k) a ys n Φ ω)
      =
    (wordAllRowsTupleEvent (k := k) a ys n Φ).indicator
      (fun _ => (1 : ℝ)) := by
  classical
  funext ω
  by_cases hω :
      ∀ i : Fin k,
        ∀ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
          rowSuccessorVisitProcess (k := k) i ω (Φ i t).1 =
            wordAnchorFiberValue (k := k) a ys i t
  · have hmem : ω ∈ wordAllRowsTupleEvent (k := k) a ys n Φ := by
      simpa [wordAllRowsTupleEvent] using hω
    have hrow :
        ∀ i : Fin k, wordRowTupleIndicator (k := k) a ys i n (Φ i) ω = 1 := by
      intro i
      rw [wordRowTupleIndicator]
      simp [successorReadProductIndicatorReal, hω i]
    simp [wordAllRowsTupleIndicator, hrow, Set.indicator_of_mem hmem]
  · have hnotmem : ω ∉ wordAllRowsTupleEvent (k := k) a ys n Φ := by
      simpa [wordAllRowsTupleEvent] using hω
    push Not at hω
    rcases hω with ⟨i, t, ht⟩
    have hrow_zero : wordRowTupleIndicator (k := k) a ys i n (Φ i) ω = 0 := by
      rw [wordRowTupleIndicator, successorReadProductIndicatorReal]
      have hfactor :
          ({ω' : ℕ → Fin k |
            rowSuccessorVisitProcess (k := k) i ω' (Φ i t).1 =
              wordAnchorFiberValue (k := k) a ys i t}.indicator
            (fun _ => (1 : ℝ)) ω) = 0 := by
        simp [Set.indicator, ht]
      exact Finset.prod_eq_zero (Finset.mem_univ t) hfactor
    have hall_zero : wordAllRowsTupleIndicator (k := k) a ys n Φ ω = 0 := by
      rw [wordAllRowsTupleIndicator]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hrow_zero
    simp [hall_zero, Set.indicator_of_notMem hnotmem]

lemma wordAllRowsSourceEvent_eq_wordSuccessorReadEvent
    (a : Fin k) (ys : List (Fin k)) :
    wordAllRowsSourceEvent (k := k) a ys =
      successorReadEvent (k := k) ys.length
        (fun j : Fin ys.length => (a :: ys).getD j.1 a)
        (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
        (wordSuccessorTuple (k := k) a ys) := by
  ext ω
  constructor
  · intro hω j
    let i : Fin k := (a :: ys).getD j.1 a
    have hmem : j ∈ wordAnchorFiberList (k := k) a ys i :=
      (mem_wordAnchorFiberList_iff (k := k) a ys i j).mpr rfl
    obtain ⟨t, ht⟩ := List.mem_iff_get.mp hmem
    have ht_eq : (wordAnchorFiberList (k := k) a ys i)[t] = j := ht
    have h := hω i t
    have h' :
        rowSuccessorVisitProcess (k := k) i ω
            (wordVisitIndex (k := k) (a :: ys) a
              ((wordAnchorFiberList (k := k) a ys i)[t]).1) =
          wordSuccessorTuple (k := k) a ys
            ((wordAnchorFiberList (k := k) a ys i)[t]) := by
      simpa [wordAnchorFiberIdx, wordAnchorFiberValue] using h
    rw [ht_eq] at h'
    simpa [i] using h'
  · intro hω i t
    have h := hω ((wordAnchorFiberList (k := k) a ys i)[t])
    have hanchor :
        (a :: ys).getD ((wordAnchorFiberList (k := k) a ys i)[t]).1 a = i :=
      getElem_wordAnchorFiberList_eq_anchor (k := k) a ys i t.2
    have hanchor_get :
        (a :: ys)[((wordAnchorFiberList (k := k) a ys i)[t]).1] = i := by
      simpa using hanchor
    have h' :
        rowSuccessorVisitProcess (k := k)
            ((a :: ys)[((wordAnchorFiberList (k := k) a ys i)[t]).1]) ω
            (wordVisitIndex (k := k) (a :: ys) a
              ((wordAnchorFiberList (k := k) a ys i)[t]).1) =
          wordSuccessorTuple (k := k) a ys
            ((wordAnchorFiberList (k := k) a ys i)[t]) := by
      simpa using h
    rw [hanchor_get] at h'
    simpa [wordAnchorFiberIdx, wordAnchorFiberValue] using h'

/-- Rowwise injectivity for a simultaneous all-row tuple selection. -/
def wordAllRowsInjective
    (a : Fin k) (ys : List (Fin k)) (n : ℕ)
    (Φ : (i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) : Prop :=
  ∀ i : Fin k, Function.Injective (Φ i)

lemma wordAnchorFiberList_length_le_ys_length
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    (wordAnchorFiberList (k := k) a ys i).length ≤ ys.length := by
  rw [length_wordAnchorFiberList_eq_countP]
  simpa using
    (List.countP_le_length
      (p := fun j : Fin ys.length => decide ((a :: ys).getD j.1 a = i))
      (l := List.finRange ys.length))

lemma wordAnchorFiberList_length_le_of_ys_length_le
    (a : Fin k) (ys : List (Fin k)) {n : ℕ}
    (hn : ys.length ≤ n) (i : Fin k) :
    (wordAnchorFiberList (k := k) a ys i).length ≤ n :=
  Nat.le_trans (wordAnchorFiberList_length_le_ys_length (k := k) a ys i) hn

def wordRowInjectiveTuples
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) (n : ℕ) :
    Finset (Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) := by
  classical
  exact Finset.univ.filter Function.Injective

def wordAllRowsInjectiveTuples
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) :
    Finset ((i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) := by
  classical
  exact Finset.univ.filter (fun Φ => wordAllRowsInjective (k := k) a ys n Φ)

def wordAllRowsNoninjectiveTuples
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) :
    Finset ((i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) := by
  classical
  exact Finset.univ.filter (fun Φ => ¬ wordAllRowsInjective (k := k) a ys n Φ)

def wordAllRowsEmpiricalInjectiveTupleAverage
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) (ω : ℕ → Fin k) : ℝ :=
  wordAllRowsEmpiricalCoeff (k := k) a ys n *
    ((wordAllRowsInjectiveTuples (k := k) a ys n).sum fun Φ =>
      wordAllRowsTupleIndicator (k := k) a ys n Φ ω)

def wordAllRowsNormalizedInjectiveTupleAverage
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) (ω : ℕ → Fin k) : ℝ :=
  (1 / ((wordAllRowsInjectiveTuples (k := k) a ys n).card : ℝ)) *
    ((wordAllRowsInjectiveTuples (k := k) a ys n).sum fun Φ =>
      wordAllRowsTupleIndicator (k := k) a ys n Φ ω)

lemma wordAllRowsInjectiveTuples_nonempty
    (a : Fin k) (ys : List (Fin k)) {n : ℕ}
    (hn : ∀ i : Fin k, (wordAnchorFiberList (k := k) a ys i).length ≤ n) :
    (wordAllRowsInjectiveTuples (k := k) a ys n).Nonempty := by
  classical
  let base :
      (i : Fin k) →
        Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n :=
    fun i t => ⟨t.1, lt_of_lt_of_le t.isLt (hn i)⟩
  have hbase : wordAllRowsInjective (k := k) a ys n base := by
    intro i t u htu
    have hval : t.1 = u.1 := by
      have hval' := congrArg Fin.val htu
      simpa [base] using hval'
    exact Fin.ext hval
  exact ⟨base, by simp [wordAllRowsInjectiveTuples, base, hbase]⟩

lemma wordAllRowsInjectiveTuples_eq_piFinset
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) :
    wordAllRowsInjectiveTuples (k := k) a ys n =
      Fintype.piFinset (fun i : Fin k => wordRowInjectiveTuples (k := k) a ys i n) := by
  classical
  ext Φ
  rw [Fintype.mem_piFinset]
  simp [wordAllRowsInjectiveTuples, wordAllRowsInjective, wordRowInjectiveTuples]

lemma wordAllRowsInjectiveTuples_card
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) :
    (wordAllRowsInjectiveTuples (k := k) a ys n).card =
      ∏ i : Fin k, (wordRowInjectiveTuples (k := k) a ys i n).card := by
  classical
  rw [wordAllRowsInjectiveTuples_eq_piFinset]
  simp [Fintype.piFinset, Finset.card_pi, wordRowInjectiveTuples]

lemma wordAllRowsInjectiveMass_tendsto_one
    (a : Fin k) (ys : List (Fin k)) :
    Tendsto
      (fun n : ℕ =>
        wordAllRowsEmpiricalCoeff (k := k) a ys n *
          ((wordAllRowsInjectiveTuples (k := k) a ys n).card : ℝ))
      atTop (nhds 1) := by
  classical
  have hrow' :
      ∀ i : Fin k,
        Tendsto
          (fun n : ℕ =>
            (1 / (n : ℝ)) ^ (wordAnchorFiberList (k := k) a ys i).length *
              ((wordRowInjectiveTuples (k := k) a ys i n).card : ℝ))
          atTop (nhds 1) := by
    intro i
    simpa [wordRowInjectiveTuples] using
      injectiveTupleMass_tendsto_one
        (m := (wordAnchorFiberList (k := k) a ys i).length)
  have hprod :=
    tendsto_finsetProd (s := (Finset.univ : Finset (Fin k)))
      (f := fun i (n : ℕ) =>
        (1 / (n : ℝ)) ^ (wordAnchorFiberList (k := k) a ys i).length *
          ((wordRowInjectiveTuples (k := k) a ys i n).card : ℝ))
      (a := fun _i : Fin k => (1 : ℝ))
      (fun i _ => hrow' i)
  have hprod1 :
      Tendsto
        (fun n : ℕ =>
          ∏ i : Fin k,
            (1 / (n : ℝ)) ^ (wordAnchorFiberList (k := k) a ys i).length *
              ((wordRowInjectiveTuples (k := k) a ys i n).card : ℝ))
        atTop (nhds 1) := by
    simpa using hprod
  refine Filter.Tendsto.congr' ?_ hprod1
  refine Filter.Eventually.of_forall ?_
  intro n
  simp [wordAllRowsEmpiricalCoeff, wordAllRowsInjectiveTuples_card,
    Finset.prod_mul_distrib]

lemma wordAllRowsTotalMass_eq_one
    (a : Fin k) (ys : List (Fin k)) {n : ℕ} (hn : 0 < n) :
    wordAllRowsEmpiricalCoeff (k := k) a ys n *
      ((Finset.univ : Finset ((i : Fin k) →
        Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n)).card : ℝ) = 1 := by
  rw [Finset.card_univ, Fintype.card_pi]
  simp [wordAllRowsEmpiricalCoeff, Fintype.card_fin]
  have hprod_pos :
      0 < ∏ x : Fin k,
        (n : ℝ) ^ (wordAnchorFiberList (k := k) a ys x).length := by
    exact Finset.prod_pos (fun _i _hi => pow_pos (Nat.cast_pos.mpr hn) _)
  field_simp [ne_of_gt hprod_pos]

lemma wordAllRowsNoninjectiveMass_eq_one_sub_injectiveMass
    (a : Fin k) (ys : List (Fin k)) {n : ℕ} (hn : 0 < n) :
    wordAllRowsEmpiricalCoeff (k := k) a ys n *
        ((wordAllRowsNoninjectiveTuples (k := k) a ys n).card : ℝ)
      =
    1 -
      wordAllRowsEmpiricalCoeff (k := k) a ys n *
        ((wordAllRowsInjectiveTuples (k := k) a ys n).card : ℝ) := by
  classical
  let good := wordAllRowsInjectiveTuples (k := k) a ys n
  let bad := wordAllRowsNoninjectiveTuples (k := k) a ys n
  let allTuples : Finset ((i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) := Finset.univ
  have hsplit_nat : good.card + bad.card = allTuples.card := by
    simpa [good, bad, allTuples, wordAllRowsInjectiveTuples, wordAllRowsNoninjectiveTuples] using
      (Finset.card_filter_add_card_filter_not
        (s := allTuples)
        (p := fun Φ => wordAllRowsInjective (k := k) a ys n Φ))
  have hsplit_real : (allTuples.card : ℝ) = (good.card : ℝ) + (bad.card : ℝ) := by
    exact_mod_cast hsplit_nat.symm
  have htotal :
      wordAllRowsEmpiricalCoeff (k := k) a ys n * (allTuples.card : ℝ) = 1 := by
    simpa [allTuples] using wordAllRowsTotalMass_eq_one (k := k) a ys hn
  calc
    wordAllRowsEmpiricalCoeff (k := k) a ys n * (bad.card : ℝ)
        =
      wordAllRowsEmpiricalCoeff (k := k) a ys n * (allTuples.card : ℝ) -
        wordAllRowsEmpiricalCoeff (k := k) a ys n * (good.card : ℝ) := by
        rw [hsplit_real]
        ring
    _ =
      1 - wordAllRowsEmpiricalCoeff (k := k) a ys n * (good.card : ℝ) := by
      rw [htotal]

lemma wordAllRowsNoninjectiveMass_tendsto_zero
    (a : Fin k) (ys : List (Fin k)) :
    Tendsto
      (fun n : ℕ =>
        wordAllRowsEmpiricalCoeff (k := k) a ys n *
          ((wordAllRowsNoninjectiveTuples (k := k) a ys n).card : ℝ))
      atTop (nhds 0) := by
  let badMass : ℕ → ℝ := fun n =>
    wordAllRowsEmpiricalCoeff (k := k) a ys n *
      ((wordAllRowsNoninjectiveTuples (k := k) a ys n).card : ℝ)
  let goodMass : ℕ → ℝ := fun n =>
    wordAllRowsEmpiricalCoeff (k := k) a ys n *
      ((wordAllRowsInjectiveTuples (k := k) a ys n).card : ℝ)
  have heq : badMass =ᶠ[atTop] fun n => 1 - goodMass n := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hnpos : 0 < n := by omega
    simpa [badMass, goodMass] using
      wordAllRowsNoninjectiveMass_eq_one_sub_injectiveMass (k := k) a ys hnpos
  have hgood : Tendsto goodMass atTop (nhds 1) := by
    simpa [goodMass] using wordAllRowsInjectiveMass_tendsto_one (k := k) a ys
  have hlim : Tendsto (fun n => 1 - goodMass n) atTop (nhds (1 - 1)) :=
    tendsto_const_nhds.sub hgood
  exact Filter.Tendsto.congr' heq.symm (by simpa using hlim)

lemma exists_rowPerms_map_wordAnchorFiberIdx
    (a : Fin k) (ys : List (Fin k)) {n : ℕ}
    (Φ : (i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n)
    (hΦ : wordAllRowsInjective (k := k) a ys n Φ) :
    ∃ σ : Fin k → Equiv.Perm ℕ,
      ∀ i : Fin k,
        ∀ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
          σ i (wordAnchorFiberIdx (k := k) a ys i t) = (Φ i t).1 := by
  classical
  have hrow :
      ∀ i : Fin k,
        ∃ τ : Equiv.Perm ℕ,
          ∀ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
            τ (wordAnchorFiberIdx (k := k) a ys i t) = (Φ i t).1 := by
    intro i
    have htarget :
        Function.Injective (fun t : Fin (wordAnchorFiberList (k := k) a ys i).length =>
          (Φ i t).1) := by
      intro t u htu
      apply hΦ i
      exact Fin.ext htu
    exact exists_nat_perm_map_injective_tuple
      (idx := wordAnchorFiberIdx (k := k) a ys i)
      (target := fun t : Fin (wordAnchorFiberList (k := k) a ys i).length =>
        (Φ i t).1)
      (wordAnchorFiberIdx_injective (k := k) a ys i)
      htarget
  choose σ hσ using hrow
  exact ⟨σ, hσ⟩

lemma wordRowEmpiricalProduct_abs_le_one
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (n : ℕ) (ω : ℕ → Fin k) :
    |wordRowEmpiricalProduct (k := k) a ys i n ω| ≤ 1 := by
  exact rowSuccessorEmpiricalFreqProduct_abs_le_one
    (k := k) (wordAnchorFiberList (k := k) a ys i).length
    (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
    (wordAnchorFiberValue (k := k) a ys i) n ω

lemma wordRowDirectingProduct_abs_le_one
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (ω : ℕ → Fin k) :
    |directingRowKernelCellRealProduct
      (k := k) P (wordAnchorFiberList (k := k) a ys i).length
      (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
      (wordAnchorFiberValue (k := k) a ys i) ω| ≤ 1 := by
  exact directingRowKernelCellRealProduct_abs_le_one
    (k := k) P (wordAnchorFiberList (k := k) a ys i).length
    (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
    (wordAnchorFiberValue (k := k) a ys i) ω

lemma wordRowTupleIndicator_abs_le_one
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) (n : ℕ)
    (φ : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n)
    (ω : ℕ → Fin k) :
    |wordRowTupleIndicator (k := k) a ys i n φ ω| ≤ 1 := by
  exact successorReadProductIndicatorReal_abs_le_one
    (k := k) (wordAnchorFiberList (k := k) a ys i).length
    (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
    (fun j => (φ j).1)
    (wordAnchorFiberValue (k := k) a ys i) ω

lemma wordAllRowsTupleIndicator_abs_le_one
    (a : Fin k) (ys : List (Fin k)) (n : ℕ)
    (Φ : (i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n)
    (ω : ℕ → Fin k) :
    |wordAllRowsTupleIndicator (k := k) a ys n Φ ω| ≤ 1 := by
  rw [wordAllRowsTupleIndicator, Finset.abs_prod]
  exact Finset.prod_le_one
    (fun _ _ => abs_nonneg _)
    (fun i _ => wordRowTupleIndicator_abs_le_one (k := k) a ys i n (Φ i) ω)

lemma wordAllRowsEmpiricalProduct_abs_le_one
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) (ω : ℕ → Fin k) :
    |wordAllRowsEmpiricalProduct (k := k) a ys n ω| ≤ 1 := by
  rw [wordAllRowsEmpiricalProduct, Finset.abs_prod]
  exact Finset.prod_le_one
    (fun _ _ => abs_nonneg _)
    (fun i _ => wordRowEmpiricalProduct_abs_le_one (k := k) a ys i n ω)

lemma wordAllRowsDirectingProduct_abs_le_one
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (a : Fin k) (ys : List (Fin k)) (ω : ℕ → Fin k) :
    |wordAllRowsDirectingProduct (k := k) P a ys ω| ≤ 1 := by
  rw [wordAllRowsDirectingProduct, Finset.abs_prod]
  exact Finset.prod_le_one
    (fun _ _ => abs_nonneg _)
    (fun i _ => wordRowDirectingProduct_abs_le_one (k := k) P a ys i ω)

lemma aestronglyMeasurable_wordAllRowsEmpiricalProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω : ℕ → Fin k => wordAllRowsEmpiricalProduct (k := k) a ys n ω) P := by
  have hprod :
      AEStronglyMeasurable
        (∏ i : Fin k, fun ω : ℕ → Fin k =>
          rowSuccessorEmpiricalFreqProduct
            (k := k) (wordAnchorFiberList (k := k) a ys i).length
            (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
            (wordAnchorFiberValue (k := k) a ys i) n ω) P :=
    Finset.aestronglyMeasurable_prod (s := (Finset.univ : Finset (Fin k)))
      (f := fun i ω =>
        rowSuccessorEmpiricalFreqProduct
          (k := k) (wordAnchorFiberList (k := k) a ys i).length
          (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
          (wordAnchorFiberValue (k := k) a ys i) n ω)
      (fun i _ =>
        aestronglyMeasurable_rowSuccessorEmpiricalFreqProduct
          (k := k) P (wordAnchorFiberList (k := k) a ys i).length
          (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
          (wordAnchorFiberValue (k := k) a ys i) n)
  refine hprod.congr ?_
  filter_upwards with ω
  simp [wordAllRowsEmpiricalProduct, wordRowEmpiricalProduct, Finset.prod_apply]

lemma aestronglyMeasurable_wordAllRowsDirectingProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (a : Fin k) (ys : List (Fin k)) :
    AEStronglyMeasurable
      (fun ω : ℕ → Fin k => wordAllRowsDirectingProduct (k := k) P a ys ω) P := by
  have hprod :
      AEStronglyMeasurable
        (∏ i : Fin k, fun ω : ℕ → Fin k =>
          directingRowKernelCellRealProduct
            (k := k) P (wordAnchorFiberList (k := k) a ys i).length
            (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
            (wordAnchorFiberValue (k := k) a ys i) ω) P :=
    Finset.aestronglyMeasurable_prod (s := (Finset.univ : Finset (Fin k)))
      (f := fun i ω =>
        directingRowKernelCellRealProduct
          (k := k) P (wordAnchorFiberList (k := k) a ys i).length
          (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
          (wordAnchorFiberValue (k := k) a ys i) ω)
      (fun i _ =>
        (measurable_directingRowKernelCellRealProduct
          (k := k) P (wordAnchorFiberList (k := k) a ys i).length
          (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
          (wordAnchorFiberValue (k := k) a ys i)).aestronglyMeasurable)
  refine hprod.congr ?_
  filter_upwards with ω
  simp [wordAllRowsDirectingProduct, Finset.prod_apply]

lemma integrable_wordAllRowsEmpiricalProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) :
    Integrable
      (fun ω : ℕ → Fin k => wordAllRowsEmpiricalProduct (k := k) a ys n ω) P := by
  refine Integrable.of_bound
    (aestronglyMeasurable_wordAllRowsEmpiricalProduct (k := k) P a ys n)
    1 ?_
  filter_upwards with ω
  simpa [Real.norm_eq_abs] using
    wordAllRowsEmpiricalProduct_abs_le_one (k := k) a ys n ω

lemma integrable_wordAllRowsDirectingProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (a : Fin k) (ys : List (Fin k)) :
    Integrable
      (fun ω : ℕ → Fin k => wordAllRowsDirectingProduct (k := k) P a ys ω) P := by
  refine Integrable.of_bound
    (aestronglyMeasurable_wordAllRowsDirectingProduct (k := k) P a ys)
    1 ?_
  filter_upwards with ω
  simpa [Real.norm_eq_abs] using
    wordAllRowsDirectingProduct_abs_le_one (k := k) P a ys ω

lemma integrable_wordAllRowsTupleIndicator_of_finite
    (P : Measure (ℕ → Fin k)) [IsFiniteMeasure P]
    (a : Fin k) (ys : List (Fin k)) (n : ℕ)
    (Φ : (i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) :
    Integrable
      (fun ω : ℕ → Fin k => wordAllRowsTupleIndicator (k := k) a ys n Φ ω) P := by
  rw [wordAllRowsTupleIndicator_eq_event_indicator]
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_wordAllRowsTupleEvent (k := k) a ys n Φ)

lemma integrable_wordAllRowsAllTupleAverage_of_finite
    (P : Measure (ℕ → Fin k)) [IsFiniteMeasure P]
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) :
    Integrable
      (fun ω : ℕ → Fin k => wordAllRowsAllTupleAverage (k := k) a ys n ω) P := by
  unfold wordAllRowsAllTupleAverage
  exact
    (MeasureTheory.integrable_finsetSum Finset.univ
      (fun Φ _hΦ =>
        integrable_wordAllRowsTupleIndicator_of_finite (k := k) P a ys n Φ)).const_mul
      (wordAllRowsEmpiricalCoeff (k := k) a ys n)

lemma integrable_wordAllRowsEmpiricalInjectiveTupleAverage_of_finite
    (P : Measure (ℕ → Fin k)) [IsFiniteMeasure P]
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) :
    Integrable
      (fun ω : ℕ → Fin k =>
        wordAllRowsEmpiricalInjectiveTupleAverage (k := k) a ys n ω) P := by
  unfold wordAllRowsEmpiricalInjectiveTupleAverage
  exact
    (MeasureTheory.integrable_finsetSum
      (wordAllRowsInjectiveTuples (k := k) a ys n)
      (fun Φ _hΦ =>
        integrable_wordAllRowsTupleIndicator_of_finite (k := k) P a ys n Φ)).const_mul
      (wordAllRowsEmpiricalCoeff (k := k) a ys n)

lemma integrable_wordAllRowsNormalizedInjectiveTupleAverage_of_finite
    (P : Measure (ℕ → Fin k)) [IsFiniteMeasure P]
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) :
    Integrable
      (fun ω : ℕ → Fin k =>
        wordAllRowsNormalizedInjectiveTupleAverage (k := k) a ys n ω) P := by
  unfold wordAllRowsNormalizedInjectiveTupleAverage
  exact
    (MeasureTheory.integrable_finsetSum
      (wordAllRowsInjectiveTuples (k := k) a ys n)
      (fun Φ _hΦ =>
        integrable_wordAllRowsTupleIndicator_of_finite (k := k) P a ys n Φ)).const_mul
      (1 / ((wordAllRowsInjectiveTuples (k := k) a ys n).card : ℝ))

lemma abs_setIntegral_wordAllRowsAllTupleAverage_sub_empiricalInjectiveAverage_le
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    {s : Set (ℕ → Fin k)}
    (a : Fin k) (ys : List (Fin k)) (n : ℕ) :
    |∫ ω in s,
        wordAllRowsAllTupleAverage (k := k) a ys n ω -
          wordAllRowsEmpiricalInjectiveTupleAverage (k := k) a ys n ω ∂P|
      ≤
    wordAllRowsEmpiricalCoeff (k := k) a ys n *
      ((wordAllRowsNoninjectiveTuples (k := k) a ys n).card : ℝ) := by
  classical
  let good := wordAllRowsInjectiveTuples (k := k) a ys n
  let bad := wordAllRowsNoninjectiveTuples (k := k) a ys n
  let F :
      ((i : Fin k) →
        Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) →
        (ℕ → Fin k) → ℝ :=
    fun Φ ω => wordAllRowsTupleIndicator (k := k) a ys n Φ ω
  let mass : ℝ :=
    wordAllRowsEmpiricalCoeff (k := k) a ys n * (bad.card : ℝ)
  have hcoeff_nonneg : 0 ≤ wordAllRowsEmpiricalCoeff (k := k) a ys n := by
    dsimp [wordAllRowsEmpiricalCoeff]
    positivity
  have hmass_nonneg : 0 ≤ mass := by
    dsimp [mass]
    positivity
  have hsplit :
      ∀ ω : ℕ → Fin k,
        (Finset.univ.sum fun Φ => F Φ ω) =
          good.sum (fun Φ => F Φ ω) + bad.sum (fun Φ => F Φ ω) := by
    intro ω
    have h :=
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset ((i : Fin k) →
          Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n)))
        (p := fun Φ => wordAllRowsInjective (k := k) a ys n Φ)
        (f := fun Φ => F Φ ω)).symm
    simpa [good, bad, wordAllRowsInjectiveTuples, wordAllRowsNoninjectiveTuples] using h
  have hdiff :
      (fun ω : ℕ → Fin k =>
        wordAllRowsAllTupleAverage (k := k) a ys n ω -
          wordAllRowsEmpiricalInjectiveTupleAverage (k := k) a ys n ω)
      =
      (fun ω : ℕ → Fin k =>
        wordAllRowsEmpiricalCoeff (k := k) a ys n * bad.sum (fun Φ => F Φ ω)) := by
    funext ω
    dsimp [wordAllRowsAllTupleAverage, wordAllRowsEmpiricalInjectiveTupleAverage, F]
    rw [hsplit ω]
    ring
  have hpoint : ∀ ω : ℕ → Fin k,
      |wordAllRowsEmpiricalCoeff (k := k) a ys n * bad.sum (fun Φ => F Φ ω)| ≤ mass := by
    intro ω
    have hsum : |bad.sum (fun Φ => F Φ ω)| ≤ (bad.card : ℝ) := by
      calc
        |bad.sum (fun Φ => F Φ ω)|
            ≤ bad.sum (fun Φ => |F Φ ω|) := Finset.abs_sum_le_sum_abs _ _
        _ ≤ bad.sum (fun _Φ => (1 : ℝ)) := by
            exact Finset.sum_le_sum (fun Φ _hΦ =>
              wordAllRowsTupleIndicator_abs_le_one (k := k) a ys n Φ ω)
        _ = (bad.card : ℝ) := by simp
    calc
      |wordAllRowsEmpiricalCoeff (k := k) a ys n * bad.sum (fun Φ => F Φ ω)|
          =
        wordAllRowsEmpiricalCoeff (k := k) a ys n * |bad.sum (fun Φ => F Φ ω)| := by
          rw [abs_mul, abs_of_nonneg hcoeff_nonneg]
      _ ≤ wordAllRowsEmpiricalCoeff (k := k) a ys n * (bad.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsum hcoeff_nonneg
      _ = mass := by rfl
  have hnorm :=
    norm_setIntegral_le_of_norm_le_const
      (μ := P) (s := s)
      (f := fun ω : ℕ → Fin k =>
        wordAllRowsEmpiricalCoeff (k := k) a ys n * bad.sum (fun Φ => F Φ ω))
      (C := mass)
      (measure_lt_top P s)
      (fun ω _hω => by
        simpa [Real.norm_eq_abs] using hpoint ω)
  have hmeasure : mass * P.real s ≤ mass := by
    calc
      mass * P.real s ≤ mass * 1 := by
        exact mul_le_mul_of_nonneg_left measureReal_le_one hmass_nonneg
      _ = mass := by ring
  have habs :
      |∫ ω in s,
        wordAllRowsEmpiricalCoeff (k := k) a ys n * bad.sum (fun Φ => F Φ ω) ∂P|
        ≤ mass := by
    simpa [Real.norm_eq_abs] using hnorm.trans hmeasure
  simpa [hdiff, good, bad, mass] using habs

theorem setIntegral_wordAllRowsAllTupleAverage_sub_empiricalInjectiveAverage_tendsto_zero
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    {s : Set (ℕ → Fin k)} (a : Fin k) (ys : List (Fin k)) :
    Tendsto
      (fun n : ℕ =>
        |∫ ω in s,
          wordAllRowsAllTupleAverage (k := k) a ys n ω -
            wordAllRowsEmpiricalInjectiveTupleAverage (k := k) a ys n ω ∂P|)
      atTop (nhds 0) := by
  let diffInt : ℕ → ℝ := fun n =>
    |∫ ω in s,
      wordAllRowsAllTupleAverage (k := k) a ys n ω -
        wordAllRowsEmpiricalInjectiveTupleAverage (k := k) a ys n ω ∂P|
  let mass : ℕ → ℝ := fun n =>
    wordAllRowsEmpiricalCoeff (k := k) a ys n *
      ((wordAllRowsNoninjectiveTuples (k := k) a ys n).card : ℝ)
  have hdiff_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ diffInt n :=
    Filter.Eventually.of_forall (fun n => by
      dsimp [diffInt]
      positivity)
  have hdiff_le : ∀ᶠ n : ℕ in atTop, diffInt n ≤ mass n :=
    Filter.Eventually.of_forall (fun n =>
      abs_setIntegral_wordAllRowsAllTupleAverage_sub_empiricalInjectiveAverage_le
        (k := k) P a ys n)
  have hmass : Tendsto mass atTop (nhds 0) := by
    simpa [mass] using wordAllRowsNoninjectiveMass_tendsto_zero (k := k) a ys
  simpa [diffInt] using squeeze_zero' hdiff_nonneg hdiff_le hmass

lemma abs_setIntegral_wordAllRowsNormalizedInjectiveAverage_sub_empiricalInjectiveAverage_le
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    {s : Set (ℕ → Fin k)}
    (a : Fin k) (ys : List (Fin k)) {n : ℕ} (hn : ys.length ≤ n) :
    |∫ ω in s,
        wordAllRowsNormalizedInjectiveTupleAverage (k := k) a ys n ω -
          wordAllRowsEmpiricalInjectiveTupleAverage (k := k) a ys n ω ∂P|
      ≤
    |1 - wordAllRowsEmpiricalCoeff (k := k) a ys n *
      ((wordAllRowsInjectiveTuples (k := k) a ys n).card : ℝ)| := by
  classical
  let S := wordAllRowsInjectiveTuples (k := k) a ys n
  let c : ℝ := wordAllRowsEmpiricalCoeff (k := k) a ys n
  let F :
      ((i : Fin k) →
        Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) →
        (ℕ → Fin k) → ℝ :=
    fun Φ ω => wordAllRowsTupleIndicator (k := k) a ys n Φ ω
  have hS : S.Nonempty := by
    exact wordAllRowsInjectiveTuples_nonempty (k := k) a ys
      (fun i => wordAnchorFiberList_length_le_of_ys_length_le (k := k) a ys hn i)
  have hcard_nat : S.card ≠ 0 := Finset.card_ne_zero.mpr hS
  have hcard_ne : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hcard_nonneg : 0 ≤ (S.card : ℝ) := by positivity
  have hcoeff :
      |(1 / (S.card : ℝ)) - c| * (S.card : ℝ) =
        |1 - c * (S.card : ℝ)| := by
    have hmul :
        ((1 / (S.card : ℝ)) - c) * (S.card : ℝ) =
          1 - c * (S.card : ℝ) := by
      field_simp [hcard_ne]
    calc
      |(1 / (S.card : ℝ)) - c| * (S.card : ℝ)
          =
        |(1 / (S.card : ℝ)) - c| * |(S.card : ℝ)| := by
          rw [abs_of_nonneg hcard_nonneg]
      _ = |((1 / (S.card : ℝ)) - c) * (S.card : ℝ)| := by
          rw [abs_mul]
      _ = |1 - c * (S.card : ℝ)| := by
          rw [hmul]
  have hdiff :
      (fun ω : ℕ → Fin k =>
        wordAllRowsNormalizedInjectiveTupleAverage (k := k) a ys n ω -
          wordAllRowsEmpiricalInjectiveTupleAverage (k := k) a ys n ω)
      =
      (fun ω : ℕ → Fin k =>
        ((1 / (S.card : ℝ)) - c) * S.sum (fun Φ => F Φ ω)) := by
    funext ω
    dsimp [wordAllRowsNormalizedInjectiveTupleAverage,
      wordAllRowsEmpiricalInjectiveTupleAverage, S, c, F]
    ring
  let upper : ℝ := |1 - c * (S.card : ℝ)|
  have hpoint : ∀ ω : ℕ → Fin k,
      |((1 / (S.card : ℝ)) - c) * S.sum (fun Φ => F Φ ω)| ≤ upper := by
    intro ω
    have hsum : |S.sum (fun Φ => F Φ ω)| ≤ (S.card : ℝ) := by
      calc
        |S.sum (fun Φ => F Φ ω)|
            ≤ S.sum (fun Φ => |F Φ ω|) := Finset.abs_sum_le_sum_abs _ _
        _ ≤ S.sum (fun _Φ => (1 : ℝ)) := by
            exact Finset.sum_le_sum (fun Φ _hΦ =>
              wordAllRowsTupleIndicator_abs_le_one (k := k) a ys n Φ ω)
        _ = (S.card : ℝ) := by simp
    calc
      |((1 / (S.card : ℝ)) - c) * S.sum (fun Φ => F Φ ω)|
          =
        |(1 / (S.card : ℝ)) - c| * |S.sum (fun Φ => F Φ ω)| := by
          rw [abs_mul]
      _ ≤ |(1 / (S.card : ℝ)) - c| * (S.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = upper := hcoeff
  have hnorm :=
    norm_setIntegral_le_of_norm_le_const
      (μ := P) (s := s)
      (f := fun ω : ℕ → Fin k =>
        ((1 / (S.card : ℝ)) - c) * S.sum (fun Φ => F Φ ω))
      (C := upper)
      (measure_lt_top P s)
      (fun ω _hω => by
        simpa [Real.norm_eq_abs] using hpoint ω)
  have hmeasure : upper * P.real s ≤ upper := by
    calc
      upper * P.real s ≤ upper * 1 := by
        exact mul_le_mul_of_nonneg_left measureReal_le_one (abs_nonneg _)
      _ = upper := by ring
  have habs :
      |∫ ω in s,
        ((1 / (S.card : ℝ)) - c) * S.sum (fun Φ => F Φ ω) ∂P|
        ≤ upper := by
    simpa [Real.norm_eq_abs] using hnorm.trans hmeasure
  simpa [hdiff, S, c, upper] using habs

theorem setIntegral_wordAllRowsNormalizedInjectiveAverage_sub_empiricalInjectiveAverage_tendsto_zero
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    {s : Set (ℕ → Fin k)} (a : Fin k) (ys : List (Fin k)) :
    Tendsto
      (fun n : ℕ =>
        |∫ ω in s,
          wordAllRowsNormalizedInjectiveTupleAverage (k := k) a ys n ω -
            wordAllRowsEmpiricalInjectiveTupleAverage (k := k) a ys n ω ∂P|)
      atTop (nhds 0) := by
  let diffInt : ℕ → ℝ := fun n =>
    |∫ ω in s,
      wordAllRowsNormalizedInjectiveTupleAverage (k := k) a ys n ω -
        wordAllRowsEmpiricalInjectiveTupleAverage (k := k) a ys n ω ∂P|
  let mass : ℕ → ℝ := fun n =>
    wordAllRowsEmpiricalCoeff (k := k) a ys n *
      ((wordAllRowsInjectiveTuples (k := k) a ys n).card : ℝ)
  have hdiff_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ diffInt n :=
    Filter.Eventually.of_forall (fun n => by
      dsimp [diffInt]
      positivity)
  have hdiff_le : ∀ᶠ n : ℕ in atTop, diffInt n ≤ |1 - mass n| := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨ys.length, ?_⟩
    intro n hn
    exact abs_setIntegral_wordAllRowsNormalizedInjectiveAverage_sub_empiricalInjectiveAverage_le
      (k := k) P a ys hn
  have hmass : Tendsto mass atTop (nhds 1) := by
    simpa [mass] using wordAllRowsInjectiveMass_tendsto_one (k := k) a ys
  have hupper : Tendsto (fun n => |1 - mass n|) atTop (nhds 0) := by
    have hsub : Tendsto (fun n => 1 - mass n) atTop (nhds (1 - 1)) :=
      tendsto_const_nhds.sub hmass
    simpa using Filter.Tendsto.abs hsub
  simpa [diffInt] using squeeze_zero' hdiff_nonneg hdiff_le hupper

/-- Generic simultaneous spreading equality for finite successor-matrix reads. -/
theorem successorMatrixPE_spreading_map_eq
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (σ : Fin k → Equiv.Perm ℕ) :
    Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω
              ((σ (anchor j)) (idx j))) P
      =
    Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) P :=
  hPE m anchor idx σ

/-- Event-form simultaneous spreading for finite successor-matrix reads. -/
theorem successorMatrixPE_spreading_event_eq
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (σ : Fin k → Equiv.Perm ℕ) (value : Fin m → Fin k) :
    P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω
            ((σ (anchor j)) (idx j)) = value j}
      =
    P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j) = value j} := by
  classical
  let shiftedIdx : Fin m → ℕ := fun j => (σ (anchor j)) (idx j)
  let A : Set (Fin m → Fin k) := {x | ∀ j : Fin m, x j = value j}
  have hA : MeasurableSet A := by
    have hAeq : A = ({value} : Set (Fin m → Fin k)) := by
      ext x
      constructor
      · intro hx
        exact funext hx
      · intro hx j
        have hx' : x = value := by
          simpa using hx
        exact congrFun hx' j
    simp [hAeq]
  have hmap :=
    successorMatrixPE_spreading_map_eq (k := k) P hPE m anchor idx σ
  have hmap_eval :
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω
              ((σ (anchor j)) (idx j))) P) A
      =
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) P) A := by
    exact congrArg (fun M : Measure (Fin m → Fin k) => M A) hmap
  have hleft :
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω
              ((σ (anchor j)) (idx j))) P) A
        =
      P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω
            ((σ (anchor j)) (idx j)) = value j} := by
    have hmeas :
        Measurable
          (fun ω : ℕ → Fin k =>
            fun j : Fin m =>
              rowSuccessorVisitProcess (k := k) (anchor j) ω
                ((σ (anchor j)) (idx j))) := by
      simpa [shiftedIdx] using
        measurable_successorMatrix_read (k := k) m anchor shiftedIdx
    simpa [A] using
      (Measure.map_apply
        (μ := P)
        (f := fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω
              ((σ (anchor j)) (idx j)))
        (s := A) hmeas hA)
  have hright :
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) P) A
        =
      P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j) = value j} := by
    have hmeas :
        Measurable
          (fun ω : ℕ → Fin k =>
            fun j : Fin m =>
              rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) :=
      measurable_successorMatrix_read (k := k) m anchor idx
    simpa [A] using
      (Measure.map_apply
        (μ := P)
        (f := fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j))
        (s := A) hmeas hA)
  calc
    P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω
            ((σ (anchor j)) (idx j)) = value j}
        =
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω
              ((σ (anchor j)) (idx j))) P) A := hleft.symm
    _ =
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) P) A := hmap_eval
    _ =
      P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j) = value j} := hright

theorem successorMatrixPE_spreading_successorReadEvent_eq
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (σ : Fin k → Equiv.Perm ℕ) (value : Fin m → Fin k) :
    P (successorReadEvent (k := k) m anchor
        (fun j => (σ (anchor j)) (idx j)) value)
      =
    P (successorReadEvent (k := k) m anchor idx value) := by
  simpa [successorReadEvent] using
    successorMatrixPE_spreading_event_eq (k := k) P hPE m anchor idx σ value

theorem successorMatrixPE_wordAllRowsTupleEvent_eq_sourceEvent_of_injective
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k)) {n : ℕ}
    (Φ : (i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n)
    (hΦ : wordAllRowsInjective (k := k) a ys n Φ) :
    P (wordAllRowsTupleEvent (k := k) a ys n Φ) =
      P (wordAllRowsSourceEvent (k := k) a ys) := by
  classical
  rcases exists_rowPerms_map_wordAnchorFiberIdx (k := k) a ys Φ hΦ with ⟨σ, hσ⟩
  let C := Sigma fun i : Fin k => Fin (wordAnchorFiberList (k := k) a ys i).length
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let anchor : Fin (Fintype.card C) → Fin k := fun j => (e.symm j).1
  let idx : Fin (Fintype.card C) → ℕ :=
    fun j => wordAnchorFiberIdx (k := k) a ys (e.symm j).1 (e.symm j).2
  let value : Fin (Fintype.card C) → Fin k :=
    fun j => wordAnchorFiberValue (k := k) a ys (e.symm j).1 (e.symm j).2
  have hspread :=
    successorMatrixPE_spreading_successorReadEvent_eq
      (k := k) P hPE (Fintype.card C) anchor idx σ value
  have hshift_set :
      successorReadEvent (k := k) (Fintype.card C) anchor
          (fun j => (σ (anchor j)) (idx j)) value
        =
      wordAllRowsTupleEvent (k := k) a ys n Φ := by
    ext ω
    constructor
    · intro hω i t
      have hω' :
          ∀ j : Fin (Fintype.card C),
            rowSuccessorVisitProcess (k := k) (anchor j) ω
                ((σ (anchor j)) (idx j)) = value j := by
        simpa [successorReadEvent] using hω
      have h := hω' (e ⟨i, t⟩)
      have he : e.symm (e ⟨i, t⟩) = ⟨i, t⟩ := e.symm_apply_apply ⟨i, t⟩
      dsimp [anchor, idx, value] at h
      rw [he] at h
      simpa [C, hσ i t] using h
    · intro hω
      have hω' :
          ∀ i : Fin k,
            ∀ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
              rowSuccessorVisitProcess (k := k) i ω (Φ i t).1 =
                wordAnchorFiberValue (k := k) a ys i t := by
        simpa [wordAllRowsTupleEvent] using hω
      intro j
      let c : C := e.symm j
      have h := hω' c.1 c.2
      simpa [successorReadEvent, anchor, idx, value, C, c, hσ c.1 c.2] using h
  have hsource_set :
      successorReadEvent (k := k) (Fintype.card C) anchor idx value =
        wordAllRowsSourceEvent (k := k) a ys := by
    ext ω
    constructor
    · intro hω i t
      have hω' :
          ∀ j : Fin (Fintype.card C),
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j) = value j := by
        simpa [successorReadEvent] using hω
      have h := hω' (e ⟨i, t⟩)
      have he : e.symm (e ⟨i, t⟩) = ⟨i, t⟩ := e.symm_apply_apply ⟨i, t⟩
      dsimp [anchor, idx, value] at h
      rw [he] at h
      simpa [C] using h
    · intro hω
      have hω' :
          ∀ i : Fin k,
            ∀ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
              rowSuccessorVisitProcess (k := k) i ω
                  (wordAnchorFiberIdx (k := k) a ys i t) =
                wordAnchorFiberValue (k := k) a ys i t := by
        simpa [wordAllRowsSourceEvent] using hω
      intro j
      let c : C := e.symm j
      have h := hω' c.1 c.2
      simpa [successorReadEvent, anchor, idx, value, C, c] using h
  calc
    P (wordAllRowsTupleEvent (k := k) a ys n Φ)
        =
      P (successorReadEvent (k := k) (Fintype.card C) anchor
        (fun j => (σ (anchor j)) (idx j)) value) := by
          rw [hshift_set]
    _ =
      P (successorReadEvent (k := k) (Fintype.card C) anchor idx value) := hspread
    _ =
      P (wordAllRowsSourceEvent (k := k) a ys) := by
        rw [hsource_set]

theorem integral_wordAllRowsTupleIndicator_eq_sourceEvent_toReal_of_injective
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k)) {n : ℕ}
    (Φ : (i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n)
    (hΦ : wordAllRowsInjective (k := k) a ys n Φ) :
    ∫ ω, wordAllRowsTupleIndicator (k := k) a ys n Φ ω ∂P =
      (P (wordAllRowsSourceEvent (k := k) a ys)).toReal := by
  rw [wordAllRowsTupleIndicator_eq_event_indicator]
  have hInt :=
    MeasureTheory.integral_indicator_one
      (μ := P)
      (s := wordAllRowsTupleEvent (k := k) a ys n Φ)
      (measurableSet_wordAllRowsTupleEvent (k := k) a ys n Φ)
  have hEvent :=
    successorMatrixPE_wordAllRowsTupleEvent_eq_sourceEvent_of_injective
      (k := k) P hPE a ys Φ hΦ
  calc
    ∫ ω, (wordAllRowsTupleEvent (k := k) a ys n Φ).indicator
        (1 : (ℕ → Fin k) → ℝ) ω ∂P
        =
      (P (wordAllRowsTupleEvent (k := k) a ys n Φ)).toReal := by
        simpa [Measure.real] using hInt
    _ =
      (P (wordAllRowsSourceEvent (k := k) a ys)).toReal := by
        rw [hEvent]

theorem integral_wordAllRowsTupleIndicator_eq_wordSuccessorReadEvent_toReal_of_injective
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k)) {n : ℕ}
    (Φ : (i : Fin k) →
      Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n)
    (hΦ : wordAllRowsInjective (k := k) a ys n Φ) :
    ∫ ω, wordAllRowsTupleIndicator (k := k) a ys n Φ ω ∂P =
      (P (successorReadEvent (k := k) ys.length
        (fun j : Fin ys.length => (a :: ys).getD j.1 a)
        (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
        (wordSuccessorTuple (k := k) a ys))).toReal := by
  rw [integral_wordAllRowsTupleIndicator_eq_sourceEvent_toReal_of_injective
    (k := k) P hPE a ys Φ hΦ]
  rw [wordAllRowsSourceEvent_eq_wordSuccessorReadEvent (k := k) a ys]

/-- Spreading equality with all non-selected rows fixed pointwise. -/
theorem successorMatrixPE_oneRow_spreading_map_eq
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (i : Fin k) (τ : Equiv.Perm ℕ) :
    Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω
              ((oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j))) P
      =
    Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) P := by
  simpa [oneRowSpreadingPerm] using
    hPE m anchor idx (oneRowSpreadingPerm (k := k) i τ)

/-- Event-form spreading equality for a finite successor-matrix read. -/
theorem successorMatrixPE_oneRow_spreading_event_eq
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (i : Fin k) (τ : Equiv.Perm ℕ) (value : Fin m → Fin k) :
    P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω
            ((oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)) = value j}
      =
    P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j) = value j} := by
  classical
  let shiftedIdx : Fin m → ℕ :=
    fun j => (oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)
  let A : Set (Fin m → Fin k) := {x | ∀ j : Fin m, x j = value j}
  have hA : MeasurableSet A := by
    have hAeq : A = ({value} : Set (Fin m → Fin k)) := by
      ext x
      constructor
      · intro hx
        exact funext hx
      · intro hx j
        have hx' : x = value := by
          simpa using hx
        exact congrFun hx' j
    simp [hAeq]
  have hmap :=
    successorMatrixPE_oneRow_spreading_map_eq
      (k := k) P hPE m anchor idx i τ
  have hmap_eval :
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω
              ((oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j))) P) A
      =
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) P) A := by
    exact congrArg (fun M : Measure (Fin m → Fin k) => M A) hmap
  have hleft :
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω
              ((oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j))) P) A
        =
      P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω
            ((oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)) = value j} := by
    have hmeas :
        Measurable
          (fun ω : ℕ → Fin k =>
            fun j : Fin m =>
              rowSuccessorVisitProcess (k := k) (anchor j) ω
                ((oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j))) := by
      simpa [shiftedIdx] using
        measurable_successorMatrix_read (k := k) m anchor shiftedIdx
    simpa [A] using
      (Measure.map_apply
        (μ := P)
        (f := fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω
              ((oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)))
        (s := A) hmeas hA)
  have hright :
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) P) A
        =
      P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j) = value j} := by
    have hmeas :
        Measurable
          (fun ω : ℕ → Fin k =>
            fun j : Fin m =>
              rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) :=
      measurable_successorMatrix_read (k := k) m anchor idx
    simpa [A] using
      (Measure.map_apply
        (μ := P)
        (f := fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j))
        (s := A) hmeas hA)
  calc
    P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω
            ((oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)) = value j}
        =
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω
              ((oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j))) P) A := hleft.symm
    _ =
      (Measure.map
        (fun ω : ℕ → Fin k =>
          fun j : Fin m =>
            rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) P) A := hmap_eval
    _ =
      P {ω : ℕ → Fin k |
        ∀ j : Fin m,
          rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j) = value j} := hright

theorem successorMatrixPE_oneRow_spreading_successorReadEvent_eq
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (i : Fin k) (τ : Equiv.Perm ℕ) (value : Fin m → Fin k) :
    P (successorReadEvent (k := k) m anchor
        (fun j => (oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)) value)
      =
    P (successorReadEvent (k := k) m anchor idx value) := by
  simpa [successorReadEvent] using
    successorMatrixPE_oneRow_spreading_event_eq
      (k := k) P hPE m anchor idx i τ value

/-- `lintegral` form of one-row spreading for finite products of read indicators. -/
theorem successorMatrixPE_oneRow_spreading_lintegral_indicator_eq
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (i : Fin k) (τ : Equiv.Perm ℕ) (value : Fin m → Fin k) :
    ∫⁻ ω,
        successorReadProductIndicator (k := k) m anchor
          (fun j => (oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)) value ω ∂P
      =
    ∫⁻ ω, successorReadProductIndicator (k := k) m anchor idx value ω ∂P := by
  rw [lintegral_successorReadProductIndicator_eq_measure,
    lintegral_successorReadProductIndicator_eq_measure]
  exact successorMatrixPE_oneRow_spreading_successorReadEvent_eq
    (k := k) P hPE m anchor idx i τ value

/-- Real-integral form of one-row spreading for finite products of read indicators. -/
theorem successorMatrixPE_oneRow_spreading_integral_indicatorReal_eq
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (i : Fin k) (τ : Equiv.Perm ℕ) (value : Fin m → Fin k) :
    ∫ ω,
        successorReadProductIndicatorReal (k := k) m anchor
          (fun j => (oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)) value ω ∂P
      =
    ∫ ω, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P := by
  rw [integral_successorReadProductIndicatorReal_eq_measure_toReal,
    integral_successorReadProductIndicatorReal_eq_measure_toReal]
  exact congrArg ENNReal.toReal
    (successorMatrixPE_oneRow_spreading_successorReadEvent_eq
      (k := k) P hPE m anchor idx i τ value)

/-- Real-integral spreading for finite read indicators, with no normalization
assumption on the measure. -/
theorem successorMatrixPE_oneRow_spreading_integral_indicatorReal_eq_of_measure
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (i : Fin k) (τ : Equiv.Perm ℕ) (value : Fin m → Fin k) :
    ∫ ω,
        successorReadProductIndicatorReal (k := k) m anchor
          (fun j => (oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)) value ω ∂P
      =
    ∫ ω, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P := by
  rw [integral_successorReadProductIndicatorReal_eq_measure_toReal_of_measure,
    integral_successorReadProductIndicatorReal_eq_measure_toReal_of_measure]
  exact congrArg ENNReal.toReal
    (successorMatrixPE_oneRow_spreading_successorReadEvent_eq
      (k := k) P hPE m anchor idx i τ value)

theorem successorMatrixPE_oneRow_spreading_integral_indicatorReal_mul_rider_eq
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k)
    (r : ℕ) (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (riderValue : Fin r → Fin k)
    (i : Fin k) (τ : Equiv.Perm ℕ)
    (hfixed : ∀ q : Fin r, riderAnchor q ≠ i) :
    ∫ ω,
        successorReadProductIndicatorReal (k := k) m anchor
          (fun j => (oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)) value ω *
        successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω ∂P
      =
    ∫ ω,
        successorReadProductIndicatorReal (k := k) m anchor idx value ω *
        successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω ∂P := by
  have h :=
    successorMatrixPE_oneRow_spreading_integral_indicatorReal_eq_of_measure
      (k := k) P hPE (m + r) (Fin.append anchor riderAnchor)
      (Fin.append idx riderIdx) i τ (Fin.append value riderValue)
  have hshift :
      (fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) (m + r)
          (Fin.append anchor riderAnchor)
          (fun j : Fin (m + r) =>
            (oneRowSpreadingPerm (k := k) i τ (Fin.append anchor riderAnchor j))
              (Fin.append idx riderIdx j))
          (Fin.append value riderValue) ω)
        =
      (fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) m anchor
          (fun j => (oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)) value ω *
        successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω) := by
    funext ω
    rw [oneRowSpreadingPerm_append_idx_eq
      (k := k) m r anchor idx riderAnchor riderIdx i τ hfixed]
    exact successorReadProductIndicatorReal_append
      (k := k) m r anchor
      (fun j => (oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)) value
      riderAnchor riderIdx riderValue ω
  have horig :
      (fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) (m + r)
          (Fin.append anchor riderAnchor) (Fin.append idx riderIdx)
          (Fin.append value riderValue) ω)
        =
      (fun ω : ℕ → Fin k =>
        successorReadProductIndicatorReal (k := k) m anchor idx value ω *
        successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω) := by
    funext ω
    exact successorReadProductIndicatorReal_append
      (k := k) m r anchor idx value riderAnchor riderIdx riderValue ω
  change
    ∫ ω,
        (fun ω : ℕ → Fin k =>
          successorReadProductIndicatorReal (k := k) m anchor
            (fun j => (oneRowSpreadingPerm (k := k) i τ (anchor j)) (idx j)) value ω *
          successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω) ω ∂P
      =
    ∫ ω,
        (fun ω : ℕ → Fin k =>
          successorReadProductIndicatorReal (k := k) m anchor idx value ω *
          successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω) ω ∂P
  rw [← hshift, ← horig]
  exact h

theorem successorMatrixPE_oneRow_spreading_integral_indicatorReal_mul_rider_eq_of_injective_target
    (P : Measure (ℕ → Fin k))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (i : Fin k) (idx target : Fin m → ℕ)
    (value : Fin m → Fin k)
    (r : ℕ) (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (riderValue : Fin r → Fin k)
    (hidx : Function.Injective idx) (htarget : Function.Injective target)
    (hfixed : ∀ q : Fin r, riderAnchor q ≠ i) :
    ∫ ω,
        successorReadProductIndicatorReal (k := k) m (fun _ => i) target value ω *
        successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω ∂P
      =
    ∫ ω,
        successorReadProductIndicatorReal (k := k) m (fun _ => i) idx value ω *
        successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω ∂P := by
  rcases exists_nat_perm_map_injective_tuple hidx htarget with ⟨τ, hτ⟩
  have htarget_eq' : (fun j : Fin m => τ (idx j)) = target := by
    funext j
    exact hτ j
  have htarget_eq :
      (fun j : Fin m =>
        (oneRowSpreadingPerm (k := k) i τ ((fun _ : Fin m => i) j)) (idx j)) =
        target := by
    funext j
    simpa using hτ j
  have hspread :=
    successorMatrixPE_oneRow_spreading_integral_indicatorReal_mul_rider_eq
      (k := k) P hPE m (fun _ : Fin m => i) idx value
      r riderAnchor riderIdx riderValue i τ hfixed
  simpa [htarget_eq, htarget_eq'] using hspread

/-! ## Bounded-rider L¹ plumbing -/

lemma integral_fin_average_eq_average_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {K : ℕ}
    (F : Fin K → Ω → ℝ) (hF : ∀ w, Integrable (F w) μ) :
    ∫ ω, (1 / (K : ℝ)) * ∑ w : Fin K, F w ω ∂μ
      =
    (1 / (K : ℝ)) * ∑ w : Fin K, ∫ ω, F w ω ∂μ := by
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum]
  intro w _
  exact hF w

lemma integral_finset_average_eq_average_integral
    {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Finset ι) (c : ℝ) (F : ι → Ω → ℝ)
    (hF : ∀ a ∈ S, Integrable (F a) μ) :
    ∫ ω, c * (S.sum fun a => F a ω) ∂μ =
      c * (S.sum fun a => ∫ ω, F a ω ∂μ) := by
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum]
  intro a ha
  exact hF a ha

lemma fin_average_eq_of_forall_eq {K : ℕ} (hK : 0 < K)
    {x : ℝ} {y : Fin K → ℝ} (h : ∀ w, y w = x) :
    (1 / (K : ℝ)) * ∑ w : Fin K, y w = x := by
  rw [Finset.sum_congr rfl (fun w _ => h w), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr hK.ne']

lemma finset_average_eq_of_forall_mem_eq
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (hS : S.Nonempty)
    {x : ℝ} {y : ι → ℝ} (h : ∀ a ∈ S, y a = x) :
    (1 / (S.card : ℝ)) * S.sum y = x := by
  rw [Finset.sum_congr rfl (fun a ha => h a ha), Finset.sum_const, nsmul_eq_mul]
  have hcard_nat : S.card ≠ 0 := Finset.card_ne_zero.mpr hS
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast hcard_nat
  field_simp [hcard]

theorem successorMatrixPE_integral_wordAllRowsInjectiveTupleAverage_eq_sourceEvent_toReal
    (P : Measure (ℕ → Fin k)) [IsFiniteMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k)) {n : ℕ}
    (hn : ∀ i : Fin k, (wordAnchorFiberList (k := k) a ys i).length ≤ n) :
    ∫ ω,
        (1 / ((wordAllRowsInjectiveTuples (k := k) a ys n).card : ℝ)) *
          ((wordAllRowsInjectiveTuples (k := k) a ys n).sum fun Φ =>
            wordAllRowsTupleIndicator (k := k) a ys n Φ ω) ∂P
      =
    (P (wordAllRowsSourceEvent (k := k) a ys)).toReal := by
  classical
  let S := wordAllRowsInjectiveTuples (k := k) a ys n
  let F :
      ((i : Fin k) →
        Fin (wordAnchorFiberList (k := k) a ys i).length → Fin n) →
        (ℕ → Fin k) → ℝ :=
    fun Φ ω => wordAllRowsTupleIndicator (k := k) a ys n Φ ω
  have hS : S.Nonempty := wordAllRowsInjectiveTuples_nonempty (k := k) a ys hn
  have hF_int : ∀ Φ ∈ S, Integrable (F Φ) P := by
    intro Φ _hΦ
    rw [show F Φ =
        fun ω : ℕ → Fin k => wordAllRowsTupleIndicator (k := k) a ys n Φ ω from rfl]
    rw [wordAllRowsTupleIndicator_eq_event_indicator]
    exact (integrable_const (1 : ℝ)).indicator
      (measurableSet_wordAllRowsTupleEvent (k := k) a ys n Φ)
  have hEach :
      ∀ Φ ∈ S,
        ∫ ω, F Φ ω ∂P = (P (wordAllRowsSourceEvent (k := k) a ys)).toReal := by
    intro Φ hΦ
    have hΦinj : wordAllRowsInjective (k := k) a ys n Φ := by
      exact (Finset.mem_filter.mp hΦ).2
    simpa [F] using
      integral_wordAllRowsTupleIndicator_eq_sourceEvent_toReal_of_injective
        (k := k) P hPE a ys Φ hΦinj
  calc
    ∫ ω,
        (1 / ((wordAllRowsInjectiveTuples (k := k) a ys n).card : ℝ)) *
          ((wordAllRowsInjectiveTuples (k := k) a ys n).sum fun Φ =>
            wordAllRowsTupleIndicator (k := k) a ys n Φ ω) ∂P
        =
      (1 / (S.card : ℝ)) * S.sum (fun Φ => ∫ ω, F Φ ω ∂P) := by
        simpa [S, F] using
          integral_finset_average_eq_average_integral
            (μ := P) S (1 / (S.card : ℝ)) F hF_int
    _ =
      (P (wordAllRowsSourceEvent (k := k) a ys)).toReal := by
        exact finset_average_eq_of_forall_mem_eq S hS hEach

theorem successorMatrixPE_integral_wordAllRowsInjectiveTupleAverage_eq_wordSuccessorReadEvent_toReal
    (P : Measure (ℕ → Fin k)) [IsFiniteMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k)) {n : ℕ}
    (hn : ∀ i : Fin k, (wordAnchorFiberList (k := k) a ys i).length ≤ n) :
    ∫ ω,
        (1 / ((wordAllRowsInjectiveTuples (k := k) a ys n).card : ℝ)) *
          ((wordAllRowsInjectiveTuples (k := k) a ys n).sum fun Φ =>
            wordAllRowsTupleIndicator (k := k) a ys n Φ ω) ∂P
      =
    (P (successorReadEvent (k := k) ys.length
      (fun j : Fin ys.length => (a :: ys).getD j.1 a)
      (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
      (wordSuccessorTuple (k := k) a ys))).toReal := by
  rw [successorMatrixPE_integral_wordAllRowsInjectiveTupleAverage_eq_sourceEvent_toReal
    (k := k) P hPE a ys hn]
  rw [wordAllRowsSourceEvent_eq_wordSuccessorReadEvent (k := k) a ys]

theorem successorMatrixPE_setIntegral_wordAllRowsNormalizedInjectiveTupleAverage_eq_sourceEvent_toReal
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    {s : Set (ℕ → Fin k)} (hs : MeasurableSet s)
    (hPEs : SuccessorMatrixPartialExchangeable (k := k) (P.restrict s))
    (a : Fin k) (ys : List (Fin k)) {n : ℕ}
    (hn : ∀ i : Fin k, (wordAnchorFiberList (k := k) a ys i).length ≤ n) :
    ∫ ω in s,
        wordAllRowsNormalizedInjectiveTupleAverage (k := k) a ys n ω ∂P
      =
    (P (s ∩ wordAllRowsSourceEvent (k := k) a ys)).toReal := by
  have h :=
    successorMatrixPE_integral_wordAllRowsInjectiveTupleAverage_eq_sourceEvent_toReal
      (k := k) (P := P.restrict s) hPEs a ys hn
  rw [Measure.restrict_apply' hs] at h
  simpa [wordAllRowsNormalizedInjectiveTupleAverage, Set.inter_comm] using h

theorem successorMatrixPE_setIntegral_wordAllRowsNormalizedInjectiveTupleAverage_eq_wordSuccessorReadEvent_toReal
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    {s : Set (ℕ → Fin k)} (hs : MeasurableSet s)
    (hPEs : SuccessorMatrixPartialExchangeable (k := k) (P.restrict s))
    (a : Fin k) (ys : List (Fin k)) {n : ℕ}
    (hn : ∀ i : Fin k, (wordAnchorFiberList (k := k) a ys i).length ≤ n) :
    ∫ ω in s,
        wordAllRowsNormalizedInjectiveTupleAverage (k := k) a ys n ω ∂P
      =
    (P (s ∩ successorReadEvent (k := k) ys.length
      (fun j : Fin ys.length => (a :: ys).getD j.1 a)
      (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
      (wordSuccessorTuple (k := k) a ys))).toReal := by
  rw [successorMatrixPE_setIntegral_wordAllRowsNormalizedInjectiveTupleAverage_eq_sourceEvent_toReal
    (k := k) P hs hPEs a ys hn]
  rw [wordAllRowsSourceEvent_eq_wordSuccessorReadEvent (k := k) a ys]

theorem successorMatrixPE_oneRow_spreading_integral_injectiveTupleAverage_indicatorReal_mul_rider_eq
    (P : Measure (ℕ → Fin k)) [IsFiniteMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m n : ℕ) (hmn : m ≤ n) (i : Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k)
    (r : ℕ) (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (riderValue : Fin r → Fin k)
    (hidx : Function.Injective idx)
    (hfixed : ∀ q : Fin r, riderAnchor q ≠ i) :
    ∫ ω,
        successorReadProductIndicatorReal (k := k) m (fun _ => i) idx value ω *
        successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω ∂P
      =
    ∫ ω,
        (1 / ((Finset.univ.filter
            (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)) *
          ((Finset.univ.filter
              (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ =>
            successorReadProductIndicatorReal
              (k := k) m (fun _ => i) (fun j => (φ j).1) value ω *
            successorReadProductIndicatorReal
              (k := k) r riderAnchor riderIdx riderValue ω) ∂P := by
  classical
  let injTuples : Finset (Fin m → Fin n) :=
    Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)
  let F : (Fin m → Fin n) → (ℕ → Fin k) → ℝ :=
    fun φ ω =>
      successorReadProductIndicatorReal (k := k) m (fun _ => i)
        (fun j => (φ j).1) value ω *
      successorReadProductIndicatorReal
        (k := k) r riderAnchor riderIdx riderValue ω
  have hnonempty : injTuples.Nonempty := by
    let base : Fin m → Fin n := fun j => ⟨j.1, lt_of_lt_of_le j.isLt hmn⟩
    have hbase_inj : Function.Injective base := by
      intro a b hab
      have hval : a.1 = b.1 := by
        have hval' := congrArg Fin.val hab
        simpa [base] using hval'
      exact Fin.ext hval
    exact ⟨base, by simp [injTuples, base, hbase_inj]⟩
  have hF_int : ∀ φ ∈ injTuples, Integrable (F φ) P := by
    intro φ hφ
    have hfun :
        F φ =
          fun ω : ℕ → Fin k =>
            successorReadProductIndicatorReal (k := k) (m + r)
              (Fin.append (fun _ : Fin m => i) riderAnchor)
              (Fin.append (fun j : Fin m => (φ j).1) riderIdx)
              (Fin.append value riderValue) ω := by
      funext ω
      dsimp [F]
      symm
      exact successorReadProductIndicatorReal_append
        (k := k) m r (fun _ : Fin m => i)
        (fun j : Fin m => (φ j).1) value riderAnchor riderIdx riderValue ω
    rw [hfun]
    exact integrable_successorReadProductIndicatorReal_of_finite
      (k := k) P (m + r) (Fin.append (fun _ : Fin m => i) riderAnchor)
      (Fin.append (fun j : Fin m => (φ j).1) riderIdx)
      (Fin.append value riderValue)
  have hspread :
      ∀ φ ∈ injTuples,
        ∫ ω, F φ ω ∂P =
          ∫ ω,
            successorReadProductIndicatorReal (k := k) m (fun _ => i) idx value ω *
            successorReadProductIndicatorReal
              (k := k) r riderAnchor riderIdx riderValue ω ∂P := by
    intro φ hφ
    have hφinj : Function.Injective φ := (Finset.mem_filter.mp hφ).2
    have htarget :
        Function.Injective (fun j : Fin m => (φ j).1) := by
      intro a b hab
      apply hφinj
      exact Fin.ext hab
    simpa [F] using
      successorMatrixPE_oneRow_spreading_integral_indicatorReal_mul_rider_eq_of_injective_target
        (k := k) P hPE m i idx (fun j : Fin m => (φ j).1) value
        r riderAnchor riderIdx riderValue hidx htarget hfixed
  calc
    ∫ ω,
        successorReadProductIndicatorReal (k := k) m (fun _ => i) idx value ω *
        successorReadProductIndicatorReal
          (k := k) r riderAnchor riderIdx riderValue ω ∂P
        =
      (1 / (injTuples.card : ℝ)) * injTuples.sum (fun φ => ∫ ω, F φ ω ∂P) := by
        symm
        exact finset_average_eq_of_forall_mem_eq injTuples hnonempty hspread
    _ =
      ∫ ω, (1 / (injTuples.card : ℝ)) * injTuples.sum (fun φ => F φ ω) ∂P := by
        exact
          (integral_finset_average_eq_average_integral
            (μ := P) injTuples (1 / (injTuples.card : ℝ)) F hF_int).symm
    _ =
      ∫ ω,
        (1 / ((Finset.univ.filter
            (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)) *
          ((Finset.univ.filter
              (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ =>
            successorReadProductIndicatorReal
              (k := k) m (fun _ => i) (fun j => (φ j).1) value ω *
            successorReadProductIndicatorReal
              (k := k) r riderAnchor riderIdx riderValue ω) ∂P := by
        rfl

theorem successorMatrixPE_oneRow_spreading_integral_windowAverage_indicatorReal_mul_rider_eq
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    {K : ℕ} (hK : 0 < K)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (value : Fin m → Fin k)
    (r : ℕ) (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (riderValue : Fin r → Fin k)
    (i : Fin k) (τ : Fin K → Equiv.Perm ℕ)
    (hfixed : ∀ q : Fin r, riderAnchor q ≠ i) :
    ∫ ω,
        successorReadProductIndicatorReal (k := k) m anchor idx value ω *
        successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω ∂P
      =
    ∫ ω,
      (1 / (K : ℝ)) *
        ∑ w : Fin K,
          successorReadProductIndicatorReal (k := k) m anchor
            (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
            value ω *
          successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω ∂P := by
  let F : Fin K → (ℕ → Fin k) → ℝ :=
    fun w ω =>
      successorReadProductIndicatorReal (k := k) m anchor
        (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
        value ω *
      successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω
  have hF_int : ∀ w, Integrable (F w) P := by
    intro w
    have hfun :
        F w =
          fun ω : ℕ → Fin k =>
            successorReadProductIndicatorReal (k := k) (m + r)
              (Fin.append anchor riderAnchor)
              (fun j : Fin (m + r) =>
                (oneRowSpreadingPerm (k := k) i (τ w) (Fin.append anchor riderAnchor j))
                  (Fin.append idx riderIdx j))
              (Fin.append value riderValue) ω := by
      funext ω
      dsimp [F]
      rw [oneRowSpreadingPerm_append_idx_eq
        (k := k) m r anchor idx riderAnchor riderIdx i (τ w) hfixed]
      symm
      exact successorReadProductIndicatorReal_append
        (k := k) m r anchor
        (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j)) value
        riderAnchor riderIdx riderValue ω
    rw [hfun]
    exact integrable_successorReadProductIndicatorReal
      (k := k) P (m + r) (Fin.append anchor riderAnchor)
      (fun j : Fin (m + r) =>
        (oneRowSpreadingPerm (k := k) i (τ w) (Fin.append anchor riderAnchor j))
          (Fin.append idx riderIdx j))
      (Fin.append value riderValue)
  have hspread :
      ∀ w : Fin K,
        ∫ ω, F w ω ∂P =
          ∫ ω,
            successorReadProductIndicatorReal (k := k) m anchor idx value ω *
            successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω ∂P := by
    intro w
    simpa [F] using
      successorMatrixPE_oneRow_spreading_integral_indicatorReal_mul_rider_eq
        (k := k) P hPE m anchor idx value r riderAnchor riderIdx riderValue
        i (τ w) hfixed
  calc
    ∫ ω,
        successorReadProductIndicatorReal (k := k) m anchor idx value ω *
        successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω ∂P
        =
      (1 / (K : ℝ)) * ∑ w : Fin K, ∫ ω, F w ω ∂P := by
        symm
        exact fin_average_eq_of_forall_eq hK hspread
    _ =
      ∫ ω, (1 / (K : ℝ)) * ∑ w : Fin K, F w ω ∂P := by
        exact (integral_fin_average_eq_average_integral (μ := P) F hF_int).symm
    _ =
      ∫ ω,
        (1 / (K : ℝ)) *
          ∑ w : Fin K,
            successorReadProductIndicatorReal (k := k) m anchor
              (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
              value ω *
            successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω ∂P := by
        rfl

theorem successorMatrixPE_oneRow_spreading_integral_windowAverage_indicatorReal_eq
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    {K : ℕ} (hK : 0 < K)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (i : Fin k) (τ : Fin K → Equiv.Perm ℕ) (value : Fin m → Fin k) :
    ∫ ω, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P
      =
    ∫ ω,
      (1 / (K : ℝ)) *
        ∑ w : Fin K,
          successorReadProductIndicatorReal (k := k) m anchor
            (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
            value ω ∂P := by
  let F : Fin K → (ℕ → Fin k) → ℝ :=
    fun w ω =>
      successorReadProductIndicatorReal (k := k) m anchor
        (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
        value ω
  have hF_int : ∀ w, Integrable (F w) P := by
    intro w
    exact integrable_successorReadProductIndicatorReal
      (k := k) P m anchor
        (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
        value
  have hspread :
      ∀ w : Fin K,
        ∫ ω, F w ω ∂P =
          ∫ ω, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P := by
    intro w
    simpa [F] using
      successorMatrixPE_oneRow_spreading_integral_indicatorReal_eq
        (k := k) P hPE m anchor idx i (τ w) value
  calc
    ∫ ω, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P
        =
      (1 / (K : ℝ)) * ∑ w : Fin K, ∫ ω, F w ω ∂P := by
        symm
        exact fin_average_eq_of_forall_eq hK hspread
    _ =
      ∫ ω, (1 / (K : ℝ)) * ∑ w : Fin K, F w ω ∂P := by
        exact (integral_fin_average_eq_average_integral (μ := P) F hF_int).symm
    _ =
      ∫ ω,
        (1 / (K : ℝ)) *
          ∑ w : Fin K,
            successorReadProductIndicatorReal (k := k) m anchor
              (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
              value ω ∂P := by
        rfl

theorem successorMatrixPE_oneRow_spreading_integral_windowAverage_indicatorReal_eq_of_finite
    (P : Measure (ℕ → Fin k)) [IsFiniteMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    {K : ℕ} (hK : 0 < K)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (i : Fin k) (τ : Fin K → Equiv.Perm ℕ) (value : Fin m → Fin k) :
    ∫ ω, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P
      =
    ∫ ω,
      (1 / (K : ℝ)) *
        ∑ w : Fin K,
          successorReadProductIndicatorReal (k := k) m anchor
            (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
            value ω ∂P := by
  let F : Fin K → (ℕ → Fin k) → ℝ :=
    fun w ω =>
      successorReadProductIndicatorReal (k := k) m anchor
        (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
        value ω
  have hF_int : ∀ w, Integrable (F w) P := by
    intro w
    exact integrable_successorReadProductIndicatorReal_of_finite
      (k := k) P m anchor
        (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
        value
  have hspread :
      ∀ w : Fin K,
        ∫ ω, F w ω ∂P =
          ∫ ω, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P := by
    intro w
    simpa [F] using
      successorMatrixPE_oneRow_spreading_integral_indicatorReal_eq_of_measure
        (k := k) P hPE m anchor idx i (τ w) value
  calc
    ∫ ω, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P
        =
      (1 / (K : ℝ)) * ∑ w : Fin K, ∫ ω, F w ω ∂P := by
        symm
        exact fin_average_eq_of_forall_eq hK hspread
    _ =
      ∫ ω, (1 / (K : ℝ)) * ∑ w : Fin K, F w ω ∂P := by
        exact (integral_fin_average_eq_average_integral (μ := P) F hF_int).symm
    _ =
      ∫ ω,
        (1 / (K : ℝ)) *
          ∑ w : Fin K,
            successorReadProductIndicatorReal (k := k) m anchor
              (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
              value ω ∂P := by
        rfl

theorem successorMatrixPE_oneRow_spreading_setIntegral_windowAverage_indicatorReal_eq
    (P : Measure (ℕ → Fin k)) [IsFiniteMeasure P]
    {s : Set (ℕ → Fin k)} (_hs : MeasurableSet s)
    (hPEs : SuccessorMatrixPartialExchangeable (k := k) (P.restrict s))
    {K : ℕ} (hK : 0 < K)
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ)
    (i : Fin k) (τ : Fin K → Equiv.Perm ℕ) (value : Fin m → Fin k) :
    ∫ ω in s, successorReadProductIndicatorReal (k := k) m anchor idx value ω ∂P
      =
    ∫ ω in s,
      (1 / (K : ℝ)) *
        ∑ w : Fin K,
          successorReadProductIndicatorReal (k := k) m anchor
            (fun j => (oneRowSpreadingPerm (k := k) i (τ w) (anchor j)) (idx j))
            value ω ∂P := by
  simpa only [Measure.restrict_apply'] using
    successorMatrixPE_oneRow_spreading_integral_windowAverage_indicatorReal_eq_of_finite
      (k := k) (P := P.restrict s) hPEs hK m anchor idx i τ value

lemma bounded_rider_abs_mul_sub_le
    {G avg limit C : ℝ} (hC : 0 ≤ C) (hG : |G| ≤ C) :
    |G * (avg - limit)| ≤ C * |avg - limit| := by
  rw [abs_mul]
  exact mul_le_mul hG le_rfl (abs_nonneg _) hC

/-- Finite products of uniformly bounded factors inherit coordinatewise L¹ convergence. -/
theorem finiteProduct_tendsto_L1_of_factor_tendsto_L1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (f : ℕ → Fin m → Ω → ℝ) (g : Fin m → Ω → ℝ)
    (hf_bdd : ∀ n i ω, |f n i ω| ≤ 1)
    (hg_bdd : ∀ i ω, |g i ω| ≤ 1)
    (hf_meas : ∀ n i, AEStronglyMeasurable (f n i) μ)
    (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ)
    (h_conv :
      ∀ i, Tendsto (fun n => ∫ ω, |f n i ω - g i ω| ∂μ) atTop (nhds 0)) :
    Tendsto
      (fun n => ∫ ω, |∏ i : Fin m, f n i ω - ∏ i : Fin m, g i ω| ∂μ)
      atTop (nhds 0) := by
  exact Exchangeability.DeFinetti.ViaL2.prod_tendsto_L1_of_L1_tendsto
    (μ := μ) f g hf_bdd hg_bdd hf_meas hg_meas h_conv

/-- Multi-cell empirical row-frequency products converge in L¹ to the canonical row-kernel product. -/
theorem rowSuccessorEmpiricalFreqProduct_tendsto_L1_directingRowKernelCellRealProduct_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k) :
    Tendsto
      (fun n =>
        ∫ ω,
          |rowSuccessorEmpiricalFreqProduct (k := k) m anchor value n ω -
            directingRowKernelCellRealProduct (k := k) P m anchor value ω| ∂P)
      atTop (nhds 0) := by
  simpa [rowSuccessorEmpiricalFreqProduct, directingRowKernelCellRealProduct] using
    finiteProduct_tendsto_L1_of_factor_tendsto_L1
      (μ := P)
      (f := fun n j ω =>
        rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n)
      (g := fun j ω =>
        directingRowKernelCellReal (k := k) P (anchor j) (value j) ω)
      (fun n j ω => rowSuccessorEmpiricalFreq_abs_le_one (k := k) (anchor j) (value j) ω n)
      (fun j ω => directingRowKernelCellReal_abs_le_one (k := k) P (anchor j) (value j) ω)
      (fun n j =>
        aestronglyMeasurable_rowSuccessorEmpiricalFreq (k := k) P (anchor j) (value j) n)
      (fun j =>
        (measurable_directingRowKernelCellReal (k := k) P (anchor j) (value j)).aestronglyMeasurable)
      (fun j =>
        rowSuccessorEmpiricalFreq_tendsto_L1_directingRowKernelCellReal_of_successorMatrixPE
          (k := k) P hPE (anchor j) (value j))

/-- Products over all word rows inherit the per-row empirical-product L¹ limit. -/
theorem wordAllRowsEmpiricalProduct_tendsto_L1_directingProduct_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k)) :
    Tendsto
      (fun n =>
        ∫ ω,
          |wordAllRowsEmpiricalProduct (k := k) a ys n ω -
            wordAllRowsDirectingProduct (k := k) P a ys ω| ∂P)
      atTop (nhds 0) := by
  simpa [wordAllRowsEmpiricalProduct, wordAllRowsDirectingProduct, wordRowEmpiricalProduct] using
    finiteProduct_tendsto_L1_of_factor_tendsto_L1
      (μ := P)
      (f := fun n i ω =>
        rowSuccessorEmpiricalFreqProduct
          (k := k) (wordAnchorFiberList (k := k) a ys i).length
          (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
          (wordAnchorFiberValue (k := k) a ys i) n ω)
      (g := fun i ω =>
        directingRowKernelCellRealProduct
          (k := k) P (wordAnchorFiberList (k := k) a ys i).length
          (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
          (wordAnchorFiberValue (k := k) a ys i) ω)
      (fun n i ω =>
        wordRowEmpiricalProduct_abs_le_one (k := k) a ys i n ω)
      (fun i ω =>
        wordRowDirectingProduct_abs_le_one (k := k) P a ys i ω)
      (fun n i =>
        aestronglyMeasurable_rowSuccessorEmpiricalFreqProduct
          (k := k) P (wordAnchorFiberList (k := k) a ys i).length
          (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
          (wordAnchorFiberValue (k := k) a ys i) n)
      (fun i =>
        (measurable_directingRowKernelCellRealProduct
          (k := k) P (wordAnchorFiberList (k := k) a ys i).length
          (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
          (wordAnchorFiberValue (k := k) a ys i)).aestronglyMeasurable)
      (fun i =>
        rowSuccessorEmpiricalFreqProduct_tendsto_L1_directingRowKernelCellRealProduct_of_successorMatrixPE
          (k := k) P hPE (wordAnchorFiberList (k := k) a ys i).length
          (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
          (wordAnchorFiberValue (k := k) a ys i))

/-- Finite products of bounded factors inherit coordinatewise a.e. convergence in L¹. -/
theorem finiteProduct_tendsto_L1_of_factor_ae_tendsto_bounded
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (f : ℕ → Fin m → Ω → ℝ) (g : Fin m → Ω → ℝ)
    (hf_bdd : ∀ n i ω, |f n i ω| ≤ 1)
    (hg_bdd : ∀ i ω, |g i ω| ≤ 1)
    (hf_meas : ∀ n i, AEStronglyMeasurable (f n i) μ)
    (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ)
    (h_ae : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n => f n i ω) atTop (nhds (g i ω))) :
    Tendsto
      (fun n => ∫ ω, |∏ i : Fin m, f n i ω - ∏ i : Fin m, g i ω| ∂μ)
      atTop (nhds 0) := by
  refine finiteProduct_tendsto_L1_of_factor_tendsto_L1
    (μ := μ) f g hf_bdd hg_bdd hf_meas hg_meas ?_
  intro i
  exact tendsto_integral_abs_sub_of_ae_tendsto_bounded
    (μ := μ)
    (fn := fun n ω => f n i ω)
    (f := fun ω => g i ω)
    (fun n => hf_meas n i)
    (hg_meas i)
    (fun n => Filter.Eventually.of_forall (fun ω => hf_bdd n i ω))
    (Filter.Eventually.of_forall (fun ω => hg_bdd i ω))
    (h_ae i)

/-- Convert real-valued L¹ convergence to the lintegral form used by set-integral continuity. -/
theorem lintegral_nnnorm_tendsto_zero_of_integral_abs_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (h_int : ∀ n, Integrable (fun ω => fn n ω - f ω) μ)
    (h :
      Tendsto (fun n => ∫ ω, |fn n ω - f ω| ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫⁻ ω, ‖fn n ω - f ω‖₊ ∂μ) atTop (nhds 0) := by
  have h_ofReal :
      Tendsto
        (fun n => ENNReal.ofReal (∫ ω, |fn n ω - f ω| ∂μ))
        atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal h
  have h_eq :
      ∀ n, (∫⁻ ω, ‖fn n ω - f ω‖₊ ∂μ) =
        ENNReal.ofReal (∫ ω, |fn n ω - f ω| ∂μ) := by
    intro n
    calc
      ∫⁻ ω, ‖fn n ω - f ω‖₊ ∂μ
          = ∫⁻ ω, ‖fn n ω - f ω‖ₑ ∂μ := by
            apply lintegral_congr_ae
            filter_upwards with ω
            exact (enorm_eq_nnnorm (fn n ω - f ω)).symm
      _ = ENNReal.ofReal (∫ ω, ‖fn n ω - f ω‖ ∂μ) := by
          exact (ofReal_integral_norm_eq_lintegral_enorm (h_int n)).symm
      _ = ENNReal.ofReal (∫ ω, |fn n ω - f ω| ∂μ) := by
          simp only [Real.norm_eq_abs]
  simpa [h_eq] using h_ofReal

/-- All-row word empirical products converge in lintegral L¹ form. -/
theorem wordAllRowsEmpiricalProduct_tendsto_lintegral_nnnorm_directingProduct_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k)) :
    Tendsto
      (fun n =>
        ∫⁻ ω,
          ‖wordAllRowsEmpiricalProduct (k := k) a ys n ω -
            wordAllRowsDirectingProduct (k := k) P a ys ω‖₊ ∂P)
      atTop (nhds 0) := by
  exact
    lintegral_nnnorm_tendsto_zero_of_integral_abs_tendsto_zero
      (μ := P)
      (fn := fun n ω => wordAllRowsEmpiricalProduct (k := k) a ys n ω)
      (f := fun ω => wordAllRowsDirectingProduct (k := k) P a ys ω)
      (h_int := fun n =>
        (integrable_wordAllRowsEmpiricalProduct (k := k) P a ys n).sub
          (integrable_wordAllRowsDirectingProduct (k := k) P a ys))
      (wordAllRowsEmpiricalProduct_tendsto_L1_directingProduct_of_successorMatrixPE
        (k := k) P hPE a ys)

/-- Product L¹ convergence, stated directly in the lintegral form needed for bounded riders. -/
theorem finiteProduct_tendsto_lintegral_nnnorm_of_factor_tendsto_L1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (f : ℕ → Fin m → Ω → ℝ) (g : Fin m → Ω → ℝ)
    (hf_bdd : ∀ n i ω, |f n i ω| ≤ 1)
    (hg_bdd : ∀ i ω, |g i ω| ≤ 1)
    (hf_meas : ∀ n i, AEStronglyMeasurable (f n i) μ)
    (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ)
    (h_conv :
      ∀ i, Tendsto (fun n => ∫ ω, |f n i ω - g i ω| ∂μ) atTop (nhds 0))
    (h_int :
      ∀ n, Integrable
        (fun ω => (∏ i : Fin m, f n i ω) - ∏ i : Fin m, g i ω) μ) :
    Tendsto
      (fun n => ∫⁻ ω, ‖(∏ i : Fin m, f n i ω) - ∏ i : Fin m, g i ω‖₊ ∂μ)
      atTop (nhds 0) := by
  exact lintegral_nnnorm_tendsto_zero_of_integral_abs_tendsto_zero
    (μ := μ)
    (fn := fun n ω => ∏ i : Fin m, f n i ω)
    (f := fun ω => ∏ i : Fin m, g i ω)
    h_int
    (finiteProduct_tendsto_L1_of_factor_tendsto_L1
      (μ := μ) f g hf_bdd hg_bdd hf_meas hg_meas h_conv)

/-- Multi-cell empirical row-frequency products converge in lintegral L¹ form. -/
theorem rowSuccessorEmpiricalFreqProduct_tendsto_lintegral_nnnorm_directingRowKernelCellRealProduct_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k) :
    Tendsto
      (fun n =>
        ∫⁻ ω,
          ‖rowSuccessorEmpiricalFreqProduct (k := k) m anchor value n ω -
            directingRowKernelCellRealProduct (k := k) P m anchor value ω‖₊ ∂P)
      atTop (nhds 0) := by
  simpa [rowSuccessorEmpiricalFreqProduct, directingRowKernelCellRealProduct] using
    finiteProduct_tendsto_lintegral_nnnorm_of_factor_tendsto_L1
      (μ := P)
      (f := fun n j ω =>
        rowSuccessorEmpiricalFreq (k := k) (anchor j) (value j) ω n)
      (g := fun j ω =>
        directingRowKernelCellReal (k := k) P (anchor j) (value j) ω)
      (fun n j ω => rowSuccessorEmpiricalFreq_abs_le_one (k := k) (anchor j) (value j) ω n)
      (fun j ω => directingRowKernelCellReal_abs_le_one (k := k) P (anchor j) (value j) ω)
      (fun n j =>
        aestronglyMeasurable_rowSuccessorEmpiricalFreq (k := k) P (anchor j) (value j) n)
      (fun j =>
        (measurable_directingRowKernelCellReal (k := k) P (anchor j) (value j)).aestronglyMeasurable)
      (fun j =>
        rowSuccessorEmpiricalFreq_tendsto_L1_directingRowKernelCellReal_of_successorMatrixPE
          (k := k) P hPE (anchor j) (value j))
      (fun n => by
        change Integrable
          ((fun ω : ℕ → Fin k =>
              rowSuccessorEmpiricalFreqProduct (k := k) m anchor value n ω) -
            fun ω : ℕ → Fin k =>
              directingRowKernelCellRealProduct (k := k) P m anchor value ω) P
        exact
          (integrable_rowSuccessorEmpiricalFreqProduct (k := k) P m anchor value n).sub
            (integrable_directingRowKernelCellRealProduct (k := k) P m anchor value))

/-- Multiplication by a bounded rider preserves restricted integral convergence from L¹. -/
theorem bounded_rider_tendsto_set_integral_mul_of_L1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : Set Ω}
    {fn : ℕ → Ω → ℝ} {f H : Ω → ℝ} {C : ℝ}
    (hf_int : Integrable f μ)
    (hfn_int : ∀ n, Integrable (fn n) μ)
    (hH_int : Integrable H μ)
    (hL1 :
      Tendsto (fun n => ∫⁻ ω, ‖(fn n) ω - f ω‖₊ ∂μ) atTop (nhds 0))
    (hC : 0 ≤ C)
    (hH_bdd : ∀ᵐ ω ∂μ, ‖H ω‖ ≤ C) :
    Tendsto (fun n => ∫ ω in s, (fn n) ω * H ω ∂μ) atTop
      (nhds (∫ ω in s, f ω * H ω ∂μ)) := by
  exact MeasureTheory.tendsto_set_integral_mul_of_L1
    (s := s) hf_int hfn_int hH_int hL1 hC hH_bdd

/-- Bounded riders ride for free over the successor-matrix empirical product L¹ limit. -/
theorem bounded_rider_tendsto_set_integral_empiricalProduct_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    {s : Set (ℕ → Fin k)} {H : (ℕ → Fin k) → ℝ} {C : ℝ}
    (hH_int : Integrable H P)
    (hC : 0 ≤ C)
    (hH_bdd : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C) :
    Tendsto
      (fun n =>
        ∫ ω in s, rowSuccessorEmpiricalFreqProduct (k := k) m anchor value n ω * H ω ∂P)
      atTop
      (nhds
        (∫ ω in s,
          directingRowKernelCellRealProduct (k := k) P m anchor value ω * H ω ∂P)) := by
  exact
    bounded_rider_tendsto_set_integral_mul_of_L1
      (μ := P)
      (s := s)
      (fn := fun n ω => rowSuccessorEmpiricalFreqProduct (k := k) m anchor value n ω)
      (f := fun ω => directingRowKernelCellRealProduct (k := k) P m anchor value ω)
      (H := H)
      (hf_int := integrable_directingRowKernelCellRealProduct (k := k) P m anchor value)
      (hfn_int := fun n => integrable_rowSuccessorEmpiricalFreqProduct (k := k) P m anchor value n)
      hH_int
      (rowSuccessorEmpiricalFreqProduct_tendsto_lintegral_nnnorm_directingRowKernelCellRealProduct_of_successorMatrixPE
        (k := k) P hPE m anchor value)
      hC hH_bdd

theorem bounded_rider_tendsto_set_integral_wordAllRowsEmpiricalProduct_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k))
    {s : Set (ℕ → Fin k)}
    (H : (ℕ → Fin k) → ℝ) (C : ℝ)
    (hH_int : Integrable H P) (hC : 0 ≤ C)
    (hH_bdd : ∀ᵐ ω ∂P, |H ω| ≤ C) :
    Tendsto
      (fun n =>
        ∫ ω in s,
          wordAllRowsEmpiricalProduct (k := k) a ys n ω * H ω ∂P)
      atTop
      (nhds
        (∫ ω in s,
          wordAllRowsDirectingProduct (k := k) P a ys ω * H ω ∂P)) := by
  exact
    bounded_rider_tendsto_set_integral_mul_of_L1
      (μ := P)
      (s := s)
      (fn := fun n ω => wordAllRowsEmpiricalProduct (k := k) a ys n ω)
      (f := fun ω => wordAllRowsDirectingProduct (k := k) P a ys ω)
      (H := H)
      (hf_int := integrable_wordAllRowsDirectingProduct (k := k) P a ys)
      (hfn_int := fun n => integrable_wordAllRowsEmpiricalProduct (k := k) P a ys n)
      hH_int
      (wordAllRowsEmpiricalProduct_tendsto_lintegral_nnnorm_directingProduct_of_successorMatrixPE
        (k := k) P hPE a ys)
      hC hH_bdd

theorem tendsto_setIntegral_wordAllRowsEmpiricalProduct_directingProduct_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k))
    {s : Set (ℕ → Fin k)} :
    Tendsto
      (fun n =>
        ∫ ω in s, wordAllRowsEmpiricalProduct (k := k) a ys n ω ∂P)
      atTop
      (nhds
        (∫ ω in s, wordAllRowsDirectingProduct (k := k) P a ys ω ∂P)) := by
  simpa using
    bounded_rider_tendsto_set_integral_wordAllRowsEmpiricalProduct_of_successorMatrixPE
      (k := k) P hPE a ys
      (s := s)
      (H := fun _ω : ℕ → Fin k => (1 : ℝ))
      (C := 1)
      (integrable_const (1 : ℝ))
      zero_le_one
      (Filter.Eventually.of_forall (fun _ω => by simp))

theorem tendsto_setIntegral_wordAllRowsEmpiricalProduct_sourceEvent_toReal_of_restricted_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    {s : Set (ℕ → Fin k)} (hs : MeasurableSet s)
    (hPEs : SuccessorMatrixPartialExchangeable (k := k) (P.restrict s))
    (a : Fin k) (ys : List (Fin k)) :
    Tendsto
      (fun n =>
        ∫ ω in s, wordAllRowsEmpiricalProduct (k := k) a ys n ω ∂P)
      atTop
      (nhds ((P (s ∩ wordAllRowsSourceEvent (k := k) a ys)).toReal)) := by
  classical
  let allTerm : ℕ → (ℕ → Fin k) → ℝ :=
    fun n ω => wordAllRowsAllTupleAverage (k := k) a ys n ω
  let injTerm : ℕ → (ℕ → Fin k) → ℝ :=
    fun n ω => wordAllRowsEmpiricalInjectiveTupleAverage (k := k) a ys n ω
  let normTerm : ℕ → (ℕ → Fin k) → ℝ :=
    fun n ω => wordAllRowsNormalizedInjectiveTupleAverage (k := k) a ys n ω
  let target : ℝ :=
    (P (s ∩ wordAllRowsSourceEvent (k := k) a ys)).toReal
  have hall_int : ∀ n, Integrable (allTerm n) (P.restrict s) := by
    intro n
    simpa [allTerm] using
      integrable_wordAllRowsAllTupleAverage_of_finite
        (k := k) (P := P.restrict s) a ys n
  have hinj_int : ∀ n, Integrable (injTerm n) (P.restrict s) := by
    intro n
    simpa [injTerm] using
      integrable_wordAllRowsEmpiricalInjectiveTupleAverage_of_finite
        (k := k) (P := P.restrict s) a ys n
  have hnorm_int : ∀ n, Integrable (normTerm n) (P.restrict s) := by
    intro n
    simpa [normTerm] using
      integrable_wordAllRowsNormalizedInjectiveTupleAverage_of_finite
        (k := k) (P := P.restrict s) a ys n
  have hEmp_eq_all :
      (fun n =>
          ∫ ω in s, wordAllRowsEmpiricalProduct (k := k) a ys n ω ∂P)
        =ᶠ[atTop]
      (fun n => ∫ ω in s, allTerm n ω ∂P) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hnne : n ≠ 0 := by omega
    apply integral_congr_ae
    filter_upwards with ω
    simpa [allTerm, wordAllRowsAllTupleAverage] using
      wordAllRowsEmpiricalProduct_eq_allRowsTuple_average
        (k := k) a ys n ω hnne
  have hAllMinusInjAbs :
      Tendsto
        (fun n : ℕ =>
          |∫ ω in s, allTerm n ω - injTerm n ω ∂P|)
        atTop (nhds 0) := by
    simpa [allTerm, injTerm] using
      setIntegral_wordAllRowsAllTupleAverage_sub_empiricalInjectiveAverage_tendsto_zero
        (k := k) (P := P) (s := s) a ys
  have hAllMinusInjIntegral :
      Tendsto
        (fun n : ℕ => ∫ ω in s, allTerm n ω - injTerm n ω ∂P)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp_def] using hAllMinusInjAbs
  have hAllSubInj :
      Tendsto
        (fun n : ℕ => (∫ ω in s, allTerm n ω ∂P) - ∫ ω in s, injTerm n ω ∂P)
        atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hAllMinusInjIntegral
    exact Filter.Eventually.of_forall fun n => by
      exact MeasureTheory.integral_sub (μ := P.restrict s)
        (hall_int n) (hinj_int n)
  have hNormMinusInjAbs :
      Tendsto
        (fun n : ℕ =>
          |∫ ω in s, normTerm n ω - injTerm n ω ∂P|)
        atTop (nhds 0) := by
    simpa [normTerm, injTerm] using
      setIntegral_wordAllRowsNormalizedInjectiveAverage_sub_empiricalInjectiveAverage_tendsto_zero
        (k := k) (P := P) (s := s) a ys
  have hNormMinusInjIntegral :
      Tendsto
        (fun n : ℕ => ∫ ω in s, normTerm n ω - injTerm n ω ∂P)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp_def] using hNormMinusInjAbs
  have hNormSubInj :
      Tendsto
        (fun n : ℕ => (∫ ω in s, normTerm n ω ∂P) - ∫ ω in s, injTerm n ω ∂P)
        atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hNormMinusInjIntegral
    exact Filter.Eventually.of_forall fun n => by
      exact MeasureTheory.integral_sub (μ := P.restrict s)
        (hnorm_int n) (hinj_int n)
  have hNorm_eq_target :
      (fun n : ℕ => ∫ ω in s, normTerm n ω ∂P)
        =ᶠ[atTop] fun _n : ℕ => target := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨ys.length, ?_⟩
    intro n hn
    have hlen :
        ∀ i : Fin k, (wordAnchorFiberList (k := k) a ys i).length ≤ n := by
      intro i
      exact wordAnchorFiberList_length_le_of_ys_length_le (k := k) a ys hn i
    simpa [normTerm, target] using
      successorMatrixPE_setIntegral_wordAllRowsNormalizedInjectiveTupleAverage_eq_sourceEvent_toReal
        (k := k) P hs hPEs a ys hlen
  have hNorm :
      Tendsto (fun n : ℕ => ∫ ω in s, normTerm n ω ∂P) atTop (nhds target) := by
    exact Filter.Tendsto.congr' hNorm_eq_target.symm tendsto_const_nhds
  have hInjSubNorm :
      Tendsto
        (fun n : ℕ => (∫ ω in s, injTerm n ω ∂P) - ∫ ω in s, normTerm n ω ∂P)
        atTop (nhds 0) := by
    have hneg := hNormSubInj.neg
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  have hInj :
      Tendsto (fun n : ℕ => ∫ ω in s, injTerm n ω ∂P) atTop (nhds target) := by
    have hsum := hInjSubNorm.add hNorm
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  have hAll :
      Tendsto (fun n : ℕ => ∫ ω in s, allTerm n ω ∂P) atTop (nhds target) := by
    have hsum := hAllSubInj.add hInj
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  simpa [target] using Filter.Tendsto.congr' hEmp_eq_all.symm hAll

theorem setIntegral_wordAllRowsDirectingProduct_eq_sourceEvent_toReal_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    {s : Set (ℕ → Fin k)} (hs : MeasurableSet s)
    (hPEs : SuccessorMatrixPartialExchangeable (k := k) (P.restrict s))
    (a : Fin k) (ys : List (Fin k)) :
    ∫ ω in s, wordAllRowsDirectingProduct (k := k) P a ys ω ∂P =
      (P (s ∩ wordAllRowsSourceEvent (k := k) a ys)).toReal := by
  have hDirecting :=
    tendsto_setIntegral_wordAllRowsEmpiricalProduct_directingProduct_of_successorMatrixPE
      (k := k) P hPE a ys (s := s)
  have hSource :=
    tendsto_setIntegral_wordAllRowsEmpiricalProduct_sourceEvent_toReal_of_restricted_successorMatrixPE
      (k := k) P hs hPEs a ys
  exact tendsto_nhds_unique hDirecting hSource

/-- The edge-count product associated with a word is the product over the
successor list attached to each source row. -/
theorem prefixThetaPowerProduct_eq_rowSuccessorsProduct
    (a : Fin k) (ys : List (Fin k)) (Θ : Fin k → Fin k → ℝ) :
    prefixThetaPowerProduct (k := k) a ys Θ =
      ∏ i : Fin k, ((rowSuccessors i (a :: ys)).map (fun j => Θ i j)).prod := by
  induction ys generalizing a with
  | nil =>
      simp [prefixThetaPowerProduct, prefixWordState, countsOfFn,
        stateOfTraj, transCount, PerRowJointPE.wordTraj,
        rowSuccessors]
  | cons b rest ih =>
      rw [prefixThetaPowerProduct_cons]
      rw [ih b]
      have hrow : ∀ i : Fin k,
          ((rowSuccessors i (a :: b :: rest)).map (fun j => Θ i j)).prod =
            (if i = a then Θ a b else 1) *
              ((rowSuccessors i (b :: rest)).map (fun j => Θ i j)).prod := by
        intro i
        rw [rowSuccessors_cons_cons]
        by_cases hia : i = a
        · subst hia
          simp
        · have hai : ¬ a = i := by exact fun h => hia h.symm
          simp [hai, hia]
      simp_rw [hrow]
      rw [Finset.prod_mul_distrib]
      have hsingle : (∏ i : Fin k, (if i = a then Θ a b else 1)) = Θ a b := by
        simp
      rw [hsingle]

lemma wordAnchorFiberValue_ofFn_eq_map
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    List.ofFn (wordAnchorFiberValue (k := k) a ys i) =
      (wordAnchorFiberList (k := k) a ys i).map
        (fun j => wordSuccessorTuple (k := k) a ys j) := by
  exact (List.ofFn_getElem_eq_map
    (l := wordAnchorFiberList (k := k) a ys i)
    (f := fun j : Fin ys.length => wordSuccessorTuple (k := k) a ys j))

lemma wordAnchorFiberValues_map_eq_rowSuccessors
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    (wordAnchorFiberList (k := k) a ys i).map
        (fun j => wordSuccessorTuple (k := k) a ys j) =
      rowSuccessors i (a :: ys) := by
  induction ys generalizing a with
  | nil =>
      simp [wordAnchorFiberList]
  | cons b rest ih =>
      simp only [wordAnchorFiberList, List.length_cons]
      rw [List.finRange_succ]
      simp only [List.filter_cons]
      have htail :
          List.map (fun j : Fin (rest.length + 1) =>
              wordSuccessorTuple (k := k) a (b :: rest) j)
            (List.filter
              (fun j : Fin (rest.length + 1) =>
                decide ((a :: b :: rest).getD j.1 a = i))
              (List.map Fin.succ (List.finRange rest.length))) =
          rowSuccessors i (b :: rest) := by
        rw [List.filter_map]
        rw [List.map_map]
        have hpred :
            ((fun j : Fin (rest.length + 1) =>
                decide ((a :: b :: rest).getD j.1 a = i)) ∘ Fin.succ) =
              (fun x : Fin rest.length => decide ((b :: rest).getD x.1 b = i)) := by
          funext x
          dsimp [Function.comp]
          simp
        have hmap :
            ((fun j : Fin (rest.length + 1) =>
                wordSuccessorTuple (k := k) a (b :: rest) j) ∘ Fin.succ) =
              (fun x : Fin rest.length => wordSuccessorTuple (k := k) b rest x) := by
          funext x
          dsimp [Function.comp]
          change (b :: rest).getD (x.1 + 1) a = rest.getD x.1 b
          rw [List.getD_cons_succ]
          rw [List.getD_eq_getElem (l := rest) (d := a) x.2]
          rw [List.getD_eq_getElem (l := rest) (d := b) x.2]
        rw [hpred, hmap]
        simpa [wordAnchorFiberList] using ih b
      by_cases hai : a = i
      · subst hai
        simp [rowSuccessors_cons_cons]
        constructor
        · simp [wordSuccessorTuple]
        · simpa using htail
      · simpa [rowSuccessors_cons_cons, hai] using htail

lemma wordAnchorFiberProduct_eq_rowSuccessorsProduct
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) (Θ : Fin k → Fin k → ℝ) :
    (∏ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
        Θ i (wordAnchorFiberValue (k := k) a ys i t)) =
      ((rowSuccessors i (a :: ys)).map (fun j => Θ i j)).prod := by
  rw [← List.prod_ofFn]
  change (List.ofFn
      ((fun j : Fin k => Θ i j) ∘ wordAnchorFiberValue (k := k) a ys i)).prod =
    ((rowSuccessors i (a :: ys)).map (fun j => Θ i j)).prod
  rw [← List.map_ofFn]
  rw [wordAnchorFiberValue_ofFn_eq_map]
  rw [wordAnchorFiberValues_map_eq_rowSuccessors]

/-- The all-row canonical directing product is the row-kernel step product
for the same finite word, read back as a real number. -/
theorem wordAllRowsDirectingProduct_eq_rowKernelStepProd_toReal
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (a : Fin k) (ys : List (Fin k)) (ω : ℕ → Fin k) :
    wordAllRowsDirectingProduct (k := k) P a ys ω =
      (rowKernelStepProd (k := k) (directingRowKernel (k := k) P) ω (a :: ys)).toReal := by
  let Θ : Fin k → Fin k → ℝ := fun i j => directingRowKernelCellReal (k := k) P i j ω
  have hprefix :
      prefixThetaPowerProduct (k := k) a ys Θ =
        (rowKernelStepProd (k := k) (directingRowKernel (k := k) P) ω (a :: ys)).toReal := by
    refine prefixThetaPowerProduct_eq_rowKernelStepProd_toReal
      (k := k) a ys (directingRowKernel (k := k) P) ω Θ ?_
    intro i j
    rfl
  have hprefixRows :
      prefixThetaPowerProduct (k := k) a ys Θ =
        ∏ i : Fin k, ((rowSuccessors i (a :: ys)).map (fun j => Θ i j)).prod :=
    prefixThetaPowerProduct_eq_rowSuccessorsProduct (k := k) a ys Θ
  have hwordRows :
      wordAllRowsDirectingProduct (k := k) P a ys ω =
        ∏ i : Fin k, ((rowSuccessors i (a :: ys)).map (fun j => Θ i j)).prod := by
    dsimp [wordAllRowsDirectingProduct, directingRowKernelCellRealProduct, Θ]
    refine Finset.prod_congr rfl ?_
    intro i _hi
    exact wordAnchorFiberProduct_eq_rowSuccessorsProduct (k := k) a ys i Θ
  calc
    wordAllRowsDirectingProduct (k := k) P a ys ω =
        ∏ i : Fin k, ((rowSuccessors i (a :: ys)).map (fun j => Θ i j)).prod := hwordRows
    _ = prefixThetaPowerProduct (k := k) a ys Θ := hprefixRows.symm
    _ = (rowKernelStepProd (k := k) (directingRowKernel (k := k) P) ω (a :: ys)).toReal := hprefix

/-- Bare successor-matrix PE already gives the row-kernel product identity for
the successor-array event associated with a word. The missing public-G2 bridge is
only the extra coupling with the initial state that turns this event into the
ordinary cylinder. -/
lemma integral_rowKernelStepProd_toReal_eq_wordAllRowsSourceEvent_toReal_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k)) :
    ∫ ω,
        (rowKernelStepProd (k := k) (directingRowKernel (k := k) P)
          ω (a :: ys)).toReal ∂P =
      (P (wordAllRowsSourceEvent (k := k) a ys)).toReal := by
  have hPE_univ :
      SuccessorMatrixPartialExchangeable (k := k) (P.restrict Set.univ) := by
    simpa using hPE
  have hset :=
    setIntegral_wordAllRowsDirectingProduct_eq_sourceEvent_toReal_of_successorMatrixPE
      (k := k) P hPE
      (s := Set.univ) MeasurableSet.univ hPE_univ a ys
  have hprod :
      (fun ω : ℕ → Fin k => wordAllRowsDirectingProduct (k := k) P a ys ω) =
        (fun ω : ℕ → Fin k =>
          (rowKernelStepProd (k := k) (directingRowKernel (k := k) P) ω (a :: ys)).toReal) := by
    funext ω
    exact wordAllRowsDirectingProduct_eq_rowKernelStepProd_toReal (k := k) P a ys ω
  rw [hprod] at hset
  simpa [Set.univ_inter] using hset

/-- Successor-event form of the bare successor-matrix PE product identity. This
is the cylinder identity with the start coordinate deliberately absent. -/
lemma integral_rowKernelStepProd_toReal_eq_wordSuccessorReadEvent_toReal_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k)) :
    ∫ ω,
        (rowKernelStepProd (k := k) (directingRowKernel (k := k) P)
          ω (a :: ys)).toReal ∂P =
      (P (successorReadEvent (k := k) ys.length
        (fun j : Fin ys.length => (a :: ys).getD j.1 a)
        (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
        (wordSuccessorTuple (k := k) a ys))).toReal := by
  rw [integral_rowKernelStepProd_toReal_eq_wordAllRowsSourceEvent_toReal_of_successorMatrixPE
    (k := k) P hPE a ys]
  rw [wordAllRowsSourceEvent_eq_wordSuccessorReadEvent (k := k) a ys]

/-- ENNReal form of the bare successor-matrix PE product identity for the
successor-array event. This is the exact all-row product calculation without the
initial-state rider. -/
lemma lintegral_rowKernelStepProd_eq_wordAllRowsSourceEvent_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k)) :
    ∫⁻ ω,
        rowKernelStepProd (k := k) (directingRowKernel (k := k) P)
          ω (a :: ys) ∂P =
      P (wordAllRowsSourceEvent (k := k) a ys) := by
  let rowKernel := directingRowKernel (k := k) P
  have hReal :=
    integral_rowKernelStepProd_toReal_eq_wordAllRowsSourceEvent_toReal_of_successorMatrixPE
      (k := k) P hPE a ys
  have hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i) := by
    intro i b
    simpa [rowKernel] using
      (measurable_directingRowKernel_eval (k := k) P i b).aemeasurable
  have hint :
      Integrable
        (fun ω : ℕ → Fin k =>
          (rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal) P := by
    exact integrable_rowKernelStepProd_toReal (k := k) P rowKernel hEval (a :: ys)
  have hnonneg : 0 ≤ᵐ[P]
      (fun ω : ℕ → Fin k => (rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal) := by
    exact ae_of_all _ (fun _ω => ENNReal.toReal_nonneg)
  have hofReal :
      ENNReal.ofReal
          (∫ ω, (rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal ∂P) =
        ∫⁻ ω,
          ENNReal.ofReal
            ((rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal) ∂P := by
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg
  have hpoint :
      (fun ω : ℕ → Fin k =>
          ENNReal.ofReal ((rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal)) =
        (fun ω : ℕ → Fin k => rowKernelStepProd (k := k) rowKernel ω (a :: ys)) := by
    funext ω
    exact ENNReal.ofReal_toReal (ne_of_lt <| lt_of_le_of_lt
      (rowKernelStepProd_le_one (k := k) rowKernel ω (a :: ys)) (by simp))
  have hleft_ofReal :
      ENNReal.ofReal
          (∫ ω, (rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal ∂P) =
        ∫⁻ ω, rowKernelStepProd (k := k) rowKernel ω (a :: ys) ∂P := by
    simpa [rowKernel, hpoint] using hofReal
  rw [← hleft_ofReal]
  rw [hReal]
  exact ENNReal.ofReal_toReal
    (measure_ne_top P (wordAllRowsSourceEvent (k := k) a ys))

/-- Successor-event ENNReal form of the bare successor-matrix PE product
identity. The ordinary cylinder version additionally needs start coupling. -/
lemma lintegral_rowKernelStepProd_eq_wordSuccessorReadEvent_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) (ys : List (Fin k)) :
    ∫⁻ ω,
        rowKernelStepProd (k := k) (directingRowKernel (k := k) P)
          ω (a :: ys) ∂P =
      P (successorReadEvent (k := k) ys.length
        (fun j : Fin ys.length => (a :: ys).getD j.1 a)
        (fun j : Fin ys.length => wordVisitIndex (k := k) (a :: ys) a j.1)
        (wordSuccessorTuple (k := k) a ys)) := by
  rw [lintegral_rowKernelStepProd_eq_wordAllRowsSourceEvent_of_successorMatrixPE
    (k := k) P hPE a ys]
  rw [wordAllRowsSourceEvent_eq_wordSuccessorReadEvent (k := k) a ys]

lemma start_inter_wordAllRowsSourceEvent_eq_cylinder
    (a : Fin k) (ys : List (Fin k)) :
    {ω : ℕ → Fin k | ω 0 = a} ∩ wordAllRowsSourceEvent (k := k) a ys =
      MarkovDeFinettiRecurrence.cylinder (k := k) (a :: ys) := by
  rw [wordAllRowsSourceEvent_eq_wordSuccessorReadEvent (k := k) a ys]
  rw [successorReadEvent_word_eq_preimage_wordSuccessorTuple (k := k) a ys]
  rw [cylinder_cons_eq_start_inter_preimage_wordSuccessorTuple (k := k) a ys]

lemma setIntegral_rowKernelStepProd_toReal_eq_cylinder_toReal_of_successorMatrixPE_start
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (hPE_start :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a}))
    (a : Fin k) (ys : List (Fin k)) :
    ∫ ω in {ω : ℕ → Fin k | ω 0 = a},
        (rowKernelStepProd (k := k) (directingRowKernel (k := k) P) ω (a :: ys)).toReal ∂P =
      (P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: ys))).toReal := by
  have hset :=
    setIntegral_wordAllRowsDirectingProduct_eq_sourceEvent_toReal_of_successorMatrixPE
      (k := k) P hPE
      (s := {ω : ℕ → Fin k | ω 0 = a})
      (by
        change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' ({a} : Set (Fin k)))
        exact (measurable_pi_apply 0) (MeasurableSet.singleton a))
      (hPE_start a) a ys
  have hprod :
      (fun ω : ℕ → Fin k => wordAllRowsDirectingProduct (k := k) P a ys ω) =
        (fun ω : ℕ → Fin k =>
          (rowKernelStepProd (k := k) (directingRowKernel (k := k) P) ω (a :: ys)).toReal) := by
    funext ω
    exact wordAllRowsDirectingProduct_eq_rowKernelStepProd_toReal (k := k) P a ys ω
  rw [hprod] at hset
  rw [start_inter_wordAllRowsSourceEvent_eq_cylinder (k := k) a ys] at hset
  exact hset

lemma lintegral_rowKernelStepProd_eq_cylinder_of_successorMatrixPE_start
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (hPE_start :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a}))
    (a : Fin k) (ys : List (Fin k)) :
    ∫⁻ ω in {ω : ℕ → Fin k | ω 0 = a},
        rowKernelStepProd (k := k) (directingRowKernel (k := k) P) ω (a :: ys) ∂P =
      P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: ys)) := by
  let rowKernel := directingRowKernel (k := k) P
  let s : Set (ℕ → Fin k) := {ω | ω 0 = a}
  have hReal :=
    setIntegral_rowKernelStepProd_toReal_eq_cylinder_toReal_of_successorMatrixPE_start
      (k := k) P hPE hPE_start a ys
  have hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i) := by
    intro i b
    simpa [rowKernel] using
      (measurable_directingRowKernel_eval (k := k) P i b).aemeasurable
  have hintP :
      Integrable
        (fun ω : ℕ → Fin k =>
          (rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal) P := by
    exact integrable_rowKernelStepProd_toReal (k := k) P rowKernel hEval (a :: ys)
  have hint :
      Integrable
        (fun ω : ℕ → Fin k =>
          (rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal)
        (P.restrict s) := by
    exact hintP.restrict
  have hnonneg : 0 ≤ᵐ[P.restrict s]
      (fun ω : ℕ → Fin k => (rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal) := by
    exact ae_of_all _ (fun _ω => ENNReal.toReal_nonneg)
  have hofReal :
      ENNReal.ofReal
          (∫ ω,
            (rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal ∂(P.restrict s)) =
        ∫⁻ ω,
          ENNReal.ofReal
            ((rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal) ∂(P.restrict s) := by
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg
  have hpoint :
      (fun ω : ℕ → Fin k =>
          ENNReal.ofReal ((rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal)) =
        (fun ω : ℕ → Fin k => rowKernelStepProd (k := k) rowKernel ω (a :: ys)) := by
    funext ω
    exact ENNReal.ofReal_toReal (ne_of_lt <| lt_of_le_of_lt
      (rowKernelStepProd_le_one (k := k) rowKernel ω (a :: ys)) (by simp))
  have hleft_ofReal :
      ENNReal.ofReal
          (∫ ω in s, (rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal ∂P) =
        ∫⁻ ω in s, rowKernelStepProd (k := k) rowKernel ω (a :: ys) ∂P := by
    simpa [s, hpoint] using hofReal
  rw [← hleft_ofReal]
  rw [hReal]
  exact ENNReal.ofReal_toReal
    (measure_ne_top P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: ys)))

/-- For the canonical directing row kernel, public row-successor-matrix
invariance is exactly the start-coupled row-kernel product identity on all
nontrivial cylinders. This isolates the true remaining rider bridge for the
bare successor-matrix PE route. -/
theorem rowSuccessorMatrixInvariance_directingRowKernel_iff_startCoupledProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P] :
    RowSuccessorMatrixInvariance (k := k) P (directingRowKernel (k := k) P) ↔
      ∀ (a b : Fin k) (xs : List (Fin k)),
        P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: xs)) =
          ∫⁻ ω in {ω : ℕ → Fin k | ω 0 = a},
            rowKernelStepProd (k := k) (directingRowKernel (k := k) P)
              ω (a :: b :: xs) ∂P := by
  constructor
  · intro hInv a b xs
    calc
      P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: xs)) =
          ∫⁻ ω, wordProb (k := k)
            (rowKernelToMarkovParam (k := k)
              (initKernel := fun ω =>
                ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
              (liftedRowKernelFromRowProcess
                (k := k) (directingRowKernel (k := k) P)) ω)
            (a :: b :: xs) ∂P := by
            exact hInv (a :: b :: xs) (by simp)
      _ = ∫⁻ ω,
          (if ω 0 = a then
            rowKernelStepProd (k := k) (directingRowKernel (k := k) P)
              ω (a :: b :: xs)
          else 0) ∂P := by
            refine lintegral_congr_ae ?_
            filter_upwards with ω
            exact wordProb_rowKernelToMarkovParam_eq_indicator_stepProd
              (k := k) (directingRowKernel (k := k) P) ω a b xs
      _ = ∫⁻ ω in {ω : ℕ → Fin k | ω 0 = a},
          rowKernelStepProd (k := k) (directingRowKernel (k := k) P)
            ω (a :: b :: xs) ∂P := by
            exact lintegral_startIndicator_rowKernelStepProd_eq_restrict
              (k := k) P (directingRowKernel (k := k) P) a b xs
  · intro hStart xs hlen
    cases xs with
    | nil =>
        simp at hlen
    | cons a rest =>
        cases rest with
        | nil =>
            simp at hlen
        | cons b tail =>
            calc
              P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: tail)) =
                  ∫⁻ ω in {ω : ℕ → Fin k | ω 0 = a},
                    rowKernelStepProd (k := k) (directingRowKernel (k := k) P)
                      ω (a :: b :: tail) ∂P := hStart a b tail
              _ = ∫⁻ ω,
                  (if ω 0 = a then
                    rowKernelStepProd (k := k) (directingRowKernel (k := k) P)
                      ω (a :: b :: tail)
                  else 0) ∂P := by
                    rw [lintegral_startIndicator_rowKernelStepProd_eq_restrict
                      (k := k) P (directingRowKernel (k := k) P) a b tail]
              _ = ∫⁻ ω, wordProb (k := k)
                    (rowKernelToMarkovParam (k := k)
                      (initKernel := fun ω =>
                        ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
                      (liftedRowKernelFromRowProcess
                        (k := k) (directingRowKernel (k := k) P)) ω)
                    (a :: b :: tail) ∂P := by
                    refine lintegral_congr_ae ?_
                    filter_upwards with ω
                    symm
                    exact wordProb_rowKernelToMarkovParam_eq_indicator_stepProd
                      (k := k) (directingRowKernel (k := k) P) ω a b tail

/-- Same-surface constructor for exact public G2 from the corrected rider
target: once bare successor-matrix PE gives the start-coupled product identity,
the canonical directing row kernel supplies the public minimal payload. -/
theorem existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE_of_startCoupledProduct
    (hStartCoupled :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P),
        SuccessorMatrixPartialExchangeable (k := k) P →
        ∀ (a b : Fin k) (xs : List (Fin k)),
          P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: xs)) =
            ∫⁻ ω in {ω : ℕ → Fin k | ω 0 = a},
              rowKernelStepProd (k := k) (directingRowKernel (k := k) P)
                ω (a :: b :: xs) ∂P) :
    ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k := by
  intro P hP hPE
  letI : IsProbabilityMeasure P := hP
  refine ⟨directingRowKernel (k := k) P, ?_, ?_⟩
  · intro i b
    exact (measurable_directingRowKernel_eval (k := k) P i b).aemeasurable
  · exact
      (rowSuccessorMatrixInvariance_directingRowKernel_iff_startCoupledProduct
        (k := k) P).2 (hStartCoupled P hP hPE)

/-- Start-restricted successor-matrix PE proves the corrected start-coupled
product target. This records the old stronger route as one supplier of the
new exact rider bridge. -/
theorem startCoupledProduct_of_successorMatrixPE_start
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (hPE_start :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a})) :
    ∀ (a b : Fin k) (xs : List (Fin k)),
      P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: xs)) =
        ∫⁻ ω in {ω : ℕ → Fin k | ω 0 = a},
          rowKernelStepProd (k := k) (directingRowKernel (k := k) P)
            ω (a :: b :: xs) ∂P := by
  intro a b xs
  exact
    (lintegral_rowKernelStepProd_eq_cylinder_of_successorMatrixPE_start
      (k := k) P hPE hPE_start a (b :: xs)).symm

theorem rowSuccessorMatrixInvariance_directingRowKernel_of_successorMatrixPE_start
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (hPE_start :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a})) :
    RowSuccessorMatrixInvariance (k := k) P (directingRowKernel (k := k) P) := by
  exact
    (rowSuccessorMatrixInvariance_directingRowKernel_iff_startCoupledProduct
      (k := k) P).2
      (startCoupledProduct_of_successorMatrixPE_start
        (k := k) P hPE hPE_start)

theorem directingRowKernel_payload_of_successorMatrixPE_start
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (hPE_start :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a})) :
    ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
      (∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i)) ∧
      RowSuccessorMatrixInvariance (k := k) P rowKernel := by
  refine ⟨directingRowKernel (k := k) P, ?_, ?_⟩
  · intro i b
    exact (measurable_directingRowKernel_eval (k := k) P i b).aemeasurable
  · exact rowSuccessorMatrixInvariance_directingRowKernel_of_successorMatrixPE_start
      (k := k) P hPE hPE_start

/-- Start-restricted successor-matrix PE gives the minimal row-kernel payload
used by the public Crux interface, with the canonical directing row kernel as
witness. -/
theorem existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE_start
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (hPE_start :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a})) :
    ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
      (∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i)) ∧
      RowSuccessorMatrixInvariance (k := k) P rowKernel :=
  directingRowKernel_payload_of_successorMatrixPE_start (k := k) P hPE hPE_start

/-- The exact missing bridge for the bare successor-matrix PE route:
successor-matrix PE remains true after conditioning on any initial state. -/
def SuccessorMatrixPEStableUnderStartRestriction (k : ℕ) : Prop :=
  ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P),
    SuccessorMatrixPartialExchangeable (k := k) P →
    ∀ a : Fin k,
      SuccessorMatrixPartialExchangeable (k := k)
        (P.restrict {ω : ℕ → Fin k | ω 0 = a})

/-- Start-riding successor-matrix invariance: the same row-successor finite
permutation law remains true when the initial-state event is carried as a
bounded rider. This is the invariant needed by the corrected spreading plus
block-average peel. -/
def SuccessorMatrixStartRidingInvariant (k : ℕ) : Prop :=
  ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P),
    SuccessorMatrixPartialExchangeable (k := k) P →
    ∀ a : Fin k,
      SuccessorMatrixPartialExchangeable (k := k)
        (P.restrict {ω : ℕ → Fin k | ω 0 = a})

/-- The start-riding invariant is exactly the start-restriction stability
bridge needed by the bare successor-matrix PE payload route. -/
theorem successorMatrixPEStableUnderStartRestriction_of_startRidingInvariant
    (hRide : SuccessorMatrixStartRidingInvariant k) :
    SuccessorMatrixPEStableUnderStartRestriction k := by
  intro P hP hPE a
  exact hRide P hP hPE a

/-- Conversely, start-restriction stability supplies the start-riding invariant
used by the spreading/block-average proof skeleton. -/
theorem startRidingInvariant_of_successorMatrixPEStableUnderStartRestriction
    (hStart : SuccessorMatrixPEStableUnderStartRestriction k) :
    SuccessorMatrixStartRidingInvariant k := by
  intro P hP hPE a
  exact hStart P hP hPE a

/-- The start-riding and start-restriction stability formulations are the same
bridge, with two names for the two proof viewpoints. -/
theorem successorMatrixStartRidingInvariant_iff_stableUnderStartRestriction :
    SuccessorMatrixStartRidingInvariant k ↔
      SuccessorMatrixPEStableUnderStartRestriction k := by
  constructor
  · exact successorMatrixPEStableUnderStartRestriction_of_startRidingInvariant (k := k)
  · exact startRidingInvariant_of_successorMatrixPEStableUnderStartRestriction (k := k)

/-- If successor-matrix PE is stable under conditioning on the initial state,
then the original bare-PE Crux payload follows. This isolates the exact missing
bridge needed to discharge the public `ExistsRowKernel...of_successorMatrixPE`
surface without changing its statement. -/
theorem existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE_of_start_restrict
    (hStart : SuccessorMatrixPEStableUnderStartRestriction k) :
    ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k := by
  intro P hP hPE
  letI : IsProbabilityMeasure P := hP
  exact
    existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE_start
      (k := k) P hPE (hStart P hP hPE)

/-- A start-riding invariant is enough to discharge the public bare-PE payload
surface. This theorem deliberately exposes the extra bridge rather than hiding
it in the row-kernel construction. -/
theorem existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE_of_startRiding
    (hRide : SuccessorMatrixStartRidingInvariant k) :
    ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k :=
  existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE_of_start_restrict
    (k := k)
    (successorMatrixPEStableUnderStartRestriction_of_startRidingInvariant
      (k := k) hRide)

/-- Once the start-riding bridge is available, the public minimal Route-A
constructor closes exactly as intended: minted strong-recurrence
successor-matrix PE plus the canonical row-kernel payload gives Fortini's
strong-recurrence Markov de Finetti theorem. -/
theorem fortiniStrongRecurrence_of_successorMatrixPE_startRiding
    (hPEStrong : SuccessorMatrixPE_of_markovExchangeable_strongRecurrence k)
    (hRide : SuccessorMatrixStartRidingInvariant k) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k :=
  fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_successorMatrixPE_minimal
    (k := k) hPEStrong
    (existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE_of_startRiding
      (k := k) hRide)

/-- A concrete law whose successor-matrix PE is not stable under start
restriction would refute the missing bridge. -/
theorem not_successorMatrixPEStableUnderStartRestriction_of_witness
    (hWitness :
      ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
        SuccessorMatrixPartialExchangeable (k := k) P ∧
        ∃ a : Fin k,
          ¬ SuccessorMatrixPartialExchangeable (k := k)
            (P.restrict {ω : ℕ → Fin k | ω 0 = a})) :
    ¬ SuccessorMatrixPEStableUnderStartRestriction k := by
  intro hStable
  rcases hWitness with ⟨P, hP, hPE, a, hNot⟩
  exact hNot (hStable P hP hPE a)

/-- Counterexample hook for the bare bridge: it is enough to build a law whose
finite successor-selection marginals match some successor-matrix PE law, while
one start slice fails successor-matrix PE. The transfer lemma supplies bare PE
for the full law, and the bad slice refutes start stability. -/
theorem not_successorMatrixPEStableUnderStartRestriction_of_selectionMap_eq_bad_start
    (P Q : Measure (ℕ → Fin k))
    (hP : IsProbabilityMeasure P)
    (hQPE : SuccessorMatrixPartialExchangeable (k := k) Q)
    (hsel :
      ∀ (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ),
        Measure.map (successorMatrixSelectionMap (k := k) m anchor idx) P =
          Measure.map (successorMatrixSelectionMap (k := k) m anchor idx) Q)
    (hbad :
      ∃ a : Fin k,
        ¬ SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a})) :
    ¬ SuccessorMatrixPEStableUnderStartRestriction k := by
  exact
    not_successorMatrixPEStableUnderStartRestriction_of_witness
      (k := k)
      ⟨P, hP,
        successorMatrixPartialExchangeable_of_forall_selectionMap_eq
          (k := k) Q P hsel hQPE,
        hbad⟩

/-- The same witness also refutes the start-riding formulation, since it is
equivalent to start-restriction stability. -/
theorem not_successorMatrixStartRidingInvariant_of_witness
    (hWitness :
      ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
        SuccessorMatrixPartialExchangeable (k := k) P ∧
        ∃ a : Fin k,
          ¬ SuccessorMatrixPartialExchangeable (k := k)
            (P.restrict {ω : ℕ → Fin k | ω 0 = a})) :
    ¬ SuccessorMatrixStartRidingInvariant k := by
  intro hRide
  exact
    not_successorMatrixPEStableUnderStartRestriction_of_witness
      (k := k) hWitness
      ((successorMatrixStartRidingInvariant_iff_stableUnderStartRestriction
        (k := k)).1 hRide)

/-! ## Binary start-coupling obstruction scaffold

The suspected obstruction to bare successor-matrix PE implying start-coupled
cylinder factorization is a binary path decoder: an external stream `x` is read
as the row-0 successor process, while the initial state is coupled to `x 0`.
The measure-level iid construction is developed separately; the lemmas here
pin down the deterministic decoder identity it needs.
-/

/-- Decoder state for the binary start-coupling canary. The second component
counts how many row-0 successors have been consumed. -/
def binaryStartRow0State (x : ℕ → Fin 2) : ℕ → Fin 2 × ℕ
  | 0 => (x 0, 0)
  | t + 1 =>
      let st := binaryStartRow0State x t
      if st.1 = (0 : Fin 2) then (x st.2, st.2 + 1) else (0, st.2)

/-- The path decoded from an external binary stream. -/
def binaryStartRow0Path (x : ℕ → Fin 2) (t : ℕ) : Fin 2 :=
  (binaryStartRow0State x t).1

/-- Explicit time of the `n`-th row-0 visit in the binary decoder. -/
def binaryStartRow0VisitTime (x : ℕ → Fin 2) : ℕ → ℕ
  | 0 => if x 0 = (0 : Fin 2) then 0 else 1
  | n + 1 => binaryStartRow0VisitTime x n + if x n = (0 : Fin 2) then 1 else 2

@[simp] theorem binaryStartRow0State_zero (x : ℕ → Fin 2) :
    binaryStartRow0State x 0 = (x 0, 0) := rfl

@[simp] theorem binaryStartRow0Path_zero (x : ℕ → Fin 2) :
    binaryStartRow0Path x 0 = x 0 := rfl

@[simp] theorem binaryStartRow0State_succ (x : ℕ → Fin 2) (t : ℕ) :
    binaryStartRow0State x (t + 1) =
      let st := binaryStartRow0State x t
      if st.1 = (0 : Fin 2) then (x st.2, st.2 + 1) else (0, st.2) := rfl

theorem binaryStartRow0Path_succ_of_zero
    (x : ℕ → Fin 2) (t : ℕ)
    (h : binaryStartRow0Path x t = (0 : Fin 2)) :
    binaryStartRow0Path x (t + 1) = x (binaryStartRow0State x t).2 := by
  change (binaryStartRow0State x t).1 = (0 : Fin 2) at h
  simp [binaryStartRow0Path, h]

theorem binaryStartRow0Path_succ_of_nonzero
    (x : ℕ → Fin 2) (t : ℕ)
    (h : binaryStartRow0Path x t ≠ (0 : Fin 2)) :
    binaryStartRow0Path x (t + 1) = (0 : Fin 2) := by
  change (binaryStartRow0State x t).1 ≠ (0 : Fin 2) at h
  simp [binaryStartRow0Path, h]

/-- The decoder's counter is exactly the number of previous row-0 visits. -/
theorem binaryStartRow0State_counter_eq_visitCountBefore
    (x : ℕ → Fin 2) (t : ℕ) :
    (binaryStartRow0State x t).2 =
      visitCountBefore (k := 2) (binaryStartRow0Path x) (0 : Fin 2) t := by
  induction t with
  | zero =>
      simp [visitCountBefore]
  | succ t ih =>
      rw [binaryStartRow0State_succ, visitCountBefore, Finset.sum_range_succ,
        ← visitCountBefore]
      by_cases h : (binaryStartRow0State x t).1 = (0 : Fin 2)
      · simp [binaryStartRow0Path, h, ih, Nat.add_comm]
      · simp [binaryStartRow0Path, h, ih]

/-- At the explicit row-0 visit time, the decoder is at row 0 and has consumed
exactly `n` previous row-0 successors; one step later it emits `x n`. -/
theorem binaryStartRow0State_visitTime
    (x : ℕ → Fin 2) (n : ℕ) :
    binaryStartRow0State x (binaryStartRow0VisitTime x n) = ((0 : Fin 2), n) ∧
      binaryStartRow0State x (binaryStartRow0VisitTime x n + 1) = (x n, n + 1) := by
  induction n with
  | zero =>
      unfold binaryStartRow0VisitTime
      by_cases h0 : x 0 = (0 : Fin 2)
      · simp [h0]
      · simp [h0]
  | succ n ih =>
      rcases ih with ⟨hvisit, hsucc⟩
      constructor
      · unfold binaryStartRow0VisitTime
        by_cases hn : x n = (0 : Fin 2)
        · simpa [hn] using hsucc
        · have hnext :
              binaryStartRow0State x (binaryStartRow0VisitTime x n + 2) =
                ((0 : Fin 2), n + 1) := by
            rw [show binaryStartRow0VisitTime x n + 2 =
                (binaryStartRow0VisitTime x n + 1) + 1 by omega,
              binaryStartRow0State_succ, hsucc]
            simp [hn]
          simpa [hn, Nat.add_assoc] using hnext
      · unfold binaryStartRow0VisitTime
        by_cases hn : x n = (0 : Fin 2)
        · have hnext :
              binaryStartRow0State x (binaryStartRow0VisitTime x n + 2) =
                (x (n + 1), n + 2) := by
            rw [show binaryStartRow0VisitTime x n + 2 =
                (binaryStartRow0VisitTime x n + 1) + 1 by omega,
              binaryStartRow0State_succ, hsucc]
            simp [hn]
          simpa [hn, Nat.add_assoc] using hnext
        · have hzero :
              binaryStartRow0State x (binaryStartRow0VisitTime x n + 2) =
                ((0 : Fin 2), n + 1) := by
            rw [show binaryStartRow0VisitTime x n + 2 =
                (binaryStartRow0VisitTime x n + 1) + 1 by omega,
              binaryStartRow0State_succ, hsucc]
            simp [hn]
          have hnext :
              binaryStartRow0State x (binaryStartRow0VisitTime x n + 3) =
                (x (n + 1), n + 2) := by
            rw [show binaryStartRow0VisitTime x n + 3 =
                (binaryStartRow0VisitTime x n + 2) + 1 by omega,
              binaryStartRow0State_succ, hzero]
            simp
          simpa [hn, Nat.add_assoc] using hnext

theorem binaryStartRow0_nthVisitTime
    (x : ℕ → Fin 2) (n : ℕ) :
    nthVisitTime (k := 2) (binaryStartRow0Path x) (0 : Fin 2) n =
      some (binaryStartRow0VisitTime x n) := by
  have hstate := (binaryStartRow0State_visitTime x n).1
  exact
    (nthVisitTime_eq_some_iff (k := 2) (binaryStartRow0Path x)
      (0 : Fin 2) n (binaryStartRow0VisitTime x n)).2
      ⟨by exact congrArg Prod.fst hstate,
        by
          rw [← binaryStartRow0State_counter_eq_visitCountBefore x
            (binaryStartRow0VisitTime x n)]
          exact congrArg Prod.snd hstate⟩

/-- The decoder really has the external stream as its row-0 successor
process. This is the deterministic core of the binary counterexample route. -/
theorem binaryStartRow0_rowSuccessorVisitProcess_zero
    (x : ℕ → Fin 2) :
    rowSuccessorVisitProcess (k := 2) (0 : Fin 2) (binaryStartRow0Path x) = x := by
  funext n
  have hsucc := (binaryStartRow0State_visitTime x n).2
  unfold rowSuccessorVisitProcess rowSuccessorAtNthVisit
  rw [binaryStartRow0_nthVisitTime x n]
  simpa [successorAt, binaryStartRow0Path] using congrArg Prod.fst hsucc

/-- The decoder couples the path's initial state to the first row-0 successor
readout.  This is the pointwise start-rider obstruction: the start event is not
independent of the row-successor process; it is one of its coordinates. -/
theorem binaryStartRow0_start_eq_first_rowSuccessor
    (x : ℕ → Fin 2) :
    binaryStartRow0Path x 0 =
      rowSuccessorVisitProcess (k := 2) (0 : Fin 2) (binaryStartRow0Path x) 0 := by
  rw [binaryStartRow0_rowSuccessorVisitProcess_zero]
  rfl

/-- Pulling the start event back through the decoder is the same as pulling back
the first row-0 successor event. -/
theorem binaryStartRow0_start_preimage_eq_first_rowSuccessor_preimage
    (a : Fin 2) :
    {x : ℕ → Fin 2 | binaryStartRow0Path x 0 = a} =
      {x : ℕ → Fin 2 |
        rowSuccessorVisitProcess (k := 2) (0 : Fin 2) (binaryStartRow0Path x) 0 = a} := by
  ext x
  simp [binaryStartRow0_rowSuccessorVisitProcess_zero]

/-- The same start event is just the zeroth coordinate of the external stream. -/
theorem binaryStartRow0_start_preimage_eq_stream_zero_preimage
    (a : Fin 2) :
    {x : ℕ → Fin 2 | binaryStartRow0Path x 0 = a} =
      {x : ℕ → Fin 2 | x 0 = a} := by
  ext x
  rfl

/-- The first row-0 successor event of the decoded path is the zeroth external
stream coordinate. -/
theorem binaryStartRow0_first_rowSuccessor_preimage_eq_stream_zero_preimage
    (a : Fin 2) :
    {x : ℕ → Fin 2 |
        rowSuccessorVisitProcess (k := 2) (0 : Fin 2) (binaryStartRow0Path x) 0 = a} =
      {x : ℕ → Fin 2 | x 0 = a} := by
  rw [← binaryStartRow0_start_preimage_eq_first_rowSuccessor_preimage,
    binaryStartRow0_start_preimage_eq_stream_zero_preimage]

/-- Positive canary: in a subsingleton alphabet, conditioning on the initial
state is conditioning on the whole path space, so bare successor-matrix PE is
stable under start restriction. -/
theorem successorMatrixPE_start_restrict_of_successorMatrixPE_subsingleton
    [Subsingleton (Fin k)]
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (a : Fin k) :
    SuccessorMatrixPartialExchangeable (k := k)
      (P.restrict {ω : ℕ → Fin k | ω 0 = a}) := by
  have hstart : {ω : ℕ → Fin k | ω 0 = a} = Set.univ := by
    ext ω
    constructor
    · intro _
      trivial
    · intro _
      exact Subsingleton.elim (ω 0) a
  simpa [hstart] using hPE

/-- In a subsingleton alphabet, successor-matrix PE is stable under
conditioning on the initial state. -/
theorem successorMatrixPEStableUnderStartRestriction_subsingleton
    [Subsingleton (Fin k)] :
    SuccessorMatrixPEStableUnderStartRestriction k := by
  intro P hP hPE a
  letI : IsProbabilityMeasure P := hP
  exact
    successorMatrixPE_start_restrict_of_successorMatrixPE_subsingleton
      (k := k) P hPE a

/-- Subsingleton-alphabet canary for the original Crux Prop: in a degenerate
alphabet, start restriction is harmless, so the bare PE payload is available
without extra hypotheses. -/
theorem existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE_subsingleton
    [Subsingleton (Fin k)] :
    ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k := by
  apply
    existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE_of_start_restrict
      (k := k)
  exact successorMatrixPEStableUnderStartRestriction_subsingleton (k := k)

/-- One-state canary for the original Crux Prop: the bare PE payload is
discharged without extra hypotheses when the alphabet has exactly one state. -/
theorem existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE_fin_one :
    ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE 1 := by
  exact
    existsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE_subsingleton
      (k := 1)

/-- Extension-level Markov-mixture law from successor-matrix PE plus the
start-restricted PE needed to retain the initial-state/cylinder coupling. -/
theorem exists_markovParamLaw_of_successorMatrixPE_start
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (hPE_start :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a})) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k),
        P (MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
          ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  rcases directingRowKernel_payload_of_successorMatrixPE_start
      (k := k) P hPE hPE_start with ⟨rowKernel, hEval, hInv⟩
  exact exists_markovParamLaw_of_hEval_and_rowSuccessorMatrixInvariance
    (k := k) (P := P) rowKernel hEval hInv

noncomputable def markovMixture_of_extension_successorMatrixPE_start
    (μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k))
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k),
      μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (hPE_start :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a})) :
    MarkovMixture k μ := by
  let hmix := exists_markovParamLaw_of_successorMatrixPE_start
    (k := k) P hPE hPE_start
  exact
    { mixingLaw := Classical.choose hmix
      mixingLaw_prob := (Classical.choose_spec hmix).1
      represents := by
        intro xs
        rw [hExt xs]
        exact (Classical.choose_spec hmix).2 xs }

/-- Markov exchangeability and strong recurrence give successor-matrix partial
exchangeability on each start-restricted law. This is the start-conditioned
form needed for cylinder identities, packaged from the joint FLPR
start-intersection bridge. -/
theorem successorMatrixPartialExchangeable_start_restrict_of_markovExchangeable_strongRecurrence
    [NeZero k]
    (μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P)
    (a : Fin k) :
    SuccessorMatrixPartialExchangeable (k := k)
      (P.restrict {ω : ℕ → Fin k | ω 0 = a}) := by
  intro m' anchor idx σ
  obtain ⟨σ', M, hagree, hsupp, hidxM⟩ :=
    Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSuccessorArrayPE.exists_rowwise_finiteSupport_agree
      (k := k) σ anchor idx
  have hmapEq :
      (fun ω : ℕ → Fin k => fun j : Fin m' =>
        rowSuccessorVisitProcess (k := k) (anchor j) ω ((σ (anchor j)) (idx j))) =
    (fun ω : ℕ → Fin k => fun j : Fin m' =>
      rowSuccessorVisitProcess (k := k) (anchor j) ω (σ' (anchor j) (idx j))) := by
    funext ω j
    rw [hagree j]
  rw [hmapEq]
  have hmeas_rsp : ∀ i : Fin k,
      Measurable (rowSuccessorVisitProcess (k := k) i) :=
    fun i => measurable_rowSuccessorVisitProcess (k := k) i
  have hf : Measurable (fun ω : ℕ → Fin k => fun j : Fin m' =>
      rowSuccessorVisitProcess (k := k) (anchor j) ω (σ' (anchor j) (idx j))) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (σ' (anchor j) (idx j))).comp (hmeas_rsp (anchor j))
  have hg : Measurable (fun ω : ℕ → Fin k => fun j : Fin m' =>
      rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (idx j)).comp (hmeas_rsp (anchor j))
  apply MeasureTheory.Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply hf (measurableSet_singleton c),
    Measure.map_apply hg (measurableSet_singleton c)]
  have hpre : ∀ readIdx : Fin m' → ℕ,
      ((fun ω : ℕ → Fin k => fun j : Fin m' =>
        rowSuccessorVisitProcess (k := k) (anchor j) ω (readIdx j)) ⁻¹' {c}) =
      ⋂ j : Fin m', {ω : ℕ → Fin k |
        rowSuccessorAtNthVisit (k := k) (anchor j) (readIdx j) ω = c j} := by
    intro readIdx
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
      Set.mem_setOf_eq, funext_iff, rowSuccessorVisitProcess]
  rw [hpre (fun j => σ' (anchor j) (idx j)), hpre idx]
  have hmeasE : ∀ readIdx : Fin m' → ℕ,
      MeasurableSet (⋂ j : Fin m', {ω : ℕ → Fin k |
        rowSuccessorAtNthVisit (k := k) (anchor j) (readIdx j) ω = c j}) :=
    fun readIdx => MeasurableSet.iInter fun j =>
      measurableSet_rowSuccessorValueEvent (k := k) (anchor j) (readIdx j) (c j)
  rw [Measure.restrict_apply (μ := P)
      (s := {ω : ℕ → Fin k | ω 0 = a})
      (t := ⋂ j : Fin m', {ω : ℕ → Fin k |
        rowSuccessorAtNthVisit (k := k) (anchor j) (σ' (anchor j) (idx j)) ω = c j})
      (hmeasE (fun j => σ' (anchor j) (idx j))),
    Measure.restrict_apply (μ := P)
      (s := {ω : ℕ → Fin k | ω 0 = a})
      (t := ⋂ j : Fin m', {ω : ℕ → Fin k |
        rowSuccessorAtNthVisit (k := k) (anchor j) (idx j) ω = c j})
      (hmeasE idx)]
  simpa [Set.inter_comm] using
    Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSuccessorArrayPE.measure_start_inter_biInter_rsp_perm_eq
      (k := k) μ hμ P hExt hStrRec anchor idx σ' M hsupp hidxM c a

/-- Extension-level row-kernel payload for the strongly recurrent
Markov-exchangeable extension: the canonical directing row kernel has
singleton-evaluation measurability and row-successor-matrix invariance. -/
theorem directingRowKernel_payload_of_markovExchangeable_strongRecurrence
    (μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P) :
    ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
      (∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i)) ∧
      RowSuccessorMatrixInvariance (k := k) P rowKernel := by
  have hPE : SuccessorMatrixPartialExchangeable (k := k) P :=
    Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSuccessorArrayPE.successorMatrixPE_of_markovExchangeable_strongRecurrence_holds
      k μ P inferInstance hμ hExt hStrRec
  have hPE_start :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a}) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · intro a
      exact Fin.elim0 a
    · haveI : NeZero k := NeZero.of_pos hk
      intro a
      exact
        successorMatrixPartialExchangeable_start_restrict_of_markovExchangeable_strongRecurrence
          (k := k) μ hμ P hExt hStrRec a
  exact directingRowKernel_payload_of_successorMatrixPE_start (k := k) P hPE hPE_start

/-- Unconditional Markov de Finetti for strongly recurrent Markov-exchangeable
prefix laws, using the minted successor-matrix PE bridge and the canonical
directing-row-kernel payload. -/
theorem markovDeFinetti_strongRecurrence (k : ℕ) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  intro μ hμ hExtStrong
  rcases hExtStrong with ⟨P, hP, hExt, hStrong⟩
  letI : IsProbabilityMeasure P := hP
  rcases directingRowKernel_payload_of_markovExchangeable_strongRecurrence
      (k := k) μ hμ P hExt hStrong with ⟨rowKernel, hEval, hInv⟩
  rcases exists_markovParamLaw_of_hEval_and_rowSuccessorMatrixInvariance
      (k := k) P rowKernel hEval hInv with ⟨pi, hpi, hreprP⟩
  refine ⟨pi, hpi, ?_⟩
  intro xs
  rw [hExt xs]
  exact hreprP xs

theorem bounded_rider_tendsto_set_integral_empiricalProduct_successorReadProductIndicatorReal_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (anchor : Fin m → Fin k) (value : Fin m → Fin k)
    (r : ℕ) (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (riderValue : Fin r → Fin k)
    {s : Set (ℕ → Fin k)} :
    Tendsto
      (fun n =>
        ∫ ω in s,
          rowSuccessorEmpiricalFreqProduct (k := k) m anchor value n ω *
            successorReadProductIndicatorReal
              (k := k) r riderAnchor riderIdx riderValue ω ∂P)
      atTop
      (nhds
        (∫ ω in s,
          directingRowKernelCellRealProduct (k := k) P m anchor value ω *
            successorReadProductIndicatorReal
              (k := k) r riderAnchor riderIdx riderValue ω ∂P)) := by
  exact
    bounded_rider_tendsto_set_integral_empiricalProduct_of_successorMatrixPE
      (k := k) P hPE m anchor value
      (s := s)
      (H := fun ω =>
        successorReadProductIndicatorReal (k := k) r riderAnchor riderIdx riderValue ω)
      (C := 1)
      (integrable_successorReadProductIndicatorReal
        (k := k) P r riderAnchor riderIdx riderValue)
      zero_le_one
      (Filter.Eventually.of_forall (fun ω => by
        simpa [Real.norm_eq_abs] using
          successorReadProductIndicatorReal_abs_le_one
            (k := k) r riderAnchor riderIdx riderValue ω))

theorem tendsto_integral_injectiveTupleAverage_successorReadProductIndicatorReal_mul_rider_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (i : Fin k) (value : Fin m → Fin k)
    (r : ℕ) (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (riderValue : Fin r → Fin k) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω,
          (1 / ((Finset.univ.filter
              (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)) *
            ((Finset.univ.filter
                (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ =>
              successorReadProductIndicatorReal
                (k := k) m (fun _ => i) (fun j => (φ j).1) value ω *
              successorReadProductIndicatorReal
                (k := k) r riderAnchor riderIdx riderValue ω) ∂P)
      atTop
      (nhds
        (∫ ω,
      directingRowKernelCellRealProduct (k := k) P m (fun _ => i) value ω *
        successorReadProductIndicatorReal
          (k := k) r riderAnchor riderIdx riderValue ω ∂P)) := by
  classical
  let rider : (ℕ → Fin k) → ℝ :=
    fun ω =>
      successorReadProductIndicatorReal
        (k := k) r riderAnchor riderIdx riderValue ω
  let rowAt : (n : ℕ) → (Fin m → Fin n) → (ℕ → Fin k) → ℝ :=
    fun n φ ω =>
      successorReadProductIndicatorReal
        (k := k) m (fun _ : Fin m => i) (fun j => (φ j).1) value ω
  let injTuples : (n : ℕ) → Finset (Fin m → Fin n) :=
    fun n => Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)
  let allTerm : ℕ → (ℕ → Fin k) → ℝ :=
    fun n ω =>
      (1 / (n : ℝ)) ^ m *
        (Finset.univ.sum fun φ : Fin m → Fin n => rowAt n φ ω * rider ω)
  let injTerm : ℕ → (ℕ → Fin k) → ℝ :=
    fun n ω =>
      (1 / (n : ℝ)) ^ m *
        ((injTuples n).sum fun φ => rowAt n φ ω * rider ω)
  let normTerm : ℕ → (ℕ → Fin k) → ℝ :=
    fun n ω =>
      (1 / ((injTuples n).card : ℝ)) *
        ((injTuples n).sum fun φ => rowAt n φ ω * rider ω)
  let limit : ℝ :=
    ∫ ω,
      directingRowKernelCellRealProduct (k := k) P m (fun _ : Fin m => i) value ω *
        rider ω ∂P
  have hrow_rider_int :
      ∀ n (φ : Fin m → Fin n), Integrable (fun ω => rowAt n φ ω * rider ω) P := by
    intro n φ
    exact integrable_successorReadProductIndicatorReal_mul_successorReadProductIndicatorReal
      (k := k) P m r (fun _ : Fin m => i) (fun j : Fin m => (φ j).1)
      value riderAnchor riderIdx riderValue
  have hsum_all_int :
      ∀ n,
        Integrable
          (fun ω : ℕ → Fin k =>
            Finset.univ.sum fun φ : Fin m → Fin n => rowAt n φ ω * rider ω) P := by
    intro n
    exact MeasureTheory.integrable_finsetSum Finset.univ
      (fun φ _hφ => hrow_rider_int n φ)
  have hsum_inj_int :
      ∀ n,
        Integrable
          (fun ω : ℕ → Fin k =>
            (injTuples n).sum fun φ => rowAt n φ ω * rider ω) P := by
    intro n
    exact MeasureTheory.integrable_finsetSum (injTuples n)
      (fun φ _hφ => hrow_rider_int n φ)
  have hall_int : ∀ n, Integrable (allTerm n) P := by
    intro n
    exact (hsum_all_int n).const_mul ((1 / (n : ℝ)) ^ m)
  have hinj_int : ∀ n, Integrable (injTerm n) P := by
    intro n
    exact (hsum_inj_int n).const_mul ((1 / (n : ℝ)) ^ m)
  have hnorm_int : ∀ n, Integrable (normTerm n) P := by
    intro n
    exact (hsum_inj_int n).const_mul (1 / ((injTuples n).card : ℝ))
  have hEmp :
      Tendsto
        (fun n =>
          ∫ ω,
            rowSuccessorEmpiricalFreqProduct
              (k := k) m (fun _ : Fin m => i) value n ω * rider ω ∂P)
        atTop (nhds limit) := by
    simpa [limit, rider] using
      bounded_rider_tendsto_set_integral_empiricalProduct_successorReadProductIndicatorReal_of_successorMatrixPE
        (k := k) P hPE m (fun _ : Fin m => i) value
        r riderAnchor riderIdx riderValue
        (s := Set.univ)
  have hEmp_eq_all :
      (fun n =>
          ∫ ω,
            rowSuccessorEmpiricalFreqProduct
              (k := k) m (fun _ : Fin m => i) value n ω * rider ω ∂P)
        =ᶠ[atTop]
      (fun n => ∫ ω, allTerm n ω ∂P) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hnne : n ≠ 0 := by omega
    apply integral_congr_ae
    filter_upwards with ω
    rw [rowSuccessorEmpiricalFreqProduct_eq_allTuple_average
      (k := k) m n (fun _ : Fin m => i) value ω hnne]
    dsimp [allTerm, rowAt]
    rw [← Finset.sum_mul]
    ring
  have hAll : Tendsto (fun n => ∫ ω, allTerm n ω ∂P) atTop (nhds limit) :=
    Filter.Tendsto.congr' hEmp_eq_all hEmp
  have hrow_bound :
      ∀ n (φ : Fin m → Fin n) ω, |rowAt n φ ω| ≤ 1 := by
    intro n φ ω
    exact successorReadProductIndicatorReal_abs_le_one
      (k := k) m (fun _ : Fin m => i) (fun j : Fin m => (φ j).1) value ω
  have hrider_bound : ∀ ω, |rider ω| ≤ 1 := by
    intro ω
    exact successorReadProductIndicatorReal_abs_le_one
      (k := k) r riderAnchor riderIdx riderValue ω
  have hF_bound :
      ∀ n (φ : Fin m → Fin n) ω, |rowAt n φ ω * rider ω| ≤ 1 := by
    intro n φ ω
    calc
      |rowAt n φ ω * rider ω| = |rowAt n φ ω| * |rider ω| := abs_mul _ _
      _ ≤ 1 * 1 := by
          exact mul_le_mul (hrow_bound n φ ω) (hrider_bound ω)
            (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  have hCollAbs :
      Tendsto
        (fun n : ℕ =>
          |∫ ω, allTerm n ω - injTerm n ω ∂P|)
        atTop (nhds 0) := by
    have h :=
      setIntegral_allTuples_sub_injectiveTuples_average_mul_bounded_tendsto_zero
        (P := P) (s := Set.univ) m
        (F := fun n φ ω => rowAt n φ ω * rider ω)
        (H := fun _ω : ℕ → Fin k => (1 : ℝ))
        hF_bound
        (fun _ω => by simp)
    simpa [allTerm, injTerm, injTuples] using h
  have hCollDiffIntegral :
      Tendsto
        (fun n : ℕ => ∫ ω, allTerm n ω - injTerm n ω ∂P)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp_def] using hCollAbs
  have hAllSubInj :
      Tendsto
        (fun n : ℕ => (∫ ω, allTerm n ω ∂P) - ∫ ω, injTerm n ω ∂P)
        atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hCollDiffIntegral
    exact Filter.Eventually.of_forall fun n => by
      exact MeasureTheory.integral_sub (hall_int n) (hinj_int n)
  have hInjSubAll :
      Tendsto
        (fun n : ℕ => (∫ ω, injTerm n ω ∂P) - ∫ ω, allTerm n ω ∂P)
        atTop (nhds 0) := by
    have hneg := hAllSubInj.neg
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  have hInj :
      Tendsto (fun n : ℕ => ∫ ω, injTerm n ω ∂P) atTop (nhds limit) := by
    have hsum := hInjSubAll.add hAll
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  have hNormAbs :
      Tendsto
        (fun n : ℕ =>
          |∫ ω, normTerm n ω - injTerm n ω ∂P|)
        atTop (nhds 0) := by
    have h :=
      setIntegral_injectiveTupleAverage_sub_empiricalInjectiveAverage_tendsto_zero
        (P := P) (s := Set.univ) m
        (F := fun n φ ω => rowAt n φ ω * rider ω)
        hF_bound
    simpa [normTerm, injTerm, injTuples] using h
  have hNormDiffIntegral :
      Tendsto
        (fun n : ℕ => ∫ ω, normTerm n ω - injTerm n ω ∂P)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp_def] using hNormAbs
  have hNormSubInj :
      Tendsto
        (fun n : ℕ => (∫ ω, normTerm n ω ∂P) - ∫ ω, injTerm n ω ∂P)
        atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hNormDiffIntegral
    exact Filter.Eventually.of_forall fun n => by
      exact MeasureTheory.integral_sub (hnorm_int n) (hinj_int n)
  have hNorm :
      Tendsto (fun n : ℕ => ∫ ω, normTerm n ω ∂P) atTop (nhds limit) := by
    have hsum := hNormSubInj.add hInj
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  simpa [normTerm, injTuples, rowAt, rider, limit] using hNorm

theorem tendsto_setIntegral_injectiveTupleAverage_successorReadProductIndicatorReal_mul_rider_of_successorMatrixPE
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    {s : Set (ℕ → Fin k)}
    (m : ℕ) (i : Fin k) (value : Fin m → Fin k)
    (r : ℕ) (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (riderValue : Fin r → Fin k) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω in s,
          (1 / ((Finset.univ.filter
              (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)) *
            ((Finset.univ.filter
                (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ =>
              successorReadProductIndicatorReal
                (k := k) m (fun _ => i) (fun j => (φ j).1) value ω *
              successorReadProductIndicatorReal
                (k := k) r riderAnchor riderIdx riderValue ω) ∂P)
      atTop
      (nhds
        (∫ ω in s,
          directingRowKernelCellRealProduct (k := k) P m (fun _ => i) value ω *
            successorReadProductIndicatorReal
              (k := k) r riderAnchor riderIdx riderValue ω ∂P)) := by
  classical
  let rider : (ℕ → Fin k) → ℝ :=
    fun ω =>
      successorReadProductIndicatorReal
        (k := k) r riderAnchor riderIdx riderValue ω
  let rowAt : (n : ℕ) → (Fin m → Fin n) → (ℕ → Fin k) → ℝ :=
    fun n φ ω =>
      successorReadProductIndicatorReal
        (k := k) m (fun _ : Fin m => i) (fun j => (φ j).1) value ω
  let injTuples : (n : ℕ) → Finset (Fin m → Fin n) :=
    fun n => Finset.univ.filter (fun φ : Fin m → Fin n => Function.Injective φ)
  let allTerm : ℕ → (ℕ → Fin k) → ℝ :=
    fun n ω =>
      (1 / (n : ℝ)) ^ m *
        (Finset.univ.sum fun φ : Fin m → Fin n => rowAt n φ ω * rider ω)
  let injTerm : ℕ → (ℕ → Fin k) → ℝ :=
    fun n ω =>
      (1 / (n : ℝ)) ^ m *
        ((injTuples n).sum fun φ => rowAt n φ ω * rider ω)
  let normTerm : ℕ → (ℕ → Fin k) → ℝ :=
    fun n ω =>
      (1 / ((injTuples n).card : ℝ)) *
        ((injTuples n).sum fun φ => rowAt n φ ω * rider ω)
  let limit : ℝ :=
    ∫ ω in s,
      directingRowKernelCellRealProduct (k := k) P m (fun _ : Fin m => i) value ω *
        rider ω ∂P
  have hrow_rider_int :
      ∀ n (φ : Fin m → Fin n), Integrable (fun ω => rowAt n φ ω * rider ω) P := by
    intro n φ
    exact integrable_successorReadProductIndicatorReal_mul_successorReadProductIndicatorReal
      (k := k) P m r (fun _ : Fin m => i) (fun j : Fin m => (φ j).1)
      value riderAnchor riderIdx riderValue
  have hsum_all_int :
      ∀ n,
        Integrable
          (fun ω : ℕ → Fin k =>
            Finset.univ.sum fun φ : Fin m → Fin n => rowAt n φ ω * rider ω) P := by
    intro n
    exact MeasureTheory.integrable_finsetSum Finset.univ
      (fun φ _hφ => hrow_rider_int n φ)
  have hsum_inj_int :
      ∀ n,
        Integrable
          (fun ω : ℕ → Fin k =>
            (injTuples n).sum fun φ => rowAt n φ ω * rider ω) P := by
    intro n
    exact MeasureTheory.integrable_finsetSum (injTuples n)
      (fun φ _hφ => hrow_rider_int n φ)
  have hall_int : ∀ n, Integrable (allTerm n) P := by
    intro n
    exact (hsum_all_int n).const_mul ((1 / (n : ℝ)) ^ m)
  have hinj_int : ∀ n, Integrable (injTerm n) P := by
    intro n
    exact (hsum_inj_int n).const_mul ((1 / (n : ℝ)) ^ m)
  have hnorm_int : ∀ n, Integrable (normTerm n) P := by
    intro n
    exact (hsum_inj_int n).const_mul (1 / ((injTuples n).card : ℝ))
  have hall_int_restrict : ∀ n, Integrable (allTerm n) (P.restrict s) := by
    intro n
    exact (hall_int n).mono_measure Measure.restrict_le_self
  have hinj_int_restrict : ∀ n, Integrable (injTerm n) (P.restrict s) := by
    intro n
    exact (hinj_int n).mono_measure Measure.restrict_le_self
  have hnorm_int_restrict : ∀ n, Integrable (normTerm n) (P.restrict s) := by
    intro n
    exact (hnorm_int n).mono_measure Measure.restrict_le_self
  have hEmp :
      Tendsto
        (fun n =>
          ∫ ω in s,
            rowSuccessorEmpiricalFreqProduct
              (k := k) m (fun _ : Fin m => i) value n ω * rider ω ∂P)
        atTop (nhds limit) := by
    simpa [limit, rider] using
      bounded_rider_tendsto_set_integral_empiricalProduct_successorReadProductIndicatorReal_of_successorMatrixPE
        (k := k) P hPE m (fun _ : Fin m => i) value
        r riderAnchor riderIdx riderValue
        (s := s)
  have hEmp_eq_all :
      (fun n =>
          ∫ ω in s,
            rowSuccessorEmpiricalFreqProduct
              (k := k) m (fun _ : Fin m => i) value n ω * rider ω ∂P)
        =ᶠ[atTop]
      (fun n => ∫ ω in s, allTerm n ω ∂P) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hnne : n ≠ 0 := by omega
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    rw [rowSuccessorEmpiricalFreqProduct_eq_allTuple_average
      (k := k) m n (fun _ : Fin m => i) value ω hnne]
    dsimp [allTerm, rowAt]
    rw [← Finset.sum_mul]
    ring
  have hAll : Tendsto (fun n => ∫ ω in s, allTerm n ω ∂P) atTop (nhds limit) :=
    Filter.Tendsto.congr' hEmp_eq_all hEmp
  have hrow_bound :
      ∀ n (φ : Fin m → Fin n) ω, |rowAt n φ ω| ≤ 1 := by
    intro n φ ω
    exact successorReadProductIndicatorReal_abs_le_one
      (k := k) m (fun _ : Fin m => i) (fun j : Fin m => (φ j).1) value ω
  have hrider_bound : ∀ ω, |rider ω| ≤ 1 := by
    intro ω
    exact successorReadProductIndicatorReal_abs_le_one
      (k := k) r riderAnchor riderIdx riderValue ω
  have hF_bound :
      ∀ n (φ : Fin m → Fin n) ω, |rowAt n φ ω * rider ω| ≤ 1 := by
    intro n φ ω
    calc
      |rowAt n φ ω * rider ω| = |rowAt n φ ω| * |rider ω| := abs_mul _ _
      _ ≤ 1 * 1 := by
          exact mul_le_mul (hrow_bound n φ ω) (hrider_bound ω)
            (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  have hCollAbs :
      Tendsto
        (fun n : ℕ =>
          |∫ ω in s, allTerm n ω - injTerm n ω ∂P|)
        atTop (nhds 0) := by
    have h :=
      setIntegral_allTuples_sub_injectiveTuples_average_mul_bounded_tendsto_zero
        (P := P) (s := s) m
        (F := fun n φ ω => rowAt n φ ω * rider ω)
        (H := fun _ω : ℕ → Fin k => (1 : ℝ))
        hF_bound
        (fun _ω => by simp)
    simpa [allTerm, injTerm, injTuples] using h
  have hCollDiffIntegral :
      Tendsto
        (fun n : ℕ => ∫ ω in s, allTerm n ω - injTerm n ω ∂P)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp_def] using hCollAbs
  have hAllSubInj :
      Tendsto
        (fun n : ℕ => (∫ ω in s, allTerm n ω ∂P) - ∫ ω in s, injTerm n ω ∂P)
        atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hCollDiffIntegral
    exact Filter.Eventually.of_forall fun n => by
      exact MeasureTheory.integral_sub (μ := P.restrict s)
        (hall_int_restrict n) (hinj_int_restrict n)
  have hInjSubAll :
      Tendsto
        (fun n : ℕ => (∫ ω in s, injTerm n ω ∂P) - ∫ ω in s, allTerm n ω ∂P)
        atTop (nhds 0) := by
    have hneg := hAllSubInj.neg
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  have hInj :
      Tendsto (fun n : ℕ => ∫ ω in s, injTerm n ω ∂P) atTop (nhds limit) := by
    have hsum := hInjSubAll.add hAll
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  have hNormAbs :
      Tendsto
        (fun n : ℕ =>
          |∫ ω in s, normTerm n ω - injTerm n ω ∂P|)
        atTop (nhds 0) := by
    have h :=
      setIntegral_injectiveTupleAverage_sub_empiricalInjectiveAverage_tendsto_zero
        (P := P) (s := s) m
        (F := fun n φ ω => rowAt n φ ω * rider ω)
        hF_bound
    simpa [normTerm, injTerm, injTuples] using h
  have hNormDiffIntegral :
      Tendsto
        (fun n : ℕ => ∫ ω in s, normTerm n ω - injTerm n ω ∂P)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp_def] using hNormAbs
  have hNormSubInj :
      Tendsto
        (fun n : ℕ => (∫ ω in s, normTerm n ω ∂P) - ∫ ω in s, injTerm n ω ∂P)
        atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hNormDiffIntegral
    exact Filter.Eventually.of_forall fun n => by
      exact MeasureTheory.integral_sub (μ := P.restrict s)
        (hnorm_int_restrict n) (hinj_int_restrict n)
  have hNorm :
      Tendsto (fun n : ℕ => ∫ ω in s, normTerm n ω ∂P) atTop (nhds limit) := by
    have hsum := hNormSubInj.add hInj
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  simpa [normTerm, injTuples, rowAt, rider, limit] using hNorm

theorem successorMatrixPE_oneRow_peel_integral_indicatorReal_mul_rider_eq_directingRowKernelCellRealProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (m : ℕ) (i : Fin k) (idx : Fin m → ℕ) (value : Fin m → Fin k)
    (r : ℕ) (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (riderValue : Fin r → Fin k)
    (hidx : Function.Injective idx)
    (hfixed : ∀ q : Fin r, riderAnchor q ≠ i) :
    ∫ ω,
        successorReadProductIndicatorReal (k := k) m (fun _ => i) idx value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω ∂P
      =
    ∫ ω,
        directingRowKernelCellRealProduct (k := k) P m (fun _ => i) value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω ∂P := by
  classical
  let fixed : ℝ :=
    ∫ ω,
      successorReadProductIndicatorReal (k := k) m (fun _ : Fin m => i) idx value ω *
        successorReadProductIndicatorReal
          (k := k) r riderAnchor riderIdx riderValue ω ∂P
  let target : ℝ :=
    ∫ ω,
      directingRowKernelCellRealProduct (k := k) P m (fun _ : Fin m => i) value ω *
        successorReadProductIndicatorReal
          (k := k) r riderAnchor riderIdx riderValue ω ∂P
  let normSeq : ℕ → ℝ := fun n =>
    ∫ ω,
      (1 / ((Finset.univ.filter
          (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)) *
        ((Finset.univ.filter
            (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ =>
          successorReadProductIndicatorReal
            (k := k) m (fun _ : Fin m => i) (fun j => (φ j).1) value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω) ∂P
  have hnorm_tendsto : Tendsto normSeq atTop (nhds target) := by
    simpa [normSeq, target] using
      tendsto_integral_injectiveTupleAverage_successorReadProductIndicatorReal_mul_rider_of_successorMatrixPE
        (k := k) P hPE m i value r riderAnchor riderIdx riderValue
  have hnorm_eq_fixed : normSeq =ᶠ[atTop] fun _n : ℕ => fixed := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨m, ?_⟩
    intro n hn
    symm
    simpa [normSeq, fixed] using
      successorMatrixPE_oneRow_spreading_integral_injectiveTupleAverage_indicatorReal_mul_rider_eq
        (k := k) P hPE m n hn i idx value
        r riderAnchor riderIdx riderValue hidx hfixed
  have hfixed_tendsto : Tendsto (fun _n : ℕ => fixed) atTop (nhds target) :=
    Filter.Tendsto.congr' hnorm_eq_fixed hnorm_tendsto
  have hfixed_const : Tendsto (fun _n : ℕ => fixed) atTop (nhds fixed) :=
    tendsto_const_nhds
  have heq : fixed = target :=
    tendsto_nhds_unique hfixed_const hfixed_tendsto
  simpa [fixed, target] using heq

theorem successorMatrixPE_oneRow_peel_setIntegral_indicatorReal_mul_rider_eq_directingRowKernelCellRealProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    {s : Set (ℕ → Fin k)}
    (hPEs : SuccessorMatrixPartialExchangeable (k := k) (P.restrict s))
    (m : ℕ) (i : Fin k) (idx : Fin m → ℕ) (value : Fin m → Fin k)
    (r : ℕ) (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (riderValue : Fin r → Fin k)
    (hidx : Function.Injective idx)
    (hfixed : ∀ q : Fin r, riderAnchor q ≠ i) :
    ∫ ω in s,
        successorReadProductIndicatorReal (k := k) m (fun _ => i) idx value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω ∂P
      =
    ∫ ω in s,
        directingRowKernelCellRealProduct (k := k) P m (fun _ => i) value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω ∂P := by
  classical
  let fixed : ℝ :=
    ∫ ω in s,
      successorReadProductIndicatorReal (k := k) m (fun _ : Fin m => i) idx value ω *
        successorReadProductIndicatorReal
          (k := k) r riderAnchor riderIdx riderValue ω ∂P
  let target : ℝ :=
    ∫ ω in s,
      directingRowKernelCellRealProduct (k := k) P m (fun _ : Fin m => i) value ω *
        successorReadProductIndicatorReal
          (k := k) r riderAnchor riderIdx riderValue ω ∂P
  let normSeq : ℕ → ℝ := fun n =>
    ∫ ω in s,
      (1 / ((Finset.univ.filter
          (fun φ : Fin m → Fin n => Function.Injective φ)).card : ℝ)) *
        ((Finset.univ.filter
            (fun φ : Fin m → Fin n => Function.Injective φ)).sum fun φ =>
          successorReadProductIndicatorReal
            (k := k) m (fun _ : Fin m => i) (fun j => (φ j).1) value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω) ∂P
  have hnorm_tendsto : Tendsto normSeq atTop (nhds target) := by
    simpa [normSeq, target] using
      tendsto_setIntegral_injectiveTupleAverage_successorReadProductIndicatorReal_mul_rider_of_successorMatrixPE
        (k := k) P hPE (s := s) m i value r riderAnchor riderIdx riderValue
  have hnorm_eq_fixed : normSeq =ᶠ[atTop] fun _n : ℕ => fixed := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨m, ?_⟩
    intro n hn
    symm
    simpa [normSeq, fixed] using
      successorMatrixPE_oneRow_spreading_integral_injectiveTupleAverage_indicatorReal_mul_rider_eq
        (k := k) (P := P.restrict s) hPEs m n hn i idx value
        r riderAnchor riderIdx riderValue hidx hfixed
  have hfixed_tendsto : Tendsto (fun _n : ℕ => fixed) atTop (nhds target) :=
    Filter.Tendsto.congr' hnorm_eq_fixed hnorm_tendsto
  have hfixed_const : Tendsto (fun _n : ℕ => fixed) atTop (nhds fixed) :=
    tendsto_const_nhds
  have heq : fixed = target :=
    tendsto_nhds_unique hfixed_const hfixed_tendsto
  simpa [fixed, target] using heq

theorem successorMatrixPE_oneRow_peel_startSetIntegral_indicatorReal_mul_rider_eq_directingRowKernelCellRealProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (hPE_start :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a}))
    (a : Fin k)
    (m : ℕ) (i : Fin k) (idx : Fin m → ℕ) (value : Fin m → Fin k)
    (r : ℕ) (riderAnchor : Fin r → Fin k) (riderIdx : Fin r → ℕ)
    (riderValue : Fin r → Fin k)
    (hidx : Function.Injective idx)
    (hfixed : ∀ q : Fin r, riderAnchor q ≠ i) :
    ∫ ω in {ω : ℕ → Fin k | ω 0 = a},
        successorReadProductIndicatorReal (k := k) m (fun _ => i) idx value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω ∂P
      =
    ∫ ω in {ω : ℕ → Fin k | ω 0 = a},
        directingRowKernelCellRealProduct (k := k) P m (fun _ => i) value ω *
          successorReadProductIndicatorReal
            (k := k) r riderAnchor riderIdx riderValue ω ∂P := by
  exact
    successorMatrixPE_oneRow_peel_setIntegral_indicatorReal_mul_rider_eq_directingRowKernelCellRealProduct
      (k := k) P hPE
      (s := {ω : ℕ → Fin k | ω 0 = a})
      (hPEs := hPE_start a)
      m i idx value r riderAnchor riderIdx riderValue hidx hfixed

theorem successorMatrixPE_oneRow_peel_start_wordFiber_integral_eq_directingRowKernelCellRealProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hPE : SuccessorMatrixPartialExchangeable (k := k) P)
    (hPE_start :
      ∀ a : Fin k,
        SuccessorMatrixPartialExchangeable (k := k)
          (P.restrict {ω : ℕ → Fin k | ω 0 = a}))
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    (P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: ys))).toReal
      =
    ∫ ω in {ω : ℕ → Fin k | ω 0 = a},
        directingRowKernelCellRealProduct
            (k := k) P (wordAnchorFiberList (k := k) a ys i).length
            (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
            (wordAnchorFiberValue (k := k) a ys i) ω *
          successorReadProductIndicatorReal
            (k := k) (wordAnchorComplementList (k := k) a ys i).length
            (wordAnchorComplementAnchor (k := k) a ys i)
            (wordAnchorComplementIdx (k := k) a ys i)
            (wordAnchorComplementValue (k := k) a ys i) ω ∂P := by
  calc
    (P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: ys))).toReal
        =
      ∫ ω in {ω : ℕ → Fin k | ω 0 = a},
          successorReadProductIndicatorReal
              (k := k) (wordAnchorFiberList (k := k) a ys i).length
              (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
              (wordAnchorFiberIdx (k := k) a ys i)
              (wordAnchorFiberValue (k := k) a ys i) ω *
            successorReadProductIndicatorReal
              (k := k) (wordAnchorComplementList (k := k) a ys i).length
              (wordAnchorComplementAnchor (k := k) a ys i)
              (wordAnchorComplementIdx (k := k) a ys i)
              (wordAnchorComplementValue (k := k) a ys i) ω ∂P := by
          exact (integral_start_wordFiber_mul_complement_eq_measure_cylinder_toReal
            (k := k) P a ys i).symm
    _ =
      ∫ ω in {ω : ℕ → Fin k | ω 0 = a},
          directingRowKernelCellRealProduct
              (k := k) P (wordAnchorFiberList (k := k) a ys i).length
              (fun _ : Fin (wordAnchorFiberList (k := k) a ys i).length => i)
              (wordAnchorFiberValue (k := k) a ys i) ω *
            successorReadProductIndicatorReal
              (k := k) (wordAnchorComplementList (k := k) a ys i).length
              (wordAnchorComplementAnchor (k := k) a ys i)
              (wordAnchorComplementIdx (k := k) a ys i)
              (wordAnchorComplementValue (k := k) a ys i) ω ∂P := by
          exact
            successorMatrixPE_oneRow_peel_startSetIntegral_indicatorReal_mul_rider_eq_directingRowKernelCellRealProduct
              (k := k) P hPE hPE_start a
              (wordAnchorFiberList (k := k) a ys i).length i
              (wordAnchorFiberIdx (k := k) a ys i)
              (wordAnchorFiberValue (k := k) a ys i)
              (wordAnchorComplementList (k := k) a ys i).length
              (wordAnchorComplementAnchor (k := k) a ys i)
              (wordAnchorComplementIdx (k := k) a ys i)
              (wordAnchorComplementValue (k := k) a ys i)
              (wordAnchorFiberIdx_injective (k := k) a ys i)
              (wordAnchorComplementAnchor_ne (k := k) a ys i)

end MarkovDeFinettiHard

open Mettapedia.UniversalAI.UniversalPrediction
open Mettapedia.UniversalAI.UniversalPrediction.MarkovExchangeabilityBridge

namespace MarkovMixture

variable {k : ℕ}
variable {μ : FiniteAlphabet.PrefixMeasure (Fin k)}

/-- Public constructor for the proved strong-recurrence Markov de Finetti
surface. It packages the closed Fortini endpoint into the `MarkovMixture` API. -/
noncomputable def of_markovExchangeable_strongRecurrence
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [hP : IsProbabilityMeasure P]
    (hExt :
      ∀ xs : List (Fin k),
        μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (hStrRec : MarkovDeFinettiHard.StrongRecurrence (k := k) P) :
    MarkovMixture k μ :=
  of_extension_strongRecurrence
    (k := k)
    (μ := μ)
    (hFortini := MarkovDeFinettiHard.markovDeFinetti_strongRecurrence k)
    hμ P hExt hStrRec

end MarkovMixture

end Mettapedia.ProbabilityTheory.Exchangeability
