/-
Copyright (c) 2025 Mettapedia Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mettapedia Contributors
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Fintype.Card

/-!
# Measurable Partitions for Stratified Inference

This file defines measurable partitions (histogram bins) of a feature space,
which form the foundation for stratified PLN inference.

## Main Definitions

* `HistogramBins` - A K-bin partition of a measurable space
* `binIndex` - Function mapping points to their bin index
* `maxBinDiameter` - Maximum diameter of all bins (for refinement analysis)

## References

* Stratified sampling in survey statistics
* Histogram regression (Györfi et al., "A Distribution-Free Theory of Nonparametric Regression")
-/

namespace Mettapedia.Logic.StratifiedPLN

open Set MeasureTheory

/-! ## Histogram Bins -/

/-- A K-bin partition of a measurable space X.
    Each bin is a measurable set, bins are pairwise disjoint, and they cover X.

    This models the stratification in histogram regression:
    partition the feature space into bins, then estimate P(Y=1|X) separately per bin. -/
structure HistogramBins (X : Type*) [MeasurableSpace X] (K : ℕ) where
  /-- The bins as a function from Fin K to sets -/
  bins : Fin K → Set X
  /-- Each bin is measurable -/
  bins_measurable : ∀ i, MeasurableSet (bins i)
  /-- Bins are pairwise disjoint -/
  bins_disjoint : ∀ i j, i ≠ j → Disjoint (bins i) (bins j)
  /-- Bins cover the entire space -/
  bins_cover : ⋃ i, bins i = univ

namespace HistogramBins

variable {X : Type*} [MeasurableSpace X] {K : ℕ} (partition : HistogramBins X K)

/-- Each point x belongs to at least one bin. -/
theorem exists_bin_containing (x : X) : ∃ i, x ∈ partition.bins i := by
  have h := partition.bins_cover
  have hx : x ∈ ⋃ i, partition.bins i := by rw [h]; exact mem_univ x
  simp only [mem_iUnion] at hx
  exact hx

/-- Each point x belongs to at most one bin. -/
theorem unique_bin_containing (x : X) (i j : Fin K) (hi : x ∈ partition.bins i)
    (hj : x ∈ partition.bins j) : i = j := by
  by_contra hij
  have hdisj := partition.bins_disjoint i j hij
  exact hdisj.ne_of_mem hi hj rfl

/-- Each point belongs to exactly one bin. -/
theorem exists_unique_bin (x : X) : ∃! i, x ∈ partition.bins i := by
  obtain ⟨i, hi⟩ := partition.exists_bin_containing x
  exact ⟨i, hi, fun j hj => partition.unique_bin_containing x j i hj hi⟩

/-- The bin index function: maps each point x to its unique bin.
    This is the key function for stratified estimation. -/
noncomputable def binIndex (hK : 0 < K) (x : X) : Fin K :=
  by
    classical
    -- `hK` rules out the degenerate `K = 0` case and also keeps the linter happy.
    have _ : 0 < K := hK
    exact (partition.exists_unique_bin x).choose

/-- The bin index correctly identifies the containing bin. -/
theorem mem_bin_of_binIndex (hK : 0 < K) (x : X) :
    x ∈ partition.bins (partition.binIndex hK x) :=
  (partition.exists_unique_bin x).choose_spec.1

/-- The bin index is the unique bin containing x. -/
theorem binIndex_eq_iff (hK : 0 < K) (x : X) (i : Fin K) :
    partition.binIndex hK x = i ↔ x ∈ partition.bins i := by
  constructor
  · intro h
    rw [← h]
    exact partition.mem_bin_of_binIndex hK x
  · intro hx
    have huniq := (partition.exists_unique_bin x).choose_spec.2
    exact (huniq i hx).symm

/-- The preimage of a single bin index is that bin. -/
theorem binIndex_preimage (hK : 0 < K) (i : Fin K) :
    partition.binIndex hK ⁻¹' {i} = partition.bins i := by
  ext x
  simp only [mem_preimage, mem_singleton_iff]
  exact partition.binIndex_eq_iff hK x i

/-- The bin index function is measurable. -/
theorem binIndex_measurable (hK : 0 < K) :
    Measurable (partition.binIndex hK) := by
  -- Fin K has the discrete (⊤) measurable space, so we show preimages of all sets are measurable
  intro s _
  -- Any subset of Fin K is a finite union of singletons
  have : s = ⋃ i ∈ s, {i} := by simp
  rw [this, Set.preimage_iUnion₂]
  apply MeasurableSet.biUnion (Set.toFinite s).countable
  intro i _
  rw [partition.binIndex_preimage hK i]
  exact partition.bins_measurable i

end HistogramBins

/-! ## Bin Diameter (for Metric Spaces) -/

section MetricSpace

variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]

/-- The diameter of a single set. -/
noncomputable def setDiameter (S : Set X) : ℝ := Metric.diam S

/-- The maximum diameter across all bins.
    This controls the approximation error in histogram regression. -/
noncomputable def maxBinDiameter {K : ℕ} (partition : HistogramBins X K) : ℝ :=
  ⨆ i : Fin K, setDiameter (partition.bins i)

/-- Maximum diameter is non-negative when K > 0. -/
theorem maxBinDiameter_nonneg {K : ℕ} (partition : HistogramBins X K) (hK : 0 < K) :
    0 ≤ maxBinDiameter partition := by
  unfold maxBinDiameter setDiameter
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hbdd : BddAbove (Set.range fun i => Metric.diam (partition.bins i)) :=
    (Set.finite_range _).bddAbove
  exact le_ciSup_of_le hbdd ⟨0, hK⟩ Metric.diam_nonneg

end MetricSpace

/-! ## Partition Refinement -/

variable {X : Type*} [MeasurableSpace X]

/-- Partition P₂ refines P₁ if every bin of P₂ is contained in some bin of P₁.
    This is the key property for showing histogram regression convergence. -/
def Refines {K₁ K₂ : ℕ} (P₁ : HistogramBins X K₁) (P₂ : HistogramBins X K₂) : Prop :=
  ∀ i₂ : Fin K₂, ∃ i₁ : Fin K₁, P₂.bins i₂ ⊆ P₁.bins i₁

/-- Refinement is reflexive. -/
theorem Refines.refl {K : ℕ} (P : HistogramBins X K) : Refines P P :=
  fun i => ⟨i, subset_refl _⟩

/-- Refinement is transitive. -/
theorem Refines.trans {K₁ K₂ K₃ : ℕ} {P₁ : HistogramBins X K₁}
    {P₂ : HistogramBins X K₂} {P₃ : HistogramBins X K₃}
    (h₁₂ : Refines P₁ P₂) (h₂₃ : Refines P₂ P₃) : Refines P₁ P₃ := by
  intro i₃
  obtain ⟨i₂, h₂⟩ := h₂₃ i₃
  obtain ⟨i₁, h₁⟩ := h₁₂ i₂
  exact ⟨i₁, subset_trans h₂ h₁⟩

/-! ## Evidence per Bin -/

/-- Evidence counts for each bin in a K-bin partition.
    This is what PLN uses for stratified inference. -/
structure BinEvidence (K : ℕ) where
  /-- Positive evidence count per bin -/
  pos : Fin K → ℕ
  /-- Negative evidence count per bin -/
  neg : Fin K → ℕ

namespace BinEvidence

variable {K : ℕ}

/-- Total evidence in bin i. -/
def total (evidence : BinEvidence K) (i : Fin K) : ℕ :=
  evidence.pos i + evidence.neg i

/-- Zero evidence: no observations in any bin. -/
def zero : BinEvidence K where
  pos := fun _ => 0
  neg := fun _ => 0

/-- Add evidence from a single observation to a bin. -/
def addObservation (evidence : BinEvidence K) (i : Fin K) (positive : Bool) : BinEvidence K where
  pos := fun j => if j = i ∧ positive then evidence.pos j + 1 else evidence.pos j
  neg := fun j => if j = i ∧ ¬positive then evidence.neg j + 1 else evidence.neg j

end BinEvidence

end Mettapedia.Logic.StratifiedPLN
