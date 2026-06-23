import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.Group.Defs
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Order.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import KnuthSkilling

/-
# Measure Theory from Symmetry

This file shows how measure theory EMERGES from the Knuth–Skilling
symmetry foundations, connecting to Mathlib's standard structures.

Key results:
- Un-normalized valuations (`μ(⊤)` allowed in `(0,∞)`, not necessarily `1`)
- σ-additivity from continuity (the paper's KEY insight)
- Connection to `MeasureTheory.Measure`
- Haar measures from translation invariance

References:
- Skilling & Knuth (2018), Section 2 (Measure Theory)
- ~/claude/literature/Knuth_Skilling/Knuth_Skilling_1712.09725v3.pdf
-/

noncomputable section

open Classical
open scoped BigOperators Pointwise ENNReal Topology
open MeasureTheory Filter Set
open KnuthSkilling

namespace Mettapedia.MeasureTheory

/-! ## Un-normalized valuations -/

/-- An un-normalized plausibility valuation into extended non-negative reals.
Unlike a probability valuation, we do not require `val ⊤ = 1`. -/
structure UnnormalizedValuation (α : Type*) [CompleteLattice α] where
  val : α → ℝ≥0∞
  monotone : Monotone val
  val_bot : val ⊥ = 0
  -- Note: NO requirement that val ⊤ = 1

/-! ## Cox-style combination in the un-normalized setting -/

/-- Cox combination laws for un-normalized valuations.
We keep only the algebraic structure needed for the additivity derivation. -/
structure UnnormalizedCox (α : Type*) [CompleteLattice α] (μ : UnnormalizedValuation α) where
  combine_fn : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞
  combine_comm : ∀ x y, combine_fn x y = combine_fn y x
  combine_assoc :
    ∀ x y z, combine_fn (combine_fn x y) z = combine_fn x (combine_fn y z)
  combine_val :
    ∀ a b, Disjoint a b → μ.val (a ⊔ b) = combine_fn (μ.val a) (μ.val b)
  /-- Regraduation map that linearizes the combination law. -/
  regrade : ℝ≥0∞ → ℝ≥0∞
  regrade_strictMono : StrictMono regrade
  regrade_additive : ∀ x y, regrade (x + y) = regrade x + regrade y
  regrade_combine : ∀ x y, regrade (combine_fn x y) = regrade x + regrade y

/-! ## Finite additivity for un-normalized valuations -/

-- TODO: Adapt the regraduation-based proof from `KnuthSkilling.lean`.
theorem unnormalized_combine_is_add {α : Type*}
    [CompleteLattice α]
    (μ : UnnormalizedValuation α) (cox : UnnormalizedCox α μ) :
    ∀ x y, cox.combine_fn x y = x + y := by
  intro x y
  -- The regraduation map linearizes the combination; strict monotonicity gives injectivity.
  refine cox.regrade_strictMono.injective ?_
  calc
    cox.regrade (cox.combine_fn x y) = cox.regrade x + cox.regrade y :=
      cox.regrade_combine x y
    _ = cox.regrade (x + y) := (cox.regrade_additive x y).symm

/-! ## σ-additivity from continuity (core Knuth–Skilling insight) -/

theorem sigma_additive_from_continuity {α : Type*}
    [CompleteBooleanAlgebra α]
    (μ : UnnormalizedValuation α)
    (cox : UnnormalizedCox α μ)
    (continuity : ∀ (s : ℕ → α), Monotone s →
      Tendsto (μ.val ∘ s) atTop (𝓝 (μ.val (⨆ i, s i)))) :
    ∀ (f : ℕ → α), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
      μ.val (⨆ i, f i) = ∑' i, μ.val (f i) := by
  /-
  PROOF STRATEGY (Knuth-Skilling's KEY insight):

  The key idea: σ-additivity is DERIVED from continuity + finite additivity.

  Steps:
  1. Define partial finite unions s_n := f 0 ⊔ f 1 ⊔ ... ⊔ f n (recursive definition)
  2. Prove s is monotone: s_n ≤ s_{n+1} by construction
  3. Prove ⨆ n, s_n = ⨆ i, f_i (lattice algebra)
  4. Prove finite additivity: μ(s_n) = ∑_{i=0}^n μ(f_i)
     - By induction on n
     - Base: μ(s_0) = μ(f_0)
     - Step: μ(s_{n+1}) = μ(s_n ⊔ f_{n+1})
                         = μ(s_n) + μ(f_{n+1})  [by combine_fn = (+)]
                         = ∑_{i=0}^n μ(f_i) + μ(f_{n+1})  [by IH]
                         = ∑_{i=0}^{n+1} μ(f_i)
     - Need disjointness: s_n ⊥ f_{n+1} follows from pairwise disjoint f
  5. Apply continuity: μ(⨆ n, s_n) = ⨆ n, μ(s_n)
     - This uses the continuity hypothesis
     - Plus: ENNReal values preserve suprema under Tendsto
  6. Connect to infinite series:
     - ⨆ n, μ(s_n) = ⨆ n, ∑_{i=0}^n μ(f_i)  [by step 4]
                    = ∑' i, μ(f_i)           [ENNReal.tsum_eq_iSup_nat]

  Combining: μ(⨆ i, f_i) = μ(⨆ n, s_n)  [step 3]
                         = ⨆ n, μ(s_n)  [step 5]
                         = ∑' i, μ(f_i)  [step 6]

  Technical challenge: Lean's `let rec` doesn't unfold easily in proofs.
  Solution: Define s as auxiliary recursive function, or use Finset.sup directly.

  Key lemmas needed:
  - unnormalized_combine_is_add (already proven!)
  - Finset.sum_range_succ
  - ENNReal.tsum_eq_iSup_nat
  - Monotone.map_iSup_of_continuousAt or similar

  This proof is the CORE MATHEMATICAL CONTENT of the Knuth-Skilling paper's
  measure theory section. It shows σ-additivity is not an axiom but a
  THEOREM derived from symmetry + continuity.
  -/
  classical
  intro f hf_disj

  -- Partial finite suprema: `s (n+1) = s n ⊔ f (n+1)`
  let s : ℕ → α :=
    Nat.rec (f 0) (fun n sn => sn ⊔ f (n + 1))
  have s_zero : s 0 = f 0 := rfl
  have s_succ : ∀ n, s (n + 1) = s n ⊔ f (n + 1) := fun _ => rfl

  -- Monotonicity of `s`.
  have hs_step : ∀ n, s n ≤ s (n + 1) := by
    intro n
    simp only [s_succ, le_sup_left]
  have hs_mono : Monotone s := by
    -- Monotonicity follows from the step inequality.
    exact monotone_nat_of_le_succ hs_step

  -- Each `f i` sits inside `s i`.
  have hf_le_s : ∀ i, f i ≤ s i := by
    intro i
    induction i with
    | zero => simp only [s_zero, le_refl]
    | succ k hk =>
        have : f (k + 1) ≤ s k ⊔ f (k + 1) := le_sup_right
        simp only [s_succ, this]

  -- Supremum of partial unions coincides with supremum of the whole family.
  have hs_sup : (⨆ n, s n) = ⨆ i, f i := by
    apply le_antisymm
    · -- `s n` is built from earlier `f i`, so it is bounded by `⨆ i, f i`.
      have hs_le : ∀ n, s n ≤ ⨆ i, f i := by
        intro n
        induction n with
        | zero => exact le_iSup (fun i => f i) 0
        | succ k hk =>
            calc
              s (k + 1) = s k ⊔ f (k + 1) := s_succ k
              _ ≤ (⨆ i, f i) ⊔ (⨆ i, f i) := sup_le_sup hk (le_iSup (fun i => f i) (k + 1))
              _ = ⨆ i, f i := by simp only [sup_idem]
      exact iSup_le hs_le
    · -- Conversely, each `f i` is contained in `s i`, hence under the `iSup`.
      refine iSup_le ?_
      intro i
      exact le_iSup_of_le i (hf_le_s i)

  -- Disjointness: prefixes stay disjoint from any later element.
  have hs_disj_future : ∀ n m, n < m → Disjoint (s n) (f m) := by
    intro n
    induction n with
    | zero =>
        intro m hm
        have hneq : 0 ≠ m := Nat.ne_of_lt hm
        simpa [s_zero] using hf_disj 0 m hneq
    | succ k hk =>
        intro m hm
        have hkm : k < m := Nat.lt_trans (Nat.lt_succ_self _) hm
        have hdisj_sk : Disjoint (s k) (f m) := hk m hkm
        have hdisj_fk : Disjoint (f (k + 1)) (f m) := hf_disj (k + 1) m (Nat.ne_of_lt hm)
        have hsup : Disjoint (s k ⊔ f (k + 1)) (f m) :=
          (disjoint_sup_left (a := s k) (b := f (k + 1)) (c := f m)).2
            ⟨hdisj_sk, hdisj_fk⟩
        simpa [s_succ] using hsup
  have hs_disj : ∀ k, Disjoint (s k) (f (k + 1)) := by
    intro k
    exact hs_disj_future k (k + 1) (Nat.lt_succ_self _)

  -- Finite additivity on the partial suprema.
  have hs_finite_add :
      ∀ n, μ.val (s n) = (Finset.range (n + 1)).sum (fun i => μ.val (f i)) := by
    intro n
    induction n with
    | zero =>
        simp only [s_zero, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    | succ k hk =>
        have hdisj : Disjoint (s k) (f (k + 1)) := hs_disj k
        calc
          μ.val (s (k + 1))
              = μ.val (s k ⊔ f (k + 1)) := by simp [s_succ]
          _ = μ.val (s k) + μ.val (f (k + 1)) := by
                simpa [unnormalized_combine_is_add μ cox, s_succ] using
                  cox.combine_val (a := s k) (b := f (k + 1)) hdisj
          _ = (Finset.range (k + 1)).sum (fun i => μ.val (f i)) + μ.val (f (k + 1)) := by
                simp [hk]
          _ = (Finset.range (k + 2)).sum (fun i => μ.val (f i)) := by
                simp only [Finset.sum_range_succ]

  -- Continuity identifies the supremum of values with the value of the supremum.
  have hμ_mono : Monotone (μ.val ∘ s) := μ.monotone.comp hs_mono
  have hlimit_eq : μ.val (⨆ n, s n) = ⨆ n, μ.val (s n) :=
    tendsto_nhds_unique (continuity s hs_mono) (tendsto_atTop_iSup hμ_mono)

  -- Identify the limit of finite sums with the infinite sum.
  let b : ℕ → ℝ≥0∞ := fun n => (Finset.range n).sum (fun i => μ.val (f i))
  have hb_step : ∀ n, b n ≤ b (n + 1) := by
    intro n
    have hb : b (n + 1) = b n + μ.val (f n) := by
      simp only [b, Finset.sum_range_succ]
    rw [hb]
    exact le_self_add
  have hb_mono : Monotone b := monotone_nat_of_le_succ hb_step
  have hb_shift : (⨆ n, b (n + 1)) = ⨆ n, b n := by
    apply le_antisymm
    · refine iSup_le ?_
      intro n
      exact le_iSup_of_le (n + 1) le_rfl
    · refine iSup_le ?_
      intro n
      exact le_trans (hb_mono (Nat.le_succ n)) (le_iSup_of_le n le_rfl)
  have htsum :
      (∑' i, μ.val (f i)) = ⨆ n, b (n + 1) := by
    have hbase := ENNReal.tsum_eq_iSup_nat (f := fun n => μ.val (f n))
    calc
      (∑' i, μ.val (f i)) = ⨆ n, b n := by simpa [b]
      _ = ⨆ n, b (n + 1) := hb_shift.symm

  -- Assemble the chain of equalities.
  calc
    μ.val (⨆ i, f i)
        = μ.val (⨆ n, s n) := by simp only [hs_sup]
    _ = ⨆ n, μ.val (s n) := hlimit_eq
    _ = ⨆ n, b (n + 1) := by
          classical
          refine iSup_congr fun n => ?_
          simpa [b] using hs_finite_add n
    _ = ∑' i, μ.val (f i) := htsum.symm

/-! ## Constructing a Mathlib measure from a symmetric valuation -/

/-- Build a `Measure` from an un-normalized valuation satisfying σ-additivity. -/
def toMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : UnnormalizedValuation (Set Ω))
    (cox : UnnormalizedCox (Set Ω) μ)
    (h_sigma : ∀ (f : ℕ → Set Ω), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
               μ.val (⨆ i, f i) = ∑' i, μ.val (f i)) :
    Measure Ω := by
  classical
  -- Mark `cox` as used to avoid linter warnings.
  have _ := cox.combine_comm 0 0
  refine Measure.ofMeasurable (m := fun s _ => μ.val s) ?m0 ?mUnion
  · simpa using μ.val_bot
  · intro f hf hpair
    -- `h_sigma` already provides σ-additivity on pairwise disjoint families.
    have hdisj : ∀ i j, i ≠ j → Disjoint (f i) (f j) := by
      intro i j hij
      exact hpair hij
    simpa using h_sigma f hdisj

@[simp]
theorem toMeasure_apply {Ω : Type*} [MeasurableSpace Ω]
    (μ : UnnormalizedValuation (Set Ω))
    (cox : UnnormalizedCox (Set Ω) μ)
    (h_sigma : ∀ (f : ℕ → Set Ω), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
               μ.val (⨆ i, f i) = ∑' i, μ.val (f i))
    {s : Set Ω} (hs : MeasurableSet s) :
    toMeasure μ cox h_sigma s = μ.val s := by
  -- Mark `cox` as used to avoid linter warnings.
  have _ := cox.combine_comm 0 0
  simp [toMeasure, Measure.ofMeasurable_apply, hs]

/-! ## Translation invariance and Haar measure -/

/-- Translation invariance of an un-normalized valuation on sets of a group. -/
structure TranslationInvariant (G : Type*) [Group G] [TopologicalSpace G]
    (μ : UnnormalizedValuation (Set G)) where
  invariant : ∀ (g : G) (A : Set G), μ.val (g • A) = μ.val A

/-- A translation-invariant symmetric valuation yields a left-invariant measure.
TODO: upgrade conclusion to `IsHaarMeasure` once the predicate is wired up in this build. -/
theorem translation_invariant_is_haar
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : UnnormalizedValuation (Set G))
    (cox : UnnormalizedCox (Set G) μ)
    (h_sigma : ∀ (f : ℕ → Set G), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
               μ.val (⨆ i, f i) = ∑' i, μ.val (f i))
    (h_trans : TranslationInvariant G μ) :
    MeasureTheory.Measure.IsMulLeftInvariant (toMeasure μ cox h_sigma) := by
  classical
  let ν := toMeasure (μ := μ) (cox := cox) (h_sigma := h_sigma)
  refine ⟨?_⟩
  intro g
  -- Compare the measures on measurable sets via `Measure.ext`.
  refine Measure.ext (fun A hA => ?_) 
  have hpre : (fun x => g * x) ⁻¹' A = g⁻¹ • A := by
    ext x
    constructor
    · intro hx
      refine ⟨g * x, hx, ?_⟩
      simp
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  have hmeas_mul : Measurable fun x => g * x := by
    have hcont : Continuous fun x => g * x := by
      exact continuous_const.mul continuous_id
    simpa using hcont.measurable
  have hpre_meas : MeasurableSet ((fun x => g * x) ⁻¹' A) := hA.preimage hmeas_mul
  have hmeas_smul : MeasurableSet (g⁻¹ • A) := by
    simpa [hpre] using hpre_meas
  have hν_pre : ν ((fun x => g * x) ⁻¹' A) = μ.val (g⁻¹ • A) := by
    have := toMeasure_apply (μ := μ) (cox := cox) (h_sigma := h_sigma)
      (s := (fun x => g * x) ⁻¹' A) (hs := hpre_meas)
    simpa [ν, hpre] using this
  have hν_smul : ν (g⁻¹ • A) = μ.val (g⁻¹ • A) := by
    have := toMeasure_apply (μ := μ) (cox := cox) (h_sigma := h_sigma)
      (s := g⁻¹ • A) (hs := hmeas_smul)
    simpa [ν] using this
  have hν_A : ν A = μ.val A := by
    have := toMeasure_apply (μ := μ) (cox := cox) (h_sigma := h_sigma)
      (s := A) (hs := hA)
    simpa [ν] using this
  have hinv : μ.val (g⁻¹ • A) = μ.val A := h_trans.invariant g⁻¹ A
  calc
    Measure.map (fun x => g * x) ν A
        = ν ((fun x => g * x) ⁻¹' A) := Measure.map_apply hmeas_mul hA
    _ = μ.val (g⁻¹ • A) := hν_pre
    _ = μ.val A := hinv
    _ = ν A := hν_A.symm

end Mettapedia.MeasureTheory
