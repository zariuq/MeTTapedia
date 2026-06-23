import Mettapedia.ProbabilityTheory.HigherOrderProbability.Basic
import Mettapedia.Logic.DeFinetti
import Mettapedia.ProbabilityTheory.FiniteMeasureSupport
import Exchangeability.Core
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# De Finetti as Kyburg Flattening

This file packages the Bernoulli-mixture model from `Mettapedia.Logic.DeFinetti` as an instance of
Kyburg's higher-order probability structure (`ParametrizedDistribution`).

The key theorem is the singleton-level identification:

`flatten(pd_M n) {xs} = ENNReal.ofReal (M.prob xs)`.

This is the precise "De Finetti is Kyburg" bridge needed by the higher-order PLN story.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability

open scoped BigOperators ENNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory
open Mettapedia.ProbabilityTheory.FiniteMeasureSupport

namespace DeFinettiConnection

open Mettapedia.Logic.DeFinetti
open Mettapedia.Logic.Exchangeability

/-! ## Parameter space and mixing measure -/

abbrev Theta : Type := Set.Icc (0 : ℝ) 1

lemma measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1) := by
  simp [isClosed_Icc.measurableSet]

@[simp] lemma Theta.coe_mk (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((⟨x, hx⟩ : Theta) : ℝ) = x := rfl

/-- Pull a mixing measure supported on `[0,1]` back to the subtype `Theta = Icc 0 1`. -/
def mixingMeasureTheta (M : BernoulliMixture) : Measure Theta :=
  M.mixingMeasure.comap (fun θ : Theta => (θ : ℝ))

instance mixingMeasureTheta_isProbability (M : BernoulliMixture) :
    IsProbabilityMeasure (mixingMeasureTheta M) := by
  classical
  haveI : IsProbabilityMeasure M.mixingMeasure := M.isProbability
  -- Evaluate on `univ` by rewriting `comap` along the subtype coercion.
  have hIcc :
      mixingMeasureTheta M Set.univ = M.mixingMeasure (Set.Icc (0 : ℝ) 1) := by
    -- `comap_subtype_coe_apply` identifies the pullback with the image set.
    have hcomap :
        (mixingMeasureTheta M) Set.univ =
          M.mixingMeasure (Subtype.val '' (Set.univ : Set (Set.Icc (0 : ℝ) 1))) :=
      comap_subtype_coe_apply (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc
        (μ := M.mixingMeasure) (t := (Set.univ : Set (Set.Icc (0 : ℝ) 1)))
    rw [hcomap]
    congr 1
    rw [Subtype.coe_image_univ]
  -- Since `M.mixingMeasure` is a probability measure supported on `Icc 0 1`,
  -- the measure of `Icc 0 1` is `1`.
  have hIcc_one : M.mixingMeasure (Set.Icc (0 : ℝ) 1) = 1 := by
    have hIcc_eq_univ : M.mixingMeasure (Set.Icc (0 : ℝ) 1) = M.mixingMeasure Set.univ := by
      simpa using
        (MeasureTheory.measure_of_measure_compl_eq_zero (μ := M.mixingMeasure) (s := Set.Icc (0 : ℝ) 1)
          M.support_unit)
    simpa [measure_univ] using hIcc_eq_univ
  -- Finish.
  refine ⟨?_⟩
  simp [hIcc, hIcc_one]

/-- If two Bernoulli mixtures induce the same pulled-back measure on
`Theta = [0,1]`, then their original mixing measures on `ℝ` are equal. -/
theorem mixingMeasure_eq_of_mixingMeasureTheta_eq
    (M1 M2 : BernoulliMixture)
    (hΘ : mixingMeasureTheta M1 = mixingMeasureTheta M2) :
    M1.mixingMeasure = M2.mixingMeasure := by
  ext t ht
  have hμ1_diff0 : M1.mixingMeasure (t \ Set.Icc (0 : ℝ) 1) = 0 := by
    refine le_antisymm ?_ (zero_le)
    calc
      M1.mixingMeasure (t \ Set.Icc (0 : ℝ) 1) ≤ M1.mixingMeasure (Set.Icc (0 : ℝ) 1)ᶜ := by
        refine measure_mono ?_
        intro x hx
        exact hx.2
      _ = 0 := M1.support_unit
  have hμ2_diff0 : M2.mixingMeasure (t \ Set.Icc (0 : ℝ) 1) = 0 := by
    refine le_antisymm ?_ (zero_le)
    calc
      M2.mixingMeasure (t \ Set.Icc (0 : ℝ) 1) ≤ M2.mixingMeasure (Set.Icc (0 : ℝ) 1)ᶜ := by
        refine measure_mono ?_
        intro x hx
        exact hx.2
      _ = 0 := M2.support_unit
  have hμ1_inter : M1.mixingMeasure t = M1.mixingMeasure (t ∩ Set.Icc (0 : ℝ) 1) := by
    have hsplit :
        M1.mixingMeasure (t ∩ Set.Icc (0 : ℝ) 1) +
          M1.mixingMeasure (t \ Set.Icc (0 : ℝ) 1) =
        M1.mixingMeasure t :=
      measure_inter_add_diff t measurableSet_Icc
    simpa [hμ1_diff0] using hsplit.symm
  have hμ2_inter : M2.mixingMeasure t = M2.mixingMeasure (t ∩ Set.Icc (0 : ℝ) 1) := by
    have hsplit :
        M2.mixingMeasure (t ∩ Set.Icc (0 : ℝ) 1) +
          M2.mixingMeasure (t \ Set.Icc (0 : ℝ) 1) =
        M2.mixingMeasure t :=
      measure_inter_add_diff t measurableSet_Icc
    simpa [hμ2_diff0] using hsplit.symm
  have hμ1_comap :
      M1.mixingMeasure (t ∩ Set.Icc (0 : ℝ) 1) =
        mixingMeasureTheta M1 ((Subtype.val) ⁻¹' t) := by
    symm
    calc
      mixingMeasureTheta M1 ((Subtype.val) ⁻¹' t)
          = M1.mixingMeasure ((Subtype.val) '' (((Subtype.val) ⁻¹' t) : Set Theta)) := by
              simpa [mixingMeasureTheta, Theta, measurableSet_Icc] using
                (comap_subtype_coe_apply (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc
                  (μ := M1.mixingMeasure) (t := ((Subtype.val) ⁻¹' t)))
      _ = M1.mixingMeasure (t ∩ Set.Icc (0 : ℝ) 1) := by
            simp [Set.image_preimage_eq_inter_range, Set.Icc]
  have hμ2_comap :
      M2.mixingMeasure (t ∩ Set.Icc (0 : ℝ) 1) =
        mixingMeasureTheta M2 ((Subtype.val) ⁻¹' t) := by
    symm
    calc
      mixingMeasureTheta M2 ((Subtype.val) ⁻¹' t)
          = M2.mixingMeasure ((Subtype.val) '' (((Subtype.val) ⁻¹' t) : Set Theta)) := by
              simpa [mixingMeasureTheta, Theta, measurableSet_Icc] using
                (comap_subtype_coe_apply (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc
                  (μ := M2.mixingMeasure) (t := ((Subtype.val) ⁻¹' t)))
      _ = M2.mixingMeasure (t ∩ Set.Icc (0 : ℝ) 1) := by
            simp [Set.image_preimage_eq_inter_range, Set.Icc]
  calc
    M1.mixingMeasure t = M1.mixingMeasure (t ∩ Set.Icc (0 : ℝ) 1) := hμ1_inter
    _ = mixingMeasureTheta M1 ((Subtype.val) ⁻¹' t) := hμ1_comap
    _ = mixingMeasureTheta M2 ((Subtype.val) ⁻¹' t) := by simp [hΘ]
    _ = M2.mixingMeasure (t ∩ Set.Icc (0 : ℝ) 1) := hμ2_comap.symm
    _ = M2.mixingMeasure t := hμ2_inter.symm

/-- A Bernoulli mixture is determined by its pulled-back mixing measure on
`Theta = [0,1]`. -/
theorem bernoulliMixture_ext_of_mixingMeasureTheta_eq
    (M1 M2 : BernoulliMixture)
    (hΘ : mixingMeasureTheta M1 = mixingMeasureTheta M2) :
    M1 = M2 := by
  have hmix : M1.mixingMeasure = M2.mixingMeasure :=
    mixingMeasure_eq_of_mixingMeasureTheta_eq M1 M2 hΘ
  cases M1 with
  | mk μ1 p1 s1 =>
    cases M2 with
    | mk μ2 p2 s2 =>
      change (BernoulliMixture.mk μ1 p1 s1 = BernoulliMixture.mk μ2 p2 s2)
      have hμ : μ1 = μ2 := by simpa using hmix
      cases hμ
      simp

/-! ## Bernoulli product kernel as a Markov kernel -/

section Kernel

variable {n : ℕ}

private lemma theta_nonneg (θ : Theta) : 0 ≤ (θ : ℝ) := θ.2.1
private lemma theta_le_one (θ : Theta) : (θ : ℝ) ≤ 1 := θ.2.2
private lemma one_sub_theta_nonneg (θ : Theta) : 0 ≤ 1 - (θ : ℝ) :=
  sub_nonneg.2 (theta_le_one θ)

private lemma bernoulliPMF_nonneg (θ : Theta) (b : Bool) :
    0 ≤ bernoulliPMF (θ : ℝ) b := by
  cases b with
  | false =>
      simpa [bernoulliPMF] using one_sub_theta_nonneg (θ := θ)
  | true =>
      simpa [bernoulliPMF] using theta_nonneg (θ := θ)

/-- The `ENNReal` weight of a word `xs` under a parameter `θ`. -/
def weight (θ : Theta) (xs : Fin n → Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs)

private lemma weight_cons (θ : Theta) (b : Bool) (xs : Fin n → Bool) :
    weight (n := n + 1) θ (Fin.cons b xs) =
      ENNReal.ofReal (bernoulliPMF (θ : ℝ) b) * weight (n := n) θ xs := by
  classical
  -- Split the product on `Fin (n+1)` into head and tail.
  have hprod :
      bernoulliProductPMF (θ : ℝ) (Fin.cons b xs) =
        bernoulliPMF (θ : ℝ) b * bernoulliProductPMF (θ : ℝ) xs := by
    unfold bernoulliProductPMF
    -- `Fin.prod_univ_succ` isolates the `0`-th coordinate.
    simpa using
      (Fin.prod_univ_succ (n := n)
        (f := fun i : Fin (n + 1) =>
          bernoulliPMF (θ : ℝ) ((Fin.cons b xs : Fin (n + 1) → Bool) i)))
  -- Move `ENNReal.ofReal` across multiplication; the head factor is nonnegative on `Theta`.
  have hnonneg : 0 ≤ bernoulliPMF (θ : ℝ) b := bernoulliPMF_nonneg (θ := θ) b
  simp [weight, hprod, ENNReal.ofReal_mul hnonneg]

private lemma ofReal_bernoulliPMF_add (θ : Theta) :
    ENNReal.ofReal (bernoulliPMF (θ : ℝ) true) + ENNReal.ofReal (bernoulliPMF (θ : ℝ) false) = 1 := by
  have hθ : 0 ≤ (θ : ℝ) := theta_nonneg θ
  have h1θ : 0 ≤ 1 - (θ : ℝ) := one_sub_theta_nonneg θ
  -- `bernoulliPMF θ true = θ`, `bernoulliPMF θ false = 1-θ`.
  have hsum : (θ : ℝ) + (1 - (θ : ℝ)) = (1 : ℝ) := by ring
  have : ENNReal.ofReal (θ : ℝ) + ENNReal.ofReal (1 - (θ : ℝ)) = 1 := by
    -- Rewrite the sum as `ofReal (θ + (1-θ))` and use `hsum`.
    calc
      ENNReal.ofReal (θ : ℝ) + ENNReal.ofReal (1 - (θ : ℝ))
          = ENNReal.ofReal ((θ : ℝ) + (1 - (θ : ℝ))) := by
              simpa using (ENNReal.ofReal_add hθ h1θ).symm
      _ = 1 := by simp [hsum]
  simpa [bernoulliPMF] using this

private lemma sum_weight_eq_one : ∀ (n : ℕ) (θ : Theta), (∑ xs : Fin n → Bool, weight (n := n) θ xs) = 1
  | 0, θ => by
      classical
      -- Only one word on `Fin 0`.
      simp [weight, bernoulliProductPMF]
  | Nat.succ n, θ => by
      classical
      -- Rewrite the sum over words using `Fin.consEquiv` (head bit + tail).
      -- `Fin.consEquiv` has type `Bool × (Fin n → Bool) ≃ (Fin (n+1) → Bool)`.
      have hs :
          (∑ xs : Fin (n + 1) → Bool, weight (n := n + 1) θ xs) =
            ∑ p : Bool × (Fin n → Bool), weight (n := n + 1) θ (Fin.cons p.1 p.2) := by
        -- Sum over an equivalence.
        simpa using
          (Fintype.sum_equiv (Fin.consEquiv (n := n) (α := fun _ : Fin (n + 1) => Bool))
              (fun p : Bool × (Fin n → Bool) => weight (n := n + 1) θ (Fin.cons p.1 p.2))
              (fun xs : Fin (n + 1) → Bool => weight (n := n + 1) θ xs)
              (fun _p => rfl)).symm
      -- Now split the product sum into head/tail.
      rw [hs]
      -- Turn the sum over pairs into an iterated sum.
      simp only [Fintype.sum_prod_type]
      -- Use the multiplicative factorization `weight_cons`.
      have htrue :
          (∑ xs : Fin n → Bool, weight (n := n + 1) θ (Fin.cons true xs)) =
            ENNReal.ofReal (bernoulliPMF (θ : ℝ) true) * (∑ xs : Fin n → Bool, weight (n := n) θ xs) := by
        -- Factor out the constant multiplier.
        have :
            (∑ xs : Fin n → Bool,
                ENNReal.ofReal (bernoulliPMF (θ : ℝ) true) * weight (n := n) θ xs) =
              ENNReal.ofReal (bernoulliPMF (θ : ℝ) true) * (∑ xs : Fin n → Bool, weight (n := n) θ xs) := by
          -- `∑ xs, ...` is a `Finset.univ` sum; use `Finset.mul_sum`.
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin n → Bool)))
              (f := fun xs : Fin n → Bool => weight (n := n) θ xs)
              (a := ENNReal.ofReal (bernoulliPMF (θ : ℝ) true))).symm
        simp [weight_cons, this]
      have hfalse :
          (∑ xs : Fin n → Bool, weight (n := n + 1) θ (Fin.cons false xs)) =
            ENNReal.ofReal (bernoulliPMF (θ : ℝ) false) * (∑ xs : Fin n → Bool, weight (n := n) θ xs) := by
        have :
            (∑ xs : Fin n → Bool,
                ENNReal.ofReal (bernoulliPMF (θ : ℝ) false) * weight (n := n) θ xs) =
              ENNReal.ofReal (bernoulliPMF (θ : ℝ) false) * (∑ xs : Fin n → Bool, weight (n := n) θ xs) := by
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin n → Bool)))
              (f := fun xs : Fin n → Bool => weight (n := n) θ xs)
              (a := ENNReal.ofReal (bernoulliPMF (θ : ℝ) false))).symm
        simp [weight_cons, this]
      -- Finish using the induction hypothesis and `ofReal_bernoulliPMF_add`.
      have ih : (∑ xs : Fin n → Bool, weight (n := n) θ xs) = 1 := sum_weight_eq_one n θ
      -- Combine the two branches (true/false head bit).
      calc
        (∑ b : Bool, ∑ xs : Fin n → Bool, weight (n := n + 1) θ (Fin.cons b xs))
            = (∑ xs : Fin n → Bool, weight (n := n + 1) θ (Fin.cons true xs)) +
                (∑ xs : Fin n → Bool, weight (n := n + 1) θ (Fin.cons false xs)) := by
                  -- `Bool` sum is two terms.
                  simp
        _ = (ENNReal.ofReal (bernoulliPMF (θ : ℝ) true) +
              ENNReal.ofReal (bernoulliPMF (θ : ℝ) false)) * (∑ xs : Fin n → Bool, weight (n := n) θ xs) := by
              -- Factor out the shared suffix-weight sum.
              simpa [htrue, hfalse] using
                (add_mul (ENNReal.ofReal (bernoulliPMF (θ : ℝ) true))
                    (ENNReal.ofReal (bernoulliPMF (θ : ℝ) false))
                    (∑ xs : Fin n → Bool, weight (n := n) θ xs)).symm
        _ = 1 := by
              simp [ofReal_bernoulliPMF_add (θ := θ), ih]

/-- The `PMF` on `Fin n → Bool` induced by `theta`. -/
def pmf (θ : Theta) : PMF (Fin n → Bool) :=
  PMF.ofFintype (weight (n := n) θ) (sum_weight_eq_one (n := n) θ)

@[simp] lemma pmf_apply (θ : Theta) (xs : Fin n → Bool) :
    pmf (n := n) θ xs = weight (n := n) θ xs := by
  simp [pmf]

@[simp] lemma pmf_toMeasure_apply_singleton (θ : Theta) (xs : Fin n → Bool) :
    (pmf (n := n) θ).toMeasure {xs} = weight (n := n) θ xs := by
  simp [pmf]

/-- Appending Boolean prefixes factorizes the fixed-parameter Bernoulli-product
weights into prefix and suffix weights. -/
theorem weight_append (θ : Theta) {m n : ℕ}
    (xs : Fin m → Bool) (ys : Fin n → Bool) :
    weight (n := m + n) θ (Fin.append xs ys) =
      weight (n := m) θ xs * weight (n := n) θ ys := by
  have hxs : 0 ≤ bernoulliProductPMF (θ : ℝ) xs := by
    rw [bernoulliProductPMF_eq_power]
    exact mul_nonneg (pow_nonneg (theta_nonneg θ) _) (pow_nonneg (one_sub_theta_nonneg θ) _)
  have hsplit :
      bernoulliProductPMF (θ : ℝ) (Fin.append xs ys) =
        bernoulliProductPMF (θ : ℝ) xs * bernoulliProductPMF (θ : ℝ) ys := by
    rw [bernoulliProductPMF_eq_power, bernoulliProductPMF_eq_power,
      bernoulliProductPMF_eq_power, countTrue_append_fin, countFalse_append_fin,
      pow_add, pow_add]
    ring
  rw [weight, weight, weight, hsplit, ENNReal.ofReal_mul hxs]

/-- Truncating a fixed-parameter Bernoulli-product law to a shorter prefix
recovers the shorter fixed-parameter law exactly. -/
theorem pmf_map_takePrefix_eq (θ : Theta) {m n : ℕ} (hmn : m ≤ n) :
    PMF.map (Exchangeability.takePrefix (α := Bool) hmn) (pmf (n := n) θ) =
      pmf (n := m) θ := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have h_eq : hmn = Nat.le_add_right m d := by
    apply Subsingleton.elim
  cases h_eq
  ext xs
  rw [PMF.map_apply, tsum_fintype]
  let g : (Fin (m + d) → Bool) → ℝ≥0∞ := fun ys =>
    if xs = Exchangeability.takePrefix (α := Bool) (Nat.le_add_right m d) ys
    then pmf (n := m + d) θ ys else 0
  have hg :
      (∑ b : Fin (m + d) → Bool,
        if xs = Exchangeability.takePrefix (α := Bool) (Nat.le_add_right m d) b
        then pmf (n := m + d) θ b else 0) =
      ∑ ys : Fin (m + d) → Bool, g ys := by
    rfl
  have hsum :
      (∑ ys : Fin (m + d) → Bool, g ys) =
        ∑ p : (Fin m → Bool) × (Fin d → Bool), g (Fin.append p.1 p.2) := by
    simpa [g] using
      (Fintype.sum_equiv (Fin.appendEquiv (α := Bool) m d)
        (fun p : (Fin m → Bool) × (Fin d → Bool) => g (Fin.append p.1 p.2))
        g (fun _ => rfl)).symm
  have hinner :
      ∀ p : Fin m → Bool,
        (∑ q : Fin d → Bool, g (Fin.append p q)) =
          if xs = p then pmf (n := m) θ p else 0 := by
    intro p
    by_cases hxp : xs = p
    · rw [if_pos hxp]
      calc
        ∑ q : Fin d → Bool, g (Fin.append p q)
            = ∑ q : Fin d → Bool, pmf (n := m + d) θ (Fin.append p q) := by
                apply Finset.sum_congr rfl
                intro q _hq
                have hprefix :
                    Exchangeability.takePrefix (α := Bool) (Nat.le_add_right m d)
                        (Fin.append p q) = p := by
                  ext i
                  simp [Exchangeability.takePrefix]
                simp [g, hprefix, hxp]
        _ = ∑ q : Fin d → Bool,
              weight (n := m) θ p * weight (n := d) θ q := by
                apply Finset.sum_congr rfl
                intro q _hq
                rw [pmf_apply, weight_append]
        _ = weight (n := m) θ p * ∑ q : Fin d → Bool, weight (n := d) θ q := by
                simpa using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin d → Bool)))
                    (f := fun q : Fin d → Bool => weight (n := d) θ q)
                    (a := weight (n := m) θ p)).symm
        _ = weight (n := m) θ p := by simp [sum_weight_eq_one]
        _ = pmf (n := m) θ p := by rw [pmf_apply]
    · have hgzero : ∀ q : Fin d → Bool, g (Fin.append p q) = 0 := by
        intro q
        have hprefix :
            Exchangeability.takePrefix (α := Bool) (Nat.le_add_right m d)
                (Fin.append p q) = p := by
          ext i
          simp [Exchangeability.takePrefix]
        simp [g, hprefix, hxp]
      simp [hxp, hgzero]
  have houter :
      (∑ p : Fin m → Bool, if xs = p then pmf (n := m) θ p else 0) =
        pmf (n := m) θ xs := by
    rw [Finset.sum_eq_single xs]
    · simp
    · intro p _hp hpx
      have hneq : xs ≠ p := by
        intro h
        exact hpx h.symm
      simp [hneq]
    · intro hxs
      exact (hxs (Finset.mem_univ xs)).elim
  have hmain :
      (∑ ys : Fin (m + d) → Bool, g ys) = pmf (n := m) θ xs := by
    calc
      ∑ ys : Fin (m + d) → Bool, g ys
          = ∑ p : (Fin m → Bool) × (Fin d → Bool), g (Fin.append p.1 p.2) := hsum
      _ = ∑ p : Fin m → Bool, ∑ q : Fin d → Bool, g (Fin.append p q) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ p : Fin m → Bool, if xs = p then pmf (n := m) θ p else 0 := by
            apply Finset.sum_congr rfl
            intro p _hp
            exact hinner p
      _ = pmf (n := m) θ xs := houter
  simpa [g] using hmain

/-- The fixed-parameter Bernoulli-product measure truncates exactly to the
shorter fixed-parameter prefix measure. -/
theorem pmf_toMeasure_map_takePrefix_eq (θ : Theta) {m n : ℕ} (hmn : m ≤ n) :
    Measure.map (Exchangeability.takePrefix (α := Bool) hmn)
      ((pmf (n := n) θ).toMeasure) =
    (pmf (n := m) θ).toMeasure := by
  simpa [pmf_map_takePrefix_eq (θ := θ) hmn] using
    (PMF.toMeasure_map (f := Exchangeability.takePrefix (α := Bool) hmn)
      (p := pmf (n := n) θ)
      (hf := Exchangeability.takePrefix_measurable (α := Bool) hmn))

private lemma measurable_weight (xs : Fin n → Bool) :
    Measurable fun θ : Theta => weight (n := n) θ xs := by
  -- `bernoulliProductPMF` is a finite product of measurable functions.
  -- We use the closed form `θ^k * (1-θ)^(n-k)` for measurability.
  have hmeas : Measurable fun t : ℝ => bernoulliProductPMF t xs := by
    -- Use `bernoulliProductPMF_eq_power` and measurability of `pow` and subtraction.
    have : Measurable fun t : ℝ =>
        t ^ (countTrue xs) * (1 - t) ^ (countFalse xs) := by
      have hm1 : Measurable fun t : ℝ => t ^ (countTrue xs) := by
        simpa using (measurable_id.pow_const (countTrue xs))
      have hm2 : Measurable fun t : ℝ => (1 - t) ^ (countFalse xs) := by
        have : Measurable fun t : ℝ => 1 - t := measurable_const.sub measurable_id
        exact this.pow_const (countFalse xs)
      exact hm1.mul hm2
    simpa [bernoulliProductPMF_eq_power] using this
  -- Restrict to the subtype and apply `ENNReal.measurable_ofReal`.
  simpa [weight, Function.comp_def] using
    (ENNReal.measurable_ofReal.comp (hmeas.comp measurable_subtype_coe))

private lemma measurable_pmf_toMeasure_apply (s : Set (Fin n → Bool)) :
    Measurable fun θ : Theta => (pmf (n := n) θ).toMeasure s := by
  classical
  -- On a fintype, `PMF.toMeasure` is computed by a finite sum.
  have hrewrite :
      (fun θ : Theta => (pmf (n := n) θ).toMeasure s) =
        fun θ : Theta => ∑ x : Fin n → Bool, (if x ∈ s then weight (n := n) θ x else 0) := by
    funext θ
    -- Rewrite `toMeasure s` as a `Fintype` sum of indicators.
    simp [PMF.toMeasure_apply_fintype, pmf_apply, weight, Set.indicator]
  -- Use measurability of finite sums.
  have hmeasTerm :
      ∀ x : Fin n → Bool, Measurable fun θ : Theta =>
        (if x ∈ s then weight (n := n) θ x else 0) := by
    intro x
    by_cases hx : x ∈ s
    · simp [hx, measurable_weight (n := n) (xs := x)]
    · simp [hx]
  -- Finish with the rewrite.
  classical
  -- Use `Finset.measurable_fun_sum` (from mathlib's measurability lemmas).
  have hsum :
      Measurable (fun θ : Theta =>
        ∑ x : Fin n → Bool, (if x ∈ s then weight (n := n) θ x else 0)) := by
    simpa using
      (Finset.measurable_fun_sum (s := (Finset.univ : Finset (Fin n → Bool)))
        (f := fun x : Fin n → Bool => fun θ : Theta => (if x ∈ s then weight (n := n) θ x else 0))
        (fun x _hx => hmeasTerm x))
  rw [hrewrite]
  exact hsum

/-- The Bernoulli product kernel on `Theta` at horizon `n`. -/
def kernel (n : ℕ) : ProbabilityTheory.Kernel Theta (Fin n → Bool) :=
  { toFun := fun θ => (pmf (n := n) θ).toMeasure
    measurable' := by
      -- Use the characterization of measurability of `Measure`-valued functions.
      refine MeasureTheory.Measure.measurable_of_measurable_coe _ ?_
      intro s _hs
      exact measurable_pmf_toMeasure_apply (n := n) s }

instance kernel_isMarkov (n : ℕ) : ProbabilityTheory.IsMarkovKernel (kernel (n := n)) := by
  classical
  refine ⟨fun θ => ?_⟩
  -- `PMF.toMeasure` is a probability measure.
  simpa [kernel] using (show IsProbabilityMeasure ((pmf (n := n) θ).toMeasure) from (by infer_instance))

end Kernel

/-! ## Packaging as a Kyburg parametrized distribution -/

/-- The Kyburg parametrized distribution corresponding to a Bernoulli mixture at horizon `n`. -/
def pd (M : BernoulliMixture) (n : ℕ) :
    ParametrizedDistribution Theta (Fin n → Bool) :=
  { kernel := kernel (n := n)
    kernel_isMarkov := kernel_isMarkov (n := n)
    mixingMeasure := mixingMeasureTheta M
    mixing_isProbability := inferInstance }

/-- Truncating the Kyburg/de Finetti flattened finite prefix law to a shorter
prefix recovers the shorter flattened law. -/
theorem flatten_map_takePrefix_eq (M : BernoulliMixture) {m n : ℕ} (hmn : m ≤ n) :
    Measure.map (Exchangeability.takePrefix (α := Bool) hmn)
      (ParametrizedDistribution.flatten (pd M n)) =
    ParametrizedDistribution.flatten (pd M m) := by
  ext s hs
  rw [Measure.map_apply (Exchangeability.takePrefix_measurable (α := Bool) hmn) hs]
  rw [ParametrizedDistribution.flatten_apply (pd M n)
    ((Exchangeability.takePrefix (α := Bool) hmn) ⁻¹' s)
    ((Exchangeability.takePrefix_measurable (α := Bool) hmn) hs)]
  rw [ParametrizedDistribution.flatten_apply (pd M m) s hs]
  apply lintegral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro θ
  have hθ := congrArg (fun μ : Measure (Fin m → Bool) => μ s)
    (pmf_toMeasure_map_takePrefix_eq (θ := θ) hmn)
  simpa [Measure.map_apply (Exchangeability.takePrefix_measurable (α := Bool) hmn) hs,
    pd, kernel] using hθ

/-! ## Main bridge lemma -/

theorem flatten_apply_singleton (M : BernoulliMixture) (n : ℕ) (xs : Fin n → Bool) :
    (ParametrizedDistribution.flatten (pd M n)) {xs}
      = ENNReal.ofReal (M.prob xs) := by
  classical
  -- Expand `flatten` as a `lintegral` of singleton masses.
  have hmeas : MeasurableSet ({xs} : Set (Fin n → Bool)) := by simp
  have hflat :
      (ParametrizedDistribution.flatten (pd M n)) {xs} =
        ∫⁻ θ : Theta, ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs) ∂mixingMeasureTheta M := by
    -- `flatten_apply` + the explicit kernel gives the desired integrand.
    simpa [pd, kernel, pmf_toMeasure_apply_singleton, pmf, weight] using
      (ParametrizedDistribution.flatten_apply (pd M n) {xs} hmeas)
  -- Reduce the subtype integral to a set-lintegral on `ℝ`.
  have hs : MeasurableSet (Set.Icc (0 : ℝ) 1) := measurableSet_Icc
  -- The integrand is `ENNReal.ofReal (bernoulliProductPMF θ xs)`.
  -- `lintegral_subtype_comap` converts `Θ`-integral with `comap` to a set integral.
  have hsub :
      (∫⁻ θ : Theta, ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs) ∂mixingMeasureTheta M) =
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bernoulliProductPMF t xs) ∂M.mixingMeasure := by
    -- `mixingMeasureTheta` is `comap (↑)`.
    simpa [mixingMeasureTheta, hs] using
      (MeasureTheory.lintegral_subtype_comap (μ := M.mixingMeasure) (s := Set.Icc (0 : ℝ) 1) hs
        (f := fun t : ℝ => ENNReal.ofReal (bernoulliProductPMF t xs)))
  -- Convert the set-lintegral of `ENNReal.ofReal` to `ENNReal.ofReal` of the Bochner integral.
  have hcont : Continuous fun t : ℝ => bernoulliProductPMF t xs := by
    -- Use the closed form and continuity of `pow`.
    have h1 : Continuous fun t : ℝ => t ^ (countTrue xs) := by
      simpa using (continuous_pow (countTrue xs))
    have h2 : Continuous fun t : ℝ => (1 - t) ^ (countFalse xs) := by
      have hsub : Continuous fun t : ℝ => 1 - t := continuous_const.sub continuous_id
      exact (continuous_pow (countFalse xs)).comp hsub
    have hmul : Continuous fun t : ℝ => t ^ (countTrue xs) * (1 - t) ^ (countFalse xs) :=
      h1.mul h2
    simpa [bernoulliProductPMF_eq_power] using hmul
  have hint :
      Integrable (fun t : ℝ => bernoulliProductPMF t xs)
        (M.mixingMeasure.restrict (Set.Icc (0 : ℝ) 1)) := by
    -- On a finite measure, a measurable function bounded by a constant is integrable.
    haveI : IsProbabilityMeasure M.mixingMeasure := M.isProbability
    have hs_finite : M.mixingMeasure (Set.Icc (0 : ℝ) 1) ≠ ∞ := by
      have hle : M.mixingMeasure (Set.Icc (0 : ℝ) 1) ≤ M.mixingMeasure Set.univ :=
        measure_mono (Set.subset_univ _)
      have huniv : M.mixingMeasure Set.univ = 1 := by
        simp
      -- `μ(Icc) ≤ 1 < ∞`.
      exact ne_of_lt (lt_of_le_of_lt (hle.trans_eq huniv) (by simp))
    have hmeas :
        AEStronglyMeasurable (fun t : ℝ => bernoulliProductPMF t xs) M.mixingMeasure :=
      hcont.measurable.aestronglyMeasurable
    have hbound :
        ∀ᵐ t ∂(M.mixingMeasure.restrict (Set.Icc (0 : ℝ) 1)),
          ‖bernoulliProductPMF t xs‖ ≤ (1 : ℝ) := by
      -- On `[0,1]` each factor is in `[0,1]`, so the product is in `[0,1]`.
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_
      intro t ht
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
      have hpow1 : t ^ (countTrue xs) ≤ 1 := by
        exact pow_le_one₀ (n := countTrue xs) ht0 ht1
      have hpow2 : (1 - t) ^ (countFalse xs) ≤ 1 := by
        have hle : 1 - t ≤ 1 := by linarith
        exact pow_le_one₀ (n := countFalse xs) h1t hle
      have hnonneg1 : 0 ≤ t ^ (countTrue xs) := pow_nonneg ht0 _
      have hnonneg2 : 0 ≤ (1 - t) ^ (countFalse xs) := pow_nonneg h1t _
      have hnonneg : 0 ≤ t ^ (countTrue xs) * (1 - t) ^ (countFalse xs) :=
        mul_nonneg hnonneg1 hnonneg2
      have hle1 : t ^ (countTrue xs) * (1 - t) ^ (countFalse xs) ≤ 1 := by
        -- Multiply the `≤ 1` bounds.
        have := mul_le_mul hpow1 hpow2 hnonneg2 (by linarith)
        simpa [one_mul] using this
      have habs : ‖t ^ (countTrue xs) * (1 - t) ^ (countFalse xs)‖ ≤ (1 : ℝ) := by
        simpa [Real.norm_of_nonneg hnonneg] using hle1
      simpa [bernoulliProductPMF_eq_power] using habs
    -- Now apply the bounded-integrable lemma.
    have hIntOn :
        IntegrableOn (fun t : ℝ => bernoulliProductPMF t xs) (Set.Icc (0 : ℝ) 1) M.mixingMeasure :=
      (Measure.integrableOn_of_bounded (μ := M.mixingMeasure) (s := Set.Icc (0 : ℝ) 1)
        hs_finite hmeas (M := (1 : ℝ)) hbound)
    simpa [IntegrableOn]
  have hnonneg :
      (0 : ℝ → ℝ) ≤ᵐ[(M.mixingMeasure.restrict (Set.Icc (0 : ℝ) 1))]
        (fun t : ℝ => bernoulliProductPMF t xs) := by
    -- On `Icc 0 1`, `bernoulliProductPMF` is nonnegative.
    refine (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_)
    intro t ht
    -- Use the closed form and nonnegativity of factors.
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
    -- Powers of nonneg are nonneg.
    have : 0 ≤ t ^ (countTrue xs) * (1 - t) ^ (countFalse xs) := by
      exact mul_nonneg (pow_nonneg ht0 _) (pow_nonneg h1t _)
    simpa [bernoulliProductPMF_eq_power] using this
  have hconv :
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bernoulliProductPMF t xs) ∂M.mixingMeasure =
        ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) 1, bernoulliProductPMF t xs ∂M.mixingMeasure) := by
    -- Apply `ofReal_integral_eq_lintegral_ofReal` to the restricted measure.
    -- Then rewrite the integrals-on-sets as integrals w.r.t. `restrict` (definitionally).
    have h :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := M.mixingMeasure.restrict (Set.Icc (0 : ℝ) 1))
        (f := fun t : ℝ => bernoulliProductPMF t xs) hint hnonneg)
    simpa using h.symm
  -- Put everything together.
  calc
    (ParametrizedDistribution.flatten (pd M n)) {xs}
        = ∫⁻ θ : Theta, ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs) ∂mixingMeasureTheta M := hflat
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bernoulliProductPMF t xs) ∂M.mixingMeasure := hsub
    _ = ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) 1, bernoulliProductPMF t xs ∂M.mixingMeasure) := hconv
    _ = ENNReal.ofReal (M.prob xs) := by simp [BernoulliMixture.prob]

/-! ## Finite-prefix probability laws -/

/-- Bernoulli-mixture finite-prefix probabilities are nonnegative.  The proof is
the analytic integral fact: on the support interval `[0,1]`, every Bernoulli
product factor is nonnegative. -/
theorem bernoulliMixture_prob_nonneg
    (M : BernoulliMixture) (n : ℕ) (xs : Fin n → Bool) :
    0 ≤ M.prob xs := by
  unfold BernoulliMixture.prob
  have hnonneg :
      (0 : ℝ → ℝ) ≤ᵐ[(M.mixingMeasure.restrict (Set.Icc (0 : ℝ) 1))]
        (fun t : ℝ => bernoulliProductPMF t xs) := by
    refine (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_)
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
    have : 0 ≤ t ^ (countTrue xs) * (1 - t) ^ (countFalse xs) := by
      exact mul_nonneg (pow_nonneg ht0 _) (pow_nonneg h1t _)
    simpa [bernoulliProductPMF_eq_power] using this
  exact integral_nonneg_of_ae hnonneg

/-- Bernoulli-mixture finite-prefix probabilities sum to one.  This packages
the finite product normalization from `pmf`/`sum_weight_eq_one` through
Kyburg flattening: the flattened measure is a probability measure, and finite
singletons partition the prefix space. -/
theorem bernoulliMixture_prob_total
    (M : BernoulliMixture) (n : ℕ) :
    ∑ xs : (Fin n → Bool), M.prob xs = 1 := by
  classical
  let ν : Measure (Fin n → Bool) := ParametrizedDistribution.flatten (pd M n)
  have hνuniv : ν Set.univ = 1 := by
    haveI : IsProbabilityMeasure ν := by
      dsimp [ν]
      infer_instance
    simp
  have hsumMass :
      ν Set.univ = ∑ xs : (Fin n → Bool), ν ({xs} : Set (Fin n → Bool)) :=
    finiteMeasure_univ_eq_sum_singletons ν
  have hsumENN : ∑ xs : (Fin n → Bool), ENNReal.ofReal (M.prob xs) = 1 := by
    calc
      ∑ xs : (Fin n → Bool), ENNReal.ofReal (M.prob xs)
          = ∑ xs : (Fin n → Bool), ν ({xs} : Set (Fin n → Bool)) := by
            apply Finset.sum_congr rfl
            intro xs _hxs
            exact (flatten_apply_singleton M n xs).symm
      _ = ν Set.univ := hsumMass.symm
      _ = 1 := hνuniv
  have hOfRealSum :
      ENNReal.ofReal (∑ xs : (Fin n → Bool), M.prob xs) = 1 := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · exact hsumENN
    · intro xs _hxs
      exact bernoulliMixture_prob_nonneg M n xs
  have hsumNonneg : 0 ≤ ∑ xs : (Fin n → Bool), M.prob xs := by
    exact Finset.sum_nonneg fun xs _hxs => bernoulliMixture_prob_nonneg M n xs
  have hReal := congrArg ENNReal.toReal hOfRealSum
  simpa [ENNReal.toReal_ofReal hsumNonneg] using hReal

end DeFinettiConnection

end Mettapedia.ProbabilityTheory.HigherOrderProbability
