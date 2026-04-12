import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCore
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence

/-!
# Counterexample: Moment Equality Does NOT Imply A.E. Equality

The claim "if f, g : Ω → ENNReal with f,g ≤ 1 and ∫⁻ f^m dμ = ∫⁻ g^m dμ
for all m ≥ 1, then f = g a.e. μ" is FALSE.

Counterexample: Ω = Bool, μ = (1/2)•δ_false + (1/2)•δ_true.
  f(false) = 0, f(true) = 1
  g(false) = 1, g(true) = 0
All moments agree (both equal 1/2), but f ≠ g everywhere.

This refutes the "L2 trick" approach to kernel uniqueness that was
attempted in an earlier version of this file.
-/

open MeasureTheory

noncomputable section

namespace Mettapedia.Logic.MomentCounterexample

private def μ : Measure Bool :=
  (1/2 : ENNReal) • Measure.dirac false + (1/2 : ENNReal) • Measure.dirac true

private def f : Bool → ENNReal := fun b => if b then 1 else 0
private def g : Bool → ENNReal := fun b => if b then 0 else 1

private lemma f_le : ∀ ω, f ω ≤ 1 := by intro ω; simp [f]; split <;> norm_num
private lemma g_le : ∀ ω, g ω ≤ 1 := by intro ω; simp [g]; split <;> norm_num

private lemma lintegral_pow_eq (m : ℕ) (hm : m ≥ 1) :
    ∫⁻ ω, (f ω) ^ m ∂μ = ∫⁻ ω, (g ω) ^ m ∂μ := by
  simp only [μ, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
  simp only [f, g, Bool.false_eq_true, ite_false, ite_true,
    one_pow, zero_pow (by omega : m ≠ 0)]
  simp

private lemma f_ne_g_everywhere : ∀ ω : Bool, f ω ≠ g ω := by
  intro ω; cases ω <;> simp [f, g]

/-- The moment-uniqueness claim is FALSE: equal moments does not give a.e. equality. -/
theorem moment_uniqueness_is_false :
    ¬(∀ {Ω : Type} [MeasurableSpace Ω] (μ_arg : Measure Ω) [SigmaFinite μ_arg]
        (f g : Ω → ENNReal),
        Measurable f → Measurable g →
        (∀ ω, f ω ≤ 1) → (∀ ω, g ω ≤ 1) →
        (∀ m : ℕ, m ≥ 1 → ∫⁻ ω, (f ω) ^ m ∂μ_arg = ∫⁻ ω, (g ω) ^ m ∂μ_arg) →
        f =ᵐ[μ_arg] g) := by
  intro h
  haveI : IsFiniteMeasure μ := by
    constructor; simp only [μ, Measure.coe_add, Pi.add_apply, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _)]; norm_num
  have hae := h μ f g (measurable_of_finite _) (measurable_of_finite _)
    f_le g_le lintegral_pow_eq
  -- hae : f =ᵐ[μ] g. Extract: μ {ω | f ω ≠ g ω} = 0
  have hzero : μ {ω | f ω ≠ g ω} = 0 := by
    rw [show {ω : Bool | f ω ≠ g ω} = {ω | ¬(f ω = g ω)} from rfl]
    exact ae_iff.mp hae
  -- But f ≠ g everywhere, so {ω | f ω ≠ g ω} = Set.univ
  rw [show {ω : Bool | f ω ≠ g ω} = Set.univ from by
    ext ω; simp [f_ne_g_everywhere ω]] at hzero
  -- But μ is nonzero: contradiction
  have hpos : μ Set.univ > 0 := by
    simp only [μ, Measure.coe_add, Pi.add_apply, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _)]
    norm_num
  exact absurd hzero (ne_of_gt hpos)

end Mettapedia.Logic.MomentCounterexample

/-!
# Counterexample: ConditionallyIID Bind Identity Does NOT Determine Kernel

The ConditionallyIID definition uses `μ.bind(pi(ν))` — a MARGINAL identity.
Two different kernels can produce the same marginals (equal in distribution ≠ equal a.e.).

Counterexample: Ω = Bool, X_n(ω) = ω (constant sequence).
  μ = (1/2)•δ_false + (1/2)•δ_true (uniform on Bool).
  ν₁(false) = δ_false, ν₁(true) = δ_true  — the "correct" kernel
  ν₂(false) = δ_true,  ν₂(true) = δ_false  — the "swapped" kernel

Both satisfy μ.bind(pi(ν)) = μ.map(proj) for all m, sel, but ν₁ ≠ ν₂ everywhere.

The de Finetti kernel IS unique, but its uniqueness comes from the conditional
expectation characterization (directing_measure_integral_eq_condExp), NOT from
the bind identity alone.
-/

namespace Mettapedia.Logic.BindKernelCounterexample

open MeasureTheory Exchangeability

noncomputable section

private def μ_B : Measure Bool :=
  (1/2 : ENNReal) • Measure.dirac false + (1/2 : ENNReal) • Measure.dirac true

private def X_const : ℕ → Bool → Bool := fun _ ω => ω

private def ν₁ : Bool → Measure Bool := fun ω => Measure.dirac ω
private def ν₂ : Bool → Measure Bool := fun ω => Measure.dirac (!ω)

/-- ν₁ and ν₂ differ at every point. -/
theorem ν_ne_everywhere : ∀ ω : Bool, ν₁ ω ≠ ν₂ ω := by
  intro ω habs
  have : ν₁ ω {ω} = ν₂ ω {ω} := by rw [habs]
  cases ω <;> simp [ν₁, ν₂, Set.mem_singleton_iff] at this

/-- Measure.bind is NOT injective in the kernel argument:
two different kernels can produce the same bind with a symmetric base measure.
This is the core reason why the ConditionallyIID bind identity
does not uniquely determine the de Finetti kernel. -/
theorem bind_not_injective_in_kernel :
    ∃ (μ : Measure Bool) (ν₁ ν₂ : Bool → Measure Bool),
      μ.bind ν₁ = μ.bind ν₂ ∧ ∀ ω, ν₁ ω ≠ ν₂ ω := by
  refine ⟨μ_B, ν₁, ν₂, ?_, ν_ne_everywhere⟩
  -- μ_B.bind(ν₁) = (1/2)•δ_false + (1/2)•δ_true = μ_B.bind(ν₂)
  -- because swapping false↔true under uniform measure is invisible
  ext S hS
  simp only [μ_B]
  rw [Measure.bind_apply hS (measurable_of_finite _).aemeasurable,
      Measure.bind_apply hS (measurable_of_finite _).aemeasurable]
  simp only [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
  simp only [ν₁, ν₂, Bool.not_false, Bool.not_true]
  exact add_comm _ _

end

end Mettapedia.Logic.BindKernelCounterexample

/-!
# L² Uniqueness of De Finetti Directing Measures

The de Finetti directing measure `K(ω)` for an exchangeable sequence is the
conditional distribution of `X₀` given the tail σ-algebra. This file proves
that directing measures agree a.e. under absolutely continuous measures,
using an elementary L² variance argument.

## Core insight (L² variance approach)

For exchangeable `μ` with directing measure `K_μ`, the Cesaro means
`C_n(ω) = (1/n) #{j < n : X_j(ω) = b}` satisfy:

  `E_μ[(C_n - K_μ({b}))²] ≤ 1/n → 0`

Since the Cesaro mean `C_n(ω)` is a **deterministic function of ω** (independent
of the measure), when `ν ≤ μ` we get `C_n → K_μ` in L²(ν) as well. But also
`C_n → K_ν` in L²(ν). By L² uniqueness: `K_μ = K_ν` a.e. ν.

This bypasses the difficult disintegration/tail-measurability approach entirely.

## Structure

1. `integral_mul_condExp_zero` — general condExp pull-out engine (fully proved)
2. `integral_indicator_mul_directingMeasure` — ∫ K·1_{X_j=b} = ∫ K² (from 1)
3. `pair_indicator_eq_integral_K_sq` — μ{X_i=b ∧ X_j=b} = ∫ K² (product formula)
4. `cesaro_variance_bound` — E[(C_n - K)²] ≤ 1/n (from 2, 3)
5. `directingMeasure_singleton_ae_eq_of_le` — K_μ = K_ν a.e. ν (L² uniqueness)
-/

namespace Mettapedia.Logic.CondExpBridge

open MeasureTheory ProbabilityTheory

/-! ### General conditional expectation lemma -/

section GeneralCondExp

/-- **Zero condExp pull-out**: If `E[h | m] = 0` a.e. μ and `g` is m-strongly
measurable with `h * g` integrable, then `∫ h · g dμ = 0`.

Proof: By pull-out, `E[h·g | m] = E[h|m] · g = 0 · g = 0` a.e.
Then `∫ h·g dμ = ∫ E[h·g | m] dμ = ∫ 0 dμ = 0`.

This is the engine behind the condExp pull-out in the variance calculation. -/
theorem integral_mul_condExp_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {m : MeasurableSpace Ω} {μ : @Measure Ω mΩ}
    (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)]
    {h g : Ω → ℝ}
    (hh_int : Integrable h μ)
    (hhg_int : Integrable (h * g) μ)
    (hg_meas : AEStronglyMeasurable (m := m) g μ)
    (hcond : μ[h | m] =ᵐ[μ] 0) :
    ∫ ω, (h * g) ω ∂μ = 0 := by
  -- Step 1: E[h·g | m] =ᵐ[μ] E[h|m] · g  (pull-out, g is m-measurable)
  have hpullout : μ[h * g | m] =ᵐ[μ] μ[h | m] * g :=
    condExp_mul_of_aestronglyMeasurable_right hg_meas hhg_int hh_int
  -- Step 2: E[h|m] · g = 0 · g = 0  a.e.
  have hzero_mul : μ[h | m] * g =ᵐ[μ] 0 := by
    filter_upwards [hcond] with ω hω
    simp [Pi.mul_apply, hω]
  -- Step 3: E[h·g | m] = 0  a.e.
  have hcondprod : μ[h * g | m] =ᵐ[μ] (0 : Ω → ℝ) :=
    hpullout.trans hzero_mul
  -- Step 4: ∫ h·g dμ = ∫ E[h·g | m] dμ = ∫ 0 dμ = 0
  have htower := @integral_condExp Ω ℝ m mΩ μ (h * g) _ _ _ hm _
  rw [← htower]
  calc ∫ ω, μ[h * g | m] ω ∂μ = ∫ ω, (0 : ℝ) ∂μ :=
        integral_congr_ae hcondprod
    _ = 0 := integral_zero Ω ℝ

end GeneralCondExp

end Mettapedia.Logic.CondExpBridge

/-!
# L² Uniqueness of Directing Measures

We prove that if μ, ν are exchangeable probability measures on a path space
with ν ≤ μ, then their de Finetti directing measures agree a.e. ν.

## Strategy

The proof uses the **L¹ Cesaro-to-condExp convergence** from the exchangeability
library. The Cesaro mean `C_m(ω) = (1/m) #{j < m : X_j(ω) = b}` is a
deterministic function of ω (measure-independent). Under each exchangeable
measure π, it converges in L¹(π) to the tail conditional expectation
`π[1_{b} ∘ X₀ | tail]`, which equals `K_π({b}).toReal` a.e. π.

When ν ≤ μ:
  ∫ |C_m - K_μ| dν ≤ ∫ |C_m - K_μ| dμ → 0  (measure domination)
  ∫ |C_m - K_ν| dν → 0                       (L¹ convergence under ν)

By triangle inequality: ∫ |K_μ - K_ν| dν = 0, whence K_μ = K_ν a.e. ν.
-/

namespace Mettapedia.Logic.DirectingMeasureUniqueness

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

/-! ### L¹ limit uniqueness -/

/-- **Core uniqueness lemma**: If two functions are each L¹ limits of the same
sequence under measure ν, they agree a.e. ν.

Formally: if `∫ |c_m - f| dν → 0` and `∫ |c_m - g| dν → 0` for the same
sequence `c_m`, then `f = g` a.e. ν. -/
theorem ae_eq_of_L1_limits
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {c : ℕ → Ω → ℝ} {f g : Ω → ℝ}
    (hf_int : Integrable f ν) (hg_int : Integrable g ν)
    (hc_int : ∀ m, Integrable (c m) ν)
    (hcf : ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M,
      ∫ ω, |c m ω - f ω| ∂ν < ε)
    (hcg : ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M,
      ∫ ω, |c m ω - g ω| ∂ν < ε) :
    f =ᵐ[ν] g := by
  -- ∫ |f - g| dν ≤ ∫ |f - c_m| + |c_m - g| dν → 0
  have hfg_int : Integrable (fun ω => |f ω - g ω|) ν := (hf_int.sub hg_int).norm
  -- For any ε > 0, pick M so that both terms < ε/2
  have h_le_eps : ∀ ε > (0 : ℝ), ∫ ω, |f ω - g ω| ∂ν < ε := by
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    obtain ⟨M₁, hM₁⟩ := hcf (ε / 2) hε2
    obtain ⟨M₂, hM₂⟩ := hcg (ε / 2) hε2
    set M := max M₁ M₂
    have h1 := hM₁ M (le_max_left _ _)
    have h2 := hM₂ M (le_max_right _ _)
    have hfcM_int : Integrable (fun ω => f ω - c M ω) ν := hf_int.sub (hc_int M)
    have hcMg_int : Integrable (fun ω => c M ω - g ω) ν := (hc_int M).sub hg_int
    calc ∫ ω, |f ω - g ω| ∂ν
        ≤ ∫ ω, (|f ω - c M ω| + |c M ω - g ω|) ∂ν := by
          apply integral_mono_of_nonneg
          · exact ae_of_all ν (fun _ => abs_nonneg _)
          · exact hfcM_int.norm.add hcMg_int.norm
          · exact ae_of_all ν (fun ω => by
              calc |f ω - g ω| = |(f ω - c M ω) + (c M ω - g ω)| := by ring_nf
                _ ≤ |f ω - c M ω| + |c M ω - g ω| := abs_add_le _ _)
      _ = ∫ ω, |f ω - c M ω| ∂ν + ∫ ω, |c M ω - g ω| ∂ν :=
          integral_add hfcM_int.norm hcMg_int.norm
      _ = ∫ ω, |c M ω - f ω| ∂ν + ∫ ω, |c M ω - g ω| ∂ν := by
          congr 1; congr 1; ext ω; rw [abs_sub_comm]
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := by ring
  -- ∫ |f - g| ≥ 0 and < ε for all ε > 0 means ∫ |f - g| = 0
  have hint_zero : ∫ ω, |f ω - g ω| ∂ν = 0 := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      exact absurd (h_le_eps _ h) (lt_irrefl _)
    · exact integral_nonneg_of_ae (ae_of_all ν (fun _ => abs_nonneg _))
  -- |f - g| = 0 a.e. ν ⟹ f - g = 0 a.e. ν ⟹ f = g a.e. ν
  have h_abs_zero : (fun ω => |f ω - g ω|) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all ν (fun _ => abs_nonneg _))
      hfg_int).mp hint_zero
  filter_upwards [h_abs_zero] with ω hω
  exact sub_eq_zero.mp (abs_eq_zero.mp hω)

end Mettapedia.Logic.DirectingMeasureUniqueness

/-!
## Directing Measure Uniqueness via L¹ Transfer

We prove that exchangeable probability measures that are absolutely continuous
produce the same de Finetti directing measure. The proof uses the
L¹ Cesaro convergence from the exchangeability library.
-/

namespace Mettapedia.Logic.DirectingMeasureL1Transfer

open MeasureTheory ProbabilityTheory Filter
open _root_.Exchangeability _root_.Exchangeability.DeFinetti.ViaMartingale
open scoped BigOperators

/-! ### Contractability of indicator processes -/

section IndicatorProcess

variable {Ω : Type*} [MeasurableSpace Ω]
  {α : Type*} [MeasurableSpace α] [DecidableEq α]

/-- The indicator process for value `b`: maps ω to 1 if X n ω = b, else 0.
This is a real-valued process derived from an α-valued process. -/
noncomputable def indicatorProcess (X : ℕ → Ω → α) (b : α) : ℕ → Ω → ℝ :=
  fun n ω => if X n ω = b then (1 : ℝ) else (0 : ℝ)

lemma indicatorProcess_measurable (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n))
    (b : α) (hb : MeasurableSet ({b} : Set α)) (n : ℕ) :
    Measurable (indicatorProcess X b n) := by
  unfold indicatorProcess
  exact Measurable.ite (hX n hb) measurable_const measurable_const

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- The indicator process is bounded by 1. -/
lemma indicatorProcess_abs_le_one (X : ℕ → Ω → α) (b : α) (n : ℕ) (ω : Ω) :
    |indicatorProcess X b n ω| ≤ 1 := by
  unfold indicatorProcess
  split_ifs <;> norm_num

/-- Exchangeability of X implies contractability of the indicator process.
This follows directly from the fact that finite-dimensional distributions
of (1_{X_{k(i)} = b})_i are determined by those of (X_{k(i)})_i. -/
lemma contractable_indicatorProcess
    {μ : Measure Ω}
    {X : ℕ → Ω → α} (hX_exch : Exchangeable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (b : α) (hb : MeasurableSet ({b} : Set α)) :
    Contractable μ (indicatorProcess X b) := by
  -- Exchangeable → Contractable
  have hX_contract := contractable_of_exchangeable hX_exch hX_meas
  intro m k hk
  have hcontract := hX_contract m k hk
  -- g : (Fin m → α) → (Fin m → ℝ) is the pointwise indicator
  let g : (Fin m → α) → (Fin m → ℝ) := fun f i => if f i = b then (1 : ℝ) else 0
  have hg_meas : Measurable g := by
    apply measurable_pi_lambda
    intro i
    apply Measurable.ite _ measurable_const measurable_const
    -- Need: MeasurableSet {f : Fin m → α | f i = b}
    -- This is (fun f => f i) ⁻¹' {b}
    have : {a : Fin m → α | a i = b} = (fun f => f i) ⁻¹' {b} := by
      ext f; simp [Set.mem_preimage, Set.mem_singleton_iff]
    rw [this]
    exact (measurable_pi_apply i) hb
  -- Measurability of the projection maps
  have h_meas_k : Measurable (fun ω => (fun (i : Fin m) => X (k i) ω)) :=
    measurable_pi_lambda _ (fun i => hX_meas (k i))
  have h_meas_id : Measurable (fun ω => (fun (i : Fin m) => X i.val ω)) :=
    measurable_pi_lambda _ (fun i => hX_meas i.val)
  -- indicatorProcess at subsequence = g ∘ (X at subsequence)
  have h_eq_k : (fun ω (i : Fin m) => indicatorProcess X b (k i) ω) =
      g ∘ (fun ω (i : Fin m) => X (k i) ω) := by
    ext ω i; simp [indicatorProcess, g]
  have h_eq_id : (fun ω (i : Fin m) => indicatorProcess X b i.val ω) =
      g ∘ (fun ω (i : Fin m) => X i.val ω) := by
    ext ω i; simp [indicatorProcess, g]
  rw [h_eq_k, h_eq_id,
    ← Measure.map_map hg_meas h_meas_k, ← Measure.map_map hg_meas h_meas_id, hcontract]

end IndicatorProcess

/-! ### L¹ transfer under measure domination -/

section L1Transfer

variable {Ω : Type*} [MeasurableSpace Ω]

/-- If `∫ |f_n - g| dμ → 0` and `ν ≤ μ`, then `∫ |f_n - g| dν → 0`.
The key insight: for nonneg functions, `ν ≤ μ` implies `∫ f dν ≤ ∫ f dμ`.  -/
theorem L1_convergence_transfer
    {μ ν : Measure Ω}
    (hle : ν ≤ μ)
    {c : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hcf_int : ∀ m, Integrable (fun ω => |c m ω - f ω|) μ)
    (hcf : ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M,
      ∫ ω, |c m ω - f ω| ∂μ < ε) :
    ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M,
      ∫ ω, |c m ω - f ω| ∂ν < ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := hcf ε hε
  exact ⟨M, fun m hm => by
    calc ∫ ω, |c m ω - f ω| ∂ν
        ≤ ∫ ω, |c m ω - f ω| ∂μ :=
          integral_mono_measure hle (ae_of_all μ (fun _ => abs_nonneg _))
            (hcf_int m)
      _ < ε := hM m hm⟩

/-- **Scaled L¹ transfer**: If `∫ |f_n - g| dμ → 0` and `ν ≤ c • μ` for finite `c`,
then `∫ |f_n - g| dν → 0`. The constant `c` is absorbed by convergence to 0.

This handles the case where `ν` is a NORMALIZED restricted measure:
`ρ_a_norm = (1/c)•ρ_a ≤ (1/c)•ρ`, so `ρ_a_norm ≤ c'•ρ` with `c' = 1/c ≥ 1`. -/
theorem L1_convergence_transfer_smul
    {μ ν : Measure Ω} {C : ENNReal} (hC : C ≠ ⊤)
    (hle : ν ≤ C • μ)
    {c : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hcf_int : ∀ m, Integrable (fun ω => |c m ω - f ω|) μ)
    (hcf : ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M,
      ∫ ω, |c m ω - f ω| ∂μ < ε) :
    ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M,
      ∫ ω, |c m ω - f ω| ∂ν < ε := by
  intro ε hε
  have hC_pos : (0 : ℝ) ≤ C.toReal := ENNReal.toReal_nonneg
  have hden : (0 : ℝ) < C.toReal + 1 := by linarith
  obtain ⟨M, hM⟩ := hcf (ε / (C.toReal + 1)) (div_pos hε hden)
  exact ⟨M, fun m hm => by
    have h1 : ∫ ω, |c m ω - f ω| ∂ν ≤ C.toReal * ∫ ω, |c m ω - f ω| ∂μ :=
      calc ∫ ω, |c m ω - f ω| ∂ν
          ≤ ∫ ω, |c m ω - f ω| ∂(C • μ) :=
            integral_mono_measure hle (ae_of_all _ (fun _ => abs_nonneg _))
              ((hcf_int m).smul_measure hC)
        _ = C.toReal • ∫ ω, |c m ω - f ω| ∂μ :=
            integral_smul_measure (fun ω => |c m ω - f ω|) C
        _ = C.toReal * ∫ ω, |c m ω - f ω| ∂μ := smul_eq_mul _ _
    have h2 : ∫ ω, |c m ω - f ω| ∂μ < ε / (C.toReal + 1) := hM m hm
    calc ∫ ω, |c m ω - f ω| ∂ν
        ≤ C.toReal * ∫ ω, |c m ω - f ω| ∂μ := h1
      _ ≤ C.toReal * (ε / (C.toReal + 1)) :=
          mul_le_mul_of_nonneg_left h2.le hC_pos
      _ < (C.toReal + 1) * (ε / (C.toReal + 1)) :=
          mul_lt_mul_of_pos_right (by linarith : C.toReal < C.toReal + 1)
            (div_pos hε hden)
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hden)⟩

end L1Transfer

/-! ### L² variance curriculum: building blocks -/

section VarianceBound

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- **Pair product formula (ENNReal)**: For exchangeable μ with directing measure K,
the probability of a pair coincidence equals the integral of K({b})².

This extracts a singleton evaluation from the de Finetti finite product formula. -/
lemma pair_product_integral
    [MeasurableSingletonClass α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ n, Measurable (X n))
    (hX_exch : Exchangeable μ X)
    (b : α) :
    μ {ω | X 0 ω = b ∧ X 1 ω = b} =
      ∫⁻ ω, (directingMeasure (μ := μ) X hX_meas ω {b}) ^ 2 ∂μ := by
  have hContract := contractable_of_exchangeable hX_exch hX_meas
  let K := directingMeasure (μ := μ) X hX_meas
  -- Product formula: map(proj) = bind(pi(K)) for sel = Fin.val : Fin 2 → ℕ
  have hprod := finite_product_formula X hContract hX_meas K
    (directingMeasure_isProb X hX_meas)
    (directingMeasure_measurable_eval X hX_meas)
    (fun n B hB => conditional_law_eq_directingMeasure X hContract hX_meas n B hB)
    2 Fin.val Fin.val_strictMono
  -- Evaluate both sides at singleton {fun _ => b}
  let c : Fin 2 → α := fun _ => b
  -- LHS side: μ.map(proj){c} = μ(proj⁻¹'{c}) = μ{X₀=b ∧ X₁=b}
  have hLHS : (Measure.map (fun ω i => X (Fin.val i) ω) μ) {c} =
      μ {ω | X 0 ω = b ∧ X 1 ω = b} := by
    rw [Measure.map_apply (measurable_pi_lambda _ (fun i => hX_meas i.val))
        (measurableSet_singleton c)]
    congr 1; ext ω; simp [c, Set.mem_preimage, funext_iff]
  -- RHS side: μ.bind(pi(K)){c} = ∫⁻ pi(K ω){c} dμ = ∫⁻ K(ω){b}² dμ
  have hRHS : (μ.bind (fun ω => Measure.pi fun _ : Fin 2 => K ω)) {c} =
      ∫⁻ ω, (K ω {b}) ^ 2 ∂μ := by
    have hK_meas_pi : Measurable (fun ω => Measure.pi fun _ : Fin 2 => K ω) :=
      measurable_measure_pi K (directingMeasure_isProb X hX_meas)
        (fun s hs => directingMeasure_measurable_eval X hX_meas s hs)
    rw [Measure.bind_apply (measurableSet_singleton c) hK_meas_pi.aemeasurable]
    congr 1; ext ω
    haveI : IsProbabilityMeasure (K ω) := directingMeasure_isProb X hX_meas ω
    rw [Measure.pi_singleton]
    simp [c, Finset.prod_const, sq]
  -- Chain: LHS = RHS by hprod, then use hLHS and hRHS
  have heval := Measure.ext_iff'.mp hprod {c}
  rw [hLHS] at heval; rw [hRHS] at heval
  exact heval

/-! ### Tail σ-algebra preservation under injective embedding -/

/-- For discrete `α`, `comap (f ∘ g)` equals `comap g` when `f` is injective measurable.
Key step: `g⁻¹'(A) = (f∘g)⁻¹'(f '' A)` for injective `f`, and finite images are measurable. -/
lemma comap_comp_eq_of_injective_discrete
    {Ω α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (g : Ω → α) (f : α → β) (hf_inj : Function.Injective f) (hf_meas : Measurable f) :
    MeasurableSpace.comap (f ∘ g) ‹MeasurableSpace β› =
      MeasurableSpace.comap g ‹MeasurableSpace α› := by
  apply le_antisymm
  · -- (≤): comap(f∘g) = comap(g)(comap(f)) ≤ comap(g) since comap(f) ≤ inst_α by measurability
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (MeasurableSpace.comap_le_iff_le_map.mpr
      (fun _ hs => hf_meas hs))
  · -- (≥): g⁻¹'(A) = (f∘g)⁻¹'(f(A)) for injective f, and f(A) is finite hence measurable
    intro S ⟨A, _, hS⟩
    exact ⟨f '' A, (Set.toFinite (f '' A)).measurableSet,
      by rw [← hS, Set.preimage_comp, Set.preimage_image_eq _ hf_inj]⟩

/-- **Tail σ-algebra preservation**: For discrete `α` and injective measurable `f`,
composing a process with `f` preserves the tail σ-algebra. This is essential for
embedding `Fin k`-valued processes into `ℝ` without losing σ-algebra structure. -/
lemma tailProcess_comp_injective
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (X : ℕ → Ω → α) (f : α → β) (hf_inj : Function.Injective f) (hf_meas : Measurable f) :
    Tail.tailProcess (fun n ω => f (X n ω)) = Tail.tailProcess X := by
  simp only [Tail.tailProcess_def]
  congr 1; funext n
  simp only [Tail.tailFamily]
  exact iSup_congr (fun k =>
    comap_comp_eq_of_injective_discrete (fun ω => X (n + k) ω) f hf_inj hf_meas)

/-! ### Contractability preservation under composition -/

end VarianceBound

section ContractableComposition

variable {Ω : Type*} [MeasurableSpace Ω]
  {α : Type*} [MeasurableSpace α]
  {β : Type*} [MeasurableSpace β]

/-- Contractability is preserved by composing the process with a measurable function.
If `X` is contractable and `f` is measurable, then `f ∘ X` is contractable.
This generalizes `contractable_indicatorProcess` to any measurable `f`. -/
lemma contractable_comp_measurable
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {μ : Measure Ω}
    {X : ℕ → Ω → α} (hX_contract : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (f : α → β) (hf_meas : Measurable f) :
    Contractable μ (fun n ω => f (X n ω)) := by
  intro m k hk
  have hcontract := hX_contract m k hk
  let g : (Fin m → α) → (Fin m → β) := fun v i => f (v i)
  have hg_meas : Measurable g :=
    measurable_pi_lambda _ (fun i => hf_meas.comp (measurable_pi_apply i))
  have h_meas_k : Measurable (fun ω => (fun i : Fin m => X (k i) ω)) :=
    measurable_pi_lambda _ (fun i => hX_meas (k i))
  have h_meas_id : Measurable (fun ω => (fun i : Fin m => X i.val ω)) :=
    measurable_pi_lambda _ (fun i => hX_meas i.val)
  have h_eq_k : (fun ω (i : Fin m) => f (X (k i) ω)) =
      g ∘ (fun ω (i : Fin m) => X (k i) ω) := by ext ω i; simp [g]
  have h_eq_id : (fun ω (i : Fin m) => f (X i.val ω)) =
      g ∘ (fun ω (i : Fin m) => X i.val ω) := by ext ω i; simp [g]
  rw [h_eq_k, h_eq_id,
    ← Measure.map_map hg_meas h_meas_k, ← Measure.map_map hg_meas h_meas_id, hcontract]

end ContractableComposition

/-! ### Main theorem: directing measure uniqueness -/

section MainTheorem

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- **Directing measure uniqueness under measure domination**.

If μ, ν are exchangeable probability measures on a sequence space with `ν ≤ μ`,
then their de Finetti directing measures agree at singletons a.e. ν.

## Proof architecture (embedding + Cesaro + L¹ uniqueness)

Embed `α → ℝ` via injective `emb`. By `tailProcess_comp_injective`, the embedded
process has the same tail σ-algebra as `X`. Apply `cesaro_to_condexp_L1` (ViaL2)
to the embedded process under both `μ` and `ν` — Cesaro means converge in L¹ to
the respective tail condExps, which equal `K_π({b}).toReal` a.e. by
`directingMeasure_X0_marginal`. Transfer L¹(μ) convergence to L¹(ν) via `ν ≤ μ`.
By `ae_eq_of_L1_limits`, the two limits agree a.e. ν. Chain with
`directingMeasure_X0_marginal` under each measure to get `K_μ = K_ν` a.e. ν.

**Proved infrastructure**:
- `ae_eq_of_L1_limits`, `L1_convergence_transfer` (L¹ uniqueness + transfer)
- `contractable_comp_measurable` (contractability under composition)
- `tailProcess_comp_injective` (tail σ-algebra preserved under injection)
- `directingMeasure_X0_marginal` (condExp characterization, from ViaMartingale)
- `cesaro_to_condexp_L1` (L¹ Cesaro convergence, from ViaL2)
- `tailSigma_eq_canonical` (σ-algebra definitions agree, from ViaMartingale)

**Remaining step**: Chain the σ-algebra equalities to match `cesaro_to_condexp_L1`'s
tail σ-algebra (`Tail.tailProcess(emb∘X)`) with `directingMeasure_X0_marginal`'s
(`ViaMartingale.tailSigma X`). By `tailProcess_comp_injective` + `tailSigma_eq_canonical`,
these are propositionally equal, enabling condExp rewriting.
-/
theorem directingMeasure_singleton_ae_eq_of_le
    [Fintype α] [MeasurableSingletonClass α]
    (X : ℕ → Ω → α) (hX_meas : ∀ n, Measurable (X n))
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hX_exch_μ : Exchangeable μ X) (hX_exch_ν : Exchangeable ν X)
    (hle : ν ≤ μ)
    (b : α) :
    (fun ω => (directingMeasure (μ := μ) X hX_meas ω {b}).toReal) =ᵐ[ν]
    (fun ω => (directingMeasure (μ := ν) X hX_meas ω {b}).toReal) := by
  -- Abbreviations
  let K_μ := fun ω => (directingMeasure (μ := μ) X hX_meas ω {b}).toReal
  let K_ν := fun ω => (directingMeasure (μ := ν) X hX_meas ω {b}).toReal
  -- Step 0: Embedding α → ℝ
  let emb : α → ℝ := fun a => ((Fintype.equivFin α a).val : ℝ)
  have hemb_inj : Function.Injective emb := by
    intro a₁ a₂ h; simp only [emb, Nat.cast_inj] at h
    exact (Fintype.equivFin α).injective (Fin.val_injective h)
  have hemb_meas : Measurable emb := measurable_of_finite _
  let Y : ℕ → Ω → ℝ := fun n ω => emb (X n ω)
  have hY_meas : ∀ n, Measurable (Y n) := fun n => hemb_meas.comp (hX_meas n)
  -- Step 1: Contractable Y under both measures
  have hY_contr_μ : Contractable μ Y :=
    contractable_comp_measurable (contractable_of_exchangeable hX_exch_μ hX_meas) hX_meas
      emb hemb_meas
  have hY_contr_ν : Contractable ν Y :=
    contractable_comp_measurable (contractable_of_exchangeable hX_exch_ν hX_meas) hX_meas
      emb hemb_meas
  -- Step 2: σ-algebra chain (the key infrastructure)
  -- TailSigma.tailSigma Y = Tail.tailProcess Y (definitional)
  --                        = Tail.tailProcess X (tailProcess_comp_injective)
  --                        = tailSigma X        (tailSigma_eq_canonical⁻¹)
  have htail : Tail.tailProcess Y = tailSigma X := by
    rw [tailProcess_comp_injective X emb hemb_inj hemb_meas,
        ← tailSigma_eq_canonical X]
  -- Step 3: directingMeasure = condExp via directingMeasure_X0_marginal + σ-algebra chain
  -- K_π({b}).toReal =ᵃᵉ[π] π[1_{b}∘X₀ | tailSigma X] = π[fb∘Y₀ | Tail.tailProcess Y]
  have hK_μ_ae : K_μ =ᵐ[μ]
      (μ[Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0 | tailSigma X]) :=
    directingMeasure_X0_marginal X hX_meas {b} (measurableSet_singleton b)
  have hK_ν_ae : K_ν =ᵐ[ν]
      (ν[Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0 | tailSigma X]) :=
    directingMeasure_X0_marginal X hX_meas {b} (measurableSet_singleton b)
  -- Step 4: Transfer K_μ a.e. equality from μ to ν (since ν ≤ μ)
  have hac : ν.AbsolutelyContinuous μ := Measure.absolutelyContinuous_of_le hle
  have hK_μ_ae_ν : K_μ =ᵐ[ν]
      (μ[Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0 | tailSigma X]) :=
    hac.ae_eq hK_μ_ae
  -- Step 5: Both condExps μ[1_b∘X₀|tail] and ν[1_b∘X₀|tail] are L¹ limits of
  -- the SAME Cesaro sequence (1/m)Σ 1_{X_j=b}. By ae_eq_of_L1_limits they agree a.e. ν.
  -- This is the core argument using cesaro_to_condexp_L1 + L1_convergence_transfer.
  have hcondExp_eq :
      (μ[Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0 | tailSigma X]) =ᵐ[ν]
      (ν[Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0 | tailSigma X]) := by
    -- The indicator function on ℝ for value emb(b)
    let fb : ℝ → ℝ := fun x => if x = emb b then 1 else 0
    have hfb_meas : Measurable fb :=
      Measurable.ite (measurableSet_singleton (emb b)) measurable_const measurable_const
    have hfb_bdd : ∀ x, |fb x| ≤ 1 := fun x => by simp [fb]; split_ifs <;> norm_num
    -- Key: fb ∘ Y₀ = indicator ∘ X₀ (pointwise, by injectivity)
    have hfun_eq : ∀ ω, (fb ∘ Y 0) ω = (Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0) ω := by
      intro ω; simp only [Function.comp, fb, Y, Set.indicator, Set.mem_singleton_iff]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (hemb_inj h1) h2
      · exact absurd (congrArg emb h2) h1
      · rfl
    -- σ-algebra chain: TailSigma.tailSigma Y = Tail.tailProcess Y = tailSigma X
    -- TailSigma.tailSigma = Tail.tailProcess definitionally, and htail gives the rest
    -- So condExp w.r.t. TailSigma.tailSigma Y = condExp w.r.t. tailSigma X
    -- (after rewriting function argument too)
    -- Apply cesaro_to_condexp_L1 under μ
    have hces_μ := _root_.Exchangeability.DeFinetti.ViaL2.cesaro_to_condexp_L1
      hY_contr_μ hY_meas fb hfb_meas hfb_bdd
    -- Apply cesaro_to_condexp_L1 under ν
    have hces_ν := _root_.Exchangeability.DeFinetti.ViaL2.cesaro_to_condexp_L1
      hY_contr_ν hY_meas fb hfb_meas hfb_bdd
    -- Function extensional equality
    have hfun_ext : fb ∘ Y 0 = Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0 := funext hfun_eq
    -- σ-algebra rewrite: unfold TailSigma.tailSigma (= Tail.tailProcess by def),
    -- then rewrite with htail (Tail.tailProcess Y = tailSigma X),
    -- then rewrite function argument (fb∘Y₀ = indicator∘X₀).
    simp only [_root_.Exchangeability.DeFinetti.ViaL2.TailSigma.tailSigma,
               show Tail.tailProcess Y = tailSigma X from htail,
               hfun_ext] at hces_μ hces_ν
    -- hces_μ: ∀ε>0, ∃M, ∀m≥M, ∫|Cesaro - μ[indicator∘X₀|tailSigma X]|dμ < ε
    -- hces_ν: ∀ε>0, ∃M, ∀m≥M, ∫|Cesaro - ν[indicator∘X₀|tailSigma X]|dν < ε
    -- Define Cesaro sequence explicitly
    let cesaro : ℕ → Ω → ℝ := fun m ω => 1 / (m:ℝ) * ∑ i : Fin m, fb (Y (↑i) ω)
    -- Helper: each fb(Y i ω) is integrable (bounded by 1)
    have hfbY_int : ∀ (π : Measure Ω) [IsFiniteMeasure π] (i : ℕ),
        Integrable (fun ω => fb (Y i ω)) π := by
      intro π _ i
      exact (integrable_const (1:ℝ)).mono
        ((hfb_meas.comp (hY_meas i)).aestronglyMeasurable)
        (ae_of_all π fun ω => by
          simp only [Real.norm_eq_abs, norm_one]; exact hfb_bdd _)
    -- Helper: Cesaro mean integrable (const_mul of sum of integrables)
    have hces_int : ∀ (π : Measure Ω) [IsProbabilityMeasure π] (m : ℕ),
        Integrable (cesaro m) π := by
      intro π _ m; show Integrable (fun ω => 1 / (m:ℝ) * ∑ i : Fin m, fb (Y ↑i ω)) π
      exact (integrable_finset_sum (Finset.univ : Finset (Fin m))
        (f := fun i ω => fb (Y (↑i) ω))
        (fun i _ => hfbY_int π ↑i)).const_mul _
    -- |Cesaro - condExp| integrable (sub of integrables)
    have habs_int : ∀ m : ℕ,
        Integrable (fun ω => |cesaro m ω -
          (μ[Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0 | tailSigma X]) ω|) μ :=
      fun m => ((hces_int μ m).sub integrable_condExp).abs
    -- Transfer L¹(μ) → L¹(ν)
    have hces_μ_ν := L1_convergence_transfer hle habs_int hces_μ
    -- L¹ uniqueness
    exact DirectingMeasureUniqueness.ae_eq_of_L1_limits
      (c := cesaro)
      (integrable_condExp.mono_measure hle) integrable_condExp
      (fun m => hces_int ν m)
      hces_μ_ν hces_ν
  -- Step 6: Chain: K_μ =ᵃᵉ[ν] condExp_μ =ᵃᵉ[ν] condExp_ν =ᵃᵉ[ν] K_ν
  exact hK_μ_ae_ν.trans (hcondExp_eq.trans hK_ν_ae.symm)

/-- **Scaled version**: directing measures agree a.e. ν when `ν ≤ C • μ` for finite C.
Needed for start-restricted measures: `ρ_a_norm ≤ (1/c) • ρ` where c = P({ω₀=a}). -/
theorem directingMeasure_singleton_ae_eq_of_smul_le
    [Fintype α] [MeasurableSingletonClass α]
    (X : ℕ → Ω → α) (hX_meas : ∀ n, Measurable (X n))
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hX_exch_μ : Exchangeable μ X) (hX_exch_ν : Exchangeable ν X)
    {C : ENNReal} (hC : C ≠ ⊤) (hle : ν ≤ C • μ)
    (b : α) :
    (fun ω => (directingMeasure (μ := μ) X hX_meas ω {b}).toReal) =ᵐ[ν]
    (fun ω => (directingMeasure (μ := ν) X hX_meas ω {b}).toReal) := by
  -- Same structure as directingMeasure_singleton_ae_eq_of_le,
  -- using L1_convergence_transfer_smul instead of L1_convergence_transfer.
  let emb : α → ℝ := fun a => ((Fintype.equivFin α a).val : ℝ)
  have hemb_inj : Function.Injective emb := by
    intro a₁ a₂ h; simp only [emb, Nat.cast_inj] at h
    exact (Fintype.equivFin α).injective (Fin.val_injective h)
  have hemb_meas : Measurable emb := measurable_of_finite _
  let Y : ℕ → Ω → ℝ := fun n ω => emb (X n ω)
  have hY_meas : ∀ n, Measurable (Y n) := fun n => hemb_meas.comp (hX_meas n)
  have hY_contr_μ : Contractable μ Y :=
    contractable_comp_measurable (contractable_of_exchangeable hX_exch_μ hX_meas) hX_meas
      emb hemb_meas
  have hY_contr_ν : Contractable ν Y :=
    contractable_comp_measurable (contractable_of_exchangeable hX_exch_ν hX_meas) hX_meas
      emb hemb_meas
  have htail : Tail.tailProcess Y = tailSigma X := by
    rw [tailProcess_comp_injective X emb hemb_inj hemb_meas, ← tailSigma_eq_canonical X]
  have hK_μ_ae := @directingMeasure_X0_marginal _ _ _ μ _ _ _ _ _ X hX_meas {b} (measurableSet_singleton b)
  have hK_ν_ae := @directingMeasure_X0_marginal _ _ _ ν _ _ _ _ _ X hX_meas {b} (measurableSet_singleton b)
  have hac : ν.AbsolutelyContinuous μ := Measure.absolutelyContinuous_of_le_smul hle
  have hK_μ_ae_ν := hac.ae_eq hK_μ_ae
  -- Cesaro L¹ convergence under both measures
  let fb : ℝ → ℝ := fun x => if x = emb b then 1 else 0
  have hfb_meas : Measurable fb :=
    Measurable.ite (measurableSet_singleton (emb b)) measurable_const measurable_const
  have hfb_bdd : ∀ x, |fb x| ≤ 1 := fun x => by simp [fb]; split_ifs <;> norm_num
  have hfun_eq : ∀ ω, (fb ∘ Y 0) ω = (Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0) ω := by
    intro ω; simp only [Function.comp, fb, Y, Set.indicator, Set.mem_singleton_iff]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hemb_inj h1) h2
    · exact absurd (congrArg emb h2) h1
    · rfl
  have hfun_ext : fb ∘ Y 0 = Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0 := funext hfun_eq
  have hces_μ := _root_.Exchangeability.DeFinetti.ViaL2.cesaro_to_condexp_L1
    hY_contr_μ hY_meas fb hfb_meas hfb_bdd
  have hces_ν := _root_.Exchangeability.DeFinetti.ViaL2.cesaro_to_condexp_L1
    hY_contr_ν hY_meas fb hfb_meas hfb_bdd
  simp only [_root_.Exchangeability.DeFinetti.ViaL2.TailSigma.tailSigma,
             show Tail.tailProcess Y = tailSigma X from htail,
             hfun_ext] at hces_μ hces_ν
  -- σ-algebra chain succeeded; condExps now use tailSigma X
  have hcondExp_eq :
      (μ[Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0 | tailSigma X]) =ᵐ[ν]
      (ν[Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0 | tailSigma X]) := by
    let cesaro : ℕ → Ω → ℝ := fun m ω => 1 / (m:ℝ) * ∑ i : Fin m, fb (Y (↑i) ω)
    have hfbY_int : ∀ (π : Measure Ω) [IsFiniteMeasure π] (i : ℕ),
        Integrable (fun ω => fb (Y i ω)) π := by
      intro π _ i
      exact (integrable_const (1:ℝ)).mono
        ((hfb_meas.comp (hY_meas i)).aestronglyMeasurable)
        (ae_of_all π fun ω => by
          simp only [Real.norm_eq_abs, norm_one]; exact hfb_bdd _)
    have hces_int : ∀ (π : Measure Ω) [IsProbabilityMeasure π] (m : ℕ),
        Integrable (cesaro m) π := by
      intro π _ m; show Integrable (fun ω => 1 / (m:ℝ) * ∑ i : Fin m, fb (Y ↑i ω)) π
      exact (integrable_finset_sum (Finset.univ : Finset (Fin m))
        (f := fun i ω => fb (Y (↑i) ω))
        (fun i _ => hfbY_int π ↑i)).const_mul _
    have habs_int : ∀ m : ℕ,
        Integrable (fun ω => |cesaro m ω -
          (μ[Set.indicator {b} (fun _ => (1:ℝ)) ∘ X 0 | tailSigma X]) ω|) μ :=
      fun m => ((hces_int μ m).sub integrable_condExp).abs
    -- Transfer L¹(μ) → L¹(ν) using SCALED domination
    have hces_μ_ν := L1_convergence_transfer_smul hC hle habs_int hces_μ
    exact DirectingMeasureUniqueness.ae_eq_of_L1_limits
      (c := cesaro)
      ((integrable_condExp.smul_measure hC).mono_measure hle) integrable_condExp
      (fun m => hces_int ν m)
      hces_μ_ν hces_ν
  exact hK_μ_ae_ν.trans (hcondExp_eq.trans hK_ν_ae.symm)

/-- **Directing measure condExp characterization under dominated measures.**

For exchangeable probability measures μ, ν with ν ≤ C•μ, the μ-directing measure
satisfies the condExp characterization under ν needed by `finite_product_formula`.

This chains:
1. `directingMeasure_singleton_ae_eq_of_smul_le`: K_μ({b}) = K_ν({b}) a.e. ν (singletons)
2. Finite union: K_μ(B) = K_ν(B) a.e. ν (all measurable B, via Fintype)
3. `conditional_law_eq_directingMeasure`: K_ν(B) = ν-condExp a.e. ν -/
theorem directingMeasure_condExp_law_of_smul_le
    [Fintype α] [MeasurableSingletonClass α]
    (X : ℕ → Ω → α) (hX_meas : ∀ n, Measurable (X n))
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hX_exch_μ : Exchangeable μ X) (hX_exch_ν : Exchangeable ν X)
    {C : ENNReal} (hC : C ≠ ⊤) (hle : ν ≤ C • μ)
    (n : ℕ) (B : Set α) (hB : MeasurableSet B) :
    (fun ω => (directingMeasure (μ := μ) X hX_meas ω B).toReal) =ᵐ[ν]
      ν[Set.indicator B (fun _ => (1:ℝ)) ∘ X n | tailSigma X] := by
  -- Step 1: K_μ(B) = K_ν(B) a.e. ν (from singleton equality + finite union)
  have hK_eq_B : (fun ω => (directingMeasure (μ := μ) X hX_meas ω B).toReal) =ᵐ[ν]
      (fun ω => (directingMeasure (μ := ν) X hX_meas ω B).toReal) := by
    -- For finite α: B = ⋃ b ∈ B, {b}. K(B) = Σ_{b ∈ B} K({b}).
    -- Singleton equality for each b gives K_μ(B) = K_ν(B) a.e.
    -- Use measure_eq_sum_singletons for Fintype α
    have h_sing : ∀ b : α,
        (fun ω => (directingMeasure (μ := μ) X hX_meas ω {b}).toReal) =ᵐ[ν]
        (fun ω => (directingMeasure (μ := ν) X hX_meas ω {b}).toReal) :=
      fun b => directingMeasure_singleton_ae_eq_of_smul_le X hX_meas hX_exch_μ hX_exch_ν hC hle b
    -- Finite intersection: all singletons agree simultaneously a.e.
    have h_all : ∀ᵐ ω ∂ν, ∀ b : α,
        (directingMeasure (μ := μ) X hX_meas ω {b}).toReal =
        (directingMeasure (μ := ν) X hX_meas ω {b}).toReal :=
      ae_all_iff.mpr h_sing
    -- Pointwise: singleton agreement → full measure equality → B agreement
    filter_upwards [h_all] with ω hω
    -- From toReal equality at singletons → ENNReal equality at singletons
    have h_ennreal : ∀ b : α,
        directingMeasure (μ := μ) X hX_meas ω {b} =
        directingMeasure (μ := ν) X hX_meas ω {b} := by
      intro b
      haveI : IsProbabilityMeasure (directingMeasure (μ := μ) X hX_meas ω) :=
        directingMeasure_isProb (μ := μ) X hX_meas ω
      haveI : IsProbabilityMeasure (directingMeasure (μ := ν) X hX_meas ω) :=
        directingMeasure_isProb (μ := ν) X hX_meas ω
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (hω b)
    -- From singleton ENNReal equality → measure equality (Countable α)
    have h_meas_eq : directingMeasure (μ := μ) X hX_meas ω =
        directingMeasure (μ := ν) X hX_meas ω :=
      Measure.ext_of_singleton h_ennreal
    -- Evaluate at B
    exact congrArg (fun K => (K B).toReal) h_meas_eq
  -- Step 2: K_ν(B) = ν-condExp a.e. ν (from conditional_law_eq_directingMeasure)
  have hContract_ν := contractable_of_exchangeable hX_exch_ν hX_meas
  have hK_ν_law := conditional_law_eq_directingMeasure X hContract_ν hX_meas n B hB
  exact hK_eq_B.trans hK_ν_law

end MainTheorem

/-! ## A.E. Limit Identification via L¹ Subsequence

When a sequence converges both a.e. (to some limit q) and in L¹ (to directingMeasure),
the a.e. limit must equal the L¹ limit a.e. This uses:
1. L¹ → convergence in measure → a.e. convergence along subsequence (Riesz-Weyl)
2. If full sequence converges a.e. to q, so does any subsequence
3. By `tendsto_nhds_unique` in T2 spaces, the limits agree
-/

/-- **Key bridge**: If a sequence converges a.e. to some limit AND in L¹ to another limit,
the a.e. limit equals the L¹ limit a.e.

This is the pathwise identification theorem that connects:
- `ae_exists_tendsto` (existence of some pointwise limit)
- `cesaro_to_condexp_L1` (L¹ limit = directingMeasure)
-/
lemma ae_limit_eq_L1_limit_of_ae_tendsto_and_L1_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf_meas : ∀ n, Measurable (f n))
    (hg_meas : Measurable g)
    (hf_int : ∀ n, Integrable (f n) μ)
    (hg_int : Integrable g μ)
    (hL1 : ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M, ∫ ω, |f m ω - g ω| ∂μ < ε)
    (hae : ∀ᵐ ω ∂μ, ∃ q : ℝ, Filter.Tendsto (fun n => f n ω) Filter.atTop (nhds q)) :
    ∀ᵐ ω ∂μ,
      ∀ q : ℝ,
        Filter.Tendsto (fun n => f n ω) Filter.atTop (nhds q) →
        q = g ω := by
  -- L¹ convergence → eLpNorm convergence (for p = 1)
  have h_snorm : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (f n - g) 1 μ) Filter.atTop (nhds 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    by_cases hε_top : ε = ⊤
    · -- Trivially ≤ ⊤
      use 0; intro m _; simp [hε_top]
    have hε_real : (0 : ℝ) < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
    obtain ⟨M, hM⟩ := hL1 ε.toReal hε_real
    use M
    intro m hm
    calc MeasureTheory.eLpNorm (f m - g) 1 μ
        = ∫⁻ ω, ‖(f m - g) ω‖ₑ ∂μ := MeasureTheory.eLpNorm_one_eq_lintegral_enorm
      _ = ∫⁻ ω, ENNReal.ofReal |f m ω - g ω| ∂μ := by
          congr 1; ext ω
          simp only [Pi.sub_apply, Real.enorm_eq_ofReal_abs]
      _ = ENNReal.ofReal (∫ ω, |f m ω - g ω| ∂μ) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            ((hf_int m).sub hg_int).abs (ae_of_all μ (fun ω => abs_nonneg _))).symm
      _ ≤ ENNReal.ofReal ε.toReal := by
          apply ENNReal.ofReal_le_ofReal
          exact le_of_lt (hM m hm)
      _ = ε := ENNReal.ofReal_toReal hε_top
  -- eLpNorm convergence → convergence in measure
  have h_in_measure : MeasureTheory.TendstoInMeasure μ f Filter.atTop g :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
      (by norm_num : (1 : ENNReal) ≠ 0) (by norm_num : (1 : ENNReal) ≠ ⊤)
      (fun n => (hf_meas n).aestronglyMeasurable) hg_meas.aestronglyMeasurable h_snorm
  -- Convergence in measure → a.e. convergence along a subsequence
  obtain ⟨ns, hns_mono, hns_ae⟩ := h_in_measure.exists_seq_tendsto_ae
  -- For a.e. ω: full sequence converges to q(ω), subsequence converges to g(ω)
  -- By tendsto_nhds_unique, they must agree
  filter_upwards [hae, hns_ae] with ω ⟨_q, _hq⟩ hns_to_g
  intro q' hq'
  -- Subsequence of convergent sequence converges to same limit
  have hns_to_q' : Filter.Tendsto (fun n => f (ns n) ω) Filter.atTop (nhds q') :=
    hq'.comp (hns_mono.tendsto_atTop)
  exact tendsto_nhds_unique hns_to_q' hns_to_g

end Mettapedia.Logic.DirectingMeasureL1Transfer
