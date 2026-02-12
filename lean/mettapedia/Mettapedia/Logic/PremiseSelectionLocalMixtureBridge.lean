import Mettapedia.Logic.Exchangeability
import Mettapedia.Logic.DeFinetti
import Mettapedia.Logic.DiaconisFreedmanFinite
import Mettapedia.Logic.PremiseSelectionCoverage

/-!
# Finite de Finetti to Local-Mixture Bridge for Premise Selection

This file specializes exchangeability/de Finetti count-sufficiency to a premise-selection
setting:

- A local neighborhood/bin provides binary observations (`used` / `not used`) for a premise.
- Under finite exchangeability, sequence probability depends only on success count `k`.
- Therefore there exists a local count-kernel `q(k)` that represents local prior mass.

This is the finite theorem-level bridge from exchangeable local evidence to a
mixture-of-locals architecture.
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped Classical
open scoped ENNReal
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {n : ℕ}
variable (X : Fin n → Ω → Bool) (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Local evidence state: `(k, n-k)` from a binary local pattern. -/
def localEvidence (vals : Fin n → Bool) : Nat × Nat :=
  (Mettapedia.Logic.Exchangeability.countTrue vals,
    Mettapedia.Logic.Exchangeability.countFalse vals)

/-- Dependency set encoded by a local binary pattern (`true = used/relevant`). -/
def depSetOfVals (vals : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => vals i = true)

@[simp] theorem depSetOfVals_card (vals : Fin n → Bool) :
    (depSetOfVals vals).card = Mettapedia.Logic.Exchangeability.countTrue vals := by
  simp [depSetOfVals, Mettapedia.Logic.Exchangeability.countTrue]

/-- Exchangeable local probability depends only on local evidence `(k, n-k)`. -/
theorem finite_exchangeable_prob_depends_only_on_localEvidence
    (hexch : Mettapedia.Logic.Exchangeability.FiniteExchangeable n X μ)
    (vals₁ vals₂ : Fin n → Bool)
    (hev : localEvidence vals₁ = localEvidence vals₂) :
    μ {ω | ∀ i, X i ω = vals₁ i} = μ {ω | ∀ i, X i ω = vals₂ i} := by
  have hcount :
      Mettapedia.Logic.Exchangeability.countTrue vals₁ =
        Mettapedia.Logic.Exchangeability.countTrue vals₂ := by
    simpa [localEvidence] using congrArg Prod.fst hev
  exact
    Mettapedia.Logic.Exchangeability.exchangeable_same_counts_same_prob
      (X := X) (μ := μ) hexch vals₁ vals₂ hcount

/-- Canonical finite count-kernel induced by an exchangeable local model. -/
noncomputable def localCountKernel
    (_hexch : Mettapedia.Logic.Exchangeability.FiniteExchangeable n X μ) : Nat → ℝ≥0∞ :=
  fun k =>
    if hk : ∃ vals : Fin n → Bool, Mettapedia.Logic.Exchangeability.countTrue vals = k then
      let vals0 := Classical.choose hk
      μ {ω | ∀ i, X i ω = vals0 i}
    else 0

/-- The local count-kernel reproduces the probability of any local pattern by `k=countTrue`. -/
theorem localCountKernel_spec
    (hexch : Mettapedia.Logic.Exchangeability.FiniteExchangeable n X μ)
    (vals : Fin n → Bool) :
    localCountKernel X μ hexch (Mettapedia.Logic.Exchangeability.countTrue vals) =
      μ {ω | ∀ i, X i ω = vals i} := by
  let k := Mettapedia.Logic.Exchangeability.countTrue vals
  have hk :
      ∃ v : Fin n → Bool, Mettapedia.Logic.Exchangeability.countTrue v = k := ⟨vals, rfl⟩
  unfold localCountKernel
  rw [dif_pos hk]
  have hchoose :
      Mettapedia.Logic.Exchangeability.countTrue (Classical.choose hk) = k :=
    Classical.choose_spec hk
  have hsame :
      μ {ω | ∀ i, X i ω = (Classical.choose hk) i} =
        μ {ω | ∀ i, X i ω = vals i} :=
    Mettapedia.Logic.Exchangeability.exchangeable_same_counts_same_prob
      (X := X) (μ := μ) hexch (Classical.choose hk) vals (hchoose.trans rfl)
  simpa [k] using hsame

/-- Finite de Finetti bridge: existence of a local mixture kernel over count states. -/
theorem finite_deFinetti_local_mixture_bridge
    (hexch : Mettapedia.Logic.Exchangeability.FiniteExchangeable n X μ) :
    ∃ q : Nat → ℝ≥0∞, ∀ vals : Fin n → Bool,
      q (Mettapedia.Logic.Exchangeability.countTrue vals) =
        μ {ω | ∀ i, X i ω = vals i} := by
  refine ⟨localCountKernel X μ hexch, ?_⟩
  intro vals
  exact localCountKernel_spec (X := X) (μ := μ) hexch vals

/-- Surrogate link: local evidence count `k` bounds achievable dependency coverage by budget. -/
theorem localEvidence_coverage_bound
    (S : Finset (Fin n)) (vals : Fin n → Bool) :
    dependencyCoverage (depSetOfVals vals) S ≤
      Nat.min S.card (Mettapedia.Logic.Exchangeability.countTrue vals) := by
  have hbase :
      dependencyCoverage (depSetOfVals vals) S ≤ Nat.min S.card (depSetOfVals vals).card :=
    dependencyCoverage_le_min_of_card_le (D := depSetOfVals vals) (S := S) (k := S.card) (le_rfl)
  simpa [depSetOfVals_card] using hbase

section Partitioned

variable {Bin : Type*}
variable (nBin : Bin → Nat)
variable (Xbin : (b : Bin) → Fin (nBin b) → Ω → Bool)

/-- Partitioned finite de Finetti bridge: each local bin has its own count-kernel,
and all kernels coexist as a single bin-indexed family. -/
theorem finite_deFinetti_partitioned_local_mixture_bridge :
    (hexchBin :
      ∀ b : Bin,
        Mettapedia.Logic.Exchangeability.FiniteExchangeable (nBin b) (Xbin b) μ) →
    ∃ q : (b : Bin) → Nat → ℝ≥0∞, ∀ b : Bin, ∀ vals : Fin (nBin b) → Bool,
      q b (Mettapedia.Logic.Exchangeability.countTrue vals) =
        μ {ω | ∀ i, Xbin b i ω = vals i} := by
  intro hexchBin
  refine ⟨
    (fun b =>
      Classical.choose
        (finite_deFinetti_local_mixture_bridge
          (X := Xbin b) (μ := μ) (n := nBin b) (hexch := hexchBin b))),
    ?_⟩
  intro b vals
  exact
    (Classical.choose_spec
      (finite_deFinetti_local_mixture_bridge
        (X := Xbin b) (μ := μ) (n := nBin b) (hexch := hexchBin b))) vals

end Partitioned

section QuantitativeFinite

open BigOperators

/-- Quantitative finite bridge (Diaconis–Freedman finite core):
for any finite local statistic, the pushforward L1 discrepancy between iid sampling
and without-replacement injective sampling is bounded by `4 m² / R`.

This provides an explicit finite-sample approximation guarantee for local-mixture
statistics, complementing the existential count-kernel bridge above. -/
theorem finite_statistic_l1_mixture_bound
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (R m : ℕ) (hR : 0 < R) (hRm : m ≤ R)
    (stat : (Fin m → Fin R) → Γ) :
    let μ : (Fin m → Fin R) → ℝ := fun _ => (1 : ℝ) / (R : ℝ) ^ m
    let Z : ℝ := ∑ g : Fin m → Fin R,
      if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0
    let ν : (Fin m → Fin R) → ℝ := fun ω =>
      if Function.Injective ω then ((1 : ℝ) / (R : ℝ) ^ m) / Z else 0
    (∑ γ : Γ, abs ((∑ ω : Fin m → Fin R, if stat ω = γ then μ ω else 0) -
        (∑ ω : Fin m → Fin R, if stat ω = γ then ν ω else 0)))
      ≤ (4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by
  intro μ Z ν
  have hpush :
      (∑ γ : Γ, abs ((∑ ω : Fin m → Fin R, if stat ω = γ then μ ω else 0) -
          (∑ ω : Fin m → Fin R, if stat ω = γ then ν ω else 0)))
        ≤ ∑ ω : Fin m → Fin R, abs (μ ω - ν ω) :=
    Mettapedia.Logic.l1_pushforward_le (μ := μ) (ν := ν) (f := stat)
  have hbase : (∑ ω : Fin m → Fin R, abs (μ ω - ν ω))
      ≤ (4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by
    dsimp [μ, ν, Z]
    simpa using (Mettapedia.Logic.l1_iid_inj_le R m hR hRm)
  exact le_trans hpush hbase

/-- TV-style finite bound (`TV = 1/2 * L1`) for statistic pushforwards. -/
theorem finite_statistic_tv_mixture_bound
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (R m : ℕ) (hR : 0 < R) (hRm : m ≤ R)
    (stat : (Fin m → Fin R) → Γ) :
    let μ : (Fin m → Fin R) → ℝ := fun _ => (1 : ℝ) / (R : ℝ) ^ m
    let Z : ℝ := ∑ g : Fin m → Fin R,
      if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0
    let ν : (Fin m → Fin R) → ℝ := fun ω =>
      if Function.Injective ω then ((1 : ℝ) / (R : ℝ) ^ m) / Z else 0
    ((1 / 2 : ℝ) *
      (∑ γ : Γ, abs ((∑ ω : Fin m → Fin R, if stat ω = γ then μ ω else 0) -
          (∑ ω : Fin m → Fin R, if stat ω = γ then ν ω else 0))))
      ≤ (2 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by
  intro μ Z ν
  have hl1 :
      (∑ γ : Γ, abs ((∑ ω : Fin m → Fin R, if stat ω = γ then μ ω else 0) -
          (∑ ω : Fin m → Fin R, if stat ω = γ then ν ω else 0)))
        ≤ (4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) :=
    finite_statistic_l1_mixture_bound (R := R) (m := m) hR hRm stat
  have hmul :
      (1 / 2 : ℝ) *
        (∑ γ : Γ, abs ((∑ ω : Fin m → Fin R, if stat ω = γ then μ ω else 0) -
            (∑ ω : Fin m → Fin R, if stat ω = γ then ν ω else 0)))
        ≤ (1 / 2 : ℝ) * ((4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ)) :=
    mul_le_mul_of_nonneg_left hl1 (by positivity)
  calc
    (1 / 2 : ℝ) *
        (∑ γ : Γ, abs ((∑ ω : Fin m → Fin R, if stat ω = γ then μ ω else 0) -
            (∑ ω : Fin m → Fin R, if stat ω = γ then ν ω else 0)))
        ≤ (1 / 2 : ℝ) * ((4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ)) := hmul
    _ = (2 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by ring

/-- Binary (`used`/`not-used`) specialization of the finite TV mixture bound. -/
theorem finite_binary_statistic_tv_mixture_bound
    (R m : ℕ) (hR : 0 < R) (hRm : m ≤ R)
    (stat : (Fin m → Fin R) → Bool) :
    let μ : (Fin m → Fin R) → ℝ := fun _ => (1 : ℝ) / (R : ℝ) ^ m
    let Z : ℝ := ∑ g : Fin m → Fin R,
      if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0
    let ν : (Fin m → Fin R) → ℝ := fun ω =>
      if Function.Injective ω then ((1 : ℝ) / (R : ℝ) ^ m) / Z else 0
    ((1 / 2 : ℝ) *
      (∑ b : Bool, abs ((∑ ω : Fin m → Fin R, if stat ω = b then μ ω else 0) -
          (∑ ω : Fin m → Fin R, if stat ω = b then ν ω else 0))))
      ≤ (2 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by
  simpa using
    (finite_statistic_tv_mixture_bound
      (Γ := Bool) (R := R) (m := m) hR hRm stat)

end QuantitativeFinite

end Mettapedia.Logic.PremiseSelection
