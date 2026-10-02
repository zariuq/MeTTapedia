import Mettapedia.ProbabilityTheory.BayesianInference.Basic
import Mettapedia.InformationTheory.ConditionalMutualInformation

/-!
# Variational inference on a finite state space

The variational functional is defined from the unnormalized joint density.
Its posterior-divergence decomposition and minimizing distribution are derived.
All finite real-valued claims require support compatibility; the log convention
at zero is not used to disguise an infinite divergence.

References: Da Costa et al., *Active inference on discrete state-spaces: a
synthesis* (2020), equation (2).
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference

open Finset
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV

variable {S : Type*} [Fintype S]

/-- Absolute continuity for finite probability masses. -/
def SupportedBy (q : Prob S) (density : S → ℝ) : Prop :=
  ∀ s, 0 < q.1 s → 0 < density s

/-- The log-density variational functional, before normalization of the joint density. -/
noncomputable def variationalFreeEnergy (prior : Prob S) (likelihood : S → ℝ)
    (q : Prob S) : ℝ :=
  ∑ s, q.1 s * (Real.log (q.1 s) - Real.log (prior.1 s * likelihood s))

theorem supportedBy_posterior (prior q : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood)
    (support : SupportedBy q (fun s => prior.1 s * likelihood s)) :
    SupportedBy q (posterior prior likelihood nonneg possible).1 := by
  intro s hs
  exact div_pos (support s hs) possible

/-- The variational gap is exactly divergence from the true posterior. -/
theorem variationalFreeEnergy_eq (prior q : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood)
    (support : SupportedBy q (fun s => prior.1 s * likelihood s)) :
    variationalFreeEnergy prior likelihood q =
      klSum q.1 (posterior prior likelihood nonneg possible).1 -
        Real.log (evidence prior likelihood) := by
  have hterm : ∀ s, q.1 s * Real.log
      (q.1 s / (posterior prior likelihood nonneg possible).1 s) =
      q.1 s * (Real.log (q.1 s) - Real.log (prior.1 s * likelihood s)) +
        q.1 s * Real.log (evidence prior likelihood) := by
    intro s
    rcases (q.2.1 s).lt_or_eq with hs | hs
    · have hd : 0 < prior.1 s * likelihood s := support s hs
      rw [posterior_apply, Real.log_div hs.ne' (div_pos hd possible).ne',
        Real.log_div hd.ne' possible.ne']
      ring
    · rw [← hs]
      simp
  rw [klSum_eq_sum, Finset.sum_congr rfl (fun s _ => hterm s),
    Finset.sum_add_distrib, ← Finset.sum_mul, q.2.2, one_mul]
  unfold variationalFreeEnergy
  ring

/-- Gibbs' inequality gives the evidence lower bound. -/
theorem neg_log_evidence_le_variationalFreeEnergy (prior q : Prob S)
    (likelihood : S → ℝ) (nonneg : ∀ s, 0 ≤ likelihood s)
    (possible : 0 < evidence prior likelihood)
    (support : SupportedBy q (fun s => prior.1 s * likelihood s)) :
    -Real.log (evidence prior likelihood) ≤ variationalFreeEnergy prior likelihood q := by
  rw [variationalFreeEnergy_eq prior q likelihood nonneg possible support]
  have h := klSumOn_nonneg Finset.univ q.1
    (posterior prior likelihood nonneg possible).1
    (fun s _ => q.2.1 s)
    (fun s _ => (posterior prior likelihood nonneg possible).2.1 s)
    (fun s _ hs => supportedBy_posterior prior q likelihood nonneg possible support s hs)
    (by rw [q.2.2, (posterior prior likelihood nonneg possible).2.2])
  change 0 ≤ klSum q.1 (posterior prior likelihood nonneg possible).1 at h
  linarith

/-- The posterior attains the evidence bound. -/
theorem variationalFreeEnergy_posterior (prior : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood) :
    variationalFreeEnergy prior likelihood (posterior prior likelihood nonneg possible) =
      -Real.log (evidence prior likelihood) := by
  have hs : SupportedBy (posterior prior likelihood nonneg possible)
      (fun s => prior.1 s * likelihood s) := by
    intro s h
    exact (div_pos_iff_of_pos_right possible).mp h
  rw [variationalFreeEnergy_eq prior _ likelihood nonneg possible hs,
    klSum_self_eq_zero _ (posterior prior likelihood nonneg possible).2.1, zero_sub]

/-- Equality in the evidence bound characterizes the posterior uniquely. -/
theorem variationalFreeEnergy_eq_bound_iff (prior q : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood)
    (support : SupportedBy q (fun s => prior.1 s * likelihood s)) :
    variationalFreeEnergy prior likelihood q = -Real.log (evidence prior likelihood) ↔
      q = posterior prior likelihood nonneg possible := by
  constructor
  · intro heq
    have hk : klSum q.1 (posterior prior likelihood nonneg possible).1 = 0 := by
      rw [variationalFreeEnergy_eq prior q likelihood nonneg possible support] at heq
      linarith
    apply Subtype.ext
    funext s
    exact klSumOn_eq_zero_imp Finset.univ q.1
      (posterior prior likelihood nonneg possible).1
      (fun t _ => q.2.1 t)
      (fun t _ => (posterior prior likelihood nonneg possible).2.1 t)
      (fun t _ ht => supportedBy_posterior prior q likelihood nonneg possible support t ht)
      (by rw [q.2.2, (posterior prior likelihood nonneg possible).2.2]) hk s (mem_univ s)
  · rintro rfl
    exact variationalFreeEnergy_posterior prior likelihood nonneg possible

/-- Complexity minus expected log likelihood is the same log-density functional. -/
theorem variationalFreeEnergy_complexity_accuracy (prior q : Prob S)
    (likelihood : S → ℝ)
    (support : SupportedBy q (fun s => prior.1 s * likelihood s)) :
    variationalFreeEnergy prior likelihood q =
      klSum q.1 prior.1 - ∑ s, q.1 s * Real.log (likelihood s) := by
  rw [klSum_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rcases (q.2.1 s).lt_or_eq with hs | hs
  · have hd : 0 < prior.1 s * likelihood s := support s hs
    have hp : prior.1 s ≠ 0 := by
      intro heq
      rw [heq, zero_mul] at hd
      exact (lt_irrefl 0) hd
    have hl : likelihood s ≠ 0 := by
      intro heq
      rw [heq, mul_zero] at hd
      exact (lt_irrefl 0) hd
    rw [Real.log_div hs.ne' hp, Real.log_mul hp hl]
    ring
  · rw [← hs]
    simp

end Mettapedia.ProbabilityTheory.BayesianInference
