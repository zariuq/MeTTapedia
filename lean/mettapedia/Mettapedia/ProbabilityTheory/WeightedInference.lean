import Mettapedia.ProbabilityTheory.BayesianInference.Basic
import Mathlib.Tactic

/-!
# Proper weighting for finite Monte Carlo algorithms

The contract concerns the expectation of the entire returned weighted measure,
not the validity of numerical weights considered separately. This is the finite
form of proper weighting in Naesseth, Lindsten and Schön, *Nested Sequential
Monte Carlo Methods* (ICML 2015), https://proceedings.mlr.press/v37/naesseth15.pdf.
No consistency, independence or effective-sample-size guarantee follows solely
from this first-moment contract.

The defensive-mixture terminology follows Hesterberg, *Weighted Average
Importance Sampling and Defensive Mixture Distributions*, Technometrics 37
(1995), 185–194, DOI 10.1080/00401706.1995.10484303.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.ProbabilityTheory.WeightedInference
open Finset Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference

variable {Ω S A B I J : Type} [Fintype Ω] [Fintype S]

def expectation (p : Prob Ω) (f : Ω → ℝ) : ℝ := ∑ ω, p.1 ω * f ω

/-- The sampling law, output and weight are independent data. -/
structure ProperlyWeighted (p : Prob Ω) (output : Ω → S) (weight : Ω → ℝ)
    (target : S → ℝ) : Prop where
  nonnegative : ∀ ω, 0 ≤ weight ω
  integral : ∀ f : S → ℝ,
    expectation p (fun ω => weight ω * f (output ω)) = ∑ s, target s * f s

theorem ProperlyWeighted.normalizer {p : Prob Ω} {output : Ω → S} {weight : Ω → ℝ}
    {target : S → ℝ} (h : ProperlyWeighted p output weight target) :
    expectation p weight = ∑ s, target s := by simpa using h.integral (fun _ => 1)

/-- Support compatibility is in the target-to-proposal direction. -/
def Covers (proposal : Prob S) (target : S → ℝ) : Prop :=
  ∀ s, target s ≠ 0 → proposal.1 s ≠ 0

theorem importance (proposal : Prob S) (target : S → ℝ)
    (nonneg : ∀ s, 0 ≤ target s) (support : Covers proposal target) :
    ProperlyWeighted proposal id (fun s => target s / proposal.1 s) target where
  nonnegative s := div_nonneg (nonneg s) (proposal.2.1 s)
  integral f := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : target s = 0
    · simp [h]
    · have hp := support s h
      dsimp only [id_eq]
      field_simp

variable [Fintype A] [Fintype B]

/-- A backward auxiliary kernel is normalized over the discarded coordinate.
The extended target must be dominated by the joint proposal, not conversely. -/
theorem auxiliary_importance (proposal : Prob (S × A)) (target : S → ℝ)
    (backward : S → Prob A) (nonneg : ∀ s, 0 ≤ target s)
    (support : Covers proposal (fun sa => target sa.1 * (backward sa.1).1 sa.2)) :
    ProperlyWeighted proposal Prod.fst
      (fun sa => target sa.1 * (backward sa.1).1 sa.2 / proposal.1 sa) target where
  nonnegative sa := div_nonneg (mul_nonneg (nonneg _) ((backward _).2.1 _)) (proposal.2.1 _)
  integral f := by
    have h := (importance proposal _ (fun sa => mul_nonneg (nonneg _) ((backward _).2.1 _)) support).integral
      (fun sa => f sa.1)
    simp only [id_eq] at h
    rw [h, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    simp_rw [mul_right_comm (target s)]
    rw [← Finset.mul_sum, (backward s).2.2, mul_one]

/-- Append a proposed coordinate to a properly weighted history. -/
theorem extend (p : Prob Ω) (output : Ω → S) (weight : Ω → ℝ) (target : S → ℝ)
    (proper : ProperlyWeighted p output weight target) (proposal : S → Prob A)
    (factor : S → A → ℝ) (nonneg : ∀ s a, 0 ≤ factor s a)
    (support : ∀ s, Covers (proposal s) (factor s)) :
    ProperlyWeighted (joint p (fun ω => proposal (output ω)))
      (fun wa => (output wa.1, wa.2))
      (fun wa => weight wa.1 * (factor (output wa.1) wa.2 / (proposal (output wa.1)).1 wa.2))
      (fun sa => target sa.1 * factor sa.1 sa.2) where
  nonnegative wa := mul_nonneg (proper.nonnegative _) (div_nonneg (nonneg _ _) ((proposal _).2.1 _))
  integral f := by
    unfold expectation
    simp only [Fintype.sum_prod_type, joint_apply]
    have inner (ω : Ω) :
        (∑ a, p.1 ω * (proposal (output ω)).1 a *
          (weight ω * (factor (output ω) a / (proposal (output ω)).1 a) * f (output ω, a))) =
        p.1 ω * (weight ω * ∑ a, factor (output ω) a * f (output ω, a)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : factor (output ω) a = 0
      · simp [h]
      · have hp := support (output ω) a h
        field_simp
    simp_rw [inner]
    have hp := proper.integral (fun s => ∑ a, factor s a * f (s, a))
    simp only [expectation] at hp
    rw [hp]
    simp only [Finset.mul_sum, mul_assoc]

/-- Proposals may depend on a recorded past without changing the target. -/
theorem adaptive_importance (history : Prob Ω) (proposal : Ω → Prob S) (target : S → ℝ)
    (nonneg : ∀ s, 0 ≤ target s) (support : ∀ ω, Covers (proposal ω) target) :
    ProperlyWeighted (joint history proposal) Prod.snd
      (fun ws => target ws.2 / (proposal ws.1).1 ws.2) target where
  nonnegative ws := div_nonneg (nonneg _) ((proposal _).2.1 _)
  integral f := by
    unfold expectation
    simp only [Fintype.sum_prod_type, joint_apply, mul_assoc, ← Finset.mul_sum]
    have h (ω : Ω) := (importance (proposal ω) target nonneg (support ω)).integral f
    simp only [expectation, id_eq] at h
    simp_rw [h]
    rw [← Finset.sum_mul, history.2.2, one_mul]

section Batch
variable [Fintype I] [Nonempty I]

noncomputable def batchEstimate (output : Ω → I → S) (weight : Ω → I → ℝ) (f : S → ℝ) (ω : Ω) : ℝ :=
  (∑ i, weight ω i * f (output ω i)) / Fintype.card I

/-- A batch property, allowing dependence between its members. -/
structure ProperBatch (p : Prob Ω) (output : Ω → I → S) (weight : Ω → I → ℝ)
    (target : S → ℝ) : Prop where
  positive_size : 0 < Fintype.card I
  nonnegative : ∀ ω i, 0 ≤ weight ω i
  integral : ∀ f, expectation p (batchEstimate output weight f) = ∑ s, target s * f s

theorem properBatch_of_members (p : Prob Ω) (output : Ω → I → S) (weight : Ω → I → ℝ)
    (target : S → ℝ) (members : ∀ i, ProperlyWeighted p (output · i) (weight · i) target) :
    ProperBatch p output weight target where
  positive_size := Fintype.card_pos
  nonnegative ω i := (members i).nonnegative ω
  integral f := by
    unfold expectation batchEstimate
    simp only [← mul_div_assoc, Finset.mul_sum]
    rw [← Finset.sum_div, Finset.sum_comm]
    have h (i : I) := (members i).integral f
    simp only [expectation] at h
    simp_rw [h]
    simp [Fintype.card_ne_zero]

omit [Fintype S] in
/-- Expected offspring counts are sufficient for unbiased resampling. The
offspring may be dependent; no independent-sample variance law is inferred. -/
theorem resampling_of_offspring_counts [DecidableEq I] (p : Prob A)
    (parent : A → I → I) (z : I → S) (w : I → ℝ)
    (positive : 0 < ∑ i, w i)
    (counts : ∀ i, expectation p (fun a => ∑ j, if parent a j = i then (1 : ℝ) else 0) =
      (Fintype.card I : ℝ) * w i / ∑ j, w j) (f : S → ℝ) :
    expectation p (batchEstimate (fun a j => z (parent a j))
      (fun _ _ => (∑ i, w i) / Fintype.card I) f) =
      (∑ i, w i * f (z i)) / Fintype.card I := by
  have nc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := I)
  let mean : ℝ := (∑ i, w i) / Fintype.card I
  change expectation p (batchEstimate (fun a j => z (parent a j)) (fun _ _ => mean) f) = _
  have partition (a : A) : (∑ j, mean * f (z (parent a j))) =
        ∑ i, (∑ j, if parent a j = i then (1 : ℝ) else 0) * mean * f (z i) := by
    symm
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp [ite_mul]
  unfold expectation batchEstimate
  simp_rw [partition]
  simp only [Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have eq : (∑ a, p.1 a *
      ((∑ j, if parent a j = i then (1 : ℝ) else 0) * mean * f (z i) / Fintype.card I)) =
      expectation p (fun a => ∑ j, if parent a j = i then (1 : ℝ) else 0) *
        mean * f (z i) / Fintype.card I := by
    simp only [expectation, Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    simp only [← Finset.sum_mul, ← Finset.sum_div]
    ring
  rw [eq, counts]
  dsimp only [mean]
  field_simp [nc, positive.ne']

omit [Nonempty I] in
/-- General conditional criterion: the resampling law preserves the original
batch's unnormalized average measure. It does not require independent offspring. -/
theorem resample_by_conditional_mean (p : Prob Ω) (kernel : Ω → Prob A)
    (output : Ω → I → S) (weight : Ω → I → ℝ) (target : S → ℝ)
    (proper : ProperBatch p output weight target)
    (newOutput : A → I → S) (newWeight : A → I → ℝ)
    (nonneg : ∀ a i, 0 ≤ newWeight a i)
    (conditional : ∀ ω f, expectation (kernel ω) (batchEstimate newOutput newWeight f) =
      batchEstimate output weight f ω) :
    ProperBatch (Prob.bind p kernel) newOutput newWeight target where
  positive_size := proper.positive_size
  nonnegative := nonneg
  integral f := by
    rw [expectation, Prob.expectation_bind]
    change expectation p (fun ω => expectation (kernel ω) (batchEstimate newOutput newWeight f)) = _
    simp_rw [conditional]
    exact proper.integral f

omit [Nonempty I] in
/-- Reindex a complete weighted batch through a declared observation. -/
theorem ProperBatch.map [DecidableEq B]
    {p : Prob Ω} {output : Ω → I → S} {weight : Ω → I → ℝ} {target : S → ℝ}
    (proper : ProperBatch p output weight target) (view : S → B) :
    ProperBatch p (fun ω i => view (output ω i)) weight
      (Mettapedia.InformationTheory.FiniteRV.pushforward target view) where
  positive_size := proper.positive_size
  nonnegative := proper.nonnegative
  integral f := by
    rw [show expectation p (batchEstimate (fun ω i => view (output ω i)) weight f) =
      ∑ s, target s * f (view s) from proper.integral (f ∘ view)]
    exact (Mettapedia.InformationTheory.FiniteRV.sum_pushforward_mul target view f).symm

end Batch

/-- An independently drawn pair is an importance sample on the product carrier.
Zero targets represent pairs that do not join; they remain in the population. -/
theorem pair_importance (left : Prob S) (right : Prob A) (target : S × A → ℝ)
    (nonneg : ∀ sa, 0 ≤ target sa) (support : Covers (joint left (fun _ => right)) target) :
    ProperlyWeighted (joint left (fun _ => right)) id
      (fun sa => target sa / (left.1 sa.1 * right.1 sa.2)) target :=
  importance _ target nonneg support

/-- Grouping by the meeting key preserves the sum over all compatible pairs. -/
theorem grouped_pair_sum [Fintype I] [Fintype J] [DecidableEq B]
    (keyLeft : I → B) (keyRight : J → B) (left : I → ℝ) (right : J → ℝ) :
    (∑ i, ∑ j, if keyLeft i = keyRight j then left i * right j else 0) =
      ∑ b, (∑ i, if keyLeft i = b then left i else 0) *
        (∑ j, if keyRight j = b then right j else 0) := by
  classical
  symm
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [Finset.mul_sum, eq_comm]

noncomputable def defensiveMixture (base guide : Prob S) (ε : ℝ) (hε : 0 ≤ ε) (h1 : ε ≤ 1) : Prob S :=
  ⟨fun s => ε * base.1 s + (1-ε) * guide.1 s,
    fun s => add_nonneg (mul_nonneg hε (base.2.1 s)) (mul_nonneg (sub_nonneg.mpr h1) (guide.2.1 s)), by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, base.2.2, guide.2.2]
      ring⟩

theorem defensive_weight_bound (base guide : Prob S) (ε C : ℝ) (hε : 0 < ε) (h1 : ε ≤ 1)
    (target : S → ℝ) (nonneg : ∀ s, 0 ≤ target s) (hC : 0 ≤ C)
    (bounded : ∀ s, target s ≤ C * base.1 s) (s : S) :
    target s / (defensiveMixture base guide ε hε.le h1).1 s ≤ C / ε := by
  have hb := base.2.1 s
  have hg := guide.2.1 s
  change target s / (ε * base.1 s + (1-ε) * guide.1 s) ≤ _
  by_cases hp : base.1 s = 0
  · have hz : target s = 0 := le_antisymm (by simpa [hp] using bounded s) (nonneg s)
    simp [hz, div_nonneg hC hε.le]
  · have bp : 0 < base.1 s := lt_of_le_of_ne hb (Ne.symm hp)
    have lower : ε * base.1 s ≤ ε * base.1 s + (1-ε) * guide.1 s := le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr h1) hg)
    have denom : 0 < ε * base.1 s + (1-ε) * guide.1 s := (mul_pos hε bp).trans_le lower
    apply (div_le_div_iff₀ denom hε).mpr
    calc
      target s * ε ≤ (C * base.1 s) * ε := mul_le_mul_of_nonneg_right (bounded s) hε.le
      _ ≤ C * (ε * base.1 s + (1-ε) * guide.1 s) := by nlinarith

theorem defensive_covers (base guide : Prob S) (ε : ℝ) (hε : 0 < ε) (h1 : ε ≤ 1)
    (target : S → ℝ) (support : Covers base target) :
    Covers (defensiveMixture base guide ε hε.le h1) target := by
  intro s hs
  have bp : 0 < base.1 s := lt_of_le_of_ne (base.2.1 s) (Ne.symm (support s hs))
  exact ne_of_gt (add_pos_of_pos_of_nonneg (mul_pos hε bp)
    (mul_nonneg (sub_nonneg.mpr h1) (guide.2.1 s)))

/-- Pushforward is a change of observation, not a change of sampling weights. -/
theorem ProperlyWeighted.map [DecidableEq B]
    {p : Prob Ω} {output : Ω → S} {weight : Ω → ℝ} {target : S → ℝ}
    (proper : ProperlyWeighted p output weight target) (view : S → B) :
    ProperlyWeighted p (view ∘ output) weight (Mettapedia.InformationTheory.FiniteRV.pushforward target view) where
  nonnegative := proper.nonnegative
  integral f := by
    rw [show expectation p (fun ω => weight ω * f ((view ∘ output) ω)) =
      ∑ s, target s * f (view s) from proper.integral (f ∘ view)]
    exact (Mettapedia.InformationTheory.FiniteRV.sum_pushforward_mul target view f).symm

section Joining
variable [DecidableEq A]

def joinTarget (join : S → Option A) (target : A → ℝ) (s : S) : ℝ :=
  match join s with | none => 0 | some a => target a

omit [Fintype A] in
/-- Unique splitting prevents a trace being counted once per decomposition. -/
theorem joinTarget_pushforward (join : S → Option A) (split : A → S)
    (roundtrip : ∀ a, join (split a) = some a)
    (unique : ∀ s a, join s = some a → s = split a) (target : A → ℝ) :
    Mettapedia.InformationTheory.FiniteRV.pushforward (joinTarget join target) join =
      fun a => match a with | none => 0 | some x => target x := by
  classical
  funext a
  rw [Mettapedia.InformationTheory.FiniteRV.pushforward_eq_sum_ite]
  cases a with
  | none =>
    apply Finset.sum_eq_zero
    intro s _
    by_cases h : join s = none <;> simp [h, joinTarget]
  | some a =>
    rw [Finset.sum_eq_single (split a)]
    · simp [joinTarget, roundtrip]
    · intro s _ different
      have no : join s ≠ some a := fun h => different (unique s a h)
      simp [no]
    · simp

theorem joined_importance (q : Prob S) (join : S → Option A) (split : A → S)
    (roundtrip : ∀ a, join (split a) = some a)
    (unique : ∀ s a, join s = some a → s = split a) (target : A → ℝ)
    (nonneg : ∀ a, 0 ≤ target a) (support : Covers q (joinTarget join target)) :
    ProperlyWeighted q join (fun s => joinTarget join target s / q.1 s)
      (fun a => match a with | none => 0 | some x => target x) := by
  have hn (s : S) : 0 ≤ joinTarget join target s := by
    unfold joinTarget
    cases join s <;> simp_all
  have h := (importance q (joinTarget join target) hn support).map join
  simpa only [Function.comp_id, joinTarget_pushforward join split roundtrip unique] using h

end Joining

namespace Controls
noncomputable def fair : Prob Bool :=
  ⟨fun _ => 1/2, fun _ => by norm_num, by norm_num⟩

/-- Support in the reverse direction permits loss of half the target mass. -/
theorem auxiliary_reverse_support_failure :
    (∀ u : Bool, (Prob.dirac false).1 u ≠ 0 → fair.1 u ≠ 0) ∧
    expectation (Prob.dirac false) (fun u => fair.1 u / (Prob.dirac false).1 u) = 1/2 := by
  constructor
  · intro u _; norm_num [fair]
  · norm_num [expectation, fair, Prob.dirac]

/-- Selecting the larger of two valid unit-weight samples changes the law. -/
theorem selection_bias :
    expectation (joint fair (fun _ => fair)) (fun b => if b.1 || b.2 then 1 else 0) = 3/4 ∧
    expectation fair (fun b => if b then 1 else 0) = 1/2 := by
  norm_num [expectation, joint, fair, Fintype.sum_prod_type]

/-- Reusing one fair bit twice has twice the variance of two independent bits. -/
theorem dependence_changes_variance :
    expectation fair (fun b => ((if b then (1 : ℝ) else 0) - 1/2)^2) = 1/4 ∧
    expectation (joint fair (fun _ => fair))
      (fun b => (((if b.1 then (1 : ℝ) else 0) + (if b.2 then 1 else 0))/2 - 1/2)^2) = 1/8 := by
  norm_num [expectation, joint, fair, Fintype.sum_prod_type]

/-- Four all-pairs outputs reuse two left draws. For a query of the left
coordinate their variance is twice that of four fresh independent draws. -/
theorem paired_population_variance :
    let law := joint (joint fair (fun _ => fair)) (fun _ => joint fair (fun _ => fair))
    expectation law (fun ab =>
      ((∑ i : Bool, ∑ _j : Bool,
          if (if i then ab.1.1 else ab.1.2) then (1 : ℝ) else 0)/4-1/2)^2) = 1/8 ∧
    expectation law (fun ab =>
      (((if ab.1.1 then (1 : ℝ) else 0) + (if ab.1.2 then 1 else 0) +
        (if ab.2.1 then 1 else 0) + (if ab.2.2 then 1 else 0))/4-1/2)^2) = 1/16 := by
  norm_num [expectation, joint, fair, Fintype.sum_prod_type]

/-- A finite batch may miss all target support despite its positive mass. -/
theorem zero_sample_not_zero_target :
    (fair.1 false > 0) ∧ ((if false then (1 : ℝ) else 0) / fair.1 false = 0) ∧
    (∑ b : Bool, if b then (1 : ℝ) else 0) = 1 := by norm_num [fair]

/-- Two samples can both miss positive evidence. Their occurrence remains in
the original denominator; deleting them is not an unbiased transformation. -/
theorem all_zero_batch_possible :
    (joint fair (fun _ => fair)).1 (false,false) = 1/4 ∧
    batchEstimate (fun b (i : Bool) => if i then b.1 else b.2)
      (fun b (i : Bool) => if (if i then b.1 else b.2) then (2 : ℝ) else 0)
      (fun _ : Bool => 1) (false,false) = 0 ∧
    (∑ b : Bool, if b then (1 : ℝ) else 0) = 1 := by
  norm_num [joint, fair, batchEstimate]

/-- Equal carriers and result types do not certify equal model laws. -/
theorem same_type_different_model :
    expectation fair (fun b => if b then (1 : ℝ) else 0) = 1/2 ∧
    expectation (Prob.dirac true) (fun b => if b then (1 : ℝ) else 0) = 1 := by
  norm_num [expectation, fair, Prob.dirac]

/-- A density-score ratio alone does not make an arbitrary trace replacement
an invariant transition. A constant replacement loses a fair bit even though
the old and new target scores are equal. -/
theorem density_ratio_not_transition :
    (∀ b : Bool, fair.1 true / fair.1 b = 1) ∧
    expectation fair (fun b => (fair.1 true / fair.1 b) * (1 : ℝ)) = 1 ∧
    expectation fair (fun b => if b then (1 : ℝ) else 0) = 1/2 := by
  norm_num [expectation, fair]

/-- An unbiased density estimate cannot simply be reciprocated. -/
theorem reciprocal_bias :
    expectation fair (fun b => if b then (1/4 : ℝ) else 3/4) = 1/2 ∧
    expectation fair (fun b => 1 / (if b then (1/4 : ℝ) else 3/4)) = 8/3 := by
  norm_num [expectation, fair]

/-- One self-normalized importance sample is generally biased even when the
unnormalized estimator is properly weighted. -/
theorem self_normalized_bias :
    expectation fair (fun b =>
      ((if b then (3/2 : ℝ) else 1/2) * if b then 1 else 0) /
        (if b then (3/2 : ℝ) else 1/2)) = 1/2 ∧ (1/2 : ℝ) ≠ 3/4 := by
  norm_num [expectation, fair]

noncomputable def jointMass (b : Bool × Bool) : ℝ :=
  if b.1 then 3/10 else if b.2 then 4/10 else 0

/-- Summation preserves a marginal, but changes which first coordinate is most
probable compared with the coordinate of the joint mode. -/
theorem marginalization_changes_mode :
    (∀ b, jointMass b ≤ jointMass (false,true)) ∧
    (∑ b : Bool, jointMass (true,b)) > ∑ b : Bool, jointMass (false,b) := by
  constructor
  · rintro ⟨a,b⟩; cases a <;> cases b <;> norm_num [jointMass]
  · norm_num [jointMass]

end Controls

end Mettapedia.ProbabilityTheory.WeightedInference
