import Mettapedia.ProbabilityTheory.BayesianInference.Information
import Mettapedia.InformationTheory.FiniteProbability

/-!
# Coarsening and the sequential information law

Expected information gain is the mutual information of the latent state and the
observation. A map of the observation pushes that joint law forward, so the
gain cannot increase. Two likelihood kernels of one latent state split by the
chain rule `I(S; O1, O2) = I(S; O1) + I(S; O2 | O1)`.

Collapsing a perfectly observed fair bit to one point drops the gain from
`log 2` to zero.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference

open Finset Real
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.InformationTheory.Prob

section DataProcessing

variable {Ω α γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype γ]
  [DecidableEq α] [DecidableEq γ] [DecidableEq δ]

/-- The joint law of `(f, ψ ∘ h)` is the pushforward of the joint law of `(f, h)`. -/
theorem law2_map_right (p : Ω → ℝ) (f : Ω → α) (h : Ω → γ) (ψ : γ → δ) :
    law2 p f (ψ ∘ h) =
      pushforward (law2 p f h) (fun y : α × γ => (y.1, ψ y.2)) := by
  funext x
  unfold law2
  rw [pushforward_pushforward p (fun ω => (f ω, h ω)) (fun y => (y.1, ψ y.2)) x]
  rfl

/-- Pushing the product of the `f` and `h` marginals along `ψ` multiplies the pushed marginals. -/
theorem pushforward_prod_marginal (p : Ω → ℝ) (f : Ω → α) (h : Ω → γ) (ψ : γ → δ)
    (x : α × δ) :
    pushforward (fun y : α × γ => pushforward p f y.1 * pushforward p h y.2)
        (fun y => (y.1, ψ y.2)) x =
      pushforward p f x.1 * pushforward p (ψ ∘ h) x.2 := by
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type, Finset.sum_comm]
  dsimp only
  rw [← pushforward_pushforward p h ψ x.2]
  rw [pushforward_eq_sum_ite (pushforward p h) ψ x.2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : ψ c = x.2
  · rw [if_pos hc]
    have hcond : ∀ a, ((a, ψ c) = x) ↔ a = x.1 := by
      intro a
      constructor
      · intro hax
        exact (Prod.ext_iff.mp hax).1
      · intro ha
        have hx : (x.1, x.2) = x := Prod.mk.eta
        rw [← hx]
        exact Prod.ext ha hc
    simp_rw [hcond]
    rw [Finset.sum_ite_eq' Finset.univ x.1
        (fun a => pushforward p f a * pushforward p h c), if_pos (Finset.mem_univ _)]
  · rw [if_neg hc, mul_zero]
    refine Finset.sum_eq_zero fun a _ => ?_
    exact if_neg fun hax => hc ((Prod.ext_iff.mp hax).2)

variable [Fintype δ] in
/-- A function of the second argument cannot increase mutual information. -/
theorem mutualInfo_map_right_le (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (h : Ω → γ)
    (ψ : γ → δ) :
    mutualInfo p f (ψ ∘ h) ≤ mutualInfo p f h := by
  unfold mutualInfo
  rw [law2_map_right p f h ψ]
  have hq :
      pushforward (fun y : α × γ => pushforward p f y.1 * pushforward p h y.2)
          (fun y => (y.1, ψ y.2)) =
        fun x : α × δ => pushforward p f x.1 * pushforward p (ψ ∘ h) x.2 := by
    funext x
    exact pushforward_prod_marginal p f h ψ x
  rw [← hq]
  exact klSum_pushforward_le (law2 p f h)
    (fun y => pushforward p f y.1 * pushforward p h y.2)
    (fun y => (y.1, ψ y.2))
    (fun y => pushforward_nonneg p hp (fun ω => (f ω, h ω)) y)
    (fun y => mul_nonneg (pushforward_nonneg p hp f y.1) (pushforward_nonneg p hp h y.2))
    (fun y hy => mul_pos
      (lt_of_lt_of_le hy (law2_le_pushforward_fst p hp f h y))
      (lt_of_lt_of_le hy (law2_le_pushforward_snd p hp f h y)))

end DataProcessing

/-- Mutual information is unchanged by presenting its sample through a map. -/
theorem mutualInfo_of_pushforward
    {Ω Ω' α γ : Type*} [Fintype Ω] [Fintype Ω'] [Fintype α] [Fintype γ]
    [DecidableEq Ω'] [DecidableEq α] [DecidableEq γ]
    (p : Ω → ℝ) (φ : Ω → Ω') (f : Ω' → α) (g : Ω' → γ) :
    mutualInfo (pushforward p φ) f g = mutualInfo p (f ∘ φ) (g ∘ φ) := by
  unfold mutualInfo
  have hlaw : law2 (pushforward p φ) f g = law2 p (f ∘ φ) (g ∘ φ) := by
    funext x
    unfold law2
    rw [pushforward_pushforward]
    rfl
  have hprod :
      (fun x : α × γ =>
        pushforward (pushforward p φ) f x.1 * pushforward (pushforward p φ) g x.2) =
      fun x => pushforward p (f ∘ φ) x.1 * pushforward p (g ∘ φ) x.2 := by
    funext x
    rw [pushforward_pushforward, pushforward_pushforward]
  rw [hlaw, hprod]

/-- The joint law of a coarsened observation kernel is the observation pushforward of the joint. -/
theorem joint_coarsen_eq_pushforward
    {S O C : Type*} [Fintype S] [Fintype O] [Fintype C]
    [DecidableEq S] [DecidableEq O] [DecidableEq C]
    (prior : Prob S) (likelihood : S → Prob O) (view : O → C) :
    (joint prior (fun s => coarsen (likelihood s) view)).1 =
      pushforward (joint prior likelihood).1 (fun so => (so.1, view so.2)) := by
  funext sc
  calc
    (joint prior (fun s => coarsen (likelihood s) view)).1 sc
      = prior.1 sc.1 * ∑ o, if view o = sc.2 then (likelihood sc.1).1 o else 0 := by
          rw [joint_apply, coarsen_apply, pushforward_eq_sum_ite]
    _ = ∑ o, prior.1 sc.1 * (if view o = sc.2 then (likelihood sc.1).1 o else 0) := by
          rw [Finset.mul_sum]
    _ = ∑ o, ∑ s, if (s, view o) = sc then prior.1 s * (likelihood s).1 o else 0 := by
          refine Finset.sum_congr rfl fun o _ => ?_
          by_cases ho : view o = sc.2
          · rw [if_pos ho]
            have hcond : ∀ s, ((s, view o) = sc) ↔ s = sc.1 := by
              intro s
              constructor
              · intro h
                exact (Prod.ext_iff.mp h).1
              · intro hs
                have hsc : (sc.1, sc.2) = sc := Prod.mk.eta
                rw [← hsc]
                exact Prod.ext hs ho
            simp_rw [hcond]
            rw [Finset.sum_ite_eq' Finset.univ sc.1
                (fun s => prior.1 s * (likelihood s).1 o), if_pos (Finset.mem_univ _)]
          · rw [if_neg ho, mul_zero]
            symm
            refine Finset.sum_eq_zero fun s _ => ?_
            exact if_neg fun h => ho ((Prod.ext_iff.mp h).2)
    _ = pushforward (joint prior likelihood).1 (fun so => (so.1, view so.2)) sc := by
          rw [pushforward_eq_sum_ite, Fintype.sum_prod_type, Finset.sum_comm]
          simp_rw [joint_apply]

/-- Coarsening the observation cannot increase expected information gain. -/
theorem expectedInformationGain_coarsen_le
    {S O C : Type*} [Fintype S] [Fintype O] [Fintype C]
    [DecidableEq S] [DecidableEq O] [DecidableEq C]
    (prior : Prob S) (likelihood : S → Prob O) (view : O → C) :
    expectedInformationGain prior (fun s => coarsen (likelihood s) view) ≤
      expectedInformationGain prior likelihood := by
  rw [expectedInformationGain_eq_mutualInfo, expectedInformationGain_eq_mutualInfo,
    joint_coarsen_eq_pushforward]
  rw [mutualInfo_of_pushforward (joint prior likelihood).1
    (fun so => (so.1, view so.2)) Prod.fst Prod.snd]
  have hfst : Prod.fst ∘ (fun so : S × O => (so.1, view so.2)) = Prod.fst := by
    funext so
    rfl
  have hsnd : Prod.snd ∘ (fun so : S × O => (so.1, view so.2)) = view ∘ Prod.snd := by
    funext so
    rfl
  rw [hfst, hsnd]
  exact mutualInfo_map_right_le (joint prior likelihood).1 (joint prior likelihood).2.1
    Prod.fst Prod.snd view

section ChainRule

variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Pair mutual information lifts to the triple by summing out the unused coordinate. -/
theorem mutualInfo_eq_sum_law3 (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    mutualInfo p f g =
      ∑ x : α × β × γ, law3 p f g h x *
        Real.log (law2 p f g (x.1, x.2.1) /
          (pushforward p f x.1 * pushforward p g x.2.1)) := by
  rw [mutualInfo, klSum_eq_sum]
  conv_lhs =>
    rw [Fintype.sum_prod_type]
    dsimp only
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  generalize hL : Real.log (law2 p f g (a, b) /
    (pushforward p f a * pushforward p g b)) = L
  clear hL
  rw [← sum_law3_right p f g h a b, Finset.sum_mul]

/-- `I(f ; g, h) = I(f ; g) + I(f ; h | g)`. -/
theorem mutualInfo_pair_eq (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → α) (g : Ω → β)
    (h : Ω → γ) :
    mutualInfo p f (fun ω => (g ω, h ω)) =
      mutualInfo p f g + condMutualInfo p f g h := by
  have hlaw : law2 p f (fun ω => (g ω, h ω)) = law3 p f g h := rfl
  have hmarg : pushforward p (fun ω => (g ω, h ω)) = law2 p g h := rfl
  rw [mutualInfo_eq_sum_law3 p f g h, condMutualInfo, ← Finset.sum_add_distrib]
  rw [mutualInfo, hlaw, klSum_eq_sum, hmarg]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx2 : law2 p g h x.2 = law2 p g h (x.2.1, x.2.2) :=
    congr_arg (law2 p g h) Prod.mk.eta.symm
  rw [hx2]
  have hnn : 0 ≤ law3 p f g h x :=
    pushforward_nonneg p hp (fun ω => (f ω, g ω, h ω)) x
  rcases hnn.lt_or_eq with hpos | hzero
  · have hLfg : 0 < law2 p f g (x.1, x.2.1) :=
      lt_of_lt_of_le hpos (law3_le_law2_fg p hp f g h x)
    have hLgh : 0 < law2 p g h (x.2.1, x.2.2) :=
      lt_of_lt_of_le hpos (law3_le_law2_gh p hp f g h x)
    have hpA : 0 < pushforward p f x.1 :=
      lt_of_lt_of_le hLfg (law2_le_pushforward_fst p hp f g (x.1, x.2.1))
    have hpB : 0 < pushforward p g x.2.1 :=
      lt_of_lt_of_le hLfg (law2_le_pushforward_snd p hp f g (x.1, x.2.1))
    have hA : law2 p f g (x.1, x.2.1) /
        (pushforward p f x.1 * pushforward p g x.2.1) ≠ 0 :=
      div_ne_zero hLfg.ne' (mul_ne_zero hpA.ne' hpB.ne')
    have hB : law3 p f g h x * pushforward p g x.2.1 /
        (law2 p f g (x.1, x.2.1) * law2 p g h (x.2.1, x.2.2)) ≠ 0 :=
      div_ne_zero (mul_ne_zero hpos.ne' hpB.ne') (mul_ne_zero hLfg.ne' hLgh.ne')
    have hprod :
        (law2 p f g (x.1, x.2.1) / (pushforward p f x.1 * pushforward p g x.2.1)) *
          (law3 p f g h x * pushforward p g x.2.1 /
            (law2 p f g (x.1, x.2.1) * law2 p g h (x.2.1, x.2.2))) =
        law3 p f g h x /
          (pushforward p f x.1 * law2 p g h (x.2.1, x.2.2)) := by
      rw [div_mul_div_comm]
      rw [div_eq_div_iff
        (mul_ne_zero (mul_ne_zero hpA.ne' hpB.ne') (mul_ne_zero hLfg.ne' hLgh.ne'))
        (mul_ne_zero hpA.ne' hLgh.ne')]
      ring
    rw [← mul_add, ← Real.log_mul hA hB, hprod]
  · have hz : law3 p f g h x = 0 := hzero.symm
    rw [hz]
    simp only [zero_mul, add_zero]

end ChainRule

/-- The joint law of a latent state and two likelihood kernels, the second read from the state. -/
noncomputable def successiveJoint {S O1 O2 : Type*} [Fintype S] [Fintype O1] [Fintype O2]
    (prior : Prob S) (first : S → Prob O1) (second : S → Prob O2) :
    Prob ((S × O1) × O2) :=
  joint (joint prior first) (fun so => second so.1)

@[simp] theorem successiveJoint_apply {S O1 O2 : Type*} [Fintype S] [Fintype O1] [Fintype O2]
    (prior : Prob S) (first : S → Prob O1) (second : S → Prob O2) (s : S) (o1 : O1) (o2 : O2) :
    (successiveJoint prior first second).1 ((s, o1), o2) =
      prior.1 s * (first s).1 o1 * (second s).1 o2 := by
  simp [successiveJoint, joint_apply]

theorem pushforward_fst_sum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (p : A × B → ℝ) (a : A) :
    pushforward p Prod.fst a = ∑ b, p (a, b) := by
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ ha'
    apply Finset.sum_eq_zero
    intro b _
    simp [ha']
  · intro h
    exact (h (Finset.mem_univ a)).elim

theorem successive_law2_state_observation
    {S O1 O2 : Type*} [Fintype S] [Fintype O1] [Fintype O2]
    [DecidableEq S] [DecidableEq O1] [DecidableEq O2]
    (prior : Prob S) (first : S → Prob O1) (second : S → Prob O2) :
    law2 (successiveJoint prior first second).1 (fun x => x.1.1) (fun x => x.1.2) =
      (joint prior first).1 := by
  funext y
  unfold law2
  have hproj : (fun x : (S × O1) × O2 => (x.1.1, x.1.2)) = Prod.fst := by
    funext x
    exact Prod.mk.eta
  rw [hproj, pushforward_fst_sum]
  exact joint_latent_marginal (joint prior first) (fun so => second so.1) y

theorem successive_push_state
    {S O1 O2 : Type*} [Fintype S] [Fintype O1] [Fintype O2]
    [DecidableEq S] [DecidableEq O1] [DecidableEq O2]
    (prior : Prob S) (first : S → Prob O1) (second : S → Prob O2) :
    pushforward (successiveJoint prior first second).1 (fun x => x.1.1) = prior.1 := by
  funext s
  rw [← sum_law2_right (successiveJoint prior first second).1
      (fun x => x.1.1) (fun x => x.1.2) s, successive_law2_state_observation]
  exact joint_latent_marginal prior first s

theorem successive_push_observation
    {S O1 O2 : Type*} [Fintype S] [Fintype O1] [Fintype O2]
    [DecidableEq S] [DecidableEq O1] [DecidableEq O2]
    (prior : Prob S) (first : S → Prob O1) (second : S → Prob O2) :
    pushforward (successiveJoint prior first second).1 (fun x => x.1.2) =
      (observationLaw prior first).1 := by
  funext o
  rw [← sum_law2_left (successiveJoint prior first second).1
      (fun x => x.1.1) (fun x => x.1.2) o, successive_law2_state_observation]
  exact joint_observation_marginal prior first o

theorem successive_mutualInfo_state_observation
    {S O1 O2 : Type*} [Fintype S] [Fintype O1] [Fintype O2]
    [DecidableEq S] [DecidableEq O1] [DecidableEq O2]
    (prior : Prob S) (first : S → Prob O1) (second : S → Prob O2) :
    mutualInfo (successiveJoint prior first second).1 (fun x => x.1.1) (fun x => x.1.2) =
      expectedInformationGain prior first := by
  rw [expectedInformationGain_eq_mutualInfo, mutualInfo, mutualInfo,
    successive_law2_state_observation, successive_push_state, successive_push_observation,
    joint_law2, joint_pushforward_fst, joint_pushforward_snd]

/-- For two likelihoods of one latent state, `I(S; O1, O2) = I(S; O1) + I(S; O2 | O1)`. -/
theorem successive_information_chain
    {S O1 O2 : Type*} [Fintype S] [Fintype O1] [Fintype O2]
    [DecidableEq S] [DecidableEq O1] [DecidableEq O2]
    (prior : Prob S) (first : S → Prob O1) (second : S → Prob O2) :
    mutualInfo (successiveJoint prior first second).1 (fun x => x.1.1)
        (fun x => (x.1.2, x.2)) =
      expectedInformationGain prior first +
        condMutualInfo (successiveJoint prior first second).1
          (fun x => x.1.1) (fun x => x.1.2) (fun x => x.2) := by
  rw [mutualInfo_pair_eq (successiveJoint prior first second).1
      (successiveJoint prior first second).2.1
      (fun x => x.1.1) (fun x => x.1.2) (fun x => x.2),
    successive_mutualInfo_state_observation]

/-! ## Lossy coarsening -/

/-- An observation kernel that ignores the latent state has the observation as its marginal. -/
theorem observationLaw_const {S O : Type*} [Fintype S] [Fintype O]
    (prior : Prob S) (obs : Prob O) :
    observationLaw prior (fun _ => obs) = obs := by
  apply Subtype.ext
  funext o
  rw [observationLaw_apply, evidence, ← Finset.sum_mul, prior.2.2, one_mul]

/-- A state-independent observation carries no expected information about the state. -/
theorem expectedInformationGain_const {S O : Type*} [Fintype S] [Fintype O]
    (prior : Prob S) (obs : Prob O) :
    expectedInformationGain prior (fun _ => obs) = 0 := by
  rw [expectedInformationGain_eq_joint_divergence]
  have hlaw : (fun so => prior.1 so.1 * (observationLaw prior (fun _ => obs)).1 so.2) =
      (joint prior (fun _ => obs)).1 := by
    funext so
    rw [joint_apply, observationLaw_const]
  rw [hlaw]
  exact klSum_self_eq_zero _ (joint prior (fun _ => obs)).2.1

/-- Every distribution pushed along the unique map into `Unit` is the point mass. -/
theorem coarsen_constant_unit {S : Type*} [Fintype S] (prior : Prob S) :
    coarsen prior (fun _ : S => ()) = dirac () := by
  apply Subtype.ext
  funext u
  have hone (q : Prob Unit) : q.1 u = 1 := by
    have hsum : ∑ x, q.1 x = 1 := q.2.2
    rwa [Fintype.sum_subsingleton q.1 u] at hsum
  rw [hone (coarsen prior (fun _ : S => ())), hone (dirac ())]

theorem shannonEntropyFin_dirac {α : Type*} [Fintype α] [DecidableEq α] (state : α) :
    shannonEntropyFin α (dirac state) = 0 := by
  unfold shannonEntropyFin
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases h : a = state
  · simp [h, dirac_apply, negMulLog_one]
  · simp [h, dirac_apply, negMulLog_zero]

theorem shannonEntropyFin_binaryUniform :
    shannonEntropyFin (Fin 2) binaryUniform = Real.log 2 := by
  unfold shannonEntropyFin
  rw [Fin.sum_univ_two, binaryUniform_apply_zero, binaryUniform_apply_one]
  simp only [negMulLog]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

/-- A perfect observation of a fair bit has evidence equal to the prior mass. -/
theorem reveal_evidence (o : Fin 2) :
    evidence binaryUniform (fun s => (dirac s).1 o) = binaryUniform.1 o := by
  unfold evidence
  rw [Finset.sum_eq_single o]
  · simp [dirac_apply]
  · intro s _ hs
    have : o ≠ s := fun h => hs h.symm
    simp [dirac_apply, this]
  · intro h
    exact (h (Finset.mem_univ o)).elim

theorem reveal_posterior (o : Fin 2)
    (possible : 0 < evidence binaryUniform (fun s => (dirac s).1 o)) :
    posterior binaryUniform (fun s => (dirac s).1 o) (fun s => (dirac s).2.1 o) possible =
      dirac o := by
  apply Subtype.ext
  funext s
  rw [posterior_apply, reveal_evidence]
  by_cases h : s = o
  · subst h
    have hs : binaryUniform.1 s ≠ 0 := by
      fin_cases s <;> simp [binaryUniform_apply_zero, binaryUniform_apply_one]
    rw [dirac_apply, if_pos rfl, mul_one]
    exact div_self hs
  · rw [dirac_apply, if_neg (Ne.symm h), mul_zero, zero_div, dirac_apply, if_neg h]

theorem expectedPosteriorEntropy_reveal :
    expectedPosteriorEntropy binaryUniform dirac = 0 := by
  have hpos : ∀ o : Fin 2, 0 < evidence binaryUniform (fun s => (dirac s).1 o) := by
    intro o
    rw [reveal_evidence]
    fin_cases o <;> simp [binaryUniform_apply_zero, binaryUniform_apply_one]
  rw [expectedPosteriorEntropy_eq binaryUniform dirac hpos]
  refine Finset.sum_eq_zero fun o _ => ?_
  rw [reveal_posterior o (hpos o), shannonEntropyFin_dirac, mul_zero]

/-- Revealing a fair bit gains exactly `log 2`. -/
theorem reveal_information_eq_log_two :
    expectedInformationGain binaryUniform dirac = Real.log 2 := by
  rw [expectedInformationGain_eq_entropy_sub, expectedPosteriorEntropy_reveal,
    shannonEntropyFin_binaryUniform, sub_zero]

/-- Forgetting which fair bit was revealed removes the whole information gain. -/
theorem lossy_observation_coarsening :
    expectedInformationGain binaryUniform
        (fun s => coarsen (dirac s) (fun _ : Fin 2 => ())) <
      expectedInformationGain binaryUniform dirac := by
  have hkernel :
      (fun s : Fin 2 => coarsen (dirac s) (fun _ : Fin 2 => ())) = fun _ => dirac () := by
    funext s
    exact coarsen_constant_unit (dirac s)
  rw [hkernel, expectedInformationGain_const, reveal_information_eq_log_two]
  exact Real.log_pos (by norm_num)

end Mettapedia.ProbabilityTheory.BayesianInference
