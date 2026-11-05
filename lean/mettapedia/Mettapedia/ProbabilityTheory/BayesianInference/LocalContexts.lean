import Mettapedia.ProbabilityTheory.BayesianInference.Coarsening
import Mathlib.Tactic

/-!
# Bayesian revision in local contexts

Marginalization commutes with conditioning when the likelihood is measurable
through the retained finite observation. Thus a query and its evidence can be
answered in any context realizing their same joint law. No greatest context
is required. Individual marginals alone do not determine this joint law;
agreement on overlaps also need not imply joint extendibility.

The latter is the classical marginal problem (Vorob'ev, 1962,
*Consistent Families of Measures and Their Extensions*).
-/
set_option autoImplicit false
namespace Mettapedia.ProbabilityTheory.BayesianInference.LocalContexts
open Finset Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV

variable {S A B T : Type*} [Fintype S] [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B]

/-- Revision needs the joint query/evidence observation, not all latent data. -/
theorem query_from_joint (p : Prob S) (query : S → A) (obs : S → B) (L : B → ℝ)
    (hn : ∀ b, 0 ≤ L b) (hz : 0 < evidence p (L ∘ obs)) :
    Prob.coarsen (posterior p (L ∘ obs) (fun s => hn (obs s)) hz) query =
      Prob.coarsen (posterior (Prob.coarsen p (fun s => (query s, obs s)))
        (L ∘ Prod.snd) (fun ab => hn ab.2)
        (by simpa only [evidence_coarsen, Function.comp_def] using hz)) Prod.fst := by
  rw [← coarsen_posterior p (fun s => (query s, obs s)) (L ∘ Prod.snd)
    (fun ab => hn ab.2)]
  rw [Prob.coarsen_comp]
  rfl

/-- Two contexts agreeing on the relevant joint marginal agree after revision.
The evidence normalizer, including its zero boundary, is already determined
by that marginal. -/
theorem covering_evidence_agree [Fintype T]
    (p : Prob S) (q : Prob T) (query : S → A) (obs : S → B)
    (query' : T → A) (obs' : T → B) (L : B → ℝ)
    (joint_agreement : Prob.coarsen p (fun s => (query s, obs s)) =
      Prob.coarsen q (fun t => (query' t, obs' t))) :
    evidence p (L ∘ obs) = evidence q (L ∘ obs') := by
  have hp := evidence_coarsen p (fun s => (query s, obs s)) (L ∘ Prod.snd)
  have hq := evidence_coarsen q (fun t => (query' t, obs' t)) (L ∘ Prod.snd)
  rw [joint_agreement] at hp
  exact hp.symm.trans hq

/-- Two contexts agreeing on the relevant joint marginal agree after revision.
The inputs may have different latent carriers and unrelated extra variables. -/
theorem covering_contexts_agree [Fintype T]
    (p : Prob S) (q : Prob T) (query : S → A) (obs : S → B)
    (query' : T → A) (obs' : T → B) (L : B → ℝ) (hn : ∀ b, 0 ≤ L b)
    (joint_agreement : Prob.coarsen p (fun s => (query s, obs s)) =
      Prob.coarsen q (fun t => (query' t, obs' t)))
    (hp : 0 < evidence p (L ∘ obs)) (hq : 0 < evidence q (L ∘ obs')) :
    Prob.coarsen (posterior p (L ∘ obs) (fun s => hn (obs s)) hp) query =
      Prob.coarsen (posterior q (L ∘ obs') (fun t => hn (obs' t)) hq) query' := by
  rw [query_from_joint p query obs L hn hp, query_from_joint q query' obs' L hn hq]
  congr 2

/-- Finite contexts have common enlargements. -/
theorem finite_contexts_directed (s t : Finset Nat) :
    ∃ u : Finset Nat, s ⊆ u ∧ t ⊆ u :=
  ⟨s ∪ t, subset_union_left, subset_union_right⟩

/-- They have no greatest member, without any large-cardinal premise. -/
theorem finite_contexts_no_greatest (s : Finset Nat) : ∃ t : Finset Nat, s ⊂ t := by
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset s
  exact ⟨insert n s, ssubset_insert hn⟩

namespace Controls
noncomputable def fair : Prob Bool :=
  ⟨fun _ => 1/2, fun _ => by norm_num, by norm_num⟩

/-- Equal and opposite couplings have the same individual fair marginals. -/
noncomputable def coupling (equal : Bool) : Prob (Bool × Bool) :=
  ⟨fun ab => if (ab.1 == ab.2) = equal then 1/2 else 0,
    fun ab => by dsimp only; split_ifs <;> norm_num, by cases equal <;> norm_num [Fintype.sum_prod_type]⟩

theorem coupling_marginals (equal : Bool) :
    Prob.coarsen (coupling equal) Prod.fst = fair ∧
      Prob.coarsen (coupling equal) Prod.snd = fair := by
  constructor <;> apply Subtype.ext <;> funext b <;>
    cases equal <;> cases b <;>
    norm_num [Prob.coarsen_apply, pushforward_eq_sum_ite, coupling, fair, Fintype.sum_prod_type]

noncomputable def trueLikelihood (b : Bool) : ℝ := if b then 1 else 0

theorem coupling_possible (equal : Bool) :
    0 < evidence (coupling equal) (trueLikelihood ∘ Prod.snd) := by
  cases equal <;> norm_num [evidence, coupling, trueLikelihood, Fintype.sum_prod_type]

/-- With identical marginals, observing the second bit yields opposite certain
answers for the first bit. Neither coupling is selected by marginal data. -/
theorem coupling_revision (equal : Bool) :
    Prob.coarsen (posterior (coupling equal) (trueLikelihood ∘ Prod.snd)
      (fun ab => by dsimp only [Function.comp_apply, trueLikelihood]; split_ifs <;> norm_num)
      (coupling_possible equal)) Prod.fst = Prob.dirac equal := by
  apply Subtype.ext
  funext b
  cases equal <;> cases b <;>
    norm_num [Prob.coarsen_apply, pushforward_eq_sum_ite, posterior_apply,
      coupling, trueLikelihood, evidence, Prob.dirac, Fintype.sum_prod_type]

/-- A positive pair law with disagreement probability 7/8. -/
noncomputable def noisyAnti : Prob (Bool × Bool) :=
  ⟨fun ab => if ab.1 = ab.2 then 1/16 else 7/16,
    fun ab => by dsimp only; split_ifs <;> norm_num, by norm_num [Fintype.sum_prod_type]⟩

theorem noisyAnti_positive (ab : Bool × Bool) : 0 < noisyAnti.1 ab := by
  dsimp only [noisyAnti]
  split_ifs <;> norm_num

theorem noisyAnti_marginals :
    Prob.coarsen noisyAnti Prod.fst = fair ∧ Prob.coarsen noisyAnti Prod.snd = fair := by
  constructor <;> apply Subtype.ext <;> funext b <;> cases b <;>
    norm_num [Prob.coarsen_apply, pushforward_eq_sum_ite, noisyAnti, fair, Fintype.sum_prod_type]

noncomputable def agreement (p : Prob (Bool × Bool)) : ℝ :=
  ∑ ab, p.1 ab * if ab.1 = ab.2 then 1 else 0

theorem noisyAnti_agreement : agreement noisyAnti = 1/8 := by
  norm_num [agreement, noisyAnti, Fintype.sum_prod_type]

/-- Any three Boolean values have at least one equal pair. This forces a
probability inequality on every joint law, independently of its factorization. -/
theorem triangle_agreement_bound (p : Prob (Bool × Bool × Bool)) :
    1 ≤ agreement (Prob.coarsen p (fun w => (w.1,w.2.1))) +
      agreement (Prob.coarsen p (fun w => (w.2.1,w.2.2))) +
      agreement (Prob.coarsen p (fun w => (w.1,w.2.2))) := by
  simp only [agreement, Prob.coarsen_expectation]
  have point (w : Bool × Bool × Bool) : p.1 w ≤
      p.1 w * (if w.1 = w.2.1 then 1 else 0) +
      p.1 w * (if w.2.1 = w.2.2 then 1 else 0) +
      p.1 w * (if w.1 = w.2.2 then 1 else 0) := by
    have hn := p.2.1 w
    rcases w with ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;> simp_all
  have h := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Bool × Bool × Bool))) => point w)
  simpa only [Finset.sum_add_distrib, p.2.2] using h

/-- The three strictly positive pair laws agree on every overlap, but have no
joint extension. This is the 1/16, 7/16 example, not a zero-support artifact. -/
theorem no_joint_for_noisy_pairs : ¬ ∃ p : Prob (Bool × Bool × Bool),
    Prob.coarsen p (fun w => (w.1,w.2.1)) = noisyAnti ∧
    Prob.coarsen p (fun w => (w.2.1,w.2.2)) = noisyAnti ∧
    Prob.coarsen p (fun w => (w.1,w.2.2)) = noisyAnti := by
  rintro ⟨p, h1, h2, h3⟩
  have h := triangle_agreement_bound p
  rw [h1, h2, h3, noisyAnti_agreement] at h
  norm_num at h

/-- Join two pair charts through their common fair middle marginal. This
selects conditional independence of the endpoints given the middle bit. -/
noncomputable def chainBridge : Prob (Bool × Bool × Bool) :=
  ⟨fun w => 2 * noisyAnti.1 (w.1,w.2.1) * noisyAnti.1 (w.2.1,w.2.2),
    fun w => mul_nonneg (mul_nonneg (by norm_num) (noisyAnti.2.1 _)) (noisyAnti.2.1 _),
    by norm_num [noisyAnti, Fintype.sum_prod_type]⟩

theorem chainBridge_preserves_two_charts :
    Prob.coarsen chainBridge (fun w => (w.1,w.2.1)) = noisyAnti ∧
    Prob.coarsen chainBridge (fun w => (w.2.1,w.2.2)) = noisyAnti := by
  constructor <;> apply Subtype.ext <;> funext ab <;>
    rcases ab with ⟨a,b⟩ <;> cases a <;> cases b <;>
    norm_num [Prob.coarsen_apply, pushforward_eq_sum_ite,
      chainBridge, noisyAnti, Fintype.sum_prod_type]

/-- The valid two-chart joint fails the third supplied marginal. -/
theorem chainBridge_disagrees_with_third :
    (Prob.coarsen chainBridge (fun w => (w.1,w.2.2))).1 (true,true) = 25/64 ∧
    noisyAnti.1 (true,true) = 1/16 := by
  norm_num [Prob.coarsen_apply, pushforward_eq_sum_ite,
    chainBridge, noisyAnti, Fintype.sum_prod_type]

theorem chainBridge_observation_possible :
    0 < evidence chainBridge (fun w => trueLikelihood w.2.2) := by
  norm_num [evidence, chainBridge, noisyAnti, trueLikelihood, Fintype.sum_prod_type]

/-- A path-specific answer is meaningful, but remains relative to its chosen
joint model. A path label does not establish agreement with the third chart. -/
theorem chainBridge_revision :
    (Prob.coarsen (posterior chainBridge (fun w => trueLikelihood w.2.2)
      (fun w => by dsimp only [trueLikelihood]; split_ifs <;> norm_num)
      chainBridge_observation_possible) (fun w => w.1)).1 true = 25/32 := by
  norm_num [Prob.coarsen_apply, pushforward_eq_sum_ite, posterior_apply,
    evidence, chainBridge, noisyAnti, trueLikelihood, Fintype.sum_prod_type]

/-- A prior over two model hypotheses performs an ordinary Bayesian update:
the observation is nine times likelier under the first hypothesis. -/
theorem model_prior_revision :
    (posterior fair (fun m => if m then (9/10 : ℝ) else 1/10)
      (fun m => by cases m <;> norm_num)
      (by norm_num [evidence, fair])).1 true = 9/10 := by
  norm_num [posterior_apply, evidence, fair]

end Controls
end Mettapedia.ProbabilityTheory.BayesianInference.LocalContexts
