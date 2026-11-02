import Mettapedia.Logic.WorldModel.Basic
import Mettapedia.ProbabilityTheory.BayesianInference.Variational
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Distributional spaces

A space keeps a joint observation model and an identified evidence ledger.
Atoms denote events on worlds, not alternatives in a categorical bag of atoms.
Conditioning is partial; evidence with zero mass is retained for later retraction.
A product likelihood is derived only for the independent-channel construction.
-/
set_option autoImplicit false

namespace Mettapedia.Logic.DistributionalSpace
set_option backward.isDefEq.respectTransparency false
open Finset Mettapedia.InformationTheory Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.InformationTheory.FiniteRV

variable {Ω O Id Θ : Type*} [Fintype Ω] [Fintype O]

/-- The catalogue fixes what each observation identity asserts. The kernel may
correlate its observation coordinates arbitrarily. -/
structure Model (Θ Ω O Id : Type*) [Fintype Ω] [Fintype O] where
  prior : Θ → Prob Ω
  observations : Θ → Ω → Prob O
  catalogue : Id → O → Bool

/-- A view retains evidence across parameter changes. The model and immutable
catalogue are supplied separately, so ledgers cannot silently pool models. -/
structure View (Θ Id : Type*) where
  parameter : Θ
  active : Finset Id

def View.withParameters (v : View Θ Id) (θ : Θ) : View Θ Id := ⟨θ, v.active⟩

@[simp] theorem View.withParameters_active (v : View Θ Id) (θ : Θ) :
    (v.withParameters θ).active = v.active := rfl

namespace Model
variable (m : Model Θ Ω O Id)

def accepts (E : Finset Id) (o : O) : Bool := decide (∀ i ∈ E, m.catalogue i o = true)

noncomputable def likelihood (θ : Θ) (E : Finset Id) (w : Ω) : ℝ :=
  ∑ o, if m.accepts E o then (m.observations θ w).1 o else 0

theorem likelihood_nonneg (θ : Θ) (E : Finset Id) (w : Ω) :
    0 ≤ m.likelihood θ E w := by
  apply Finset.sum_nonneg
  intro o _
  split_ifs
  · exact (m.observations θ w).2.1 o
  · exact le_refl 0

@[simp] theorem likelihood_empty (θ : Θ) (w : Ω) : m.likelihood θ ∅ w = 1 := by
  simp [likelihood, accepts, (m.observations θ w).2.2]

noncomputable def normalizer (θ : Θ) (E : Finset Id) : ℝ :=
  evidence (m.prior θ) (m.likelihood θ E)

noncomputable def posterior? (θ : Θ) (E : Finset Id) : Option (Prob Ω) :=
  if h : 0 < m.normalizer θ E then
    some (posterior (m.prior θ) (m.likelihood θ E) (m.likelihood_nonneg θ E) h)
  else none

@[simp] theorem posterior?_none_iff (θ : Θ) (E : Finset Id) :
    m.posterior? θ E = none ↔ m.normalizer θ E = 0 := by
  have hn := evidence_nonneg (m.prior θ) _ (m.likelihood_nonneg θ E)
  simp only [posterior?, dite_eq_right_iff, reduceCtorEq, imp_false]
  change ¬ 0 < m.normalizer θ E ↔ _
  change 0 ≤ m.normalizer θ E at hn
  exact ⟨fun h => le_antisymm (le_of_not_gt h) hn, fun h => by simp [h]⟩

@[simp] theorem likelihood_empty_fun (θ : Θ) : m.likelihood θ ∅ = fun _ => 1 :=
  funext (m.likelihood_empty θ)

@[simp] theorem posterior?_empty (θ : Θ) : m.posterior? θ ∅ = some (m.prior θ) := by
  simp [posterior?, normalizer, likelihood_empty_fun, evidence_one, posterior_one]

noncomputable def expectation? (θ : Θ) (E : Finset Id) (f : Ω → ℝ) : Option ℝ :=
  (m.posterior? θ E).map fun p => ∑ w, p.1 w * f w

noncomputable def probability? (θ : Θ) (E : Finset Id) (event : Ω → Bool) : Option ℝ :=
  m.expectation? θ E fun w => if event w then 1 else 0

noncomputable def marginal? {A : Type*} [Fintype A] [DecidableEq A]
    (θ : Θ) (E : Finset Id) (view : Ω → A) : Option (Prob A) :=
  (m.posterior? θ E).map fun p => Prob.coarsen p view

/-- The same likelihood gives the same posterior; observation identity is not
recovered by this theorem. -/
theorem posterior?_congr (θ : Θ) (E F : Finset Id)
    (same : m.likelihood θ E = m.likelihood θ F) :
    m.posterior? θ E = m.posterior? θ F := by
  simp only [posterior?, normalizer, same]

/-- An exact probability query keeps impossible evidence distinct from zero. -/
theorem probability?_formula (θ : Θ) (E : Finset Id) (event : Ω → Bool) :
    m.probability? θ E event =
      if 0 < m.normalizer θ E then
        some ((∑ w, if event w then (m.prior θ).1 w * m.likelihood θ E w else 0) /
          m.normalizer θ E) else none := by
  unfold probability? expectation? posterior?
  split_ifs with h
  · simp only [Option.map_some, posterior_apply]
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> simp [normalizer]
  · rfl

/-- The law of worlds and complete observations, before evidence selection. -/
noncomputable def jointLaw (θ : Θ) : Prob (Ω × O) :=
  joint (m.prior θ) (m.observations θ)

noncomputable def jointLikelihood (E : Finset Id) (wo : Ω × O) : ℝ :=
  if m.accepts E wo.2 then 1 else 0

theorem jointLikelihood_nonneg (E : Finset Id) (wo : Ω × O) :
    0 ≤ m.jointLikelihood E wo := by unfold jointLikelihood; split_ifs <;> norm_num

theorem joint_evidence (θ : Θ) (E : Finset Id) :
    evidence (m.jointLaw θ) (m.jointLikelihood E) = m.normalizer θ E := by
  simp only [evidence, jointLaw, joint_apply, jointLikelihood, normalizer, likelihood,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro o _
  split_ifs <;> ring

/-- Conditioning the independently constructed joint, then forgetting the
observation coordinates, agrees with the latent-space posterior. -/
theorem condition_joint_project [DecidableEq Ω] (θ : Θ) (E : Finset Id)
    (h : 0 < m.normalizer θ E) :
    Prob.coarsen (posterior (m.jointLaw θ) (m.jointLikelihood E)
      (m.jointLikelihood_nonneg E) (by rw [m.joint_evidence]; exact h)) Prod.fst =
    posterior (m.prior θ) (m.likelihood θ E) (m.likelihood_nonneg θ E) h := by
  classical
  apply Subtype.ext
  funext w
  change pushforward _ Prod.fst w = _
  rw [pushforward_fst]
  simp only [posterior_apply]
  rw [m.joint_evidence]
  simp only [jointLaw, joint_apply, jointLikelihood, ← Finset.sum_div]
  congr 1
  simp only [likelihood, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  split_ifs <;> ring

/-- Revision is union of identified observations. Probability extraction is
nonlinear and is not asserted to preserve addition. Parameters remain fixed
within this instance. -/
@[instance_reducible] noncomputable def worldModel [DecidableEq Id] (θ : Θ) :
    MonoidalWorldModel (Finset Id) (Ω → Bool) (Option ℝ) where
  revise := (· ∪ ·)
  empty := ∅
  extract := m.probability? θ
  revise_assoc := Finset.union_assoc
  revise_empty_left := Finset.empty_union
  revise_empty_right := Finset.union_empty

/-- Evaluation of a parameterized evidence view. -/
noncomputable def viewPosterior? (v : View Θ Id) : Option (Prob Ω) :=
  m.posterior? v.parameter v.active

@[simp] theorem withParameters_posterior (v : View Θ Id) (θ : Θ) :
    m.viewPosterior? (v.withParameters θ) = m.posterior? θ v.active := rfl

end Model

variable [DecidableEq Id]

def observe (E : Finset Id) (i : Id) : Finset Id := insert i E
def retract (E : Finset Id) (i : Id) : Finset Id := E.erase i
@[simp] theorem observe_replay (E : Finset Id) (i : Id) :
    observe (observe E i) i = observe E i := Finset.insert_idem _ _
@[simp] theorem retract_fresh (E : Finset Id) (i : Id) (h : i ∉ E) :
    retract (observe E i) i = E := Finset.erase_insert h

theorem merge_comm (E F : Finset Id) : E ∪ F = F ∪ E := Finset.union_comm _ _
theorem merge_idem (E : Finset Id) : E ∪ E = E := Finset.union_self _

section Independent
variable [Fintype Id] [DecidableEq O]

/-- Product channel, normalized by finite distributivity. -/
noncomputable def independent (channels : Id → Prob O) : Prob (Id → O) :=
  ⟨fun outcomes => ∏ i, (channels i).1 (outcomes i),
   fun outcomes => Finset.prod_nonneg fun i _ => (channels i).2.1 (outcomes i), by
    rw [← Fintype.prod_sum]
    simp only [fun i => (channels i).2.2, Finset.prod_const_one]⟩

noncomputable def independentModel (prior : Θ → Prob Ω)
    (channels : Θ → Ω → Id → Prob O) (observed : Id → O) :
    Model Θ Ω (Id → O) Id where
  prior := prior
  observations θ w := independent (channels θ w)
  catalogue i outcomes := decide (outcomes i = observed i)

/-- Summing unobserved coordinates derives the product likelihood. -/
theorem independent_likelihood (prior : Θ → Prob Ω)
    (channels : Θ → Ω → Id → Prob O) (observed : Id → O)
    (θ : Θ) (E : Finset Id) (w : Ω) :
    (independentModel prior channels observed).likelihood θ E w =
      ∏ i ∈ E, (channels θ w i).1 (observed i) := by
  classical
  unfold Model.likelihood
  have term : ∀ outcomes : Id → O,
      (if (independentModel prior channels observed).accepts E outcomes then
        (independent (channels θ w)).1 outcomes else 0) =
      ∏ i, (if i ∈ E then if outcomes i = observed i then
        (channels θ w i).1 (outcomes i) else 0 else (channels θ w i).1 (outcomes i)) := by
    intro outcomes
    simp only [Model.accepts, independentModel, decide_eq_true_eq, independent]
    by_cases h : ∀ i ∈ E, outcomes i = observed i
    · rw [if_pos h]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ E <;> simp [hi, h]
    · have bad : ∃ i ∈ E, outcomes i ≠ observed i := by simpa using h
      obtain ⟨i, hi, hb⟩ := bad
      have hz : (∏ j, (if j ∈ E then if outcomes j = observed j then
          (channels θ w j).1 (outcomes j) else 0 else (channels θ w j).1 (outcomes j))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hb])
      rw [if_neg h, hz]
  change (∑ outcomes : Id → O, if (independentModel prior channels observed).accepts E outcomes
    then (independent (channels θ w)).1 outcomes else 0) = _
  simp_rw [term]
  rw [← Fintype.prod_sum (fun i o => if i ∈ E then if o = observed i then
    (channels θ w i).1 o else 0 else (channels θ w i).1 o)]
  have localSum : ∀ i, (∑ o : O, if i ∈ E then if o = observed i then
      (channels θ w i).1 o else 0 else (channels θ w i).1 o) =
      if i ∈ E then (channels θ w i).1 (observed i) else 1 := by
    intro i
    by_cases h : i ∈ E <;> simp [h, (channels θ w i).2.2]
  simp_rw [localSum]
  simp only [← Finset.prod_filter]
  simp

/-- Only newly introduced independent factors are multiplied into a posterior. -/
theorem independent_union_likelihood (prior : Θ → Prob Ω)
    (channels : Θ → Ω → Id → Prob O) (observed : Id → O)
    (θ : Θ) (E F : Finset Id) (h : Disjoint E F) (w : Ω) :
    (independentModel prior channels observed).likelihood θ (E ∪ F) w =
    (independentModel prior channels observed).likelihood θ E w *
    (independentModel prior channels observed).likelihood θ F w := by
  simp only [independent_likelihood]
  exact Finset.prod_union h

set_option backward.isDefEq.respectTransparency false in
/-- Sequential conditioning, derived for disjoint sets of observation identities. -/
theorem independent_update (prior : Θ → Prob Ω)
    (channels : Θ → Ω → Id → Prob O) (observed : Id → O)
    (θ : Θ) (E F : Finset Id) (disjoint : Disjoint E F)
    (first : 0 < (independentModel prior channels observed).normalizer θ E)
    (second : 0 < evidence
      (posterior (prior θ) ((independentModel prior channels observed).likelihood θ E)
        ((independentModel prior channels observed).likelihood_nonneg θ E) first)
      ((independentModel prior channels observed).likelihood θ F)) :
    (independentModel prior channels observed).posterior? θ (E ∪ F) = some
      (posterior (posterior (prior θ)
        ((independentModel prior channels observed).likelihood θ E)
        ((independentModel prior channels observed).likelihood_nonneg θ E) first)
        ((independentModel prior channels observed).likelihood θ F)
        ((independentModel prior channels observed).likelihood_nonneg θ F) second) := by
  let m := independentModel prior channels observed
  have law : m.likelihood θ (E ∪ F) = fun w => m.likelihood θ E w * m.likelihood θ F w :=
    funext (independent_union_likelihood prior channels observed θ E F disjoint)
  have pos : 0 < m.normalizer θ (E ∪ F) := by
    change 0 < evidence (prior θ) (m.likelihood θ (E ∪ F))
    rw [law]
    rw [evidence_posterior] at second
    exact (div_pos_iff_of_pos_right first).mp second
  change m.posterior? θ (E ∪ F) = _
  rw [Model.posterior?, dif_pos pos]
  congr 1
  rw [posterior_posterior]
  simp only [law]
  rfl

end Independent
end Mettapedia.Logic.DistributionalSpace
