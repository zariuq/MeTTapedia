import Mettapedia.LearningTheory.FiniteClass
import Mettapedia.Ethics.HostVirtuePossession

/-!
# Virtue as learning

Target-centered virtue ethics judges acts; virtue proper is a disposition that has
to be learned.  Following Stenseke's analysis of virtue ethics through learning
theory, a disposition is a hypothesis mapping situations to acts, the situations
a virtue concerns carry a distribution, and learning a virtue from an exemplar is
learning a hypothesis that agrees with the exemplar's disposition.

* **PAC for dispositions** (`virtue_occam`).  A disposition from a finite class
  that agrees with the exemplar on every sampled situation misses the exemplar's
  target with probability above `ε` only with sample probability at most
  `|class| · exp (-ε m)`.
* **No universal virtue learner** (`virtue_no_free_lunch`).  In a situation it has
  not observed, any learner is wrong for exactly half of all possible exemplars.
  The class of all dispositions shatters the field (`all_dispositions_shatter`), so
  its VC bound is vacuous; a learnable virtue needs an inductive bias, such as the
  constant class of VC dimension at most one.
* **Learning a virtue by trial and error** (`virtue_halving`).  An agent that acts
with the majority of the dispositions still consistent with every correction it
has received errs at most `log₂` of the class size times, on any sequence of
situations, when the exemplar's disposition is in the class.
* **The overfit honest agent.**  Situations record whether a lie would be detected
  and what is true; beliefs are accurate.  The overfit disposition reports its
  belief when a lie would be detected and the opposite otherwise.
  - On the training distribution, which contains only detectable situations, it
    has zero risk and every sample certifies it (`overfit_certified_in_training`).
  - On the shifted distribution it misses half the time (`overfit_fails_shifted`).
  - The outcome observer, which sees whether a report was true only where that can
    be checked, cannot tell it from the honest disposition
    (`outcome_observer_blind`); neither can any record of responses in the
    situations training presents (`training_record_blind`).
  - The two dispositions disagree exactly in the situations training never
    presents (`disagreement_is_untrained`).  A record of responses there separates
    them without consulting beliefs: what is missing from training is coverage of
    the field, not access to the agent's inner states.
* **Bounded possession is exhaustive certification** (`boundedPossession_iff_zero_risk`).
  For a host agent and a finite field, possession within a reduction budget holds
  exactly when the budgeted disposition has zero risk under every full-support
  distribution on the field.  PAC learning certifies the same disposition from
  samples, relative to one distribution, and the overfit agent is what the
  difference allows.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.VirtueLearning

open Mettapedia.LearningTheory
open Mettapedia.Languages.PartrecMachine
open Mettapedia.Ethics.VirtuePossessionUndecidability
open Mettapedia.Ethics.HostVirtuePossession
open Turing.ToPartrec
open Finset Classical

/-! ## Learning dispositions -/

variable {Situation : Type} [Fintype Situation] [DecidableEq Situation]

/-- A disposition: in each situation, act or refrain. -/
abbrev Disposition (Situation : Type) := Situation → Bool

/-- **PAC for dispositions.** -/
theorem virtue_occam (field : Distribution Situation) (dispositions : Finset (Disposition Situation))
    (exemplar : Disposition Situation) (ε : ℝ) (m : ℕ) :
    sampleProb field m
        (fun situations => ∃ disposition ∈ dispositions, Consistent disposition exemplar situations ∧
          ε < risk field disposition exemplar) ≤
      dispositions.card * Real.exp (-(ε * m)) :=
  occam_bound field dispositions exemplar ε m

/-- **No universal virtue learner.** -/
theorem virtue_no_free_lunch {m : ℕ} (learner : Learner Situation m) (observed : Fin m → Situation)
    (unobserved : Situation) (notObserved : ∀ i, observed i ≠ unobserved) :
    2 * (univ.filter fun exemplar : Disposition Situation =>
        learner (label exemplar observed) unobserved ≠ exemplar unobserved).card =
      Fintype.card (Disposition Situation) :=
  no_free_lunch_unseen learner observed unobserved notObserved

omit [Fintype Situation] [DecidableEq Situation] in
/-- **Learning a virtue by trial and error.** -/
theorem virtue_halving (exemplar : Disposition Situation) (dispositions : Finset (Disposition Situation))
    (realizable : exemplar ∈ dispositions) (situations : List Situation) :
    halvingMistakes exemplar dispositions situations ≤ Nat.log 2 dispositions.card :=
  halving_mistakes_le_log exemplar dispositions realizable situations

theorem all_dispositions_shatter :
    (classFamily (univ : Finset (Disposition Situation))).Shatters univ :=
  all_shatters_univ

omit [DecidableEq Situation] in
theorem risk_eq_zero_iff (distribution : Distribution Situation) (disposition exemplar : Disposition Situation) :
    risk distribution disposition exemplar = 0 ↔
      ∀ situation, 0 < distribution.1 situation → disposition situation = exemplar situation := by
  unfold risk prob
  rw [sum_eq_zero_iff_of_nonneg fun x _ => by split_ifs <;> simp [distribution.2.1 x]]
  constructor
  · intro zero situation positive
    by_contra different
    have := zero situation (mem_univ _)
    rw [if_pos different] at this
    exact positive.ne' this
  · intro agree situation _
    by_cases positive : 0 < distribution.1 situation
    · rw [if_neg (not_not.mpr (agree situation positive))]
    · by_cases different : disposition situation ≠ exemplar situation
      · rw [if_pos different]
        exact le_antisymm (not_lt.mp positive) (distribution.2.1 situation)
      · rw [if_neg different]

/-! ## The overfit honest agent -/

/-- A situation: whether a lie would be detected, and what is true. -/
abbrev CommunicationSituation : Type := Bool × Bool

def detectable (situation : CommunicationSituation) : Bool := situation.1

/-- Beliefs are accurate. -/
def belief (situation : CommunicationSituation) : Bool := situation.2

def honest : Disposition CommunicationSituation := belief

def overfit : Disposition CommunicationSituation := fun situation =>
  if detectable situation then belief situation else !belief situation

/-- Only detectable situations occur in training. -/
noncomputable def training : Distribution CommunicationSituation :=
  ⟨fun situation => if situation.1 then 1 / 2 else 0,
    fun situation => by dsimp only; split_ifs <;> norm_num,
    by simp [Fintype.sum_prod_type]; norm_num⟩

/-- Every situation is equally likely. -/
noncomputable def shifted : Distribution CommunicationSituation :=
  ⟨fun _ => 1 / 4, fun _ => by norm_num, by simp⟩

theorem overfit_certified_in_training (m : ℕ) :
    risk training overfit honest = 0 ∧ sampleProb training m (Consistent overfit honest) = 1 := by
  have zero : risk training overfit honest = 0 := by
    rw [risk_eq_zero_iff]
    rintro ⟨_ | _, _⟩ positive <;> simp_all [training, overfit, honest, detectable]
  refine ⟨zero, ?_⟩
  rw [sampleProb_consistent, zero]
  simp

theorem overfit_fails_shifted : risk shifted overfit honest = 1 / 2 := by
  simp [risk, prob, shifted, overfit, honest, detectable, belief, Fintype.sum_prod_type]
  norm_num

theorem overfit_not_honest : overfit ≠ honest := fun same => by
  have := congrFun same (false, true)
  simp [overfit, honest, detectable, belief] at this

/-- What an outcome observer sees: whether the report was true, where that can be checked. -/
def outcomeView (disposition : Disposition CommunicationSituation) (situation : CommunicationSituation) :
    Option Bool :=
  if detectable situation then some (disposition situation == belief situation) else none

theorem outcome_observer_blind : outcomeView overfit = outcomeView honest := by
  funext situation
  rcases situation with ⟨_ | _, _ | _⟩ <;> rfl

/-- The responses in the situations training presents. -/
noncomputable def trainingRecord (disposition : Disposition CommunicationSituation) :
    {situation // 0 < training.1 situation} → Bool :=
  fun situation => disposition situation.1

theorem training_record_blind : trainingRecord overfit = trainingRecord honest := by
  funext ⟨situation, positive⟩
  exact (risk_eq_zero_iff training overfit honest).mp (overfit_certified_in_training 0).1 situation
    positive

/-- **The disagreement is exactly what training never presents.** -/
theorem disagreement_is_untrained (situation : CommunicationSituation) :
    overfit situation ≠ honest situation ↔ training.1 situation = 0 := by
  rcases situation with ⟨_ | _, _ | _⟩ <;> simp [overfit, honest, detectable, belief, training]

/-! ## Bounded possession as exhaustive certification -/

/-- Whether a host agent, within a reduction budget, responds on target at a situation. -/
noncomputable def budgetedDisposition (virtue : FiniteBehavioralVirtue) (budget : ℕ) (agent : Code) :
    Disposition (Fin virtue.field.length) := fun index =>
  ((outputWithin budget agent [virtue.field.get index]).bind List.head?).any
    (virtue.target (virtue.field.get index))

/-- **Bounded possession is zero risk under every full-support field distribution.** -/
theorem boundedPossession_iff_zero_risk (virtue : FiniteBehavioralVirtue) (budget : ℕ) (agent : Code)
    (distribution : Distribution (Fin virtue.field.length))
    (fullSupport : ∀ index, 0 < distribution.1 index) :
    hostRespondsWithin virtue budget agent = true ↔
      risk distribution (budgetedDisposition virtue budget agent) (fun _ => true) = 0 := by
  rw [risk_eq_zero_iff]
  simp only [fullSupport, forall_const, hostRespondsWithin, List.all_eq_true, budgetedDisposition]
  constructor
  · intro all index
    exact all _ (List.get_mem _ _)
  · intro all situation member
    obtain ⟨index, rfl⟩ := List.get_of_mem member
    exact all index

#print axioms virtue_occam
#print axioms virtue_no_free_lunch
#print axioms virtue_halving
#print axioms overfit_certified_in_training
#print axioms overfit_fails_shifted
#print axioms outcome_observer_blind
#print axioms training_record_blind
#print axioms disagreement_is_untrained
#print axioms boundedPossession_iff_zero_risk

end Mettapedia.Ethics.VirtueLearning
