import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SetFamily.Shatter

/-!
# Learning a finite hypothesis class on a finite domain

Distributions are Mathlib's standard simplex on a finite domain; a sample of size
`m` is a function `Fin m → Point` drawn independently, so its weight is the
product of the point masses.  Hypotheses are Boolean functions on the domain.

* **Occam bound** (`occam_bound`).  The probability that some hypothesis in a
  finite class agrees with the target on the whole sample yet has true risk
  above `ε` is at most `|H| · exp (-ε m)`.  A consistent hypothesis is
  therefore probably approximately correct once
  `m ≥ (log |H| + log (1/δ)) / ε` (`occam_sample_complexity`).
* **No free lunch** (`no_free_lunch_unseen`).  For any learner and any point the
  sample does not contain, exactly half of all targets make the learner wrong at
  that point.  No learner beats chance on unseen points, averaged over targets.
* **VC dimension** (`card_le_sum_vcDim`, `vc_occam_bound`).  Through Mathlib's
  shattering theory, a class of VC dimension `d` on `n` points has at most
  `∑_{k ≤ d} (n choose k)` members, so the Occam bound holds with that count in
  place of `|H|`.  The count grows with the domain size `n`, so this is a
  finite-domain counting bound, not the distribution-free VC theorem whose sample
  complexity depends on `d` alone.  The class of constant hypotheses has VC
  dimension at most one; the class of all hypotheses shatters the whole domain.
* **Learning online by halving** (`halving_mistake_bound`).  Predict with the
  majority of the hypotheses still consistent with every labeled point, then
  discard the inconsistent ones.  When the target is in the class, every mistake
  at least halves what remains, so on any sequence of points there are at most
  `log₂ |H|` mistakes (`halving_mistakes_le_log`).
-/

set_option autoImplicit false

namespace Mettapedia.LearningTheory

open Finset Classical

variable {Point : Type*} [Fintype Point]

/-- A probability distribution on a finite domain. -/
abbrev Distribution (Point : Type*) [Fintype Point] := ↥(stdSimplex ℝ Point)

/-- The probability of an event. -/
noncomputable def prob (distribution : Distribution Point) (event : Point → Prop) : ℝ :=
  ∑ x, if event x then distribution.1 x else 0

theorem prob_nonneg (distribution : Distribution Point) (event : Point → Prop) :
    0 ≤ prob distribution event :=
  sum_nonneg fun x _ => by split_ifs <;> simp [distribution.2.1 x]

theorem prob_add_prob_not (distribution : Distribution Point) (event : Point → Prop) :
    prob distribution event + prob distribution (fun x => ¬ event x) = 1 := by
  rw [prob, prob, ← sum_add_distrib, ← distribution.2.2]
  exact sum_congr rfl fun x _ => by split_ifs <;> simp_all

/-- The true risk of a hypothesis against a target. -/
noncomputable def risk (distribution : Distribution Point) (hypothesis target : Point → Bool) : ℝ :=
  prob distribution fun x => hypothesis x ≠ target x

/-- The probability of an event about an independent sample of size `m`. -/
noncomputable def sampleProb (distribution : Distribution Point) (m : ℕ)
    (event : (Fin m → Point) → Prop) : ℝ :=
  ∑ sample, if event sample then ∏ i, distribution.1 (sample i) else 0

/-- A hypothesis agrees with the target on every sample point. -/
def Consistent {m : ℕ} (hypothesis target : Point → Bool) (sample : Fin m → Point) : Prop :=
  ∀ i, hypothesis (sample i) = target (sample i)

theorem sampleProb_consistent (distribution : Distribution Point) (m : ℕ)
    (hypothesis target : Point → Bool) :
    sampleProb distribution m (Consistent hypothesis target) =
      (1 - risk distribution hypothesis target) ^ m := by
  have agree : 1 - risk distribution hypothesis target =
      ∑ x, if hypothesis x = target x then distribution.1 x else 0 := by
    have total := prob_add_prob_not distribution fun x => hypothesis x ≠ target x
    have complement : 1 - risk distribution hypothesis target =
        prob distribution fun x => ¬ hypothesis x ≠ target x := by
      rw [risk]; linarith
    rw [complement, prob]
    simp only [ne_eq, not_not]
  rw [agree, Fintype.sum_pow, sampleProb]
  refine sum_congr rfl fun sample _ => ?_
  simp only [Consistent, Finset.prod_ite_zero, Finset.mem_univ, true_implies]
  congr

/-- **Occam bound.** -/
theorem occam_bound (distribution : Distribution Point) [DecidableEq Point]
    (hypotheses : Finset (Point → Bool)) (target : Point → Bool) (ε : ℝ) (m : ℕ) :
    sampleProb distribution m
        (fun sample => ∃ hypothesis ∈ hypotheses, Consistent hypothesis target sample ∧
          ε < risk distribution hypothesis target) ≤
      hypotheses.card * Real.exp (-(ε * m)) := by
  set bad := hypotheses.filter fun hypothesis => ε < risk distribution hypothesis target
  have weight_nonneg : ∀ sample : Fin m → Point, 0 ≤ ∏ i, distribution.1 (sample i) :=
    fun sample => prod_nonneg fun i _ => distribution.2.1 _
  have union : sampleProb distribution m
      (fun sample => ∃ hypothesis ∈ hypotheses, Consistent hypothesis target sample ∧
        ε < risk distribution hypothesis target) ≤
      ∑ hypothesis ∈ bad, sampleProb distribution m (Consistent hypothesis target) := by
    rw [sampleProb]
    simp only [sampleProb]
    rw [sum_comm]
    refine sum_le_sum fun sample _ => ?_
    split_ifs with exists_bad
    · obtain ⟨hypothesis, member, consistent, large⟩ := exists_bad
      have inBad : hypothesis ∈ bad := mem_filter.mpr ⟨member, large⟩
      have single := single_le_sum (s := bad) (a := hypothesis)
        (f := fun h => if Consistent h target sample then ∏ i, distribution.1 (sample i) else 0)
        (fun h _ => by split_ifs <;> simp [weight_nonneg sample]) inBad
      simpa [consistent] using single
    · exact sum_nonneg fun h _ => by split_ifs <;> simp [weight_nonneg sample]
  have each : ∀ hypothesis ∈ bad,
      sampleProb distribution m (Consistent hypothesis target) ≤ Real.exp (-(ε * m)) := by
    intro hypothesis member
    rw [sampleProb_consistent]
    have large := (mem_filter.mp member).2
    have lower : 0 ≤ 1 - risk distribution hypothesis target := by
      have := prob_add_prob_not distribution fun x => hypothesis x ≠ target x
      have := prob_nonneg distribution fun x => ¬ hypothesis x ≠ target x
      simp only [risk]; linarith
    calc (1 - risk distribution hypothesis target) ^ m ≤ (1 - ε) ^ m :=
          pow_le_pow_left₀ lower (by linarith) m
      _ ≤ Real.exp (-ε) ^ m := pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg ε) m
      _ = Real.exp (-(ε * m)) := by rw [← Real.exp_nat_mul]; ring_nf
  calc _ ≤ ∑ hypothesis ∈ bad, sampleProb distribution m (Consistent hypothesis target) := union
    _ ≤ ∑ _hypothesis ∈ bad, Real.exp (-(ε * m)) := sum_le_sum each
    _ = bad.card * Real.exp (-(ε * m)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ hypotheses.card * Real.exp (-(ε * m)) := by
        gcongr
        exact filter_subset _ _

/-- **Sample complexity.**  Enough samples make the Occam bound at most `δ`. -/
theorem occam_sample_complexity (distribution : Distribution Point) [DecidableEq Point]
    (hypotheses : Finset (Point → Bool)) (target : Point → Bool) {ε δ : ℝ}
    (positive : 0 < ε) (confidence : 0 < δ) (nonempty : hypotheses.Nonempty)
    {m : ℕ} (enough : (Real.log hypotheses.card + Real.log (1 / δ)) / ε ≤ m) :
    sampleProb distribution m
        (fun sample => ∃ hypothesis ∈ hypotheses, Consistent hypothesis target sample ∧
          ε < risk distribution hypothesis target) ≤ δ := by
  refine (occam_bound distribution hypotheses target ε m).trans ?_
  have cardPositive : (0 : ℝ) < hypotheses.card := by exact_mod_cast nonempty.card_pos
  have scaled : Real.log hypotheses.card + Real.log (1 / δ) ≤ ε * m := by
    rwa [div_le_iff₀ positive, mul_comm] at enough
  have logBound : Real.log (hypotheses.card * Real.exp (-(ε * m))) ≤ Real.log δ := by
    rw [Real.log_mul cardPositive.ne' (Real.exp_pos _).ne', Real.log_exp,
      one_div, Real.log_inv] at *
    linarith
  exact (Real.log_le_log_iff (mul_pos cardPositive (Real.exp_pos _)) confidence).mp logBound

/-! ## No free lunch -/

/-- A learner maps a labelled sample to a hypothesis. -/
abbrev Learner (Point : Type*) (m : ℕ) := (Fin m → Point × Bool) → Point → Bool

/-- The labelled sample a target produces on given sample points. -/
def label {m : ℕ} (target : Point → Bool) (sample : Fin m → Point) : Fin m → Point × Bool :=
  fun i => (sample i, target (sample i))

/-- **No free lunch on unseen points.**  For any learner, sample points, and a point
the sample does not contain, the learner is wrong at that point for exactly half
of all targets. -/
theorem no_free_lunch_unseen [DecidableEq Point] {m : ℕ} (learner : Learner Point m)
    (sample : Fin m → Point) (unseen : Point) (notSampled : ∀ i, sample i ≠ unseen) :
    2 * (univ.filter fun target : Point → Bool =>
        learner (label target sample) unseen ≠ target unseen).card =
      Fintype.card (Point → Bool) := by
  let flip : (Point → Bool) → (Point → Bool) := fun target => Function.update target unseen (!target unseen)
  have flip_label : ∀ target, label (flip target) sample = label target sample := by
    intro target
    funext i
    simp [label, flip, Function.update_of_ne (notSampled i)]
  have flip_flip : ∀ target, flip (flip target) = target := by
    intro target
    funext x
    by_cases same : x = unseen
    · subst same; simp [flip]
    · simp [flip, Function.update_of_ne same]
  set wrong := univ.filter fun target : Point → Bool =>
    learner (label target sample) unseen ≠ target unseen
  set right := univ.filter fun target : Point → Bool =>
    ¬ learner (label target sample) unseen ≠ target unseen
  have swap : wrong.card = right.card := by
    refine card_nbij' flip flip (fun target member => ?_) (fun target member => ?_)
      (fun target _ => flip_flip target) (fun target _ => flip_flip target)
    · simp only [wrong, right, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, not_not,
        ne_eq] at member ⊢
      rw [flip_label]
      have flipped : flip target unseen = !target unseen := by simp [flip]
      rw [flipped]
      revert member
      cases learner (label target sample) unseen <;> cases target unseen <;> decide
    · simp only [wrong, right, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, not_not,
        ne_eq] at member ⊢
      rw [flip_label]
      have flipped : flip target unseen = !target unseen := by simp [flip]
      rw [flipped]
      revert member
      cases learner (label target sample) unseen <;> cases target unseen <;> decide
  have partition := card_filter_add_card_filter_not
    (s := (univ : Finset (Point → Bool)))
    (fun target : Point → Bool => learner (label target sample) unseen ≠ target unseen)
  rw [card_univ] at partition
  change wrong.card + right.card = Fintype.card (Point → Bool) at partition
  omega

/-! ## VC dimension -/

/-- A hypothesis class as a family of subsets of the domain. -/
noncomputable def classFamily [DecidableEq Point] (hypotheses : Finset (Point → Bool)) :
    Finset (Finset Point) :=
  hypotheses.image fun hypothesis => univ.filter fun x => hypothesis x = true

theorem classFamily_card [DecidableEq Point] (hypotheses : Finset (Point → Bool)) :
    (classFamily hypotheses).card = hypotheses.card := by
  refine card_image_of_injOn fun first _ second _ same => ?_
  funext x
  have := congrArg (fun set : Finset Point => x ∈ set) same
  simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
  cases h₁ : first x <;> cases h₂ : second x <;> simp_all

/-- **Sauer–Shelah through Mathlib.**  A class of VC dimension `d` has at most
`∑_{k ≤ d} (n choose k)` members. -/
theorem card_le_sum_vcDim [DecidableEq Point] (hypotheses : Finset (Point → Bool)) :
    hypotheses.card ≤
      ∑ k ∈ Iic (classFamily hypotheses).vcDim, (Fintype.card Point).choose k := by
  rw [← classFamily_card]
  exact (card_le_card_shatterer _).trans card_shatterer_le_sum_vcDim

/-- The Occam bound stated through VC dimension, with the Sauer–Shelah count over
the whole finite domain in place of the class size. -/
theorem vc_occam_bound (distribution : Distribution Point) [DecidableEq Point]
    (hypotheses : Finset (Point → Bool)) (target : Point → Bool) (ε : ℝ) (m : ℕ) :
    sampleProb distribution m
        (fun sample => ∃ hypothesis ∈ hypotheses, Consistent hypothesis target sample ∧
          ε < risk distribution hypothesis target) ≤
      (∑ k ∈ Iic (classFamily hypotheses).vcDim, (Fintype.card Point).choose k : ℕ) *
        Real.exp (-(ε * m)) := by
  refine (occam_bound distribution hypotheses target ε m).trans ?_
  gcongr
  exact_mod_cast card_le_sum_vcDim hypotheses

/-- The two constant hypotheses. -/
def constants : Finset (Point → Bool) := {fun _ => false, fun _ => true}

/-- The constant class has VC dimension at most one. -/
theorem constants_vcDim_le_one [DecidableEq Point] :
    (classFamily (constants : Finset (Point → Bool))).vcDim ≤ 1 := by
  refine Finset.sup_le fun shattered member => ?_
  rw [mem_shatterer] at member
  by_contra small
  have large := not_le.mp small
  obtain ⟨a, aMem, b, bMem, different⟩ := one_lt_card.mp large
  obtain ⟨u, uMem, singleton⟩ := member (singleton_subset_iff.mpr aMem)
  simp only [classFamily, constants, image_insert, image_singleton, mem_insert, mem_singleton]
    at uMem
  rcases uMem with rfl | rfl
  · simp at singleton
  · have := congrArg (fun set : Finset Point => b ∈ set) singleton
    simp [bMem, different.symm] at this

/-- The class of all hypotheses shatters the whole domain. -/
theorem all_shatters_univ [DecidableEq Point] :
    (classFamily (univ : Finset (Point → Bool))).Shatters univ := by
  intro subset _
  refine ⟨subset, ?_, by simp⟩
  simp only [classFamily, mem_image, mem_univ, true_and]
  exact ⟨fun x => decide (x ∈ subset), by ext x; simp⟩

/-! ## Online learning by halving -/

/-- The majority prediction of a set of hypotheses: `true` when strictly more than
half of them say `true`. -/
def majority (hypotheses : Finset (Point → Bool)) (x : Point) : Bool :=
  decide (hypotheses.card < 2 * (hypotheses.filter fun hypothesis => hypothesis x = true).card)

/-- The mistakes the halving learner makes on a sequence of points, starting from a
set of hypotheses and keeping those consistent with each revealed label. -/
def halvingMistakes (target : Point → Bool) :
    Finset (Point → Bool) → List Point → ℕ
  | _, [] => 0
  | hypotheses, x :: rest =>
      (if majority hypotheses x = target x then 0 else 1) +
        halvingMistakes target (hypotheses.filter fun hypothesis => hypothesis x = target x) rest

omit [Fintype Point] in
/-- A mistake leaves at most half of the hypotheses. -/
theorem card_consistent_le_half_of_mistake (hypotheses : Finset (Point → Bool))
    (target : Point → Bool) (x : Point) (mistake : majority hypotheses x ≠ target x) :
    2 * (hypotheses.filter fun hypothesis => hypothesis x = target x).card ≤ hypotheses.card := by
  have partition := card_filter_add_card_filter_not (s := hypotheses)
    (fun hypothesis : Point → Bool => hypothesis x = true)
  cases targetValue : target x with
  | true =>
      rw [targetValue] at mistake
      simp only [majority, ne_eq, decide_eq_true_eq, not_lt] at mistake
      exact mistake
  | false =>
      rw [targetValue] at mistake
      simp only [majority, ne_eq, decide_eq_false_iff_not, not_not] at mistake
      have falseIsNotTrue : (hypotheses.filter fun hypothesis : Point → Bool => hypothesis x = false) =
          hypotheses.filter fun hypothesis => ¬ hypothesis x = true := by
        congr 1
        funext hypothesis
        simp
      rw [falseIsNotTrue]
      omega

omit [Fintype Point] in
/-- **The halving mistake bound.**  When the target is among the hypotheses, two to
the number of mistakes never exceeds the number of hypotheses. -/
theorem halving_mistake_bound (target : Point → Bool) (hypotheses : Finset (Point → Bool))
    (realizable : target ∈ hypotheses) (points : List Point) :
    2 ^ halvingMistakes target hypotheses points ≤ hypotheses.card := by
  induction points generalizing hypotheses with
  | nil => exact card_pos.mpr ⟨target, realizable⟩
  | cons x rest ih =>
      have kept : target ∈ hypotheses.filter fun hypothesis => hypothesis x = target x :=
        mem_filter.mpr ⟨realizable, rfl⟩
      have smaller := ih _ kept
      simp only [halvingMistakes]
      split_ifs with correct
      · simp only [zero_add]
        exact smaller.trans (card_filter_le _ _)
      · rw [add_comm, pow_succ]
        have halved := card_consistent_le_half_of_mistake hypotheses target x correct
        omega

omit [Fintype Point] in
theorem halving_mistakes_le_log (target : Point → Bool) (hypotheses : Finset (Point → Bool))
    (realizable : target ∈ hypotheses) (points : List Point) :
    halvingMistakes target hypotheses points ≤ Nat.log 2 hypotheses.card :=
  Nat.le_log_of_pow_le (by norm_num) (halving_mistake_bound target hypotheses realizable points)

omit [Fintype Point] in
/-- **Realizability is load-bearing.**  With no hypotheses at all, the learner
predicts `false` and errs on every point labeled `true`. -/
theorem halving_without_target (x : Point) :
    halvingMistakes (fun _ => true) ∅ [x, x] = 2 := by
  simp [halvingMistakes, majority]

#print axioms sampleProb_consistent
#print axioms occam_bound
#print axioms occam_sample_complexity
#print axioms no_free_lunch_unseen
#print axioms vc_occam_bound
#print axioms constants_vcDim_le_one
#print axioms halving_mistake_bound
#print axioms halving_mistakes_le_log
#print axioms all_shatters_univ

end Mettapedia.LearningTheory
