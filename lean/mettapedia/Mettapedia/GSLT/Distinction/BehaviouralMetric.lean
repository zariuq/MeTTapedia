import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mettapedia.Cybernetics.DistinctionCalculus.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Behavioural distance over a GSLT and its quantitative Hennessy–Milner theorem

A distinction-calculus observer is a similarity kernel; over a GSLT the kernel
that respects the dynamics is a behavioural distance.  This module builds it
for a labelled system over a GSLT (`HennessyMilner.System`) whose observations
are graded, that is valued in `[0, 1]`, and proves that it is characterised by
a real-valued modal logic.

* **Graded observations** (`GradedObservations`) read a term into `[0, 1]` and
  cannot separate equated terms.  Crisp observations are the indicator case
  (`GradedObservations.ofSystem`).
* **The logic** (`GradedFormula`) is the functional logic of Desharnais, Gupta,
  Jagadeesan and Panangaden (*Metrics for labelled Markov processes*, TCS 318,
  2004, Definition 4.1): `1`, `1 − f`, `min`, the truncated shift `f ⊖ q`
  (here clamped to `[0, 1]`, so a negative threshold is a truncated addition),
  and a diamond.  Over nondeterministic steps the diamond is the discounted
  supremum over the successors, `⟨a⟩f = c · sup f`, as in the branching
  metrics of de Alfaro, Faella and Stoelinga and the metric transition systems
  of Forster, Goncharov, Hofmann, Nora, Schröder and Wild (CSL 2023).
* **Logical distance** (`logicalDistance`) is the supremum of the differences
  of all formulas.  It is a pseudometric bounded by one.
* **Bisimulation metrics** (`IsBisimMetric`) are the prefixed points of the
  Hausdorff functional: they dominate the observations, and every labelled
  step of one side is matched, up to every positive slack, by a step of the
  other side at discounted distance, or the pair is already at distance at
  least the discount.  The **behavioural distance** (`behaviouralDistance`) is
  their infimum, the least fixed point in the sense of van Breugel and
  Worrell.
* **Adequacy** (`logicalDistance_le_behaviouralDistance`): the logical distance
  is below every bisimulation metric.  No hypothesis is needed.
* **Expressivity** (`isBisimMetric_logicalDistance`): when every term has
  finitely many successor classes under each label, the logical distance is
  itself a bisimulation metric.  Hence the **quantitative Hennessy–Milner
  theorem** (`behaviouralDistance_eq_logicalDistance`): behavioural and
  logical distance coincide.
* **The zero kernel** (`logicalDistance_eq_zero_iff`): with a positive discount
  and finite branching, distance zero is bisimilarity that preserves every
  graded observation; for crisp observations it is the bisimilarity of the
  system (`logicalDistance_ofSystem_eq_zero_iff`).
* **The distinction-calculus observer** (`toTolerance`): `1 − d` is a real
  tolerance satisfying the metric law, whose indistinguishable pairs are the
  zero kernel.

The controls are in `BehaviouralMetricControls`: without finite branching the
logical distance of two states can be `0` while their behavioural distance is
`1`, and a threshold of the distance is not transitive.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner

universe uS uAtom uLabel uObs

/-! ## Clamping to the unit interval -/

/-- Clamp a real number to `[0, 1]`. -/
def clamp (value : ℝ) : ℝ := max 0 (min 1 value)

theorem clamp_nonneg (value : ℝ) : 0 ≤ clamp value := le_max_left _ _

theorem clamp_le_one (value : ℝ) : clamp value ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem clamp_of_mem {value : ℝ} (nonneg : 0 ≤ value) (le_one : value ≤ 1) :
    clamp value = value := by
  unfold clamp
  rw [min_eq_right le_one, max_eq_right nonneg]

theorem clamp_lt_of_lt {value bound : ℝ} (positive : 0 < bound) (below : value < bound) :
    clamp value < bound :=
  max_lt positive (lt_of_le_of_lt (min_le_right _ _) below)

/-- Clamping does not increase differences. -/
theorem abs_clamp_sub_clamp_le (first second : ℝ) :
    |clamp first - clamp second| ≤ |first - second| := by
  unfold clamp
  calc |max 0 (min 1 first) - max 0 (min 1 second)|
      ≤ max |(0 : ℝ) - 0| |min 1 first - min 1 second| := abs_max_sub_max_le_max _ _ _ _
    _ ≤ |first - second| := by
      rw [sub_self, abs_zero]
      refine max_le (abs_nonneg _) ?_
      calc |min 1 first - min 1 second| ≤ max |(1 : ℝ) - 1| |first - second| :=
            abs_min_sub_min_le_max _ _ _ _
        _ = |first - second| := by rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]

/-! ## Graded observations and graded systems -/

/-- **Graded observations** on a GSLT: readings in `[0, 1]` that cannot
separate equated terms. -/
structure GradedObservations (S : GSLT.{uS}) where
  /-- The observation names. -/
  Atom : Type uObs
  /-- The reading of a term. -/
  value : Atom → S.Term → ℝ
  value_nonneg : ∀ atom term, 0 ≤ value atom term
  value_le_one : ∀ atom term, value atom term ≤ 1
  /-- Equated terms read alike. -/
  value_resp : ∀ atom {left right : S.Term}, S.Equiv left right → value atom left = value atom right

set_option linter.checkUnivs false in
/-- A **graded system** over a GSLT: labelled dynamics, graded observations and
a discount in `[0, 1]`.  The crisp atoms of the dynamics are not read; crisp
observations enter through `GradedObservations.ofSystem`. -/
structure GradedSystem (S : GSLT.{uS}) where
  /-- The labelled steps. -/
  dynamics : System.{uAtom, uLabel} S
  /-- The graded observations. -/
  observations : GradedObservations.{uS, uObs} S
  /-- The weight of one step into the future. -/
  discount : ℝ
  discount_nonneg : 0 ≤ discount
  discount_le_one : discount ≤ 1

/-! ## The logic -/

/-- Real-valued Hennessy–Milner formulas: truth, a graded atom, `1 − f`, `min`,
the clamped shift `f ⊖ q`, and the discounted diamond. -/
inductive GradedFormula (Atom : Type uObs) (Label : Type uLabel) : Type (max uObs uLabel) where
  | top : GradedFormula Atom Label
  | atom (atom : Atom) : GradedFormula Atom Label
  | neg (inner : GradedFormula Atom Label) : GradedFormula Atom Label
  | conj (left right : GradedFormula Atom Label) : GradedFormula Atom Label
  | shift (threshold : ℝ) (inner : GradedFormula Atom Label) : GradedFormula Atom Label
  | dia (label : Label) (inner : GradedFormula Atom Label) : GradedFormula Atom Label

instance {Atom : Type uObs} {Label : Type uLabel} : Inhabited (GradedFormula Atom Label) :=
  ⟨.top⟩

/-- Finite conjunction. -/
def GradedFormula.conjList {Atom : Type uObs} {Label : Type uLabel} :
    List (GradedFormula Atom Label) → GradedFormula Atom Label
  | [] => .top
  | formula :: formulas => .conj formula (GradedFormula.conjList formulas)

namespace GradedSystem

variable {S : GSLT.{uS}} (Q : GradedSystem.{uS, uAtom, uLabel, uObs} S)

/-- The formulas of a graded system. -/
abbrev Formula : Type (max uObs uLabel) := GradedFormula Q.observations.Atom Q.dynamics.Label

/-- The successors of a term under a label. -/
def successors (label : Q.dynamics.Label) (term : S.Term) : Set S.Term :=
  {target | Q.dynamics.act label term target}

/-- The value of a formula at a term. -/
noncomputable def eval : Q.Formula → S.Term → ℝ
  | .top, _ => 1
  | .atom atom, term => Q.observations.value atom term
  | .neg inner, term => 1 - eval inner term
  | .conj left right, term => min (eval left term) (eval right term)
  | .shift threshold inner, term => clamp (eval inner term - threshold)
  | .dia label inner, term => Q.discount * sSup ((eval inner) '' Q.successors label term)

@[simp] theorem eval_top (term : S.Term) : Q.eval .top term = 1 := rfl

@[simp] theorem eval_atom (atom : Q.observations.Atom) (term : S.Term) :
    Q.eval (.atom atom) term = Q.observations.value atom term := rfl

@[simp] theorem eval_neg (inner : Q.Formula) (term : S.Term) :
    Q.eval (.neg inner) term = 1 - Q.eval inner term := rfl

@[simp] theorem eval_conj (left right : Q.Formula) (term : S.Term) :
    Q.eval (.conj left right) term = min (Q.eval left term) (Q.eval right term) := rfl

@[simp] theorem eval_shift (threshold : ℝ) (inner : Q.Formula) (term : S.Term) :
    Q.eval (.shift threshold inner) term = clamp (Q.eval inner term - threshold) := rfl

@[simp] theorem eval_dia (label : Q.dynamics.Label) (inner : Q.Formula) (term : S.Term) :
    Q.eval (.dia label inner) term =
      Q.discount * sSup ((Q.eval inner) '' Q.successors label term) := rfl

/-- Every formula takes values in `[0, 1]`. -/
theorem eval_mem : ∀ (formula : Q.Formula) (term : S.Term),
    0 ≤ Q.eval formula term ∧ Q.eval formula term ≤ 1
  | .top, _ => ⟨zero_le_one, le_rfl⟩
  | .atom atom, term => ⟨Q.observations.value_nonneg atom term, Q.observations.value_le_one atom term⟩
  | .neg inner, term => by
      have bounds := eval_mem inner term
      rw [eval_neg]
      constructor <;> linarith [bounds.1, bounds.2]
  | .conj left right, term => by
      have leftBounds := eval_mem left term
      have rightBounds := eval_mem right term
      rw [eval_conj]
      exact ⟨le_min leftBounds.1 rightBounds.1, min_le_of_left_le leftBounds.2⟩
  | .shift threshold inner, term => ⟨clamp_nonneg _, clamp_le_one _⟩
  | .dia label inner, term => by
      rw [eval_dia]
      have nonneg : 0 ≤ sSup ((Q.eval inner) '' Q.successors label term) :=
        Real.sSup_nonneg (by rintro _ ⟨target, -, rfl⟩; exact (eval_mem inner target).1)
      have le_one : sSup ((Q.eval inner) '' Q.successors label term) ≤ 1 :=
        Real.sSup_le (by rintro _ ⟨target, -, rfl⟩; exact (eval_mem inner target).2) zero_le_one
      constructor
      · exact mul_nonneg Q.discount_nonneg nonneg
      · calc Q.discount * sSup ((Q.eval inner) '' Q.successors label term)
            ≤ 1 * sSup ((Q.eval inner) '' Q.successors label term) :=
              mul_le_mul_of_nonneg_right Q.discount_le_one nonneg
          _ ≤ 1 := by linarith

theorem eval_nonneg (formula : Q.Formula) (term : S.Term) : 0 ≤ Q.eval formula term :=
  (Q.eval_mem formula term).1

theorem eval_le_one (formula : Q.Formula) (term : S.Term) : Q.eval formula term ≤ 1 :=
  (Q.eval_mem formula term).2

theorem bddAbove_image (formula : Q.Formula) (terms : Set S.Term) :
    BddAbove ((Q.eval formula) '' terms) :=
  ⟨1, by rintro _ ⟨term, -, rfl⟩; exact Q.eval_le_one formula term⟩

theorem sSup_image_nonneg (formula : Q.Formula) (terms : Set S.Term) :
    0 ≤ sSup ((Q.eval formula) '' terms) :=
  Real.sSup_nonneg (by rintro _ ⟨term, -, rfl⟩; exact Q.eval_nonneg formula term)

theorem sSup_image_le_one (formula : Q.Formula) (terms : Set S.Term) :
    sSup ((Q.eval formula) '' terms) ≤ 1 :=
  Real.sSup_le (by rintro _ ⟨term, -, rfl⟩; exact Q.eval_le_one formula term) zero_le_one

/-- **Formulas are predicates on equation classes.** -/
theorem eval_resp : ∀ (formula : Q.Formula) {left right : S.Term},
    S.Equiv left right → Q.eval formula left = Q.eval formula right
  | .top, _, _, _ => rfl
  | .atom atom, _, _, equivalent => Q.observations.value_resp atom equivalent
  | .neg inner, _, _, equivalent => by
      rw [eval_neg, eval_neg, eval_resp inner equivalent]
  | .conj left right, _, _, equivalent => by
      rw [eval_conj, eval_conj, eval_resp left equivalent, eval_resp right equivalent]
  | .shift threshold inner, _, _, equivalent => by
      rw [eval_shift, eval_shift, eval_resp inner equivalent]
  | .dia label inner, first, second, equivalent => by
      rw [eval_dia, eval_dia]
      congr 2
      ext value
      constructor
      · rintro ⟨target, step, rfl⟩
        obtain ⟨target', step', targetEquivalent⟩ := Q.dynamics.act_resp_left equivalent step
        exact ⟨target', step', (eval_resp inner targetEquivalent).symm⟩
      · rintro ⟨target, step, rfl⟩
        obtain ⟨target', step', targetEquivalent⟩ :=
          Q.dynamics.act_resp_left (S.equations.iseqv.symm equivalent) step
        exact ⟨target', step', (eval_resp inner targetEquivalent).symm⟩

theorem eval_conjList_eq_one (formulas : List Q.Formula) (term : S.Term)
    (each : ∀ formula ∈ formulas, Q.eval formula term = 1) :
    Q.eval (GradedFormula.conjList formulas) term = 1 := by
  induction formulas with
  | nil => rfl
  | cons formula formulas inductionHypothesis =>
      simp only [GradedFormula.conjList, eval_conj]
      rw [each formula List.mem_cons_self,
        inductionHypothesis fun other member => each other (List.mem_cons_of_mem _ member), min_self]

theorem eval_conjList_le (formulas : List Q.Formula) (term : S.Term) {formula : Q.Formula}
    (member : formula ∈ formulas) :
    Q.eval (GradedFormula.conjList formulas) term ≤ Q.eval formula term := by
  induction formulas with
  | nil => exact absurd member List.not_mem_nil
  | cons head formulas inductionHypothesis =>
      simp only [GradedFormula.conjList, eval_conj]
      rcases List.mem_cons.mp member with rfl | member
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (inductionHypothesis member)

/-! ## Logical distance -/

/-- **Logical distance**: the largest difference of a formula at two terms. -/
noncomputable def logicalDistance (left right : S.Term) : ℝ :=
  ⨆ formula : Q.Formula, |Q.eval formula left - Q.eval formula right|

theorem abs_eval_sub_le_one (formula : Q.Formula) (left right : S.Term) :
    |Q.eval formula left - Q.eval formula right| ≤ 1 := by
  rw [abs_le]
  constructor <;>
    linarith [Q.eval_nonneg formula left, Q.eval_le_one formula left,
      Q.eval_nonneg formula right, Q.eval_le_one formula right]

theorem bddAbove_differences (left right : S.Term) :
    BddAbove (Set.range fun formula : Q.Formula =>
      |Q.eval formula left - Q.eval formula right|) :=
  ⟨1, by rintro _ ⟨formula, rfl⟩; exact Q.abs_eval_sub_le_one formula left right⟩

theorem abs_eval_sub_le_logicalDistance (formula : Q.Formula) (left right : S.Term) :
    |Q.eval formula left - Q.eval formula right| ≤ Q.logicalDistance left right :=
  le_ciSup (Q.bddAbove_differences left right) formula

theorem logicalDistance_le_iff {left right : S.Term} {bound : ℝ} :
    Q.logicalDistance left right ≤ bound ↔
      ∀ formula : Q.Formula, |Q.eval formula left - Q.eval formula right| ≤ bound :=
  ⟨fun le formula => (Q.abs_eval_sub_le_logicalDistance formula left right).trans le,
    fun each => ciSup_le each⟩

theorem logicalDistance_nonneg (left right : S.Term) : 0 ≤ Q.logicalDistance left right :=
  (abs_nonneg _).trans (Q.abs_eval_sub_le_logicalDistance .top left right)

theorem logicalDistance_le_one (left right : S.Term) : Q.logicalDistance left right ≤ 1 :=
  Q.logicalDistance_le_iff.mpr fun formula => Q.abs_eval_sub_le_one formula left right

@[simp] theorem logicalDistance_self (term : S.Term) : Q.logicalDistance term term = 0 :=
  le_antisymm (Q.logicalDistance_le_iff.mpr fun formula => by simp)
    (Q.logicalDistance_nonneg term term)

theorem logicalDistance_symm (left right : S.Term) :
    Q.logicalDistance left right = Q.logicalDistance right left := by
  unfold logicalDistance
  congr 1
  funext formula
  exact abs_sub_comm _ _

/-- The logical distance satisfies the triangle inequality. -/
theorem logicalDistance_triangle (first second third : S.Term) :
    Q.logicalDistance first third ≤
      Q.logicalDistance first second + Q.logicalDistance second third :=
  Q.logicalDistance_le_iff.mpr fun formula =>
    (abs_sub_le _ (Q.eval formula second) _).trans
      (add_le_add (Q.abs_eval_sub_le_logicalDistance formula first second)
        (Q.abs_eval_sub_le_logicalDistance formula second third))

theorem logicalDistance_resp_left {left left' : S.Term} (equivalent : S.Equiv left left')
    (right : S.Term) : Q.logicalDistance left right = Q.logicalDistance left' right := by
  unfold logicalDistance
  congr 1
  funext formula
  rw [Q.eval_resp formula equivalent]

theorem logicalDistance_resp_right (left : S.Term) {right right' : S.Term}
    (equivalent : S.Equiv right right') :
    Q.logicalDistance left right = Q.logicalDistance left right' := by
  unfold logicalDistance
  congr 1
  funext formula
  rw [Q.eval_resp formula equivalent]

/-! ## Bisimulation metrics -/

/-- A **bisimulation metric**: a prefixed point of the Hausdorff functional.
It dominates every graded observation, and a labelled step of either side is
matched, up to every positive slack, by a step of the other side at discounted
distance, unless the pair is already at distance at least the discount (the
Hausdorff distance to an empty successor set is one). -/
structure IsBisimMetric (distance : S.Term → S.Term → ℝ) : Prop where
  nonneg : ∀ left right, 0 ≤ distance left right
  observes : ∀ atom left right,
    |Q.observations.value atom left - Q.observations.value atom right| ≤ distance left right
  forth : ∀ label left right left', Q.dynamics.act label left left' →
    Q.discount ≤ distance left right ∨
      ∀ ε > 0, ∃ right', Q.dynamics.act label right right' ∧
        Q.discount * distance left' right' ≤ distance left right + ε
  back : ∀ label left right right', Q.dynamics.act label right right' →
    Q.discount ≤ distance left right ∨
      ∀ ε > 0, ∃ left', Q.dynamics.act label left left' ∧
        Q.discount * distance left' right' ≤ distance left right + ε

/-- The diamond estimate behind adequacy: a discounted supremum over a source
set exceeds one over a target set by at most the gap, when every source point
is matched in the target up to every slack. -/
theorem discount_mul_sSup_le_of_transfer (inner : Q.Formula) {source target : Set S.Term}
    {gap : ℝ} {cost : S.Term → S.Term → ℝ} (gap_nonneg : 0 ≤ gap)
    (lipschitz : ∀ first second, Q.eval inner first ≤ Q.eval inner second + cost first second)
    (transfer : ∀ first ∈ source, Q.discount ≤ gap ∨
      ∀ ε > 0, ∃ second ∈ target, Q.discount * cost first second ≤ gap + ε) :
    Q.discount * sSup ((Q.eval inner) '' source) ≤
      Q.discount * sSup ((Q.eval inner) '' target) + gap := by
  have targetNonneg := Q.sSup_image_nonneg inner target
  by_cases large : Q.discount ≤ gap
  · have sourceLe := Q.sSup_image_le_one inner source
    have := mul_le_mul_of_nonneg_left sourceLe Q.discount_nonneg
    nlinarith [mul_nonneg Q.discount_nonneg targetNonneg]
  · have each : ∀ first ∈ source, Q.discount * Q.eval inner first ≤
        Q.discount * sSup ((Q.eval inner) '' target) + gap := by
      intro first member
      rcases transfer first member with tooLarge | matched
      · exact absurd tooLarge large
      · refine le_of_forall_pos_le_add fun ε positive => ?_
        obtain ⟨second, secondMember, close⟩ := matched ε positive
        have inSup : Q.eval inner second ≤ sSup ((Q.eval inner) '' target) :=
          le_csSup (Q.bddAbove_image inner target) ⟨second, secondMember, rfl⟩
        have step := lipschitz first second
        calc Q.discount * Q.eval inner first
            ≤ Q.discount * (Q.eval inner second + cost first second) :=
              mul_le_mul_of_nonneg_left step Q.discount_nonneg
          _ = Q.discount * Q.eval inner second + Q.discount * cost first second := by ring
          _ ≤ Q.discount * sSup ((Q.eval inner) '' target) + (gap + ε) :=
              add_le_add (mul_le_mul_of_nonneg_left inSup Q.discount_nonneg) close
          _ = Q.discount * sSup ((Q.eval inner) '' target) + gap + ε := by ring
    rcases ((Q.eval inner) '' source).eq_empty_or_nonempty with empty | nonempty
    · rw [empty, Real.sSup_empty, mul_zero]
      exact add_nonneg (mul_nonneg Q.discount_nonneg targetNonneg) gap_nonneg
    · rcases Q.discount_nonneg.lt_or_eq with positive | zero
      · have bound : sSup ((Q.eval inner) '' source) ≤
            (Q.discount * sSup ((Q.eval inner) '' target) + gap) / Q.discount := by
          apply csSup_le nonempty
          rintro _ ⟨first, member, rfl⟩
          rw [le_div_iff₀ positive]
          linarith [each first member]
        calc Q.discount * sSup ((Q.eval inner) '' source)
            ≤ Q.discount * ((Q.discount * sSup ((Q.eval inner) '' target) + gap) /
                Q.discount) := mul_le_mul_of_nonneg_left bound Q.discount_nonneg
          _ = Q.discount * sSup ((Q.eval inner) '' target) + gap := by
              field_simp
      · rw [← zero, zero_mul, zero_mul, zero_add]
        exact gap_nonneg

/-- **Adequacy, pointwise.** Every formula is nonexpansive for every
bisimulation metric. -/
theorem abs_eval_sub_le {distance : S.Term → S.Term → ℝ} (bisim : Q.IsBisimMetric distance) :
    ∀ (formula : Q.Formula) (left right : S.Term),
      |Q.eval formula left - Q.eval formula right| ≤ distance left right
  | .top, left, right => by
      rw [eval_top, eval_top, sub_self, abs_zero]
      exact bisim.nonneg left right
  | .atom atom, left, right => bisim.observes atom left right
  | .neg inner, left, right => by
      rw [eval_neg, eval_neg, show (1 - Q.eval inner left) - (1 - Q.eval inner right) =
        Q.eval inner right - Q.eval inner left by ring, abs_sub_comm]
      exact abs_eval_sub_le bisim inner left right
  | .conj first second, left, right => by
      rw [eval_conj, eval_conj]
      exact (abs_min_sub_min_le_max _ _ _ _).trans
        (max_le (abs_eval_sub_le bisim first left right) (abs_eval_sub_le bisim second left right))
  | .shift threshold inner, left, right => by
      rw [eval_shift, eval_shift]
      refine (abs_clamp_sub_clamp_le _ _).trans ?_
      rw [show (Q.eval inner left - threshold) - (Q.eval inner right - threshold) =
        Q.eval inner left - Q.eval inner right by ring]
      exact abs_eval_sub_le bisim inner left right
  | .dia label inner, left, right => by
      have inductionHypothesis := abs_eval_sub_le bisim inner
      rw [eval_dia, eval_dia, abs_le]
      constructor
      · have backward := Q.discount_mul_sSup_le_of_transfer inner
          (source := Q.successors label right) (target := Q.successors label left)
          (cost := fun first second => distance second first) (bisim.nonneg left right)
          (fun first second => by
            have bound := inductionHypothesis second first
            rw [abs_le] at bound
            linarith [bound.1])
          (fun first member => (bisim.back label left right first member).imp id
            fun matched ε positive => by
              obtain ⟨second, step, close⟩ := matched ε positive
              exact ⟨second, step, close⟩)
        linarith
      · have forward := Q.discount_mul_sSup_le_of_transfer inner
          (source := Q.successors label left) (target := Q.successors label right)
          (cost := distance) (bisim.nonneg left right)
          (fun first second => by
            have bound := inductionHypothesis first second
            rw [abs_le] at bound
            linarith [bound.2])
          (fun first member => bisim.forth label left right first member)
        linarith

/-- The logical distance lies below every bisimulation metric. -/
theorem logicalDistance_le_of_isBisimMetric {distance : S.Term → S.Term → ℝ}
    (bisim : Q.IsBisimMetric distance) (left right : S.Term) :
    Q.logicalDistance left right ≤ distance left right :=
  Q.logicalDistance_le_iff.mpr fun formula => Q.abs_eval_sub_le bisim formula left right

/-- The constant distance one is a bisimulation metric. -/
theorem isBisimMetric_one : Q.IsBisimMetric fun _ _ => 1 where
  nonneg _ _ := zero_le_one
  observes atom left right := by
    rw [abs_le]
    constructor <;>
      linarith [Q.observations.value_nonneg atom left, Q.observations.value_le_one atom left,
        Q.observations.value_nonneg atom right, Q.observations.value_le_one atom right]
  forth _ _ _ _ _ := Or.inl Q.discount_le_one
  back _ _ _ _ _ := Or.inl Q.discount_le_one

instance : Nonempty {distance : S.Term → S.Term → ℝ // Q.IsBisimMetric distance} :=
  ⟨⟨_, Q.isBisimMetric_one⟩⟩

/-- **Behavioural distance**: the infimum of all bisimulation metrics. -/
noncomputable def behaviouralDistance (left right : S.Term) : ℝ :=
  ⨅ distance : {distance : S.Term → S.Term → ℝ // Q.IsBisimMetric distance},
    distance.1 left right

theorem behaviouralDistance_le {distance : S.Term → S.Term → ℝ}
    (bisim : Q.IsBisimMetric distance) (left right : S.Term) :
    Q.behaviouralDistance left right ≤ distance left right :=
  ciInf_le (show BddBelow (Set.range fun other :
      {distance : S.Term → S.Term → ℝ // Q.IsBisimMetric distance} => other.1 left right) from
    ⟨0, by rintro _ ⟨other, rfl⟩; exact other.2.nonneg left right⟩) ⟨distance, bisim⟩

theorem le_behaviouralDistance {left right : S.Term} {bound : ℝ}
    (below : ∀ distance, Q.IsBisimMetric distance → bound ≤ distance left right) :
    bound ≤ Q.behaviouralDistance left right :=
  le_ciInf fun distance => below distance.1 distance.2

theorem behaviouralDistance_le_one (left right : S.Term) :
    Q.behaviouralDistance left right ≤ 1 :=
  Q.behaviouralDistance_le Q.isBisimMetric_one left right

/-- **Adequacy.** The logical distance never exceeds the behavioural distance. -/
theorem logicalDistance_le_behaviouralDistance (left right : S.Term) :
    Q.logicalDistance left right ≤ Q.behaviouralDistance left right :=
  Q.le_behaviouralDistance fun _ bisim => Q.logicalDistance_le_of_isBisimMetric bisim left right

/-! ## Expressivity under finite branching -/

/-- A formula that is `1` at a given term and below a given bound at another
term, built from any formula separating the two by more than the gap. -/
theorem exists_peaked_formula {peak other : S.Term} {gap : ℝ} (gap_lt_one : gap < 1)
    (separated : gap < Q.logicalDistance peak other) :
    ∃ formula : Q.Formula, Q.eval formula peak = 1 ∧ Q.eval formula other < 1 - gap := by
  obtain ⟨formula, far⟩ := exists_lt_of_lt_ciSup separated
  have positive : 0 < 1 - gap := by linarith
  by_cases oriented : Q.eval formula other ≤ Q.eval formula peak
  · rw [abs_of_nonneg (sub_nonneg.mpr oriented)] at far
    refine ⟨.shift (Q.eval formula peak - 1) formula, ?_, ?_⟩
    · rw [eval_shift, show Q.eval formula peak - (Q.eval formula peak - 1) = 1 by ring]
      exact clamp_of_mem zero_le_one le_rfl
    · rw [eval_shift]
      exact clamp_lt_of_lt positive (by linarith)
  · have reversed : Q.eval formula peak < Q.eval formula other := lt_of_not_ge oriented
    rw [abs_of_neg (sub_neg.mpr reversed)] at far
    refine ⟨.shift (Q.eval (.neg formula) peak - 1) (.neg formula), ?_, ?_⟩
    · rw [eval_shift, show Q.eval (.neg formula) peak - (Q.eval (.neg formula) peak - 1) = 1 by
        ring]
      exact clamp_of_mem zero_le_one le_rfl
    · rw [eval_shift, eval_neg, eval_neg]
      exact clamp_lt_of_lt positive (by linarith)

/-- A term has **finitely many successor classes** under a label: a finite set
of representatives covers its successors up to the equations. -/
def FinitelyBranchingAt (label : Q.dynamics.Label) (term : S.Term) : Prop :=
  ∃ representatives : Set S.Term, representatives.Finite ∧
    ∀ ⦃target⦄, Q.dynamics.act label term target →
      ∃ representative ∈ representatives, S.Equiv target representative

/-- **The matching step, pointwise.** When the matching side has finitely many
successor classes under the label, a step of the other side is matched at
discounted logical distance, or the pair is at logical distance at least the
discount. -/
theorem exists_matching_successor_of_branching (label : Q.dynamics.Label)
    {left right left' : S.Term} (branching : Q.FinitelyBranchingAt label right)
    (step : Q.dynamics.act label left left') :
    Q.discount ≤ Q.logicalDistance left right ∨
      ∃ right', Q.dynamics.act label right right' ∧
        Q.discount * Q.logicalDistance left' right' ≤ Q.logicalDistance left right := by
  by_contra contrary
  push Not at contrary
  obtain ⟨small, far⟩ := contrary
  have gapNonneg := Q.logicalDistance_nonneg left right
  have positive : 0 < Q.discount := lt_of_le_of_lt gapNonneg small
  set gap := Q.logicalDistance left right with gapDef
  have gapRatio : gap / Q.discount < 1 := (div_lt_one positive).mpr small
  have separators : ∀ candidate : S.Term, ∃ formula : Q.Formula,
      Q.eval formula left' = 1 ∧
        ((∃ target, Q.dynamics.act label right target ∧ S.Equiv target candidate) →
          Q.eval formula candidate < 1 - gap / Q.discount) := by
    intro candidate
    by_cases reachable : ∃ target, Q.dynamics.act label right target ∧ S.Equiv target candidate
    · obtain ⟨target, targetStep, equivalent⟩ := reachable
      have separated : gap / Q.discount < Q.logicalDistance left' candidate := by
        rw [div_lt_iff₀ positive, ← Q.logicalDistance_resp_right left' equivalent, mul_comm]
        exact far target targetStep
      obtain ⟨formula, top, low⟩ := Q.exists_peaked_formula gapRatio separated
      exact ⟨formula, top, fun _ => low⟩
    · exact ⟨.top, rfl, fun reached => absurd reached reachable⟩
  choose separator separatorTop separatorLow using separators
  obtain ⟨representatives, representativesFinite, covered⟩ := branching
  obtain ⟨finiteRepresentatives, coe⟩ := representativesFinite.exists_finset_coe
  let bundle : Q.Formula :=
    GradedFormula.conjList (finiteRepresentatives.toList.map separator)
  have bundleTop : Q.eval bundle left' = 1 :=
    Q.eval_conjList_eq_one _ _ fun formula member => by
      obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp member
      exact separatorTop candidate
  have bundleLow : ∀ target, Q.dynamics.act label right target →
      Q.eval bundle target < 1 - gap / Q.discount := by
    intro target targetStep
    obtain ⟨representative, membership, equivalent⟩ := covered targetStep
    rw [Q.eval_resp bundle equivalent]
    have inList : separator representative ∈ finiteRepresentatives.toList.map separator := by
      apply List.mem_map.mpr
      refine ⟨representative, ?_, rfl⟩
      rw [Finset.mem_toList, ← Finset.mem_coe, coe]
      exact membership
    exact lt_of_le_of_lt (Q.eval_conjList_le _ _ inList)
      (separatorLow representative ⟨target, targetStep, equivalent⟩)
  have probeLeft : Q.discount ≤ Q.eval (.dia label bundle) left := by
    rw [eval_dia]
    have : 1 ≤ sSup ((Q.eval bundle) '' Q.successors label left) := by
      rw [← bundleTop]
      exact le_csSup (Q.bddAbove_image bundle _) ⟨left', step, rfl⟩
    nlinarith
  have probeRight : Q.eval (.dia label bundle) right < Q.discount - gap := by
    rw [eval_dia]
    rcases ((Q.eval bundle) '' Q.successors label right).eq_empty_or_nonempty with
      empty | nonempty
    · rw [empty, Real.sSup_empty, mul_zero]
      linarith
    · have finiteImage : ((Q.eval bundle) '' Q.successors label right).Finite := by
        apply (representativesFinite.image (Q.eval bundle)).subset
        rintro _ ⟨target, targetStep, rfl⟩
        obtain ⟨representative, membership, equivalent⟩ := covered targetStep
        exact ⟨representative, membership, (Q.eval_resp bundle equivalent).symm⟩
      obtain ⟨target, targetStep, attained⟩ := nonempty.csSup_mem finiteImage
      rw [← attained]
      calc Q.discount * Q.eval bundle target < Q.discount * (1 - gap / Q.discount) :=
            mul_lt_mul_of_pos_left (bundleLow target targetStep) positive
        _ = Q.discount - gap := by field_simp
  have bounded := Q.abs_eval_sub_le_logicalDistance (.dia label bundle) left right
  rw [abs_le] at bounded
  linarith [bounded.2]

/-- **The matching step.** Under finite branching modulo the equations, a step
of one side is matched by a step of the other side at discounted logical
distance, or the pair is at logical distance at least the discount. -/
theorem exists_matching_successor (finite : Q.dynamics.ImageFiniteModulo)
    (label : Q.dynamics.Label) {left right left' : S.Term}
    (step : Q.dynamics.act label left left') :
    Q.discount ≤ Q.logicalDistance left right ∨
      ∃ right', Q.dynamics.act label right right' ∧
        Q.discount * Q.logicalDistance left' right' ≤ Q.logicalDistance left right :=
  Q.exists_matching_successor_of_branching label (finite label right) step

/-- **Expressivity.** Under finite branching modulo the equations, the logical
distance is a bisimulation metric. -/
theorem isBisimMetric_logicalDistance (finite : Q.dynamics.ImageFiniteModulo) :
    Q.IsBisimMetric Q.logicalDistance where
  nonneg := Q.logicalDistance_nonneg
  observes atom left right := Q.abs_eval_sub_le_logicalDistance (.atom atom) left right
  forth label left right left' step :=
    (Q.exists_matching_successor finite label step).imp id fun matched ε positive => by
      obtain ⟨right', rightStep, close⟩ := matched
      exact ⟨right', rightStep, by linarith⟩
  back label left right right' step := by
    rcases Q.exists_matching_successor finite label (right := left) step with
      large | ⟨left', leftStep, close⟩
    · left
      rwa [Q.logicalDistance_symm]
    · right
      intro ε positive
      refine ⟨left', leftStep, ?_⟩
      rw [Q.logicalDistance_symm left' right', Q.logicalDistance_symm left right]
      linarith

/-- **The quantitative Hennessy–Milner theorem.** Under finite branching
modulo the equations, behavioural distance is logical distance. -/
theorem behaviouralDistance_eq_logicalDistance (finite : Q.dynamics.ImageFiniteModulo)
    (left right : S.Term) :
    Q.behaviouralDistance left right = Q.logicalDistance left right :=
  le_antisymm (Q.behaviouralDistance_le (Q.isBisimMetric_logicalDistance finite) left right)
    (Q.logicalDistance_le_behaviouralDistance left right)

/-- Under finite branching the behavioural distance is the least bisimulation
metric. -/
theorem isBisimMetric_behaviouralDistance (finite : Q.dynamics.ImageFiniteModulo) :
    Q.IsBisimMetric Q.behaviouralDistance := by
  have same : Q.behaviouralDistance = Q.logicalDistance :=
    funext fun left => funext fun right => Q.behaviouralDistance_eq_logicalDistance finite left right
  rw [same]
  exact Q.isBisimMetric_logicalDistance finite

/-! ## Finite branching on a region -/

/-- A set of terms closed under every labelled step. -/
def StepClosed (region : Set S.Term) : Prop :=
  ∀ (label : Q.dynamics.Label) ⦃term target : S.Term⦄, term ∈ region →
    Q.dynamics.act label term target → target ∈ region

/-- **The quantitative Hennessy–Milner theorem on a region.** On a step-closed
region whose terms have finitely many successor classes under every label,
behavioural and logical distance coincide.  Nothing is assumed outside the
region. -/
theorem behaviouralDistance_eq_logicalDistance_on {region : Set S.Term}
    (closed : Q.StepClosed region)
    (branching : ∀ (label : Q.dynamics.Label) ⦃term : S.Term⦄, term ∈ region →
      Q.FinitelyBranchingAt label term)
    {left right : S.Term} (leftMember : left ∈ region) (rightMember : right ∈ region) :
    Q.behaviouralDistance left right = Q.logicalDistance left right := by
  classical
  let regional : S.Term → S.Term → ℝ := fun first second =>
    if first ∈ region ∧ second ∈ region then Q.logicalDistance first second else 1
  have bisim : Q.IsBisimMetric regional := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro first second
      simp only [regional]
      split_ifs
      · exact Q.logicalDistance_nonneg _ _
      · exact zero_le_one
    · intro atom first second
      simp only [regional]
      split_ifs
      · exact Q.abs_eval_sub_le_logicalDistance (.atom atom) first second
      · exact Q.isBisimMetric_one.observes atom first second
    · intro label first second first' step
      by_cases members : first ∈ region ∧ second ∈ region
      · rcases Q.exists_matching_successor_of_branching label (branching label members.2) step with
          large | ⟨second', secondStep, close⟩
        · left
          simp only [regional, if_pos members]
          exact large
        · right
          intro ε positive
          refine ⟨second', secondStep, ?_⟩
          have nextMembers : first' ∈ region ∧ second' ∈ region :=
            ⟨closed label members.1 step, closed label members.2 secondStep⟩
          simp only [regional, if_pos members, if_pos nextMembers]
          linarith
      · left
        simp only [regional, if_neg members]
        exact Q.discount_le_one
    · intro label first second second' step
      by_cases members : first ∈ region ∧ second ∈ region
      · rcases Q.exists_matching_successor_of_branching label (branching label members.1)
            (right := first) step with large | ⟨first', firstStep, close⟩
        · left
          simp only [regional, if_pos members]
          rwa [Q.logicalDistance_symm]
        · right
          intro ε positive
          refine ⟨first', firstStep, ?_⟩
          have nextMembers : first' ∈ region ∧ second' ∈ region :=
            ⟨closed label members.1 firstStep, closed label members.2 step⟩
          simp only [regional, if_pos members, if_pos nextMembers]
          rw [Q.logicalDistance_symm first' second', Q.logicalDistance_symm first second]
          linarith
      · left
        simp only [regional, if_neg members]
        exact Q.discount_le_one
  have upper := Q.behaviouralDistance_le bisim left right
  simp only [regional, if_pos (And.intro leftMember rightMember)] at upper
  exact le_antisymm upper (Q.logicalDistance_le_behaviouralDistance left right)

/-! ## The zero kernel -/

/-- A bisimulation of the labelled steps that preserves every graded
observation exactly. -/
def IsGradedBisimulation (relation : S.Term → S.Term → Prop) : Prop :=
  (∀ ⦃left right⦄, relation left right → ∀ (label : Q.dynamics.Label) ⦃left'⦄,
      Q.dynamics.act label left left' →
        ∃ right', Q.dynamics.act label right right' ∧ relation left' right') ∧
    (∀ ⦃left right⦄, relation left right → ∀ (label : Q.dynamics.Label) ⦃right'⦄,
      Q.dynamics.act label right right' →
        ∃ left', Q.dynamics.act label left left' ∧ relation left' right') ∧
    (∀ ⦃left right⦄, relation left right → ∀ atom,
      Q.observations.value atom left = Q.observations.value atom right)

/-- Graded bisimilarity: the union of graded bisimulations. -/
def GradedBisimilar (left right : S.Term) : Prop :=
  ∃ relation, Q.IsGradedBisimulation relation ∧ relation left right

/-- The crisp distance of a graded bisimulation is a bisimulation metric. -/
theorem isBisimMetric_of_isGradedBisimulation {relation : S.Term → S.Term → Prop}
    (bisimulation : Q.IsGradedBisimulation relation) [DecidableRel relation] :
    Q.IsBisimMetric fun left right => if relation left right then 0 else 1 where
  nonneg left right := by split_ifs <;> norm_num
  observes atom left right := by
    split_ifs with related
    · rw [bisimulation.2.2 related atom, sub_self, abs_zero]
    · exact Q.isBisimMetric_one.observes atom left right
  forth label left right left' step := by
    by_cases related : relation left right
    · right
      intro ε positive
      obtain ⟨right', rightStep, related'⟩ := bisimulation.1 related label step
      refine ⟨right', rightStep, ?_⟩
      rw [if_pos related', if_pos related, mul_zero]
      linarith
    · left
      rw [if_neg related]
      exact Q.discount_le_one
  back label left right right' step := by
    by_cases related : relation left right
    · right
      intro ε positive
      obtain ⟨left', leftStep, related'⟩ := bisimulation.2.1 related label step
      refine ⟨left', leftStep, ?_⟩
      rw [if_pos related', if_pos related, mul_zero]
      linarith
    · left
      rw [if_neg related]
      exact Q.discount_le_one

/-- Graded bisimilar terms are at behavioural distance zero, with no
finiteness hypothesis. -/
theorem behaviouralDistance_eq_zero_of_gradedBisimilar {left right : S.Term}
    (bisimilar : Q.GradedBisimilar left right) : Q.behaviouralDistance left right = 0 := by
  classical
  obtain ⟨relation, bisimulation, related⟩ := bisimilar
  have bound := Q.behaviouralDistance_le
    (Q.isBisimMetric_of_isGradedBisimulation bisimulation) left right
  rw [if_pos related] at bound
  exact le_antisymm bound ((Q.logicalDistance_nonneg left right).trans
    (Q.logicalDistance_le_behaviouralDistance left right))

/-- Graded bisimilar terms are at logical distance zero. -/
theorem logicalDistance_eq_zero_of_gradedBisimilar {left right : S.Term}
    (bisimilar : Q.GradedBisimilar left right) : Q.logicalDistance left right = 0 :=
  le_antisymm ((Q.logicalDistance_le_behaviouralDistance left right).trans_eq
    (Q.behaviouralDistance_eq_zero_of_gradedBisimilar bisimilar))
    (Q.logicalDistance_nonneg left right)

/-- The equations are a graded bisimulation. -/
theorem isGradedBisimulation_equiv : Q.IsGradedBisimulation S.Equiv := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right equivalent label left' step
    exact Q.dynamics.act_resp_left equivalent step
  · intro left right equivalent label right' step
    obtain ⟨left', step', equivalent'⟩ :=
      Q.dynamics.act_resp_left (S.equations.iseqv.symm equivalent) step
    exact ⟨left', step', S.equations.iseqv.symm equivalent'⟩
  · intro left right equivalent atom
    exact Q.observations.value_resp atom equivalent

@[simp] theorem behaviouralDistance_self (term : S.Term) :
    Q.behaviouralDistance term term = 0 :=
  Q.behaviouralDistance_eq_zero_of_gradedBisimilar
    ⟨S.Equiv, Q.isGradedBisimulation_equiv, S.equations.iseqv.refl term⟩

/-- Under finite branching and a positive discount, logical distance zero is a
graded bisimulation. -/
theorem isGradedBisimulation_logicalDistance_eq_zero (finite : Q.dynamics.ImageFiniteModulo)
    (positive : 0 < Q.discount) :
    Q.IsGradedBisimulation fun left right => Q.logicalDistance left right = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right zero label left' step
    rcases Q.exists_matching_successor finite label (right := right) step with
      large | ⟨right', rightStep, close⟩
    · rw [zero] at large
      exact absurd large (not_le.mpr positive)
    · refine ⟨right', rightStep, ?_⟩
      rw [zero] at close
      have nonneg := Q.logicalDistance_nonneg left' right'
      have : Q.logicalDistance left' right' ≤ 0 := by
        by_contra positiveDistance
        push Not at positiveDistance
        nlinarith [mul_pos positive positiveDistance]
      exact le_antisymm this nonneg
  · intro left right zero label right' step
    have zero' : Q.logicalDistance right left = 0 := by rwa [Q.logicalDistance_symm]
    rcases Q.exists_matching_successor finite label (right := left) step with
      large | ⟨left', leftStep, close⟩
    · rw [zero'] at large
      exact absurd large (not_le.mpr positive)
    · refine ⟨left', leftStep, ?_⟩
      rw [zero'] at close
      have nonneg := Q.logicalDistance_nonneg right' left'
      have : Q.logicalDistance right' left' ≤ 0 := by
        by_contra positiveDistance
        push Not at positiveDistance
        nlinarith [mul_pos positive positiveDistance]
      show Q.logicalDistance left' right' = 0
      rw [Q.logicalDistance_symm]
      exact le_antisymm this nonneg
  · intro left right zero atom
    have bound := Q.abs_eval_sub_le_logicalDistance (.atom atom) left right
    rw [zero, eval_atom, eval_atom] at bound
    exact sub_eq_zero.mp (abs_nonpos_iff.mp bound)

/-- **The zero kernel is graded bisimilarity**, under finite branching and a
positive discount. -/
theorem logicalDistance_eq_zero_iff (finite : Q.dynamics.ImageFiniteModulo)
    (positive : 0 < Q.discount) (left right : S.Term) :
    Q.logicalDistance left right = 0 ↔ Q.GradedBisimilar left right :=
  ⟨fun zero => ⟨_, Q.isGradedBisimulation_logicalDistance_eq_zero finite positive, zero⟩,
    Q.logicalDistance_eq_zero_of_gradedBisimilar⟩

/-! ## The distinction-calculus observer -/

open Mettapedia.Cybernetics.DistinctionCalculus in
/-- **The behavioural observer**: similarity `1 − d`, a real tolerance. -/
noncomputable def toTolerance : Tolerance S.Term ℝ where
  similarity left right := 1 - Q.logicalDistance left right
  nonnegative left right := by linarith [Q.logicalDistance_le_one left right]
  bounded left right := by linarith [Q.logicalDistance_nonneg left right]
  reflexive term := by simp
  symmetric left right := by rw [Q.logicalDistance_symm]

open Mettapedia.Cybernetics.DistinctionCalculus in
theorem toTolerance_distance (left right : S.Term) :
    Q.toTolerance.distance left right = Q.logicalDistance left right := by
  simp [Tolerance.distance, toTolerance]

open Mettapedia.Cybernetics.DistinctionCalculus in
/-- The behavioural observer satisfies the metric law. -/
theorem toTolerance_metric : Q.toTolerance.Metric := by
  intro first second third
  rw [Q.toTolerance_distance, Q.toTolerance_distance, Q.toTolerance_distance]
  exact Q.logicalDistance_triangle first second third

open Mettapedia.Cybernetics.DistinctionCalculus in
/-- Its indistinguishable pairs are the graded bisimilar ones. -/
theorem toTolerance_indistinguishable_iff (finite : Q.dynamics.ImageFiniteModulo)
    (positive : 0 < Q.discount) (left right : S.Term) :
    Q.toTolerance.Indistinguishable left right ↔ Q.GradedBisimilar left right := by
  rw [Tolerance.Indistinguishable, Q.toTolerance_distance]
  exact Q.logicalDistance_eq_zero_iff finite positive left right

end GradedSystem

/-! ## Crisp observations -/

namespace GradedObservations

variable {S : GSLT.{uS}}

open Classical in
/-- The crisp observations of a system, read as indicators. -/
noncomputable def ofSystem (M : System.{uAtom, uLabel} S) : GradedObservations.{uS, uAtom} S where
  Atom := M.Atom
  value atom term := if M.observes atom term then 1 else 0
  value_nonneg atom term := by split_ifs <;> norm_num
  value_le_one atom term := by split_ifs <;> norm_num
  value_resp atom _ _ equivalent := by
    simp only [M.observes_resp atom equivalent]

theorem ofSystem_value_eq_iff (M : System.{uAtom, uLabel} S) (atom : M.Atom)
    (left right : S.Term) :
    (ofSystem M).value atom left = (ofSystem M).value atom right ↔
      (M.observes atom left ↔ M.observes atom right) := by
  classical
  simp only [ofSystem]
  by_cases leftHolds : M.observes atom left <;> by_cases rightHolds : M.observes atom right <;>
    simp [leftHolds, rightHolds]

end GradedObservations

/-- The graded system of a crisp system: its own steps and its atoms as
indicators. -/
noncomputable def GradedSystem.ofSystem {S : GSLT.{uS}} (M : System.{uAtom, uLabel} S)
    (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1) :
    GradedSystem.{uS, uAtom, uLabel, uAtom} S where
  dynamics := M
  observations := GradedObservations.ofSystem M
  discount := discount
  discount_nonneg := discount_nonneg
  discount_le_one := discount_le_one

namespace GradedSystem

variable {S : GSLT.{uS}} (M : System.{uAtom, uLabel} S) {discount : ℝ}
  (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1)

/-- For crisp observations, graded bisimilarity is the system's bisimilarity. -/
theorem gradedBisimilar_ofSystem_iff (left right : S.Term) :
    (GradedSystem.ofSystem M discount discount_nonneg discount_le_one).GradedBisimilar left right ↔
      M.Bisimilar left right := by
  constructor
  · rintro ⟨relation, ⟨forward, backward, values⟩, related⟩
    exact ⟨relation, ⟨forward, backward, fun _ _ related' atom =>
      (GradedObservations.ofSystem_value_eq_iff M atom _ _).mp (values related' atom)⟩, related⟩
  · rintro ⟨relation, ⟨forward, backward, atoms⟩, related⟩
    exact ⟨relation, ⟨forward, backward, fun _ _ related' atom =>
      (GradedObservations.ofSystem_value_eq_iff M atom _ _).mpr (atoms related' atom)⟩, related⟩

/-- **For crisp observations the zero kernel is bisimilarity**, under finite
branching and a positive discount. -/
theorem logicalDistance_ofSystem_eq_zero_iff (finite : M.ImageFiniteModulo)
    (positive : 0 < discount) (left right : S.Term) :
    (GradedSystem.ofSystem M discount discount_nonneg discount_le_one).logicalDistance left right = 0 ↔
      M.Bisimilar left right := by
  rw [(GradedSystem.ofSystem M discount discount_nonneg discount_le_one).logicalDistance_eq_zero_iff
    finite positive]
  exact gradedBisimilar_ofSystem_iff M discount_nonneg discount_le_one left right

end GradedSystem

end Mettapedia.GSLT.Distinction
