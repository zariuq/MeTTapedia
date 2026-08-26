import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finite.Sigma
import Mathlib.SetTheory.Cardinal.Finite
import Mettapedia.Cybernetics.HierarchicalComplexity.Basic

/-!
# The finite Commons--Pekker hierarchy as a specialization

The ambient action tree and ordinal rank are defined in `Basic`.  Here finite
branching is a property of that same object, not a second action foundation.
Every finitely branching action has rank below `omega`, which yields its
natural-number order.  The chain maximum and coordination successor laws then
recover HC1--HC3 for Commons-admissible actions.

Reference:

- M. L. Commons and A. Pekker, *Presenting the Formal Theory of Hierarchical
  Complexity* (2008).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity

universe uOccurrence uOutcome

namespace Action

/-- Every immediate occurrence family is finite, recursively. -/
def FinitelyBranching {Outcome : Type uOutcome} :
    Action.{uOccurrence, uOutcome} Outcome → Prop :=
  Action.rec True (fun Occurrence _ _ _ childFinite =>
    _root_.Finite Occurrence ∧ ∀ occurrence, childFinite occurrence)

@[simp] theorem finitelyBranching_simple {Outcome : Type uOutcome} :
    FinitelyBranching
      (Action.simple : Action.{uOccurrence, uOutcome} Outcome) := trivial

@[simp] theorem finitelyBranching_compound
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Action.{uOccurrence, uOutcome} Outcome)
    (organization : Organization Occurrence Outcome) :
    FinitelyBranching
      (.compound Occurrence hasAtLeastTwo child organization) ↔
      _root_.Finite Occurrence ∧ ∀ occurrence, FinitelyBranching (child occurrence) :=
  Iff.rfl

/-- Finite branching forces the ambient ordinal rank below `omega`. -/
theorem rank_lt_omega0_of_finitelyBranching
    {Outcome : Type uOutcome}
    (action : Action.{uOccurrence, uOutcome} Outcome)
    (finite : FinitelyBranching action) :
    rank action < Ordinal.omega0 := by
  induction action with
  | simple => exact Ordinal.natCast_lt_omega0 0
  | compound Occurrence hasAtLeastTwo child organization inductionHypothesis =>
      rw [finitelyBranching_compound] at finite
      letI : _root_.Finite Occurrence := finite.1
      letI : Nonempty Occurrence := hasAtLeastTwo.nonempty
      have childFinite : ∀ occurrence, FinitelyBranching (child occurrence) := finite.2
      have childBelow : ∀ occurrence,
          rank (child occurrence) < Ordinal.omega0 :=
        fun occurrence => inductionHypothesis occurrence (childFinite occurrence)
      obtain ⟨greatest, greatestRank⟩ :=
        exists_eq_ciSup_of_finite
          (f := fun occurrence => rank (child occurrence))
      cases organization with
      | chain semantics invariant =>
          rw [rank_chain, ← greatestRank]
          exact childBelow greatest
      | coordination semantics sensitive =>
          rw [rank_coordination, ← greatestRank]
          obtain ⟨n, rankEqual⟩ := Ordinal.lt_omega0.mp (childBelow greatest)
          rw [rankEqual, Order.succ_eq_add_one, ← Nat.cast_add_one]
          exact Ordinal.natCast_lt_omega0 (n + 1)

/-- Finite branching makes the informative simple-leaf family finite. -/
theorem finite_simpleLeaves
    {Outcome : Type uOutcome}
    (action : Action.{uOccurrence, uOutcome} Outcome)
    (finite : FinitelyBranching action) :
    _root_.Finite (SimpleLeaves action) := by
  induction action with
  | simple =>
      change _root_.Finite PUnit
      infer_instance
  | compound Occurrence hasAtLeastTwo child organization inductionHypothesis =>
      rw [finitelyBranching_compound] at finite
      letI : _root_.Finite Occurrence := finite.1
      letI : ∀ occurrence, _root_.Finite (SimpleLeaves (child occurrence)) :=
        fun occurrence => inductionHypothesis occurrence (finite.2 occurrence)
      change _root_.Finite (Sigma (fun occurrence => SimpleLeaves (child occurrence)))
      infer_instance

/-- Commons and Pekker's `phi n = 2^n` is the lower-bound theorem for finite,
atomic, Commons-admissible action trees: every action of order `n` contains at
least `2^n` simple leaves. -/
theorem pow_two_le_natCard_simpleLeaves_of_rank_eq
    {Outcome : Type uOutcome}
    (action : Action.{uOccurrence, uOutcome} Outcome)
    (finite : FinitelyBranching action)
    (admissible : CommonsAdmissible action)
    (n : Nat) (rankEqual : rank action = (n : Ordinal)) :
    2 ^ n ≤ Nat.card (SimpleLeaves action) := by
  classical
  induction action generalizing n with
  | simple =>
      have nZero : n = 0 := by
        apply Nat.cast_injective (R := Ordinal)
        simpa only [rank_simple, Nat.cast_zero] using rankEqual.symm
      subst nZero
      simp [SimpleLeaves]
  | compound Occurrence hasAtLeastTwo child organization inductionHypothesis =>
      rw [finitelyBranching_compound] at finite
      letI : _root_.Finite Occurrence := finite.1
      letI : Nonempty Occurrence := hasAtLeastTwo.nonempty
      letI : Fintype Occurrence := Fintype.ofFinite Occurrence
      have childFinite : ∀ occurrence, FinitelyBranching (child occurrence) := finite.2
      letI : ∀ occurrence, _root_.Finite (SimpleLeaves (child occurrence)) :=
        fun occurrence => finite_simpleLeaves (child occurrence) (childFinite occurrence)
      change 2 ^ n ≤ Nat.card (Sigma (fun occurrence => SimpleLeaves (child occurrence)))
      rw [Nat.card_sigma]
      cases organization with
      | chain semantics invariant =>
          obtain ⟨greatest, greatestRank⟩ :=
            exists_eq_ciSup_of_finite
              (f := fun occurrence => rank (child occurrence))
          have childRankEqual : rank (child greatest) = (n : Ordinal) := by
            exact greatestRank.trans
              ((rank_chain hasAtLeastTwo child semantics invariant).symm.trans rankEqual)
          exact (inductionHypothesis greatest (childFinite greatest)
            (admissible greatest) n childRankEqual).trans
              (Finset.single_le_sum
                (s := Finset.univ)
                (f := fun occurrence =>
                  Nat.card (SimpleLeaves (child occurrence)))
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ greatest))
      | coordination semantics sensitive =>
          rcases admissible with ⟨childAdmissible, equalRank⟩
          have compoundHasAtLeastTwo := hasAtLeastTwo
          obtain ⟨first, second, different⟩ := hasAtLeastTwo
          obtain ⟨m, firstRank⟩ := Ordinal.lt_omega0.mp
            (rank_lt_omega0_of_finitelyBranching
              (child first) (childFinite first))
          have childRank (occurrence : Occurrence) :
              rank (child occurrence) = (m : Ordinal) :=
            (equalRank occurrence first).trans firstRank
          have childSupEqual :
              (⨆ occurrence, rank (child occurrence)) = rank (child first) := by
            apply le_antisymm
            · exact Ordinal.iSup_le fun occurrence => (equalRank occurrence first).le
            · exact Ordinal.le_iSup (fun occurrence => rank (child occurrence)) first
          have rootRank : Order.succ (rank (child first)) = (n : Ordinal) := by
            calc
              Order.succ (rank (child first)) =
                  Order.succ (⨆ occurrence, rank (child occurrence)) :=
                congrArg Order.succ childSupEqual.symm
              _ = rank (.compound Occurrence compoundHasAtLeastTwo child
                    (.coordination semantics sensitive)) :=
                (rank_coordination compoundHasAtLeastTwo child semantics sensitive).symm
              _ = (n : Ordinal) := rankEqual
          have nEqual : n = m + 1 := by
            apply Nat.cast_injective (R := Ordinal)
            calc
              (n : Ordinal) = Order.succ (rank (child first)) := rootRank.symm
              _ = Order.succ (m : Ordinal) := congrArg Order.succ firstRank
              _ = (m : Ordinal) + 1 := Order.succ_eq_add_one _
              _ = ((m + 1 : Nat) : Ordinal) := (Nat.cast_add_one m).symm
          have firstBound :
              2 ^ m ≤ Nat.card (SimpleLeaves (child first)) :=
            inductionHypothesis first (childFinite first)
              (childAdmissible first) m (childRank first)
          have secondBound :
              2 ^ m ≤ Nat.card (SimpleLeaves (child second)) :=
            inductionHypothesis second (childFinite second)
              (childAdmissible second) m (childRank second)
          have pairBound :
              2 ^ m + 2 ^ m ≤
                ∑ occurrence, Nat.card (SimpleLeaves (child occurrence)) := by
            calc
              2 ^ m + 2 ^ m ≤
                  Nat.card (SimpleLeaves (child first)) +
                    Nat.card (SimpleLeaves (child second)) :=
                Nat.add_le_add firstBound secondBound
              _ = ∑ occurrence ∈ ({first, second} : Finset Occurrence),
                    Nat.card (SimpleLeaves (child occurrence)) :=
                (Finset.sum_pair
                  (f := fun occurrence =>
                    Nat.card (SimpleLeaves (child occurrence))) different).symm
              _ ≤ ∑ occurrence, Nat.card (SimpleLeaves (child occurrence)) :=
                Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          subst nEqual
          simpa only [pow_succ, Nat.mul_two] using pairBound

/-- Every positive finite Commons order contains a subaction at its immediate
predecessor order.  This is the structural content needed for C2; it uses
finite attainment and HC2 homogeneity. -/
theorem exists_subaction_rank_pred
    {Outcome : Type uOutcome}
    (action : Action.{uOccurrence, uOutcome} Outcome)
    (finite : FinitelyBranching action)
    (admissible : CommonsAdmissible action)
    (n : Nat) (rankEqual : rank action = ((n + 1 : Nat) : Ordinal)) :
    ∃ subaction,
      IsSubaction subaction action ∧
      FinitelyBranching subaction ∧
      CommonsAdmissible subaction ∧
      rank subaction = (n : Ordinal) := by
  induction action generalizing n with
  | simple =>
      have castImpossible : (0 : Ordinal) = ((n + 1 : Nat) : Ordinal) := by
        simpa only [rank_simple] using rankEqual
      have natImpossible : 0 = n + 1 :=
        Nat.cast_injective castImpossible
      exact (Nat.zero_ne_add_one n natImpossible).elim
  | compound Occurrence hasAtLeastTwo child organization inductionHypothesis =>
      rw [finitelyBranching_compound] at finite
      letI : _root_.Finite Occurrence := finite.1
      letI : Nonempty Occurrence := hasAtLeastTwo.nonempty
      have childFinite : ∀ occurrence, FinitelyBranching (child occurrence) := finite.2
      cases organization with
      | chain semantics invariant =>
          obtain ⟨greatest, greatestRank⟩ :=
            exists_eq_ciSup_of_finite
              (f := fun occurrence => rank (child occurrence))
          have childRankEqual :
              rank (child greatest) = ((n + 1 : Nat) : Ordinal) :=
            greatestRank.trans
              ((rank_chain hasAtLeastTwo child semantics invariant).symm.trans rankEqual)
          obtain ⟨subaction, contained, subFinite, subAdmissible, subRank⟩ :=
            inductionHypothesis greatest (childFinite greatest)
              (admissible greatest) n childRankEqual
          exact ⟨subaction,
            IsSubaction.trans contained
              (IsSubaction.immediate hasAtLeastTwo child
                (.chain semantics invariant) greatest),
            subFinite, subAdmissible, subRank⟩
      | coordination semantics sensitive =>
          rcases admissible with ⟨childAdmissible, equalRank⟩
          have compoundHasAtLeastTwo := hasAtLeastTwo
          obtain ⟨first, _, _⟩ := hasAtLeastTwo
          have childSupEqual :
              (⨆ occurrence, rank (child occurrence)) = rank (child first) := by
            apply le_antisymm
            · exact Ordinal.iSup_le fun occurrence => (equalRank occurrence first).le
            · exact Ordinal.le_iSup (fun occurrence => rank (child occurrence)) first
          have successorEqual :
              Order.succ (rank (child first)) =
                Order.succ (n : Ordinal) := by
            calc
              Order.succ (rank (child first)) =
                  Order.succ (⨆ occurrence, rank (child occurrence)) :=
                congrArg Order.succ childSupEqual.symm
              _ = rank (.compound Occurrence compoundHasAtLeastTwo child
                    (.coordination semantics sensitive)) :=
                (rank_coordination compoundHasAtLeastTwo child semantics sensitive).symm
              _ = ((n + 1 : Nat) : Ordinal) := rankEqual
              _ = (n : Ordinal) + 1 := Nat.cast_add_one n
              _ = Order.succ (n : Ordinal) := (Order.succ_eq_add_one _).symm
          exact ⟨child first,
            IsSubaction.immediate compoundHasAtLeastTwo child
              (.coordination semantics sensitive) first,
            childFinite first, childAdmissible first,
            Order.succ_injective successorEqual⟩

end Action

/-! ## The source-faithful finite view -/

namespace Finite

/-- A finite Commons action is one ambient action with finite branching and
the recursive equal-order condition for coordinations. -/
structure Action (Outcome : Type uOutcome) where
  toAmbient :
    HierarchicalComplexity.Action.{uOccurrence, uOutcome} Outcome
  finitelyBranching : toAmbient.FinitelyBranching
  commonsAdmissible : toAmbient.CommonsAdmissible

namespace Action

/-- The natural-number order whose ordinal cast is the ambient rank. -/
noncomputable def order {Outcome : Type uOutcome}
    (action : Finite.Action.{uOccurrence, uOutcome} Outcome) : Nat :=
  Classical.choose (Ordinal.lt_omega0.mp
    (HierarchicalComplexity.Action.rank_lt_omega0_of_finitelyBranching
      action.toAmbient action.finitelyBranching))

/-- Finite order is not a second measure: its ordinal cast is exactly the
ambient rank. -/
theorem rank_eq_natCast_order {Outcome : Type uOutcome}
    (action : Finite.Action.{uOccurrence, uOutcome} Outcome) :
    action.toAmbient.rank = (action.order : Ordinal) :=
  Classical.choose_spec (Ordinal.lt_omega0.mp
    (HierarchicalComplexity.Action.rank_lt_omega0_of_finitelyBranching
      action.toAmbient action.finitelyBranching))

/-- HC1: the simple action has order zero. -/
def simple (Outcome : Type uOutcome) : Finite.Action.{uOccurrence, uOutcome} Outcome where
  toAmbient := .simple
  finitelyBranching := trivial
  commonsAdmissible := trivial

@[simp] theorem order_simple (Outcome : Type uOutcome) :
    (simple Outcome : Finite.Action.{uOccurrence, uOutcome} Outcome).order = 0 := by
  apply Nat.cast_injective (R := Ordinal)
  rw [← rank_eq_natCast_order]
  rfl

/-- Form a finite chain from finite Commons children. -/
def chain
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    [finiteOccurrence : _root_.Finite Occurrence]
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Finite.Action.{uOccurrence, uOutcome} Outcome)
    (semantics : ScheduleSemantics Occurrence Outcome)
    (invariant : IsChain semantics) :
    Finite.Action.{uOccurrence, uOutcome} Outcome where
  toAmbient := .compound Occurrence hasAtLeastTwo
    (fun occurrence => (child occurrence).toAmbient)
    (.chain semantics invariant)
  finitelyBranching :=
    ⟨finiteOccurrence, fun occurrence => (child occurrence).finitelyBranching⟩
  commonsAdmissible :=
    fun occurrence => (child occurrence).commonsAdmissible

/-- Form a finite coordination.  Equal child order is the explicit HC2
premise rather than an automatically true constructor field. -/
def coordination
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    [finiteOccurrence : _root_.Finite Occurrence]
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Finite.Action.{uOccurrence, uOutcome} Outcome)
    (semantics : ScheduleSemantics Occurrence Outcome)
    (sensitive : IsCoordination semantics)
    (equalOrder : ∀ first second,
      (child first).order = (child second).order) :
    Finite.Action.{uOccurrence, uOutcome} Outcome where
  toAmbient := .compound Occurrence hasAtLeastTwo
    (fun occurrence => (child occurrence).toAmbient)
    (.coordination semantics sensitive)
  finitelyBranching :=
    ⟨finiteOccurrence, fun occurrence => (child occurrence).finitelyBranching⟩
  commonsAdmissible := by
    refine ⟨fun occurrence => (child occurrence).commonsAdmissible, ?_⟩
    intro first second
    rw [(child first).rank_eq_natCast_order,
      (child second).rank_eq_natCast_order, equalOrder first second]

/-- HC3 for chains: the resulting order is attained by a child and bounds
every child order.  This is the `max` law without choosing a presentation of
the finite occurrence family as `Fin n`. -/
theorem chain_order_is_child_maximum
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    [finiteOccurrence : _root_.Finite Occurrence]
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Finite.Action.{uOccurrence, uOutcome} Outcome)
    (semantics : ScheduleSemantics Occurrence Outcome)
    (invariant : IsChain semantics) :
    (∃ occurrence,
      (chain hasAtLeastTwo child semantics invariant).order =
        (child occurrence).order) ∧
    ∀ occurrence,
      (child occurrence).order ≤
        (chain hasAtLeastTwo child semantics invariant).order := by
  letI : Nonempty Occurrence := hasAtLeastTwo.nonempty
  obtain ⟨greatest, greatestRank⟩ :=
    exists_eq_ciSup_of_finite
      (f := fun occurrence => (child occurrence).toAmbient.rank)
  constructor
  · refine ⟨greatest, ?_⟩
    apply Nat.cast_injective (R := Ordinal)
    rw [← rank_eq_natCast_order, ← (child greatest).rank_eq_natCast_order]
    exact (HierarchicalComplexity.Action.rank_chain hasAtLeastTwo
      (fun occurrence => (child occurrence).toAmbient)
      semantics invariant).trans greatestRank.symm
  · intro occurrence
    apply (Nat.cast_le (α := Ordinal)).mp
    rw [← (child occurrence).rank_eq_natCast_order,
      ← (chain hasAtLeastTwo child semantics invariant).rank_eq_natCast_order]
    exact HierarchicalComplexity.Action.child_rank_le_chain
      hasAtLeastTwo (fun index => (child index).toAmbient)
      semantics invariant occurrence

/-- HC3 for coordinations: homogeneous children of order `n` produce an
action of order `n + 1`. -/
theorem coordination_order_eq_child_add_one
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    [finiteOccurrence : _root_.Finite Occurrence]
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Finite.Action.{uOccurrence, uOutcome} Outcome)
    (semantics : ScheduleSemantics Occurrence Outcome)
    (sensitive : IsCoordination semantics)
    (equalOrder : ∀ first second,
      (child first).order = (child second).order)
    (occurrence : Occurrence) :
    (coordination hasAtLeastTwo child semantics sensitive equalOrder).order =
      (child occurrence).order + 1 := by
  letI : Nonempty Occurrence := hasAtLeastTwo.nonempty
  apply Nat.cast_injective (R := Ordinal)
  rw [← (coordination hasAtLeastTwo child semantics sensitive
      equalOrder).rank_eq_natCast_order, Nat.cast_add_one,
    ← (child occurrence).rank_eq_natCast_order]
  change Order.succ (⨆ index, (child index).toAmbient.rank) =
    (child occurrence).toAmbient.rank + 1
  rw [Order.succ_eq_add_one]
  congr 1
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro index
    rw [(child index).rank_eq_natCast_order,
      (child occurrence).rank_eq_natCast_order,
      equalOrder index occurrence]
  · exact Ordinal.le_iSup
      (fun index => (child index).toAmbient.rank) occurrence

/-- Number of simple leaves in the finite projection. -/
noncomputable def simpleLeafCount {Outcome : Type uOutcome}
    (action : Finite.Action.{uOccurrence, uOutcome} Outcome) : Nat :=
  Nat.card (HierarchicalComplexity.Action.SimpleLeaves action.toAmbient)

/-- Every finite Commons action meets the exponential simple-action lower
bound at its own order. -/
theorem pow_two_order_le_simpleLeafCount {Outcome : Type uOutcome}
    (action : Finite.Action.{uOccurrence, uOutcome} Outcome) :
    2 ^ action.order ≤ action.simpleLeafCount := by
  exact HierarchicalComplexity.Action.pow_two_le_natCard_simpleLeaves_of_rank_eq
    action.toAmbient action.finitelyBranching action.commonsAdmissible
      action.order action.rank_eq_natCast_order

/-- C3: finite orders are trichotomous. -/
theorem order_trichotomy {Outcome : Type uOutcome}
    (first second : Finite.Action.{uOccurrence, uOutcome} Outcome) :
    first.order < second.order ∨ first.order = second.order ∨
      second.order < first.order :=
  lt_trichotomy first.order second.order

/-- C4: strict comparison of finite orders is transitive. -/
theorem order_lt_trans {Outcome : Type uOutcome}
    {first second third : Finite.Action.{uOccurrence, uOutcome} Outcome}
    (firstSecond : first.order < second.order)
    (secondThird : second.order < third.order) :
    first.order < third.order :=
  firstSecond.trans secondThird

end Action

/-! ## C2: no gaps in the realized finite spectrum -/

/-- An order is realized when some finite Commons action has that order. -/
def RealizesOrder (Outcome : Type uOutcome) (n : Nat) : Prop :=
  ∃ action : Finite.Action.{uOccurrence, uOutcome} Outcome, action.order = n

/-- Strong form of C2: realization of order `n+1` already exposes a realized
subaction of order `n`; no separate lower-order premise is required. -/
theorem realizesOrder_pred_of_succ
    {Outcome : Type uOutcome} {n : Nat}
    (higher : RealizesOrder.{uOccurrence, uOutcome} Outcome (n + 1)) :
    RealizesOrder.{uOccurrence, uOutcome} Outcome n := by
  obtain ⟨action, actionOrder⟩ := higher
  have actionRank : action.toAmbient.rank = ((n + 1 : Nat) : Ordinal) := by
    rw [action.rank_eq_natCast_order, actionOrder]
  obtain ⟨subaction, _, subFinite, subAdmissible, subRank⟩ :=
    HierarchicalComplexity.Action.exists_subaction_rank_pred
      action.toAmbient action.finitelyBranching action.commonsAdmissible n actionRank
  let finiteSubaction : Finite.Action.{uOccurrence, uOutcome} Outcome :=
    ⟨subaction, subFinite, subAdmissible⟩
  refine ⟨finiteSubaction, ?_⟩
  apply Nat.cast_injective (R := Ordinal)
  rw [← finiteSubaction.rank_eq_natCast_order]
  exact subRank

/-- Commons and Pekker's stated C2 form. -/
theorem no_gaps
    {Outcome : Type uOutcome} {n : Nat}
    (_lower : RealizesOrder.{uOccurrence, uOutcome} Outcome n)
    (higher : RealizesOrder.{uOccurrence, uOutcome} Outcome (n + 2)) :
    RealizesOrder.{uOccurrence, uOutcome} Outcome (n + 1) := by
  have reshaped : n + 2 = (n + 1) + 1 := by omega
  rw [reshaped] at higher
  exact realizesOrder_pred_of_succ higher


/-! ## The exact `phi n = 2^n` minimum -/

namespace Phi

open HierarchicalComplexity.LimitCanary

@[simp] theorem finitelyBranching_finiteTower (n : Nat) :
    HierarchicalComplexity.Action.FinitelyBranching (finiteTower n) := by
  induction n with
  | zero => trivial
  | succ n inductionHypothesis =>
      exact ⟨inferInstance, fun _ => inductionHypothesis⟩

/-- The binary witness, regarded through the finite Commons specialization. -/
def binaryTower (n : Nat) : Finite.Action.{0, 0} (Fin 2) where
  toAmbient := finiteTower n
  finitelyBranching := finitelyBranching_finiteTower n
  commonsAdmissible := commonsAdmissible_finiteTower n

@[simp] theorem order_binaryTower (n : Nat) :
    (binaryTower n).order = n := by
  apply Nat.cast_injective (R := Ordinal)
  rw [← (binaryTower n).rank_eq_natCast_order]
  exact rank_finiteTower n

@[simp] theorem natCard_simpleLeaves_finiteTower (n : Nat) :
    Nat.card (HierarchicalComplexity.Action.SimpleLeaves (finiteTower n)) =
      2 ^ n := by
  induction n with
  | zero => simp [finiteTower, HierarchicalComplexity.Action.SimpleLeaves]
  | succ n inductionHypothesis =>
      letI : _root_.Finite
          (HierarchicalComplexity.Action.SimpleLeaves (finiteTower n)) :=
        HierarchicalComplexity.Action.finite_simpleLeaves
          (finiteTower n) (finitelyBranching_finiteTower n)
      rw [finiteTower]
      change Nat.card
        (Sigma (fun _ : Fin 2 =>
          HierarchicalComplexity.Action.SimpleLeaves (finiteTower n))) =
            2 ^ (n + 1)
      rw [Nat.card_sigma]
      simp [inductionHypothesis, pow_succ, Nat.mul_two, two_mul]

@[simp] theorem simpleLeafCount_binaryTower (n : Nat) :
    (binaryTower n).simpleLeafCount = 2 ^ n :=
  natCard_simpleLeaves_finiteTower n

/-- `count` is a realized minimum simple-leaf count at order `n`. -/
def IsMinimumSimpleLeafCount (n count : Nat) : Prop :=
  (∃ action : Finite.Action.{0, 0} (Fin 2),
      action.order = n ∧ action.simpleLeafCount = count) ∧
  ∀ action : Finite.Action.{0, 0} (Fin 2),
    action.order = n → count ≤ action.simpleLeafCount

/-- Commons and Pekker's `phi_n = 2^n`: the exponential lower bound is
attained by the binary coordination tower. -/
theorem phi_eq_pow_two (n : Nat) :
    IsMinimumSimpleLeafCount n (2 ^ n) := by
  constructor
  · exact ⟨binaryTower n, order_binaryTower n,
      simpleLeafCount_binaryTower n⟩
  · intro action orderEqual
    simpa only [orderEqual] using action.pow_two_order_le_simpleLeafCount

end Phi

end Finite

end Mettapedia.Cybernetics.HierarchicalComplexity

#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Action.rank_lt_omega0_of_finitelyBranching
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Action.pow_two_le_natCard_simpleLeaves_of_rank_eq
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Action.exists_subaction_rank_pred
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Finite.Action.chain_order_is_child_maximum
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Finite.Action.coordination_order_eq_child_add_one
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Finite.no_gaps
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Finite.Phi.phi_eq_pow_two
