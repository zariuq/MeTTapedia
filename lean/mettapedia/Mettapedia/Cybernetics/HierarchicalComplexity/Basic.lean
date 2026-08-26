import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Ordinal.Family

/-!
# Hierarchical complexity from schedule sensitivity

This file isolates the reusable mathematical core of hierarchical complexity.
An occurrence family may be infinite.  Its schedules are permutations of the
occurrence type, and an organization is either invariant under every schedule
or carries a witness that two schedules have different outcomes.

The ordinal rank is an infinitary extension developed here: invariant
organization takes the supremum of child ranks, while order-sensitive
coordination takes its successor.  Michael Lamport Commons and Alexander
Pekker's published natural-number model is recovered separately as the finite
specialization; the transfinite extension must not be attributed to them.

References:

- M. L. Commons and A. Pekker, *Presenting the Formal Theory of Hierarchical
  Complexity* (2008), for the permutation test and axioms A1--A3, HC1--HC3.
- M. L. Commons, P. M. Trudeau, S. A. Stein, F. A. Richards, and S. R. Krause,
  *Hierarchical Complexity of Tasks Shows the Existence of Developmental
  Stages* (1998), for the task-relative interpretation of hierarchical order.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity

universe uOccurrence uOutcome

/-- Schedules of an occurrence family are permutations of its occurrences. -/
abbrev Schedule (Occurrence : Type uOccurrence) := Equiv.Perm Occurrence

/-- A compound action has at least two distinct occurrences. -/
def HasAtLeastTwo (Occurrence : Type uOccurrence) : Prop :=
  ∃ first second : Occurrence, first ≠ second

namespace HasAtLeastTwo

/-- Two distinct occurrences in particular supply one occurrence. -/
theorem nonempty {Occurrence : Type uOccurrence}
    (hasAtLeastTwo : HasAtLeastTwo Occurrence) : Nonempty Occurrence := by
  obtain ⟨first, _, _⟩ := hasAtLeastTwo
  exact ⟨first⟩

end HasAtLeastTwo

/-- A schedule semantics is a readout for every permutation of the occurrence
family.  It abstracts from any particular evaluator while retaining exactly
the observation needed by the Commons--Pekker permutation test. -/
abbrev ScheduleSemantics
    (Occurrence : Type uOccurrence) (Outcome : Type uOutcome) :=
  Schedule Occurrence → Outcome

/-- A chain is insensitive to the order in which its occurrences are
scheduled. -/
def IsChain {Occurrence : Type uOccurrence} {Outcome : Type uOutcome}
    (semantics : ScheduleSemantics Occurrence Outcome) : Prop :=
  ∀ first second, semantics first = semantics second

/-- A coordination carries positive evidence of order sensitivity. -/
def IsCoordination {Occurrence : Type uOccurrence} {Outcome : Type uOutcome}
    (semantics : ScheduleSemantics Occurrence Outcome) : Prop :=
  ∃ first second, semantics first ≠ semantics second

/-- Chain and coordination are disjoint. -/
theorem IsChain.not_coordination
    {Occurrence : Type uOccurrence} {Outcome : Type uOutcome}
    {semantics : ScheduleSemantics Occurrence Outcome}
    (chain : IsChain semantics) : ¬ IsCoordination semantics := by
  rintro ⟨first, second, different⟩
  exact different (chain first second)

/-- Classically, every schedule semantics is either invariant or has a
concrete order-sensitivity witness. -/
theorem chain_or_coordination
    {Occurrence : Type uOccurrence} {Outcome : Type uOutcome}
    (semantics : ScheduleSemantics Occurrence Outcome) :
    IsChain semantics ∨ IsCoordination semantics := by
  classical
  by_cases chain : IsChain semantics
  · exact Or.inl chain
  · right
    by_contra noCoordination
    apply chain
    intro first second
    by_contra different
    exact noCoordination ⟨first, second, different⟩

/-- An organization stores which side of the permutation test it inhabits.
The evidence is data, so later proofs never infer coordination from a label. -/
inductive Organization
    (Occurrence : Type uOccurrence) (Outcome : Type uOutcome) :
    Type (max uOccurrence uOutcome) where
  | chain (semantics : ScheduleSemantics Occurrence Outcome)
      (invariant : IsChain semantics)
  | coordination (semantics : ScheduleSemantics Occurrence Outcome)
      (sensitive : IsCoordination semantics)

namespace Organization

/-- Forget the classification while retaining the schedule semantics. -/
def semantics {Occurrence : Type uOccurrence} {Outcome : Type uOutcome} :
    Organization Occurrence Outcome → ScheduleSemantics Occurrence Outcome
  | .chain semantics _ => semantics
  | .coordination semantics _ => semantics

/-- Whether this organization is order-sensitive. -/
def isCoordination {Occurrence : Type uOccurrence} {Outcome : Type uOutcome} :
    Organization Occurrence Outcome → Bool
  | .chain _ _ => false
  | .coordination _ _ => true

@[simp] theorem semantics_chain
    {Occurrence : Type uOccurrence} {Outcome : Type uOutcome}
    (semantics : ScheduleSemantics Occurrence Outcome)
    (invariant : IsChain semantics) :
    Organization.semantics (.chain semantics invariant) = semantics := rfl

@[simp] theorem semantics_coordination
    {Occurrence : Type uOccurrence} {Outcome : Type uOutcome}
    (semantics : ScheduleSemantics Occurrence Outcome)
    (sensitive : IsCoordination semantics) :
    Organization.semantics (.coordination semantics sensitive) = semantics := rfl

end Organization

/-! ## Infinitely branching action trees -/

/-- A well-founded action tree whose immediate occurrence family may be
infinite.  `Outcome` records only the observation used to distinguish chains
from coordinations; downstream interpretations may retain richer semantics. -/
inductive Action (Outcome : Type uOutcome) : Type (max (uOccurrence + 1) uOutcome) where
  | simple : Action Outcome
  | compound (Occurrence : Type uOccurrence)
      (hasAtLeastTwo : HasAtLeastTwo Occurrence)
      (child : Occurrence → Action Outcome)
      (organization : Organization Occurrence Outcome) : Action Outcome

namespace Action

/-- The ambient ordinal rank.  A chain takes the supremum of its children;
a coordination creates the successor of that supremum. -/
noncomputable def rank {Outcome : Type uOutcome} :
    Action.{uOccurrence, uOutcome} Outcome → Ordinal.{uOccurrence} :=
  Action.rec 0 (fun _ _ _ organization childRank =>
    match organization with
    | .chain _ _ => ⨆ occurrence, childRank occurrence
    | .coordination _ _ =>
        Order.succ (⨆ occurrence, childRank occurrence))

/-- The supremum of the ranks of an immediate child family. -/
noncomputable def childSup
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    (child : Occurrence → Action.{uOccurrence, uOutcome} Outcome) :
    Ordinal.{uOccurrence} :=
  ⨆ occurrence, rank (child occurrence)

/-- The informative family of simple leaves.  Cardinality is deliberately a
downstream readout: the leaf type itself remains meaningful for infinite
branching. -/
def SimpleLeaves {Outcome : Type uOutcome} :
    Action.{uOccurrence, uOutcome} Outcome → Type uOccurrence :=
  Action.rec PUnit (fun _ _ _ _ childLeaves => Sigma childLeaves)

@[simp] theorem simpleLeaves_simple {Outcome : Type uOutcome} :
    SimpleLeaves
      (Action.simple : Action.{uOccurrence, uOutcome} Outcome) = PUnit := rfl

@[simp] theorem simpleLeaves_compound
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Action.{uOccurrence, uOutcome} Outcome)
    (organization : Organization Occurrence Outcome) :
    SimpleLeaves (.compound Occurrence hasAtLeastTwo child organization) =
      Sigma (fun occurrence => SimpleLeaves (child occurrence)) := rfl

/-- Simple-action amount before any finite projection. -/
noncomputable def simpleLeafCardinal {Outcome : Type uOutcome}
    (action : Action.{uOccurrence, uOutcome} Outcome) : Cardinal.{uOccurrence} :=
  Cardinal.mk (SimpleLeaves action)

@[simp] theorem simpleLeafCardinal_simple {Outcome : Type uOutcome} :
    simpleLeafCardinal
      (Action.simple : Action.{uOccurrence, uOutcome} Outcome) = 1 := by
  simp [simpleLeafCardinal]

theorem simpleLeafCardinal_compound
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Action.{uOccurrence, uOutcome} Outcome)
    (organization : Organization Occurrence Outcome) :
    simpleLeafCardinal
      (.compound Occurrence hasAtLeastTwo child organization) =
      Cardinal.sum (fun occurrence => simpleLeafCardinal (child occurrence)) := by
  simpa only [simpleLeafCardinal, simpleLeaves_compound] using
    Cardinal.mk_sigma (fun occurrence => SimpleLeaves (child occurrence))

@[simp] theorem rank_simple {Outcome : Type uOutcome} :
    rank (Action.simple : Action.{uOccurrence, uOutcome} Outcome) = 0 := rfl

@[simp] theorem rank_chain
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Action.{uOccurrence, uOutcome} Outcome)
    (semantics : ScheduleSemantics Occurrence Outcome)
    (invariant : IsChain semantics) :
    rank (.compound Occurrence hasAtLeastTwo child
      (.chain semantics invariant)) =
        ⨆ occurrence, rank (child occurrence) := rfl

@[simp] theorem rank_coordination
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Action.{uOccurrence, uOutcome} Outcome)
    (semantics : ScheduleSemantics Occurrence Outcome)
    (sensitive : IsCoordination semantics) :
    rank (.compound Occurrence hasAtLeastTwo child
      (.coordination semantics sensitive)) =
        Order.succ (⨆ occurrence, rank (child occurrence)) := rfl

/-- Every child rank is bounded by the rank of an invariant compound action. -/
theorem child_rank_le_chain
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Action.{uOccurrence, uOutcome} Outcome)
    (semantics : ScheduleSemantics Occurrence Outcome)
    (invariant : IsChain semantics) (occurrence : Occurrence) :
    rank (child occurrence) ≤
      rank (.compound Occurrence hasAtLeastTwo child
        (.chain semantics invariant)) := by
  rw [rank_chain]
  exact Ordinal.le_iSup (fun index => rank (child index)) occurrence

/-- Coordination strictly raises the rank above every immediate child, even
when the child supremum is not attained. -/
theorem child_rank_lt_coordination
    {Outcome : Type uOutcome} {Occurrence : Type uOccurrence}
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Action.{uOccurrence, uOutcome} Outcome)
    (semantics : ScheduleSemantics Occurrence Outcome)
    (sensitive : IsCoordination semantics) (occurrence : Occurrence) :
    rank (child occurrence) <
      rank (.compound Occurrence hasAtLeastTwo child
        (.coordination semantics sensitive)) := by
  rw [rank_coordination, Order.lt_succ_iff]
  exact Ordinal.le_iSup (fun index => rank (child index)) occurrence

/-- Commons's equal-order condition is retained as an admissibility predicate,
not hidden in the action constructor.  This leaves room for a real HC2
counterexample and for more general order-sensitive systems downstream. -/
def CommonsAdmissible {Outcome : Type uOutcome} :
    Action.{uOccurrence, uOutcome} Outcome → Prop
  | .simple => True
  | .compound _ _ child (.chain _ _) =>
      ∀ occurrence, CommonsAdmissible (child occurrence)
  | .compound _ _ child (.coordination _ _) =>
      (∀ occurrence, CommonsAdmissible (child occurrence)) ∧
      ∀ first second, rank (child first) = rank (child second)

@[simp] theorem commonsAdmissible_simple {Outcome : Type uOutcome} :
    CommonsAdmissible
      (Action.simple : Action.{uOccurrence, uOutcome} Outcome) := trivial

/-- Reflexive-transitive containment in an action tree. -/
inductive IsSubaction {Outcome : Type uOutcome} :
    Action.{uOccurrence, uOutcome} Outcome →
      Action.{uOccurrence, uOutcome} Outcome → Prop where
  | refl (action) : IsSubaction action action
  | immediate
      {Occurrence : Type uOccurrence}
      (hasAtLeastTwo : HasAtLeastTwo Occurrence)
      (child : Occurrence → Action.{uOccurrence, uOutcome} Outcome)
      (organization : Organization Occurrence Outcome)
      (occurrence : Occurrence) :
      IsSubaction (child occurrence)
        (.compound Occurrence hasAtLeastTwo child organization)
  | trans {first second third} :
      IsSubaction first second → IsSubaction second third →
        IsSubaction first third

end Action

/-! ## Limit formation is not successor coordination -/

namespace LimitCanary

/-- Two binary occurrences. -/
theorem binary_hasAtLeastTwo : HasAtLeastTwo (Fin 2) := by
  exact ⟨0, 1, by decide⟩

/-- The schedule outcome records where occurrence zero is sent. -/
def binarySemantics : ScheduleSemantics (Fin 2) (Fin 2) :=
  fun schedule => schedule 0

/-- Swapping the two occurrences changes the binary schedule outcome. -/
theorem binarySensitive : IsCoordination binarySemantics := by
  refine ⟨Equiv.refl (Fin 2), Equiv.swap 0 1, ?_⟩
  simp [binarySemantics]

/-- A canonical action of every finite order. -/
def finiteTower : Nat → Action.{0, 0} (Fin 2)
  | 0 => .simple
  | n + 1 =>
      .compound (Fin 2) binary_hasAtLeastTwo (fun _ => finiteTower n)
        (.coordination binarySemantics binarySensitive)

@[simp] theorem rank_finiteTower (n : Nat) :
    Action.rank (finiteTower n) = (n : Ordinal) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [finiteTower, Action.rank_coordination]
      rw [inductionHypothesis, ciSup_const]
      rw [Order.succ_eq_add_one, Nat.cast_add_one]

@[simp] theorem commonsAdmissible_finiteTower (n : Nat) :
    Action.CommonsAdmissible (finiteTower n) := by
  induction n with
  | zero => trivial
  | succ n inductionHypothesis =>
      change (∀ _ : Fin 2, Action.CommonsAdmissible (finiteTower n)) ∧
        ∀ _ _ : Fin 2,
          Action.rank (finiteTower n) = Action.rank (finiteTower n)
      exact ⟨fun _ => inductionHypothesis, fun _ _ => rfl⟩

/-- A schedule-insensitive countable occurrence family. -/
def constantSemantics : ScheduleSemantics Nat (Fin 2) := fun _ => 0

theorem constantInvariant : IsChain constantSemantics :=
  fun _ _ => rfl

theorem nat_hasAtLeastTwo : HasAtLeastTwo Nat :=
  ⟨0, 1, Nat.zero_ne_one⟩

/-- A countable chain whose child ranks are unbounded below `omega`. -/
def limitChain : Action.{0, 0} (Fin 2) :=
  .compound Nat nat_hasAtLeastTwo finiteTower
    (.chain constantSemantics constantInvariant)

/-- The invariant chain reaches a limit ordinal even though no coordination
occurs at its root. -/
theorem rank_limitChain : Action.rank limitChain = Ordinal.omega0 := by
  rw [limitChain, Action.rank_chain]
  simpa only [rank_finiteTower] using Ordinal.iSup_natCast

/-- Every child remains strictly below the chain's limit rank.  Hence the
finite slogan "chains do not raise order" depends on the supremum being
attained; it is not valid for arbitrary infinite occurrence families. -/
theorem every_child_strictly_below_limitChain (n : Nat) :
    Action.rank (finiteTower n) < Action.rank limitChain := by
  rw [rank_finiteTower, rank_limitChain]
  exact Ordinal.natCast_lt_omega0 n

/-- The limit counterexample still satisfies Commons's recursive equal-order
condition: the root is a chain, and every finite coordination is homogeneous. -/
theorem commonsAdmissible_limitChain :
    Action.CommonsAdmissible limitChain := by
  exact fun n => commonsAdmissible_finiteTower n

end LimitCanary

end Mettapedia.Cybernetics.HierarchicalComplexity

#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.chain_or_coordination
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Action.child_rank_lt_coordination
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.LimitCanary.rank_limitChain
