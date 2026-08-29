import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.MapFold
import Mathlib.Order.Lattice

/-!
# Monotone join handler for cooperative worlds

Alternative worlds and cooperative producers require different handlers.
When every branch contributes information in a join-semilattice, all deltas
may be joined.  The result is permutation-invariant, inflationary, and
idempotent under duplicate contributions.

The occurrence answers remain a multiset.  Idempotence applies to the state
delta, not to answer multiplicity.  A second additive construction provides
the negative control: duplicate resource or evidence occurrences count twice
under monoid addition and therefore must not be silently interpreted as join.
-/

namespace Mettapedia.GSLT.Dynamics.MonotoneWorldHandler

set_option autoImplicit false

universe uAnswer uDelta

/-- One cooperative branch contributes an answer occurrence and an
inflationary state delta. -/
structure Contribution (Answer : Type uAnswer) (Delta : Type uDelta) where
  answer : Answer
  delta : Delta
deriving DecidableEq

/-- Join all state contributions. -/
def joinDeltas {Answer : Type uAnswer} {Delta : Type uDelta}
    [SemilatticeSup Delta] [OrderBot Delta] :
    List (Contribution Answer Delta) -> Delta
  | [] => ⊥
  | branch :: rest => branch.delta ⊔ joinDeltas rest

/-- The complete cooperative result retains answer multiplicity and joins all
state contributions into the parent. -/
@[ext] structure JoinedResult (Answer : Type uAnswer) (Delta : Type uDelta) where
  answers : Multiset Answer
  state : Delta
deriving DecidableEq

/-- Execute one complete monotone wave. -/
def runJoin {Answer : Type uAnswer} {Delta : Type uDelta}
    [SemilatticeSup Delta] [OrderBot Delta]
    (parent : Delta) (branches : List (Contribution Answer Delta)) :
    JoinedResult Answer Delta where
  answers := branches.map Contribution.answer
  state := parent ⊔ joinDeltas branches

@[simp] theorem joinDeltas_nil {Answer : Type uAnswer} {Delta : Type uDelta}
    [SemilatticeSup Delta] [OrderBot Delta] :
    joinDeltas ([] : List (Contribution Answer Delta)) = ⊥ :=
  rfl

@[simp] theorem joinDeltas_cons {Answer : Type uAnswer} {Delta : Type uDelta}
    [SemilatticeSup Delta] [OrderBot Delta]
    (branch : Contribution Answer Delta)
    (rest : List (Contribution Answer Delta)) :
    joinDeltas (branch :: rest) = branch.delta ⊔ joinDeltas rest :=
  rfl

/-- Join respects occurrence-family concatenation. -/
theorem joinDeltas_append {Answer : Type uAnswer} {Delta : Type uDelta}
    [SemilatticeSup Delta] [OrderBot Delta]
    (left right : List (Contribution Answer Delta)) :
    joinDeltas (left ++ right) = joinDeltas left ⊔ joinDeltas right := by
  induction left with
  | nil => simp [joinDeltas]
  | cons branch rest inductionHypothesis =>
      simp only [List.cons_append, joinDeltas_cons, inductionHypothesis]
      exact (sup_assoc _ _ _).symm

/-- Cooperative state is independent of branch enumeration. -/
theorem joinDeltas_perm {Answer : Type uAnswer} {Delta : Type uDelta}
    [SemilatticeSup Delta] [OrderBot Delta]
    {left right : List (Contribution Answer Delta)}
    (permutation : left.Perm right) :
    joinDeltas left = joinDeltas right := by
  induction permutation with
  | nil => rfl
  | cons branch permutation inductionHypothesis =>
      simp [joinDeltas, inductionHypothesis]
  | swap first second rest =>
      simp only [joinDeltas_cons]
      exact sup_left_comm _ _ _
  | trans first second firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

/-- Every retained branch delta is below the total joined delta. -/
theorem delta_le_joinDeltas {Answer : Type uAnswer} {Delta : Type uDelta}
    [SemilatticeSup Delta] [OrderBot Delta]
    {branch : Contribution Answer Delta}
    {branches : List (Contribution Answer Delta)}
    (member : branch ∈ branches) :
    branch.delta ≤ joinDeltas branches := by
  induction branches with
  | nil => simp at member
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with same | inRest
      · subst head
        exact le_sup_left
      · exact le_trans (inductionHypothesis inRest) le_sup_right

/-- A monotone wave cannot retract information from its parent. -/
theorem parent_le_runJoin_state {Answer : Type uAnswer} {Delta : Type uDelta}
    [SemilatticeSup Delta] [OrderBot Delta]
    (parent : Delta) (branches : List (Contribution Answer Delta)) :
    parent ≤ (runJoin parent branches).state :=
  le_sup_left

/-- Repeating one branch delta is observationally inert at the joined state. -/
theorem duplicate_delta_idempotent {Answer : Type uAnswer}
    {Delta : Type uDelta} [SemilatticeSup Delta] [OrderBot Delta]
    (branch : Contribution Answer Delta)
    (rest : List (Contribution Answer Delta)) :
    joinDeltas (branch :: branch :: rest) =
      joinDeltas (branch :: rest) := by
  simp [joinDeltas]

/-- Complete joined execution is invariant under branch permutations at both
the occurrence-bag answer and state observations. -/
theorem runJoin_perm {Answer : Type uAnswer} {Delta : Type uDelta}
    [SemilatticeSup Delta] [OrderBot Delta]
    (parent : Delta) {left right : List (Contribution Answer Delta)}
    (permutation : left.Perm right) :
    runJoin parent left = runJoin parent right := by
  apply JoinedResult.ext
  · exact Quot.sound (permutation.map Contribution.answer)
  · exact congrArg (fun delta => parent ⊔ delta)
      (joinDeltas_perm permutation)

/-! ## Additive occurrences are deliberately separate -/

/-- Additive deltas count duplicate occurrences and need not be idempotent. -/
def sumDeltas {Delta : Type uDelta} [AddMonoid Delta] : List Delta -> Delta
  | [] => 0
  | delta :: rest => delta + sumDeltas rest

@[simp] theorem sumDeltas_nil {Delta : Type uDelta} [AddMonoid Delta] :
    sumDeltas ([] : List Delta) = 0 :=
  rfl

@[simp] theorem sumDeltas_cons {Delta : Type uDelta} [AddMonoid Delta]
    (delta : Delta) (rest : List Delta) :
    sumDeltas (delta :: rest) = delta + sumDeltas rest :=
  rfl

/-! ## Positive and negative controls -/

namespace Canary

inductive Fact where
  | p
  | q
  | r
  | s
deriving DecidableEq, Repr

inductive Answer where
  | left
  | right
deriving DecidableEq, Repr

def leftBranch : Contribution Answer (Finset Fact) :=
  { answer := .left, delta := {.q, .r} }

def rightBranch : Contribution Answer (Finset Fact) :=
  { answer := .right, delta := {.r, .s} }

/-- Cooperative branches retain both answers and converge to set union. -/
theorem cooperative_wave_result :
    runJoin ({.p} : Finset Fact) [leftBranch, rightBranch] =
      { answers := {.left, .right}, state := {.p, .q, .r, .s} } := by
  decide

/-- Reversing cooperative branches is unobservable. -/
theorem cooperative_wave_order_free :
    runJoin ({.p} : Finset Fact) [leftBranch, rightBranch] =
      runJoin ({.p} : Finset Fact) [rightBranch, leftBranch] :=
  runJoin_perm _ (by decide)

/-- Repeating a set-valued contribution adds no new state. -/
theorem repeated_set_delta_collapses :
    joinDeltas [leftBranch, leftBranch] = joinDeltas [leftBranch] :=
  duplicate_delta_idempotent leftBranch []

/-- The same duplicate policy is false for an additive occurrence account. -/
theorem repeated_additive_delta_counts :
    sumDeltas ([1, 1] : List Nat) = 2 /\
      sumDeltas ([1] : List Nat) = 1 := by
  decide

/-- Set join and occurrence addition therefore cannot share one implicit
duplicate policy. -/
theorem join_is_not_occurrence_addition :
    (joinDeltas [leftBranch, leftBranch]).card = 2 /\
      sumDeltas ([2, 2] : List Nat) = 4 := by
  decide

end Canary

/-! ## Axiom audit -/

#print axioms joinDeltas_append
#print axioms joinDeltas_perm
#print axioms delta_le_joinDeltas
#print axioms parent_le_runJoin_state
#print axioms duplicate_delta_idempotent
#print axioms runJoin_perm
#print axioms Canary.cooperative_wave_result
#print axioms Canary.join_is_not_occurrence_addition

end Mettapedia.GSLT.Dynamics.MonotoneWorldHandler
