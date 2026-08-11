import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Basic
import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# Alternating parity certificates for ProofGSLT

This module supplies the global evidence shape needed beyond deterministic
Buchi controllers.  A verifier strategy chooses one successor at verifier
positions; every authored successor remains possible at falsifier positions.
The certificate carries one natural-valued rank for every odd priority.

Below an odd threshold, ranks may not increase along controlled edges and
must decrease when leaving a vertex at exactly that priority.  Consequently
an infinite controlled play cannot have an odd priority as its eventual
maximum recurring priority.

The result here is deliberately one-sided: a valid rank is sound for the
parity objective.  Completeness of this rank format and adequacy of a modal
mu-calculus evaluation-game translation are separate obligations.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT.Parity

open Mettapedia.GSLT.LanguageDef.KernelAuthority

universe uState

/-- Ownership of a parity-game position. -/
inductive Player where
  | verifier
  | falsifier
deriving Repr, DecidableEq

/-- A finite-state parity-game presentation.  The carrier is made finite by
the instances used by checking; the semantic definitions remain relational. -/
structure Game (State : Type uState) where
  edge : State -> State -> Bool
  owner : State -> Player
  priority : State -> Nat

namespace Game

variable {State : Type uState}

/-- Largest priority present in a finite game carrier. -/
def maxPriority [Fintype State] (game : Game State) : Nat :=
  Finset.univ.sup game.priority

/-- Every vertex priority lies below the computed finite maximum. -/
theorem priority_le_max [Fintype State] (game : Game State) (state : State) :
    game.priority state <= game.maxPriority := by
  exact Finset.le_sup (Finset.mem_univ state)

/-- Finite threshold indices available to a progress certificate. -/
abbrev Threshold [Fintype State] (game : Game State) :=
  Fin (game.maxPriority + 1)

end Game

/-- A memoryless verifier strategy plus the finite cone it certifies. -/
structure Strategy (State : Type uState) where
  active : State -> Bool
  next : State -> State

namespace Strategy

variable {State : Type uState}

/-- A controlled edge is always an authored game edge.  At verifier-owned
positions it must be the selected successor; at falsifier-owned positions the
opponent retains every authored choice. -/
def ControlledEdge (game : Game State) (strategy : Strategy State)
    (source target : State) : Prop :=
  game.edge source target = true /\
    match game.owner source with
    | .verifier => target = strategy.next source
    | .falsifier => True

instance controlledEdgeDecidable [DecidableEq State]
    (game : Game State) (strategy : Strategy State)
    (source target : State) :
    Decidable (strategy.ControlledEdge game source target) := by
  unfold ControlledEdge
  cases game.owner source <;> infer_instance

/-- The root is covered, every active position has a move, and every
controlled successor remains in the certified cone. -/
def LocallyValid (game : Game State) (strategy : Strategy State)
    (root : State) : Prop :=
  strategy.active root = true /\
    forall source, strategy.active source = true ->
      (exists target, strategy.ControlledEdge game source target) /\
      forall target, strategy.ControlledEdge game source target ->
        strategy.active target = true

/-- An infinite play respecting the selected verifier moves and every
possible falsifier move. -/
structure Play (game : Game State) (strategy : Strategy State)
    (root : State) where
  state : Nat -> State
  starts : state 0 = root
  follows : forall index,
    strategy.ControlledEdge game (state index) (state (index + 1))

/-- An odd priority is dominant on a path when it appears infinitely often
and all priorities are eventually no larger. -/
def BadOddDominant (game : Game State) (path : Nat -> State) : Prop :=
  exists priority,
    Odd priority /\
      Set.Infinite {index | game.priority (path index) = priority} /\
      exists cutoff, forall index, cutoff <= index ->
        game.priority (path index) <= priority

/-- A strategy wins when no controlled play has an odd dominant priority.
This is the maximum-priority-even convention, stated negatively so it remains
meaningful without assuming a finite carrier. -/
def ParityWinning (game : Game State) (strategy : Strategy State)
    (root : State) : Prop :=
  forall play : Play game strategy root,
    ¬ BadOddDominant game play.state

end Strategy

/-- One natural rank at every finite priority threshold and active state. -/
structure ProgressMeasure {State : Type uState} [Fintype State]
    (game : Game State) where
  rank : game.Threshold -> State -> Nat

namespace ProgressMeasure

variable {State : Type uState} [Fintype State]

/-- Below each odd threshold, controlled edges do not increase its rank.
Leaving a vertex at exactly that odd priority decreases the rank strictly. -/
def GloballyValid (game : Game State) (strategy : Strategy State)
    (measure : ProgressMeasure game) : Prop :=
  forall threshold : game.Threshold, Odd threshold.val ->
    forall source, strategy.active source = true ->
      forall target, strategy.ControlledEdge game source target ->
        game.priority source <= threshold.val ->
        game.priority target <= threshold.val ->
          measure.rank threshold target <= measure.rank threshold source /\
          (game.priority source = threshold.val ->
            measure.rank threshold target < measure.rank threshold source)

/-- Complete parity-certificate validity combines local edge closure with the
global threshold ranks. -/
def Valid (game : Game State) (strategy : Strategy State)
    (measure : ProgressMeasure game) (root : State) : Prop :=
  strategy.LocallyValid game root /\
    measure.GloballyValid game strategy

private def validDecidable [DecidableEq State]
    (game : Game State) (strategy : Strategy State)
    (measure : ProgressMeasure game) (root : State) :
    Decidable (measure.Valid game strategy root) := by
  unfold Valid GloballyValid Strategy.LocallyValid
  infer_instance

/-- Executable finite checker for a parity progress certificate. -/
def check [DecidableEq State]
    (game : Game State) (strategy : Strategy State)
    (measure : ProgressMeasure game) (root : State) : Bool :=
  @decide (measure.Valid game strategy root)
    (validDecidable game strategy measure root)

theorem check_eq_true_iff [DecidableEq State]
    (game : Game State) (strategy : Strategy State)
    (measure : ProgressMeasure game) (root : State) :
    measure.check game strategy root = true <->
      measure.Valid game strategy root := by
  simp [check]

end ProgressMeasure

/-! ## Infinite-occurrence and descent lemmas -/

/-- An infinite set of natural indices contains an index beyond every lower
bound. -/
theorem infiniteNatSet_exists_ge {indices : Set Nat}
    (infinite : indices.Infinite) (lower : Nat) :
    exists index, lower <= index /\ index ∈ indices := by
  by_contra noWitness
  have subset : indices ⊆ Set.Iio lower := by
    intro index member
    by_contra notBelow
    exact noWitness
      ⟨index, Nat.le_of_not_gt notBelow, member⟩
  exact infinite ((Set.finite_Iio lower).subset subset)

/-- First selected member of an infinite set at or beyond a lower bound. -/
noncomputable def nextIndex {indices : Set Nat} (infinite : indices.Infinite)
    (lower : Nat) : Nat :=
  Classical.choose (infiniteNatSet_exists_ge infinite lower)

theorem nextIndex_ge {indices : Set Nat} (infinite : indices.Infinite)
    (lower : Nat) :
    lower <= nextIndex infinite lower :=
  (Classical.choose_spec (infiniteNatSet_exists_ge infinite lower)).1

theorem nextIndex_mem {indices : Set Nat} (infinite : indices.Infinite)
    (lower : Nat) :
    nextIndex infinite lower ∈ indices :=
  (Classical.choose_spec (infiniteNatSet_exists_ge infinite lower)).2

/-- Increasing enumeration of selected members of an infinite index set. -/
noncomputable def occurrence {indices : Set Nat}
    (infinite : indices.Infinite) (lower : Nat) : Nat -> Nat
  | 0 => nextIndex infinite lower
  | index + 1 => nextIndex infinite (occurrence infinite lower index + 1)

theorem occurrence_mem {indices : Set Nat} (infinite : indices.Infinite)
    (lower index : Nat) :
    occurrence infinite lower index ∈ indices := by
  cases index with
  | zero => exact nextIndex_mem infinite lower
  | succ index => exact nextIndex_mem infinite _

theorem occurrence_ge_lower {indices : Set Nat}
    (infinite : indices.Infinite) (lower index : Nat) :
    lower <= occurrence infinite lower index := by
  induction index with
  | zero => exact nextIndex_ge infinite lower
  | succ index inductionHypothesis =>
      exact le_trans inductionHypothesis
        (le_trans (Nat.le_succ _) (nextIndex_ge infinite _))

theorem occurrence_strict {indices : Set Nat} (infinite : indices.Infinite)
    (lower index : Nat) :
    occurrence infinite lower index <
      occurrence infinite lower (index + 1) := by
  exact lt_of_lt_of_le (Nat.lt_succ_self _)
    (nextIndex_ge infinite _)

/-- Natural numbers admit no infinite pointwise-strict descending sequence. -/
theorem no_infinite_nat_descent (values : Nat -> Nat)
    (decreases : forall index, values (index + 1) < values index) : False := by
  have bounded : forall index, values index + index <= values 0 := by
    intro index
    induction index with
    | zero => simp
    | succ index inductionHypothesis =>
        have decrease := decreases index
        omega
  have impossible := bounded (values 0 + 1)
  omega

namespace Strategy.Play

variable {State : Type uState}

/-- Local validity keeps every state of a controlled play inside the active
cone. -/
theorem active {game : Game State} {strategy : Strategy State} {root : State}
    (localValidity : strategy.LocallyValid game root)
    (play : Strategy.Play game strategy root) :
    forall index, strategy.active (play.state index) = true := by
  intro index
  induction index with
  | zero => simpa [play.starts] using localValidity.1
  | succ index inductionHypothesis =>
      exact localValidity.2 (play.state index) inductionHypothesis |>.2
        (play.state (index + 1)) (play.follows index)

end Strategy.Play

namespace ProgressMeasure

variable {State : Type uState} [Fintype State]

/-- Once a path remains under a threshold, its corresponding rank is
nonincreasing. -/
private theorem rank_nonincreasing
    {game : Game State} {strategy : Strategy State} {root : State}
    {measure : ProgressMeasure game}
    (valid : measure.Valid game strategy root)
    (play : Strategy.Play game strategy root)
    (threshold : game.Threshold) (odd : Odd threshold.val)
    (cutoff : Nat)
    (bounded : forall index, cutoff <= index ->
      game.priority (play.state index) <= threshold.val)
    {first second : Nat} (afterCutoff : cutoff <= first)
    (ordered : first <= second) :
    measure.rank threshold (play.state second) <=
      measure.rank threshold (play.state first) := by
  obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le ordered
  induction distance with
  | zero => simp
  | succ distance inductionHypothesis =>
      let index := first + distance
      have indexAfter : cutoff <= index := by
        dsimp [index]
        omega
      have nextAfter : cutoff <= index + 1 := by omega
      have edgeValidity := valid.2 threshold odd
        (play.state index) (play.active valid.1 index)
        (play.state (index + 1)) (play.follows index)
        (bounded index indexAfter) (bounded (index + 1) nextAfter)
      have stepLe := edgeValidity.1
      have accumulated :
          measure.rank threshold (play.state index) <=
            measure.rank threshold (play.state first) := by
        simpa [index] using inductionHypothesis
      have combined := le_trans stepLe accumulated
      simpa [index, Nat.add_assoc] using combined

/-- Two successive occurrences of the threshold priority force a strict rank
decrease, even when lower-priority states occur between them. -/
private theorem rank_strict_between
    {game : Game State} {strategy : Strategy State} {root : State}
    {measure : ProgressMeasure game}
    (valid : measure.Valid game strategy root)
    (play : Strategy.Play game strategy root)
    (threshold : game.Threshold) (odd : Odd threshold.val)
    (cutoff : Nat)
    (bounded : forall index, cutoff <= index ->
      game.priority (play.state index) <= threshold.val)
    {first second : Nat} (afterCutoff : cutoff <= first)
    (ordered : first < second)
    (atThreshold : game.priority (play.state first) = threshold.val) :
    measure.rank threshold (play.state second) <
      measure.rank threshold (play.state first) := by
  have firstNextAfter : cutoff <= first + 1 := by omega
  have firstBound := bounded first afterCutoff
  have nextBound := bounded (first + 1) firstNextAfter
  have edgeValidity := valid.2 threshold odd
    (play.state first) (play.active valid.1 first)
    (play.state (first + 1)) (play.follows first)
    firstBound nextBound
  have firstDecrease := edgeValidity.2 atThreshold
  have remaining :
      measure.rank threshold (play.state second) <=
        measure.rank threshold (play.state (first + 1)) :=
    rank_nonincreasing valid play threshold odd cutoff bounded
      firstNextAfter (by omega)
  exact lt_of_le_of_lt remaining firstDecrease

/-- **Parity soundness.**  A valid finite threshold measure rules out every
odd-dominant controlled infinite play. -/
theorem parity_sound
    {game : Game State} {strategy : Strategy State} {root : State}
    {measure : ProgressMeasure game}
    (valid : measure.Valid game strategy root) :
    strategy.ParityWinning game root := by
  intro play bad
  rcases bad with ⟨priority, odd, recurring, cutoff, bounded⟩
  obtain ⟨firstVisit, _, firstPriority⟩ :=
    infiniteNatSet_exists_ge recurring cutoff
  have priorityLeMax : priority <= game.maxPriority := by
    rw [← firstPriority]
    exact game.priority_le_max (play.state firstVisit)
  let threshold : game.Threshold :=
    ⟨priority, Nat.lt_succ_of_le priorityLeMax⟩
  let indices : Set Nat :=
    {index | game.priority (play.state index) = priority}
  have indicesInfinite : indices.Infinite := by
    exact recurring
  let visits : Nat -> Nat := occurrence indicesInfinite cutoff
  let ranks : Nat -> Nat := fun index =>
    measure.rank threshold (play.state (visits index))
  apply no_infinite_nat_descent ranks
  intro index
  apply rank_strict_between valid play threshold
    (by simpa [threshold] using odd) cutoff
    (by
      intro position after
      simpa [threshold] using bounded position after)
    (occurrence_ge_lower indicesInfinite cutoff index)
    (occurrence_strict indicesInfinite cutoff index)
  have member := occurrence_mem indicesInfinite cutoff index
  simpa [indices, threshold] using member

/-- The executable parity measure checker, packaged at the common checker
interface.  This theorem states soundness only; it does not manufacture the
still-missing completeness theorem. -/
def parityChecker [DecidableEq State] (game : Game State) :
    Checker (Strategy State × State) (ProgressMeasure game) where
  check claim measure :=
    measure.check game claim.1 claim.2

theorem parityChecker_sound [DecidableEq State] (game : Game State) :
    Checker.Sound (parityChecker game)
      (fun claim => claim.1.ParityWinning game claim.2) := by
  intro claim measure accepted
  apply parity_sound
  exact (check_eq_true_iff game claim.1 measure claim.2).mp accepted

end ProgressMeasure

/-! ## Separating fixtures -/

namespace Canary

/-- An odd-priority state immediately exits above that threshold, while the
even-priority state returns.  The maximum recurring priority is even. -/
def goodGame : Game Bool where
  edge source target := decide (target = !source)
  owner _ := .verifier
  priority state := if state then 2 else 1

def goodStrategy : Strategy Bool where
  active _ := true
  next state := !state

def goodMeasure : ProgressMeasure goodGame where
  rank _ _ := 0

theorem goodCertificate :
    goodMeasure.check goodGame goodStrategy false = true := by
  decide

theorem goodStrategy_wins :
    goodStrategy.ParityWinning goodGame false := by
  apply ProgressMeasure.parity_sound
  exact (ProgressMeasure.check_eq_true_iff
    goodGame goodStrategy goodMeasure false).mp goodCertificate

/-- A one-state odd self-loop is the minimal losing parity game. -/
def oddLoopGame : Game Unit where
  edge _ _ := true
  owner _ := .verifier
  priority _ := 1

def oddLoopStrategy : Strategy Unit where
  active _ := true
  next _ := ()

def oddLoopPlay : Strategy.Play oddLoopGame oddLoopStrategy () where
  state _ := ()
  starts := rfl
  follows _ := by simp [Strategy.ControlledEdge, oddLoopGame, oddLoopStrategy]

theorem oddLoop_bad :
    Strategy.BadOddDominant oddLoopGame oddLoopPlay.state := by
  refine ⟨1, ⟨0, by omega⟩, ?_, 0, ?_⟩
  · have infiniteRange : Set.Infinite (Set.range (fun index : Nat => index)) :=
      Set.infinite_range_of_injective Function.injective_id
    simpa [oddLoopGame, oddLoopPlay, Set.range_id] using infiniteRange
  · intro index _
    simp [oddLoopGame, oddLoopPlay]

theorem oddLoop_not_winning :
    ¬ oddLoopStrategy.ParityWinning oddLoopGame () := by
  intro winning
  exact winning oddLoopPlay oddLoop_bad

/-- No natural-valued parity progress measure can validate an odd self-loop:
its sole threshold rank would have to be strictly smaller than itself. -/
theorem oddLoop_no_valid_measure
    (measure : ProgressMeasure oddLoopGame) :
    ¬ measure.Valid oddLoopGame oddLoopStrategy () := by
  intro valid
  let threshold : oddLoopGame.Threshold := ⟨1, by
    simp [Game.maxPriority, oddLoopGame]⟩
  have thresholdOdd : Odd threshold.val := by
    change Odd 1
    exact ⟨0, rfl⟩
  have edgeValidity := valid.2 threshold thresholdOdd
    () (by rfl) ()
    (by simp [Strategy.ControlledEdge, oddLoopGame, oddLoopStrategy])
    (by simp [oddLoopGame, threshold])
    (by simp [oddLoopGame, threshold])
  have impossible := edgeValidity.2 (by simp [oddLoopGame, threshold])
  exact (Nat.lt_irrefl _) impossible

/-- The positive and negative examples separate sound acceptance from a real
odd-dominant failure. -/
theorem parity_boundary_nontrivial :
    goodMeasure.check goodGame goodStrategy false = true /\
      goodStrategy.ParityWinning goodGame false /\
      (¬ oddLoopStrategy.ParityWinning oddLoopGame ()) /\
      forall measure : ProgressMeasure oddLoopGame,
        ¬ measure.Valid oddLoopGame oddLoopStrategy () :=
  ⟨goodCertificate, goodStrategy_wins, oddLoop_not_winning,
    oddLoop_no_valid_measure⟩

end Canary

end Mettapedia.GSLT.LanguageDef.ProofGSLT.Parity
