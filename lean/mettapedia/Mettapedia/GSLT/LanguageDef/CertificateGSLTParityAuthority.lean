import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Chain
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Basic
import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# Alternating parity certificates for CertificateGSLT

This module supplies the global evidence shape needed beyond deterministic
Buchi controllers.  A verifier strategy chooses one successor at verifier
positions; every authored successor remains possible at falsifier positions.
The certificate carries one natural-valued rank for every odd priority.

Below an odd threshold, ranks may not increase along controlled edges and
must decrease when leaving a vertex at exactly that priority.  Consequently
an infinite controlled play cannot have an odd priority as its eventual
maximum recurring priority.

The rank format is characterized exactly by the absence of a return to an
odd-threshold vertex while remaining below that threshold.  Restricting a
root-winning strategy to its reachable controlled cone satisfies this graph
condition and therefore generates an accepted rank certificate.  Adequacy of
a modal mu-calculus evaluation-game translation remains a separate obligation.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity

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

/-- A strategy wins when it generates legal play from the root and no
controlled play has an odd dominant priority.  Including local validity here
is essential: otherwise a verifier could select a non-edge and vacuously
"win" because no controlled infinite play would exist.

The second conjunct is the maximum-priority-even convention, stated
negatively so it remains meaningful without assuming a finite carrier. -/
def ParityWinning (game : Game State) (strategy : Strategy State)
    (root : State) : Prop :=
  strategy.LocallyValid game root /\
    forall play : Play game strategy root,
      ¬ BadOddDominant game play.state

/-! ## Root-reachable strategy cones -/

/-- A state is reachable from the root by the moves retained by a strategy.
This relation depends on the selected verifier moves and authored falsifier
moves, but not on the strategy's separately declared active bitmap. -/
def Reachable (game : Game State) (strategy : Strategy State)
    (root state : State) : Prop :=
  Relation.ReflTransGen (strategy.ControlledEdge game) root state

/-- Restrict the active bitmap to the states that can actually be reached
from the root.  The selected verifier move is unchanged. -/
noncomputable def reachableRestriction (game : Game State)
    (strategy : Strategy State) (root : State) : Strategy State := by
  classical
  exact
    { active := fun state => decide (strategy.Reachable game root state)
      next := strategy.next }

@[simp]
theorem reachableRestriction_active_eq_true_iff (game : Game State)
    (strategy : Strategy State) (root state : State) :
    (strategy.reachableRestriction game root).active state = true ↔
      strategy.Reachable game root state := by
  classical
  simp [reachableRestriction]

@[simp]
theorem reachableRestriction_controlledEdge_iff (game : Game State)
    (strategy : Strategy State) (root source target : State) :
    (strategy.reachableRestriction game root).ControlledEdge game source target ↔
      strategy.ControlledEdge game source target := by
  simp [ControlledEdge, reachableRestriction]

/-- Local validity propagates the original active invariant along every
root-reachable controlled path. -/
theorem active_of_reachable {game : Game State} {strategy : Strategy State}
    {root state : State} (locallyValid : strategy.LocallyValid game root)
    (reachable : strategy.Reachable game root state) :
    strategy.active state = true := by
  induction reachable with
  | refl => exact locallyValid.1
  | @tail source target _ controlled sourceActive =>
      exact (locallyValid.2 source sourceActive).2 target controlled

/-- A locally valid strategy remains locally valid after discarding every
active state outside its root-reachable cone. -/
theorem reachableRestriction_locallyValid
    {game : Game State} {strategy : Strategy State} {root : State}
    (locallyValid : strategy.LocallyValid game root) :
    (strategy.reachableRestriction game root).LocallyValid game root := by
  classical
  constructor
  · apply (reachableRestriction_active_eq_true_iff
      game strategy root root).2
    exact Relation.ReflTransGen.refl
  · intro source sourceActive
    have sourceReachable : strategy.Reachable game root source :=
      (reachableRestriction_active_eq_true_iff game strategy root source).1
        sourceActive
    have originalActive := active_of_reachable locallyValid sourceReachable
    obtain ⟨⟨target, controlled⟩, closed⟩ :=
      locallyValid.2 source originalActive
    constructor
    · exact ⟨target,
        (reachableRestriction_controlledEdge_iff game strategy root source target).2
          controlled⟩
    · intro successor restrictedControlled
      have originalControlled :
          strategy.ControlledEdge game source successor :=
        (reachableRestriction_controlledEdge_iff game strategy root source successor).1
          restrictedControlled
      apply (reachableRestriction_active_eq_true_iff
        game strategy root successor).2
      exact sourceReachable.tail originalControlled

/-- Root restriction does not alter any controlled play, so it preserves a
winning strategy while removing irrelevant disconnected active components. -/
theorem parityWinning_reachableRestriction
    {game : Game State} {strategy : Strategy State} {root : State}
    (winning : strategy.ParityWinning game root) :
    (strategy.reachableRestriction game root).ParityWinning game root := by
  refine ⟨reachableRestriction_locallyValid winning.1, ?_⟩
  intro restrictedPlay bad
  let originalPlay : strategy.Play game root :=
    { state := restrictedPlay.state
      starts := restrictedPlay.starts
      follows := fun index =>
        (reachableRestriction_controlledEdge_iff game strategy root
          (restrictedPlay.state index)
          (restrictedPlay.state (index + 1))).1
            (restrictedPlay.follows index) }
  exact winning.2 originalPlay bad

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

/-! ## Constructing ranks from the controlled graph -/

/-- A controlled edge whose endpoints both lie at or below one priority
threshold.  The source is required to be in the strategy cone; local validity
then keeps its target in the same cone. -/
def thresholdEdge (game : Game State) (strategy : Strategy State)
    (threshold : game.Threshold) (source target : State) : Prop :=
  strategy.active source = true /\
    strategy.ControlledEdge game source target /\
    game.priority source <= threshold.val /\
    game.priority target <= threshold.val

/-- Graph-theoretic condition sufficient to synthesize the natural ranks:
after leaving an active vertex at an odd threshold, no path remaining below
that threshold may return to it. -/
def NoOddThresholdReturn (game : Game State) (strategy : Strategy State) : Prop :=
  forall threshold : game.Threshold, Odd threshold.val ->
    forall source target,
      strategy.active source = true ->
      strategy.ControlledEdge game source target ->
      game.priority source = threshold.val ->
      game.priority target <= threshold.val ->
      ¬ Relation.ReflTransGen
        (thresholdEdge game strategy threshold) target source

/-- Critical vertices reachable without crossing above a threshold. -/
noncomputable def criticalReachable (game : Game State)
    (strategy : Strategy State) (threshold : game.Threshold)
    (source : State) : Finset State := by
  classical
  exact Finset.univ.filter fun target =>
    Relation.ReflTransGen (thresholdEdge game strategy threshold)
        source target /\
      game.priority target = threshold.val

theorem criticalReachable_mono_of_thresholdEdge
    (game : Game State) (strategy : Strategy State)
    (threshold : game.Threshold) {source target : State}
    (edge : thresholdEdge game strategy threshold source target) :
    criticalReachable game strategy threshold target ⊆
      criticalReachable game strategy threshold source := by
  classical
  intro candidate member
  simp only [criticalReachable, Finset.mem_filter, Finset.mem_univ,
    true_and] at member ⊢
  exact ⟨Relation.ReflTransGen.head edge member.1, member.2⟩

/-- The canonical finite rank counts threshold-priority vertices still
reachable below that threshold. -/
noncomputable def ofNoOddThresholdReturn (game : Game State)
    (strategy : Strategy State) : ProgressMeasure game where
  rank threshold source :=
    (criticalReachable game strategy threshold source).card

/-- The graph condition constructs a globally valid threshold measure. -/
theorem ofNoOddThresholdReturn_globallyValid
    (game : Game State) (strategy : Strategy State)
    (noReturn : NoOddThresholdReturn game strategy) :
    (ofNoOddThresholdReturn game strategy).GloballyValid game strategy := by
  classical
  intro threshold odd source sourceActive target controlled
    sourceBelow targetBelow
  let edge : thresholdEdge game strategy threshold source target :=
    ⟨sourceActive, controlled, sourceBelow, targetBelow⟩
  have subset := criticalReachable_mono_of_thresholdEdge
    game strategy threshold edge
  constructor
  · exact Finset.card_le_card subset
  · intro sourceAtThreshold
    apply Finset.card_lt_card
    apply (Finset.ssubset_iff_of_subset subset).2
    refine ⟨source, ?_, ?_⟩
    · simp only [criticalReachable, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨Relation.ReflTransGen.refl, sourceAtThreshold⟩
    · simp only [criticalReachable, Finset.mem_filter, Finset.mem_univ,
        true_and, not_and]
      intro returns _
      exact noReturn threshold odd source target sourceActive controlled
        sourceAtThreshold targetBelow returns

/-- A globally valid rank is nonincreasing along every finite path that stays
below an odd threshold. -/
theorem rank_nonincreasing_of_reflTransGen
    (game : Game State) (strategy : Strategy State)
    (measure : ProgressMeasure game)
    (valid : measure.GloballyValid game strategy)
    (threshold : game.Threshold) (odd : Odd threshold.val)
    {source target : State}
    (path : Relation.ReflTransGen
      (thresholdEdge game strategy threshold) source target) :
    measure.rank threshold target <= measure.rank threshold source := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | @head source next first _ inductionHypothesis =>
      have firstValidity := valid threshold odd source first.1 next first.2.1
        first.2.2.1 first.2.2.2
      exact inductionHypothesis.trans firstValidity.1

/-- Conversely, a valid rank rules out every odd-threshold return. -/
theorem globallyValid_noOddThresholdReturn
    (game : Game State) (strategy : Strategy State)
    (measure : ProgressMeasure game)
    (valid : measure.GloballyValid game strategy) :
    NoOddThresholdReturn game strategy := by
  intro threshold odd source target sourceActive controlled
    sourceAtThreshold targetBelow returns
  have firstValidity := valid threshold odd source sourceActive target controlled
    sourceAtThreshold.le targetBelow
  have returnNonincrease := rank_nonincreasing_of_reflTransGen
    game strategy measure valid threshold odd returns
  exact (Nat.not_lt_of_ge returnNonincrease)
    (firstValidity.2 sourceAtThreshold)

/-- On a finite carrier, the graph condition exactly characterizes the
existence of this threshold-rank format. -/
theorem exists_globallyValid_iff_noOddThresholdReturn
    (game : Game State) (strategy : Strategy State) :
    (exists measure : ProgressMeasure game,
      measure.GloballyValid game strategy) <->
      NoOddThresholdReturn game strategy := by
  constructor
  · rintro ⟨measure, valid⟩
    exact globallyValid_noOddThresholdReturn game strategy measure valid
  · intro noReturn
    exact ⟨ofNoOddThresholdReturn game strategy,
      ofNoOddThresholdReturn_globallyValid game strategy noReturn⟩

/-- A locally valid strategy satisfying the graph condition always has an
accepted progress certificate. -/
theorem exists_valid_of_noOddThresholdReturn
    (game : Game State) (strategy : Strategy State) (root : State)
    (locallyValid : strategy.LocallyValid game root)
    (noReturn : NoOddThresholdReturn game strategy) :
    exists measure : ProgressMeasure game,
      measure.Valid game strategy root :=
  ⟨ofNoOddThresholdReturn game strategy, locallyValid,
    ofNoOddThresholdReturn_globallyValid game strategy noReturn⟩

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

/-- Choose one controlled successor of an active state.  This construction is
semantic rather than executable: the finite certificate checker verifies the
existence claim, while a concrete play may choose any of the retained
falsifier moves. -/
noncomputable def legalSuccessor
    {game : Game State} {strategy : Strategy State} {root : State}
    (localValidity : strategy.LocallyValid game root) (source : State) : State :=
  if active : strategy.active source = true then
    Classical.choose (localValidity.2 source active).1
  else source

theorem legalSuccessor_controlled
    {game : Game State} {strategy : Strategy State} {root : State}
    (localValidity : strategy.LocallyValid game root) (source : State)
    (active : strategy.active source = true) :
    strategy.ControlledEdge game source
      (legalSuccessor localValidity source) := by
  rw [legalSuccessor, dif_pos active]
  exact Classical.choose_spec (localValidity.2 source active).1

theorem legalSuccessor_active
    {game : Game State} {strategy : Strategy State} {root : State}
    (localValidity : strategy.LocallyValid game root) (source : State)
    (active : strategy.active source = true) :
    strategy.active (legalSuccessor localValidity source) = true :=
  (localValidity.2 source active).2 _
    (legalSuccessor_controlled localValidity source active)

/-- The path generated by repeatedly choosing a legal controlled successor. -/
noncomputable def generatedPath
    {game : Game State} {strategy : Strategy State} {root : State}
    (localValidity : strategy.LocallyValid game root) : Nat → State
  | 0 => root
  | index + 1 => legalSuccessor localValidity (generatedPath localValidity index)

theorem generatedPath_active
    {game : Game State} {strategy : Strategy State} {root : State}
    (localValidity : strategy.LocallyValid game root) :
    ∀ index, strategy.active (generatedPath localValidity index) = true := by
  intro index
  induction index with
  | zero => exact localValidity.1
  | succ index inductionHypothesis =>
      exact legalSuccessor_active localValidity _ inductionHypothesis

/-- Local validity is precisely the missing productivity condition: it
constructs an infinite controlled play, so the parity objective can no longer
hold merely because the strategy gets stuck. -/
noncomputable def ofLocallyValid
    {game : Game State} {strategy : Strategy State} {root : State}
    (localValidity : strategy.LocallyValid game root) :
    Strategy.Play game strategy root where
  state := generatedPath localValidity
  starts := rfl
  follows index :=
    legalSuccessor_controlled localValidity _
      (generatedPath_active localValidity index)

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

/-- Prepend one controlled edge to an infinite play. -/
def prepend {game : Game State} {strategy : Strategy State}
    {source target : State}
    (first : strategy.ControlledEdge game source target)
    (tail : Strategy.Play game strategy target) :
    Strategy.Play game strategy source where
  state
    | 0 => source
    | index + 1 => tail.state index
  starts := rfl
  follows
    | 0 => by simpa [tail.starts] using first
    | index + 1 => by simpa [Nat.add_assoc] using tail.follows index

/-- A bad parity tail remains bad after adding one finite prefix edge. -/
theorem prepend_badOddDominant
    {game : Game State} {strategy : Strategy State}
    {source target : State}
    (first : strategy.ControlledEdge game source target)
    (tail : Strategy.Play game strategy target)
    (bad : BadOddDominant game tail.state) :
    BadOddDominant game (tail.prepend first).state := by
  rcases bad with ⟨priority, odd, recurring, cutoff, bounded⟩
  refine ⟨priority, odd, ?_, cutoff + 1, ?_⟩
  · have shiftedInfinite :
        Set.Infinite (Nat.succ ''
          {index | game.priority (tail.state index) = priority}) :=
      recurring.image Nat.succ_injective.injOn
    apply shiftedInfinite.mono
    rintro index ⟨tailIndex, tailMember, rfl⟩
    simpa [prepend] using tailMember
  · intro index afterCutoff
    cases index with
    | zero => omega
    | succ tailIndex =>
        simpa [prepend] using bounded tailIndex (by omega)

end Strategy.Play

/-- Winning from a state implies winning from each controlled successor. -/
theorem Strategy.ParityWinning.of_controlledEdge
    {State : Type uState} {game : Game State} {strategy : Strategy State}
    {source target : State} (winning : strategy.ParityWinning game source)
    (controlled : strategy.ControlledEdge game source target) :
    strategy.ParityWinning game target := by
  have targetActive : strategy.active target = true :=
    (winning.1.2 source winning.1.1).2 target controlled
  refine ⟨⟨targetActive, winning.1.2⟩, ?_⟩
  intro tail bad
  exact winning.2 (tail.prepend controlled)
    (tail.prepend_badOddDominant controlled bad)

/-- Winning propagates along every finite controlled path. -/
theorem Strategy.ParityWinning.of_reachable
    {State : Type uState} {game : Game State} {strategy : Strategy State}
    {root state : State} (winning : strategy.ParityWinning game root)
    (reachable : strategy.Reachable game root state) :
    strategy.ParityWinning game state := by
  induction reachable with
  | refl => exact winning
  | @tail source target _ controlled sourceWinning =>
      exact sourceWinning.of_controlledEdge controlled

/-- Read a nonempty finite loop forever. -/
private def periodicGet {α : Type*} (loop : List α) (nonempty : loop ≠ [])
    (index : Nat) : α :=
  loop[index % loop.length]'(
    Nat.mod_lt _ (List.length_pos_of_ne_nil nonempty))

private theorem periodicGet_zero {α : Type*} (loop : List α)
    (nonempty : loop ≠ []) :
    periodicGet loop nonempty 0 = loop.head nonempty := by
  simp [periodicGet, List.head_eq_getElem]

/-- A finite chain with its head appended supplies every adjacent edge of its
infinite periodic reading, including the wraparound edge. -/
private theorem periodicGet_follows {α : Type*} {relation : α -> α -> Prop}
    (loop : List α) (nonempty : loop ≠ [])
    (chain : List.IsChain relation (loop ++ [loop.head nonempty]))
    (index : Nat) :
    relation (periodicGet loop nonempty index)
      (periodicGet loop nonempty (index + 1)) := by
  rw [List.isChain_iff_getElem] at chain
  let current := index % loop.length
  have lengthPos : 0 < loop.length := List.length_pos_of_ne_nil nonempty
  have currentLt : current < loop.length := Nat.mod_lt _ lengthPos
  by_cases nextLt : current + 1 < loop.length
  · have oneLt : 1 < loop.length := by omega
    have nextMod : (index + 1) % loop.length = current + 1 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt oneLt, Nat.mod_eq_of_lt nextLt]
    have link := chain current (by simp [currentLt])
    simpa only [periodicGet, current, nextMod,
      List.getElem_append_left currentLt,
      List.getElem_append_left nextLt] using link
  · have currentLast : current + 1 = loop.length := by omega
    have nextMod : (index + 1) % loop.length = 0 := by
      rw [Nat.add_mod]
      by_cases lengthOne : loop.length = 1
      · simp only [lengthOne, Nat.mod_one]
      · have oneLt : 1 < loop.length := by omega
        rw [Nat.mod_eq_of_lt oneLt, currentLast, Nat.mod_self]
    have link := chain current (by simp [currentLt])
    simpa only [periodicGet, current, nextMod,
      List.getElem_append_left currentLt, currentLast,
      List.getElem_append_right (le_refl loop.length), Nat.sub_self,
      List.getElem_cons_zero, List.head_eq_getElem] using link

/-- A first edge followed by a finite return path can be represented as a
nonempty loop whose appended head closes the chain. -/
private theorem exists_loopList {α : Type*} {relation : α -> α -> Prop}
    {source target : α} (first : relation source target)
    (returns : Relation.ReflTransGen relation target source) :
    ∃ (loop : List α) (nonempty : loop ≠ []),
      loop.head nonempty = source /\
        List.IsChain relation (loop ++ [loop.head nonempty]) := by
  obtain ⟨tail, pathChain, pathLast⟩ :=
    List.exists_isChain_cons_of_relationReflTransGen returns
  let path := target :: tail
  have pathNonempty : path ≠ [] := List.cons_ne_nil _ _
  have pathLast' : path.getLast pathNonempty = source := pathLast
  let loop := source :: path.dropLast
  have loopNonempty : loop ≠ [] := List.cons_ne_nil _ _
  refine ⟨loop, loopNonempty, rfl, ?_⟩
  have restored : path.dropLast ++ [source] = path := by
    calc
      path.dropLast ++ [source] =
          path.dropLast ++ [path.getLast pathNonempty] := by rw [pathLast']
      _ = path := List.dropLast_append_getLast pathNonempty
  have cycleChain : List.IsChain relation (source :: path) :=
    List.IsChain.cons_cons first pathChain
  simpa [loop, List.cons_append, restored] using cycleChain

/-- Periodically repeat a finite threshold-bounded controlled loop. -/
private def periodicThresholdPlay
    {State : Type uState} [Fintype State]
    {game : Game State} {strategy : Strategy State}
    {threshold : game.Threshold} {source : State}
    (loop : List State) (nonempty : loop ≠ [])
    (head : loop.head nonempty = source)
    (chain : List.IsChain
      (ProgressMeasure.thresholdEdge game strategy threshold)
      (loop ++ [loop.head nonempty])) :
    Strategy.Play game strategy source where
  state := periodicGet loop nonempty
  starts := by simpa [head] using periodicGet_zero loop nonempty
  follows index := (periodicGet_follows loop nonempty chain index).2.1

/-- Repeating an odd-threshold loop is a concrete parity-losing play. -/
private theorem periodicThresholdPlay_badOddDominant
    {State : Type uState} [Fintype State]
    {game : Game State} {strategy : Strategy State}
    {threshold : game.Threshold} {source : State}
    (odd : Odd threshold.val)
    (sourcePriority : game.priority source = threshold.val)
    (loop : List State) (nonempty : loop ≠ [])
    (head : loop.head nonempty = source)
    (chain : List.IsChain
      (ProgressMeasure.thresholdEdge game strategy threshold)
      (loop ++ [loop.head nonempty])) :
    Strategy.BadOddDominant game
      (periodicThresholdPlay loop nonempty head chain).state := by
  refine ⟨threshold.val, odd, ?_, 0, ?_⟩
  · have multiplesInfinite :
        Set.Infinite (Set.range (fun index : Nat => loop.length * index)) :=
      Set.infinite_range_of_injective (by
        intro first second equal
        exact Nat.mul_left_cancel (List.length_pos_of_ne_nil nonempty) equal)
    apply multiplesInfinite.mono
    rintro index ⟨factor, rfl⟩
    have atSource :
        (periodicThresholdPlay loop nonempty head chain).state
            (loop.length * factor) = source := by
      change periodicGet loop nonempty (loop.length * factor) = source
      calc
        periodicGet loop nonempty (loop.length * factor) =
            periodicGet loop nonempty 0 := by
          simp [periodicGet]
        _ = loop.head nonempty := periodicGet_zero loop nonempty
        _ = source := head
    change game.priority
      ((periodicThresholdPlay loop nonempty head chain).state
        (loop.length * factor)) = threshold.val
    rw [atSource]
    exact sourcePriority
  · intro index _
    exact (periodicGet_follows loop nonempty chain index).2.2.1

/-- Every winning strategy generates at least one legal infinite play. -/
theorem Strategy.ParityWinning.playNonempty
    {State : Type uState} {game : Game State} {strategy : Strategy State}
    {root : State} (winning : strategy.ParityWinning game root) :
    Nonempty (Strategy.Play game strategy root) :=
  ⟨Strategy.Play.ofLocallyValid winning.1⟩

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
  refine ⟨valid.1, ?_⟩
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

/-- A root-winning strategy has no odd-threshold return after its active
bitmap is restricted to the root-reachable controlled cone.  Otherwise the
return path can be repeated into a concrete odd-dominant play from the
reachable source. -/
theorem noOddThresholdReturn_reachableRestriction
    {game : Game State} {strategy : Strategy State} {root : State}
    (winning : strategy.ParityWinning game root) :
    NoOddThresholdReturn game
      (strategy.reachableRestriction game root) := by
  classical
  intro threshold odd source target sourceActive controlled
    sourcePriority targetBelow returns
  have sourceReachable : strategy.Reachable game root source :=
    (Strategy.reachableRestriction_active_eq_true_iff
      game strategy root source).1 sourceActive
  have sourceWinning : strategy.ParityWinning game source :=
    winning.of_reachable sourceReachable
  have firstThreshold : thresholdEdge game
      (strategy.reachableRestriction game root) threshold source target :=
    ⟨sourceActive, controlled, sourcePriority.le, targetBelow⟩
  obtain ⟨loop, nonempty, head, chain⟩ :=
    exists_loopList firstThreshold returns
  let restrictedPlay : Strategy.Play game
      (strategy.reachableRestriction game root) source :=
    periodicThresholdPlay loop nonempty head chain
  have restrictedBad : Strategy.BadOddDominant game restrictedPlay.state :=
    periodicThresholdPlay_badOddDominant odd sourcePriority
      loop nonempty head chain
  let originalPlay : Strategy.Play game strategy source :=
    { state := restrictedPlay.state
      starts := restrictedPlay.starts
      follows := fun index =>
        (Strategy.reachableRestriction_controlledEdge_iff
          game strategy root (restrictedPlay.state index)
          (restrictedPlay.state (index + 1))).1
            (restrictedPlay.follows index) }
  have originalBad : Strategy.BadOddDominant game originalPlay.state := by
    exact restrictedBad
  exact sourceWinning.2 originalPlay originalBad

/-- Every root-winning finite strategy therefore has a generated accepted
certificate after canonical restriction to the part of the strategy that can
actually be played from the root. -/
theorem exists_valid_reachableRestriction_of_parityWinning
    {game : Game State} {strategy : Strategy State} {root : State}
    (winning : strategy.ParityWinning game root) :
    ∃ measure : ProgressMeasure game,
      measure.Valid game (strategy.reachableRestriction game root) root :=
  exists_valid_of_noOddThresholdReturn game
    (strategy.reachableRestriction game root) root
    (Strategy.reachableRestriction_locallyValid winning.1)
    (noOddThresholdReturn_reachableRestriction winning)

/-- The executable parity measure checker, packaged at the common checker
interface. -/
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

/-- The positive fixture also satisfies the graph condition directly: its
odd vertex exits above the odd threshold, so there is no below-threshold
return path. -/
theorem goodStrategy_noOddThresholdReturn :
    ProgressMeasure.NoOddThresholdReturn goodGame goodStrategy := by
  intro threshold odd source target _sourceActive controlled
    sourceAtThreshold targetBelow _returns
  cases source with
  | false =>
      cases target with
      | false =>
          simp [goodGame, goodStrategy, Strategy.ControlledEdge] at controlled
      | true =>
          simp [goodGame] at sourceAtThreshold targetBelow
          omega
  | true =>
      cases target with
      | false =>
          simp [goodGame] at sourceAtThreshold
          obtain ⟨half, halfEquation⟩ := odd
          omega
      | true =>
          simp [goodGame, goodStrategy, Strategy.ControlledEdge] at controlled

/-- The graph constructor synthesizes a valid certificate for the positive
fixture without choosing ranks by hand. -/
theorem goodStrategy_generatedCertificate :
    exists measure : ProgressMeasure goodGame,
      measure.Valid goodGame goodStrategy false := by
  apply ProgressMeasure.exists_valid_of_noOddThresholdReturn
  · constructor
    · rfl
    · intro source _sourceActive
      constructor
      · cases source with
        | false =>
            exact ⟨true, by
              simp [Strategy.ControlledEdge, goodGame, goodStrategy]⟩
        | true =>
            exact ⟨false, by
              simp [Strategy.ControlledEdge, goodGame, goodStrategy]⟩
      · intro _target _controlled
        rfl
  · exact goodStrategy_noOddThresholdReturn

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
  exact winning.2 oddLoopPlay oddLoop_bad

/-- The negative fixture violates the graph condition by its reflexive odd
return. -/
theorem oddLoop_not_noOddThresholdReturn :
    ¬ ProgressMeasure.NoOddThresholdReturn oddLoopGame oddLoopStrategy := by
  intro noReturn
  let threshold : oddLoopGame.Threshold := ⟨1, by
    simp [Game.maxPriority, oddLoopGame]⟩
  have forbidden := noReturn threshold (by
      change Odd 1
      exact ⟨0, rfl⟩)
    () () rfl
    (by simp [Strategy.ControlledEdge, oddLoopGame, oddLoopStrategy])
    (by simp [oddLoopGame, threshold])
    (by simp [oddLoopGame, threshold])
  exact forbidden Relation.ReflTransGen.refl

/-- A verifier cannot win by selecting a nonexistent move.  Before local
validity became part of `ParityWinning`, this stranded strategy satisfied the
path condition vacuously because it generated no controlled play. -/
def strandedGame : Game Unit where
  edge _ _ := false
  owner _ := .verifier
  priority _ := 0

def strandedStrategy : Strategy Unit where
  active _ := true
  next _ := ()

theorem strandedStrategy_not_winning :
    ¬ strandedStrategy.ParityWinning strandedGame () := by
  intro winning
  obtain ⟨target, controlled⟩ := winning.1.2 () rfl |>.1
  simp [Strategy.ControlledEdge, strandedGame] at controlled

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

/-! ### Reachable-cone normalization -/

/-- The `true` root is an even self-loop.  The disconnected `false` component
is an odd self-loop deliberately left active in the original strategy. -/
def splitGame : Game Bool where
  edge source target := decide (target = source)
  owner _ := .verifier
  priority state := if state then 0 else 1

def splitStrategy : Strategy Bool where
  active _ := true
  next := id

theorem splitStrategy_wins_from_true :
    splitStrategy.ParityWinning splitGame true := by
  constructor
  · constructor
    · rfl
    · intro source _
      constructor
      · exact ⟨source, by
          simp [Strategy.ControlledEdge, splitGame, splitStrategy]⟩
      · intro _ _
        rfl
  · intro play bad
    have constant : ∀ index, play.state index = true := by
      intro index
      induction index with
      | zero => exact play.starts
      | succ index inductionHypothesis =>
          have step := play.follows index
          simp [Strategy.ControlledEdge, splitGame, splitStrategy] at step
          exact step.trans inductionHypothesis
    rcases bad with ⟨priority, odd, recurring, _cutoff, _bounded⟩
    obtain ⟨index, member⟩ := recurring.nonempty
    have priorityZero : priority = 0 := by
      simpa [splitGame, constant index] using member.symm
    rw [priorityZero] at odd
    exact Nat.not_odd_zero odd

/-- The disconnected odd component prevents the unreduced active bitmap from
admitting a global certificate. -/
theorem splitStrategy_no_unrestricted_measure :
    ¬ ∃ measure : ProgressMeasure splitGame,
      measure.Valid splitGame splitStrategy true := by
  rintro ⟨measure, valid⟩
  let threshold : splitGame.Threshold := ⟨1, by
    simp [Game.maxPriority, splitGame]⟩
  have edgeValidity := valid.2 threshold (by
      change Odd 1
      exact ⟨0, rfl⟩)
    false rfl false
    (by simp [Strategy.ControlledEdge, splitGame, splitStrategy])
    (by simp [splitGame, threshold])
    (by simp [splitGame, threshold])
  have impossible := edgeValidity.2 (by simp [splitGame, threshold])
  exact (Nat.lt_irrefl _) impossible

/-- Reachable-cone normalization removes exactly the irrelevant odd component
and the generic constructor then produces an accepted certificate. -/
theorem splitStrategy_generated_reachableCertificate :
    ∃ measure : ProgressMeasure splitGame,
      measure.Valid splitGame
        (splitStrategy.reachableRestriction splitGame true) true :=
  ProgressMeasure.exists_valid_reachableRestriction_of_parityWinning
    splitStrategy_wins_from_true

/-- The positive and negative examples separate sound acceptance from a real
odd-dominant failure. -/
theorem parity_boundary_nontrivial :
    goodMeasure.check goodGame goodStrategy false = true /\
      goodStrategy.ParityWinning goodGame false /\
      (¬ oddLoopStrategy.ParityWinning oddLoopGame ()) /\
      (¬ strandedStrategy.ParityWinning strandedGame ()) /\
      forall measure : ProgressMeasure oddLoopGame,
        ¬ measure.Valid oddLoopGame oddLoopStrategy () :=
  ⟨goodCertificate, goodStrategy_wins, oddLoop_not_winning,
    strandedStrategy_not_winning, oddLoop_no_valid_measure⟩

end Canary

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity
