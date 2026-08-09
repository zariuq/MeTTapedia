import Mathlib.Data.List.Basic

/-!
# Collection pull/fold representation refinement

A finite collection may be represented either as a materialized list or as a
producer exposing one weak-head constructor at a time.  This module isolates
the representation law needed to consume such a producer without allocating
its intermediate spine.

The two sides are defined independently:

* `Produces` is a relational trace from producer states to an ordered list;
* `pullFold` is an executable, fuel-bounded consumer of producer steps; and
* `List.foldl` is the canonical materialized-list observation.

`pullFold_refines_foldl` proves equality of the executable and canonical
results whenever `Produces` supplies the complete trace.  Because the theorem
is equality over lists before folding, answer order and duplicate occurrences
are retained.  `pullFold_chunking_invariant` additionally proves that choosing
open one-item constructors or a flat terminal suffix is only a representation
choice.

This is not a native-runtime refinement theorem.  A native implementation must
still provide evidence that each admitted weak-head execution realizes a
`Produces` trace.  Nondeterministic, effectful, faulting, escaping, or otherwise
unobserved executions are outside this deterministic producer model and must
decline to the authoritative evaluator.
-/

namespace Mettapedia.Languages.MeTTa.CollectionPullFoldRefinement

universe u v w

/-- One observation of a deterministic finite producer.

`yield` exposes one demanded item and a continuation state.  `finish` exposes a
terminal flat suffix, including the empty suffix.  `decline` says that the
specialized representation cannot justify a semantic result. -/
inductive PullStep (Item : Type u) (State : Type v) where
  | yield (item : Item) (next : State)
  | finish (suffix : List Item)
  | decline
deriving Repr

/-- The externally visible result of the pull machine.  Partial accumulators
are absent by construction: a declined or fuel-exhausted attempt cannot publish
one. -/
inductive PullOutcome (Accumulator : Type w) where
  | commit (value : Accumulator)
  | decline
  | incomplete
deriving DecidableEq, Repr

/-- Consume an already materialized suffix in authored order. -/
def consumeAll
    (consume : Accumulator → Item → Option Accumulator) :
    Accumulator → List Item → Option Accumulator
  | accumulator, [] => some accumulator
  | accumulator, item :: rest =>
      match consume accumulator item with
      | none => none
      | some next => consumeAll consume next rest

/-- Execute a producer one weak-head step at a time.

Fuel bounds producer transitions, not items in a terminal flat suffix.  This
matches the representation boundary: `finish suffix` is one producer result,
and `consumeAll` observes every occurrence in that result. -/
def pullFold
    (step : State → PullStep Item State)
    (consume : Accumulator → Item → Option Accumulator) :
    Nat → State → Accumulator → PullOutcome Accumulator
  | 0, _, _ => .incomplete
  | fuel + 1, state, accumulator =>
      match step state with
      | .decline => .decline
      | .finish suffix =>
          match consumeAll consume accumulator suffix with
          | none => .decline
          | some result => .commit result
      | .yield item next =>
          match consume accumulator item with
          | none => .decline
          | some nextAccumulator =>
              pullFold step consume fuel next nextAccumulator

/-- Relational meaning of a complete producer trace.  The resulting list is
ordered and occurrence-sensitive; no quotient by permutation or idempotence is
taken. -/
inductive Produces
    (step : State → PullStep Item State) :
    State → List Item → Nat → Prop where
  | finish {state suffix}
      (observed : step state = .finish suffix) :
      Produces step state suffix 1
  | yield {state item next suffix transitions}
      (observed : step state = .yield item next)
      (tail : Produces step next suffix transitions) :
      Produces step state (item :: suffix) (Nat.succ transitions)

/-- Pulling a complete trace commits exactly the result of consuming its
ordered materialized list.  This theorem also covers consumers that may reject:
the successful `consumeAll` premise proves that no rejection occurred. -/
theorem pullFold_commit_of_produces
    (step : State → PullStep Item State)
    (consume : Accumulator → Item → Option Accumulator)
    {state : State} {items : List Item} {transitions : Nat}
    {accumulator result : Accumulator}
    (trace : Produces step state items transitions)
    (consumed : consumeAll consume accumulator items = some result) :
    pullFold step consume transitions state accumulator = .commit result := by
  induction trace generalizing accumulator result with
  | finish observed =>
      simp [pullFold, observed, consumed]
  | @yield state item next suffix transitions observed tail ih =>
      cases consumedItem : consume accumulator item with
      | none =>
          simp [consumeAll, consumedItem] at consumed
      | some nextAccumulator =>
          have consumedTail :
              consumeAll consume nextAccumulator suffix = some result := by
            simpa [consumeAll, consumedItem] using consumed
          simpa [pullFold, observed, consumedItem] using
            ih consumedTail

/-- Lift an ordinary total fold algebra into the rejecting-consumer interface. -/
def totalConsumer
    (combine : Accumulator → Item → Accumulator) :
    Accumulator → Item → Option Accumulator :=
  fun accumulator item => some (combine accumulator item)

@[simp] theorem consumeAll_total
    (combine : Accumulator → Item → Accumulator)
    (accumulator : Accumulator) (items : List Item) :
    consumeAll (totalConsumer combine) accumulator items =
      some (items.foldl combine accumulator) := by
  induction items generalizing accumulator with
  | nil => rfl
  | cons item rest ih =>
      simp [consumeAll, totalConsumer, ih]

/-- **Representation refinement.**  Pulling a complete deterministic producer
and folding each demanded item is exactly canonical folding of its materialized
ordered list. -/
theorem pullFold_refines_foldl
    (step : State → PullStep Item State)
    (combine : Accumulator → Item → Accumulator)
    {state : State} {items : List Item} {transitions : Nat}
    (trace : Produces step state items transitions)
    (accumulator : Accumulator) :
    pullFold step (totalConsumer combine) transitions state accumulator =
      .commit (items.foldl combine accumulator) := by
  exact pullFold_commit_of_produces step (totalConsumer combine) trace
    (consumeAll_total combine accumulator items)

/-- Producer chunking is unobservable: two producers denoting the same ordered
list have the same folded result even if one yields open constructors and the
other finishes with a flat suffix. -/
theorem pullFold_chunking_invariant
    (leftStep : LeftState → PullStep Item LeftState)
    (rightStep : RightState → PullStep Item RightState)
    (combine : Accumulator → Item → Accumulator)
    {leftState : LeftState} {rightState : RightState}
    {items : List Item} {leftTransitions rightTransitions : Nat}
    (leftTrace : Produces leftStep leftState items leftTransitions)
    (rightTrace : Produces rightStep rightState items rightTransitions)
    (accumulator : Accumulator) :
    pullFold leftStep (totalConsumer combine) leftTransitions
        leftState accumulator =
      pullFold rightStep (totalConsumer combine) rightTransitions
        rightState accumulator := by
  rw [pullFold_refines_foldl leftStep combine leftTrace accumulator]
  rw [pullFold_refines_foldl rightStep combine rightTrace accumulator]

/-! ## Cardinality consumer -/

/-- Cardinality is one fold algebra; it does not require a counted collection
representation in the producer. -/
def countItem (count : Nat) (_item : Item) : Nat := count + 1

theorem foldl_countItem
    (items : List Item) (initial : Nat) :
    items.foldl (countItem (Item := Item)) initial =
      initial + items.length := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
      simp only [List.foldl_cons, countItem, ih, List.length_cons]
      ac_rfl

/-- The length specialization computes the cardinality of the exact ordered
producer trace without materializing its spine. -/
theorem pullFold_refines_length
    (step : State → PullStep Item State)
    {state : State} {items : List Item} {transitions : Nat}
    (trace : Produces step state items transitions) :
    pullFold step (totalConsumer (countItem (Item := Item))) transitions
        state 0 = .commit items.length := by
  calc
    pullFold step (totalConsumer (countItem (Item := Item))) transitions
        state 0 =
        .commit (items.foldl (countItem (Item := Item)) 0) :=
      pullFold_refines_foldl step (countItem (Item := Item)) trace 0
    _ = .commit items.length := by simp [foldl_countItem]

/-- A finite-width cardinality consumer.  At the representable boundary it
declines instead of wrapping, so canonical evaluation remains authoritative. -/
def boundedCountItem
    (limit count : Nat) (_item : Item) : Option Nat :=
  if count < limit then some (count + 1) else none

theorem consumeAll_boundedCountItem_of_fits
    (limit initial : Nat) (items : List Item)
    (fits : initial + items.length ≤ limit) :
    consumeAll (boundedCountItem (Item := Item) limit) initial items =
      some (initial + items.length) := by
  induction items generalizing initial with
  | nil => simp [consumeAll]
  | cons item rest ih =>
      simp only [List.length_cons] at fits ⊢
      have below : initial < limit :=
        Nat.lt_of_lt_of_le
          (Nat.lt_add_of_pos_right (Nat.succ_pos rest.length)) fits
      have tailFits : initial + 1 + rest.length ≤ limit := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fits
      simpa [consumeAll, boundedCountItem, below,
        ih (initial + 1) tailFits, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-- Successful bounded cardinality pulling agrees with materialized length. -/
theorem pullFold_refines_bounded_length
    (step : State → PullStep Item State)
    (limit : Nat)
    {state : State} {items : List Item} {transitions : Nat}
    (trace : Produces step state items transitions)
    (fits : items.length ≤ limit) :
    pullFold step (boundedCountItem (Item := Item) limit) transitions
        state 0 = .commit items.length := by
  have consumed :
      consumeAll (boundedCountItem (Item := Item) limit) 0 items =
        some items.length := by
    simpa using
      (consumeAll_boundedCountItem_of_fits
        (Item := Item) limit 0 items (by simpa using fits))
  exact pullFold_commit_of_produces step
    (boundedCountItem (Item := Item) limit) trace consumed

/-- At the finite-width boundary, counting declines rather than wrapping. -/
theorem boundedCountItem_rejects_at_limit
    (limit : Nat) (item : Item) :
    boundedCountItem limit limit item = none := by
  simp [boundedCountItem]

/-! ## Decline is transactional -/

/-- Resolve a specialized attempt at the authoritative boundary.  A decline
discards all private work and selects the canonical result; fuel exhaustion is
not a semantic result. -/
def resolveWithCanonical
    (canonical : Accumulator) : PullOutcome Accumulator → Option Accumulator
  | .commit result => some result
  | .decline => some canonical
  | .incomplete => none

theorem pullFold_declines_on_step_decline
    (step : State → PullStep Item State)
    (consume : Accumulator → Item → Option Accumulator)
    {state : State} {accumulator : Accumulator} {fuel : Nat}
    (declines : step state = .decline) :
    pullFold step consume (fuel + 1) state accumulator = .decline := by
  simp [pullFold, declines]

theorem pullFold_declines_on_consumer_failure
    (step : State → PullStep Item State)
    (consume : Accumulator → Item → Option Accumulator)
    {state next : State} {item : Item} {accumulator : Accumulator}
    {fuel : Nat}
    (yields : step state = .yield item next)
    (rejects : consume accumulator item = none) :
    pullFold step consume (fuel + 1) state accumulator = .decline := by
  simp [pullFold, yields, rejects]

theorem decline_uses_canonical_result
    (canonical : Accumulator) :
    resolveWithCanonical canonical (.decline : PullOutcome Accumulator) =
      some canonical := by
  rfl

/-- A successful specialized execution resolves to the same canonical fold;
the fallback wrapper does not weaken the refinement statement. -/
theorem resolved_pull_refines_canonical_fold
    (step : State → PullStep Item State)
    (combine : Accumulator → Item → Accumulator)
    {state : State} {items : List Item} {transitions : Nat}
    (trace : Produces step state items transitions)
    (accumulator : Accumulator) :
    resolveWithCanonical (items.foldl combine accumulator)
        (pullFold step (totalConsumer combine) transitions state accumulator) =
      some (items.foldl combine accumulator) := by
  rw [pullFold_refines_foldl step combine trace accumulator]
  rfl

/-- The incorrect alternative, included only to state the negative boundary:
publishing the private accumulator on decline exposes representation-dependent
partial work. -/
def exposePartialOnDecline
    (partialAccumulator _canonical : Accumulator) :
    PullOutcome Accumulator → Option Accumulator
  | .commit result => some result
  | .decline => some partialAccumulator
  | .incomplete => none

/-- **Negative discriminator.**  Exposing a partially consumed accumulator on
decline differs from authoritative fallback. -/
theorem exposing_partial_accumulator_changes_result :
    resolveWithCanonical 2 (.decline : PullOutcome Nat) ≠
      exposePartialOnDecline 1 2 (.decline : PullOutcome Nat) := by
  decide

/-! ## Exact-order and multiplicity discriminators -/

/-- A non-commutative consumer that records the exact encounter sequence. -/
def recordItem (seen : List Item) (item : Item) : List Item :=
  seen ++ [item]

theorem foldl_recordItem (seed items : List Item) :
    items.foldl (recordItem (Item := Item)) seed = seed ++ items := by
  induction items generalizing seed with
  | nil => simp
  | cons item rest ih =>
      simp [recordItem, ih, List.append_assoc]

/-- Pull execution exposes items in exactly the producer trace order. -/
theorem pullFold_preserves_order_and_multiplicity
    (step : State → PullStep Item State)
    {state : State} {items : List Item} {transitions : Nat}
    (trace : Produces step state items transitions) :
    pullFold step (totalConsumer (recordItem (Item := Item))) transitions
        state [] = .commit items := by
  calc
    pullFold step (totalConsumer (recordItem (Item := Item))) transitions
        state [] =
        .commit (items.foldl (recordItem (Item := Item)) []) :=
      pullFold_refines_foldl step (recordItem (Item := Item)) trace []
    _ = .commit items := by simp [foldl_recordItem]

/-- **Negative discriminator.**  Reversing two distinct occurrences changes a
non-commutative observation. -/
theorem reversing_items_changes_observation :
    ([1, 2] : List Nat).foldl (recordItem (Item := Nat)) [] ≠
      ([2, 1] : List Nat).foldl (recordItem (Item := Nat)) [] := by
  decide

/-- **Negative discriminator.**  Collapsing equal-looking occurrences changes
cardinality; multiplicity is not set membership. -/
theorem dropping_duplicate_changes_cardinality :
    ([7, 7] : List Nat).foldl (countItem (Item := Nat)) 0 ≠
      ([7] : List Nat).foldl (countItem (Item := Nat)) 0 := by
  decide

/-! ## Executable mixed-representation fixture -/

inductive DemoState where
  | open
  | flat
deriving DecidableEq, Repr

/-- One open constructor followed by a terminal flat suffix. -/
def demoStep : DemoState → PullStep Nat DemoState
  | .open => .yield 5 .flat
  | .flat => .finish [4, 3, 2]

theorem demoProduces :
    Produces demoStep .open [5, 4, 3, 2] 2 := by
  exact Produces.yield rfl (Produces.finish rfl)

theorem demoPullCount :
    pullFold demoStep (totalConsumer (countItem (Item := Nat))) 2
        .open 0 = .commit 4 := by
  exact pullFold_refines_length demoStep demoProduces

theorem demoPullSequence :
    pullFold demoStep (totalConsumer (recordItem (Item := Nat))) 2
        .open [] = .commit [5, 4, 3, 2] := by
  exact pullFold_preserves_order_and_multiplicity demoStep demoProduces

end Mettapedia.Languages.MeTTa.CollectionPullFoldRefinement
