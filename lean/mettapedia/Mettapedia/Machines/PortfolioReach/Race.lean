import Mettapedia.Machines.BoundedSearchPortfolio

/-!
# Two resumable strategies over one world, served in slices

A strategy keeps a private state and acts on a world it shares with the other
strategy. A slice gives one strategy a quantum of units; it stops early at an
outcome, and an outcome is published at once. After a publication nothing
moves. The first strategy is served before the second in every round.

`execute_follows` is the frame law: strategies that leave the world alone on
the states an invariant holds of run exactly as their world-free readings do.

The cost theorems hold for every sequence of quanta (`race_cases`): when the
first strategy has an outcome after `a` units, the race has spent at most
`2 * a - 1`; when the second has one after `b` units, at most `b` plus the
units the first was offered through the round of publication. With quanta
`q, 2 q, 4 q, ...` that is `3 * b + q - 2` (`doubling_second_cost`), which is
under `4 * b` only when `q ≤ b` (`doubling_under_four`,
`Controls.small_need_pays_first_quantum`); with equal quanta `q` it is
`2 * b + q` (`uniform_second_cost`).

A unit is one `step` of a strategy. It is a count of steps, not of time: a
step's own cost is whatever the strategy's step costs.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PortfolioReach

open Mettapedia.Machines.BoundedSearchPortfolio (Origin)

universe u v w

variable {W : Type u} {T : Type v} {U : Type w}

/-- A strategy acting on a common world: one `step` is one unit of work. -/
structure Actor (W : Type u) (T : Type v) where
  step : W → T → W × T
  ready : T → Bool

/-- A strategy that needs no world. -/
structure Resumable (T : Type v) where
  step : T → T
  ready : T → Bool

/-- A world-free strategy as an actor on any world, which it leaves alone. -/
def Resumable.actor (W : Type u) (strategy : Resumable T) : Actor W T where
  step world state := (world, strategy.step state)
  ready := strategy.ready

@[simp] theorem Resumable.actor_ready (W : Type u) (strategy : Resumable T) :
    (strategy.actor W).ready = strategy.ready := rfl

@[simp] theorem Resumable.actor_step (W : Type u) (strategy : Resumable T) (world : W)
    (state : T) : (strategy.actor W).step world state = (world, strategy.step state) := rfl

/-- Up to `quantum` units of one strategy. It stops at an outcome, and when
the world has halted. The units used come first. -/
def Actor.work (actor : Actor W T) (halted : W → Bool) : Nat → W → T → Nat × W × T
  | 0, world, state => (0, world, state)
  | quantum + 1, world, state =>
      if actor.ready state || halted world then (0, world, state)
      else
        let rest := actor.work halted quantum (actor.step world state).1 (actor.step world state).2
        (rest.1 + 1, rest.2)

/-- More units change nothing once the strategy has an outcome or the world
has halted. -/
theorem Actor.work_stable (actor : Actor W T) (halted : W → Bool) :
    ∀ (quantum extra : Nat) (world : W) (state : T),
      (actor.ready (actor.work halted quantum world state).2.2 ||
          halted (actor.work halted quantum world state).2.1) = true →
        actor.work halted (quantum + extra) world state = actor.work halted quantum world state
  | 0, extra, world, state, stopped => by
      cases extra with
      | zero => rfl
      | succ extra =>
          have here : (actor.ready state || halted world) = true := stopped
          simp only [Actor.work, here, if_true]
  | quantum + 1, extra, world, state, stopped => by
      rw [show quantum + 1 + extra = (quantum + extra) + 1 by omega]
      by_cases here : (actor.ready state || halted world) = true
      · simp only [Actor.work, here, if_true]
      · simp only [Actor.work, here] at stopped ⊢
        rw [Actor.work_stable actor halted quantum extra _ _ stopped]

/-- The units a world-free slice uses: up to the first outcome. -/
def Resumable.used (strategy : Resumable T) : Nat → T → Nat
  | 0, _ => 0
  | quantum + 1, state =>
      if strategy.ready state then 0 else strategy.used quantum (strategy.step state) + 1

theorem Resumable.work_eq (strategy : Resumable T) (world : W) :
    ∀ (quantum : Nat) (state : T),
      (strategy.actor W).work (fun _ => false) quantum world state =
        (strategy.used quantum state, world, strategy.step^[strategy.used quantum state] state)
  | 0, _ => rfl
  | quantum + 1, state => by
      by_cases outcome : strategy.ready state = true
      · simp [Actor.work, Resumable.used, Resumable.actor, outcome]
      · have waiting : strategy.ready state = false := by simpa using outcome
        have rest := Resumable.work_eq strategy world quantum (strategy.step state)
        simp only [Resumable.actor] at rest
        simp [Actor.work, Resumable.used, Resumable.actor, waiting, rest]

theorem Resumable.used_le (strategy : Resumable T) :
    ∀ (quantum : Nat) (state : T), strategy.used quantum state ≤ quantum
  | 0, _ => Nat.le_refl 0
  | quantum + 1, state => by
      unfold Resumable.used
      split
      · omega
      · have := Resumable.used_le strategy quantum (strategy.step state)
        omega

theorem Resumable.used_waiting (strategy : Resumable T) :
    ∀ (quantum : Nat) (state : T) (unit : Nat), unit < strategy.used quantum state →
      strategy.ready (strategy.step^[unit] state) = false
  | 0, _, unit, small => by simp [Resumable.used] at small
  | quantum + 1, state, unit, small => by
      unfold Resumable.used at small
      split at small
      · omega
      · rename_i waiting
        cases unit with
        | zero => simpa using waiting
        | succ unit =>
            rw [Function.iterate_succ_apply]
            exact Resumable.used_waiting strategy quantum (strategy.step state) unit (by omega)

theorem Resumable.used_ready (strategy : Resumable T) :
    ∀ (quantum : Nat) (state : T), strategy.used quantum state < quantum →
      strategy.ready (strategy.step^[strategy.used quantum state] state) = true
  | 0, _, small => by simp [Resumable.used] at small
  | quantum + 1, state, small => by
      unfold Resumable.used at small ⊢
      split
      · rename_i outcome
        simpa using outcome
      · rename_i waiting
        rw [if_neg waiting] at small
        rw [Function.iterate_succ_apply]
        exact Resumable.used_ready strategy quantum (strategy.step state) (by omega)

/-- What one slice does to a strategy that has run `offered` units from
`start` without an outcome. -/
theorem Resumable.slice_spec (strategy : Resumable T) (start : T) (offered quantum : Nat)
    (waiting : ∀ unit, unit < offered → strategy.ready (strategy.step^[unit] start) = false) :
    strategy.step^[strategy.used quantum (strategy.step^[offered] start)]
        (strategy.step^[offered] start) =
      strategy.step^[offered + strategy.used quantum (strategy.step^[offered] start)] start ∧
    (∀ unit, unit < offered + strategy.used quantum (strategy.step^[offered] start) →
      strategy.ready (strategy.step^[unit] start) = false) ∧
    (strategy.used quantum (strategy.step^[offered] start) < quantum →
      strategy.ready
        (strategy.step^[offered + strategy.used quantum (strategy.step^[offered] start)] start) =
          true) := by
  have joined : ∀ unit, strategy.step^[unit] (strategy.step^[offered] start) =
      strategy.step^[offered + unit] start := by
    intro unit
    rw [Nat.add_comm, Function.iterate_add_apply]
  refine ⟨joined _, ?_, ?_⟩
  · intro unit small
    by_cases before : unit < offered
    · exact waiting unit before
    · have inside := strategy.used_waiting quantum (strategy.step^[offered] start)
        (unit - offered) (by omega)
      rw [joined] at inside
      rwa [show offered + (unit - offered) = unit by omega] at inside
  · intro early
    have outcome := strategy.used_ready quantum (strategy.step^[offered] start) early
    rwa [joined] at outcome

/-- Two strategies, the world they share, the units spent and who published. -/
structure Duo (W : Type u) (T : Type v) (U : Type w) where
  world : W
  first : T
  second : U
  spent : Nat
  published : Option Origin

/-- One slice. Nothing moves after a publication or in a halted world; an
outcome reached in a world that has not halted is published at once. -/
def serve (x : Actor W T) (y : Actor W U) (halted : W → Bool) (slice : Origin × Nat)
    (duo : Duo W T U) : Duo W T U :=
  if duo.published.isSome || halted duo.world then duo
  else
    match slice.1 with
    | .left =>
        let worked := x.work halted slice.2 duo.world duo.first
        { world := worked.2.1, first := worked.2.2, second := duo.second,
          spent := duo.spent + worked.1,
          published := if x.ready worked.2.2 && !halted worked.2.1 then some .left else none }
    | .right =>
        let worked := y.work halted slice.2 duo.world duo.second
        { world := worked.2.1, first := duo.first, second := worked.2.2,
          spent := duo.spent + worked.1,
          published := if y.ready worked.2.2 && !halted worked.2.1 then some .right else none }

def execute (x : Actor W T) (y : Actor W U) (halted : W → Bool) :
    List (Origin × Nat) → Duo W T U → Duo W T U
  | [], duo => duo
  | slice :: rest, duo => execute x y halted rest (serve x y halted slice duo)

theorem execute_append (x : Actor W T) (y : Actor W U) (halted : W → Bool)
    (first second : List (Origin × Nat)) (duo : Duo W T U) :
    execute x y halted (first ++ second) duo =
      execute x y halted second (execute x y halted first duo) := by
  induction first generalizing duo with
  | nil => rfl
  | cons slice rest ih => exact ih (serve x y halted slice duo)

theorem serve_published (x : Actor W T) (y : Actor W U) (halted : W → Bool)
    (slice : Origin × Nat) (duo : Duo W T U) (committed : duo.published.isSome = true) :
    serve x y halted slice duo = duo := by
  simp [serve, committed]

/-- A publication freezes both strategies, the world and the account. -/
theorem execute_published (x : Actor W T) (y : Actor W U) (halted : W → Bool)
    (slices : List (Origin × Nat)) (duo : Duo W T U) (committed : duo.published.isSome = true) :
    execute x y halted slices duo = duo := by
  induction slices with
  | nil => rfl
  | cons slice rest ih => rw [execute, serve_published x y halted slice duo committed, ih]

/-- Whoever published has an outcome, in a world that has not halted. -/
def Duo.Settled (x : Actor W T) (y : Actor W U) (halted : W → Bool) (duo : Duo W T U) : Prop :=
  (duo.published = some .left → x.ready duo.first = true ∧ halted duo.world = false) ∧
    (duo.published = some .right → y.ready duo.second = true ∧ halted duo.world = false)

theorem serve_settled (x : Actor W T) (y : Actor W U) (halted : W → Bool)
    (slice : Origin × Nat) (duo : Duo W T U) (settled : duo.Settled x y halted) :
    (serve x y halted slice duo).Settled x y halted := by
  unfold serve
  split
  · exact settled
  · rcases slice with ⟨origin, quantum⟩
    cases origin with
    | left =>
        refine ⟨?_, ?_⟩
        · intro published
          dsimp only at published ⊢
          split at published
          · rename_i outcome
            simpa using outcome
          · cases published
        · intro published
          dsimp only at published
          split at published <;> cases published
    | right =>
        refine ⟨?_, ?_⟩
        · intro published
          dsimp only at published
          split at published <;> cases published
        · intro published
          dsimp only at published ⊢
          split at published
          · rename_i outcome
            simpa using outcome
          · cases published

theorem execute_settled (x : Actor W T) (y : Actor W U) (halted : W → Bool)
    (slices : List (Origin × Nat)) (duo : Duo W T U) (settled : duo.Settled x y halted) :
    (execute x y halted slices duo).Settled x y halted := by
  induction slices generalizing duo with
  | nil => exact settled
  | cons slice rest ih => exact ih _ (serve_settled x y halted slice duo settled)

/-! ## The frame law -/

/-- On the states `Inv` holds of, the actor leaves `world` alone and moves as
`pure` does, and `Inv` is kept. -/
structure Actor.Follows (actor : Actor W T) (world : W) (pure : Resumable T)
    (Inv : T → Prop) : Prop where
  ready : ∀ state, actor.ready state = pure.ready state
  step : ∀ state, Inv state → pure.ready state = false →
    actor.step world state = (world, pure.step state)
  keeps : ∀ state, Inv state → pure.ready state = false → Inv (pure.step state)

theorem Actor.work_follows {actor : Actor W T} {world : W} {pure : Resumable T}
    {Inv : T → Prop} (follows : actor.Follows world pure Inv) {halted : W → Bool}
    (running : halted world = false) :
    ∀ (quantum : Nat) (state : T), Inv state →
      actor.work halted quantum world state =
          (pure.used quantum state, world, pure.step^[pure.used quantum state] state) ∧
        Inv (pure.step^[pure.used quantum state] state)
  | 0, _, holds => ⟨rfl, holds⟩
  | quantum + 1, state, holds => by
      by_cases outcome : pure.ready state = true
      · simp [Actor.work, Resumable.used, follows.ready, outcome, holds]
      · have waiting : pure.ready state = false := by simpa using outcome
        obtain ⟨rest, kept⟩ := Actor.work_follows follows running quantum (pure.step state)
          (follows.keeps state holds waiting)
        simp [Actor.work, Resumable.used, follows.ready, waiting, running,
          follows.step state holds waiting, rest, kept]

/-- **The frame law.** Strategies that leave the world alone on the states
their invariants hold of run, under every sequence of slices, exactly as their
world-free readings do: the world is the one they began in, and the
invariants still hold. -/
theorem execute_follows {x : Actor W T} {y : Actor W U} {world : W}
    {px : Resumable T} {py : Resumable U} {InvX : T → Prop} {InvY : U → Prop}
    (followsX : x.Follows world px InvX) (followsY : y.Follows world py InvY)
    {halted : W → Bool} (running : halted world = false) :
    ∀ (slices : List (Origin × Nat)) (duo : Duo W T U), duo.world = world →
      InvX duo.first → InvY duo.second →
      execute x y halted slices duo =
          execute (px.actor W) (py.actor W) (fun _ => false) slices duo ∧
        (execute x y halted slices duo).world = world ∧
        InvX (execute x y halted slices duo).first ∧
        InvY (execute x y halted slices duo).second
  | [], duo, same, holdsX, holdsY => ⟨rfl, same, holdsX, holdsY⟩
  | slice :: rest, duo, same, holdsX, holdsY => by
      rcases duo with ⟨held, first, second, spent, published⟩
      subst same
      rcases slice with ⟨origin, quantum⟩
      have one : serve x y halted (origin, quantum) ⟨held, first, second, spent, published⟩ =
            serve (px.actor W) (py.actor W) (fun _ => false) (origin, quantum)
              ⟨held, first, second, spent, published⟩ ∧
          (serve x y halted (origin, quantum) ⟨held, first, second, spent, published⟩).world =
            held ∧
          InvX (serve x y halted (origin, quantum) ⟨held, first, second, spent, published⟩).first ∧
          InvY (serve x y halted (origin, quantum)
            ⟨held, first, second, spent, published⟩).second := by
        cases committed : published with
        | some winner => simp [serve, holdsX, holdsY]
        | none =>
            cases origin with
            | left =>
                obtain ⟨worked, kept⟩ := Actor.work_follows followsX running quantum first holdsX
                simp [serve, running, worked, kept, holdsY, Resumable.work_eq,
                  followsX.ready]
            | right =>
                obtain ⟨worked, kept⟩ := Actor.work_follows followsY running quantum second holdsY
                simp [serve, running, worked, kept, holdsX, Resumable.work_eq,
                  followsY.ready]
      obtain ⟨equal, sameWorld, keptX, keptY⟩ := one
      have later := execute_follows followsX followsY running rest _ sameWorld keptX keptY
      simp only [execute]
      rw [← equal]
      exact later

/-! ## Rounds and their cost -/

/-- The slices of rounds `0` to `count - 1`: in each, the first strategy and
then the second are offered the round's quantum. -/
def rounds (quantum : Nat → Nat) : Nat → List (Origin × Nat)
  | 0 => []
  | count + 1 => rounds quantum count ++ [(.left, quantum count), (.right, quantum count)]

/-- The units each strategy has been offered before round `count`. -/
def allowance (quantum : Nat → Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => allowance quantum count + quantum count

theorem serve_left_pure (x : Resumable T) (y : Resumable U) (units : Nat) (duo : Duo W T U)
    (unpublished : duo.published = none) :
    serve (x.actor W) (y.actor W) (fun _ => false) (.left, units) duo =
      { world := duo.world, first := x.step^[x.used units duo.first] duo.first,
        second := duo.second, spent := duo.spent + x.used units duo.first,
        published :=
          if x.ready (x.step^[x.used units duo.first] duo.first) then some .left else none } := by
  simp [serve, unpublished, Resumable.work_eq]

theorem serve_right_pure (x : Resumable T) (y : Resumable U) (units : Nat) (duo : Duo W T U)
    (unpublished : duo.published = none) :
    serve (x.actor W) (y.actor W) (fun _ => false) (.right, units) duo =
      { world := duo.world, first := duo.first,
        second := y.step^[y.used units duo.second] duo.second,
        spent := duo.spent + y.used units duo.second,
        published :=
          if y.ready (y.step^[y.used units duo.second] duo.second) then some .right else none } := by
  simp [serve, unpublished, Resumable.work_eq]

section Race

variable (x : Resumable T) (y : Resumable U) (quantum : Nat → Nat) (world : W)
  (startFirst : T) (startSecond : U)

/-- The race after `count` rounds. -/
def race (count : Nat) : Duo W T U :=
  execute (x.actor W) (y.actor W) (fun _ => false) (rounds quantum count)
    ⟨world, startFirst, startSecond, 0, none⟩

/-- No round has published: both strategies have used every unit offered,
and neither had an outcome on the way. -/
structure Open (count : Nat) (duo : Duo W T U) : Prop where
  unpublished : duo.published = none
  sameWorld : duo.world = world
  first : duo.first = x.step^[allowance quantum count] startFirst
  second : duo.second = y.step^[allowance quantum count] startSecond
  spent : duo.spent = 2 * allowance quantum count
  firstWaiting : ∀ unit, unit < allowance quantum count →
    x.ready (x.step^[unit] startFirst) = false
  secondWaiting : ∀ unit, unit < allowance quantum count →
    y.ready (y.step^[unit] startSecond) = false
  firstNow : 0 < count → x.ready (x.step^[allowance quantum count] startFirst) = false
  secondNow : 0 < count → y.ready (y.step^[allowance quantum count] startSecond) = false

/-- A round has published, within the cost bounds: `round` is that round. -/
structure Closed (duo : Duo W T U) : Prop where
  published : duo.published.isSome = true
  firstCost : ∀ need, x.ready (x.step^[need] startFirst) = true → duo.spent ≤ 2 * need - 1
  secondCost : ∃ round, ∀ need, y.ready (y.step^[need] startSecond) = true →
    allowance quantum round ≤ need ∧ (0 < round → allowance quantum round < need) ∧
      duo.spent ≤ need + allowance quantum round + quantum round

theorem round_step (count : Nat) (duo : Duo W T U)
    (opened : Open x y quantum world startFirst startSecond count duo) :
    Open x y quantum world startFirst startSecond (count + 1)
        (serve (x.actor W) (y.actor W) (fun _ => false) (.right, quantum count)
          (serve (x.actor W) (y.actor W) (fun _ => false) (.left, quantum count) duo)) ∨
      Closed x y quantum startFirst startSecond
        (serve (x.actor W) (y.actor W) (fun _ => false) (.right, quantum count)
          (serve (x.actor W) (y.actor W) (fun _ => false) (.left, quantum count) duo)) := by
  obtain ⟨unpublished, sameWorld, first, second, spent, firstWaiting, secondWaiting,
    firstNow, secondNow⟩ := opened
  obtain ⟨joinX, waitX, readyX⟩ :=
    x.slice_spec startFirst (allowance quantum count) (quantum count) firstWaiting
  obtain ⟨joinY, waitY, readyY⟩ :=
    y.slice_spec startSecond (allowance quantum count) (quantum count) secondWaiting
  have leX := x.used_le (quantum count) (x.step^[allowance quantum count] startFirst)
  have leY := y.used_le (quantum count) (y.step^[allowance quantum count] startSecond)
  have firstFloor : ∀ need, x.ready (x.step^[need] startFirst) = true →
      allowance quantum count +
        x.used (quantum count) (x.step^[allowance quantum count] startFirst) ≤ need := by
    intro need outcome
    by_contra short
    have waiting := waitX need (by omega)
    rw [outcome] at waiting
    cases waiting
  have secondFloor : ∀ need, y.ready (y.step^[need] startSecond) = true →
      allowance quantum count +
        y.used (quantum count) (y.step^[allowance quantum count] startSecond) ≤ need := by
    intro need outcome
    by_contra short
    have waiting := waitY need (by omega)
    rw [outcome] at waiting
    cases waiting
  have secondStrict : ∀ need, y.ready (y.step^[need] startSecond) = true → 0 < count →
      allowance quantum count < need := by
    intro need outcome positive
    have floor := secondFloor need outcome
    by_contra short
    have same : need = allowance quantum count := by omega
    have waiting := secondNow positive
    rw [← same, outcome] at waiting
    cases waiting
  rw [serve_left_pure x y (quantum count) duo unpublished, first, joinX]
  by_cases outcomeX : x.ready (x.step^[allowance quantum count +
      x.used (quantum count) (x.step^[allowance quantum count] startFirst)] startFirst) = true
  · -- the first strategy publishes in this round
    rw [if_pos outcomeX, serve_published _ _ _ _ _ rfl]
    refine Or.inr ⟨rfl, ?_, count, ?_⟩
    · intro need outcome
      have floor := firstFloor need outcome
      show duo.spent + _ ≤ 2 * need - 1
      rw [spent]
      rcases Nat.eq_zero_or_pos
        (x.used (quantum count) (x.step^[allowance quantum count] startFirst)) with none | some
      · rcases Nat.eq_zero_or_pos count with zero | positive
        · subst zero
          simp only [allowance] at none ⊢
          omega
        · have waiting := firstNow positive
          rw [none, Nat.add_zero] at outcomeX
          rw [outcomeX] at waiting
          cases waiting
      · omega
    · intro need outcome
      have floor := secondFloor need outcome
      refine ⟨by omega, secondStrict need outcome, ?_⟩
      show duo.spent + _ ≤ _
      rw [spent]
      omega
  · -- the first strategy used its whole quantum without an outcome
    have waitingX : x.ready (x.step^[allowance quantum count +
        x.used (quantum count) (x.step^[allowance quantum count] startFirst)] startFirst) =
          false := by simpa using outcomeX
    have fullX : x.used (quantum count) (x.step^[allowance quantum count] startFirst) =
        quantum count := by
      by_contra short
      exact outcomeX (readyX (by omega))
    have firstLate : ∀ need, x.ready (x.step^[need] startFirst) = true →
        allowance quantum count + quantum count < need := by
      intro need outcome
      have floor := firstFloor need outcome
      by_contra short
      have same : need = allowance quantum count +
          x.used (quantum count) (x.step^[allowance quantum count] startFirst) := by omega
      rw [← same, outcome] at waitingX
      cases waitingX
    rw [if_neg outcomeX, serve_right_pure x y (quantum count) _ rfl]
    dsimp only
    rw [second, joinY]
    by_cases outcomeY : y.ready (y.step^[allowance quantum count +
        y.used (quantum count) (y.step^[allowance quantum count] startSecond)] startSecond) = true
    · -- the second strategy publishes in this round
      rw [if_pos outcomeY]
      refine Or.inr ⟨rfl, ?_, count, ?_⟩
      · intro need outcome
        have late := firstLate need outcome
        show duo.spent + _ + _ ≤ 2 * need - 1
        rw [spent]
        omega
      · intro need outcome
        have floor := secondFloor need outcome
        refine ⟨by omega, secondStrict need outcome, ?_⟩
        show duo.spent + _ + _ ≤ _
        rw [spent]
        omega
    · -- neither has an outcome: the next round begins
      have waitingY : y.ready (y.step^[allowance quantum count +
          y.used (quantum count) (y.step^[allowance quantum count] startSecond)] startSecond) =
            false := by simpa using outcomeY
      have fullY : y.used (quantum count) (y.step^[allowance quantum count] startSecond) =
          quantum count := by
        by_contra short
        exact outcomeY (readyY (by omega))
      rw [if_neg outcomeY]
      refine Or.inl ⟨rfl, sameWorld, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show x.step^[_] startFirst = x.step^[allowance quantum count + quantum count] startFirst
        rw [fullX]
      · show y.step^[_] startSecond = y.step^[allowance quantum count + quantum count] startSecond
        rw [fullY]
      · show duo.spent + _ + _ = 2 * (allowance quantum count + quantum count)
        rw [spent, fullX, fullY]
        omega
      · intro unit small
        exact waitX unit (by rw [fullX]; exact small)
      · intro unit small
        exact waitY unit (by rw [fullY]; exact small)
      · intro _
        show x.ready (x.step^[allowance quantum count + quantum count] startFirst) = false
        rw [← fullX]
        exact waitingX
      · intro _
        show y.ready (y.step^[allowance quantum count + quantum count] startSecond) = false
        rw [← fullY]
        exact waitingY

/-- After every number of rounds, either nothing is published and both
strategies have used all they were offered, or a round published within the
cost bounds. -/
theorem race_cases : ∀ count,
    Open x y quantum world startFirst startSecond count
        (race x y quantum world startFirst startSecond count) ∨
      Closed x y quantum startFirst startSecond
        (race x y quantum world startFirst startSecond count)
  | 0 => Or.inl
      { unpublished := rfl, sameWorld := rfl, first := rfl, second := rfl, spent := rfl
        firstWaiting := fun unit small => absurd small (Nat.not_lt_zero unit)
        secondWaiting := fun unit small => absurd small (Nat.not_lt_zero unit)
        firstNow := fun positive => absurd positive (Nat.lt_irrefl 0)
        secondNow := fun positive => absurd positive (Nat.lt_irrefl 0) }
  | count + 1 => by
      have unfolded : race x y quantum world startFirst startSecond (count + 1) =
          serve (x.actor W) (y.actor W) (fun _ => false) (.right, quantum count)
            (serve (x.actor W) (y.actor W) (fun _ => false) (.left, quantum count)
              (race x y quantum world startFirst startSecond count)) := by
        simp [race, rounds, execute_append, execute]
      rw [unfolded]
      rcases race_cases count with opened | closed
      · exact round_step x y quantum world startFirst startSecond count _ opened
      · rw [serve_published _ _ _ _ _ closed.published,
          serve_published _ _ _ _ _ closed.published]
        exact Or.inr closed

theorem allowance_ge (positive : ∀ round, 0 < quantum round) :
    ∀ count, count ≤ allowance quantum count
  | 0 => Nat.le_refl 0
  | count + 1 => by
      have earlier := allowance_ge positive count
      have here := positive count
      simp only [allowance]
      omega

/-- **A race with positive quanta publishes** once the first strategy has an
outcome within reach. -/
theorem race_publishes_first (positive : ∀ round, 0 < quantum round) {need : Nat}
    (outcome : x.ready (x.step^[need] startFirst) = true) :
    (race x y quantum world startFirst startSecond (need + 1)).published.isSome = true := by
  rcases race_cases x y quantum world startFirst startSecond (need + 1) with opened | closed
  · have waiting := opened.firstWaiting need
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self need) (allowance_ge quantum positive (need + 1)))
    rw [outcome] at waiting
    cases waiting
  · exact closed.published

/-- The same when the second strategy has an outcome within reach. -/
theorem race_publishes_second (positive : ∀ round, 0 < quantum round) {need : Nat}
    (outcome : y.ready (y.step^[need] startSecond) = true) :
    (race x y quantum world startFirst startSecond (need + 1)).published.isSome = true := by
  rcases race_cases x y quantum world startFirst startSecond (need + 1) with opened | closed
  · have waiting := opened.secondWaiting need
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self need) (allowance_ge quantum positive (need + 1)))
    rw [outcome] at waiting
    cases waiting
  · exact closed.published

theorem race_closed {count : Nat}
    (published : (race x y quantum world startFirst startSecond count).published.isSome = true) :
    Closed x y quantum startFirst startSecond
      (race x y quantum world startFirst startSecond count) := by
  rcases race_cases x y quantum world startFirst startSecond count with opened | closed
  · rw [opened.unpublished] at published
    cases published
  · exact closed

/-- **Cost against the first strategy, for every sequence of quanta.** A race
that has published has spent at most `2 * need - 1` units when the first
strategy has an outcome after `need` units. -/
theorem race_first_cost {count need : Nat}
    (published : (race x y quantum world startFirst startSecond count).published.isSome = true)
    (outcome : x.ready (x.step^[need] startFirst) = true) :
    (race x y quantum world startFirst startSecond count).spent ≤ 2 * need - 1 :=
  (race_closed x y quantum world startFirst startSecond published).firstCost need outcome

/-- The world is never touched by world-free strategies. -/
theorem race_world (count : Nat) :
    (race x y quantum world startFirst startSecond count).world = world := by
  have follows : ∀ (strategy : Resumable T), (strategy.actor W).Follows world strategy
      (fun _ => True) := fun strategy => ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => trivial⟩
  have followsSecond : (y.actor W).Follows world y (fun _ => True) :=
    ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => trivial⟩
  exact (execute_follows (follows x) followsSecond (halted := fun _ => false) rfl
    (rounds quantum count) ⟨world, startFirst, startSecond, 0, none⟩ rfl trivial trivial).2.1

end Race

/-! ## Doubling quanta and equal quanta -/

/-- Quanta `first, 2 * first, 4 * first, ...`. -/
def doubling (first : Nat) (round : Nat) : Nat := first * 2 ^ round

theorem doubling_succ (first round : Nat) :
    doubling first (round + 1) = 2 * doubling first round := by
  unfold doubling
  rw [pow_succ]
  ring

/-- A doubling round offers what all earlier rounds offered, and the first
quantum more. -/
theorem doubling_eq (first : Nat) :
    ∀ round, doubling first round = allowance (doubling first) round + first
  | 0 => by simp [doubling, allowance]
  | round + 1 => by
      have earlier := doubling_eq first round
      have next := doubling_succ first round
      simp only [allowance]
      omega

theorem doubling_pos {first : Nat} (positive : 0 < first) (round : Nat) :
    0 < doubling first round :=
  Nat.mul_pos positive (Nat.pos_of_ne_zero (by positivity))

/-- **Cost against the second strategy under doubling quanta.** When the
second strategy has an outcome after `need` units, a race that has published
has spent at most `3 * need + first`, and two units less when `need` is
positive. -/
theorem doubling_second_cost (x : Resumable T) (y : Resumable U) (first : Nat) (world : W)
    (startFirst : T) (startSecond : U) {count need : Nat}
    (published :
      (race x y (doubling first) world startFirst startSecond count).published.isSome = true)
    (outcome : y.ready (y.step^[need] startSecond) = true) :
    (race x y (doubling first) world startFirst startSecond count).spent ≤ 3 * need + first ∧
      (0 < need →
        (race x y (doubling first) world startFirst startSecond count).spent + 2 ≤
          3 * need + first) := by
  obtain ⟨round, bound⟩ :=
    (race_closed x y (doubling first) world startFirst startSecond published).secondCost
  obtain ⟨floor, strict, cost⟩ := bound need outcome
  have offered := doubling_eq first round
  rcases Nat.eq_zero_or_pos round with zero | positive
  · subst zero
    simp only [allowance] at floor cost offered
    constructor <;> intros <;> omega
  · have below := strict positive
    constructor <;> intros <;> omega

/-- **Under four times, from the first quantum on.** With doubling quanta, a
second strategy whose need is at least the first quantum is found for less
than four times its need. -/
theorem doubling_under_four (x : Resumable T) (y : Resumable U) (first : Nat) (world : W)
    (startFirst : T) (startSecond : U) {count need : Nat}
    (published :
      (race x y (doubling first) world startFirst startSecond count).published.isSome = true)
    (outcome : y.ready (y.step^[need] startSecond) = true) (large : first ≤ need)
    (positive : 0 < need) :
    (race x y (doubling first) world startFirst startSecond count).spent < 4 * need := by
  have cost := (doubling_second_cost x y first world startFirst startSecond published outcome).2
    positive
  omega

/-- **Cost against the second strategy under equal quanta.** -/
theorem uniform_second_cost (x : Resumable T) (y : Resumable U) (each : Nat) (world : W)
    (startFirst : T) (startSecond : U) {count need : Nat}
    (published :
      (race x y (fun _ => each) world startFirst startSecond count).published.isSome = true)
    (outcome : y.ready (y.step^[need] startSecond) = true) :
    (race x y (fun _ => each) world startFirst startSecond count).spent ≤ 2 * need + each := by
  obtain ⟨round, bound⟩ :=
    (race_closed x y (fun _ => each) world startFirst startSecond published).secondCost
  obtain ⟨floor, _, cost⟩ := bound need outcome
  omega

namespace Controls

/-- A strategy with an outcome after exactly `target` units. -/
def counter (target : Nat) : Resumable Nat where
  step count := count + 1
  ready count := decide (target ≤ count)

/-- A strategy that never has an outcome. -/
def endless : Resumable Nat where
  step count := count + 1
  ready _ := false

/-- A need below the first quantum pays the whole first quantum of the other
strategy: here `9` units for a need of `1`, more than four times the need. -/
theorem small_need_pays_first_quantum :
    (race endless (counter 1) (doubling 8) () 0 0 1).published = some .right ∧
      (race endless (counter 1) (doubling 8) () 0 0 1).spent = 9 ∧
      ¬ (race endless (counter 1) (doubling 8) () 0 0 1).spent < 4 * 1 := by decide

/-- The bound `3 * need + first - 2` is met: a need of `2` with first quantum
`1` costs `5`. -/
theorem doubling_bound_met :
    (race endless (counter 2) (doubling 1) () 0 0 2).published = some .right ∧
      (race endless (counter 2) (doubling 1) () 0 0 2).spent = 3 * 2 + 1 - 2 := by decide

/-- The first strategy's bound `2 * need - 1` is met: a need of `4` costs `7`. -/
theorem first_bound_met :
    (race (counter 4) endless (doubling 1) () 0 0 3).published = some .left ∧
      (race (counter 4) endless (doubling 1) () 0 0 3).spent = 2 * 4 - 1 := by decide

/-- Equal quanta cost less in the same case that meets the doubling bound, at
the price of more switches: `2 * need + each` against `3 * need + first - 2`. -/
theorem uniform_is_cheaper_here :
    (race endless (counter 6) (fun _ => 1) () 0 0 6).spent = 12 ∧
      (race endless (counter 6) (doubling 1) () 0 0 3).spent = 13 := by decide

/-- Neither strategy with an outcome: no round publishes, and every unit
offered is spent. -/
theorem nothing_to_find_spends_everything :
    (race endless endless (doubling 1) () 0 0 4).published = none ∧
      (race endless endless (doubling 1) () 0 0 4).spent = 2 * (1 + 2 + 4 + 8) := by decide

end Controls

#print axioms execute_follows
#print axioms race_cases
#print axioms race_publishes_first
#print axioms race_publishes_second
#print axioms race_first_cost
#print axioms doubling_second_cost
#print axioms doubling_under_four
#print axioms uniform_second_cost
#print axioms Controls.small_need_pays_first_quantum
#print axioms Controls.doubling_bound_met

end Mettapedia.Machines.PortfolioReach
