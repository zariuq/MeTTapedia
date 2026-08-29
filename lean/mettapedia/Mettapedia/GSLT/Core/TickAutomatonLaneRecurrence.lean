/-!
# Tick-automaton lane recurrence

A frontier selection discipline may be supplied as data: a deterministic
tick automaton whose current state names which end of the live occurrence
store is selected next.  The runtime admits such an automaton only after a
structural model check: the cycle reached from the start state must contain
an OLDEST-lane state.

This file proves what that check certifies, on the two shapes the runtime
actually constructs:

* a ratio automaton (a cyclic successor on `deep + 1` states whose final
  state is the OLDEST lane) selects the oldest lane again within every
  window of `deep + 1` ticks — the recurrence `always eventually oldest`,
  with an explicit bound; and
* the bare newest-only automaton never selects the oldest lane, so the
  check's rejection of it is not conservative but exact.

Neither theorem mentions a frontier.  They are about the discipline as
data, which is precisely what the runtime checks.  Connecting oldest-lane
recurrence to the selection of every persistent live occurrence is the
separate store-level duty already treated by the age-protected schedule
theory; the composition of the two is the named next lemma, not assumed
here.
-/

namespace Mettapedia.GSLT.Core.TickAutomatonLaneRecurrence

/-- Which end of the live occurrence store a state selects. -/
inductive Lane where
  | oldest
  | newest
deriving DecidableEq, Repr

/-- The ratio discipline's lane assignment on states `0..deep`: the first
`deep` states dive to the newest occurrence, the final state pays the age
lane. -/
def ratioLane (deep : Nat) (state : Nat) : Lane :=
  if state = deep then .oldest else .newest

/-- The ratio automaton's trajectory is cyclic-successor iteration. -/
def ratioTrajectory (deep start : Nat) (tick : Nat) : Nat :=
  (start + tick) % (deep + 1)

/-- The trajectory never leaves the state space. -/
theorem ratioTrajectory_lt (deep start tick : Nat) :
    ratioTrajectory deep start tick < deep + 1 :=
  Nat.mod_lt _ (Nat.succ_pos deep)

/-- **Always eventually oldest, with an explicit bound.**  From any tick,
the ratio automaton selects the oldest lane again within `deep` further
ticks.  This is the recurrence property the runtime's cycle check
certifies, stated as arithmetic rather than as a temporal formula. -/
theorem ratio_oldest_lane_recurs_within
    (deep start k : Nat) :
    ∃ j, k ≤ j ∧ j ≤ k + deep ∧
      ratioLane deep (ratioTrajectory deep start j) = .oldest := by
  have remainder_lt : (start + k) % (deep + 1) < deep + 1 :=
    Nat.mod_lt _ (Nat.succ_pos deep)
  refine ⟨k + (deep - (start + k) % (deep + 1)),
    Nat.le_add_right _ _, by omega, ?_⟩
  have decompose :
      (deep + 1) * ((start + k) / (deep + 1)) +
        (start + k) % (deep + 1) = start + k :=
    Nat.div_add_mod (start + k) (deep + 1)
  have landing :
      (start + (k + (deep - (start + k) % (deep + 1)))) %
        (deep + 1) = deep := by
    have rearrange :
        start + (k + (deep - (start + k) % (deep + 1))) =
          deep + (deep + 1) * ((start + k) / (deep + 1)) := by
      omega
    rw [rearrange, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (Nat.lt_succ_self deep)
  unfold ratioTrajectory ratioLane
  rw [landing]
  simp

/-- The FIFO instance: the zero-ratio automaton pays the age lane on every
tick. -/
theorem fifo_every_tick_selects_oldest_lane (start k : Nat) :
    ratioLane 0 (ratioTrajectory 0 start k) = .oldest := by
  unfold ratioTrajectory ratioLane
  simp [Nat.mod_one]

/-- **The negative witness is exact.**  The newest-only discipline — bare
LIFO as data — never selects the oldest lane, at any tick, from any start.
The runtime check's rejection of it is therefore not a conservative
approximation but the precise boundary. -/
def newestOnlyLane (_state : Nat) : Lane := .newest

theorem newest_only_never_oldest (trajectory : Nat → Nat) (tick : Nat) :
    newestOnlyLane (trajectory tick) = .newest := rfl

theorem newest_only_has_no_oldest_lane_tick (trajectory : Nat → Nat) :
    ¬ ∃ tick, newestOnlyLane (trajectory tick) = .oldest := by
  rintro ⟨tick, contradiction⟩
  simp [newestOnlyLane] at contradiction

/-- A singleton frontier is discipline-invariant: with one live occurrence
both lanes name the same index.  This is the data-level shadow of the
existing scheduler theorem that every lawful scheduler selects the sole
live occurrence. -/
def laneIndex (lane : Lane) (length : Nat) : Nat :=
  match lane with
  | .oldest => 0
  | .newest => length - 1

theorem singleton_frontier_lane_invariant (lane : Lane) :
    laneIndex lane 1 = 0 := by
  cases lane <;> rfl

/-- Runtime-style singleton selection is phase-transparent as well as
lane-invariant.  Deterministic stretches therefore cannot perturb the ratio
phase used at a later genuine choice. -/
def selectStep (next : Nat → Nat) (lane : Nat → Lane)
    (state length : Nat) : Nat × Nat :=
  if length = 0 then (state, 0)
  else if length = 1 then (state, 0)
  else (next state, laneIndex (lane state) length)

theorem singleton_frontier_state_invariant
    (next : Nat → Nat) (lane : Nat → Lane) (state : Nat) :
    selectStep next lane state 1 = (state, 0) := by
  simp [selectStep]

end Mettapedia.GSLT.Core.TickAutomatonLaneRecurrence

#print axioms
  Mettapedia.GSLT.Core.TickAutomatonLaneRecurrence.ratio_oldest_lane_recurs_within
#print axioms
  Mettapedia.GSLT.Core.TickAutomatonLaneRecurrence.fifo_every_tick_selects_oldest_lane
#print axioms
  Mettapedia.GSLT.Core.TickAutomatonLaneRecurrence.newest_only_has_no_oldest_lane_tick
#print axioms
  Mettapedia.GSLT.Core.TickAutomatonLaneRecurrence.singleton_frontier_lane_invariant
#print axioms
  Mettapedia.GSLT.Core.TickAutomatonLaneRecurrence.singleton_frontier_state_invariant
