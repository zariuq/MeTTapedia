import Mettapedia.Machines.ScheduledRun.Core
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Finite cyclic replay certificates for actual scheduled runs

Replay stores the phase inside a candidate segment, not an unbounded turn.
One circuit reproduces the actual finite prefix exactly. A live return makes
its initial configuration a periodic point of this autonomous replay map.
Mathlib's periodic-point laws then put every replay position inside that
prefix. Only afterwards does a segment-local schedule licence identify replay
with the actual infinite future; confinement is proved, not assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

universe u
variable {S : Type u}

def ShiftCompatible (schedule : Schedule) (start period count : Nat) : Prop :=
  ∀ offset, schedule.pick (start + offset) count = schedule.pick (start + offset % period) count

def replayStep (next : S → List S) (schedule : Schedule) (start period : Nat)
    (positive : 0 < period) (configuration : Option S × Fin period) : Option S × Fin period :=
  (step next schedule (start + configuration.2.val) configuration.1,
    ⟨(configuration.2.val + 1) % period, Nat.mod_lt _ positive⟩)

def replayOrbit (next : S → List S) (schedule : Schedule) (start period : Nat)
    (positive : 0 < period) (initial : Option S) (offset : Nat) : Option S × Fin period :=
  (replayStep next schedule start period positive)^[offset] (initial, ⟨0, positive⟩)

theorem replay_succ (next : S → List S) (schedule : Schedule) (start period : Nat)
    (positive : 0 < period) (initial : Option S) (offset : Nat) :
    replayOrbit next schedule start period positive initial (offset + 1) =
      replayStep next schedule start period positive (replayOrbit next schedule start period positive initial offset) :=
  Function.iterate_succ_apply' _ _ _

theorem replay_phase (next : S → List S) (schedule : Schedule) (start period : Nat)
    (positive : 0 < period) (initial : Option S) (offset : Nat) :
    (replayOrbit next schedule start period positive initial offset).2.val = offset % period := by
  induction offset with
  | zero => simp [replayOrbit]
  | succ offset ih =>
    rw [replay_succ]
    change ((replayOrbit next schedule start period positive initial offset).2.val + 1) % period = _
    rw [ih, Nat.mod_add_mod]

theorem replay_prefix (next : S → List S) (schedule : Schedule) (initial : S)
    (start period : Nat) (positive : 0 < period) :
    ∀ offset, offset ≤ period →
      (replayOrbit next schedule start period positive (run next schedule initial start) offset).1 =
        run next schedule initial (start + offset) := by
  intro offset
  induction offset with
  | zero => intro _; simp [replayOrbit]
  | succ offset ih =>
    intro bound
    rw [replay_succ]
    change step next schedule
      (start + (replayOrbit next schedule start period positive (run next schedule initial start) offset).2.val)
      (replayOrbit next schedule start period positive (run next schedule initial start) offset).1 = _
    rw [replay_phase, Nat.mod_eq_of_lt (by omega : offset < period), ih (by omega)]
    rfl

theorem replay_periodic_point (next : S → List S) (schedule : Schedule) (initial : S)
    (start period : Nat) (positive : 0 < period)
    (returned : run next schedule initial (start + period) = run next schedule initial start) :
    Function.IsPeriodicPt (replayStep next schedule start period positive) period
      (run next schedule initial start, ⟨0, positive⟩) := by
  apply Prod.ext
  · exact (replay_prefix next schedule initial start period positive period le_rfl).trans returned
  · apply Fin.ext
    exact (replay_phase next schedule start period positive _ period).trans (Nat.mod_self period)

theorem replay_in_prefix (next : S → List S) (schedule : Schedule) (initial : S)
    (start period : Nat) (positive : 0 < period)
    (returned : run next schedule initial (start + period) = run next schedule initial start) (offset : Nat) :
    (replayOrbit next schedule start period positive (run next schedule initial start) offset).1 =
      run next schedule initial (start + offset % period) := by
  have periodic := replay_periodic_point next schedule initial start period positive returned
  have reduce := congrArg Prod.fst (periodic.iterate_mod_apply offset)
  exact reduce.symm.trans (replay_prefix next schedule initial start period positive _
    (Nat.le_of_lt (Nat.mod_lt offset positive)))

theorem actual_eq_replay (next : S → List S) (schedule : Schedule) (initial : S)
    (start period : Nat) (positive : 0 < period)
    (returned : run next schedule initial (start + period) = run next schedule initial start)
    (licensed : ∀ offset < period, ∀ state, run next schedule initial (start + offset) = some state →
      ShiftCompatible schedule start period (next state).length) :
    ∀ offset, run next schedule initial (start + offset) =
      (replayOrbit next schedule start period positive (run next schedule initial start) offset).1 := by
  intro offset
  induction offset with
  | zero => simp [replayOrbit]
  | succ offset ih =>
    rw [Nat.add_succ, run_succ, replay_succ]
    change step next schedule (start + offset) (run next schedule initial (start + offset)) =
      step next schedule
        (start + (replayOrbit next schedule start period positive (run next schedule initial start) offset).2.val)
        (replayOrbit next schedule start period positive (run next schedule initial start) offset).1
    rw [ih, replay_phase]
    apply step_eq_of_picks
    intro state present
    have inPrefix : run next schedule initial (start + offset % period) = some state :=
      (replay_in_prefix next schedule initial start period positive returned offset).symm.trans present
    exact licensed _ (Nat.mod_lt offset positive) state inPrefix offset

theorem return_periodic_of_shift_compatible (next : S → List S) (schedule : Schedule) (initial : S)
    (start period : Nat) (positive : 0 < period) (state : S)
    (present : run next schedule initial start = some state)
    (returned : run next schedule initial (start + period) = some state)
    (licensed : ∀ offset < period, ∀ value, run next schedule initial (start + offset) = some value →
      ShiftCompatible schedule start period (next value).length) :
    Nonterminating next schedule initial ∧ PeriodicFrom next schedule initial start period := by
  have back : run next schedule initial (start + period) = run next schedule initial start :=
    returned.trans present.symm
  have actual := actual_eq_replay next schedule initial start period positive back licensed
  have periodic := replay_periodic_point next schedule initial start period positive back
  constructor
  · apply nonterminating_of_tail next schedule initial start
    intro offset stopped
    have noneInPrefix : run next schedule initial (start + offset % period) = none :=
      (replay_in_prefix next schedule initial start period positive back offset).symm.trans
        ((actual offset).symm.trans stopped)
    exact present_before next schedule initial
      (Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt offset positive)) start)
      returned noneInPrefix
  · intro offset
    rw [show start + offset + period = start + (offset + period) by omega, actual, actual]
    apply congrArg Prod.fst
    exact (Function.iterate_add_apply _ offset period _).trans (congrArg
      ((replayStep next schedule start period positive)^[offset]) periodic.eq)

end Mettapedia.Machines.ScheduledRun
