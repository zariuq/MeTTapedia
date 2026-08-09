import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTCanaryAdmission
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# State identity for timing-dependent weighted-GSLT updates

A state key is adequate for a one-step observable only when equal keys force
equal next observables.  The shipped configuration key contains marking and
weights but omits both the timing trace and simulator clock.  The timing update
therefore distinguishes states that the key identifies.

Including every field repairs one-step key adequacy, but the real-valued clock
makes the repaired key space infinite.  Finite-dimensional state augmentation
thus restores Markov sufficiency without by itself restoring the finite-state
hypothesis required by finite model checking.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
namespace WeightedGSLTStateIdentity

/-- Equal keys must determine equal next observables. -/
def KeyAdequate {State Key Observable : Type*}
    (key : State → Key) (nextObservable : State → Observable) : Prop :=
  ∀ ⦃left right⦄, key left = key right →
    nextObservable left = nextObservable right

theorem keyAdequate_of_injective {State Key Observable : Type*}
    {key : State → Key} (hinjective : Function.Injective key)
    (nextObservable : State → Observable) :
    KeyAdequate key nextObservable := by
  intro left right hkey
  rw [hinjective hkey]

/-- Minimal timing state needed by the shipped update formula. -/
structure TimingState where
  marking : ℕ
  weight : ℝ
  lastFired : Option ℝ
  clock : ℝ

/-- The current implementation-level key shape: trace and clock are omitted. -/
def shippedTimingKey (state : TimingState) : ℕ × ℝ :=
  (state.marking, state.weight)

/-- Including the trace but still omitting the current clock. -/
def traceTimingKey (state : TimingState) : (ℕ × ℝ) × Option ℝ :=
  ((state.marking, state.weight), state.lastFired)

/-- A state-complete key. -/
def fullTimingKey (state : TimingState) : ((ℕ × ℝ) × Option ℝ) × ℝ :=
  (((state.marking, state.weight), state.lastFired), state.clock)

/-- The weight marginal of the shipped timing-dependent update. -/
noncomputable def timingNextWeight (eta tau ceiling : ℝ)
    (state : TimingState) : ℝ :=
  let bump := match state.lastFired with
    | none => eta
    | some firedAt => eta * Real.exp (-|state.clock - firedAt| / tau)
  min ceiling (state.weight + bump)

def plainTimingState : TimingState where
  marking := 1
  weight := 1
  lastFired := none
  clock := 1

def tracedTimingState : TimingState where
  marking := 1
  weight := 1
  lastFired := some 0
  clock := 1

theorem plain_traced_shippedKey_equal :
    shippedTimingKey plainTimingState = shippedTimingKey tracedTimingState := rfl

theorem exp_neg_one_lt_one : Real.exp (-1) < 1 := by
  rw [Real.exp_lt_one_iff]
  norm_num

theorem exp_neg_one_pos : 0 < Real.exp (-1) := Real.exp_pos _

theorem plain_timingNextWeight :
    timingNextWeight 1 1 10 plainTimingState = 2 := by
  norm_num [timingNextWeight, plainTimingState, min_def]

theorem traced_timingNextWeight :
    timingNextWeight 1 1 10 tracedTimingState = 1 + Real.exp (-1) := by
  rw [timingNextWeight]
  norm_num [tracedTimingState, abs_of_nonneg, min_eq_right]
  linarith [exp_neg_one_pos, exp_neg_one_lt_one]

theorem plain_traced_nextWeight_ne :
    timingNextWeight 1 1 10 plainTimingState ≠
      timingNextWeight 1 1 10 tracedTimingState := by
  rw [plain_timingNextWeight, traced_timingNextWeight]
  linarith [exp_neg_one_lt_one]

/-- Negative certificate: the shipped key is not sufficient for its timing
update's next weight. -/
theorem shippedTimingKey_not_adequate :
    ¬ KeyAdequate shippedTimingKey (timingNextWeight 1 1 10) := by
  intro hadequate
  exact plain_traced_nextWeight_ne
    (hadequate plain_traced_shippedKey_equal)

def earlyClockState : TimingState where
  marking := 1
  weight := 1
  lastFired := some 0
  clock := 1

def lateClockState : TimingState where
  marking := 1
  weight := 1
  lastFired := some 0
  clock := 2

theorem early_late_traceKey_equal :
    traceTimingKey earlyClockState = traceTimingKey lateClockState := rfl

theorem exp_neg_two_lt_exp_neg_one : Real.exp (-2) < Real.exp (-1) := by
  exact Real.exp_lt_exp.mpr (by norm_num)

theorem early_late_nextWeight_ne :
    timingNextWeight 1 1 10 earlyClockState ≠
      timingNextWeight 1 1 10 lateClockState := by
  simp only [timingNextWeight, earlyClockState, lateClockState]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 0)]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 - 0)]
  rw [min_eq_right, min_eq_right]
  · norm_num
  · linarith [Real.exp_pos (-2), exp_neg_two_lt_exp_neg_one,
      exp_neg_one_lt_one]
  · linarith [exp_neg_one_pos, exp_neg_one_lt_one]

/-- Trace alone is still insufficient when the update reads the clock. -/
theorem traceTimingKey_not_adequate :
    ¬ KeyAdequate traceTimingKey (timingNextWeight 1 1 10) := by
  intro hadequate
  exact early_late_nextWeight_ne (hadequate early_late_traceKey_equal)

theorem fullTimingKey_injective : Function.Injective fullTimingKey := by
  intro left right hkey
  cases left
  cases right
  simp only [fullTimingKey, Prod.mk.injEq] at hkey
  simp_all

/-- Positive repair: a state-complete key is adequate for the timing update. -/
theorem fullTimingKey_adequate :
    KeyAdequate fullTimingKey (timingNextWeight 1 1 10) :=
  keyAdequate_of_injective fullTimingKey_injective _

def clockFamily (clock : ℝ) : TimingState where
  marking := 1
  weight := 1
  lastFired := some 0
  clock := clock

theorem fullTimingKey_clockFamily_injective :
    Function.Injective (fun clock : ℝ => fullTimingKey (clockFamily clock)) := by
  intro left right hkey
  simpa [fullTimingKey, clockFamily] using hkey

/-- The repaired real-clock state space is infinite, despite having only
finitely many coordinates. -/
theorem fullTimingKey_range_infinite : Set.Infinite (Set.range fullTimingKey) := by
  have hfamily : Set.Infinite
      (Set.range (fun clock : ℝ => fullTimingKey (clockFamily clock))) :=
    Set.infinite_range_of_injective fullTimingKey_clockFamily_injective
  refine hfamily.mono ?_
  intro key hkey
  rcases hkey with ⟨clock, rfl⟩
  exact ⟨clockFamily clock, rfl⟩

#print axioms shippedTimingKey_not_adequate
#print axioms traceTimingKey_not_adequate
#print axioms fullTimingKey_adequate
#print axioms fullTimingKey_range_infinite

end WeightedGSLTStateIdentity
end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
