import Mettapedia.UniversalAI.ReflectiveOracles.FixedPoints
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Probabilistic machines that call an oracle

A machine is given by its states and one step: it halts, possibly with an
output bit; or it moves on; or it flips a fair coin; or it asks the oracle
about a machine state and a threshold and continues according to the answer.
Nothing else is assumed, so every machine model that can be run one step at a
time is an instance: its states are the configurations.

The probability that a machine outputs a bit is defined by first-step
analysis, as in the existence proof of Fallenstein, Taylor and Christiano
(2015, Appendix B): `haltsWithin` gives the probability of halting with that
output within a number of steps, and `output` is the limit. The machine may
run forever, so the two output probabilities add up to at most one.

A query is a state together with a rational threshold, as in Definition 1 of
Leike, Taylor and Fallenstein (2016), where a query is a machine, an input and
a threshold; here the state stands for the machine started on its input.

## Main statements

* `output_halt`, `output_next`, `output_flip`, `output_ask`: the output
  probability satisfies the first-step equations.
* `continuous_haltsWithin`, `lowerSemicontinuous_output`: each bounded
  probability is continuous in the oracle, so the output probability is lower
  semicontinuous.
* `exists_reflective`: **every such family of machines has a reflective
  oracle** (Theorem 2.1 of Fallenstein, Taylor and Christiano; Theorem 4 of
  Leike, Taylor and Fallenstein; Theorem 7.5 of Leike's thesis).
* `liar_reflective`: for the machine that asks about itself and outputs the
  opposite, every reflective oracle answers that query with probability one
  half (Example 3 of Leike, Taylor and Fallenstein).
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.ReflectiveOracles

open Set
open scoped unitInterval

universe u

/-- What a machine does in one step. -/
inductive Step (M : Type u) where
  /-- Halt, with an output bit or without one. -/
  | halt (output : Option Bool)
  /-- Move to another state. -/
  | next (state : M)
  /-- Flip a fair coin. -/
  | flip (heads tails : M)
  /-- Ask the oracle whether `machine` outputs `1` with probability above
  `threshold`, and continue in `yes` or `no`. -/
  | ask (machine : M) (threshold : ℚ) (yes no : M)

/-- A family of machines: every state has its next step. -/
structure Machines (M : Type u) where
  step : M → Step M

namespace Machines

variable {M : Type u} (T : Machines M)

/-- The probability of halting with `output` within `fuel` steps. -/
noncomputable def haltsWithin (O : Oracle (M × ℚ)) (output : Bool) : ℕ → M → ℝ
  | 0, _ => 0
  | fuel + 1, state =>
    match T.step state with
    | .halt result => if result = some output then 1 else 0
    | .next state' => haltsWithin O output fuel state'
    | .flip heads tails => (haltsWithin O output fuel heads + haltsWithin O output fuel tails) / 2
    | .ask machine threshold yes no =>
        (O (machine, threshold) : ℝ) * haltsWithin O output fuel yes +
          (1 - (O (machine, threshold) : ℝ)) * haltsWithin O output fuel no

theorem haltsWithin_zero (O : Oracle (M × ℚ)) (output : Bool) (state : M) :
    T.haltsWithin O output 0 state = 0 := rfl

theorem haltsWithin_succ (O : Oracle (M × ℚ)) (output : Bool) (fuel : ℕ) (state : M) :
    T.haltsWithin O output (fuel + 1) state =
      match T.step state with
      | .halt result => if result = some output then 1 else 0
      | .next state' => T.haltsWithin O output fuel state'
      | .flip heads tails =>
          (T.haltsWithin O output fuel heads + T.haltsWithin O output fuel tails) / 2
      | .ask machine threshold yes no =>
          (O (machine, threshold) : ℝ) * T.haltsWithin O output fuel yes +
            (1 - (O (machine, threshold) : ℝ)) * T.haltsWithin O output fuel no := rfl

theorem haltsWithin_nonneg (O : Oracle (M × ℚ)) (output : Bool) (fuel : ℕ) (state : M) :
    0 ≤ T.haltsWithin O output fuel state := by
  induction fuel generalizing state with
  | zero => exact le_refl 0
  | succ fuel ih =>
    rw [haltsWithin_succ]
    cases T.step state with
    | halt result => simp only; split_ifs <;> norm_num
    | next state' => exact ih state'
    | flip heads tails => exact div_nonneg (add_nonneg (ih heads) (ih tails)) (by norm_num)
    | ask machine threshold yes no =>
      have answer := (O (machine, threshold)).2
      exact add_nonneg (mul_nonneg answer.1 (ih yes))
        (mul_nonneg (sub_nonneg.mpr answer.2) (ih no))

/-- The two outputs exclude each other. -/
theorem haltsWithin_add_le_one (O : Oracle (M × ℚ)) (fuel : ℕ) (state : M) :
    T.haltsWithin O true fuel state + T.haltsWithin O false fuel state ≤ 1 := by
  induction fuel generalizing state with
  | zero => simp [haltsWithin_zero]
  | succ fuel ih =>
    rw [haltsWithin_succ, haltsWithin_succ]
    cases T.step state with
    | halt result =>
      simp only
      rcases result with _ | _ | _ <;> simp
    | next state' => exact ih state'
    | flip heads tails =>
      have h := ih heads
      have t := ih tails
      simp only
      linarith
    | ask machine threshold yes no =>
      have answer := (O (machine, threshold)).2
      have y := ih yes
      have n := ih no
      simp only
      nlinarith [answer.1, answer.2]

theorem haltsWithin_le_one (O : Oracle (M × ℚ)) (output : Bool) (fuel : ℕ) (state : M) :
    T.haltsWithin O output fuel state ≤ 1 := by
  have sum := T.haltsWithin_add_le_one O fuel state
  have one := T.haltsWithin_nonneg O true fuel state
  have zero := T.haltsWithin_nonneg O false fuel state
  cases output <;> linarith

/-- More steps cannot lower the probability of an output. -/
theorem haltsWithin_le_succ (O : Oracle (M × ℚ)) (output : Bool) (fuel : ℕ) (state : M) :
    T.haltsWithin O output fuel state ≤ T.haltsWithin O output (fuel + 1) state := by
  induction fuel generalizing state with
  | zero => exact T.haltsWithin_nonneg O output 1 state
  | succ fuel ih =>
    rw [haltsWithin_succ, haltsWithin_succ]
    cases T.step state with
    | halt result => exact le_refl _
    | next state' => exact ih state'
    | flip heads tails =>
      simp only
      linarith [ih heads, ih tails]
    | ask machine threshold yes no =>
      have answer := (O (machine, threshold)).2
      simp only
      nlinarith [ih yes, ih no, answer.1, answer.2]

theorem monotone_haltsWithin (O : Oracle (M × ℚ)) (output : Bool) (state : M) :
    Monotone fun fuel => T.haltsWithin O output fuel state :=
  monotone_nat_of_le_succ fun fuel => T.haltsWithin_le_succ O output fuel state

/-- Each bounded probability depends continuously on the oracle: it is a
polynomial in finitely many answers. -/
theorem continuous_haltsWithin (output : Bool) (fuel : ℕ) (state : M) :
    Continuous fun O : Oracle (M × ℚ) => T.haltsWithin O output fuel state := by
  induction fuel generalizing state with
  | zero => exact continuous_const
  | succ fuel ih =>
    simp only [haltsWithin_succ]
    cases T.step state with
    | halt result => exact continuous_const
    | next state' => exact ih state'
    | flip heads tails => exact ((ih heads).add (ih tails)).div_const 2
    | ask machine threshold yes no =>
      have answer : Continuous fun O : Oracle (M × ℚ) => (O (machine, threshold) : ℝ) :=
        continuous_subtype_val.comp (continuous_apply (machine, threshold))
      exact (answer.mul (ih yes)).add ((continuous_const.sub answer).mul (ih no))

/-! ## The output probability -/

/-- The probability that the machine started in `state` halts with `output`. -/
noncomputable def output (O : Oracle (M × ℚ)) (result : Bool) (state : M) : ℝ :=
  ⨆ fuel, T.haltsWithin O result fuel state

theorem bddAbove_haltsWithin (O : Oracle (M × ℚ)) (result : Bool) (state : M) :
    BddAbove (range fun fuel => T.haltsWithin O result fuel state) :=
  ⟨1, by rintro _ ⟨fuel, rfl⟩; exact T.haltsWithin_le_one O result fuel state⟩

theorem haltsWithin_le_output (O : Oracle (M × ℚ)) (result : Bool) (fuel : ℕ) (state : M) :
    T.haltsWithin O result fuel state ≤ T.output O result state :=
  le_ciSup (T.bddAbove_haltsWithin O result state) fuel

theorem output_nonneg (O : Oracle (M × ℚ)) (result : Bool) (state : M) :
    0 ≤ T.output O result state :=
  le_trans (T.haltsWithin_nonneg O result 0 state) (T.haltsWithin_le_output O result 0 state)

theorem output_le_one (O : Oracle (M × ℚ)) (result : Bool) (state : M) :
    T.output O result state ≤ 1 :=
  ciSup_le fun fuel => T.haltsWithin_le_one O result fuel state

/-- The machine may run forever: the two output probabilities add up to at
most one. -/
theorem output_add_le_one (O : Oracle (M × ℚ)) (state : M) :
    T.output O true state + T.output O false state ≤ 1 := by
  have first : T.output O true state ≤ 1 - T.output O false state := by
    apply ciSup_le
    intro fuel
    have second : T.output O false state ≤ 1 - T.haltsWithin O true fuel state := by
      apply ciSup_le
      intro fuel'
      have joint := T.haltsWithin_add_le_one O (max fuel fuel') state
      have left := T.monotone_haltsWithin O true state (le_max_left fuel fuel')
      have right := T.monotone_haltsWithin O false state (le_max_right fuel fuel')
      simp only at left right
      linarith
    linarith
  linarith

/-- **The output probability is lower semicontinuous in the oracle.** -/
theorem lowerSemicontinuous_output (result : Bool) (state : M) :
    LowerSemicontinuous fun O : Oracle (M × ℚ) => T.output O result state :=
  lowerSemicontinuous_ciSup (fun O => T.bddAbove_haltsWithin O result state) fun fuel =>
    (T.continuous_haltsWithin result fuel state).lowerSemicontinuous

/-- The output probability is also the limit over one step more. -/
theorem output_eq_iSup_succ (O : Oracle (M × ℚ)) (result : Bool) (state : M) :
    T.output O result state = ⨆ fuel, T.haltsWithin O result (fuel + 1) state := by
  apply le_antisymm
  · apply ciSup_le
    intro fuel
    exact le_trans (T.haltsWithin_le_succ O result fuel state)
      (le_ciSup (f := fun fuel => T.haltsWithin O result (fuel + 1) state)
        ⟨1, by rintro _ ⟨k, rfl⟩; exact T.haltsWithin_le_one O result (k + 1) state⟩ fuel)
  · apply ciSup_le
    intro fuel
    exact T.haltsWithin_le_output O result (fuel + 1) state

/-! ## First-step equations -/

theorem output_halt (O : Oracle (M × ℚ)) (result : Bool) (state : M) (outcome : Option Bool)
    (step : T.step state = .halt outcome) :
    T.output O result state = if outcome = some result then 1 else 0 := by
  rw [output_eq_iSup_succ]
  simp only [haltsWithin_succ, step]
  exact ciSup_const

theorem output_next (O : Oracle (M × ℚ)) (result : Bool) (state state' : M)
    (step : T.step state = .next state') :
    T.output O result state = T.output O result state' := by
  rw [output_eq_iSup_succ]
  simp only [haltsWithin_succ, step]
  rfl

/-- A limit of a nonnegative combination of two increasing bounded sequences. -/
theorem iSup_combination {a b : ℕ → ℝ} (monotoneA : Monotone a) (monotoneB : Monotone b)
    (boundA : BddAbove (range a)) (boundB : BddAbove (range b)) {c d : ℝ} (c_nonneg : 0 ≤ c)
    (d_nonneg : 0 ≤ d) : (⨆ k, c * a k + d * b k) = c * (⨆ k, a k) + d * ⨆ k, b k := by
  have limitA := tendsto_atTop_ciSup monotoneA boundA
  have limitB := tendsto_atTop_ciSup monotoneB boundB
  have monotone : Monotone fun k => c * a k + d * b k := fun i j le =>
    add_le_add (mul_le_mul_of_nonneg_left (monotoneA le) c_nonneg)
      (mul_le_mul_of_nonneg_left (monotoneB le) d_nonneg)
  have bound : BddAbove (range fun k => c * a k + d * b k) := by
    obtain ⟨boundOfA, isBoundA⟩ := boundA
    obtain ⟨boundOfB, isBoundB⟩ := boundB
    refine ⟨c * boundOfA + d * boundOfB, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact add_le_add (mul_le_mul_of_nonneg_left (isBoundA ⟨k, rfl⟩) c_nonneg)
      (mul_le_mul_of_nonneg_left (isBoundB ⟨k, rfl⟩) d_nonneg)
  exact tendsto_nhds_unique (tendsto_atTop_ciSup monotone bound)
    ((limitA.const_mul c).add (limitB.const_mul d))

theorem output_flip (O : Oracle (M × ℚ)) (result : Bool) (state heads tails : M)
    (step : T.step state = .flip heads tails) :
    T.output O result state = (T.output O result heads + T.output O result tails) / 2 := by
  rw [output_eq_iSup_succ]
  simp only [haltsWithin_succ, step]
  have rewritten : (fun fuel =>
      (T.haltsWithin O result fuel heads + T.haltsWithin O result fuel tails) / 2) =
      fun fuel => 1 / 2 * T.haltsWithin O result fuel heads +
        1 / 2 * T.haltsWithin O result fuel tails := by
    funext fuel
    ring
  rw [rewritten, iSup_combination (T.monotone_haltsWithin O result heads)
    (T.monotone_haltsWithin O result tails) (T.bddAbove_haltsWithin O result heads)
    (T.bddAbove_haltsWithin O result tails) (c := 1 / 2) (d := 1 / 2) (by norm_num) (by norm_num)]
  unfold output
  ring

theorem output_ask (O : Oracle (M × ℚ)) (result : Bool) (state machine : M) (threshold : ℚ)
    (yes no : M) (step : T.step state = .ask machine threshold yes no) :
    T.output O result state =
      (O (machine, threshold) : ℝ) * T.output O result yes +
        (1 - (O (machine, threshold) : ℝ)) * T.output O result no := by
  have answer := (O (machine, threshold)).2
  rw [output_eq_iSup_succ]
  simp only [haltsWithin_succ, step]
  exact iSup_combination (T.monotone_haltsWithin O result yes)
    (T.monotone_haltsWithin O result no) (T.bddAbove_haltsWithin O result yes)
    (T.bddAbove_haltsWithin O result no) answer.1 (sub_nonneg.mpr answer.2)

/-! ## The reflective oracle -/

/-- The queries about these machines: a state and a threshold. -/
noncomputable def queries : QuerySystem (M × ℚ) where
  threshold query := (query.2 : ℝ)
  outputOne query O := T.output O true query.1
  outputZero query O := T.output O false query.1
  outputOne_nonneg query O := T.output_nonneg O true query.1
  outputZero_nonneg query O := T.output_nonneg O false query.1
  output_le_one query O := T.output_add_le_one O query.1

theorem queries_semicontinuous : T.queries.OutputsLowerSemicontinuous := fun query =>
  ⟨T.lowerSemicontinuous_output true query.1, T.lowerSemicontinuous_output false query.1⟩

/-- An oracle is reflective for the machines. -/
def Reflective (O : Oracle (M × ℚ)) : Prop :=
  ∀ (state : M) (threshold : ℚ),
    ((threshold : ℝ) < T.output O true state → O (state, threshold) = 1) ∧
      (1 - (threshold : ℝ) < T.output O false state → O (state, threshold) = 0)

theorem reflective_iff (O : Oracle (M × ℚ)) : T.Reflective O ↔ T.queries.Reflective O :=
  ⟨fun reflective query => reflective query.1 query.2,
    fun reflective state threshold => reflective (state, threshold)⟩

/-- **Every family of probabilistic machines that call an oracle has a
reflective oracle.** -/
theorem exists_reflective : ∃ O : Oracle (M × ℚ), T.Reflective O := by
  obtain ⟨O, reflective⟩ := QuerySystem.exists_reflective T.queries_semicontinuous
  exact ⟨O, (T.reflective_iff O).mpr reflective⟩

end Machines

/-! ## The liar machine -/

/-- The states of a machine that asks the oracle about itself and outputs the
opposite of the answer. -/
inductive LiarState where
  | start
  | sayOne
  | sayZero
  deriving DecidableEq

/-- `start` asks whether `start` outputs `1` with probability above one half;
on the answer yes it outputs `0`, on the answer no it outputs `1`. -/
def liarMachine : Machines LiarState where
  step
    | .start => .ask .start (1 / 2) .sayZero .sayOne
    | .sayOne => .halt (some true)
    | .sayZero => .halt (some false)

theorem liarMachine_output_true (O : Oracle (LiarState × ℚ)) :
    liarMachine.output O true .start = 1 - (O (.start, 1 / 2) : ℝ) := by
  rw [liarMachine.output_ask O true .start .start (1 / 2) .sayZero .sayOne rfl,
    liarMachine.output_halt O true .sayZero (some false) rfl,
    liarMachine.output_halt O true .sayOne (some true) rfl]
  simp

theorem liarMachine_output_false (O : Oracle (LiarState × ℚ)) :
    liarMachine.output O false .start = (O (.start, 1 / 2) : ℝ) := by
  rw [liarMachine.output_ask O false .start .start (1 / 2) .sayZero .sayOne rfl,
    liarMachine.output_halt O false .sayZero (some false) rfl,
    liarMachine.output_halt O false .sayOne (some true) rfl]
  simp

/-- **Every reflective oracle answers the liar's query with probability one
half.** In particular no oracle with answers in `{0, 1}` is reflective. -/
theorem liar_reflective (O : Oracle (LiarState × ℚ)) (reflective : liarMachine.Reflective O) :
    (O (.start, 1 / 2) : ℝ) = 1 / 2 := by
  obtain ⟨one, zero⟩ := reflective .start (1 / 2)
  rw [liarMachine_output_true] at one
  rw [liarMachine_output_false] at zero
  have half : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  rw [half] at one zero
  by_contra different
  rcases lt_or_gt_of_ne different with below | above
  · have forced : O (.start, 1 / 2) = 1 := one (by linarith)
    rw [forced, Set.Icc.coe_one] at below
    norm_num at below
  · have forced : O (.start, 1 / 2) = 0 := zero (by linarith)
    rw [forced, Set.Icc.coe_zero] at above
    norm_num at above

/-- And such an oracle exists. -/
theorem exists_liar_reflective :
    ∃ O : Oracle (LiarState × ℚ), liarMachine.Reflective O ∧ (O (.start, 1 / 2) : ℝ) = 1 / 2 := by
  obtain ⟨O, reflective⟩ := liarMachine.exists_reflective
  exact ⟨O, reflective, liar_reflective O reflective⟩

end Mettapedia.UniversalAI.ReflectiveOracles
