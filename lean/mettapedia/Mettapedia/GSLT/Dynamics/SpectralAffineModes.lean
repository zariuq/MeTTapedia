import Mettapedia.Algebra.MatrixAffineSummary
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact modes for a coupled affine region

The source executes the existing matrix-affine summary on a two-coordinate
rational state. An explicit invertible change of coordinates turns the
symmetric coupling into independent common and difference modes. The proof
preserves every finite iterate; it does not replace a loop by equilibrium.

Retaining both modes is lossless. Dropping the difference mode preserves the
sum observer but changes the full state, with an exact coordinate error.
The arithmetic-operation benefit of powering does not remove the bit size of
its rational result. Native floating arithmetic requires a separate rounding
contract, and a hole that reads or mutates the state requires decoding.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.SpectralAffineModes

open Mettapedia.Algebra

abbrev State := Fin 2 → ℚ
abbrev Modes := ℚ × ℚ

def symmetric (self cross : ℚ) : MatrixAffineSummary (Fin 2) ℚ :=
  ⟨!![self, cross; cross, self], 0⟩

def encode (state : State) : Modes :=
  (state 0 + state 1, state 0 - state 1)

def decode (modes : Modes) : State :=
  ![(modes.1 + modes.2) / 2, (modes.1 - modes.2) / 2]

/-- The two eigenvalues multiply their corresponding coordinates separately. -/
def modeStep (self cross : ℚ) (modes : Modes) : Modes :=
  ((self + cross) * modes.1, (self - cross) * modes.2)

theorem decode_encode (state : State) : decode (encode state) = state := by
  ext position
  fin_cases position <;> simp [decode, encode]

theorem encode_decode (modes : Modes) : encode (decode modes) = modes := by
  rcases modes with ⟨common, difference⟩
  ext <;> simp [decode, encode] <;> ring

/-- Independent source matrix multiplication and target mode multiplication. -/
theorem encode_step (self cross : ℚ) (state : State) :
    encode ((symmetric self cross).act state) = modeStep self cross (encode state) := by
  ext <;> simp [encode, symmetric, MatrixAffineSummary.act,
    dotProduct, Fin.sum_univ_two, modeStep] <;> ring

theorem decode_step (self cross : ℚ) (modes : Modes) :
    decode (modeStep self cross modes) = (symmetric self cross).act (decode modes) := by
  rw [← encode_decode modes] at ⊢
  rw [← encode_step, decode_encode, decode_encode]

/-- All finite source executions, including their actual initial state. -/
theorem encode_run (count : Nat) (self cross : ℚ) (state : State) :
    encode (MatrixAffineSummary.run (List.replicate count (symmetric self cross)) state) =
      ((self + cross) ^ count * (encode state).1,
       (self - cross) ^ count * (encode state).2) := by
  induction count generalizing state with
  | zero => simp [MatrixAffineSummary.run]
  | succ count ih =>
    simp only [List.replicate_succ, MatrixAffineSummary.run, List.foldl_cons]
    change encode (MatrixAffineSummary.run (List.replicate count (symmetric self cross))
      ((symmetric self cross).act state)) = _
    rw [ih]
    rw [encode_step]
    simp only [modeStep, pow_succ]
    ext <;> simp only <;> ring

theorem run_via_modes (count : Nat) (self cross : ℚ) (state : State) :
    MatrixAffineSummary.run (List.replicate count (symmetric self cross)) state =
      decode ((self + cross) ^ count * (encode state).1,
        (self - cross) ^ count * (encode state).2) := by
  rw [← encode_run, decode_encode]

/-- A concrete averaging/diffusion region: common mode is invariant and the
disagreement mode is halved at each source step. -/
theorem diffusion_modes (count : Nat) (state : State) :
    MatrixAffineSummary.run
      (List.replicate count (symmetric (3 / 4) (1 / 4))) state =
      decode ((encode state).1, (1 / 2) ^ count * (encode state).2) := by
  rw [run_via_modes]
  norm_num

theorem diffusion_from_unit (count : Nat) :
    MatrixAffineSummary.run
      (List.replicate count (symmetric (3 / 4) (1 / 4))) ![1, 0] =
      ![(1 + (1 / 2) ^ count) / 2, (1 - (1 / 2) ^ count) / 2] := by
  rw [diffusion_modes]
  simp [encode, decode]

/-- A target region computes each mode by an ordinary scalar power. -/
def modalPower (count : Nat) (self cross : ℚ) (modes : Modes) : Modes :=
  ((self + cross) ^ count * modes.1, (self - cross) ^ count * modes.2)

/-- A hole without its own modal implementation crosses the exact boundary
back to the original state. Its position in the authored plan is retained. -/
def transportHole (hole : State → State) (modes : Modes) : Modes :=
  encode (hole (decode modes))

/-- Two independently powered regions may surround an arbitrary state
transformation. The theorem does not erase that transformation or move it
past a source step. -/
theorem powered_regions_with_hole (before after : Nat) (self cross : ℚ)
    (hole : State → State) (state : State) :
    MatrixAffineSummary.run (List.replicate after (symmetric self cross))
      (hole (MatrixAffineSummary.run
        (List.replicate before (symmetric self cross)) state)) =
      decode (modalPower after self cross
        (transportHole hole (modalPower before self cross (encode state)))) := by
  calc
    _ = decode (modalPower after self cross
        (encode (hole (MatrixAffineSummary.run
          (List.replicate before (symmetric self cross)) state)))) :=
      run_via_modes after self cross _
    _ = _ := by rw [run_via_modes]; rfl

def bumpFirst (state : State) : State := ![state 0 + 1, state 1]

/-- Keeping the final pure operator while moving an interior mutation changes
the result, even for the two-node diffusion example. -/
theorem moving_hole_changes_result :
    (symmetric (3 / 4) (1 / 4)).act
      (bumpFirst ((symmetric (3 / 4) (1 / 4)).act ![0, 0])) ≠
      bumpFirst (((symmetric (3 / 4) (1 / 4)).compose
        (symmetric (3 / 4) (1 / 4))).act ![0, 0]) := by
  intro equal
  have first := congrFun equal 0
  norm_num [symmetric, bumpFirst, MatrixAffineSummary.compose,
    MatrixAffineSummary.act, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at first

/-- In a swap, the difference mode changes sign. This is a genuine periodic
state transformation; its two occurrences are not bag cancellation. -/
theorem swap_modes (state : State) :
    encode ((symmetric 0 1).act state) = ((encode state).1, -(encode state).2) := by
  rw [encode_step]
  simp [modeStep]

def meanOnly (state : State) : State := decode ((encode state).1, 0)

theorem meanOnly_preserves_sum (state : State) :
    (encode (meanOnly state)).1 = (encode state).1 := by
  rw [meanOnly, encode_decode]

theorem meanOnly_first_error (state : State) :
    |state 0 - meanOnly state 0| = |state 0 - state 1| / 2 := by
  have exact : state 0 - meanOnly state 0 = (state 0 - state 1) / 2 := by
    simp [meanOnly, decode, encode]
    ring
  rw [exact, abs_div]
  norm_num

theorem meanOnly_second_error (state : State) :
    |state 1 - meanOnly state 1| = |state 0 - state 1| / 2 := by
  have exact : state 1 - meanOnly state 1 = -((state 0 - state 1) / 2) := by
    simp [meanOnly, decode, encode]
    ring
  rw [exact, abs_neg, abs_div]
  norm_num

theorem meanOnly_loses_state : meanOnly ![1, 0] ≠ ![1, 0] := by
  intro equal
  have first := congrFun equal 0
  norm_num [meanOnly, decode, encode] at first

/-- A sound error threshold supports an approximate coordinate observer;
it does not assert equality of the underlying state. -/
theorem meanOnly_error_bound (state : State) (tolerance : ℚ)
    (certificate : |state 0 - state 1| ≤ 2 * tolerance) :
    |state 0 - meanOnly state 0| ≤ tolerance ∧
      |state 1 - meanOnly state 1| ≤ tolerance := by
  rw [meanOnly_first_error, meanOnly_second_error]
  constructor <;> linarith

end Mettapedia.GSLT.Dynamics.SpectralAffineModes
