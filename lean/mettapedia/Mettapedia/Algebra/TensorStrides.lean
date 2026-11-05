import Mettapedia.Algebra.TensorShape

/-!
# Coordinate bounds for signed strided tensor views

The reference quantifies over independently supplied in-shape coordinates.
The target accumulates the minimum and maximum corner contributions, including
negative and zero strides. Empty shapes have no element coordinates but retain
an explicit allocation-anchor requirement; scalars have one coordinate.

Addresses are measured in scalar cells. Native byte alignment, complete-cell
capacity, pointer validity and integer/shape representation remain separate
obligations unless an explicit checked-word law states otherwise.
-/

set_option autoImplicit false
namespace Mettapedia.Algebra.TensorStrides

structure Axis where
  dimension : Nat
  stride : Int
  deriving DecidableEq, Repr

def shape (axes : List Axis) : TensorShape.Shape := axes.map Axis.dimension

def Positive (axes : List Axis) : Prop := ∀ axis ∈ axes, 0 < axis.dimension

theorem nonempty_count_iff_positive (axes : List Axis) :
    TensorShape.size (shape axes) ≠ 0 ↔ Positive axes := by
  induction axes with
  | nil => simp [shape, Positive]
  | cons axis rest ih =>
      constructor
      · intro nonzero current member
        rcases List.mem_cons.mp member with same | remaining
        · subst current
          have notZero : axis.dimension ≠ 0 := by
            intro zero
            apply nonzero
            change axis.dimension * TensorShape.size (shape rest) = 0
            simp [zero]
          omega
        · have tail : TensorShape.size (shape rest) ≠ 0 := by
            intro zero
            apply nonzero
            change axis.dimension * TensorShape.size (shape rest) = 0
            simp [zero]
          exact ih.mp tail current remaining
      · intro positive
        have head : axis.dimension ≠ 0 := by
          have := positive axis List.mem_cons_self
          omega
        have tail : TensorShape.size (shape rest) ≠ 0 :=
          ih.mpr (fun current member => positive current (List.mem_cons_of_mem _ member))
        change axis.dimension * TensorShape.size (shape rest) ≠ 0
        exact Nat.mul_ne_zero head tail

inductive Coordinate : List Axis → List Nat → Prop where
  | scalar : Coordinate [] []
  | axis {current : Axis} {rest : List Axis} {index : Nat} {indices : List Nat}
      (within : index < current.dimension) (tail : Coordinate rest indices) :
      Coordinate (current :: rest) (index :: indices)

/-- This source expression uses actual coordinates, not computed extrema. -/
def displacement : List Axis → List Nat → Int
  | axis :: rest, index :: indices => (index : Int) * axis.stride + displacement rest indices
  | _, _ => 0

def address (offset : Int) (axes : List Axis) (indices : List Nat) : Int :=
  offset + displacement axes indices

def span (axis : Axis) : Int := ((axis.dimension - 1 : Nat) : Int) * axis.stride

def lower (axis : Axis) : Int := if span axis < 0 then span axis else 0
def upper (axis : Axis) : Int := if span axis < 0 then 0 else span axis

def lowerSum : List Axis → Int
  | [] => 0
  | axis :: rest => lower axis + lowerSum rest

def upperSum : List Axis → Int
  | [] => 0
  | axis :: rest => upper axis + upperSum rest

theorem axis_contribution_bounds (axis : Axis) (index : Nat)
    (within : index < axis.dimension) :
    lower axis ≤ (index : Int) * axis.stride ∧ (index : Int) * axis.stride ≤ upper axis := by
  have bound : (index : Int) ≤ ((axis.dimension - 1 : Nat) : Int) := by omega
  have indexNonnegative : (0 : Int) ≤ index := Int.natCast_nonneg _
  have lastNonnegative : (0 : Int) ≤ ((axis.dimension - 1 : Nat) : Int) := Int.natCast_nonneg _
  by_cases nonnegative : 0 ≤ axis.stride
  · have start := Int.mul_nonneg indexNonnegative nonnegative
    have finish := Int.mul_le_mul_of_nonneg_right bound nonnegative
    have spanNonnegative := Int.mul_nonneg lastNonnegative nonnegative
    have notNegative : ¬span axis < 0 := by unfold span; omega
    simp only [lower, upper, if_neg notNegative]
    exact ⟨start, finish⟩
  · have nonpositive : axis.stride ≤ 0 := by omega
    have start := Int.mul_le_mul_of_nonpos_right bound nonpositive
    have finish := Int.mul_nonpos_of_nonneg_of_nonpos indexNonnegative nonpositive
    have spanNonpositive := Int.mul_nonpos_of_nonneg_of_nonpos lastNonnegative nonpositive
    by_cases negative : span axis < 0
    · simp only [lower, upper, if_pos negative]
      exact ⟨start, finish⟩
    · have zero : span axis = 0 := by unfold span at *; omega
      have pointZero : (index : Int) * axis.stride = 0 := by unfold span at zero; omega
      simp [lower, upper, pointZero, zero]

theorem coordinate_displacement_bounds (axes : List Axis) (indices : List Nat)
    (within : Coordinate axes indices) :
    lowerSum axes ≤ displacement axes indices ∧ displacement axes indices ≤ upperSum axes := by
  induction within with
  | scalar => exact ⟨Int.le_refl _, Int.le_refl _⟩
  | @axis current rest index indices within tail ih =>
      have head := axis_contribution_bounds current index within
      simp only [displacement, lowerSum, upperSum]
      omega

theorem coordinate_implies_positive (axes : List Axis) (indices : List Nat)
    (within : Coordinate axes indices) : Positive axes := by
  induction within with
  | scalar => intro axis member; cases member
  | @axis current rest index indices within tail ih =>
      intro axis member
      rcases List.mem_cons.mp member with same | remaining
      · subst axis
        omega
      · exact ih axis remaining

def lowIndex (axis : Axis) : Nat := if span axis < 0 then axis.dimension - 1 else 0
def highIndex (axis : Axis) : Nat := if span axis < 0 then 0 else axis.dimension - 1

def lowCorner (axes : List Axis) : List Nat := axes.map lowIndex
def highCorner (axes : List Axis) : List Nat := axes.map highIndex

theorem corners_are_coordinates (axes : List Axis) (positive : Positive axes) :
    Coordinate axes (lowCorner axes) ∧ Coordinate axes (highCorner axes) := by
  induction axes with
  | nil => exact ⟨.scalar, .scalar⟩
  | cons axis rest ih =>
      have head := positive axis List.mem_cons_self
      have tail := ih (fun current member => positive current (List.mem_cons_of_mem _ member))
      have low : lowIndex axis < axis.dimension := by unfold lowIndex; split <;> omega
      have high : highIndex axis < axis.dimension := by unfold highIndex; split <;> omega
      exact ⟨.axis low tail.1, .axis high tail.2⟩

theorem corners_attain_bounds (axes : List Axis) :
    displacement axes (lowCorner axes) = lowerSum axes ∧
      displacement axes (highCorner axes) = upperSum axes := by
  induction axes with
  | nil => exact ⟨rfl, rfl⟩
  | cons axis rest ih =>
      constructor
      · change (lowIndex axis : Int) * axis.stride + displacement rest (lowCorner rest) =
          lower axis + lowerSum rest
        rw [ih.1]
        by_cases negative : span axis < 0
        · simp only [lowIndex, lower, if_pos negative]
          rfl
        · simp [lowIndex, lower, negative]
      · change (highIndex axis : Int) * axis.stride + displacement rest (highCorner rest) =
          upper axis + upperSum rest
        rw [ih.2]
        by_cases negative : span axis < 0
        · simp [highIndex, upper, negative]
        · simp only [highIndex, upper, if_neg negative]
          rfl

structure Bounds where
  low : Int
  high : Int
  deriving DecidableEq, Repr

/-- The native corner fold updates one endpoint for each signed axis. -/
def extrema : List Axis → Bounds → Bounds
  | [], bounds => bounds
  | axis :: rest, bounds =>
      if span axis < 0 then extrema rest {bounds with low := bounds.low + span axis}
      else extrema rest {bounds with high := bounds.high + span axis}

theorem extrema_equal_corner_sums (axes : List Axis) (bounds : Bounds) :
    extrema axes bounds = ⟨bounds.low + lowerSum axes, bounds.high + upperSum axes⟩ := by
  induction axes generalizing bounds with
  | nil => simp [extrema, lowerSum, upperSum]
  | cons axis rest ih =>
      by_cases negative : span axis < 0 <;>
        simp [extrema, lowerSum, upperSum, lower, upper, negative, ih, Int.add_assoc]

/-- Universal element safety is independent of the implementation's fold. -/
def CoordinateSafe (storage : Nat) (offset : Int) (axes : List Axis) : Prop :=
  ∀ indices, Coordinate axes indices → 0 ≤ address offset axes indices ∧ address offset axes indices < storage

def ExtremaSafe (storage : Nat) (offset : Int) (axes : List Axis) : Prop :=
  let bounds := extrema axes ⟨offset, offset⟩
  0 ≤ bounds.low ∧ bounds.high < storage

theorem coordinate_safe_iff_extrema (storage : Nat) (offset : Int) (axes : List Axis)
    (positive : Positive axes) : CoordinateSafe storage offset axes ↔ ExtremaSafe storage offset axes := by
  rw [ExtremaSafe, extrema_equal_corner_sums]
  constructor
  · intro safe
    obtain ⟨low, high⟩ := corners_are_coordinates axes positive
    have lowSafe := safe _ low
    have highSafe := safe _ high
    rw [address, (corners_attain_bounds axes).1] at lowSafe
    rw [address, (corners_attain_bounds axes).2] at highSafe
    exact ⟨lowSafe.1, highSafe.2⟩
  · intro bounds indices within
    dsimp only at bounds
    have ranged := coordinate_displacement_bounds axes indices within
    unfold address
    omega

def ReferenceSafe (storage : Nat) (offset : Int) (axes : List Axis) : Prop :=
  if TensorShape.size (shape axes) = 0 then 0 ≤ offset ∧ offset ≤ storage
  else CoordinateSafe storage offset axes

def NativeSafe (storage : Nat) (offset : Int) (axes : List Axis) : Prop :=
  if TensorShape.size (shape axes) = 0 then 0 ≤ offset ∧ offset ≤ storage
  else ExtremaSafe storage offset axes

instance (storage : Nat) (offset : Int) (axes : List Axis) : Decidable (NativeSafe storage offset axes) := by
  unfold NativeSafe ExtremaSafe
  infer_instance

theorem native_reference_safety_iff (storage : Nat) (offset : Int) (axes : List Axis) :
    NativeSafe storage offset axes ↔ ReferenceSafe storage offset axes := by
  by_cases empty : TensorShape.size (shape axes) = 0
  · simp [NativeSafe, ReferenceSafe, empty]
  · simpa [NativeSafe, ReferenceSafe, empty] using
      (coordinate_safe_iff_extrema storage offset axes ((nonempty_count_iff_positive axes).mp empty)).symm

namespace Checked

def InRange (maximum : Nat) (value : Int) : Prop :=
  -((maximum : Int) + 1) ≤ value ∧ value ≤ maximum

instance (maximum : Nat) (value : Int) : Decidable (InRange maximum value) := by
  unfold InRange
  infer_instance

/-- Mathematical success contract of a checked signed operation. The C
compiler's builtins and casts must realize this range check. -/
def word (maximum : Nat) (value : Int) : Option Int :=
  if InRange maximum value then some value else none

theorem word_success (maximum : Nat) (value result : Int)
    (success : word maximum value = some result) : result = value ∧ InRange maximum result := by
  unfold word at success
  split at success
  · cases success
    exact ⟨rfl, ‹InRange maximum value›⟩
  · cases success

def EndpointsInRange (maximum : Nat) (bounds : Bounds) : Prop :=
  InRange maximum bounds.low ∧ InRange maximum bounds.high

/-- Zero strides are skipped BEFORE narrowing a possibly huge dimension.
Only nonzero terms require the dimension-1 conversion and product checks. -/
def step (maximum : Nat) (axis : Axis) (bounds : Bounds) : Option Bounds :=
  if axis.stride = 0 then some bounds
  else if maximum < axis.dimension - 1 then none
  else do
    let delta ← word maximum (span axis)
    if delta < 0 then
      let value ← word maximum (bounds.low + delta)
      pure {bounds with low := value}
    else
      let value ← word maximum (bounds.high + delta)
      pure {bounds with high := value}

theorem step_success (maximum : Nat) (axis : Axis) (before after : Bounds)
    (success : step maximum axis before = some after) :
    after = extrema [axis] before ∧
      (EndpointsInRange maximum before → EndpointsInRange maximum after) := by
  by_cases zero : axis.stride = 0
  · simp only [step, if_pos zero, Option.some.injEq] at success
    subst after
    constructor
    · cases before
      simp [extrema, span, zero]
    · exact id
  · by_cases large : maximum < axis.dimension - 1
    · simp [step, zero, large] at success
    · simp only [step, if_neg zero, if_neg large] at success
      obtain ⟨delta, product, continued⟩ := Option.bind_eq_some_iff.mp success
      have same := (word_success maximum (span axis) delta product).1
      subst delta
      by_cases negative : span axis < 0
      · simp only [if_pos negative] at continued
        obtain ⟨value, added, result⟩ := Option.bind_eq_some_iff.mp continued
        have exactValue := (word_success maximum (before.low + span axis) value added).1
        subst value
        cases result
        constructor
        · simp [extrema, negative]
        · intro range
          exact ⟨(word_success maximum _ _ added).2, range.2⟩
      · simp only [if_neg negative] at continued
        obtain ⟨value, added, result⟩ := Option.bind_eq_some_iff.mp continued
        have exactValue := (word_success maximum (before.high + span axis) value added).1
        subst value
        cases result
        constructor
        · simp [extrema, negative]
        · intro range
          exact ⟨range.1, (word_success maximum _ _ added).2⟩

def fold (maximum : Nat) : List Axis → Bounds → Option Bounds
  | [], bounds => some bounds
  | axis :: rest, bounds => (step maximum axis bounds).bind fun next => fold maximum rest next

theorem fold_success (maximum : Nat) (axes : List Axis) (before after : Bounds)
    (success : fold maximum axes before = some after) :
    after = extrema axes before ∧
      (EndpointsInRange maximum before → EndpointsInRange maximum after) := by
  induction axes generalizing before with
  | nil =>
      cases success
      exact ⟨rfl, id⟩
  | cons axis rest ih =>
      obtain ⟨middle, entered, remaining⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨head, headRange⟩ := step_success maximum axis before middle entered
      obtain ⟨tail, tailRange⟩ := ih middle remaining
      refine ⟨?_, fun range => tailRange (headRange range)⟩
      rw [tail, head]
      by_cases negative : span axis < 0 <;> simp [extrema, negative]

/-- Shape/byte-count and dtype validation precede this element-address
checker. Empty views skip all axis arithmetic but retain their anchor guard. -/
def view (maximum storage offset : Nat) (axes : List Axis) : Option Bounds :=
  if maximum < offset then none
  else if TensorShape.size (shape axes) = 0 then
    if offset ≤ storage then some ⟨offset, offset⟩ else none
  else do
    let bounds ← fold maximum axes ⟨offset, offset⟩
    if 0 ≤ bounds.low ∧ bounds.high < storage then some bounds else none

theorem view_success (maximum storage offset : Nat) (axes : List Axis) (bounds : Bounds)
    (success : view maximum storage offset axes = some bounds) :
    ReferenceSafe storage offset axes ∧ EndpointsInRange maximum bounds := by
  by_cases tooLarge : maximum < offset
  · simp [view, tooLarge] at success
  · have initial : EndpointsInRange maximum ⟨offset, offset⟩ := by
      simp only [EndpointsInRange, InRange]
      omega
    by_cases empty : TensorShape.size (shape axes) = 0
    · simp only [view, if_neg tooLarge, if_pos empty] at success
      split at success
      · rename_i anchored
        cases success
        refine ⟨?_, initial⟩
        simp only [ReferenceSafe, if_pos empty]
        omega
      · cases success
    · simp only [view, if_neg tooLarge, if_neg empty] at success
      obtain ⟨computed, ran, accepted⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨exactBounds, ranged⟩ := fold_success maximum axes _ computed ran
      split at accepted
      · rename_i safe
        cases accepted
        have native : NativeSafe storage offset axes := by
          simp only [NativeSafe, if_neg empty, ExtremaSafe]
          rw [← exactBounds]
          exact safe
        exact ⟨(native_reference_safety_iff storage offset axes).mp native, ranged initial⟩
      · cases accepted

theorem view_nonempty_bounds (maximum storage offset : Nat) (axes : List Axis) (bounds : Bounds)
    (nonempty : TensorShape.size (shape axes) ≠ 0)
    (success : view maximum storage offset axes = some bounds) :
    bounds = extrema axes ⟨offset, offset⟩ := by
  by_cases tooLarge : maximum < offset
  · simp [view, tooLarge] at success
  · simp only [view, if_neg tooLarge, if_neg nonempty] at success
    obtain ⟨computed, ran, accepted⟩ := Option.bind_eq_some_iff.mp success
    split at accepted
    · cases accepted
      exact (fold_success maximum axes _ _ ran).1
    · cases accepted

/-- Every addressed scalar fits both the allocation and the signed word.
The flat-index coordinate decoder and unchecked C readout remain a separate
native correspondence boundary. -/
theorem view_coordinate_safety (maximum storage offset : Nat) (axes : List Axis)
    (bounds : Bounds) (success : view maximum storage offset axes = some bounds)
    (indices : List Nat) (within : Coordinate axes indices) :
    InRange maximum (address offset axes indices) ∧
      0 ≤ address offset axes indices ∧ address offset axes indices < storage := by
  have nonempty := (nonempty_count_iff_positive axes).mpr (coordinate_implies_positive axes indices within)
  have valid := view_success maximum storage offset axes bounds success
  have safe : CoordinateSafe storage offset axes := by
    simpa only [ReferenceSafe, if_neg nonempty] using valid.1
  have endpoints := valid.2
  rw [view_nonempty_bounds maximum storage offset axes bounds nonempty success,
    extrema_equal_corner_sums] at endpoints
  dsimp only [EndpointsInRange, InRange] at endpoints
  have coordinates := coordinate_displacement_bounds axes indices within
  refine ⟨?_, safe indices within⟩
  unfold InRange address
  omega

end Checked

/-- Trailing allocation bytes need not form another scalar. Cell safety is
exactly full-width byte-footprint safety; no rounding up is permitted. -/
theorem full_cell_capacity (bytes width index : Nat) (positive : 0 < width) :
    index < bytes / width ↔ (index + 1) * width ≤ bytes := by
  constructor
  · intro inside
    apply (Nat.le_div_iff_mul_le positive).mp
    omega
  · intro footprint
    have within := (Nat.le_div_iff_mul_le positive).mpr footprint
    omega

namespace Controls

theorem scalar_and_empty_have_different_address_contracts :
    Checked.view 127 1 0 [] = some ⟨0, 0⟩ ∧
      Checked.view 127 0 0 [] = none ∧
      Checked.view 127 0 0 [⟨0, 1⟩] = some ⟨0, 0⟩ := by decide

theorem negative_stride_uses_a_shifted_origin :
    Checked.view 127 4 3 [⟨4, -1⟩] = some ⟨0, 3⟩ ∧
      address 3 [⟨4, -1⟩] [3] = 0 := by decide

theorem negative_stride_with_unshifted_origin_is_refused :
    Checked.view 127 4 0 [⟨4, -1⟩] = none ∧
      address 0 [⟨4, -1⟩] [1] = -1 := by decide

theorem zero_stride_does_not_narrow_the_coordinate :
    Checked.view 127 1 0 [⟨1000, 0⟩] = some ⟨0, 0⟩ ∧
      address 0 [⟨1000, 0⟩] [999] = 0 := by decide

theorem zero_stride_does_not_make_a_nonzero_axis_empty :
    TensorShape.size (shape [⟨1000, 0⟩]) = 1000 ∧
      Checked.view 127 0 0 [⟨1000, 0⟩] = none := by decide

theorem empty_views_allow_exactly_one_past_the_cells :
    Checked.view 127 4 4 [⟨0, -128⟩, ⟨1000, 127⟩] = some ⟨4, 4⟩ ∧
      Checked.view 127 4 5 [⟨0, -128⟩] = none := by decide

theorem empty_view_has_no_element_coordinate :
    ¬Coordinate [⟨0, -128⟩] [0] := by
  intro within
  cases within with
  | axis bound _ => simp at bound

theorem mixed_signed_axes_have_independent_corner_choices :
    extrema [⟨3, 4⟩, ⟨4, -1⟩] ⟨3, 3⟩ = ⟨0, 11⟩ ∧
      Checked.view 127 12 3 [⟨3, 4⟩, ⟨4, -1⟩] = some ⟨0, 11⟩ := by decide

theorem omitted_lower_bound_accepts_an_invalid_coordinate :
    let bounds := extrema [⟨4, -1⟩] ⟨0, 0⟩
    bounds.high < 4 ∧ ¬NativeSafe 4 0 [⟨4, -1⟩] ∧
      address 0 [⟨4, -1⟩] [1] < 0 := by decide

theorem inclusive_high_bound_accepts_one_cell_too_many :
    let bounds := extrema [⟨5, 1⟩] ⟨0, 0⟩
    bounds.high ≤ 4 ∧ Checked.view 127 4 0 [⟨5, 1⟩] = none ∧
      address 0 [⟨5, 1⟩] [4] = 4 := by decide

theorem zero_axis_skips_unreachable_overflowing_terms :
    Checked.view 127 0 0 [⟨0, 127⟩, ⟨1000, -128⟩] = some ⟨0, 0⟩ := by decide

theorem signed_product_overflow_is_not_wrapped :
    Checked.fold 127 [⟨3, 100⟩] ⟨0, 0⟩ = none ∧ span ⟨3, 100⟩ = 200 := by decide

theorem signed_accumulation_overflow_is_not_wrapped :
    Checked.fold 127 [⟨2, 100⟩, ⟨2, 100⟩] ⟨0, 0⟩ = none ∧
      extrema [⟨2, 100⟩, ⟨2, 100⟩] ⟨0, 0⟩ = ⟨0, 200⟩ := by decide

theorem native_word_admission_is_conservative :
    NativeSafe 201 0 [⟨3, 100⟩] ∧ Checked.view 127 201 0 [⟨3, 100⟩] = none := by decide

theorem allocation_trailer_does_not_become_an_extra_scalar :
    18 / 4 = 4 ∧ (3 + 1) * 4 ≤ 18 ∧ ¬(4 + 1) * 4 ≤ 18 := by decide

end Controls

end Mettapedia.Algebra.TensorStrides
