import Mettapedia.GSLT.LanguageDef.CheckedScalarSpans

/-!
# Checked scalar and span operational primitives

Failure edges are observable outcomes, distinct from an invalid primitive
operation. Arithmetic guards follow the overflow-avoiding tests emitted by
the checked frontend; their specifications use unbounded arithmetic instead.
Memory operations run on an independent finite list of initialized cells.

These are the operational leaves needed by checked IR. This module does not
yet prove that a source function or a compiler object realizes their semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CheckedScalarOperations

inductive Failure where
  | arithmetic | bounds | required
  deriving DecidableEq, Repr

inductive Outcome (α : Type) where
  | value (result : α)
  | failed (reason : Failure)
  | fault
  deriving DecidableEq, Repr

def rawAdd (limit a b : Nat) : Outcome Nat :=
  if a + b ≤ limit then .value (a + b) else .fault

def checkedAdd (limit a b : Nat) : Outcome Nat :=
  if b > limit ∨ a > limit - b then .failed .arithmetic else rawAdd limit a b

def additionSpec (limit a b : Nat) : Outcome Nat :=
  if a + b ≤ limit then .value (a + b) else .failed .arithmetic

theorem checkedAdd_correct (limit a b : Nat) :
    checkedAdd limit a b = additionSpec limit a b := by
  unfold checkedAdd rawAdd additionSpec
  split <;> split <;> simp_all <;> omega

theorem checkedAdd_no_fault (limit a b : Nat) :
    checkedAdd limit a b ≠ .fault := by
  rw [checkedAdd_correct]
  unfold additionSpec
  split <;> simp

def rawSub (limit a b : Nat) : Outcome Nat :=
  if b ≤ a ∧ a - b ≤ limit then .value (a - b) else .fault

def checkedSub (limit a b : Nat) : Outcome Nat :=
  if a > limit ∨ a < b then .failed .arithmetic else rawSub limit a b

def subtractionSpec (limit a b : Nat) : Outcome Nat :=
  if a ≤ limit ∧ b ≤ a then .value (a - b) else .failed .arithmetic

theorem checkedSub_correct (limit a b : Nat) :
    checkedSub limit a b = subtractionSpec limit a b := by
  unfold checkedSub rawSub subtractionSpec
  split <;> split <;> simp_all <;> omega

theorem checkedSub_no_fault (limit a b : Nat) :
    checkedSub limit a b ≠ .fault := by
  rw [checkedSub_correct]
  unfold subtractionSpec
  split <;> simp

def rawMul (limit a b : Nat) : Outcome Nat :=
  if a * b ≤ limit then .value (a * b) else .fault

def checkedMul (limit a b : Nat) : Outcome Nat :=
  if a > limit ∨ b > limit ∨ (b ≠ 0 ∧ a > limit / b) then .failed .arithmetic
  else rawMul limit a b

def multiplicationSpec (limit a b : Nat) : Outcome Nat :=
  if a * b ≤ limit then .value (a * b) else .failed .arithmetic

theorem checkedMul_correct {limit a b : Nat} (left : a ≤ limit) (right : b ≤ limit) :
    checkedMul limit a b = multiplicationSpec limit a b := by
  by_cases zero : b = 0
  · subst b
    simp [checkedMul, rawMul, multiplicationSpec, Nat.not_lt.mpr left]
  · have positive : 0 < b := Nat.pos_of_ne_zero zero
    have bound : a ≤ limit / b ↔ a * b ≤ limit := Nat.le_div_iff_mul_le positive
    by_cases fits : a * b ≤ limit
    · have quotient := bound.mpr fits
      simp [checkedMul, rawMul, multiplicationSpec, Nat.not_lt.mpr left,
        Nat.not_lt.mpr right, Nat.not_lt.mpr quotient, fits]
    · have quotient : limit / b < a := Nat.lt_of_not_ge (fun h => fits (bound.mp h))
      simp [checkedMul, multiplicationSpec, zero, quotient, fits]

theorem checkedMul_no_fault {limit a b : Nat} (left : a ≤ limit) (right : b ≤ limit) :
    checkedMul limit a b ≠ .fault := by
  rw [checkedMul_correct left right]
  unfold multiplicationSpec
  split <;> simp

def rawDivision (remainder : Bool) (a b : Nat) : Outcome Nat :=
  if b = 0 then .fault else .value (if remainder then a % b else a / b)

def checkedDivision (remainder : Bool) (a b : Nat) : Outcome Nat :=
  if b = 0 then .failed .arithmetic else rawDivision remainder a b

theorem checkedDivision_no_fault (remainder : Bool) (a b : Nat) :
    checkedDivision remainder a b ≠ .fault := by
  by_cases zero : b = 0 <;> simp [checkedDivision, rawDivision, zero]

theorem checkedDivision_bounded {remainder : Bool} {limit a b value : Nat}
    (input : a ≤ limit) (execution : checkedDivision remainder a b = .value value) :
    value ≤ limit := by
  unfold checkedDivision rawDivision at execution
  split at execution
  · cases execution
  next =>
    simp only [Outcome.value.injEq] at execution
    cases remainder with
    | false => simp only [Bool.false_eq_true, ↓reduceIte] at execution
               exact execution ▸ Nat.le_trans (Nat.div_le_self a b) input
    | true => simp only [↓reduceIte] at execution
              exact execution ▸ Nat.le_trans (Nat.mod_le a b) input

/-- Explicit modular arithmetic is an operation on words, not an unchecked
overflow assumption. The frontend uses it only for unsigned scalar types. -/
def modular (modulus : Nat) (value : Nat) : Nat := value % modulus

theorem modular_in_range {modulus value : Nat} (positive : 0 < modulus) :
    modular modulus value < modulus := Nat.mod_lt value positive

def rawShift (bits : Nat) (left : Bool) (value count : Nat) : Outcome Nat :=
  if count < bits ∧ value < 2 ^ bits then
    .value ((if left then value * 2 ^ count else value / 2 ^ count) % 2 ^ bits)
  else .fault

def checkedShift (bits : Nat) (left : Bool) (value count : Nat) : Outcome Nat :=
  if count ≥ bits then .failed .arithmetic else rawShift bits left value count

theorem checkedShift_no_fault {bits value count : Nat} {left : Bool}
    (input : value < 2 ^ bits) : checkedShift bits left value count ≠ .fault := by
  by_cases bounded : count < bits
  · simp [checkedShift, rawShift, input, bounded, Nat.not_le.mpr bounded]
  · simp [checkedShift, Nat.le_of_not_lt bounded]

theorem checkedShift_bounded {bits value count result : Nat} {left : Bool}
    (execution : checkedShift bits left value count = .value result) : result < 2 ^ bits := by
  unfold checkedShift rawShift at execution
  split at execution
  · cases execution
  · split at execution
    · cases Outcome.value.inj execution
      exact Nat.mod_lt _ (Nat.two_pow_pos bits)
    · cases execution

def rawRead (cells : List Nat) (address : Nat) : Outcome Nat :=
  match cells[address]? with
  | some value => .value value
  | none => .fault

def checkedRead (cells : List Nat) (start count index : Nat) : Outcome Nat :=
  if index < count then rawRead cells (start + index) else .failed .bounds

theorem checkedRead_exact {cells : List Nat} {start count index : Nat}
    (extent : start + count ≤ cells.length) (inside : index < count) :
    checkedRead cells start count index = .value cells[start + index] := by
  have bounded : start + index < cells.length := by omega
  simp [checkedRead, rawRead, inside, List.getElem?_eq_getElem bounded]

theorem checkedRead_no_fault {cells : List Nat} {start count index : Nat}
    (extent : start + count ≤ cells.length) :
    checkedRead cells start count index ≠ .fault := by
  by_cases inside : index < count
  · rw [checkedRead_exact extent inside]
    simp
  · simp [checkedRead, inside]

def rawWrite (cells : List Nat) (address value : Nat) : Outcome (List Nat) :=
  if address < cells.length then .value (cells.set address value) else .fault

def checkedWrite (cells : List Nat) (start count index value : Nat) : Outcome (List Nat) :=
  if index < count then rawWrite cells (start + index) value else .failed .bounds

theorem checkedWrite_exact {cells : List Nat} {start count index value : Nat}
    (extent : start + count ≤ cells.length) (inside : index < count) :
    checkedWrite cells start count index value = .value (cells.set (start + index) value) := by
  have bounded : start + index < cells.length := by omega
  simp [checkedWrite, rawWrite, inside, bounded]

theorem checkedWrite_no_fault {cells : List Nat} {start count index value : Nat}
    (extent : start + count ≤ cells.length) :
    checkedWrite cells start count index value ≠ .fault := by
  by_cases inside : index < count
  · rw [checkedWrite_exact extent inside]
    simp
  · simp [checkedWrite, inside]

theorem checkedWrite_preserves_extent {before after : List Nat} {start count index value : Nat}
    (execution : checkedWrite before start count index value = .value after) :
    after.length = before.length := by
  unfold checkedWrite rawWrite at execution
  split at execution
  · split at execution
    · cases Outcome.value.inj execution
      simp
    · cases execution
  · cases execution

theorem checkedWrite_frame {before after : List Nat} {start count index value address : Nat}
    (execution : checkedWrite before start count index value = .value after)
    (apart : address ≠ start + index) : after[address]? = before[address]? := by
  unfold checkedWrite rawWrite at execution
  split at execution
  · split at execution
    · cases Outcome.value.inj execution
      simp [Ne.symm apart]
    · cases execution
  · cases execution

example : checkedAdd 255 200 55 = .value 255 := by decide
example : checkedAdd 255 200 56 = .failed .arithmetic := by decide
example : checkedMul 255 17 15 = .value 255 := by decide
example : checkedMul 255 17 16 = .failed .arithmetic := by decide
example : checkedDivision false 17 0 = .failed .arithmetic := by decide
example : checkedShift 8 true 128 1 = .value 0 := by decide
example : checkedShift 8 false 128 8 = .failed .arithmetic := by decide
example : checkedRead [4, 8, 15, 16] 1 2 1 = .value 15 := by decide
example : checkedRead [4, 8, 15, 16] 1 2 2 = .failed .bounds := by decide
example : checkedRead [4, 8] 1 2 1 = .fault := by decide
example : checkedWrite [4, 8, 15, 16] 1 2 1 23 = .value [4, 8, 23, 16] := by decide
example : checkedWrite [4, 8, 15, 16] 1 2 2 23 = .failed .bounds := by decide

end Mettapedia.GSLT.LanguageDef.CheckedScalarOperations
