import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Lean.Elab.Tactic.Omega

/-!
# Finite coordinate buffers

Shape-valid flat buffers are compared with finite functions and Mathlib matrices.
The executable operations check both dimensions and physical buffer lengths;
failed checks yield no truncated or zero-padded result. Row-major decoding is
inverse to encoding on valid buffers, and the ordered contraction loop agrees
with matrix multiplication, including rectangular and empty dimensions.

The comparison assumes the stated arithmetic laws. It does not establish a
refinement of a language evaluator, a floating-point implementation or an
arbitrary program-supplied algebra descriptor.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.FiniteCoordinateBuffer

universe u
variable {R : Type u}

/-- A failed shape comparison has no truncated successful result. -/
def zipWith? (operation : R → R → R) : List R → List R → Option (List R)
  | [], [] => some []
  | left :: later, right :: remaining =>
      (zipWith? operation later remaining).map (operation left right :: ·)
  | _, _ => none

theorem zipWith?_ofFn (operation : R → R → R) {n : Nat}
    (left right : Fin n → R) :
    zipWith? operation (List.ofFn left) (List.ofFn right) =
      some (List.ofFn fun index => operation (left index) (right index)) := by
  induction n with
  | zero => simp [zipWith?]
  | succ n ih =>
      simp only [List.ofFn_succ, zipWith?]
      rw [ih]
      rfl

theorem zipWith?_shape_refusal (operation : R → R → R)
    (left right : List R) (different : left.length ≠ right.length) :
    zipWith? operation left right = none := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [zipWith?]
  | cons head rest ih =>
      cases right with
      | nil => rfl
      | cons other later =>
          have unequal : rest.length ≠ later.length := by simpa using different
          simp [zipWith?, ih later unequal]

/-- A finite ordered loop, independent of any matrix interpretation. -/
def sumFrom [AddMonoid R] (read : Nat → R) (start : Nat) : Nat → R
  | 0 => 0
  | count + 1 => read start + sumFrom read (start + 1) count

theorem sumFrom_exact [AddCommMonoid R] (read : Nat → R) (start count : Nat) :
    sumFrom read start count = ∑ offset : Fin count, read (start + offset.val) := by
  induction count generalizing start with
  | zero => simp [sumFrom]
  | succ count ih =>
      simp only [sumFrom, Fin.sum_univ_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
      rw [ih]
      congr 1
      apply Finset.sum_congr rfl
      intro index _
      congr 1
      omega

def tabulateFrom (read : Nat → R) (start : Nat) : Nat → List R
  | 0 => []
  | count + 1 => read start :: tabulateFrom read (start + 1) count

theorem tabulateFrom_exact (read : Nat → R) (start count : Nat) :
    tabulateFrom read start count = List.ofFn fun offset : Fin count =>
      read (start + offset.val) := by
  induction count generalizing start with
  | zero => simp [tabulateFrom]
  | succ count ih =>
      simp only [tabulateFrom, List.ofFn_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
      rw [ih]
      congr 1
      apply congrArg List.ofFn
      funext offset
      congr 1
      omega

def rowsFrom (read : Nat → Nat → R) (start : Nat) (columns : Nat) : Nat → List R
  | 0 => []
  | count + 1 => tabulateFrom (read start) 0 columns ++ rowsFrom read (start + 1) columns count

theorem rowsFrom_exact (read : Nat → Nat → R) (start columns count : Nat) :
    rowsFrom read start columns count =
      (List.ofFn fun offset : Fin count =>
        List.ofFn fun column : Fin columns => read (start + offset.val) column.val).flatten := by
  induction count generalizing start with
  | zero => simp [rowsFrom]
  | succ count ih =>
      simp only [rowsFrom, List.ofFn_succ, List.flatten_cons, Fin.val_zero,
        Nat.add_zero, Fin.val_succ]
      rw [tabulateFrom_exact, ih]
      simp only [Nat.zero_add]
      congr 1
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext offset
      apply congrArg List.ofFn
      funext column
      congr 1
      omega

/-- Row-major coordinate order; the columns are the fast index. -/
def rowMajor {m n : Nat} (matrix : Matrix (Fin m) (Fin n) R) : List R :=
  List.ofFn fun index : Fin (m * n) =>
    matrix (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2

@[simp] theorem rowMajor_length {m n : Nat} (matrix : Matrix (Fin m) (Fin n) R) :
    (rowMajor matrix).length = m * n := List.length_ofFn

theorem rowMajor_eq_rows {m n : Nat} (matrix : Matrix (Fin m) (Fin n) R) :
    rowMajor matrix = (List.ofFn fun row : Fin m => List.ofFn (matrix row)).flatten := by
  unfold rowMajor
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext column
  have position : ∀ proof : row.val * n + column.val < m * n,
      (⟨row.val * n + column.val, proof⟩ : Fin (m * n)) =
        finProdFinEquiv (row, column) := by
    intro proof
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [position, Equiv.symm_apply_apply]

theorem rowMajor_getD {m n : Nat} (matrix : Matrix (Fin m) (Fin n) R)
    (row : Fin m) (column : Fin n) (fallback : R) :
    (rowMajor matrix).getD (row.val * n + column.val) fallback = matrix row column := by
  let index : Fin (m * n) := finProdFinEquiv (row, column)
  have position : row.val * n + column.val = index.val := by
    simp [index, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [position]
  have within : index.val < (rowMajor matrix).length := by simp
  have read := List.getD_eq_getElem (rowMajor matrix) fallback within
  calc
    (rowMajor matrix).getD index.val fallback = (rowMajor matrix)[index.val] := read
    _ = matrix row column := by
      simp only [rowMajor, List.getElem_ofFn]
      change matrix (finProdFinEquiv.symm (finProdFinEquiv (row, column))).1
        (finProdFinEquiv.symm (finProdFinEquiv (row, column))).2 = matrix row column
      rw [Equiv.symm_apply_apply]

/-- Decoding is total; valid buffers never use the fallback value. -/
def toMatrix [Zero R] (m n : Nat) (entries : List R) : Matrix (Fin m) (Fin n) R :=
  fun row column => entries.getD (row.val * n + column.val) 0

@[simp] theorem toMatrix_rowMajor [Zero R] {m n : Nat}
    (matrix : Matrix (Fin m) (Fin n) R) :
    toMatrix m n (rowMajor matrix) = matrix := by
  funext row column
  exact rowMajor_getD matrix row column 0

theorem rowMajor_injective [Zero R] {m n : Nat} :
    Function.Injective (rowMajor (R := R) (m := m) (n := n)) := by
  intro left right same
  have decoded := congrArg (toMatrix m n) same
  simpa using decoded

theorem rowMajor_toMatrix [Zero R] (m n : Nat) (entries : List R)
    (valid : entries.length = m * n) :
    rowMajor (toMatrix m n entries) = entries := by
  apply List.ext_getElem
  · simp [valid]
  · intro index before after
    let bounded : Fin (m * n) := ⟨index, by simpa [valid] using after⟩
    let pair : Fin m × Fin n := finProdFinEquiv.symm bounded
    have position : pair.1.val * n + pair.2.val = index := by
      have roundTrip := congrArg Fin.val (finProdFinEquiv.apply_symm_apply bounded)
      simpa [pair, bounded, finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using roundTrip
    simp only [rowMajor, List.getElem_ofFn, toMatrix]
    change entries.getD (pair.1.val * n + pair.2.val) 0 = entries[index]
    rw [position, List.getD_eq_getElem entries 0 after]

/-- The authored dot loop loads two flat coordinates before its next iteration. -/
def contractCell [Semiring R] (left right : List R) (inner columns row column : Nat) : R :=
  sumFrom (fun position =>
    left.getD (row * inner + position) 0 *
      right.getD (position * columns + column) 0) 0 inner

theorem contractCell_rowMajor [Semiring R] {m n k : Nat}
    (left : Matrix (Fin m) (Fin n) R) (right : Matrix (Fin n) (Fin k) R)
    (row : Fin m) (column : Fin k) :
    contractCell (rowMajor left) (rowMajor right) n k row.val column.val =
      (left * right) row column := by
  rw [contractCell, sumFrom_exact, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro position _
  simp only [Nat.zero_add]
  rw [rowMajor_getD left row position 0, rowMajor_getD right position column 0]

/-- The output loop enumerates rows and columns without changing factor order. -/
def contract [Semiring R] (rows inner columns : Nat) (left right : List R) : List R :=
  rowsFrom (contractCell left right inner columns) 0 columns rows

@[simp] theorem rowsFrom_length (read : Nat → Nat → R)
    (start columns count : Nat) :
    (rowsFrom read start columns count).length = count * columns := by
  induction count generalizing start with
  | zero => simp [rowsFrom]
  | succ count ih =>
      simp only [rowsFrom, List.length_append, tabulateFrom_exact, List.length_ofFn, ih]
      rw [Nat.succ_mul, Nat.add_comm]

@[simp] theorem contract_length [Semiring R]
    (rows inner columns : Nat) (left right : List R) :
    (contract rows inner columns left right).length = rows * columns := by
  exact rowsFrom_length _ _ _ _

theorem contract_rowMajor [Semiring R] {m n k : Nat}
    (left : Matrix (Fin m) (Fin n) R) (right : Matrix (Fin n) (Fin k) R) :
    contract m n k (rowMajor left) (rowMajor right) = rowMajor (left * right) := by
  rw [contract, rowsFrom_exact, rowMajor_eq_rows (left * right)]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext column
  simpa using contractCell_rowMajor left right row column

structure Dense (R : Type u) where
  rows : Nat
  columns : Nat
  entries : List R
  deriving DecidableEq, Repr

def Dense.Valid (buffer : Dense R) : Prop :=
  buffer.entries.length = buffer.rows * buffer.columns

instance (buffer : Dense R) : Decidable buffer.Valid :=
  inferInstanceAs (Decidable (buffer.entries.length = buffer.rows * buffer.columns))

def Dense.encode {m n : Nat} (matrix : Matrix (Fin m) (Fin n) R) : Dense R :=
  ⟨m, n, rowMajor matrix⟩

@[simp] theorem Dense.encode_valid {m n : Nat} (matrix : Matrix (Fin m) (Fin n) R) :
    (Dense.encode matrix).Valid := rowMajor_length matrix

def Dense.add? [Add R] (left right : Dense R) : Option (Dense R) :=
  if left.rows = right.rows ∧ left.columns = right.columns ∧ left.Valid ∧ right.Valid then
    (zipWith? (· + ·) left.entries right.entries).map (Dense.mk left.rows left.columns)
  else none

def Dense.multiply? [Semiring R] (left right : Dense R) : Option (Dense R) :=
  if left.columns = right.rows ∧ left.Valid ∧ right.Valid then
    some ⟨left.rows, right.columns,
      contract left.rows left.columns right.columns left.entries right.entries⟩
  else none

theorem Dense.add_encode [Add R] {m n : Nat}
    (left right : Matrix (Fin m) (Fin n) R) :
    Dense.add? (Dense.encode left) (Dense.encode right) = some (Dense.encode (left + right)) := by
  simp only [Dense.add?, Dense.encode, Dense.Valid, rowMajor_length, and_self, if_true]
  rw [rowMajor, rowMajor, zipWith?_ofFn]
  rfl

theorem Dense.multiply_encode [Semiring R] {m n k : Nat}
    (left : Matrix (Fin m) (Fin n) R) (right : Matrix (Fin n) (Fin k) R) :
    Dense.multiply? (Dense.encode left) (Dense.encode right) =
      some (Dense.encode (left * right)) := by
  simp only [Dense.multiply?, Dense.encode, Dense.Valid, rowMajor_length, and_self, if_true]
  rw [contract_rowMajor]

/-- Every shape-valid physical buffer has its own exact coordinate interpretation. -/
theorem Dense.valid_encode_decode [Zero R] (buffer : Dense R) (valid : buffer.Valid) :
    Dense.encode (toMatrix buffer.rows buffer.columns buffer.entries) = buffer := by
  cases buffer with
  | mk rows columns entries =>
      simp only [Dense.encode]
      congr 1
      exact rowMajor_toMatrix rows columns entries valid

theorem Dense.multiply_shape_refusal [Semiring R] (left right : Dense R)
    (different : left.columns ≠ right.rows) : Dense.multiply? left right = none := by
  simp [Dense.multiply?, different]

theorem Dense.multiply_invalid_refusal [Semiring R] (left right : Dense R)
    (invalid : ¬ left.Valid ∨ ¬ right.Valid) : Dense.multiply? left right = none := by
  rcases invalid with invalid | invalid <;> simp [Dense.multiply?, invalid]

theorem Dense.multiply_associative [Semiring R] {m n k p : Nat}
    (left : Matrix (Fin m) (Fin n) R) (middle : Matrix (Fin n) (Fin k) R)
    (right : Matrix (Fin k) (Fin p) R) :
    ((Dense.multiply? (Dense.encode left) (Dense.encode middle)).bind
      (fun first => Dense.multiply? first (Dense.encode right))) =
    ((Dense.multiply? (Dense.encode middle) (Dense.encode right)).bind
      (fun second => Dense.multiply? (Dense.encode left) second)) := by
  simp only [Dense.multiply_encode, Option.bind_some]
  rw [Matrix.mul_assoc]

theorem empty_inner_contraction [Semiring R] (m k : Nat) :
    contract m 0 k ([] : List R) [] = List.replicate (m * k) 0 := by
  simp [contract, rowsFrom_exact, contractCell, sumFrom]

def upper : Dense Nat := ⟨2, 2, [1, 1, 0, 1]⟩
def lower : Dense Nat := ⟨2, 2, [1, 0, 1, 1]⟩

theorem matrix_order_control :
    Dense.multiply? upper lower = some ⟨2, 2, [2, 1, 1, 1]⟩ ∧
      Dense.multiply? lower upper = some ⟨2, 2, [1, 1, 1, 2]⟩ ∧
      Dense.multiply? upper lower ≠ Dense.multiply? lower upper := by
  decide +kernel

theorem rectangular_contraction_control :
    Dense.multiply? (⟨2, 3, [1, 2, 3, 4, 5, 6]⟩ : Dense Nat)
      ⟨3, 1, [7, 8, 9]⟩ = some ⟨2, 1, [50, 122]⟩ := by decide +kernel

theorem dimensions_are_not_entry_count :
    Dense.multiply? (⟨1, 4, [1, 2, 3, 4]⟩ : Dense Nat)
      ⟨2, 2, [1, 2, 3, 4]⟩ = none := by decide +kernel

theorem invalid_buffer_is_not_zero_padding :
    Dense.multiply? (⟨2, 2, [1, 2, 3]⟩ : Dense Nat) lower = none := by decide +kernel

theorem empty_dimensions_control :
    Dense.multiply? (⟨2, 0, []⟩ : Dense Nat) ⟨0, 3, []⟩ =
      some ⟨2, 3, [0, 0, 0, 0, 0, 0]⟩ ∧
    Dense.multiply? (⟨0, 2, []⟩ : Dense Nat) upper = some ⟨0, 2, []⟩ ∧
    Dense.multiply? upper ⟨2, 0, []⟩ = some ⟨2, 0, []⟩ := by decide +kernel

end Mettapedia.Algebra.FiniteCoordinateBuffer
