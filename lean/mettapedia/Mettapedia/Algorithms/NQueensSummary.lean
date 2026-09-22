import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-!
# Exact column/diagonal summaries for the N-queens safety scan

The MeTTa benchmark safety scans keep the newest queen at the head and start
the row distance at one. One scan tests absolute column difference; the other
tests both signed differences. This module proves their equivalence and the
equivalence to incremental column/diagonal summaries for arbitrary partial
boards. Rows and diagonal keys use integers, never truncated subtraction.

The list-enumeration theorem preserves order and duplicate candidate
occurrences. It is a mathematical representation result, not an executable
MeTTa or C adequacy claim or a performance measurement.
-/

namespace Mettapedia.Algorithms.NQueensSummary

set_option autoImplicit false

/-- The signed-difference scan, with the most recently placed queen first. -/
def ScanSafe (column : Int) : List Int → Nat → Prop
  | [], _ => True
  | head :: tail, distance =>
      column ≠ head ∧ column - head ≠ (distance : Int) ∧
        head - column ≠ (distance : Int) ∧ ScanSafe column tail (distance + 1)

instance scanSafeDecidable (column : Int) (placed : List Int) (distance : Nat) :
    Decidable (ScanSafe column placed distance) := by
  induction placed generalizing distance with
  | nil => exact isTrue trivial
  | cons head tail ih =>
    haveI := ih (distance + 1)
    exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ScanSafe column tail (distance + 1)))

/-- The absolute-difference variant used by the other benchmark. -/
def AbsScanSafe (column : Int) : List Int → Nat → Prop
  | [], _ => True
  | head :: tail, distance =>
      column ≠ head ∧ |column - head| ≠ (distance : Int) ∧
        AbsScanSafe column tail (distance + 1)

theorem absScanSafe_iff (column : Int) (placed : List Int) (distance : Nat) :
    AbsScanSafe column placed distance ↔ ScanSafe column placed distance := by
  induction placed generalizing distance with
  | nil => rfl
  | cons head tail ih =>
    have absolute : |column - head| = (distance : Int) ↔
        column - head = (distance : Int) ∨ head - column = (distance : Int) := by
      rw [abs_eq (Int.natCast_nonneg distance)]
      omega
    simp only [AbsScanSafe, ScanSafe, ih, ne_eq, absolute, not_or]
    tauto

/-- The battery workload's nested-if computation, including both signed tests. -/
def scanGuard (column : Int) : List Int → Nat → Bool
  | [], _ => true
  | head :: tail, distance =>
      if column = head then false
      else if column - head = (distance : Int) then false
      else if head - column = (distance : Int) then false
      else scanGuard column tail (distance + 1)

theorem scanGuard_eq_decide (column : Int) (placed : List Int) (distance : Nat) :
    scanGuard column placed distance = decide (ScanSafe column placed distance) := by
  induction placed generalizing distance with
  | nil => rfl
  | cons head tail ih =>
    by_cases columnHit : column = head
    · simp [scanGuard, ScanSafe, columnHit]
    by_cases differenceHit : column - head = (distance : Int)
    · simp [scanGuard, ScanSafe, columnHit, differenceHit]
    by_cases reverseHit : head - column = (distance : Int)
    · simp [scanGuard, ScanSafe, columnHit, differenceHit, reverseHit]
    simp [scanGuard, ScanSafe, columnHit, differenceHit, reverseHit, ih]

/-- The flat-list workload's absolute-difference computation. -/
def absScanGuard (column : Int) : List Int → Nat → Bool
  | [], _ => true
  | head :: tail, distance =>
      if column = head then false
      else if |column - head| = (distance : Int) then false
      else absScanGuard column tail (distance + 1)

theorem absScanGuard_eq_true (column : Int) (placed : List Int) (distance : Nat) :
    absScanGuard column placed distance = true ↔ AbsScanSafe column placed distance := by
  induction placed generalizing distance with
  | nil => simp [absScanGuard, AbsScanSafe]
  | cons head tail ih =>
    by_cases columnHit : column = head
    · simp [absScanGuard, AbsScanSafe, columnHit]
    by_cases diagonalHit : |column - head| = (distance : Int)
    · simp [absScanGuard, AbsScanSafe, columnHit, diagonalHit]
    simp [absScanGuard, AbsScanSafe, columnHit, diagonalHit, ih]

theorem guards_equal (column : Int) (placed : List Int) (distance : Nat) :
    absScanGuard column placed distance = scanGuard column placed distance := by
  apply Bool.eq_iff_iff.mpr
  rw [absScanGuard_eq_true, scanGuard_eq_decide, decide_eq_true_eq, absScanSafe_iff]

structure Summary where
  columns : Finset Int
  sumDiagonals : Finset Int
  differenceDiagonals : Finset Int
  deriving DecidableEq

def empty : Summary := ⟨∅, ∅, ∅⟩

def insert (row column : Int) (summary : Summary) : Summary :=
  ⟨Insert.insert column summary.columns,
    Insert.insert (column + row) summary.sumDiagonals,
    Insert.insert (column - row) summary.differenceDiagonals⟩

/-- `row` is the row of the head queen, decreasing along the stored list. -/
def summarize : Int → List Int → Summary
  | _, [] => empty
  | row, head :: tail => insert row head (summarize (row - 1) tail)

def AllowedAt (row column : Int) (summary : Summary) : Prop :=
  column ∉ summary.columns ∧ column + row ∉ summary.sumDiagonals ∧
    column - row ∉ summary.differenceDiagonals

instance allowedAtDecidable (row column : Int) (summary : Summary) :
    Decidable (AllowedAt row column summary) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The summary test is exact even for an arbitrary integer row origin and an
arbitrary initial nonnegative distance; no partial-board safety assumption is
needed for this local representation law. -/
theorem scanSafe_iff_allowedAt (column : Int) (placed : List Int)
    (row : Int) (distance : Nat) :
    ScanSafe column placed distance ↔
      AllowedAt (row + (distance : Int)) column (summarize row placed) := by
  induction placed generalizing row distance with
  | nil => simp [ScanSafe, AllowedAt, summarize, empty]
  | cons head tail ih =>
    have tailLaw := ih (row - 1) (distance + 1)
    have sameRow : row - 1 + ((distance + 1 : Nat) : Int) = row + (distance : Int) := by
      omega
    rw [sameRow] at tailLaw
    have sumCollision : column + (row + (distance : Int)) = head + row ↔
        head - column = (distance : Int) := by omega
    have differenceCollision : column - (row + (distance : Int)) = head - row ↔
        column - head = (distance : Int) := by omega
    simp only [ScanSafe, tailLaw, summarize, insert, AllowedAt, Finset.mem_insert,
      not_or, sumCollision, differenceCollision]
    tauto

/-- Canonical row origin: placed queens occupy rows zero through length-1. -/
def ofPlaced (placed : List Int) : Summary :=
  summarize ((placed.length : Int) - 1) placed

theorem scanSafe_iff_summary (column : Int) (placed : List Int) :
    ScanSafe column placed 1 ↔ AllowedAt (placed.length : Int) column (ofPlaced placed) := by
  simpa [ofPlaced] using scanSafe_iff_allowedAt column placed ((placed.length : Int) - 1) 1

/-- One placement updates the summary without traversing the old board. -/
theorem ofPlaced_cons (column : Int) (placed : List Int) :
    ofPlaced (column :: placed) = insert (placed.length : Int) column (ofPlaced placed) := by
  simp [ofPlaced, summarize]

/-- Board-size restrictions are orthogonal to the representation change. -/
def Permitted (size : Nat) (placed : List Int) (column : Int) : Prop :=
  placed.length < size ∧ 1 ≤ column ∧ column ≤ (size : Int) ∧ ScanSafe column placed 1

instance permittedDecidable (size : Nat) (placed : List Int) (column : Int) :
    Decidable (Permitted size placed column) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ScanSafe column placed 1))

theorem permitted_iff_summary (size : Nat) (placed : List Int) (column : Int) :
    Permitted size placed column ↔
      placed.length < size ∧ 1 ≤ column ∧ column ≤ (size : Int) ∧
        AllowedAt (placed.length : Int) column (ofPlaced placed) := by
  simp only [Permitted, scanSafe_iff_summary]

def scanChoices (candidates placed : List Int) : List Int :=
  candidates.filter (fun column => scanGuard column placed 1)

def summaryChoices (candidates : List Int) (row : Int) (summary : Summary) : List Int :=
  candidates.filter (fun column => decide (AllowedAt row column summary))

/-- Equality of lists, not just membership: candidate occurrences are retained. -/
theorem choices_equal (candidates placed : List Int) :
    scanChoices candidates placed =
      summaryChoices candidates (placed.length : Int) (ofPlaced placed) := by
  simp only [scanChoices, summaryChoices, scanGuard_eq_decide, scanSafe_iff_summary]

def enumerateScan (candidates : List Int) : Nat → List Int → List (List Int)
  | 0, placed => [placed]
  | remaining + 1, placed =>
      (scanChoices candidates placed).flatMap
        (fun column => enumerateScan candidates remaining (column :: placed))

/-- The summary version threads only the incrementally updated attack summary
alongside the retained board. Candidate order is unchanged. -/
def enumerateSummary (candidates : List Int) : Nat → List Int → Summary → List (List Int)
  | 0, placed, _ => [placed]
  | remaining + 1, placed, summary =>
      (summaryChoices candidates (placed.length : Int) summary).flatMap
        (fun column => enumerateSummary candidates remaining (column :: placed)
          (insert (placed.length : Int) column summary))

/-- Arbitrary depth and arbitrary partial boards: the entire answer list is
preserved, including its order and all duplicate solution occurrences. -/
theorem enumeration_equal (candidates : List Int) (remaining : Nat) (placed : List Int) :
    enumerateScan candidates remaining placed =
      enumerateSummary candidates remaining placed (ofPlaced placed) := by
  induction remaining generalizing placed with
  | zero => rfl
  | succ remaining ih =>
    simp only [enumerateScan, enumerateSummary, choices_equal]
    apply congrArg ((summaryChoices candidates (placed.length : Int) (ofPlaced placed)).flatMap)
    funext column
    rw [← ofPlaced_cons]
    exact ih (column :: placed)

end Mettapedia.Algorithms.NQueensSummary
