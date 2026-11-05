import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Basic

/-!
# Layouts of list values and representation independence

A list value means its **abstraction**: the sequence of its explicit elements
and how it ends, `Nil`, an unbound variable, or an improper tail
(`Abstract`). A **layout** is a physical representation together with
prepend, head, tail, indexing and known length, each specified through the
abstraction (`Layout`).

* **Representation independence.** Values with equal abstractions are
  indistinguishable by every observation that factors through the
  abstraction, within one layout or across two (`Layout.observe_eq`,
  `Layout.agree`), and the layout's own operations are such observations
  (`Layout.head_eq`, `Layout.nth_eq`, `Layout.knownLength_eq`,
  `Layout.cons_abs`). Printing, fingerprints and equality defined on the
  abstraction therefore never see the layout.
* **Three layouts** satisfy the specification: cons cells (`cells`), a flat
  array of elements with its end (`flat`), and chunks of elements
  (`chunked`), where one sequence has many chunkings.
* **The polynomial fingerprint** `Σ Bⁱ g(xᵢ) + Bⁿ T(end)` of an abstraction
  updates in one step on prepend (`fingerprint_cons`), and when `B` is a unit
  the tail's fingerprint is recovered from the whole (`fingerprint_tail`).
* **A physical observation is not exposed.** The number of chunks separates
  two chunkings of one sequence (`Controls.chunk_count_not_abstract`): an
  operation that reads it would make programs depend on the layout.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.Layouts

universe u v w

/-- How a list value ends. -/
inductive Terminal (A : Type u) (V : Type v) where
  | nil
  | var (v : V)
  | improper (tail : A)
  deriving DecidableEq, Repr

/-- The meaning of a list value: its explicit elements and how it ends. -/
abbrev Abstract (A : Type u) (V : Type v) := List A × Terminal A V

variable {A : Type u} {V : Type v}

/-- A physical representation of list values, specified through the
abstraction. -/
structure Layout (A : Type u) (V : Type v) where
  Carrier : Type w
  abs : Carrier → Abstract A V
  cons : A → Carrier → Carrier
  head : Carrier → Option A
  tail : Carrier → Option Carrier
  nth : Carrier → ℕ → Option A
  knownLength : Carrier → ℕ
  abs_cons : ∀ a l, abs (cons a l) = (a :: (abs l).1, (abs l).2)
  head_spec : ∀ l, head l = (abs l).1.head?
  tail_spec : ∀ l, (tail l).map abs = (abs l).1.tail?.map fun rest => (rest, (abs l).2)
  nth_spec : ∀ l i, nth l i = (abs l).1[i]?
  knownLength_spec : ∀ l, knownLength l = (abs l).1.length

namespace Layout

variable (L : Layout.{u, v, w} A V)

/-- An observation of the abstraction, read on a layout. -/
def observe {β : Type*} (f : Abstract A V → β) (l : L.Carrier) : β := f (L.abs l)

/-- **Representation independence.** Values with equal abstractions agree on
every observation of the abstraction. -/
theorem observe_eq {β : Type*} (f : Abstract A V → β) {l₁ l₂ : L.Carrier}
    (same : L.abs l₁ = L.abs l₂) : L.observe f l₁ = L.observe f l₂ := by
  simp [observe, same]

/-- Across two layouts: values with equal abstractions agree on every
observation of the abstraction. -/
theorem agree (L₁ : Layout.{u, v, w} A V) (L₂ : Layout.{u, v, w} A V) {β : Type*}
    (f : Abstract A V → β) {l₁ : L₁.Carrier} {l₂ : L₂.Carrier} (same : L₁.abs l₁ = L₂.abs l₂) :
    L₁.observe f l₁ = L₂.observe f l₂ := by
  simp [observe, same]

/-- The layout's operations are observations of the abstraction. -/
theorem head_eq {l₁ l₂ : L.Carrier} (same : L.abs l₁ = L.abs l₂) : L.head l₁ = L.head l₂ := by
  rw [L.head_spec, L.head_spec, same]

theorem nth_eq {l₁ l₂ : L.Carrier} (same : L.abs l₁ = L.abs l₂) (i : ℕ) :
    L.nth l₁ i = L.nth l₂ i := by
  rw [L.nth_spec, L.nth_spec, same]

theorem knownLength_eq {l₁ l₂ : L.Carrier} (same : L.abs l₁ = L.abs l₂) :
    L.knownLength l₁ = L.knownLength l₂ := by
  rw [L.knownLength_spec, L.knownLength_spec, same]

/-- Prepending preserves equality of abstractions. -/
theorem cons_abs (a : A) {l₁ l₂ : L.Carrier} (same : L.abs l₁ = L.abs l₂) :
    L.abs (L.cons a l₁) = L.abs (L.cons a l₂) := by
  rw [L.abs_cons, L.abs_cons, same]

theorem tail_abs {l₁ l₂ : L.Carrier} (same : L.abs l₁ = L.abs l₂) :
    (L.tail l₁).map L.abs = (L.tail l₂).map L.abs := by
  rw [L.tail_spec, L.tail_spec, same]

end Layout

/-! ## Three layouts -/

/-- Cons cells: one cell per element, ending in a terminal. -/
inductive Cells (A : Type u) (V : Type v) where
  | stop (end_ : Terminal A V)
  | cell (head : A) (tail : Cells A V)

namespace Cells

def abs : Cells A V → Abstract A V
  | .stop end_ => ([], end_)
  | .cell a rest => (a :: (abs rest).1, (abs rest).2)

def nth : Cells A V → ℕ → Option A
  | .cell a _, 0 => some a
  | .cell _ rest, i + 1 => nth rest i
  | .stop _, _ => none

def knownLength : Cells A V → ℕ
  | .stop _ => 0
  | .cell _ rest => knownLength rest + 1

theorem nth_spec : ∀ (l : Cells A V) (i : ℕ), nth l i = (abs l).1[i]?
  | .stop _, i => by cases i <;> rfl
  | .cell a rest, 0 => rfl
  | .cell a rest, i + 1 => by rw [nth, nth_spec rest i]; rfl

theorem knownLength_spec : ∀ l : Cells A V, knownLength l = (abs l).1.length
  | .stop _ => rfl
  | .cell a rest => by rw [knownLength, knownLength_spec rest]; rfl

end Cells

/-- The cons-cell layout. -/
def cells : Layout.{u, v, max u v} A V where
  Carrier := Cells A V
  abs := Cells.abs
  cons := .cell
  head | .cell a _ => some a | .stop _ => none
  tail | .cell _ rest => some rest | .stop _ => none
  nth := Cells.nth
  knownLength := Cells.knownLength
  abs_cons _ _ := rfl
  head_spec l := by cases l <;> rfl
  tail_spec l := by cases l <;> rfl
  nth_spec := Cells.nth_spec
  knownLength_spec := Cells.knownLength_spec

/-- A flat array of the elements with the terminal. -/
def flat : Layout.{u, v, max u v} A V where
  Carrier := Abstract A V
  abs := id
  cons a l := (a :: l.1, l.2)
  head l := l.1.head?
  tail l := l.1.tail?.map fun rest => (rest, l.2)
  nth l i := l.1[i]?
  knownLength l := l.1.length
  abs_cons _ _ := rfl
  head_spec _ := rfl
  tail_spec l := by simp
  nth_spec _ _ := rfl
  knownLength_spec _ := rfl

/-- Chunks of elements: a prepend opens a new chunk; the sequence is the
chunks read in order. -/
def chunked : Layout.{u, v, max u v} A V where
  Carrier := List (List A) × Terminal A V
  abs l := (l.1.flatten, l.2)
  cons a l := ([a] :: l.1, l.2)
  head l := l.1.flatten.head?
  tail l := l.1.flatten.tail?.map fun rest => ([rest], l.2)
  nth l i := l.1.flatten[i]?
  knownLength l := (l.1.map List.length).sum
  abs_cons _ _ := rfl
  head_spec _ := rfl
  tail_spec l := by simp [Option.map_map, Function.comp_def]
  nth_spec _ _ := rfl
  knownLength_spec l := by simp [List.length_flatten]

/-! ## The polynomial fingerprint -/

section Fingerprint

variable {R : Type*} [CommRing R]

/-- `Σ Bⁱ g(xᵢ) + Bⁿ T(end)` of a sequence and its end. -/
def fingerprintOf (base : R) (element : A → R) (terminal : Terminal A V → R)
    (end_ : Terminal A V) : List A → R
  | [] => terminal end_
  | x :: xs => element x + base * fingerprintOf base element terminal end_ xs

/-- The fingerprint of an abstraction. -/
def fingerprint (base : R) (element : A → R) (terminal : Terminal A V → R)
    (value : Abstract A V) : R :=
  fingerprintOf base element terminal value.2 value.1

/-- One step per prepend. -/
theorem fingerprint_cons (base : R) (element : A → R) (terminal : Terminal A V → R)
    (x : A) (xs : List A) (end_ : Terminal A V) :
    fingerprint base element terminal (x :: xs, end_) =
      element x + base * fingerprint base element terminal (xs, end_) := rfl

/-- With an invertible base, the tail's fingerprint is recovered from the
whole. -/
theorem fingerprint_tail (base : Rˣ) (element : A → R) (terminal : Terminal A V → R)
    (x : A) (xs : List A) (end_ : Terminal A V) :
    fingerprint (base : R) element terminal (xs, end_) =
      (fingerprint (base : R) element terminal (x :: xs, end_) - element x) * ↑base⁻¹ := by
  rw [fingerprint_cons, add_sub_cancel_left, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

/-- A layout's fingerprint is an observation of the abstraction. -/
theorem fingerprint_layout_eq (L : Layout.{u, v, w} A V) (base : R) (element : A → R)
    (terminal : Terminal A V → R) {l₁ l₂ : L.Carrier} (same : L.abs l₁ = L.abs l₂) :
    L.observe (fingerprint base element terminal) l₁ = L.observe (fingerprint base element terminal) l₂ :=
  L.observe_eq _ same

end Fingerprint

/-! ## Controls -/

namespace Controls

/-- Two chunkings of `[1 2 3]`: one abstraction, every operation agrees, but
the chunk count, a physical observation, separates them. -/
theorem chunk_count_not_abstract :
    let first : (chunked (A := ℕ) (V := Unit)).Carrier := ([[1, 2], [3]], .nil)
    let second : (chunked (A := ℕ) (V := Unit)).Carrier := ([[1], [2], [3]], .nil)
    chunked.abs first = chunked.abs second ∧
      chunked.nth first 2 = chunked.nth second 2 ∧
      first.1.length ≠ second.1.length := by
  refine ⟨rfl, rfl, by decide⟩

/-- The same sequence in three layouts has one abstraction. -/
theorem three_layouts_one_value :
    (cells (A := ℕ) (V := Unit)).abs (.cell 1 (.cell 2 (.stop .nil))) = ([1, 2], .nil) ∧
      (flat (A := ℕ) (V := Unit)).abs ([1, 2], .nil) = ([1, 2], .nil) ∧
      (chunked (A := ℕ) (V := Unit)).abs ([[1], [2]], .nil) = ([1, 2], .nil) := by
  exact ⟨rfl, rfl, rfl⟩

/-- An open list and a proper list with the same elements differ: the
terminal is part of the abstraction. -/
theorem terminal_matters :
    (([1, 2], .nil) : Abstract ℕ String) ≠ ([1, 2], .var "t") := by
  decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.Layouts
