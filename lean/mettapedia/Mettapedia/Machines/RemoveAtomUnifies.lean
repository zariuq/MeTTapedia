import Mathlib.Tactic

/-!
# Removing by unification: every unifying row goes

PeTTa's `remove-atom`, as stable-fixed SWI-PeTTa removes, takes every
stored row that unifies with its pattern: removing `(p a)` takes a stored
`(p $x)` too, and a pattern with a variable takes every row it meets.  It
answers whether any row went.

A space removes by a scan: each row is read once, dropped when it unifies
with the pattern, and a flag records that something went.  Modelled over a
space as a list of rows and any decidable unification relation `u`:
* `scan_left`: the rows the scan leaves are exactly the rows that do not
  unify, in their order and multiplicity;
* `scan_answer`: the scan answers true exactly when some row unifies;
* `scan_none_left`: no row it leaves unifies with the pattern;
* `scan_again`: a second removal of the same pattern answers false and leaves
  the space as it is;
* `removeFirst_leaves_unifier`: removing only the first unifying row, over
  flat rows, leaves a row the pattern still unifies with, where the scan
  leaves none.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RemoveAtomUnifies

variable {Pat Row : Type}

/-- The removal's scan: each row read once, dropped when it unifies with the
pattern; the flag records whether any row went. -/
def scan (u : Pat → Row → Bool) (p : Pat) : List Row → List Row × Bool
  | [] => ([], false)
  | r :: rs =>
      if u p r then ((scan u p rs).1, true)
      else (r :: (scan u p rs).1, (scan u p rs).2)

theorem scan_left (u : Pat → Row → Bool) (p : Pat) (rows : List Row) :
    (scan u p rows).1 = rows.filter (fun r => !u p r) := by
  induction rows with
  | nil => rfl
  | cons r rs ih => by_cases h : u p r = true <;> simp [scan, h, ih]

theorem scan_answer (u : Pat → Row → Bool) (p : Pat) (rows : List Row) :
    (scan u p rows).2 = rows.any (u p) := by
  induction rows with
  | nil => rfl
  | cons r rs ih => by_cases h : u p r = true <;> simp [scan, h, ih]

theorem scan_none_left (u : Pat → Row → Bool) (p : Pat) (rows : List Row) :
    ∀ r ∈ (scan u p rows).1, u p r = false := by
  intro r hr
  rw [scan_left] at hr
  simpa using (List.mem_filter.mp hr).2

theorem scan_again (u : Pat → Row → Bool) (p : Pat) (rows : List Row) :
    scan u p (scan u p rows).1 = ((scan u p rows).1, false) := by
  have keep : ∀ r ∈ (scan u p rows).1, (!u p r) = true := by
    intro r hr
    simp [scan_none_left u p rows r hr]
  have left : (scan u p (scan u p rows).1).1 = (scan u p rows).1 := by
    rw [scan_left u p (scan u p rows).1]
    exact List.filter_eq_self.mpr keep
  have answer : (scan u p (scan u p rows).1).2 = false := by
    rw [scan_answer]
    simpa using fun r hr => scan_none_left u p rows r hr
  exact Prod.ext left answer

/-! ## Removing only the first unifying row is another operation -/

/-- A flat row's field: a constant or a variable. -/
inductive Field
  | const (c : Nat)
  | var
  deriving DecidableEq

/-- Unification of flat rows field by field: a variable meets anything, two
constants meet when equal (variables occur once in these rows). -/
def unifies : List Field → List Field → Bool
  | [], [] => true
  | .var :: ps, _ :: rs => unifies ps rs
  | _ :: ps, .var :: rs => unifies ps rs
  | .const a :: ps, .const b :: rs => a == b && unifies ps rs
  | _, _ => false

/-- Removing the first unifying row only. -/
def removeFirst (u : Pat → Row → Bool) (p : Pat) : List Row → List Row
  | [] => []
  | r :: rs => if u p r then rs else r :: removeFirst u p rs

/-- `(p $x)` and `(p a)` stored, `(p a)` removed: removing the first
unifying row leaves `(p a)`, which the pattern still unifies with; the scan
leaves nothing. -/
theorem removeFirst_leaves_unifier :
    let rows := [[Field.const 0, .var], [Field.const 0, .const 1]]
    let pat := [Field.const 0, .const 1]
    removeFirst unifies pat rows = [[Field.const 0, .const 1]] ∧
    unifies pat [Field.const 0, .const 1] = true ∧
    (scan unifies pat rows).1 = [] := by
  decide

end Mettapedia.Machines.RemoveAtomUnifies
