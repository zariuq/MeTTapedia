import Mathlib.Tactic

/-!
# Removing an atom a space does not hold: scan, or certified answer

A space removes the rows that unify with a removal pattern.  For a ground
pattern, a row unifies only when it equals the pattern, unless it holds a
variable.  A removal that scans every row to find out costs one step per
row, even when nothing goes; building a mask as long as the space for an
empty receipt costs the same again.

A space that certifies that no row of the pattern's head holds a variable,
and finds no record of the pattern, knows no row equals it.  The removal is
then answered in one step, and an empty receipt costs nothing more.

Modelled here over a space as a list of rows, each row either ground (a
natural number standing for its record) or open (holding a variable,
unifying with every ground pattern of its head):
* `scanRemove_absent_cost`: the scanning removal costs `2 * n` steps for an
  absent ground pattern among `n` rows;
* `certified_iff`: the certificate holds exactly when no row is open and no
  row equals the pattern;
* `certifiedRemove_eq_scanRemove`: whenever the certificate holds, the
  one-step answer leaves the same space the scan leaves.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AbsentRemovalCost

/-- A row of one head: a ground record, or a row holding a variable. -/
inductive Row
  | ground (record : Nat)
  | open_
  deriving DecidableEq

/-- Whether a row unifies with the ground pattern `p`. -/
def unifies (p : Nat) : Row → Bool
  | .ground r => r == p
  | .open_ => true

/-- The rows left after removing every row that unifies with `p`. -/
def scanRemove (p : Nat) (rows : List Row) : List Row :=
  rows.filter (fun r => !unifies p r)

/-- Steps of the scanning removal: one per row read, and one per row of the
mask built after it. -/
def scanCost (rows : List Row) : Nat := rows.length + rows.length

/-- The certificate: no row is open (the head check) and no row equals the
pattern (no record). -/
def certified (p : Nat) (rows : List Row) : Bool :=
  rows.all (fun r => match r with
    | .ground q => q != p
    | .open_ => false)

/-- With the certificate the removal answers at once; otherwise it scans. -/
def certifiedRemove (p : Nat) (rows : List Row) : List Row :=
  if certified p rows then rows else scanRemove p rows

def certifiedCost (p : Nat) (rows : List Row) : Nat :=
  if certified p rows then 1 else scanCost rows

theorem scanRemove_absent_cost (rows : List Row) : scanCost rows = 2 * rows.length := by
  simp [scanCost]; ring

theorem certified_iff (p : Nat) (rows : List Row) :
    certified p rows = true ↔ ∀ r ∈ rows, unifies p r = false := by
  simp only [certified, List.all_eq_true]
  constructor
  · intro h r hr
    have := h r hr
    cases r with
    | ground q => simp_all [unifies]
    | open_ => simp at this
  · intro h r hr
    have := h r hr
    cases r with
    | ground q => simp_all [unifies]
    | open_ => simp [unifies] at this

/-- Whenever the certificate holds, nothing unifies, so the scan removes
nothing and the one-step answer leaves the same rows. -/
theorem certifiedRemove_eq_scanRemove (p : Nat) (rows : List Row) :
    certifiedRemove p rows = scanRemove p rows := by
  unfold certifiedRemove
  split_ifs with h
  · rw [certified_iff] at h
    unfold scanRemove
    symm
    rw [List.filter_eq_self]
    intro r hr
    simp [h r hr]
  · rfl

theorem certifiedCost_le (p : Nat) (rows : List Row) (h : certified p rows = true) :
    certifiedCost p rows = 1 := by
  simp [certifiedCost, h]

end Mettapedia.Machines.AbsentRemovalCost
