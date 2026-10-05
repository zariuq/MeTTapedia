import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Order.Compare
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Checked ordinal priorities in finite Cantor normal form

Natural exponents and positive natural coefficients describe priorities below
`ω^ω`. The executable comparison is an independent lexicographic comparison
of monomials. Its agreement with Mathlib's ordinal notation gives the semantic
comparison theorem after descending exponents have been checked.

Well-foundedness is not a fairness certificate: every natural priority lies
below `ω`, so an infinite succession of fresh natural priorities can postpone
an already pending `ω` priority forever.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.OrdinalPriority

abbrev Monomial := Nat × ℕ+
abbrev CantorTerms := List Monomial

def encode : CantorTerms → ONote
  | [] => 0
  | (exponent, coefficient) :: rest => ONote.oadd (ONote.ofNat exponent) coefficient (encode rest)

def compare : CantorTerms → CantorTerms → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (leftExponent, leftCoefficient) :: left, (rightExponent, rightCoefficient) :: right =>
      (_root_.cmp leftExponent rightExponent).then
        ((_root_.cmp (leftCoefficient : Nat) (rightCoefficient : Nat)).then (compare left right))

/-- The column comparisons of paired monomials, in scan order. -/
def columnComparisons (left right : CantorTerms) : List Ordering :=
  (left.zip right).flatMap fun (left, right) =>
    [_root_.cmp left.1 right.1, _root_.cmp (left.2 : Nat) (right.2 : Nat)]

/-- A scan stops at the first unequal column; equal paired prefixes are
ordered by the number of rows. -/
def scanCompare (left right : CantorTerms) : Ordering :=
  ((columnComparisons left right).find? (fun ordering => ordering != .eq)).getD
    (_root_.cmp left.length right.length)

/-- Independent column scanning agrees with recursive monomial comparison,
even before the normal-form check. -/
theorem scanCompare_eq_compare (left right : CantorTerms) :
    scanCompare left right = compare left right := by
  induction left generalizing right with
  | nil => cases right <;> simp [scanCompare, columnComparisons, compare, _root_.cmp, cmpUsing]
  | cons first rest ih =>
      cases right with
      | nil => simp [scanCompare, columnComparisons, compare, _root_.cmp, cmpUsing]
      | cons second tail =>
          rcases first with ⟨leftExponent, leftCoefficient⟩
          rcases second with ⟨rightExponent, rightCoefficient⟩
          cases exponent : _root_.cmp leftExponent rightExponent <;>
            cases coefficient : _root_.cmp (leftCoefficient : Nat) (rightCoefficient : Nat) <;>
            simp [scanCompare, columnComparisons, compare, exponent, coefficient,
              ← ih, Ordering.then]

theorem compare_natural_notations (left right : Nat) :
    ONote.cmp (ONote.ofNat left) (ONote.ofNat right) = _root_.cmp left right := by
  cases left <;> cases right <;>
    simp [ONote.ofNat, ONote.cmp, _root_.cmp, cmpUsing]

theorem compare_encode (left right : CantorTerms) :
    compare left right = ONote.cmp (encode left) (encode right) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons head rest ih =>
      cases right with
      | nil => rfl
      | cons other tail =>
          rcases head with ⟨leftExponent, leftCoefficient⟩
          rcases other with ⟨rightExponent, rightCoefficient⟩
          simp only [compare, encode, ONote.cmp, compare_natural_notations, ih]

def Descending : CantorTerms → Prop
  | [] => True
  | [_] => True
  | (exponent, _) :: (nextExponent, coefficient) :: rest =>
      nextExponent < exponent ∧ Descending ((nextExponent, coefficient) :: rest)

instance descendingDecidable : DecidablePred Descending
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | (exponent, _) :: (nextExponent, coefficient) :: rest => by
      letI := descendingDecidable ((nextExponent, coefficient) :: rest)
      unfold Descending
      infer_instance

theorem normal_cons_iff (exponent : Nat) (coefficient : ℕ+) (rest : CantorTerms) :
    ONote.NF (encode ((exponent, coefficient) :: rest)) ↔
      ONote.NF (encode rest) ∧ ONote.TopBelow (ONote.ofNat exponent) (encode rest) := by
  constructor
  · intro normal
    exact ONote.nfBelow_iff_topBelow.mp normal.snd'
  · intro ⟨normal, below⟩
    exact ONote.NF.oadd (ONote.nf_ofNat exponent) coefficient
      (ONote.nfBelow_iff_topBelow.mpr ⟨normal, below⟩)

theorem normal_iff_descending (terms : CantorTerms) : ONote.NF (encode terms) ↔ Descending terms := by
  induction terms with
  | nil => exact ⟨fun _ => trivial, fun _ => ONote.NF.zero⟩
  | cons head rest ih =>
      rcases head with ⟨exponent, coefficient⟩
      rw [normal_cons_iff, ih]
      cases rest with
      | nil => simp [Descending, encode, ONote.TopBelow]
      | cons other tail =>
          rcases other with ⟨nextExponent, nextCoefficient⟩
          simp only [Descending, encode, ONote.TopBelow, compare_natural_notations,
            _root_.cmp, cmpUsing_eq_lt]
          exact and_comm

def check (terms : CantorTerms) : Option NONote :=
  if descending : Descending terms then
    some ⟨encode terms, (normal_iff_descending terms).mpr descending⟩
  else none

theorem check_eq_none_iff (terms : CantorTerms) : check terms = none ↔ ¬ Descending terms := by
  simp [check]

theorem check_some_encoding {terms : CantorTerms} {priority : NONote}
    (checked : check terms = some priority) : priority.val = encode terms := by
  unfold check at checked
  split_ifs at checked with descending
  · cases checked
    rfl

theorem comparison_semantics {left right : CantorTerms} {leftPriority rightPriority : NONote}
    (leftChecked : check left = some leftPriority) (rightChecked : check right = some rightPriority) :
    (compare left right).Compares leftPriority.repr rightPriority.repr := by
  rw [compare_encode, ← check_some_encoding leftChecked, ← check_some_encoding rightChecked]
  have compared := ONote.cmp_compares leftPriority.val rightPriority.val
  cases outcome : ONote.cmp leftPriority.val rightPriority.val with
  | lt => simpa only [outcome, Ordering.compares_lt, ONote.lt_def, NONote.repr] using compared
  | eq =>
      have equal : leftPriority.val = rightPriority.val := by
        simpa only [outcome, Ordering.compares_eq] using compared
      exact congrArg ONote.repr equal
  | gt => simpa only [outcome, Ordering.compares_gt, ONote.lt_def, NONote.repr] using compared

theorem scan_comparison_semantics {left right : CantorTerms}
    {leftPriority rightPriority : NONote}
    (leftChecked : check left = some leftPriority) (rightChecked : check right = some rightPriority) :
    (scanCompare left right).Compares leftPriority.repr rightPriority.repr := by
  rw [scanCompare_eq_compare]
  exact comparison_semantics leftChecked rightChecked

def omega : NONote := ⟨ONote.oadd (ONote.ofNat 1) 1 0, by infer_instance⟩

theorem natural_below_omega (n : Nat) : (NONote.ofNat n).repr < omega.repr := by
  simp [NONote.repr, NONote.ofNat, omega]

theorem checked_priority_below_omega_pow_omega {terms : CantorTerms} {priority : NONote}
    (checked : check terms = some priority) :
    priority.repr < Ordinal.omega0 ^ Ordinal.omega0 := by
  have encoding := check_some_encoding checked
  cases terms with
  | nil => simp [NONote.repr, encoding, encode, Ordinal.opow_pos]
  | cons head rest =>
      rcases head with ⟨exponent, coefficient⟩
      have normal : ONote.NF (encode ((exponent, coefficient) :: rest)) := encoding ▸ priority.2
      have below := normal.below_of_lt (b := Ordinal.omega0) (by
        simp)
      simpa only [NONote.repr, encoding, encode] using below.repr_lt

theorem infinitely_many_priorities_below_omega :
    {priority : NONote | priority.repr < omega.repr}.Infinite := by
  have injective : Function.Injective NONote.ofNat := by
    intro left right equal
    have representations := congrArg NONote.repr equal
    simpa [NONote.repr, NONote.ofNat] using representations
  apply (Set.infinite_range_of_injective injective).mono
  rintro _ ⟨n, rfl⟩
  exact natural_below_omega n

theorem positive_descending_control : Descending [(3, 2), (1, 5), (0, 1)] := by decide +kernel
theorem increasing_exponents_refused : check [(0, 1), (1, 1)] = none := by decide +kernel
theorem equal_exponents_refused : check [(1, 2), (1, 3)] = none := by decide +kernel
theorem exponent_precedes_coefficient : compare [(1, 1)] [(0, 100)] = .gt := by decide +kernel
theorem coefficient_precedes_tail : compare [(2, 3)] [(2, 2), (1, 100)] = .gt := by decide +kernel
theorem tail_breaks_tie : compare [(2, 3), (0, 1)] [(2, 3)] = .gt := by decide +kernel

end Mettapedia.Algorithms.OrdinalPriority
