import Mettapedia.Algorithms.OrdinalPriority
import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCandidateGrades

/-!
# Native ordinal advice: checked atom decoding and comparison

The native `ordinal-cnf` policy reads `(Ordinal ((exponent coefficient) ...))`.
This adapter decodes its integer coordinates, checks strict descent, and
compares the admitted rows by a column scan. The independent monomial
comparison and Mathlib ordinal interpretation establish the meaning of that
scan. Coordinates have no fixed word-size bound in this readout.

The constructor parameter models the native selected symbol. Integer and
big-integer storage, symbol identity, the numeric comparison callback and
pointer/array access remain C implementation obligations. This module proves
the checked mathematical atom boundary, not those memory or ABI obligations.

Ordinal keys are scheduling advice. Refused advice grants no authority to
discard the underlying candidate; neither a well-order nor successful decoding
alone supplies a fairness theorem.

This is an operational-to-extensional comparison. It introduces no dependent
typing judgment for priorities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeOrdinalAdvice

open Mettapedia.Algorithms.OrdinalPriority
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Native row shape, with nonnegative exponent and positive coefficient. -/
def monomial? : Atom → Option Monomial
  | .expression [.grounded (.int exponent), .grounded (.int coefficient)] =>
      if 0 ≤ exponent then
        if positive : 0 < coefficient.toNat then
          some (exponent.toNat, ⟨coefficient.toNat, positive⟩)
        else none
      else none
  | _ => none

def terms? (constructor : String) : Atom → Option CantorTerms
  | .expression [.symbol head, .expression rows] =>
      if head = constructor then rows.mapM monomial? else none
  | _ => none

def checkedTerms? (constructor : String) (atom : Atom) : Option (CantorTerms × NONote) := do
  let terms ← terms? constructor atom
  let priority ← check terms
  some (terms, priority)

/-- A key is available only from an actual completed native score. The
readout neither advances the score nor changes the captured body. -/
def priorityProposal (constructor : String) (score : NativeCandidateGrades.Score) :
    Option (CantorTerms × NONote) :=
  match NativeCandidateGrades.scoreResult score with
  | some (.value atom) => checkedTerms? constructor atom
  | _ => none

theorem pending_score_has_no_proposal (constructor : String) (score : NativeCandidateGrades.Score)
    (pending : NativeCandidateGrades.scoreResult score = none) :
    priorityProposal constructor score = none := by
  simp [priorityProposal, pending]

theorem completed_score_proposal (constructor : String) (score : NativeCandidateGrades.Score)
    (atom : Atom) (completed : NativeCandidateGrades.scoreResult score = some (.value atom)) :
    priorityProposal constructor score = checkedTerms? constructor atom := by
  simp [priorityProposal, completed]

def compareAtoms? (constructor : String) (left right : Atom) : Option Ordering := do
  let (left, _) ← checkedTerms? constructor left
  let (right, _) ← checkedTerms? constructor right
  some (scanCompare left right)

def monomialAtom (term : Monomial) : Atom :=
  .expression [.grounded (.int term.1), .grounded (.int (term.2 : Nat))]

def termsAtom (constructor : String) (terms : CantorTerms) : Atom :=
  .expression [.symbol constructor, .expression (terms.map monomialAtom)]

@[simp] theorem monomial_roundTrip (term : Monomial) :
    monomial? (monomialAtom term) = some term := by
  rcases term with ⟨exponent, ⟨coefficient, positive⟩⟩
  simp [monomial?, monomialAtom, positive]

@[simp] theorem terms_roundTrip (constructor : String) (terms : CantorTerms) :
    terms? constructor (termsAtom constructor terms) = some terms := by
  have rows : (terms.map monomialAtom).mapM monomial? = some terms := by
    induction terms with
    | nil => rfl
    | cons term terms ih => simp [ih]
  simpa [terms?, termsAtom] using rows

theorem checkedTerms_check {constructor : String} {atom : Atom}
    {terms : CantorTerms} {priority : NONote}
    (checked : checkedTerms? constructor atom = some (terms, priority)) :
    check terms = some priority := by
  unfold checkedTerms? at checked
  cases decoded : terms? constructor atom with
  | none => simp [decoded] at checked
  | some actual =>
      cases accepted : check actual with
      | none => simp [decoded, accepted] at checked
      | some value =>
          simp [decoded, accepted] at checked
          rcases checked with ⟨rfl, rfl⟩
          exact accepted

theorem checkedTerms_normal {constructor : String} {atom : Atom}
    {terms : CantorTerms} {priority : NONote}
    (checked : checkedTerms? constructor atom = some (terms, priority)) :
    Descending terms ∧ priority.repr < Ordinal.omega0 ^ Ordinal.omega0 := by
  have accepted := checkedTerms_check checked
  constructor
  · by_contra refused
    have none := (check_eq_none_iff terms).mpr refused
    rw [none] at accepted
    cases accepted
  · exact checked_priority_below_omega_pow_omega accepted

theorem proposed_priority_normal {constructor : String} {score : NativeCandidateGrades.Score}
    {terms : CantorTerms} {priority : NONote}
    (proposed : priorityProposal constructor score = some (terms, priority)) :
    Descending terms ∧ priority.repr < Ordinal.omega0 ^ Ordinal.omega0 := by
  unfold priorityProposal at proposed
  split at proposed
  · exact checkedTerms_normal proposed
  · contradiction

theorem compared_atoms_sound {constructor : String} {left right : Atom}
    {leftTerms rightTerms : CantorTerms} {leftNotation rightNotation : NONote}
    {ordering : Ordering}
    (leftChecked : checkedTerms? constructor left = some (leftTerms, leftNotation))
    (rightChecked : checkedTerms? constructor right = some (rightTerms, rightNotation))
    (compared : compareAtoms? constructor left right = some ordering) :
    ordering.Compares leftNotation.repr rightNotation.repr := by
  simp [compareAtoms?, leftChecked, rightChecked] at compared
  subst ordering
  exact scan_comparison_semantics
    (checkedTerms_check leftChecked) (checkedTerms_check rightChecked)

theorem compared_atom_roundTrip (constructor : String) (left right : CantorTerms)
    (leftNormal : Descending left) (rightNormal : Descending right) :
    compareAtoms? constructor (termsAtom constructor left) (termsAtom constructor right) =
      some (compare left right) := by
  simp [compareAtoms?, checkedTerms?, leftNormal, rightNormal, check, bind, Option.bind,
    scanCompare_eq_compare]

theorem comparison_refused_of_left (constructor : String) (left right : Atom)
    (refused : checkedTerms? constructor left = none) :
    compareAtoms? constructor left right = none := by
  simp [compareAtoms?, refused]

def integer (value : Int) : Atom := .grounded (.int value)

theorem positive_literal_control :
    compareAtoms? "Ordinal" (termsAtom "Ordinal" [(1, 1)])
      (termsAtom "Ordinal" [(0, 100)]) = some .gt := by
  decide +kernel

theorem large_coordinates_compared :
    compareAtoms? "Ordinal" (termsAtom "Ordinal" [(18446744073709551616, 1)])
      (termsAtom "Ordinal" [(18446744073709551615, 18446744073709551616)]) = some .gt := by
  decide +kernel

theorem zero_coefficient_refused :
    checkedTerms? "Ordinal" (.expression [.symbol "Ordinal",
      .expression [.expression [integer 1, integer 0]]]) = none := by
  decide +kernel

theorem negative_coordinate_refused :
    checkedTerms? "Ordinal" (.expression [.symbol "Ordinal",
      .expression [.expression [integer (-1), integer 1]]]) = none := by
  decide +kernel

theorem duplicate_exponent_refused :
    checkedTerms? "Ordinal" (termsAtom "Ordinal" [(1, 2), (1, 3)]) = none := by
  decide +kernel

theorem other_constructor_refused :
    checkedTerms? "Ordinal" (termsAtom "Other" [(1, 1)]) = none := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeOrdinalAdvice
