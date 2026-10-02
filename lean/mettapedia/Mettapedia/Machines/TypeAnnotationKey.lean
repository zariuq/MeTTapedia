import Mettapedia.Machines.Cursor.ListCells

/-!
# Conservative keys for relational type declarations

Symbols and lists with a symbolic first element supply a key. Open heads
retain the wildcard bucket. The key deliberately does not decide matching:
it only rules out a branch whose declaration cannot share a substitution
instance with the requested subject. Hash collisions retain extra candidates.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TypeAnnotationKey

open Cursor.ListCells

def key : PT → Option Nat
  | .atom s => some s
  | .cons (.atom s) _ => some s
  | _ => none

theorem key_subst {term : PT} {name : Nat} (known : key term = some name)
    (θ : Nat → PT) : key (term.subst θ) = some name := by
  cases term with
  | atom s => exact known
  | var v => cases known
  | nil => cases known
  | cons h t =>
      cases h <;> simp_all [key, PT.subst]

def candidate (left right : PT) : Bool :=
  match key left, key right with
  | some a, some b => a == b
  | _, _ => true

theorem candidate_complete (left right : PT) (θ : Nat → PT)
    (unifies : left.subst θ = right.subst θ) : candidate left right = true := by
  cases hl : key left with
  | none => simp [candidate, hl]
  | some a =>
      cases hr : key right with
      | none => simp [candidate, hl, hr]
      | some b =>
          have same : a = b := by
            have ha := key_subst hl θ
            have hb := key_subst hr θ
            rw [unifies] at ha
            exact Option.some.inj (ha.symm.trans hb)
          simp [candidate, hl, hr, same]

/-- Candidate selection preserves the complete occurrence sequence, including
duplicates. It does not publish bindings or run the consumer. -/
theorem filter_occurrences (subject : PT) (rows : List PT) (θ : Nat → PT) :
    (rows.filter (candidate subject)).filter
        (fun row => decide (subject.subst θ = row.subst θ)) =
      rows.filter (fun row => decide (subject.subst θ = row.subst θ)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases h : subject.subst θ = row.subst θ
      · have hc := candidate_complete subject row θ h
        have hp : decide (subject.subst θ = row.subst θ) = true := by simp [h]
        simp only [List.filter_cons, hc, hp, ↓reduceIte]
        exact congrArg (List.cons row) ih
      · have hp : decide (subject.subst θ = row.subst θ) = false := by simp [h]
        cases hc : candidate subject row <;>
          simp only [List.filter_cons, hc, hp, Bool.false_eq_true,
            ↓reduceIte] <;> exact ih

example : candidate (.cons (.atom 1) (.var 0)) (.cons (.atom 2) .nil) = false := rfl
example : candidate (.atom 1) (.var 0) = true := rfl
example : candidate (.cons (.atom 1) .nil) (.cons (.var 0) .nil) = true := rfl
example : candidate (.atom 1) (.cons (.atom 1) .nil) = true := rfl

/-- A symbolic declaration cannot refine any variable inside a list subject,
even when that list has an open tail. Function signatures are queried on the
head separately; this law concerns the direct subject-declaration branch. -/
theorem symbol_list_clash (name : Nat) (head tail : PT) (θ : Nat → PT) :
    (PT.cons head tail).subst θ ≠ (PT.atom name).subst θ := by
  simp [PT.subst]

def symbolOnly : PT → Bool
  | .atom _ => true
  | _ => false

/-- The computed symbol-only declaration certificate excludes the whole
direct-declaration frontier for a compound subject. -/
theorem symbol_declarations_exclude_list (rows : List PT)
    (certified : rows.all symbolOnly = true) (head tail : PT) (θ : Nat → PT) :
    rows.filter (fun row => decide ((PT.cons head tail).subst θ = row.subst θ)) = [] := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.all_cons, Bool.and_eq_true] at certified
      cases row <;> simp_all [symbolOnly, PT.subst]

end Mettapedia.Machines.TypeAnnotationKey
