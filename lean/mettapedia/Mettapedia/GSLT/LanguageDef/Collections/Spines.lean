import Mettapedia.Logic.Unification.ListSpliceTerms
import Mettapedia.GSLT.LanguageDef.Collections.Layouts
import Mathlib.Data.Stream.Init

/-!
# Partial lists: spines, terminals and finite trees

A list value in splice normal form (`Logic.Unification.ListSplice`) is proper
(`[a b c]`), open (`[a b | $t]`) or improper (`[a b | z]`). Its abstraction
(`abstractOf`) is the sequence of its explicit elements with its terminal
(`Layouts.Terminal`): `Nil`, the unbound variable, or the improper tail.

* Writing an abstraction as a term and reading it back is the identity on
  well-formed abstractions: a nonempty prefix, or the terminal `Nil`, and an
  improper tail that is neither a list nor a variable (`abstractOf_ofAbstract`).
* The terminal classes describe what is known about a term, not three
  datatypes: binding the variable of an open list to a list value appends its
  elements (`abstractOf_bind_tail`), as a difference list does, and the result
  is proper, open or improper as the bound value is.
* Terms are finite trees. No term is its own tail, so the equation
  `$t = [a | $t]` has no solution among terms (`no_cyclic_list`), while among
  infinite streams it has one (`Controls.stream_solves_cycle`): the occurs
  check is the finite-tree reading of that equation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.Spines

open Mettapedia.Logic.Unification.ListSplice
open Layouts (Terminal Abstract)

variable {Leaf Var : Type}

/-- The abstraction of a list value. -/
def abstractOf : Term Leaf Var → Option (Abstract (Term Leaf Var) Var)
  | .list xs => some (xs, .nil)
  | .rest xs (.var v) => some (xs, .var v)
  | .rest xs tail => some (xs, .improper tail)
  | _ => none

/-- An abstraction written as a term. -/
def ofAbstract : Abstract (Term Leaf Var) Var → Term Leaf Var
  | (xs, .nil) => .list xs
  | (xs, .var v) => .rest xs (.var v)
  | (xs, .improper tail) => .rest xs tail

/-- A tail that is neither a list value nor a variable. -/
def ImproperTail : Term Leaf Var → Prop
  | .atom _ | .expr _ => True
  | _ => False

/-- An abstraction that a normal form realizes. -/
def WellFormed : Abstract (Term Leaf Var) Var → Prop
  | (_, .nil) => True
  | (xs, .var _) => xs ≠ []
  | (xs, .improper tail) => xs ≠ [] ∧ ImproperTail tail

theorem abstractOf_ofAbstract : ∀ (a : Abstract (Term Leaf Var) Var), WellFormed a →
    abstractOf (ofAbstract a) = some a
  | (_, .nil), _ => rfl
  | (_, .var _), _ => rfl
  | (xs, .improper tail), ⟨_, improper⟩ => by
      cases tail <;> simp_all [ImproperTail, abstractOf, ofAbstract]

/-- Written abstractions are in splice normal form when their elements are. -/
theorem normalize_ofAbstract (a : Abstract (Term Leaf Var) Var) (wellFormed : WellFormed a)
    (normal : ∀ x ∈ a.1, normalize x = x) (tailNormal : ∀ t, a.2 = .improper t → normalize t = t) :
    normalize (ofAbstract a) = ofAbstract a := by
  obtain ⟨xs, end_⟩ := a
  have elements : xs.map normalize = xs := by
    conv_rhs => rw [← List.map_id xs]
    exact List.map_congr_left normal
  cases end_ with
  | nil => simp [ofAbstract, normalize, elements]
  | var v =>
      cases xs with
      | nil => exact absurd rfl wellFormed
      | cons x xs => simp only [ofAbstract, normalize]; rw [elements]; rfl
  | improper tail =>
      obtain ⟨nonempty, improper⟩ := wellFormed
      have same := tailNormal tail rfl
      cases xs with
      | nil => exact absurd rfl nonempty
      | cons x xs =>
          simp only [ofAbstract, normalize]
          rw [elements, same]
          cases tail <;> simp_all [ImproperTail, splice]

/-- **Binding the rest of an open list appends.** If the tail variable is
bound to a list value with abstraction `(ys, e)`, the open list `[xs | $v]`
becomes the list with abstraction `(xs ++ ys, e)`. -/
theorem abstractOf_bind_tail (σ : Var → Term Leaf Var) (xs : List (Term Leaf Var)) (v : Var)
    (ys : List (Term Leaf Var)) (e : Terminal (Term Leaf Var) Var)
    (bound : normalize (σ v) = ofAbstract (ys, e)) (wellFormed : WellFormed (ys, e)) :
    abstractOf (normalize (subst σ (.rest xs (.var v)))) =
      some ((xs.map (fun x => normalize (subst σ x))) ++ ys, e) := by
  simp only [subst, normalize, List.map_map]
  rw [bound]
  cases e with
  | nil => simp [ofAbstract, abstractOf, Function.comp_def]
  | var w => simp only [ofAbstract, splice_rest, abstractOf, Function.comp_def]
  | improper tail =>
      simp only [ofAbstract, splice_rest, Function.comp_def]
      obtain ⟨-, improper⟩ := wellFormed
      cases tail <;> simp_all [ImproperTail, abstractOf]

/-- **Terms are finite trees**: no term is the tail of a list whose tail it is. -/
theorem no_cyclic_list (a : Term Leaf Var) (t : Term Leaf Var) : t ≠ .rest [a] t := by
  intro same
  have := congrArg sizeOf same
  simp at this

namespace Controls

/-- Binding `$t` in `[a b | $t]` to `[c d]` gives `[a b c d]`; binding it to
`[c | $s]` gives the open list `[a b c | $s]`. -/
theorem difference_list :
    abstractOf (normalize (subst (fun _ => .list [.atom "c", .atom "d"])
        (.rest [.atom "a", .atom "b"] (.var "t") : Term String String))) =
      some ([.atom "a", .atom "b", .atom "c", .atom "d"], .nil) ∧
    abstractOf (normalize (subst (fun v => if v = "t" then .rest [.atom "c"] (.var "s") else .var v)
        (.rest [.atom "a", .atom "b"] (.var "t") : Term String String))) =
      some ([.atom "a", .atom "b", .atom "c"], .var "s") := by
  constructor <;> simp [subst, normalize, splice, abstractOf]

/-- Among infinite streams the cyclic equation has a solution: the constant
stream is its own tail. -/
theorem stream_solves_cycle (a : ℕ) : Stream'.cons a (Stream'.const a) = Stream'.const a :=
  (Stream'.const_eq a).symm

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.Spines
