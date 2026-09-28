import Mathlib.Data.List.Basic

/-!
# Enumerating a list without building it

`(superpose L)` answers the elements of the list `L` in order.  When `L` is
built by `append` and `map-atom`, its elements can be answered as they are
produced, without the list: `superpose` distributes over `append`
(`answers_append`), and over `map-atom` with a mapper that answers exactly
once for every element it answers the mapper's value (`answers_mapAtom`).

`map-atom` with a nondeterministic mapper is the product of the mapper's
answers (`mapAtom`, PeTTa's `map-atom`/3 over `reduce`), and the elements
of those lists are not the mapper's answers over the elements
(`Controls.nondeterministic_mapper`); a mapper without an answer for some
element leaves `map-atom` without an answer at all, while the fused
enumeration still answers the other elements (`Controls.failing_mapper`).
So the fusion needs a mapper with exactly one answer for each element.

`once` takes a witness: the first answer of the fused enumeration is an
element of the list (`first_mem`), and the enumeration reaches it after
producing only as much of the list as precedes it.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SuperposeFusion

universe u v

variable {α : Type u} {β : Type v}

/-- The answers of `(superpose L)`: the elements of `L`, in order. -/
def answers (xs : List α) : List α := xs

theorem answers_append (xs ys : List α) :
    answers (xs ++ ys) = answers xs ++ answers ys := rfl

/-- PeTTa's `map-atom` with a nondeterministic mapper: the lists of one answer
of the mapper for each element, every combination, in order. -/
def mapAtom (f : α → List β) : List α → List (List β)
  | [] => [[]]
  | x :: xs => (f x).flatMap fun y => (mapAtom f xs).map (y :: ·)

/-- A mapper with exactly one answer for each element gives `map-atom` one
answer, the list of those answers. -/
theorem mapAtom_single (g : α → β) :
    ∀ xs : List α, mapAtom (fun x => [g x]) xs = [xs.map g]
  | [] => rfl
  | x :: xs => by
      simp [mapAtom, mapAtom_single g xs]

/-- `superpose` over the one list such a `map-atom` answers is the mapper's
value over each element, in order. -/
theorem answers_mapAtom (g : α → β) (xs : List α) :
    (mapAtom (fun x => [g x]) xs).flatMap answers = (answers xs).map g := by
  rw [mapAtom_single]
  simp [answers]

/-- The first answer of a nonempty enumeration is an element of the list. -/
theorem first_mem (xs : List α) (x : α) (h : (answers xs).head? = some x) :
    x ∈ xs := by
  cases xs with
  | nil => simp [answers] at h
  | cons y ys =>
      simp only [answers, List.head?_cons, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self

namespace Controls

/-- A mapper with two answers: `map-atom` answers two lists, whose elements
are not the mapper's answers over the elements. -/
theorem nondeterministic_mapper :
    (mapAtom (fun (x : ℕ) => [x, x + 10]) [1]).flatMap answers = [1, 11] ∧
      (mapAtom (fun (x : ℕ) => [x, x + 10]) [1, 2]).flatMap answers ≠
        ([1, 2] : List ℕ).flatMap (fun x => [x, x + 10]) := by
  decide

/-- A mapper without an answer for one element: `map-atom` has no answer,
while the elements' own enumeration still answers the other element. -/
theorem failing_mapper :
    mapAtom (fun (x : ℕ) => if x = 2 then [] else [x]) [1, 2] = [] ∧
      ([1, 2] : List ℕ).flatMap (fun x => if x = 2 then [] else [x]) = [1] := by
  decide

end Controls

end Mettapedia.Machines.SuperposeFusion
