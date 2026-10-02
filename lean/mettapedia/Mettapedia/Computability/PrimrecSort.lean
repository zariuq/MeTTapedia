import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Sort

/-!
# Insertion sort is primitive recursive

Inserting a value into a list in order, and sorting a list by repeated
insertion, are primitive recursive whenever the order is.
-/

set_option autoImplicit false

namespace Mettapedia.Computability

open Primrec

variable {α : Type*} [Primcodable α] {r : α → α → Prop} [DecidableRel r]

/-- Ordered insertion is primitive recursive when the relation is. -/
theorem orderedInsert_primrec (relation : PrimrecRel r) :
    Primrec₂ fun (value : α) (values : List α) => List.orderedInsert r value values := by
  have step : Primrec₂ fun (input : α × List α) (state : α × List α × List α) =>
      if r input.1 state.1 then input.1 :: state.1 :: state.2.1 else state.1 :: state.2.2 :=
    Primrec.ite (relation.comp (fst.comp fst) (fst.comp snd))
      (list_cons.comp (fst.comp fst)
        (list_cons.comp (fst.comp snd) (fst.comp (snd.comp snd))))
      (list_cons.comp (fst.comp snd) (snd.comp (snd.comp snd)))
  have recursion := list_rec (f := fun input : α × List α => input.2)
    (g := fun input : α × List α => [input.1]) snd (list_cons.comp fst (const [])) step
  refine recursion.of_eq fun input => ?_
  induction input.2 with
  | nil => rfl
  | cons head tail recurse => simp only [List.orderedInsert_cons, ← recurse]

/-- **Insertion sort is primitive recursive** when the relation is. -/
theorem insertionSort_primrec (relation : PrimrecRel r) :
    Primrec fun values : List α => List.insertionSort r values := by
  have insertion : Primrec₂ fun (_ : List α) (state : α × List α) =>
      List.orderedInsert r state.1 state.2 :=
    (orderedInsert_primrec relation).comp (fst.comp snd) (snd.comp snd)
  exact (list_foldr Primrec.id (const []) insertion).of_eq fun values => rfl

end Mettapedia.Computability
