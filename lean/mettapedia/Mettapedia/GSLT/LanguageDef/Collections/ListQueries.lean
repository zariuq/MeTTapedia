import Mettapedia.Algebra.Collections.Free
import Mettapedia.Languages.MeTTa.SpaceQueryPolicy
import Mettapedia.GSLT.LanguageDef.Collections.Evaluation

/-!
# Querying every element of a list, and lists of evaluated elements

**Matching a pattern against every element** (`matchAll`, the `match'` of
list programs) reads a list as a small space.
* It is the free monoid's homomorphism out of lists that matches each element
  (`matchAll_append`, `matchAll_eq_lift`): answers come out in the order of the
  elements.
* Its answers, as a bag, depend only on the bag the list forgets to: the
  square with `toBag` commutes, and the bag side is the free commutative
  monoid's lift of matching one element (`toBag_matchAll`, `bagMatch_eq_bagLift`).
  Permuted lists give permuted answers (`matchAll_perm`).
* That bag is the answer of the space query over the list's elements
  (`toFinsupp_matchAll`, with `SpaceQueryPolicy.query`).
* The order of the answers is not a function of the bag, and their number is
  not a function of the set (`Controls.order_not_a_bag_observation`,
  `Controls.multiplicity_counts`).

**Lists of evaluated elements.** Evaluating the elements of an expression in
code position gives one list per combination of the elements' values
(`combinations`, `mem_combinations`, `card_combinations`); an element without
a value gives no list (`combinations_eq_zero`), and elements with one value
each give one list (`combinations_pure`). The evaluation semantics agrees
(`eval_construct_mem_combinations`), so `list:from` of an expression is the
derived operation "evaluate the expression, then convert".
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.ListQueries

open Mettapedia.Algebra.Collections
open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.Languages.MeTTa.SpaceQueryPolicy

variable {Atom Pat Res : Type*} (matcher : Pat → Atom → Option Res)

/-! ## Matching every element -/

/-- The answers of a pattern against each element of a list, in order. -/
def matchAll (p : Pat) (xs : List Atom) : List Res := xs.filterMap (matcher p)

@[simp] theorem matchAll_nil (p : Pat) : matchAll matcher p [] = [] := rfl

@[simp] theorem matchAll_append (p : Pat) (xs ys : List Atom) :
    matchAll matcher p (xs ++ ys) = matchAll matcher p xs ++ matchAll matcher p ys :=
  List.filterMap_append

theorem matchAll_cons (p : Pat) (a : Atom) (xs : List Atom) :
    matchAll matcher p (a :: xs) = (matcher p a).toList ++ matchAll matcher p xs := by
  cases h : matcher p a <;> simp [matchAll, h]

/-- `matchAll` is the homomorphism out of the free monoid that matches each
element. -/
theorem matchAll_eq_lift (p : Pat) (xs : List Atom) :
    FreeMonoid.ofList (matchAll matcher p xs) =
      FreeMonoid.lift (fun a => FreeMonoid.ofList (matcher p a).toList) (FreeMonoid.ofList xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [matchAll_cons, FreeMonoid.ofList_append, ih, FreeMonoid.ofList_cons, map_mul,
        FreeMonoid.lift_eval_of]

/-- The bag of answers of a pattern against a bag of atoms. -/
def bagMatch (p : Pat) (s : Multiset Atom) : Multiset Res :=
  s.bind fun a => ((matcher p a).toList : Multiset Res)

/-- **The square with `toBag` commutes**: the bag of answers depends only on
the bag of elements. -/
theorem toBag_matchAll (p : Pat) (xs : List Atom) :
    toBag (matchAll matcher p xs) = bagMatch matcher p (toBag xs) := by
  induction xs with
  | nil => simp [bagMatch, toBag]
  | cons a xs ih =>
      rw [matchAll_cons, toBag_append, ih]
      change _ = Multiset.bind (a ::ₘ (xs : Multiset Atom)) _
      rw [Multiset.cons_bind]
      rfl

/-- The bag side is the free commutative monoid's lift of matching one element. -/
theorem bagMatch_eq_bagLift (p : Pat) :
    bagMatch matcher p = bagLift (fun a => ((matcher p a).toList : Multiset Res)) := by
  funext s
  rw [bagLift_apply, bagMatch, Multiset.bind]
  rfl

theorem matchAll_perm (p : Pat) {xs ys : List Atom} (permuted : xs.Perm ys) :
    (matchAll matcher p xs).Perm (matchAll matcher p ys) := by
  apply Multiset.coe_eq_coe.mp
  change toBag (matchAll matcher p xs) = toBag (matchAll matcher p ys)
  rw [toBag_matchAll, toBag_matchAll, show toBag xs = toBag ys from Multiset.coe_eq_coe.mpr permuted]

/-- **The list as a small space**: the bag of answers is the query of the
space that holds the list's elements. -/
theorem toFinsupp_matchAll [DecidableEq Atom] [DecidableEq Res] (p : Pat) (xs : List Atom) :
    Multiset.toFinsupp (toBag (matchAll matcher p xs)) =
      query matcher (Multiset.toFinsupp (toBag xs)) p := by
  rw [toBag_matchAll, bagMatch, toFinsupp_bind]
  unfold query
  congr 1
  funext a
  unfold contribution
  cases matcher p a with
  | none => simp
  | some r => exact toFinsupp_pure r

/-! ## Lists of evaluated elements -/

section Combinations

variable {α : Type*}

/-- The lists with one value per element, taken from each element's bag of
values: one list per combination. -/
def combinations : List (Multiset α) → Multiset (List α)
  | [] => {[]}
  | s :: rest => s.bind fun a => (combinations rest).map (a :: ·)

theorem mem_combinations : ∀ (ss : List (Multiset α)) (ys : List α),
    ys ∈ combinations ss ↔ List.Forall₂ (· ∈ ·) ys ss
  | [], ys => by cases ys <;> simp [combinations]
  | s :: rest, ys => by
      cases ys with
      | nil => simp [combinations]
      | cons y ys =>
          simp only [combinations, Multiset.mem_bind, Multiset.mem_map, List.cons.injEq,
            List.forall₂_cons, mem_combinations rest]
          constructor
          · rintro ⟨a, member, zs, inner, rfl, rfl⟩
            exact ⟨member, inner⟩
          · rintro ⟨member, inner⟩
            exact ⟨y, member, ys, inner, rfl, rfl⟩

/-- The number of lists is the product of the numbers of values. -/
theorem card_combinations : ∀ ss : List (Multiset α),
    Multiset.card (combinations ss) = (ss.map Multiset.card).prod
  | [] => by simp [combinations]
  | s :: rest => by
      rw [combinations, Multiset.card_bind, List.map_cons, List.prod_cons]
      have constant : (Multiset.card ∘ fun a => Multiset.map (fun x => a :: x) (combinations rest)) =
          fun _ => (rest.map Multiset.card).prod := by
        funext a
        simp [card_combinations rest]
      rw [constant, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul]

/-- Elements with one value each give one list. -/
theorem combinations_pure : ∀ xs : List α, combinations (xs.map fun x => ({x} : Multiset α)) = {xs}
  | [] => rfl
  | x :: xs => by simp [combinations, combinations_pure xs]

/-- An element without a value gives no list at all. -/
theorem combinations_eq_zero {ss : List (Multiset α)} (empty : (0 : Multiset α) ∈ ss) :
    combinations ss = 0 := by
  rw [← Multiset.card_eq_zero, card_combinations]
  exact List.prod_eq_zero (List.mem_map.mpr ⟨0, empty, Multiset.card_zero⟩)

end Combinations

section Semantics

open Mettapedia.Logic.Unification.ListSplice
open Evaluation

variable {Symbol Var : Type} [DecidableEq Symbol] [DecidableEq Var]
  {P : Program Symbol Var} {θ : Env Symbol Var}

theorem evalAll_iff_forall₂ : ∀ (es vs : List (Tm Symbol Var)),
    EvalAll P θ es vs ↔ List.Forall₂ (Eval P θ) es vs
  | [], vs => by
      cases vs with
      | nil => exact ⟨fun _ => .nil, fun _ => .nil⟩
      | cons v vs => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | e :: es, vs => by
      cases vs with
      | nil => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
      | cons v vs =>
          rw [List.forall₂_cons, ← evalAll_iff_forall₂ es vs]
          constructor
          · intro h
            cases h with
            | cons first rest => exact ⟨first, rest⟩
          · rintro ⟨first, rest⟩
            exact .cons first rest

theorem forall₂_eval_iff {es : List (Tm Symbol Var)} {values : List (Multiset (Tm Symbol Var))}
    (described : List.Forall₂ (fun e s => ∀ v, Eval P θ e v ↔ v ∈ s) es values)
    (vs : List (Tm Symbol Var)) :
    List.Forall₂ (Eval P θ) es vs ↔ List.Forall₂ (· ∈ ·) vs values := by
  induction described generalizing vs with
  | nil => cases vs <;> simp
  | cons first _ ih =>
      cases vs with
      | nil => simp
      | cons w ws => rw [List.forall₂_cons, List.forall₂_cons, first w, ih ws]

/-- **The evaluation semantics agrees**: when each element's values form a
bag, an expression that is not a call evaluates to exactly the expressions of
the combinations. -/
theorem eval_construct_mem_combinations (es : List (Tm Symbol Var)) (notCall : P.NotCall es)
    (values : List (Multiset (Tm Symbol Var)))
    (described : List.Forall₂ (fun e s => ∀ v, Eval P θ e v ↔ v ∈ s) es values)
    (v : Tm Symbol Var) :
    Eval P θ (.expr es) v ↔ ∃ vs ∈ combinations values, v = .expr vs := by
  rw [eval_construct_iff es notCall]
  simp only [evalAll_iff_forall₂, mem_combinations, forall₂_eval_iff described]

end Semantics

/-! ## Controls -/

namespace Controls

/-- The matcher that answers every element with itself. -/
def identity : Unit → ℕ → Option ℕ := fun _ a => some a

/-- Two orders of one bag give the same answers in different orders. -/
theorem order_not_a_bag_observation :
    toBag ([1, 2] : List ℕ) = toBag [2, 1] ∧
      matchAll identity () [1, 2] ≠ matchAll identity () [2, 1] := by
  refine ⟨Multiset.coe_eq_coe.mpr (List.Perm.swap 2 1 []), by decide⟩

/-- A repeated element is answered twice: matching is a bag observation, not a
set observation. -/
theorem multiplicity_counts :
    toSet (toBag ([1, 1] : List ℕ)) = toSet (toBag [1]) ∧
      (matchAll identity () [1, 1]).length = 2 ∧ (matchAll identity () [1]).length = 1 := by
  refine ⟨by decide, rfl, rfl⟩

/-- Elements with the values `{1, 2}` and `{3}`: the lists `[1 3]` and `[2 3]`. -/
theorem two_combinations :
    combinations [({1, 2} : Multiset ℕ), {3}] = {[1, 3], [2, 3]} := by
  decide

/-- An element without a value: no list. -/
theorem no_value_no_list : combinations [({1, 2} : Multiset ℕ), 0] = 0 :=
  combinations_eq_zero (by simp)

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.ListQueries
