import Mettapedia.GSLT.Equations.RecipeMatching
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Ring.Nat

/-! # Factorized reads of a constructor catalogue

Multiply only independent choices; sum alternatives. The dense bottom-up
algorithm materializes a scalar per (pattern position, class), not a list
of assignments. The meaning of an alternative here is a represented recipe
derivation. Existential projection, and identifying repeated variables,
require additional reasoning before replacing the sum by a count.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.FactorizedRead

open UniversalAlgebra RecipeMatching

variable {A R : Type*}

/-- Represent a Cartesian product of independent blocks of witness traces.
List order specifies which result a nested-loop consumer reads first. -/
def multiply (left right : List (List A)) : List (List A) :=
  left.flatMap fun xs => right.map (xs ++ ·)

def products : List (List (List A)) → List (List A)
  | [] => [[]]
  | x :: xs => multiply x (products xs)

section Semiring

variable [Semiring R] (weight : A → R)

def score (xs : List A) : R := (xs.map weight).prod
def sumScore (xs : List (List A)) : R := (xs.map (score weight)).sum

@[simp] theorem score_append (xs ys : List A) :
    score weight (xs ++ ys) = score weight xs * score weight ys := by
  simp [score, List.prod_append]

@[simp] theorem sumScore_append (xs ys : List (List A)) :
    sumScore weight (xs ++ ys) = sumScore weight xs + sumScore weight ys := by
  simp [sumScore, List.sum_append]

theorem sumScore_multiply (xs ys : List (List A)) :
    sumScore weight (multiply xs ys) = sumScore weight xs * sumScore weight ys := by
  induction xs with
  | nil => simp [multiply, sumScore]
  | cons x xs ih =>
    have one (choices : List (List A)) : sumScore weight (choices.map (x ++ ·)) =
        score weight x * sumScore weight choices := by
      induction choices with
      | nil => simp [sumScore]
      | cons y ys hy =>
        change score weight (x ++ y) + sumScore weight (ys.map (x ++ ·)) =
          score weight x * (score weight y + sumScore weight ys)
        rw [score_append, hy, mul_add]
    simp only [multiply, List.flatMap_cons, sumScore_append, one]
    rw [show sumScore weight (List.flatMap (fun zs => List.map (zs ++ ·) ys) xs) =
      sumScore weight xs * sumScore weight ys from ih]
    simp [sumScore, add_mul]

theorem sumScore_products (xs : List (List (List A))) :
    sumScore weight (products xs) = (xs.map (sumScore weight)).prod := by
  induction xs with
  | nil => simp [products, sumScore, score]
  | cons x xs ih =>
    rw [products, sumScore_multiply, ih]
    rfl

theorem sumScore_one (ys : List (List A)) : sumScore (R := Nat) (fun _ : A => 1) ys = ys.length := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    change score (fun _ : A => (1 : Nat)) y + sumScore (fun _ => 1) ys = _
    simp only [score, List.prod_map_one, ih, List.length_cons, Nat.add_comm]

/-- This evaluates in the scalar domain even if the enumeration is huge. -/
theorem length_products (xs : List (List (List A))) :
    (products xs).length = (xs.map List.length).prod := by
  have eq : sumScore (R := Nat) (fun _ : A => 1) = List.length := funext sumScore_one
  simpa only [eq] using sumScore_products (R := Nat) (fun _ : A => 1) xs

end Semiring

section First

theorem head_multiply (xs ys : List (List A)) :
    (multiply xs ys).head? = Option.map₂ List.append xs.head? ys.head? := by
  cases ys with
  | nil => simp [multiply]
  | cons y ys => cases xs <;> rfl

theorem head_products (xs : List (List (List A))) :
    (products xs).head? =
      xs.foldr (fun choices acc => Option.map₂ List.append choices.head? acc) (some []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [products, head_multiply, ih, List.foldr_cons]

end First

section Catalogue

variable {S : Signature} {n : Nat}

abbrev Binding (n : Nat) := Nat × Fin n

/-- Enumerate recipe derivations, keeping the variable occurrences. Variable
IDs in the trace are *not* automatically identified by taking a product. -/
def derivations (g : Catalogue S (Fin n)) : Term S → Fin n → List (List (Binding n))
  | .var v, c => [[(v, c)]]
  | .op f ps, c =>
    ((g.rows f).filter fun row => row.1 == c).flatMap fun (_, args) =>
      products (List.ofFn fun i => derivations g (ps i) (args i))

/-- Scatter one list of weighted tuples into a dense result table. -/
def scatter [AddMonoid R] {B : Type*} (key : B → Fin n) (value : B → R)
    (rows : List B) (initial : Vector R n) : Vector R n :=
  rows.foldl (fun acc row =>
    acc.set (key row).val (acc[(key row).val] + value row) (key row).isLt) initial

theorem get_scatter [AddMonoid R] {B : Type*} (key : B → Fin n) (value : B → R)
    (rows : List B) (initial : Vector R n) (c : Fin n) :
    (scatter key value rows initial)[c.val] =
      initial[c.val] + ((rows.filter fun row => key row == c).map value).sum := by
  induction rows generalizing initial with
  | nil => simp [scatter]
  | cons x xs ih =>
    change (scatter key value xs
      (initial.set (key x).val (initial[(key x).val] + value x) (key x).isLt))[c.val] = _
    rw [ih]
    by_cases e : key x = c
    · simp [e, add_assoc]
    · have ne : (key x).val ≠ c.val := fun h => e (Fin.ext h)
      simp [e, ne]

/-- Each parent tuple is scanned once at its pattern position. At fixed
arity its work uses one scalar lookup per child, then one scatter addition.
In particular this algorithm never constructs a cross product of traces. -/
def messages [Semiring R] (g : Catalogue S (Fin n)) (weight : Binding n → R) :
    Term S → Vector R n
  | .var v => Vector.ofFn fun c => weight (v, c)
  | .op f ps =>
    let child := Vector.ofFn fun i => messages g weight (ps i)
    scatter Prod.fst
      (fun (_, args) => (List.ofFn fun i => (child[i.val])[((args i).val)]).prod)
      (g.rows f) (Vector.replicate n 0)

theorem message_exact [Semiring R] (g : Catalogue S (Fin n)) (weight : Binding n → R)
    (p : Term S) (c : Fin n) :
    (messages g weight p)[c.val] = sumScore weight (derivations g p c) := by
  induction p generalizing c with
  | var v => simp [messages, derivations, sumScore, score]
  | op f ps ih =>
    simp only [messages, get_scatter, Vector.getElem_replicate, zero_add, Vector.getElem_ofFn,
      derivations]
    rw [show ∀ (rs : List (Fin n × Children S (Fin n) f)),
      sumScore weight (rs.flatMap (fun row =>
        products (List.ofFn fun i => derivations g (ps i) (row.2 i)))) =
        (rs.map (fun row =>
          (List.ofFn fun i => sumScore weight (derivations g (ps i) (row.2 i))).prod)).sum from
      fun rs => by
        induction rs with
        | nil => rfl
        | cons r rs tail =>
          simp only [List.flatMap_cons, sumScore_append, sumScore_products, List.map_ofFn,
            List.map_cons, List.sum_cons, tail, Function.comp_def]]
    congr 2
    funext row
    simp only [ih]

/-- All local alternatives in a product must admit a witness satisfying the
specified variable assignment. This statement still works for non-linear
patterns: the same assignment is passed to every child. -/
theorem products_has_iff (P : A → Prop) (xs : List (List (List A))) :
    (∃ trace ∈ products xs, ∀ a ∈ trace, P a) ↔
      ∀ choices ∈ xs, ∃ trace ∈ choices, ∀ a ∈ trace, P a := by
  induction xs with
  | nil => simp [products]
  | cons x xs ih =>
    simp only [products, multiply, List.mem_flatMap, List.mem_map, List.forall_mem_cons]
    constructor
    · rintro ⟨_, ⟨l, hl, r, hr, rfl⟩, wp⟩
      have both := List.forall_mem_append.mp wp
      exact ⟨⟨l, hl, both.1⟩, ih.mp ⟨r, hr, both.2⟩⟩
    · rintro ⟨⟨l, hl, wl⟩, rest⟩
      obtain ⟨r, hr, wr⟩ := ih.mpr rest
      exact ⟨l ++ r, ⟨l, hl, r, hr, rfl⟩, List.forall_mem_append.mpr ⟨wl, wr⟩⟩

theorem match_iff_derivation (g : Catalogue S (Fin n)) (ρ : Nat → Fin n) (p : Term S)
    (c : Fin n) :
    g.Matches ρ p c ↔
      ∃ trace ∈ derivations g p c, ∀ b ∈ trace, ρ b.1 = b.2 := by
  induction p generalizing c with
  | var v => simp [Catalogue.Matches, derivations]
  | op f ps ih =>
    simp only [Catalogue.Matches, derivations, List.mem_flatMap, List.mem_filter,
      beq_iff_eq, Prod.exists]
    constructor
    · rintro ⟨args, mem, child⟩
      have ex := (products_has_iff (fun b : Binding n => ρ b.1 = b.2)
        (List.ofFn fun i => derivations g (ps i) (args i))).2
      obtain ⟨trace, chosen, agrees⟩ := ex (by
        intro choices h
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
        exact (ih i _).1 (child i))
      exact ⟨trace, ⟨c, args, ⟨mem, rfl⟩, chosen⟩, agrees⟩
    · rintro ⟨trace, ⟨root, args, ⟨mem, rfl⟩, chosen⟩, agrees⟩
      have choices := (products_has_iff (fun b : Binding n => ρ b.1 = b.2)
        (List.ofFn fun i => derivations g (ps i) (args i))).1 ⟨trace, chosen, agrees⟩
      exact ⟨args, mem, fun i => (ih i _).2 (choices _ (List.mem_ofFn.mpr ⟨i, rfl⟩))⟩

end Catalogue

end Mettapedia.GSLT.Equations.FactorizedRead
