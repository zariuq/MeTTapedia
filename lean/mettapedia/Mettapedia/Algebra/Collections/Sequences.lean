import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.VecNotation

/-!
# Sequences and tuples

The children of an expression form a finite sequence, `ExprSeq`: Lean's
`List`, the free monoid on the atom type, with `nil` and `cons` as its
inductive presentation. An expression of arity `n` is a tuple `Fin n → α`;
across all arities the tuples are exactly the sequences, and consing onto or
extending an expression is the tuple operation read through that
correspondence (section "Expressions as tuples").

The algebraic laws apply only on the stated sequence domains. Runtime
partiality of expression eliminators on empty or non-expression atoms is a
separate operational contract and is not part of this model.
-/

namespace Mettapedia.Algebra.Collections.Sequences

/-- The children of an ordinary expression, viewed as the free monoid on its
atom type. -/
abbrev ExprSeq (α : Type u) := List α

namespace ExprSeq

def empty : ExprSeq α := []

def cons (head : α) (tail : ExprSeq α) : ExprSeq α :=
  head :: tail

def append (left right : ExprSeq α) : ExprSeq α := left ++ right

/-- The half-open natural-number interval `[start, stop)`.  The explicit
count makes the descending case empty without introducing signed arithmetic. -/
def rangeFrom : Nat → Nat → ExprSeq Nat
  | _, 0 => []
  | start, count + 1 => start :: rangeFrom (start + 1) count

def range (start stop : Nat) : ExprSeq Nat :=
  rangeFrom start (stop - start)

def «repeat» (count : Nat) (value : α) : ExprSeq α :=
  List.replicate count value

def first? : ExprSeq α → Option α
  | [] => none
  | head :: _ => some head

def rest? : ExprSeq α → Option (ExprSeq α)
  | [] => none
  | _ :: tail => some tail

@[simp] theorem append_empty (xs : ExprSeq α) : append xs empty = xs := by
  simp [append, empty]

@[simp] theorem empty_append (xs : ExprSeq α) : append empty xs = xs := by
  simp [append, empty]

theorem append_assoc (xs ys zs : ExprSeq α) :
    append (append xs ys) zs = append xs (append ys zs) := by
  simp [append, List.append_assoc]

@[simp] theorem length_rangeFrom (start count : Nat) :
    (rangeFrom start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [rangeFrom, ih]

@[simp] theorem length_range (start stop : Nat) :
    (range start stop).length = stop - start := by
  simp [range]

@[simp] theorem length_repeat (count : Nat) (value : α) :
    («repeat» count value).length = count := by
  simp [«repeat»]

@[simp] theorem first_cons (head : α) (tail : ExprSeq α) :
    first? (cons head tail) = some head := rfl

@[simp] theorem rest_cons (head : α) (tail : ExprSeq α) :
    rest? (cons head tail) = some tail := rfl

@[simp] theorem first_empty : first? (empty : ExprSeq α) = none := rfl

@[simp] theorem rest_empty : rest? (empty : ExprSeq α) = none := rfl

end ExprSeq

/-! ## Expressions as tuples

An expression of arity `n` is an `n`-tuple of atoms, one atom at each position
of `Fin n`. Its children, read in order, form the sequence `Tuple.toSeq`.

* For one arity, reading the children is injective (`Tuple.toSeq_injective`),
  and its image is the sequences of that length (`Tuple.mem_range_toSeq`).
* Across all arities the sequences are the disjoint union of the tuple types:
  `ExprSeq α ≃ Σ n, Tuple n α` (`Tuple.sigmaEquiv`); the images of different
  arities are disjoint (`Tuple.range_toSeq_disjoint`) and together they cover
  every sequence (`Tuple.iUnion_range_toSeq`).
* A signature that gives each head a number of arguments fixes the arity of
  the expressions headed by it: those expressions are exactly the sequences
  that start with the head and have one more element than the head's arity
  (`Tuple.applied_iff`).
* Consing onto an expression and extending it are operations between tuple
  types of different arities, `Fin.cons` and `Fin.append`. Read as sequences
  they are `cons` and `append` (`Tuple.toSeq_cons`, `Tuple.toSeq_append`).
  This is the sense in which a list library conses onto and extends
  expressions: it reads an expression as the sequence of its children and
  forgets its arity. A head's typing does not survive the operation: consing
  onto an application gives a sequence of the next arity, which the head no
  longer types (`Controls.cons_leaves_signature`).
-/

/-- An expression of arity `n`: one atom at each position. -/
abbrev Tuple (n : Nat) (α : Type u) := Fin n → α

namespace Tuple

variable {α : Type u} {m n : Nat}

/-- The children of a tuple, in order. -/
def toSeq (t : Tuple n α) : ExprSeq α := List.ofFn t

@[simp] theorem length_toSeq (t : Tuple n α) : (toSeq t).length = n := List.length_ofFn

theorem toSeq_injective : Function.Injective (toSeq : Tuple n α → ExprSeq α) :=
  List.ofFn_injective

/-- Tuples of different arities never have the same children. -/
theorem toSeq_eq_toSeq_iff (s : Tuple m α) (t : Tuple n α) :
    toSeq s = toSeq t ↔ m = n ∧ HEq s t :=
  List.ofFn_inj'.trans Sigma.mk.inj_iff

/-- The sequences read from tuples of arity `n` are those of length `n`. -/
theorem mem_range_toSeq (xs : ExprSeq α) :
    xs ∈ Set.range (toSeq : Tuple n α → ExprSeq α) ↔ xs.length = n := by
  constructor
  · rintro ⟨t, rfl⟩
    exact length_toSeq t
  · intro length
    subst length
    exact ⟨xs.get, List.ofFn_get xs⟩

theorem range_toSeq_disjoint (different : m ≠ n) :
    Disjoint (Set.range (toSeq : Tuple m α → ExprSeq α))
      (Set.range (toSeq : Tuple n α → ExprSeq α)) := by
  rw [Set.disjoint_left]
  intro xs first second
  exact different (((mem_range_toSeq xs).mp first).symm.trans ((mem_range_toSeq xs).mp second))

/-- Every sequence is read from a tuple, of arity its length. -/
theorem exists_range_toSeq (xs : ExprSeq α) :
    ∃ n, xs ∈ Set.range (toSeq : Tuple n α → ExprSeq α) :=
  ⟨xs.length, (mem_range_toSeq xs).mpr rfl⟩

/-- Across all arities, sequences are tuples: the arity is the length. -/
def sigmaEquiv : ExprSeq α ≃ Σ n, Tuple n α := List.equivSigmaTuple

@[simp] theorem sigmaEquiv_symm_apply (t : Σ n, Tuple n α) :
    sigmaEquiv.symm t = toSeq t.2 := rfl

@[simp] theorem sigmaEquiv_apply_fst (xs : ExprSeq α) : (sigmaEquiv xs).1 = xs.length := rfl

/-- Consing onto a tuple of arity `n` gives one of arity `n + 1`. -/
@[simp] theorem toSeq_cons (head : α) (t : Tuple n α) :
    toSeq (Fin.cons head t : Tuple (n + 1) α) = ExprSeq.cons head (toSeq t) :=
  List.ofFn_cons head t

/-- Extending a tuple of arity `m` by one of arity `n` gives one of arity `m + n`. -/
@[simp] theorem toSeq_append (s : Tuple m α) (t : Tuple n α) :
    toSeq (Fin.append s t) = ExprSeq.append (toSeq s) (toSeq t) :=
  List.ofFn_fin_append s t

/-- The expression with head `head` applied to the arguments `arguments`. -/
def apply (head : α) (arguments : Tuple n α) : ExprSeq α :=
  toSeq (Fin.cons head arguments : Tuple (n + 1) α)

/-- **A signature fixes the arity.** With `arity h` arguments declared for the
head `h`, the expressions it heads are exactly the sequences that start with
`h` and have `arity h + 1` elements. -/
theorem applied_iff {H : Type*} (head : H → α) (arity : H → Nat) (h : H) (xs : ExprSeq α) :
    (∃ arguments : Tuple (arity h) α, apply (head h) arguments = xs) ↔
      xs.head? = some (head h) ∧ xs.length = arity h + 1 := by
  constructor
  · rintro ⟨arguments, rfl⟩
    simp [apply, toSeq]
  · rintro ⟨first, length⟩
    cases xs with
    | nil => simp at first
    | cons x rest =>
        simp only [List.head?_cons, Option.some.injEq] at first
        subst first
        obtain ⟨arguments, readBack⟩ :=
          (mem_range_toSeq (n := arity h) rest).mpr (by simpa using length)
        exact ⟨arguments, by simp [apply, ExprSeq.cons, readBack]⟩

end Tuple

namespace Controls

open Tuple

/-- Consing onto `(f a b)` gives the four-element sequence `(x f a b)`. The
head `f`, declared with two arguments, types sequences of length three only,
and the new head `x` is not `f`. -/
theorem cons_leaves_signature :
    ExprSeq.cons "x" (apply "f" ![("a" : String), "b"]) = ["x", "f", "a", "b"] ∧
      ¬ ∃ arguments : Tuple 2 String,
        apply "f" arguments = ExprSeq.cons "x" (apply "f" ![("a" : String), "b"]) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨arguments, same⟩
  have typed := (applied_iff (fun head : String => head) (fun _ => 2) "f" _).mp ⟨arguments, same⟩
  exact absurd typed (by decide)

/-- Tuples of arities two and three have different children, even with a
common prefix. -/
theorem arities_separate :
    toSeq ![(1 : Nat), 2] ≠ toSeq ![1, 2, 3] := by
  decide

/-- Extending `(a b)` by `(c)` is the tuple `(a b c)` of arity three. -/
theorem extend_tuple :
    toSeq (Fin.append ![(1 : Nat), 2] ![3]) = [1, 2, 3] := by
  decide

end Controls


end Mettapedia.Algebra.Collections.Sequences
