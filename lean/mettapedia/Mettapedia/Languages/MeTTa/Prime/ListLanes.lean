import Mathlib.Algebra.FreeMonoid.Basic

/-!
# The two finite-sequence presentations used by CeTTa

An ordinary MeTTa expression exposes a finite sequence of children.  Its
mathematical model is `ExprSeq`, the free monoid on atoms.  `CList` is defined
independently as an inductive nil/cons presentation.  The conversions below
are proved inverse and monoidal; they are not definitions made equal by
construction.

The algebraic laws apply only on the stated sequence domains.  Runtime
partiality of expression eliminators on empty or non-expression atoms is a
separate operational contract and is intentionally not hidden in this model.
-/

namespace Mettapedia.Languages.MeTTa.Prime.ListLanes

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

/-- An independently defined inductive presentation of finite sequences. -/
inductive CList (α : Type u) where
  | nil
  | cons (head : α) (tail : CList α)
deriving DecidableEq, Repr

namespace CList

def toExprSeq : CList α → ExprSeq α
  | .nil => []
  | .cons head tail => head :: toExprSeq tail

def ofExprSeq : ExprSeq α → CList α
  | [] => .nil
  | head :: tail => .cons head (ofExprSeq tail)

@[simp] theorem toExprSeq_ofExprSeq (xs : ExprSeq α) :
    toExprSeq (ofExprSeq xs) = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp [ofExprSeq, toExprSeq, ih]

@[simp] theorem ofExprSeq_toExprSeq (xs : CList α) :
    ofExprSeq (toExprSeq xs) = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp [toExprSeq, ofExprSeq, ih]

theorem toExprSeq_injective : Function.Injective (@toExprSeq α) := by
  intro left right equality
  have := congrArg ofExprSeq equality
  simpa using this

def append : CList α → CList α → CList α
  | .nil, right => right
  | .cons head tail, right => .cons head (append tail right)

@[simp] theorem nil_append (xs : CList α) : append .nil xs = xs := rfl

@[simp] theorem append_nil (xs : CList α) : append xs .nil = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp [append, ih]

theorem append_assoc (xs ys zs : CList α) :
    append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp [append, ih]

instance : Monoid (CList α) where
  one := .nil
  mul := append
  one_mul := nil_append
  mul_one := append_nil
  mul_assoc := append_assoc

@[simp] theorem toExprSeq_append (xs ys : CList α) :
    toExprSeq (append xs ys) = toExprSeq xs ++ toExprSeq ys := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp [append, toExprSeq, ih]

/-- The inductive presentation is monoid-isomorphic to Mathlib's free monoid,
which pins down the algebraic object represented by both runtime lanes. -/
def freeMonoidEquiv : CList α ≃* FreeMonoid α where
  toFun := fun xs => FreeMonoid.ofList (toExprSeq xs)
  invFun := fun xs => ofExprSeq (FreeMonoid.toList xs)
  left_inv := by
    intro xs
    simp
  right_inv := by
    intro xs
    simp
  map_mul' := by
    intro xs ys
    change
      FreeMonoid.ofList (toExprSeq (append xs ys)) =
        FreeMonoid.ofList (toExprSeq xs) * FreeMonoid.ofList (toExprSeq ys)
    rw [toExprSeq_append, FreeMonoid.ofList_append]

def length : CList α → Nat
  | .nil => 0
  | .cons _ tail => length tail + 1

@[simp] theorem length_toExprSeq (xs : CList α) :
    (toExprSeq xs).length = length xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp [toExprSeq, length, ih, Nat.add_comm]

def map (f : α → β) : CList α → CList β
  | .nil => .nil
  | .cons head tail => .cons (f head) (map f tail)

@[simp] theorem toExprSeq_map (f : α → β) (xs : CList α) :
    toExprSeq (map f xs) = (toExprSeq xs).map f := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp [map, toExprSeq, ih]

def filter (predicate : α → Bool) : CList α → CList α
  | .nil => .nil
  | .cons head tail =>
      if predicate head then .cons head (filter predicate tail)
      else filter predicate tail

@[simp] theorem toExprSeq_filter (predicate : α → Bool) (xs : CList α) :
    toExprSeq (filter predicate xs) = (toExprSeq xs).filter predicate := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      by_cases selected : predicate head = true
      · simp [filter, toExprSeq, selected, ih]
      · simp [filter, toExprSeq, selected, ih]

def foldl (step : β → α → β) : β → CList α → β
  | initial, .nil => initial
  | initial, .cons head tail => foldl step (step initial head) tail

@[simp] theorem foldl_eq_exprSeq (step : β → α → β) (initial : β)
    (xs : CList α) :
    foldl step initial xs = (toExprSeq xs).foldl step initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons head tail ih => simp [foldl, toExprSeq, ih]

def reverseAux : CList α → CList α → CList α
  | .nil, accumulator => accumulator
  | .cons head tail, accumulator =>
      reverseAux tail (.cons head accumulator)

def reverse (xs : CList α) : CList α := reverseAux xs .nil

theorem toExprSeq_reverseAux (xs accumulator : CList α) :
    toExprSeq (reverseAux xs accumulator) =
      (toExprSeq xs).reverse ++ toExprSeq accumulator := by
  induction xs generalizing accumulator with
  | nil => simp [reverseAux, toExprSeq]
  | cons head tail ih =>
      simp [reverseAux, toExprSeq, ih, List.append_assoc]

@[simp] theorem toExprSeq_reverse (xs : CList α) :
    toExprSeq (reverse xs) = (toExprSeq xs).reverse := by
  simp [reverse, toExprSeq_reverseAux, toExprSeq]

@[simp] theorem reverse_reverse (xs : CList α) : reverse (reverse xs) = xs := by
  apply toExprSeq_injective
  simp

@[simp] theorem length_reverse (xs : CList α) :
    length (reverse xs) = length xs := by
  calc
    length (reverse xs) = (toExprSeq (reverse xs)).length := by
      symm
      exact length_toExprSeq (reverse xs)
    _ = (toExprSeq xs).reverse.length := by rw [toExprSeq_reverse]
    _ = (toExprSeq xs).length := List.length_reverse
    _ = length xs := length_toExprSeq xs

@[simp] theorem reverse_append (xs ys : CList α) :
    reverse (append xs ys) = append (reverse ys) (reverse xs) := by
  apply toExprSeq_injective
  simp [List.reverse_append]

def rangeFrom : Nat → Nat → CList Nat
  | _, 0 => .nil
  | start, count + 1 => .cons start (rangeFrom (start + 1) count)

def range (start stop : Nat) : CList Nat :=
  rangeFrom start (stop - start)

@[simp] theorem toExprSeq_rangeFrom (start count : Nat) :
    toExprSeq (rangeFrom start count) = ExprSeq.rangeFrom start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      change
        start :: toExprSeq (rangeFrom (start + 1) count) =
          start :: ExprSeq.rangeFrom (start + 1) count
      rw [ih]

@[simp] theorem toExprSeq_range (start stop : Nat) :
    toExprSeq (range start stop) = ExprSeq.range start stop := by
  simp [range, ExprSeq.range]

@[simp] theorem length_range (start stop : Nat) :
    length (range start stop) = stop - start := by
  calc
    length (range start stop) = (toExprSeq (range start stop)).length := by
      symm
      exact length_toExprSeq (range start stop)
    _ = (ExprSeq.range start stop).length := by rw [toExprSeq_range]
    _ = stop - start := ExprSeq.length_range start stop

def «repeat» : Nat → α → CList α
  | 0, _ => .nil
  | count + 1, value => .cons value («repeat» count value)

@[simp] theorem toExprSeq_repeat (count : Nat) (value : α) :
    toExprSeq («repeat» count value) = ExprSeq.«repeat» count value := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change
        value :: toExprSeq («repeat» count value) =
          value :: List.replicate count value
      rw [ih]
      rfl

@[simp] theorem length_repeat (count : Nat) (value : α) :
    length («repeat» count value) = count := by
  calc
    length («repeat» count value) =
        (toExprSeq («repeat» count value)).length := by
      symm
      exact length_toExprSeq («repeat» count value)
    _ = (ExprSeq.«repeat» count value).length := by rw [toExprSeq_repeat]
    _ = count := ExprSeq.length_repeat count value

/-- The universal fold induced by the free-monoid interpretation. -/
def lift [Monoid M] (generator : α → M) : CList α →* M :=
  (FreeMonoid.lift generator).comp freeMonoidEquiv.toMonoidHom

@[simp] theorem lift_nil [Monoid M] (generator : α → M) :
    lift generator (.nil : CList α) = 1 := by
  change (FreeMonoid.lift generator) (FreeMonoid.ofList []) = 1
  rw [FreeMonoid.lift_ofList]
  rfl

@[simp] theorem lift_cons [Monoid M] (generator : α → M)
    (head : α) (tail : CList α) :
    lift generator (.cons head tail) = generator head * lift generator tail := by
  change
    (FreeMonoid.lift generator)
        (FreeMonoid.ofList (head :: toExprSeq tail)) =
      generator head *
        (FreeMonoid.lift generator) (FreeMonoid.ofList (toExprSeq tail))
  rw [FreeMonoid.lift_ofList, FreeMonoid.lift_ofList]
  simp

example :
    toExprSeq (reverse (ofExprSeq ([1, 2, 3] : ExprSeq Nat))) = [3, 2, 1] := by
  decide

example : toExprSeq (range 2 6) = [2, 3, 4, 5] := by
  decide

example : toExprSeq (range 6 2) = [] := by
  decide

example : toExprSeq («repeat» 3 "x") = ["x", "x", "x"] := by
  decide

example : (CList.nil : CList Nat) ≠ .cons 0 .nil := by
  intro equality
  cases equality

end CList

end Mettapedia.Languages.MeTTa.Prime.ListLanes
