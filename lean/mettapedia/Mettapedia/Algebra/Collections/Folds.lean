import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup

/-!
# Finite collection folds and their binary algebras

A singleton-preserving operation on finite lists that respects flattening
determines a monoid. Its value on every list is the product in that monoid,
and every monoid supplies such an operation. Thus arbitrary variadic arities
are fixed by the binary operation and the empty value, rather than inferred
from finitely many tests at arity two or three.

The universal folds of lists, bags and sets, the free structures they come
from, and the exact conditions under which a list fold consumes bags or sets
are in `Algebra.Collections.Free`.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.Folds

universe u
variable {A : Type u}

structure Model (A : Type u) where
  fold : List A → A
  singleton : ∀ value, fold [value] = value
  flatten : ∀ pieces : List (List A), fold pieces.flatten = fold (pieces.map fold)

@[ext] theorem Model.ext {first second : Model A}
    (equal : first.fold = second.fold) : first = second := by
  cases first
  cases second
  cases equal
  rfl

def ofMonoid [Monoid A] : Model A where
  fold := List.prod
  singleton := by intro value; simp
  flatten := by intro pieces; exact List.prod_flatten

namespace Model

variable (algebra : Model A)

theorem fold_append (left right : List A) :
    algebra.fold (left ++ right) = algebra.fold [algebra.fold left, algebra.fold right] := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil,
    List.map_cons, List.map_nil] using algebra.flatten [left, right]

theorem fold_cons (value : A) (rest : List A) :
    algebra.fold (value :: rest) = algebra.fold [value, algebra.fold rest] := by
  simpa only [List.singleton_append, algebra.singleton] using algebra.fold_append [value] rest

theorem fold_left_unit (value : A) :
    algebra.fold [algebra.fold [], value] = value := by
  simpa only [List.nil_append, algebra.singleton] using (algebra.fold_append [] [value]).symm

theorem fold_right_unit (value : A) :
    algebra.fold [value, algebra.fold []] = value := by
  simpa only [List.append_nil, algebra.singleton] using (algebra.fold_append [value] []).symm

theorem fold_associative (first second third : A) :
    algebra.fold [algebra.fold [first, second], third] =
      algebra.fold [first, algebra.fold [second, third]] := by
  calc
    _ = algebra.fold ([first, second] ++ [third]) := by
      rw [algebra.fold_append, algebra.singleton]
    _ = _ := algebra.fold_cons first [second, third]

/-- The binary multiplication and unit are derived from the actual fold. -/
@[instance_reducible] def monoid : Monoid A where
  one := algebra.fold []
  mul first second := algebra.fold [first, second]
  one_mul := algebra.fold_left_unit
  mul_one := algebra.fold_right_unit
  mul_assoc := algebra.fold_associative

theorem fold_eq_prod (values : List A) :
    letI := algebra.monoid
    algebra.fold values = values.prod := by
  let _ := algebra.monoid
  induction values with
  | nil => rfl
  | cons value rest ih =>
    rw [List.prod_cons, ← ih]
    exact algebra.fold_cons value rest

/-- Reconstructing all arities from the extracted binary algebra returns
the entire original operation. -/
theorem ofMonoid_monoid : @ofMonoid A algebra.monoid = algebra := by
  apply Model.ext
  funext values
  exact (algebra.fold_eq_prod values).symm

def PermutationInvariant : Prop :=
  ∀ left right : List A, left.Perm right → algebra.fold left = algebra.fold right

theorem permutationInvariant_iff : algebra.PermutationInvariant ↔
    ∀ first second, algebra.fold [first, second] = algebra.fold [second, first] := by
  constructor
  · intro invariant first second
    exact invariant _ _ (List.Perm.swap _ _ [])
  · intro commutes left right permutation
    let _ : CommMonoid A := { algebra.monoid with mul_comm := commutes }
    rw [algebra.fold_eq_prod left, algebra.fold_eq_prod right]
    exact permutation.prod_eq

end Model

/-- Binary application is preserved by the finite-list realization. -/
theorem ofMonoid_binary [Monoid A] (first second : A) :
    (ofMonoid (A := A)).fold [first, second] = first * second := by
  simp [ofMonoid]

theorem ofMonoid_empty [Monoid A] : (ofMonoid (A := A)).fold [] = 1 := rfl

private theorem prod_absorb_of_mem [CommMonoid A]
    (idempotent : ∀ value : A, value * value = value)
    {value : A} {values : List A} (member : value ∈ values) :
    value * values.prod = values.prod := by
  induction values with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · rw [List.prod_cons, ← mul_assoc, idempotent]
    · rw [List.prod_cons, mul_left_comm, ih later]

private theorem prod_dedup [CommMonoid A] [DecidableEq A]
    (idempotent : ∀ value : A, value * value = value) (values : List A) :
    values.dedup.prod = values.prod := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
    by_cases member : head ∈ rest
    · rw [List.dedup_cons_of_mem member, ih, List.prod_cons,
        prod_absorb_of_mem idempotent member]
    · rw [List.dedup_cons_of_notMem member, List.prod_cons, List.prod_cons, ih]

theorem prod_eq_of_members [CommMonoid A]
    (idempotent : ∀ value : A, value * value = value)
    {left right : List A} (same : ∀ value, value ∈ left ↔ value ∈ right) :
    left.prod = right.prod := by
  classical
  have permuted : left.dedup.Perm right.dedup :=
    (List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).mpr
      (fun value => by simpa only [List.mem_dedup] using same value)
  rw [← prod_dedup idempotent left, ← prod_dedup idempotent right]
  exact permuted.prod_eq

namespace Model

variable (algebra : Model A)

def MembershipInvariant : Prop :=
  ∀ left right : List A, (∀ value, value ∈ left ↔ value ∈ right) →
    algebra.fold left = algebra.fold right

/-- Exactly the commutative idempotent binary algebras permit set-valued
folds. Bag permutation alone never licenses erasing multiplicities. -/
theorem membershipInvariant_iff : algebra.MembershipInvariant ↔
    algebra.PermutationInvariant ∧ ∀ value, algebra.fold [value, value] = value := by
  constructor
  · intro invariant
    refine ⟨fun left right permuted => invariant left right (fun _ => permuted.mem_iff), ?_⟩
    intro value
    calc
      algebra.fold [value, value] = algebra.fold [value] := invariant _ _ (by simp)
      _ = value := algebra.singleton value
  · rintro ⟨permutation, idempotent⟩ left right same
    let _ : CommMonoid A :=
      { algebra.monoid with mul_comm := algebra.permutationInvariant_iff.mp permutation }
    rw [algebra.fold_eq_prod left, algebra.fold_eq_prod right]
    exact prod_eq_of_members idempotent same

/-! ### Consuming bags and sets -/

/-- A permutation-invariant fold, read on bags. -/
def bagFold (invariant : algebra.PermutationInvariant) : Multiset A → A :=
  Quot.lift algebra.fold (fun _ _ permuted => invariant _ _ permuted)

@[simp] theorem bagFold_coe (invariant : algebra.PermutationInvariant) (values : List A) :
    algebra.bagFold invariant values = algebra.fold values := rfl

/-- A fold consumes bags, i.e. it is a function of the bag of its arguments,
exactly when it is invariant under permutation. -/
theorem factorsThroughBag_iff :
    (∃ consume : Multiset A → A, ∀ values : List A, algebra.fold values = consume values) ↔
      algebra.PermutationInvariant := by
  constructor
  · rintro ⟨consume, factors⟩ left right permuted
    rw [factors, factors, Multiset.coe_eq_coe.mpr permuted]
  · intro invariant
    exact ⟨algebra.bagFold invariant, fun _ => rfl⟩

theorem bagFold_unique (invariant : algebra.PermutationInvariant)
    (consume : Multiset A → A) (factors : ∀ values : List A, consume values = algebra.fold values) :
    consume = algebra.bagFold invariant := by
  funext values
  induction values using Quot.ind with
  | mk values => exact factors values

/-- The bag fold is a homomorphism out of the free commutative monoid. -/
theorem bagFold_add (invariant : algebra.PermutationInvariant) (left right : Multiset A) :
    algebra.bagFold invariant (left + right) =
      algebra.fold [algebra.bagFold invariant left, algebra.bagFold invariant right] := by
  obtain ⟨left, rfl⟩ := Quot.exists_rep left
  obtain ⟨right, rfl⟩ := Quot.exists_rep right
  exact algebra.fold_append left right

theorem bagFold_singleton (invariant : algebra.PermutationInvariant) (value : A) :
    algebra.bagFold invariant {value} = value :=
  algebra.singleton value

/-- A membership-invariant fold, read on sets through any enumeration. -/
noncomputable def setFold (_invariant : algebra.MembershipInvariant) (values : Finset A) : A :=
  algebra.fold values.toList

theorem setFold_toFinset [DecidableEq A] (invariant : algebra.MembershipInvariant)
    (values : List A) : algebra.setFold invariant values.toFinset = algebra.fold values :=
  invariant _ _ (fun value => by simp)

/-- A fold consumes sets exactly when it is invariant under permutation and
repetition, i.e. when it depends only on which values occur. -/
theorem factorsThroughSet_iff [DecidableEq A] :
    (∃ consume : Finset A → A, ∀ values : List A, algebra.fold values = consume values.toFinset) ↔
      algebra.MembershipInvariant := by
  constructor
  · rintro ⟨consume, factors⟩ left right same
    rw [factors, factors]
    congr 1
    ext value
    simpa using same value
  · intro invariant
    exact ⟨algebra.setFold invariant, fun values => (algebra.setFold_toFinset invariant values).symm⟩

theorem setFold_unique [DecidableEq A] (invariant : algebra.MembershipInvariant)
    (consume : Finset A → A)
    (factors : ∀ values : List A, consume values.toFinset = algebra.fold values) :
    consume = algebra.setFold invariant := by
  funext values
  rw [← Finset.toList_toFinset values, factors, setFold_toFinset]

/-- The set fold is a homomorphism out of the free idempotent commutative
monoid. -/
theorem setFold_union [DecidableEq A] (invariant : algebra.MembershipInvariant)
    (left right : Finset A) :
    algebra.setFold invariant (left ∪ right) =
      algebra.fold [algebra.setFold invariant left, algebra.setFold invariant right] := by
  unfold setFold
  rw [← algebra.fold_append]
  exact invariant _ _ (fun value => by simp)

theorem setFold_singleton (invariant : algebra.MembershipInvariant) (value : A) :
    algebra.setFold invariant {value} = value := by
  simpa [setFold] using algebra.singleton value

/-- Reading a set as the bag of its distinct elements gives the same value. -/
theorem setFold_eq_bagFold (invariant : algebra.MembershipInvariant) (values : Finset A) :
    algebra.setFold invariant values =
      algebra.bagFold ((algebra.membershipInvariant_iff.mp invariant).1) values.val := by
  conv_rhs => rw [← Finset.coe_toList values]
  rfl

end Model

end Mettapedia.Algebra.Collections.Folds
