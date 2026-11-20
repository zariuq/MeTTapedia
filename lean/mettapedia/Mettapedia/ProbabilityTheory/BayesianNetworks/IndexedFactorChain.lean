import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Retaining the products of an ordered factor chain

A chain of binary factors with one shared coordinate between neighbors can be
eliminated by matrix multiplication. A tree records a parenthesization of
that ordered product. Each admitted edit selects a leaf of the same tree.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.IndexedFactorChain

inductive Shape where
  | leaf
  | fork (left right : Shape)

inductive Slot : Shape → Type where
  | leaf : Slot .leaf
  | left : Slot left → Slot (.fork left right)
  | right : Slot right → Slot (.fork left right)

def Slot.depth : Slot shape → Nat
  | .leaf => 0
  | .left target | .right target => target.depth + 1

inductive Factors (R : Type*) : Shape → Type _ where
  | leaf : R → Factors R .leaf
  | fork : Factors R left → Factors R right → Factors R (.fork left right)

def Factors.toList : Factors R shape → List R
  | .leaf value => [value]
  | .fork left right => left.toList ++ right.toList

def Factors.replace (factors : Factors R shape) (slot : Slot shape) (replacement : R) :
    Factors R shape :=
  match factors, slot with
  | .leaf _, .leaf => .leaf replacement
  | .fork left right, .left target => .fork (left.replace target replacement) right
  | .fork left right, .right target => .fork left (right.replace target replacement)

inductive Cache (R : Type*) : Shape → Type _ where
  | leaf : R → Cache R .leaf
  | fork : R → Cache R left → Cache R right → Cache R (.fork left right)

def Cache.product : Cache R shape → R
  | .leaf value | .fork value _ _ => value

def Cache.combine [Mul R] (left : Cache R l) (right : Cache R r) : Cache R (.fork l r) :=
  .fork (left.product * right.product) left right

def Cache.build [Mul R] : Factors R shape → Cache R shape
  | .leaf value => .leaf value
  | .fork left right => combine (build left) (build right)

/-- The second component counts the matrix products performed by the edit.
Each untouched subtree is reused. -/
def Cache.refresh [Mul R] (cache : Cache R shape) (slot : Slot shape) (replacement : R) :
    Cache R shape × Nat :=
  match cache, slot with
  | .leaf _, .leaf => (.leaf replacement, 0)
  | .fork _ left right, .left target =>
    let (revised, work) := left.refresh target replacement
    (combine revised right, work + 1)
  | .fork _ left right, .right target =>
    let (revised, work) := right.refresh target replacement
    (combine left revised, work + 1)

theorem Cache.refresh_build [Mul R] (factors : Factors R shape) (slot : Slot shape)
    (replacement : R) :
    ((build factors).refresh slot replacement).1 = build (factors.replace slot replacement) := by
  induction slot with
  | leaf => cases factors; rfl
  | left target ih =>
    cases factors with
    | fork left right => simp [build, combine, refresh, Factors.replace, ih left]
  | right target ih =>
    cases factors with
    | fork left right => simp [build, combine, refresh, Factors.replace, ih right]

theorem Cache.refresh_work [Mul R] (cache : Cache R shape) (slot : Slot shape) (replacement : R) :
    (cache.refresh slot replacement).2 = slot.depth := by
  induction slot with
  | leaf => cases cache; rfl
  | left target ih => cases cache; simp [refresh, Slot.depth, ih]
  | right target ih => cases cache; simp [refresh, Slot.depth, ih]

theorem Cache.build_product [Monoid R] (factors : Factors R shape) :
    (build factors).product = factors.toList.prod := by
  induction factors with
  | leaf value => simp [build, Cache.product, Factors.toList]
  | fork left right ihl ihr =>
    change (build left).product * (build right).product = (left.toList ++ right.toList).prod
    rw [ihl, ihr, List.prod_append]

variable {S R : Type*} [Fintype S] [DecidableEq S] [Semiring R]

/-- Sum the weights of paths with prescribed endpoints in the given order. -/
def pathMass : List (Matrix S S R) → S → S → R
  | [], start, finish => if start = finish then 1 else 0
  | factor :: rest, start, finish =>
    ∑ via, factor start via * pathMass rest via finish

theorem product_apply_eq_pathMass (factors : List (Matrix S S R)) (start finish : S) :
    factors.prod start finish = pathMass factors start finish := by
  induction factors generalizing start with
  | nil => simp [pathMass, Matrix.one_apply]
  | cons factor rest ih => simp [List.prod_cons, Matrix.mul_apply, pathMass, ih]

theorem refreshed_pathMass (factors : Factors (Matrix S S R) shape) (slot : Slot shape)
    (replacement : Matrix S S R) (start finish : S) :
    ((Cache.build factors).refresh slot replacement).1.product start finish =
      pathMass (factors.replace slot replacement).toList start finish := by
  rw [Cache.refresh_build, Cache.build_product, product_apply_eq_pathMass]

section Controls

private def diagonal : Matrix (Fin 2) (Fin 2) Nat :=
  fun i j => if i = j then i.val + 1 else 0
private def coupled : Matrix (Fin 2) (Fin 2) Nat := fun _ _ => 1
private def twoFactors : Factors (Matrix (Fin 2) (Fin 2) Nat) (.fork .leaf .leaf) :=
  .fork (.leaf diagonal) (.leaf coupled)

/-- A scope-preserving substitution changes the query mass from 1 to 2. -/
theorem edit_changes_mass :
    (Cache.build twoFactors).product 0 1 = 1 ∧
      ((Cache.build twoFactors).refresh (.left .leaf) coupled).1.product 0 1 = 2 := by
  decide +kernel

/-- Reassociation is licensed. Reordering the leaves is observable. -/
theorem order_matters :
    pathMass [diagonal, coupled] 0 1 ≠ pathMass [coupled, diagonal] 0 1 := by
  decide +kernel

end Controls

#print axioms Cache.refresh_build
#print axioms Cache.refresh_work
#print axioms refreshed_pathMass
#print axioms edit_changes_mass
#print axioms order_matters

end Mettapedia.ProbabilityTheory.BayesianNetworks.IndexedFactorChain
