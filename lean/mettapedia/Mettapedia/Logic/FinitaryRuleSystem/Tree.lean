import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mettapedia.Logic.Derivation

/-!
# Finite derivation-tree measurements

Structural measurements of generic finitary replay trees, independent of any
rule predicate or object logic.
-/

set_option autoImplicit false

namespace Mettapedia.Logic

open scoped BigOperators

universe u v

namespace Derivation

/-- Sum over the explicit finite index enumeration. The carrier and its
nodup certificate are supplied directly; no `Fintype.complete` membership
interface is needed to measure the stored children. -/
def childSum (n : Nat) (counts : Fin n → Nat) : Nat :=
  (⟨(List.finRange n : Multiset (Fin n)), List.nodup_finRange n⟩ : Finset (Fin n)).sum counts

@[simp] theorem childSum_zero (counts : Fin 0 → Nat) : childSum 0 counts = 0 := rfl
@[simp] theorem childSum_one (counts : Fin 1 → Nat) : childSum 1 counts = counts 0 := rfl
@[simp] theorem childSum_two (counts : Fin 2 → Nat) :
    childSum 2 counts = counts 0 + counts 1 := rfl
@[simp] theorem childSum_three (counts : Fin 3 → Nat) :
    childSum 3 counts = counts 0 + (counts 1 + counts 2) := rfl

/-- Number of rule nodes in a replay certificate. -/
def nodeCount {J : Type u} {W : Type v} : Derivation J W → Nat
  | .node _ _ n children => 1 + childSum n (fun i => nodeCount (children i))

@[simp]
theorem nodeCount_node {J : Type u} {W : Type v}
    (conclusion : J) (witness : W) (n : Nat)
    (children : Fin n → Derivation J W) :
    nodeCount (.node conclusion witness n children) =
      1 + ∑ i : Fin n, nodeCount (children i) := rfl

/-- Every finite derivation tree contains its root node. -/
theorem nodeCount_pos {J : Type u} {W : Type v}
    (certificate : Derivation J W) : 0 < certificate.nodeCount := by
  cases certificate
  change 0 < 1 + _
  omega

end Derivation

end Mettapedia.Logic
