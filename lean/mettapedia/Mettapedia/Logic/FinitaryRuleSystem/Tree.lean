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

/-- Number of rule nodes in a replay certificate. -/
def nodeCount {J : Type u} {W : Type v} : Derivation J W → Nat
  | .node _ _ n children => 1 + ∑ i : Fin n, nodeCount (children i)

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
  simp only [nodeCount_node]
  omega

end Derivation

end Mettapedia.Logic
