import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-!
# Finite stabilization of dependency-local iteration

A simultaneous update may read only strictly lower-ranked nodes. After more
rounds than a node's natural-number rank, further iteration leaves that node
unchanged. This is independent of the value type and the initial assignment;
no monotonicity, lattice structure or finiteness of the node carrier is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Function

universe u v

/-- Dependency-local updates stabilize at every node once the iteration count
exceeds its rank. The locality premise concerns one update, not its iterates. -/
theorem iterate_stable_of_rank {Node : Type u} {Value : Type v}
    (update : (Node → Value) → Node → Value)
    (dependsOn : Node → Node → Prop) (rank : Node → Nat)
    (locality : ∀ node first second,
      (∀ dependency, dependsOn node dependency → first dependency = second dependency) →
      update first node = update second node)
    (decreases : ∀ node dependency, dependsOn node dependency → rank dependency < rank node)
    (initial : Node → Value) (rounds : Nat) :
    ∀ node, rank node < rounds →
      (update^[rounds + 1]) initial node = (update^[rounds]) initial node := by
  induction rounds with
  | zero => intro node impossible; omega
  | succ rounds ih =>
      intro node bounded
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' update rounds]
      apply locality
      intro dependency edge
      simpa only [Function.iterate_succ_apply'] using
        ih dependency (by have := decreases node dependency edge; omega)

/-- A uniform finite rank bound stabilizes the complete assignment. -/
theorem iterate_fixed_of_rank_bound {Node : Type u} {Value : Type v}
    (update : (Node → Value) → Node → Value)
    (dependsOn : Node → Node → Prop) (rank : Node → Nat)
    (locality : ∀ node first second,
      (∀ dependency, dependsOn node dependency → first dependency = second dependency) →
      update first node = update second node)
    (decreases : ∀ node dependency, dependsOn node dependency → rank dependency < rank node)
    (initial : Node → Value) (bound : Nat) (bounded : ∀ node, rank node < bound) :
    (update^[bound + 1]) initial = (update^[bound]) initial := by
  funext node
  exact iterate_stable_of_rank update dependsOn rank locality decreases initial bound node (bounded node)

#print axioms iterate_stable_of_rank
#print axioms iterate_fixed_of_rank_bound

end Mettapedia.Logic.Function
