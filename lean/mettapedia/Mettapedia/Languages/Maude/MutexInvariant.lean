import Mettapedia.Languages.Maude.MutexNormalization
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Permit conservation for normalized ground mutex markings. The invariant
is independent of the native search and supplies both the safe case and the
meaning of an extra-permit counterexample. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.MutexNormalization

/-- The single shared permit is either free or held by one critical
process. It cannot support both critical processes simultaneously. -/
def permitWeight (term : Term) : Nat :=
  if term = token "permit" ∨ term = token "crit1" ∨ term = token "crit2" then 1 else 0

def permitCount (parts : List Term) : Nat := (parts.map permitWeight).sum

theorem permitCount_append (left right : List Term) :
    permitCount (left ++ right) = permitCount left + permitCount right := by
  simp [permitCount]

theorem permitCount_perm {left right : List Term} (same : left.Perm right) : permitCount left = permitCount right :=
  (same.map permitWeight).sum_eq

theorem rule_permit_balance {row : Row} (member : row ∈ Examples.mutex.rules) :
    permitCount (operation.flatten row.left) = permitCount (operation.flatten row.right) := by
  simp only [Examples.mutex, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals decide_cbv

theorem ground_commit_permit_balance {sources residual : List Term} {row : Row}
    (member : row ∈ Examples.mutex.rules)
    (partition : sources.Perm (operation.flatten row.left ++ residual)) :
    permitCount sources = permitCount (operation.flatten row.right ++ residual) := by
  rw [permitCount_perm partition, permitCount_append, permitCount_append, rule_permit_balance member]

theorem no_two_critical (parts : List Term) (onePermit : permitCount parts = 1) :
    ¬ ∃ residual, parts.Perm (token "crit1" :: token "crit2" :: residual) := by
  rintro ⟨residual, partition⟩
  have same := permitCount_perm partition
  have first : permitWeight (token "crit1") = 1 := by decide_cbv
  have second : permitWeight (token "crit2") = 1 := by decide_cbv
  simp only [permitCount, List.map_cons, List.sum_cons, first, second] at same
  change permitCount parts = 1 + (1 + permitCount residual) at same
  omega

theorem expanded_has_one_permit : permitCount (operation.flatten expanded) = 1 := by decide_cbv

inductive GroundTransition : List Term → List Term → Prop where
  | fire (row : Row) (residual : List Term) {source : List Term} :
      row ∈ Examples.mutex.rules →
      source.Perm (operation.flatten row.left ++ residual) →
      GroundTransition source (operation.flatten row.right ++ residual)

theorem transition_permit_balance {source target : List Term} (step : GroundTransition source target) :
    permitCount source = permitCount target := by
  cases step with
  | fire row residual member partition => exact ground_commit_permit_balance member partition

theorem reachable_has_one_permit {target : List Term}
    (reachable : Relation.ReflTransGen GroundTransition (operation.flatten expanded) target) :
    permitCount target = 1 := by
  induction reachable with
  | refl => exact expanded_has_one_permit
  | tail _ step ih => exact (transition_permit_balance step).symm.trans ih

theorem reachable_mutual_exclusion {target : List Term}
    (reachable : Relation.ReflTransGen GroundTransition (operation.flatten expanded) target) :
    ¬ ∃ residual, target.Perm (token "crit1" :: token "crit2" :: residual) :=
  no_two_critical target (reachable_has_one_permit reachable)

#print axioms no_two_critical
#print axioms ground_commit_permit_balance
#print axioms reachable_mutual_exclusion

end Mettapedia.Languages.Maude.MutexNormalization
