import Mettapedia.PLN.WorldModel.ProbabilisticWitnessComposition
import Mettapedia.PLN.Evidence.PLNJointEvidence
import Mettapedia.PLN.InferenceControl.CertifiedChaining.DependenceAwareChainComposition

/-!
# Factor-tree witnesses in the existing PLN evidence semantics

A Boolean variable at each factor-tree vertex gives a finite complete-world
space. Reindex its full nonnegative weight into `JointEvidence`; the existing
query-count operation then agrees with message elimination. The reindexing is
an abstract finite equivalence, not a BDD variable-order compiler.

The source-overlap bridge keeps conjunction of a composed proof's premises
distinct from disjunction of alternative proofs.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ProbabilisticWitnessComposition

open scoped BigOperators ENNReal
open Mettapedia.PLN.Evidence.PLNJointEvidence
open Mettapedia.PLN.Evidence.PLNJointEvidence.JointEvidence
open Mettapedia.PLN.InferenceControl.CertifiedChaining.DependenceAwareChainComposition

def Shape.variables : Shape → ℕ
  | .leaf => 1
  | .fork left right => 1 + left.variables + right.variables

theorem config_bool_card (shape : Shape) :
    Fintype.card (Config Bool shape) = 2 ^ shape.variables := by
  induction shape with
  | leaf => decide +kernel
  | fork left right il ir =>
      change Fintype.card (Bool × Config Bool left × Config Bool right) = _
      simp only [Fintype.card_prod, Fintype.card_bool, il, ir, Shape.variables,
        pow_add, pow_one]
      ring

noncomputable def treeWorldEquiv (shape : Shape) : Fin (2 ^ shape.variables) ≃ Config Bool shape :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, config_bool_card])

noncomputable def treeJointEvidence {shape : Shape} (factors : Factors Bool shape) :
    JointEvidence shape.variables :=
  fun world => ENNReal.ofReal (weight factors (treeWorldEquiv shape world))

theorem treeJoint_finite {shape : Shape} (factors : Factors Bool shape)
    (world : Fin (2 ^ shape.variables)) : treeJointEvidence factors world ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- The existing PLN complete-world query extractor gives precisely the
sum-product answer, after conversion of finite masses to real numbers. -/
theorem treeJoint_count_eq_messages {shape : Shape} (factors : Factors Bool shape)
    (valid : factors.Nonnegative) (query : Bool → Bool) :
    (countWorld (treeJointEvidence factors)
      (fun world => query (root (treeWorldEquiv shape world)))).toReal =
      ∑ x, rootWeight factors x * (if query x then 1 else 0) := by
  unfold countWorld
  rw [ENNReal.toReal_sum]
  · calc
      (∑ world, (if query (root (treeWorldEquiv shape world)) then
          treeJointEvidence factors world else 0).toReal) =
          ∑ world, weight factors (treeWorldEquiv shape world) *
            (if query (root (treeWorldEquiv shape world)) then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro world _
              split <;> simp_all [treeJointEvidence, ENNReal.toReal_ofReal,
                weight_nonneg factors valid]
      _ = ∑ configuration : Config Bool shape,
          weight factors configuration * (if query (root configuration) then 1 else 0) :=
            Equiv.sum_comp (treeWorldEquiv shape)
              (fun configuration : Config Bool shape => weight factors configuration *
                (if query (root (shape := shape) configuration) then 1 else 0))
      _ = _ := tree_elimination factors (fun x => if query x then 1 else 0)
  · intro world _
    split
    · exact treeJoint_finite factors world
    · exact ENNReal.zero_ne_top

theorem treeJoint_total_eq_messages {shape : Shape} (factors : Factors Bool shape)
    (valid : factors.Nonnegative) :
    (total (treeJointEvidence factors)).toReal = ∑ x, rootWeight factors x := by
  simpa [total, countWorld] using treeJoint_count_eq_messages factors valid (fun _ => true)

/-- A tree-elimination proof is an actual quantitative query witness: its
source enumerates full configurations, while its target uses local messages. -/
def treeEliminationWitness {Event X : Type*} [Fintype X] {shape : Shape}
    (factors : Factors X shape) (observations : Finset Event) :
    QueryWitness (Event := Event)
      (fun query : X → ℝ => ∑ c : Config X shape, weight factors c * query (root c))
      (fun query : X → ℝ => ∑ x, rootWeight factors x * query x) where
  observations := observations
  agrees := tree_elimination factors

/-- Alternative proofs require an overlap correction in the existing source
model. Even when both witnesses individually preserve their query, their
support events cannot be summed as independent proof evidence. -/
theorem alternative_witness_support {X : Type*} {source target : X → ℝ}
    (left right : QueryWitness (Event := ℕ) source target) (profile : SourceProfile) :
    sourceUnionStrength profile left.observations right.observations =
      sourceStrength profile left.observations + sourceStrength profile right.observations -
        (∏ event ∈ left.observations ∪ right.observations, (profile.prob event : ℝ)) := by
  exact sourceUnionStrength_eq_add_sub_overlap profile left.observations right.observations

/-- Sequential witness composition requires all support events. Their
shared observation identities are retained once in the independent-source
profile; no independence between the two composed proofs is assumed. -/
theorem composed_witness_support {X : Type*} {first middle last : X → ℝ}
    (left : QueryWitness (Event := ℕ) first middle)
    (right : QueryWitness (Event := ℕ) middle last) (profile : SourceProfile) :
    sourceStrength profile (left.comp right).observations =
      ∏ event ∈ left.observations ∪ right.observations, (profile.prob event : ℝ) := by
  exact Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency.sourceEvent_measureReal
    profile.prob profile.prob_le_one (left.observations ∪ right.observations)

#print axioms treeJoint_count_eq_messages
#print axioms treeJoint_total_eq_messages
#print axioms alternative_witness_support

end Mettapedia.PLN.WorldModel.ProbabilisticWitnessComposition
