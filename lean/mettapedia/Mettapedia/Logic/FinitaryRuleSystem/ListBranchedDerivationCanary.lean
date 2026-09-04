import Mettapedia.Logic.FinitaryRuleSystem.ListBranchedDerivation

/-!
# Canaries for list-branched finite replay

The positive example has two differently labelled premises in a fixed order.
The negative examples swap those premises or contract them to one.  Exact
conversion preserves the accepted certificate, while replay rejects both
changes.  Thus neither branch order nor branch multiplicity is silently
quotiented by the list/indexed equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem
namespace ListBranchedDerivationCanary

inductive OrderedPairJudgment where
  | left
  | right
  | joined
deriving DecidableEq

inductive OrderedPairWitness where
  | leftAxiom
  | rightAxiom
  | join
deriving DecidableEq

inductive OrderedPairRule :
    List OrderedPairJudgment → OrderedPairJudgment → Prop where
  | leftAxiom : OrderedPairRule [] .left
  | rightAxiom : OrderedPairRule [] .right
  | join : OrderedPairRule [.left, .right] .joined

def orderedPairIsInstance (witness : OrderedPairWitness)
    (premises : List OrderedPairJudgment)
    (conclusion : OrderedPairJudgment) : Bool :=
  match witness with
  | .leftAxiom => decide (premises = [] ∧ conclusion = .left)
  | .rightAxiom => decide (premises = [] ∧ conclusion = .right)
  | .join => decide (premises = [.left, .right] ∧ conclusion = .joined)

abbrev orderedPairInterface : RuleWitness OrderedPairRule where
  W := OrderedPairWitness
  isInstance := orderedPairIsInstance
  sound := by
    intro witness premises conclusion accepted
    cases witness with
    | leftAxiom =>
        simp only [orderedPairIsInstance, decide_eq_true_eq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact OrderedPairRule.leftAxiom
    | rightAxiom =>
        simp only [orderedPairIsInstance, decide_eq_true_eq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact OrderedPairRule.rightAxiom
    | join =>
        simp only [orderedPairIsInstance, decide_eq_true_eq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact OrderedPairRule.join
  complete := by
    intro premises conclusion rule
    cases rule with
    | leftAxiom =>
        exact ⟨.leftAxiom, by simp [orderedPairIsInstance]⟩
    | rightAxiom =>
        exact ⟨.rightAxiom, by simp [orderedPairIsInstance]⟩
    | join =>
        exact ⟨.join, by simp [orderedPairIsInstance]⟩

open ListBranchedDerivation

def leftLeaf :
    ListBranchedDerivation OrderedPairJudgment orderedPairInterface.W :=
  .node .left .leftAxiom []

def rightLeaf :
    ListBranchedDerivation OrderedPairJudgment orderedPairInterface.W :=
  .node .right .rightAxiom []

/-- Positive control: the authored order and multiplicity are accepted. -/
def orderedTree :
    ListBranchedDerivation OrderedPairJudgment orderedPairInterface.W :=
  .node .joined .join [leftLeaf, rightLeaf]

/-- Negative control: exchanging the two premises changes the rule instance. -/
def swappedTree :
    ListBranchedDerivation OrderedPairJudgment orderedPairInterface.W :=
  .node .joined .join [rightLeaf, leftLeaf]

/-- Negative control: contraction changes a two-premise rule to one premise. -/
def contractedTree :
    ListBranchedDerivation OrderedPairJudgment orderedPairInterface.W :=
  .node .joined .join [leftLeaf]

theorem orderedTree_accepted :
    orderedTree.valid orderedPairInterface = true := by
  unfold orderedTree leftLeaf rightLeaf
  rw [valid_node]
  simp [orderedPairInterface, orderedPairIsInstance]
  constructor
  · rw [valid_node]
    simp [orderedPairIsInstance]
  · rw [valid_node]
    simp [orderedPairIsInstance]

theorem swappedTree_rejected :
    swappedTree.valid orderedPairInterface = false := by
  unfold swappedTree leftLeaf rightLeaf
  rw [valid_node]
  simp [orderedPairInterface, orderedPairIsInstance]

theorem contractedTree_rejected :
    contractedTree.valid orderedPairInterface = false := by
  unfold contractedTree leftLeaf
  rw [valid_node]
  simp [orderedPairInterface, orderedPairIsInstance]

theorem orderedTree_has_three_nodes : orderedTree.nodeCount = 3 := by
  unfold orderedTree leftLeaf rightLeaf
  rw [nodeCount_node]
  simp [nodeCount_node]

theorem contractedTree_has_two_nodes : contractedTree.nodeCount = 2 := by
  unfold contractedTree leftLeaf
  rw [nodeCount_node]
  simp [nodeCount_node]

/-- The nontrivial certificate survives both representation changes exactly. -/
theorem orderedTree_roundtrip :
    ofIndexed (toIndexed orderedTree) = orderedTree :=
  ofIndexed_toIndexed orderedTree

/-- Exact replay agrees after conversion to indexed branching. -/
theorem orderedTree_indexed_accepted :
    (toIndexed orderedTree).valid orderedPairInterface = true := by
  exact (valid_toIndexed orderedPairInterface orderedTree).trans
    orderedTree_accepted

/-- The initial fold computes the same root and replay result. -/
theorem orderedTree_replay_is_fold :
    (ListNodeAlgebra.fold
      (ListNodeAlgebra.replayAlgebra orderedPairInterface) orderedTree).down =
      (.joined, true) := by
  rw [ListNodeAlgebra.fold_replay]
  exact congrArg (fun accepted => (OrderedPairJudgment.joined, accepted))
    orderedTree_accepted

/-- Order sensitivity is observable at replay, not merely in raw syntax. -/
theorem order_is_not_quotiented :
    orderedTree.valid orderedPairInterface ≠
      swappedTree.valid orderedPairInterface := by
  simp [orderedTree_accepted, swappedTree_rejected]

/-- Multiplicity sensitivity is observable at replay. -/
theorem multiplicity_is_not_quotiented :
    orderedTree.valid orderedPairInterface ≠
      contractedTree.valid orderedPairInterface := by
  simp [orderedTree_accepted, contractedTree_rejected]

end ListBranchedDerivationCanary
end Mettapedia.Logic.FinitaryRuleSystem
