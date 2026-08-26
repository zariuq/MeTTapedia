import Mettapedia.Cybernetics.HierarchicalComplexity.Basic

/-!
# The atomicity boundary of simple-action counting

Commons and Pekker's finite `phi n = 2^n` result counts simple actions in a
well-founded action decomposition.  That premise is substantive.  An atomless
or "gunky" decomposition, in which every node has a proper child, admits
neither a simple node nor a strictly decreasing ordinal rank.

The relational formulation here does not attribute atomless systems to the
Model of Hierarchical Complexity.  It is a negative control for extending the
model beyond its well-founded, simple-action setting.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity

universe uNode uOutcome

/-- A decomposition relation points from an immediate child to its parent. -/
structure DecompositionSystem where
  Node : Type uNode
  Child : Node → Node → Prop

namespace DecompositionSystem

/-- A node is simple when it has no immediate child. -/
def IsSimple (system : DecompositionSystem.{uNode})
    (parent : system.Node) : Prop :=
  ∀ child, ¬ system.Child child parent

/-- An atomless decomposition has a child below every node. -/
def IsAtomless (system : DecompositionSystem.{uNode}) : Prop :=
  ∀ parent, ∃ child, system.Child child parent

/-- A strict ordinal rank decreases along every decomposition edge. -/
def AdmitsStrictOrdinalRank (system : DecompositionSystem.{uNode}) : Prop :=
  ∃ rank : system.Node → Ordinal.{uNode},
    ∀ ⦃child parent⦄, system.Child child parent → rank child < rank parent

/-- Atomlessness excludes simple nodes. -/
theorem IsAtomless.not_isSimple
    {system : DecompositionSystem.{uNode}}
    (atomless : system.IsAtomless) (parent : system.Node) :
    ¬ system.IsSimple parent := by
  intro simple
  obtain ⟨child, childOf⟩ := atomless parent
  exact simple child childOf

/-- An inhabited atomless child relation is not well-founded. -/
theorem IsAtomless.not_wellFounded
    {system : DecompositionSystem.{uNode}}
    [Nonempty system.Node] (atomless : system.IsAtomless) :
    ¬ WellFounded system.Child := by
  intro wellFounded
  obtain ⟨minimal, _, noChild⟩ :=
    wellFounded.has_min Set.univ Set.univ_nonempty
  obtain ⟨child, childOf⟩ := atomless minimal
  exact noChild child (Set.mem_univ child) childOf

/-- A strict ordinal rank would make the child relation well-founded, so an
inhabited atomless decomposition cannot carry such a rank. -/
theorem IsAtomless.not_admitsStrictOrdinalRank
    {system : DecompositionSystem.{uNode}}
    [Nonempty system.Node] (atomless : system.IsAtomless) :
    ¬ system.AdmitsStrictOrdinalRank := by
  rintro ⟨rank, decreases⟩
  apply atomless.not_wellFounded
  exact (InvImage.wf rank Ordinal.lt_wf).mono
    (fun _ _ childOf => decreases childOf)

/-! ## Positive and negative controls -/

/-- A well-founded predecessor decomposition with `0` as a simple node. -/
def predecessor : DecompositionSystem.{0} where
  Node := Nat
  Child child parent := child + 1 = parent

/-- Zero is genuinely simple in the predecessor decomposition. -/
theorem predecessor_zero_isSimple :
    predecessor.IsSimple (show predecessor.Node from (0 : Nat)) := by
  change ∀ child : Nat, ¬ child + 1 = 0
  intro child childOf
  omega

/-- The predecessor decomposition has the expected strict ordinal rank. -/
theorem predecessor_admitsStrictOrdinalRank :
    predecessor.AdmitsStrictOrdinalRank := by
  change ∃ rank : Nat → Ordinal, ∀ ⦃child parent : Nat⦄,
    child + 1 = parent → rank child < rank parent
  refine ⟨fun n => (n : Ordinal), ?_⟩
  intro child parent childOf
  subst parent
  exact (Nat.cast_lt (α := Ordinal)).mpr (Nat.lt_succ_self child)

/-- A one-node self-decomposition is the smallest atomless negative control. -/
def selfLoop : DecompositionSystem.{0} where
  Node := Unit
  Child _ _ := True

theorem selfLoop_isAtomless : selfLoop.IsAtomless := by
  intro parent
  exact ⟨parent, trivial⟩

/-- The atomless self-loop cannot be represented by a decreasing ordinal
complexity. -/
theorem selfLoop_no_strictOrdinalRank :
    ¬ selfLoop.AdmitsStrictOrdinalRank := by
  letI : Nonempty selfLoop.Node := by
    change Nonempty Unit
    infer_instance
  exact selfLoop_isAtomless.not_admitsStrictOrdinalRank

end DecompositionSystem

namespace Action

/-- Every well-founded action tree reaches at least one simple leaf.  Hence
`Action` intentionally models atomic decompositions and cannot silently stand
for an atomless ambient ontology. -/
theorem nonempty_simpleLeaves {Outcome : Type uOutcome}
    (action : Action.{uNode, uOutcome} Outcome) :
    Nonempty (SimpleLeaves action) := by
  induction action with
  | simple => exact ⟨PUnit.unit⟩
  | compound Occurrence hasAtLeastTwo child organization inductionHypothesis =>
      obtain ⟨occurrence⟩ := hasAtLeastTwo.nonempty
      obtain ⟨leaf⟩ := inductionHypothesis occurrence
      exact ⟨⟨occurrence, leaf⟩⟩

/-- Accordingly, the simple-leaf cardinal of every action tree is nonzero. -/
theorem simpleLeafCardinal_ne_zero {Outcome : Type uOutcome}
    (action : Action.{uNode, uOutcome} Outcome) :
    simpleLeafCardinal action ≠ 0 := by
  rw [simpleLeafCardinal, Cardinal.mk_ne_zero_iff]
  exact nonempty_simpleLeaves action

end Action

end Mettapedia.Cybernetics.HierarchicalComplexity

#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.DecompositionSystem.IsAtomless.not_admitsStrictOrdinalRank
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.DecompositionSystem.selfLoop_no_strictOrdinalRank
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.Action.simpleLeafCardinal_ne_zero
