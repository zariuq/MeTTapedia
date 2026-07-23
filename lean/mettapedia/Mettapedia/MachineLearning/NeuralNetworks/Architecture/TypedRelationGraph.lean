import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Defs

/-!
# Finite typed relation graphs

This module isolates the graph payload consumed by a relation-aware neural
encoder.  Node-feature positions and serialized row indices are deliberately
separate: feature construction may reuse a semantic position, whereas rotary
attention uses the serialized row index.

The edge list is ordered because the executable encoder writes an edge-bias
cell once for each occurrence.  `lastRoleIn` specifies that last-write
semantics.  `RelationFunctional` is the exact condition under which edge-list
order becomes observationally irrelevant.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

universe uNode uNodeKind uFeature uRole

/-- One directed, typed edge occurrence in an ordered encoder payload. -/
structure EdgeOccurrence (Node : Type uNode) (Role : Type uRole) where
  source : Node
  target : Node
  role : Role
deriving DecidableEq, Repr

namespace EdgeOccurrence

variable {Node : Type uNode} {Role : Type uRole}

/-- Whether an edge occurrence writes the indicated ordered node pair. -/
def Matches (edge : EdgeOccurrence Node Role) (source target : Node) : Prop :=
  edge.source = source ∧ edge.target = target

instance [DecidableEq Node] (edge : EdgeOccurrence Node Role)
    (source target : Node) : Decidable (edge.Matches source target) :=
  inferInstanceAs (Decidable (edge.source = source ∧ edge.target = target))

end EdgeOccurrence

/-- A finite typed graph together with its exact serialized node order. -/
structure TypedRelationGraph
    (Node : Type uNode) (NodeKind : Type uNodeKind)
    (Feature : Type uFeature) (Role : Type uRole) where
  nodeDecidableEq : DecidableEq Node
  nodeCount : Nat
  serialize : Node → Fin nodeCount
  serialize_bijective : Function.Bijective serialize
  nodeKind : Node → NodeKind
  feature : Node → Feature
  featurePosition : Node → Nat
  active : Node → Bool
  edges : List (EdgeOccurrence Node Role)

namespace TypedRelationGraph

variable {Node : Type uNode} {NodeKind : Type uNodeKind}
  {Feature : Type uFeature} {Role : Type uRole}

/-- The index used by index-based rotary position. -/
def ropeIndex
    (graph : TypedRelationGraph Node NodeKind Feature Role) (node : Node) : Nat :=
  (graph.serialize node).val

/-- The serialization contains every row exactly once. -/
theorem serialize_injective
    (graph : TypedRelationGraph Node NodeKind Feature Role) :
    Function.Injective graph.serialize :=
  graph.serialize_bijective.1

/-- The serialization covers every declared row. -/
theorem serialize_surjective
    (graph : TypedRelationGraph Node NodeKind Feature Role) :
    Function.Surjective graph.serialize :=
  graph.serialize_bijective.2

end TypedRelationGraph

/-! ## Exact last-write edge semantics -/

section EdgeResolution

variable {Node : Type uNode} {Role : Type uRole} [DecidableEq Node]

/-- Resolve the final role written to one ordered node pair. -/
def lastRoleIn :
    List (EdgeOccurrence Node Role) → Node → Node → Option Role
  | [], _, _ => none
  | edge :: rest, source, target =>
      match lastRoleIn rest source target with
      | some role => some role
      | none =>
          if edge.Matches source target then some edge.role else none

/-- No role is written exactly when no edge occurrence addresses the pair. -/
theorem lastRoleIn_eq_none_iff
    (edges : List (EdgeOccurrence Node Role)) (source target : Node) :
    lastRoleIn edges source target = none ↔
      ∀ edge ∈ edges, ¬edge.Matches source target := by
  induction edges with
  | nil => simp [lastRoleIn]
  | cons edge rest inductionHypothesis =>
      cases hrest : lastRoleIn rest source target with
      | none =>
          by_cases hedge : edge.Matches source target
          · simp [lastRoleIn, hrest, hedge]
          · have hrestNone : ∀ candidate ∈ rest,
                ¬candidate.Matches source target :=
              inductionHypothesis.mp hrest
            simpa [lastRoleIn, hrest, hedge] using hrestNone
      | some role =>
          have hrestHas : ¬∀ candidate ∈ rest,
                ¬candidate.Matches source target := by
            intro noMatch
            have restNone : lastRoleIn rest source target = none :=
              inductionHypothesis.mpr noMatch
            rw [hrest] at restNone
            exact Option.some_ne_none role restNone
          rw [lastRoleIn, hrest]
          constructor
          · intro impossible
            exact (Option.some_ne_none role impossible).elim
          · intro allNoMatch
            exact (hrestHas fun candidate member =>
              allNoMatch candidate (by simp [member])).elim

/-- A resolved role comes from a real occurrence in the payload. -/
theorem exists_edge_of_lastRoleIn_eq_some
    (edges : List (EdgeOccurrence Node Role)) (source target : Node)
    (role : Role) (resolved : lastRoleIn edges source target = some role) :
    ∃ edge ∈ edges, edge.Matches source target ∧ edge.role = role := by
  induction edges generalizing role with
  | nil => simp [lastRoleIn] at resolved
  | cons edge rest inductionHypothesis =>
      cases hrest : lastRoleIn rest source target with
      | none =>
          by_cases hedge : edge.Matches source target
          · have roleEq : edge.role = role := by
              simpa [lastRoleIn, hrest, hedge] using resolved
            exact ⟨edge, by simp, hedge, roleEq⟩
          · simp [lastRoleIn, hrest, hedge] at resolved
      | some restRole =>
          have restRoleEq : restRole = role := by
            simpa [lastRoleIn, hrest] using resolved
          obtain ⟨candidate, member, addressed, candidateRole⟩ :=
            inductionHypothesis restRole hrest
          exact ⟨candidate, by simp [member], addressed,
            candidateRole.trans restRoleEq⟩

/-- No ordered pair carries two different relation roles.  Repeated identical
occurrences are permitted. -/
def RelationFunctional (edges : List (EdgeOccurrence Node Role)) : Prop :=
  ∀ ⦃left right : EdgeOccurrence Node Role⦄,
    left ∈ edges → right ∈ edges →
    left.source = right.source → left.target = right.target →
    left.role = right.role

/-- Under relation functionality, every matching occurrence determines the
resolved last-write role. -/
theorem lastRoleIn_eq_some_of_mem
    {edges : List (EdgeOccurrence Node Role)}
    (functional : RelationFunctional edges)
    {edge : EdgeOccurrence Node Role} (member : edge ∈ edges)
    {source target : Node} (addressed : edge.Matches source target) :
    lastRoleIn edges source target = some edge.role := by
  cases hresolved : lastRoleIn edges source target with
  | none =>
      have noMatch :=
        (lastRoleIn_eq_none_iff edges source target).mp hresolved
      exact (noMatch edge member addressed).elim
  | some resolvedRole =>
      obtain ⟨resolvedEdge, resolvedMember, resolvedMatches, roleEq⟩ :=
        exists_edge_of_lastRoleIn_eq_some edges source target resolvedRole
          hresolved
      have edgeRoleEq : edge.role = resolvedEdge.role :=
        functional member resolvedMember
          (addressed.1.trans resolvedMatches.1.symm)
          (addressed.2.trans resolvedMatches.2.symm)
      have resolvedRoleEq : resolvedRole = edge.role :=
        roleEq.symm.trans edgeRoleEq.symm
      exact congrArg some resolvedRoleEq

/-- Two edge payloads carry the same typed relation, ignoring occurrence order
and repeated identical occurrences. -/
def SameTypedRelations
    (left right : List (EdgeOccurrence Node Role)) : Prop :=
  ∀ source target role,
    (∃ edge ∈ left,
      edge.Matches source target ∧ edge.role = role) ↔
    (∃ edge ∈ right,
      edge.Matches source target ∧ edge.role = role)

/-- Functional payloads with the same typed relation have identical
last-write semantics, regardless of enumeration order. -/
theorem lastRoleIn_eq_of_sameTypedRelations
    {left right : List (EdgeOccurrence Node Role)}
    (_leftFunctional : RelationFunctional left)
    (rightFunctional : RelationFunctional right)
    (same : SameTypedRelations left right)
    (source target : Node) :
    lastRoleIn left source target = lastRoleIn right source target := by
  cases hleft : lastRoleIn left source target with
  | none =>
      have leftNoMatch :=
        (lastRoleIn_eq_none_iff left source target).mp hleft
      have rightNoMatch : ∀ edge ∈ right,
          ¬edge.Matches source target := by
        intro edge member addressed
        obtain ⟨leftEdge, leftMember, leftMatches, _⟩ :=
          (same source target edge.role).mpr
            ⟨edge, member, addressed, rfl⟩
        exact leftNoMatch leftEdge leftMember leftMatches
      exact ((lastRoleIn_eq_none_iff right source target).mpr
        rightNoMatch).symm
  | some role =>
      obtain ⟨leftEdge, leftMember, leftMatches, leftRole⟩ :=
        exists_edge_of_lastRoleIn_eq_some left source target role hleft
      obtain ⟨rightEdge, rightMember, rightMatches, rightRole⟩ :=
        (same source target role).mp
          ⟨leftEdge, leftMember, leftMatches, leftRole⟩
      have hright := lastRoleIn_eq_some_of_mem rightFunctional rightMember
        rightMatches
      simpa [rightRole] using hright.symm

end EdgeResolution

/-! ## Enumerating a deterministic typed relation -/

section RelationEnumeration

variable {Node : Type uNode} {Role : Type uRole}

/-- Emit at most one typed edge from an ordered node pair. -/
def edgeForPair (roleAt : Node → Node → Option Role) (pair : Node × Node) :
    List (EdgeOccurrence Node Role) :=
  match roleAt pair.1 pair.2 with
  | none => []
  | some role => [⟨pair.1, pair.2, role⟩]

/-- Enumerate a deterministic partial relation over a declared node order. -/
def edgesFromRoleAt (nodes : List Node)
    (roleAt : Node → Node → Option Role) :
    List (EdgeOccurrence Node Role) :=
  (nodes.product nodes).flatMap (edgeForPair roleAt)

/-- Every emitted edge records the value of the deterministic relation. -/
theorem roleAt_eq_some_of_mem_edgesFromRoleAt
    {nodes : List Node} {roleAt : Node → Node → Option Role}
    {edge : EdgeOccurrence Node Role}
    (member : edge ∈ edgesFromRoleAt nodes roleAt) :
    roleAt edge.source edge.target = some edge.role := by
  simp only [edgesFromRoleAt, List.mem_flatMap] at member
  obtain ⟨pair, _, emitted⟩ := member
  rcases pair with ⟨source, target⟩
  cases hrole : roleAt source target with
  | none => simp [edgeForPair, hrole] at emitted
  | some role =>
      simp [edgeForPair, hrole] at emitted
      subst edge
      exact hrole

/-- Enumerating a partial function can never assign two roles to one pair. -/
theorem edgesFromRoleAt_relationFunctional
    [DecidableEq Node] (nodes : List Node)
    (roleAt : Node → Node → Option Role) :
    RelationFunctional (edgesFromRoleAt nodes roleAt) := by
  intro left right leftMember rightMember sourceEq targetEq
  have leftRole := roleAt_eq_some_of_mem_edgesFromRoleAt leftMember
  have rightRole := roleAt_eq_some_of_mem_edgesFromRoleAt rightMember
  rw [sourceEq, targetEq] at leftRole
  exact Option.some.inj (leftRole.symm.trans rightRole)

end RelationEnumeration

namespace TypedRelationGraph

variable {Node : Type uNode} {NodeKind : Type uNodeKind}
  {Feature : Type uFeature} {Role : Type uRole}

/-- Resolve the executable last-write role of one ordered node pair. -/
def lastRole?
    (graph : TypedRelationGraph Node NodeKind Feature Role)
    (source target : Node) : Option Role := by
  letI := graph.nodeDecidableEq
  exact lastRoleIn graph.edges source target

/-- Graph-level relation functionality. -/
def relationFunctional
    (graph : TypedRelationGraph Node NodeKind Feature Role) : Prop := by
  letI := graph.nodeDecidableEq
  exact RelationFunctional graph.edges

/-- The graph contains an occurrence of one typed directed relation. -/
def CarriesRole
    (graph : TypedRelationGraph Node NodeKind Feature Role)
    (source target : Node) (role : Role) : Prop :=
  ∃ edge ∈ graph.edges,
    edge.Matches source target ∧ edge.role = role

/-- On a functional graph, extensional role membership and executable
last-write lookup coincide. -/
theorem lastRole?_eq_some_iff
    (graph : TypedRelationGraph Node NodeKind Feature Role)
    (functional : graph.relationFunctional)
    (source target : Node) (role : Role) :
    graph.lastRole? source target = some role ↔
      graph.CarriesRole source target role := by
  letI := graph.nodeDecidableEq
  change lastRoleIn graph.edges source target = some role ↔ _
  constructor
  · intro resolved
    exact exists_edge_of_lastRoleIn_eq_some graph.edges source target role
      resolved
  · rintro ⟨edge, member, addressed, roleEq⟩
    have resolved := lastRoleIn_eq_some_of_mem functional member addressed
    simpa [roleEq] using resolved

end TypedRelationGraph

/-! ## Position-preserving graph isomorphisms -/

section GraphIsomorphism

universe uLeftNode uRightNode

variable {LeftNode : Type uLeftNode} {RightNode : Type uRightNode}
  {NodeKind : Type uNodeKind} {Feature : Type uFeature}
  {Role : Type uRole}

/-- A structural typed-graph isomorphism.  It deliberately does not yet
assert that serialized rotary rows are preserved. -/
structure TypedRelationGraph.Isomorphism
    (left : TypedRelationGraph LeftNode NodeKind Feature Role)
    (right : TypedRelationGraph RightNode NodeKind Feature Role) where
  node : LeftNode ≃ RightNode
  nodeKind_preserved : ∀ source,
    right.nodeKind (node source) = left.nodeKind source
  feature_preserved : ∀ source,
    right.feature (node source) = left.feature source
  featurePosition_preserved : ∀ source,
    right.featurePosition (node source) = left.featurePosition source
  active_preserved : ∀ source,
    right.active (node source) = left.active source
  relation_preserved : ∀ source target role,
    left.CarriesRole source target role ↔
      right.CarriesRole (node source) (node target) role

/-- The valid symmetry class for index-based rotary attention also preserves
serialized rows. -/
structure TypedRelationGraph.PositionPreservingIsomorphism
    (left : TypedRelationGraph LeftNode NodeKind Feature Role)
    (right : TypedRelationGraph RightNode NodeKind Feature Role)
    extends left.Isomorphism right where
  ropeIndex_preserved : ∀ source,
    right.ropeIndex (toIsomorphism.node source) = left.ropeIndex source

/-- Everything read by one relation-aware attention score before learned
linear maps are applied. -/
@[ext]
structure TypedRelationGraph.PairInput (Feature : Type uFeature)
    (Role : Type uRole) where
  sourceFeature : Feature
  targetFeature : Feature
  sourceRopeIndex : Nat
  targetRopeIndex : Nat
  edgeRole : Option Role
  sourceActive : Bool
  targetActive : Bool
deriving DecidableEq, Repr

namespace TypedRelationGraph

/-- Extract the graph-dependent inputs of one ordered attention pair. -/
def pairInput
    (graph : TypedRelationGraph LeftNode NodeKind Feature Role)
    (source target : LeftNode) : PairInput Feature Role where
  sourceFeature := graph.feature source
  targetFeature := graph.feature target
  sourceRopeIndex := graph.ropeIndex source
  targetRopeIndex := graph.ropeIndex target
  edgeRole := graph.lastRole? source target
  sourceActive := graph.active source
  targetActive := graph.active target

/-- Structural relation isomorphism transports exact last-write roles once
both payloads are relation-functional. -/
theorem Isomorphism.lastRole_preserved
    {left : TypedRelationGraph LeftNode NodeKind Feature Role}
    {right : TypedRelationGraph RightNode NodeKind Feature Role}
    (isomorphism : left.Isomorphism right)
    (leftFunctional : left.relationFunctional)
    (rightFunctional : right.relationFunctional)
    (source target : LeftNode) :
    right.lastRole? (isomorphism.node source) (isomorphism.node target) =
      left.lastRole? source target := by
  cases hleft : left.lastRole? source target with
  | none =>
      have hright : right.lastRole? (isomorphism.node source)
          (isomorphism.node target) = none := by
        cases hrightSome : right.lastRole? (isomorphism.node source)
            (isomorphism.node target) with
        | none => rfl
        | some role =>
            have rightCarries :=
              (right.lastRole?_eq_some_iff rightFunctional _ _ role).mp
                hrightSome
            have leftCarries :=
              (isomorphism.relation_preserved source target role).mpr
                rightCarries
            have leftSome :=
              (left.lastRole?_eq_some_iff leftFunctional _ _ role).mpr
                leftCarries
            rw [hleft] at leftSome
            cases leftSome
      exact hright
  | some role =>
      have leftCarries :=
        (left.lastRole?_eq_some_iff leftFunctional _ _ role).mp hleft
      have rightCarries :=
        (isomorphism.relation_preserved source target role).mp leftCarries
      have hright :=
        (right.lastRole?_eq_some_iff rightFunctional _ _ role).mpr
          rightCarries
      exact hright

/-- A position-preserving typed-graph isomorphism preserves every
graph-dependent input to one attention score. -/
theorem PositionPreservingIsomorphism.pairInput_preserved
    {left : TypedRelationGraph LeftNode NodeKind Feature Role}
    {right : TypedRelationGraph RightNode NodeKind Feature Role}
    (isomorphism : left.PositionPreservingIsomorphism right)
    (leftFunctional : left.relationFunctional)
    (rightFunctional : right.relationFunctional)
    (source target : LeftNode) :
    right.pairInput (isomorphism.node source) (isomorphism.node target) =
      left.pairInput source target := by
  apply PairInput.ext <;> simp only [pairInput]
  · exact isomorphism.feature_preserved source
  · exact isomorphism.feature_preserved target
  · exact isomorphism.ropeIndex_preserved source
  · exact isomorphism.ropeIndex_preserved target
  · exact isomorphism.toIsomorphism.lastRole_preserved
      leftFunctional rightFunctional source target
  · exact isomorphism.active_preserved source
  · exact isomorphism.active_preserved target

end TypedRelationGraph

end GraphIsomorphism

/-! ## Executable positive and negative boundary fixtures -/

namespace TypedRelationGraphFixtures

inductive FixtureRole
  | forward
  | backward
deriving DecidableEq, Repr

def forwardEdge : EdgeOccurrence Bool FixtureRole :=
  ⟨false, true, .forward⟩

def backwardEdge : EdgeOccurrence Bool FixtureRole :=
  ⟨true, false, .backward⟩

def functionalOrderA : List (EdgeOccurrence Bool FixtureRole) :=
  [forwardEdge, backwardEdge]

def functionalOrderB : List (EdgeOccurrence Bool FixtureRole) :=
  [backwardEdge, forwardEdge]

theorem functionalOrderA_functional : RelationFunctional functionalOrderA := by
  intro left right leftMember rightMember sourceEq targetEq
  simp [functionalOrderA] at leftMember rightMember
  rcases leftMember with rfl | rfl <;>
    rcases rightMember with rfl | rfl <;>
    simp_all [forwardEdge, backwardEdge]

theorem functionalOrderB_functional : RelationFunctional functionalOrderB := by
  intro left right leftMember rightMember sourceEq targetEq
  simp [functionalOrderB] at leftMember rightMember
  rcases leftMember with rfl | rfl <;>
    rcases rightMember with rfl | rfl <;>
    simp_all [forwardEdge, backwardEdge]

theorem functionalOrders_same :
    SameTypedRelations functionalOrderA functionalOrderB := by
  intro source target role
  have sameMembers : ∀ edge : EdgeOccurrence Bool FixtureRole,
      edge ∈ functionalOrderA ↔ edge ∈ functionalOrderB := by
    intro edge
    simp [functionalOrderA, functionalOrderB, or_comm]
  constructor
  · rintro ⟨edge, member, addressed, roleEq⟩
    exact ⟨edge, (sameMembers edge).mp member, addressed, roleEq⟩
  · rintro ⟨edge, member, addressed, roleEq⟩
    exact ⟨edge, (sameMembers edge).mpr member, addressed, roleEq⟩

/-- Reordering a functional relation payload cannot change its edge-bias role. -/
theorem functional_reordering_preserves_last_write (source target : Bool) :
    lastRoleIn functionalOrderA source target =
      lastRoleIn functionalOrderB source target :=
  lastRoleIn_eq_of_sameTypedRelations functionalOrderA_functional
    functionalOrderB_functional functionalOrders_same source target

def conflictingOrderA : List (EdgeOccurrence Bool FixtureRole) :=
  [forwardEdge, ⟨false, true, .backward⟩]

def conflictingOrderB : List (EdgeOccurrence Bool FixtureRole) :=
  [⟨false, true, .backward⟩, forwardEdge]

def conflictingBackwardEdge : EdgeOccurrence Bool FixtureRole :=
  ⟨false, true, .backward⟩

theorem conflictingOrderA_not_functional :
    ¬RelationFunctional conflictingOrderA := by
  intro functional
  have roleEq := functional
    (left := forwardEdge) (right := conflictingBackwardEdge)
    (by simp [conflictingOrderA])
    (by simp [conflictingOrderA, conflictingBackwardEdge]) rfl rfl
  cases roleEq

theorem conflictingOrderB_not_functional :
    ¬RelationFunctional conflictingOrderB := by
  intro functional
  have roleEq := functional
    (left := conflictingBackwardEdge) (right := forwardEdge)
    (by simp [conflictingOrderB, conflictingBackwardEdge])
    (by simp [conflictingOrderB]) rfl rfl
  cases roleEq

/-- Without relation functionality, reversing duplicate writes changes the
role observed by the encoder. -/
theorem conflicting_reordering_changes_last_write :
    lastRoleIn conflictingOrderA false true = some .backward ∧
      lastRoleIn conflictingOrderB false true = some .forward := by
  simp [conflictingOrderA, conflictingOrderB, forwardEdge, lastRoleIn,
    EdgeOccurrence.Matches]

/-- Reusing a semantic feature position does not identify rotary row indices. -/
theorem equal_feature_position_can_have_distinct_rope_rows :
    let featurePosition : Bool → Nat := fun _ => 0
    let ropeIndex : Bool → Nat := fun node => if node then 1 else 0
    featurePosition false = featurePosition true ∧
      ropeIndex false ≠ ropeIndex true := by
  decide

def constantBoolGraph : TypedRelationGraph Bool Unit Unit Unit where
  nodeDecidableEq := inferInstance
  nodeCount := 2
  serialize := finTwoEquiv.symm
  serialize_bijective := finTwoEquiv.symm.bijective
  nodeKind := fun _ => ()
  feature := fun _ => ()
  featurePosition := fun _ => 0
  active := fun _ => true
  edges := []

/-- Swapping two otherwise indistinguishable nodes is an ordinary typed-graph
isomorphism. -/
def boolSwapIsomorphism : constantBoolGraph.Isomorphism constantBoolGraph where
  node := Equiv.swap false true
  nodeKind_preserved := by simp [constantBoolGraph]
  feature_preserved := by simp [constantBoolGraph]
  featurePosition_preserved := by simp [constantBoolGraph]
  active_preserved := by simp [constantBoolGraph]
  relation_preserved := by
    intro source target role
    simp [TypedRelationGraph.CarriesRole, constantBoolGraph]

/-- Ordinary graph isomorphism is too broad for index-based rotary attention:
the nontrivial node swap changes the serialized row. -/
theorem unrestricted_isomorphism_need_not_preserve_rope_index :
    ¬∀ source, constantBoolGraph.ropeIndex (boolSwapIsomorphism.node source) =
      constantBoolGraph.ropeIndex source := by
  intro preserves
  have atFalse := preserves false
  simp [constantBoolGraph, boolSwapIsomorphism, TypedRelationGraph.ropeIndex,
    finTwoEquiv] at atFalse

end TypedRelationGraphFixtures

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
