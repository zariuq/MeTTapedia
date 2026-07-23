import Mettapedia.Languages.MeTTa.PrimeCellCausalFrontier

/-!
# Policy-neutral control for Prime cell-causal search

The operational semantics determines which transitions are legal.  Search
control is a separate layer over certified nodes: it may reorder a frontier,
defer expansion, or explicitly prune nodes, but it cannot manufacture a state
transition or an accepted answer.

Breadth-first and depth-first integration are concrete inhabitants of the same
interface.  Term orders, learned rankings, and weighted control fields belong
in additional inhabitants rather than in the semantic step relation.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCellCausalControl

open PrimeCellCausalSemantics
open PrimeCellCausalFrontier

structure TransitionSystem (State : Type*) where
  step : State → State → Prop

inductive Trace {State : Type*} (system : TransitionSystem State) :
    State → State → Prop where
  | refl (state) : Trace system state state
  | tail {first middle last} :
      Trace system first middle → system.step middle last →
      Trace system first last

structure CertifiedNode
    {State : Type*} (system : TransitionSystem State) (root : State) where
  state : State
  trace : Trace system root state

def CertifiedNode.advance
    {State : Type*} {system : TransitionSystem State} {root : State}
    (node : CertifiedNode system root) {after : State}
    (step : system.step node.state after) : CertifiedNode system root :=
  { state := after
    trace := .tail node.trace step }

/-- A deferred expansion exposes an origin view independently of forcing the
successor computation.  Every returned child must extend the parent by a
certified trace. -/
structure DeferredExpansion
    {State Origin : Type*} (system : TransitionSystem State) (root : State) where
  parent : CertifiedNode system root
  origin : Origin
  force : Unit → List (CertifiedNode system root)
  extendsParent : ∀ child ∈ force (),
    Trace system parent.state child.state

def inspectDeferred
    {State Origin : Type*} {system : TransitionSystem State} {root : State}
    (frontier : List
      (DeferredExpansion (Origin := Origin) system root)) : List Origin :=
  frontier.map DeferredExpansion.origin

@[simp]
theorem inspectDeferred_length
    {State Origin : Type*} {system : TransitionSystem State} {root : State}
    (frontier : List
      (DeferredExpansion (Origin := Origin) system root)) :
    (inspectDeferred frontier).length = frontier.length := by
  simp [inspectDeferred]

/-- Integration controls where newly generated nodes enter an existing
frontier.  `complete` prevents a discipline from manufacturing or silently
discarding nodes. -/
structure FrontierDiscipline (Node : Type*) where
  integrate : List Node → List Node → List Node
  complete : ∀ pending generated,
    (integrate pending generated).Perm (pending ++ generated)

def breadthFirst (Node : Type*) : FrontierDiscipline Node where
  integrate pending generated := pending ++ generated
  complete _ _ := .refl _

def depthFirst (Node : Type*) : FrontierDiscipline Node where
  integrate pending generated := generated ++ pending
  complete _ _ := List.perm_append_comm

/-- The two elementary disciplines expose a genuine scheduling choice while
preserving the same frontier. -/
theorem breadthFirst_depthFirst_discriminator :
    (breadthFirst Nat).integrate [0, 1] [2, 3] = [0, 1, 2, 3] ∧
    (depthFirst Nat).integrate [0, 1] [2, 3] = [2, 3, 0, 1] := by
  decide

/-- A ranking policy may reorder a frontier but preserves it exactly.  A
KBO/WPO ranker or a learned/weighted controller belongs here. -/
structure ReorderingPolicy (Node : Type*) where
  reorder : List Node → List Node
  preserves : ∀ frontier, (reorder frontier).Perm frontier

/-- A ranked controller supplies the score that explains its ordering.  Term
orders, probability-derived priorities, and learned scores can instantiate the
same contract without becoming part of the transition relation. -/
structure RankedPolicy (Node Score : Type*) [LE Score]
    extends ReorderingPolicy Node where
  rank : Node → Score
  ordered : ∀ frontier,
    (reorder frontier).Pairwise fun left right => rank left ≤ rank right

theorem ReorderingPolicy.mem_iff
    {Node : Type*} (policy : ReorderingPolicy Node)
    {frontier : List Node} {node : Node} :
    node ∈ policy.reorder frontier ↔ node ∈ frontier := by
  exact (policy.preserves frontier).mem_iff

theorem RankedPolicy.mem_iff
    {Node Score : Type*} [LE Score] (policy : RankedPolicy Node Score)
    {frontier : List Node} {node : Node} :
    node ∈ policy.reorder frontier ↔ node ∈ frontier := by
  exact policy.toReorderingPolicy.mem_iff

/-- Pruning is deliberately a different interface from ordering.  It may
discard nodes but cannot introduce a node that was not already present. -/
structure PruningPolicy (Node : Type*) where
  prune : List Node → List Node
  noManufacture : ∀ {frontier node},
    node ∈ prune frontier → node ∈ frontier

def keepAll (Node : Type*) : PruningPolicy Node where
  prune frontier := frontier
  noManufacture member := member

theorem FrontierDiscipline.mem_integrate_iff
    {Node : Type*} (discipline : FrontierDiscipline Node)
    {pending generated : List Node} {node : Node} :
    node ∈ discipline.integrate pending generated ↔
      node ∈ pending ∨ node ∈ generated := by
  rw [(discipline.complete pending generated).mem_iff]
  simp

variable
  {Rule Source Producer ExpectedType Occurrence Outcome Event Publication
    Answer Fault : Type*}
  [DecidableEq Rule] [DecidableEq Source] [DecidableEq Producer]
  [DecidableEq ExpectedType] [DecidableEq Occurrence] [DecidableEq Outcome]
  [DecidableEq Event] [DecidableEq Publication] [DecidableEq Answer]
  [DecidableEq Fault]

local notation "ApplicationStateT" =>
  ApplicationState (Rule := Rule) (Source := Source)
    (Producer := Producer) (ExpectedType := ExpectedType)
    (Occurrence := Occurrence) (Outcome := Outcome) (Event := Event)
    (Publication := Publication) (Answer := Answer) (Fault := Fault)

def cellCausalSystem
    (model : Model Producer Occurrence Outcome Event) :
    TransitionSystem ApplicationStateT where
  step := ApplicationStep model

omit [DecidableEq Fault] in
/-- Any node certified for the application system is reachable only by the
cell-causal semantic relation, regardless of the controller that selected it. -/
theorem certifiedNode_reachable
    (model : Model Producer Occurrence Outcome Event)
    (root : ApplicationStateT)
    (node : CertifiedNode (cellCausalSystem model) root) :
    Trace (cellCausalSystem model) root node.state :=
  node.trace

end Mettapedia.Languages.MeTTa.PrimeCellCausalControl
