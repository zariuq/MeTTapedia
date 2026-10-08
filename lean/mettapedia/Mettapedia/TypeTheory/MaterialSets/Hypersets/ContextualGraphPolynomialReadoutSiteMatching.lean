import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutMatching
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphUniverseLift

/-!
# Material polynomial comparison across a successor site

The original diagram is raised with all its nodes and edges. The target
polynomial graph is constructed independently. A natural relation on the
actual states, with recovery of both branch directions and comparison of
actual label and argument bodies, constructs matching at every future
world. Internal pair nodes and all body edges remain in the comparison.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutSiteMatching

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphPolynomialReadoutNodes ContextualGraphPolynomialReadoutMatching
universe u
variable {D : Type u} [Category.{u} D]
abbrev Raised := ContextualGraphUniverseLift.Raised (D := D)

structure Matching (first : System D) (second : System (Raised (D := D))) where
  relation : (point : Raised (D := D)) → first.states.obj point.down → second.states.obj point → Type (u+1)
  stable : ∀ {start finish : Raised (D := D)} (arrival : start ⟶ finish) {left right}, relation start left right →
    relation finish (first.states.map arrival.down left) (second.states.map arrival right)
  labels : ∀ {point left right}, relation point left right →
    Equal (ContextualGraphUniverseLift.value (first.labels.app point.down left)) (second.labels.app point right)
  forth : ∀ {point left right}, relation point left right → (branch : first.branches.obj ⟨point.down, left⟩) →
    Σ matched : second.branches.obj ⟨point, right⟩,
      Equal (ContextualGraphUniverseLift.value (first.arguments.app point.down ⟨left, branch⟩))
        (second.arguments.app point ⟨right, matched⟩) ×
          relation point (first.successor.app point.down ⟨left, branch⟩) (second.successor.app point ⟨right, matched⟩)
  back : ∀ {point left right}, relation point left right → (branch : second.branches.obj ⟨point, right⟩) →
    Σ matched : first.branches.obj ⟨point.down, left⟩,
      Equal (ContextualGraphUniverseLift.value (first.arguments.app point.down ⟨left, matched⟩))
        (second.arguments.app point ⟨right, branch⟩) ×
          relation point (first.successor.app point.down ⟨left, matched⟩) (second.successor.app point ⟨right, branch⟩)

variable {first : System D} {second : System (Raised (D := D))} (matching : Matching first second)

inductive Witness (relation : (point : Raised (D := D)) → first.states.obj point.down → second.states.obj point → Type (u+1))
    (point : Raised (D := D)) : first.Node point.down → second.Node point → Type (u+1)
  | established {left right} : Equal (ContextualGraphUniverseLift.value (first.value left)) (second.value right) →
      Witness relation point left right
  | state {left right} : relation point left right → Witness relation point (.state left) (.state right)
  | collection {left right} : relation point left right → Witness relation point (.collection left) (.collection right)
  | branch (left : (total first.branches).obj point.down) (right : (total second.branches).obj point)
      (arguments : Equal (ContextualGraphUniverseLift.value (first.arguments.app point.down left))
        (second.arguments.app point right))
      (children : relation point (first.successor.app point.down left) (second.successor.app point right)) :
      Witness relation point (.branch left) (.branch right)
  | pair {left right otherLeft otherRight} : Witness relation point left otherLeft → Witness relation point right otherRight →
      Witness relation point (.pair left right) (.pair otherLeft otherRight)
  | left {leftNode rightNode} : Witness relation point leftNode rightNode → Witness relation point (.left leftNode) (.left rightNode)
  | right {leftNode rightNode} : Witness relation point leftNode rightNode → Witness relation point (.right leftNode) (.right rightNode)

namespace Witness

def advance {start finish : Raised (D := D)} (arrival : start ⟶ finish) {left right}
    (proof : Witness matching.relation start left right) :
    Witness matching.relation finish (first.diagram.nodes.map arrival.down left) (second.diagram.nodes.map arrival right) := by
  induction proof with
  | established same => exact .established (Equal.restrict arrival same)
  | state related => exact .state (matching.stable arrival related)
  | collection related => exact .collection (matching.stable arrival related)
  | branch left right arguments children =>
    refine .branch ((total first.branches).map arrival.down left) ((total second.branches).map arrival right) ?_ ?_
    · exact (ContextualGraphUniverseLift.preserve (Equal.ofEq (first.arguments.naturality arrival.down left).symm)).trans
        ((Equal.restrict arrival arguments).trans (Equal.ofEq (second.arguments.naturality arrival right)))
    · have next := matching.stable arrival children
      rw [first.successor.naturality, second.successor.naturality] at next
      exact next
  | pair _ _ left right => exact .pair left right
  | left _ next => exact .left next
  | right _ next => exact .right next

def labels {point : Raised (D := D)} {left right} (related : matching.relation point left right) :
    Witness matching.relation point (labelRoot first.branches first.labels first.arguments point.down left)
      (labelRoot second.branches second.labels second.arguments point right) :=
  .established ((ContextualGraphUniverseLift.preserve (ContextualGraphPolynomialReadoutComponents.labelComparison
    first.branches first.labels first.arguments first.successor point.down left)).symm.trans
      ((matching.labels related).trans (ContextualGraphPolynomialReadoutComponents.labelComparison
        second.branches second.labels second.arguments second.successor point right)))

def arguments {point : Raised (D := D)} (left : (total first.branches).obj point.down)
    (right : (total second.branches).obj point)
    (same : Equal (ContextualGraphUniverseLift.value (first.arguments.app point.down left)) (second.arguments.app point right)) :
    Witness matching.relation point (argumentRoot first.branches first.labels first.arguments point.down left)
      (argumentRoot second.branches second.labels second.arguments point right) :=
  .established ((ContextualGraphUniverseLift.preserve (ContextualGraphPolynomialReadoutComponents.argumentComparison
    first.branches first.labels first.arguments first.successor point.down left)).symm.trans
      (same.trans (ContextualGraphPolynomialReadoutComponents.argumentComparison
        second.branches second.labels second.arguments second.successor point right)))

def currentForth {point : Raised (D := D)} {left right} (proof : Witness matching.relation point left right)
    (child : Child D (first.value left)) :
    Σ response : Child (Raised (D := D)) (second.value right), Witness matching.relation point child.val response.val := by
  induction proof with
  | @established left right same =>
    let response := ContextualGraphRealizers.Realizer.currentForth same
      ((ContextualGraphUniverseLift.childDecoder (first.value left)).symm child)
    exact ⟨response.1, .established response.2⟩
  | @state left right related =>
    cases ContextualGraphPolynomialReadoutChildren.stateChild first.branches first.labels first.arguments
        first.successor left child with
    | inl same =>
      refine ⟨⟨_, Edge.stateFirst right⟩, ?_⟩
      rw [same.down]
      exact .left (.pair (labels matching related) (labels matching related))
    | inr same =>
      refine ⟨⟨_, Edge.stateSecond right⟩, ?_⟩
      rw [same.down]
      exact .right (.pair (labels matching related) (.collection related))
  | @collection left right related =>
    let decoded := ContextualGraphPolynomialReadoutChildren.collectionChild first.branches first.labels first.arguments
      first.successor left child
    let response := matching.forth related decoded.1
    refine ⟨⟨_, Edge.collect right response.1⟩, ?_⟩
    exact cast (congrArg (fun node => Witness matching.relation point node
      (Node.branch ⟨right, response.1⟩)) decoded.2.down.symm) (.branch _ _ response.2.1 response.2.2)
  | branch left right argumentSame children =>
    cases ContextualGraphPolynomialReadoutChildren.branchChild first.branches first.labels first.arguments
        first.successor left child with
    | inl same =>
      refine ⟨⟨_, Edge.branchFirst right⟩, ?_⟩
      rw [same.down]
      exact .left (.pair (arguments matching left right argumentSame) (arguments matching left right argumentSame))
    | inr same =>
      refine ⟨⟨_, Edge.branchSecond right⟩, ?_⟩
      rw [same.down]
      exact .right (.pair (arguments matching left right argumentSame) (.state children))
  | @pair left right otherLeft otherRight firstProof secondProof firstInduction secondInduction =>
    cases ContextualGraphPolynomialReadoutChildren.pairChild first.branches first.labels first.arguments
        first.successor left right child with
    | inl same =>
      refine ⟨⟨_, Edge.pairFirst otherLeft otherRight⟩, ?_⟩
      rw [same.down]
      exact .left firstProof
    | inr same =>
      refine ⟨⟨_, Edge.pairSecond otherLeft otherRight⟩, ?_⟩
      rw [same.down]
      exact .right secondProof
  | @left left right proof induction =>
    let decoded := ContextualGraphPolynomialReadoutChildren.leftChild first.branches first.labels first.arguments
      first.successor left child
    let response := induction decoded.1
    refine ⟨⟨_, Edge.left response.1.property⟩, ?_⟩
    exact cast (congrArg (fun node => Witness matching.relation point node
      (Node.left response.1.val)) decoded.2.down.symm) (.left response.2)
  | @right left right proof induction =>
    let decoded := ContextualGraphPolynomialReadoutChildren.rightChild first.branches first.labels first.arguments
      first.successor left child
    let response := induction decoded.1
    refine ⟨⟨_, Edge.right response.1.property⟩, ?_⟩
    exact cast (congrArg (fun node => Witness matching.relation point node
      (Node.right response.1.val)) decoded.2.down.symm) (.right response.2)

def currentBack {point : Raised (D := D)} {left right} (proof : Witness matching.relation point left right)
    (child : Child (Raised (D := D)) (second.value right)) :
    Σ response : Child D (first.value left), Witness matching.relation point response.val child.val := by
  induction proof with
  | @established left right same =>
    let response := ContextualGraphRealizers.Realizer.currentBack same child
    exact ⟨ContextualGraphUniverseLift.childDecoder (first.value left) response.1, .established response.2⟩
  | @state left right related =>
    cases ContextualGraphPolynomialReadoutChildren.stateChild second.branches second.labels second.arguments
        second.successor right child with
    | inl same =>
      refine ⟨⟨_, Edge.stateFirst left⟩, ?_⟩
      rw [same.down]
      exact .left (.pair (labels matching related) (labels matching related))
    | inr same =>
      refine ⟨⟨_, Edge.stateSecond left⟩, ?_⟩
      rw [same.down]
      exact .right (.pair (labels matching related) (.collection related))
  | @collection left right related =>
    let decoded := ContextualGraphPolynomialReadoutChildren.collectionChild second.branches second.labels second.arguments
      second.successor right child
    let response := matching.back related decoded.1
    refine ⟨⟨_, Edge.collect left response.1⟩, ?_⟩
    exact cast (congrArg (fun node => Witness matching.relation point
      (Node.branch ⟨left, response.1⟩) node) decoded.2.down.symm) (.branch _ _ response.2.1 response.2.2)
  | branch left right argumentSame children =>
    cases ContextualGraphPolynomialReadoutChildren.branchChild second.branches second.labels second.arguments
        second.successor right child with
    | inl same =>
      refine ⟨⟨_, Edge.branchFirst left⟩, ?_⟩
      rw [same.down]
      exact .left (.pair (arguments matching left right argumentSame) (arguments matching left right argumentSame))
    | inr same =>
      refine ⟨⟨_, Edge.branchSecond left⟩, ?_⟩
      rw [same.down]
      exact .right (.pair (arguments matching left right argumentSame) (.state children))
  | @pair left right otherLeft otherRight firstProof secondProof firstInduction secondInduction =>
    cases ContextualGraphPolynomialReadoutChildren.pairChild second.branches second.labels second.arguments
        second.successor otherLeft otherRight child with
    | inl same =>
      refine ⟨⟨_, Edge.pairFirst left right⟩, ?_⟩
      rw [same.down]
      exact .left firstProof
    | inr same =>
      refine ⟨⟨_, Edge.pairSecond left right⟩, ?_⟩
      rw [same.down]
      exact .right secondProof
  | @left left right proof induction =>
    let decoded := ContextualGraphPolynomialReadoutChildren.leftChild second.branches second.labels second.arguments
      second.successor right child
    let response := induction decoded.1
    refine ⟨⟨_, Edge.left response.1.property⟩, ?_⟩
    exact cast (congrArg (fun node => Witness matching.relation point
      (Node.left response.1.val) node) decoded.2.down.symm) (.left response.2)
  | @right left right proof induction =>
    let decoded := ContextualGraphPolynomialReadoutChildren.rightChild second.branches second.labels second.arguments
      second.successor right child
    let response := induction decoded.1
    refine ⟨⟨_, Edge.right response.1.property⟩, ?_⟩
    exact cast (congrArg (fun node => Witness matching.relation point
      (Node.right response.1.val) node) decoded.2.down.symm) (.right response.2)

def comparison {point : Raised (D := D)} {left right} (proof : Witness matching.relation point left right) :
    Equal (ContextualGraphUniverseLift.value (first.value left)) (second.value right) :=
  ContextualGraphRealizers.corec (ContextualGraphUniverseLift.diagram first.diagram) second.diagram
    (witness := fun point left right => Witness matching.relation point left.down right)
    (fun _ _ _ related future child =>
      currentForth matching (advance matching future.2 related)
        (ContextualGraphUniverseLift.childDecoder _ child))
    (fun _ _ _ related future child =>
      let response := currentBack matching (advance matching future.2 related) child
      ⟨(ContextualGraphUniverseLift.childDecoder _).symm response.1, response.2⟩)
    proof

end Witness

def comparison {point : Raised (D := D)} {left right} (related : matching.relation point left right) :
    Equal (ContextualGraphUniverseLift.value (first.read.app point.down left)) (second.read.app point right) :=
  Witness.comparison matching (.state related)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutSiteMatching
