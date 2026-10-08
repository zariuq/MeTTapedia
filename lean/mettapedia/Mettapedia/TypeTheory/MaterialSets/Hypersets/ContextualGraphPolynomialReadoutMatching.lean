import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutChildren

/-!
# Full-future matching of constructed polynomial observations

An actual stable state relation, matching labels and branch arguments,
induces material equality of the constructed state graphs. The proof
builds the relation on every pairing node and embedded body, then
coiterates the complete future graph matcher. Branch replies retain
their receipts and successor relation; no state readout is supplied.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutMatching

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphPolynomialReadoutNodes
universe u
variable {D : Type u} [Category.{u} D]

structure System (D : Type u) [Category.{u} D] where
  states : D ⥤ Type u
  branches : states.Elements ⥤ Type u
  labels : NaturalHom states (values D)
  arguments : NaturalHom (total branches) (values D)
  successor : NaturalHom (total branches) states

namespace System
abbrev diagram (system : System D) :=
  ContextualGraphPolynomialReadoutNodes.diagram system.branches system.labels system.arguments system.successor
abbrev Node (system : System D) := ContextualGraphPolynomialReadoutNodes.Node system.branches system.labels system.arguments
abbrev value (system : System D) {point : D} (node : system.Node point) :=
  ContextualGraphPolynomialReadoutNodes.value system.branches system.labels system.arguments system.successor node
abbrev read (system : System D) :=
  ContextualGraphPolynomialReadoutNodes.reading system.branches system.labels system.arguments system.successor
end System

structure Matching (first second : System D) where
  relation : (point : D) → first.states.obj point → second.states.obj point → Type u
  stable : ∀ {start finish : D} (arrival : start ⟶ finish) {left right}, relation start left right →
    relation finish (first.states.map arrival left) (second.states.map arrival right)
  labels : ∀ {point left right}, relation point left right →
    Equal (first.labels.app point left) (second.labels.app point right)
  forth : ∀ {point left right}, relation point left right → (branch : first.branches.obj ⟨point, left⟩) →
    Σ matched : second.branches.obj ⟨point, right⟩,
      Equal (first.arguments.app point ⟨left, branch⟩) (second.arguments.app point ⟨right, matched⟩) ×
        relation point (first.successor.app point ⟨left, branch⟩) (second.successor.app point ⟨right, matched⟩)
  back : ∀ {point left right}, relation point left right → (branch : second.branches.obj ⟨point, right⟩) →
    Σ matched : first.branches.obj ⟨point, left⟩,
      Equal (first.arguments.app point ⟨left, matched⟩) (second.arguments.app point ⟨right, branch⟩) ×
        relation point (first.successor.app point ⟨left, matched⟩) (second.successor.app point ⟨right, branch⟩)

namespace Matching
variable {first second : System D}

def symm (matching : Matching first second) : Matching second first where
  relation point left right := matching.relation point right left
  stable := fun {_ _} arrival {_ _} related => matching.stable arrival related
  labels related := (matching.labels related).symm
  forth related branch :=
    let response := matching.back related branch
    ⟨response.1, response.2.1.symm, response.2.2⟩
  back related branch :=
    let response := matching.forth related branch
    ⟨response.1, response.2.1.symm, response.2.2⟩

end Matching

variable {first second : System D} (matching : Matching first second)

inductive Witness (relation : (point : D) → first.states.obj point → second.states.obj point → Type u) (point : D) : first.Node point → second.Node point → Type u
  | established {left right} : Equal (first.value left) (second.value right) → Witness relation point left right
  | state {left right} : relation point left right → Witness relation point (.state left) (.state right)
  | collection {left right} : relation point left right → Witness relation point (.collection left) (.collection right)
  | branch (left : (total first.branches).obj point) (right : (total second.branches).obj point)
      (arguments : Equal (first.arguments.app point left) (second.arguments.app point right))
      (children : relation point (first.successor.app point left) (second.successor.app point right)) :
      Witness relation point (.branch left) (.branch right)
  | pair {left right otherLeft otherRight} : Witness relation point left otherLeft → Witness relation point right otherRight →
      Witness relation point (.pair left right) (.pair otherLeft otherRight)
  | left {leftNode rightNode} : Witness relation point leftNode rightNode → Witness relation point (.left leftNode) (.left rightNode)
  | right {leftNode rightNode} : Witness relation point leftNode rightNode → Witness relation point (.right leftNode) (.right rightNode)

namespace Witness

def symm {point : D} {left right} (proof : Witness matching.relation point left right) :
    Witness matching.symm.relation point right left := by
  induction proof with
  | established same => exact .established same.symm
  | state related => exact .state related
  | collection related => exact .collection related
  | branch left right arguments children => exact .branch right left arguments.symm children
  | pair _ _ first second => exact .pair first second
  | left _ next => exact .left next
  | right _ next => exact .right next

def advance {start finish : D} (arrival : start ⟶ finish) {left right}
    (proof : Witness matching.relation start left right) :
    Witness matching.relation finish (first.diagram.nodes.map arrival left) (second.diagram.nodes.map arrival right) := by
  induction proof with
  | established same => exact .established (Equal.restrict arrival same)
  | state related => exact .state (matching.stable arrival related)
  | collection related => exact .collection (matching.stable arrival related)
  | branch left right arguments children =>
    refine .branch ((total first.branches).map arrival left) ((total second.branches).map arrival right) ?_ ?_
    · exact (Equal.ofEq (first.arguments.naturality arrival left).symm).trans
        ((Equal.restrict arrival arguments).trans (Equal.ofEq (second.arguments.naturality arrival right)))
    · have next := matching.stable arrival children
      rw [first.successor.naturality, second.successor.naturality] at next
      exact next
  | pair _ _ left right => exact .pair left right
  | left _ next => exact .left next
  | right _ next => exact .right next

def labels {point : D} {left right} (related : matching.relation point left right) :
    Witness matching.relation point (labelRoot first.branches first.labels first.arguments point left)
      (labelRoot second.branches second.labels second.arguments point right) :=
  .established ((ContextualGraphPolynomialReadoutComponents.labelComparison first.branches first.labels
    first.arguments first.successor point left).symm.trans
      ((matching.labels related).trans (ContextualGraphPolynomialReadoutComponents.labelComparison
        second.branches second.labels second.arguments second.successor point right)))

def arguments {point : D} (left : (total first.branches).obj point) (right : (total second.branches).obj point)
    (same : Equal (first.arguments.app point left) (second.arguments.app point right)) :
    Witness matching.relation point (argumentRoot first.branches first.labels first.arguments point left)
      (argumentRoot second.branches second.labels second.arguments point right) :=
  .established ((ContextualGraphPolynomialReadoutComponents.argumentComparison first.branches first.labels
    first.arguments first.successor point left).symm.trans
      (same.trans (ContextualGraphPolynomialReadoutComponents.argumentComparison
        second.branches second.labels second.arguments second.successor point right)))

def currentForth {point : D} {left right} (proof : Witness matching.relation point left right)
    (child : Child D (first.value left)) :
    Σ response : Child D (second.value right), Witness matching.relation point child.val response.val := by
  induction proof with
  | established same =>
    let response := ContextualGraphRealizers.Realizer.currentForth same child
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
      (Node.branch ⟨right, response.1⟩)) decoded.2.down.symm)
      (.branch _ _ response.2.1 response.2.2)
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

def comparison {point : D} {left right} (proof : Witness matching.relation point left right) :
    Equal (first.value left) (second.value right) :=
  ContextualGraphRealizers.corec first.diagram second.diagram
    (fun _ _ _ related future child => currentForth matching (advance matching future.2 related) child)
    (fun _ _ _ related future child =>
      let response := currentForth matching.symm (advance matching.symm future.2 (symm matching related)) child
      ⟨response.1, symm matching.symm response.2⟩)
    proof

end Witness

def comparison {point : D} {left right} (related : matching.relation point left right) :
    Equal (first.read.app point left) (second.read.app point right) :=
  Witness.comparison matching (.state related)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutMatching
