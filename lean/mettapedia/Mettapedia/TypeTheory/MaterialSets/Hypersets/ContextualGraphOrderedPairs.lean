import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRealizedGraphs

/-!
# Contextual unordered and ordered pairs of actual graph values

The polynomial diagram carries both operand diagrams and pair roots at
every context. Its node action transports each actual operand node, so
pairing commutes strictly with context movement. Internal component
matchings are constructed by coiteration; they are not supplied material
dictionaries. Kuratowski pairs retain the two actual element denotations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphOrderedPairs

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
universe u v
variable {D : Type u} [Category.{u} D] (first second : Diagram D)

inductive Node (point : D) : Type u
  | first : first.nodes.obj point → Node point
  | second : second.nodes.obj point → Node point
  | pair : first.nodes.obj point → second.nodes.obj point → Node point

def advance {source target : D} (arrival : source ⟶ target) : Node first second source → Node first second target
  | .first node => .first (first.nodes.map arrival node)
  | .second node => .second (second.nodes.map arrival node)
  | .pair left right => .pair (first.nodes.map arrival left) (second.nodes.map arrival right)

def nodes : D ⥤ Type u where
  obj := Node first second
  map arrival := TypeCat.ofHom (advance first second arrival)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro node
    cases node with
    | first node => exact congrArg Node.first (first.nodes.map_id_apply point node)
    | second node => exact congrArg Node.second (second.nodes.map_id_apply point node)
    | pair left right =>
      change (Node.pair (first.nodes.map (𝟙 point) left) (second.nodes.map (𝟙 point) right) :
        Node first second point) = Node.pair left right
      rw [first.nodes.map_id_apply, second.nodes.map_id_apply]
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro node
    cases node with
    | first node => exact congrArg Node.first (first.nodes.map_comp_apply earlier later node)
    | second node => exact congrArg Node.second (second.nodes.map_comp_apply earlier later node)
    | pair left right =>
      change (Node.pair (first.nodes.map (earlier ≫ later) left) (second.nodes.map (earlier ≫ later) right) :
        Node first second _) = Node.pair
          (first.nodes.map later (first.nodes.map earlier left))
          (second.nodes.map later (second.nodes.map earlier right))
      rw [first.nodes.map_comp_apply, second.nodes.map_comp_apply]

inductive Edge (point : D) : Node first second point → Node first second point → Prop
  | left (left : first.nodes.obj point) (right : second.nodes.obj point) :
      Edge point (.pair left right) (.first left)
  | right (left : first.nodes.obj point) (right : second.nodes.obj point) :
      Edge point (.pair left right) (.second right)
  | first {parent child : first.nodes.obj point} (available : first.edge point parent child) :
      Edge point (.first parent) (.first child)
  | second {parent child : second.nodes.obj point} (available : second.edge point parent child) :
      Edge point (.second parent) (.second child)

def diagram : Diagram D where
  nodes := nodes first second
  edge := Edge first second
  edge_transport := by
    intro source target arrival parent child proof
    cases proof with
    | left left right => exact Edge.left (first.nodes.map arrival left) (second.nodes.map arrival right)
    | right left right => exact Edge.right (first.nodes.map arrival left) (second.nodes.map arrival right)
    | first available => exact Edge.first (first.edge_transport arrival available)
    | second available => exact Edge.second (second.edge_transport arrival available)

def liftFirst {point : D} (parent : first.nodes.obj point)
    (child : ContextualGraphRealizers.Child (diagram first second) point (Node.first parent)) :
    Σ actual : ContextualGraphRealizers.Child first point parent,
      PLift (child.val = Node.first actual.val) := by
  rcases child with ⟨node, proof⟩
  cases node with
  | first node =>
    have available : first.edge point parent node := by cases proof with | first edge => exact edge
    exact ⟨⟨node, available⟩, ⟨rfl⟩⟩
  | second node => exact False.elim (by cases proof)
  | pair left right => exact False.elim (by cases proof)

def liftSecond {point : D} (parent : second.nodes.obj point)
    (child : ContextualGraphRealizers.Child (diagram first second) point (Node.second parent)) :
    Σ actual : ContextualGraphRealizers.Child second point parent,
      PLift (child.val = Node.second actual.val) := by
  rcases child with ⟨node, proof⟩
  cases node with
  | first node => exact False.elim (by cases proof)
  | second node =>
    have available : second.edge point parent node := by cases proof with | second edge => exact edge
    exact ⟨⟨node, available⟩, ⟨rfl⟩⟩
  | pair left right => exact False.elim (by cases proof)

abbrev FirstWitness (point : D) (left : first.nodes.obj point) (right : (diagram first second).nodes.obj point) :=
  PLift (right = Node.first left)
abbrev SecondWitness (point : D) (left : second.nodes.obj point) (right : (diagram first second).nodes.obj point) :=
  PLift (right = Node.second left)

def firstForth (point : D) (left : first.nodes.obj point) (right : (diagram first second).nodes.obj point)
    (same : FirstWitness first second point left right) (future : ContextualGraphRealizers.Future point)
    (child : ContextualGraphRealizers.Child first future.1 (first.nodes.map future.2 left)) :
    Σ matched : ContextualGraphRealizers.Child (diagram first second) future.1
      ((diagram first second).nodes.map future.2 right),
      FirstWitness first second future.1 child.val matched.val := by
  rcases same with ⟨same⟩
  subst right
  exact ⟨⟨Node.first child.val, Edge.first child.property⟩, ⟨rfl⟩⟩

def firstBack (point : D) (left : first.nodes.obj point) (right : (diagram first second).nodes.obj point)
    (same : FirstWitness first second point left right) (future : ContextualGraphRealizers.Future point)
    (child : ContextualGraphRealizers.Child (diagram first second) future.1
      ((diagram first second).nodes.map future.2 right)) :
    Σ matched : ContextualGraphRealizers.Child first future.1 (first.nodes.map future.2 left),
      FirstWitness first second future.1 matched.val child.val := by
  rcases same with ⟨same⟩
  subst right
  let actual := liftFirst first second (first.nodes.map future.2 left) child
  exact ⟨actual.1, actual.2⟩

def secondForth (point : D) (left : second.nodes.obj point) (right : (diagram first second).nodes.obj point)
    (same : SecondWitness first second point left right) (future : ContextualGraphRealizers.Future point)
    (child : ContextualGraphRealizers.Child second future.1 (second.nodes.map future.2 left)) :
    Σ matched : ContextualGraphRealizers.Child (diagram first second) future.1
      ((diagram first second).nodes.map future.2 right),
      SecondWitness first second future.1 child.val matched.val := by
  rcases same with ⟨same⟩
  subst right
  exact ⟨⟨Node.second child.val, Edge.second child.property⟩, ⟨rfl⟩⟩

def secondBack (point : D) (left : second.nodes.obj point) (right : (diagram first second).nodes.obj point)
    (same : SecondWitness first second point left right) (future : ContextualGraphRealizers.Future point)
    (child : ContextualGraphRealizers.Child (diagram first second) future.1
      ((diagram first second).nodes.map future.2 right)) :
    Σ matched : ContextualGraphRealizers.Child second future.1 (second.nodes.map future.2 left),
      SecondWitness first second future.1 matched.val child.val := by
  rcases same with ⟨same⟩
  subst right
  let actual := liftSecond first second (second.nodes.map future.2 left) child
  exact ⟨actual.1, actual.2⟩

def firstComparison (point : D) (node : first.nodes.obj point) :
    Equal (⟨first, node⟩ : Value D point) (⟨diagram first second, Node.first node⟩ : Value D point) :=
  ContextualGraphRealizers.corec first (diagram first second)
    (firstForth first second) (firstBack first second) ⟨rfl⟩

def secondComparison (point : D) (node : second.nodes.obj point) :
    Equal (⟨second, node⟩ : Value D point) (⟨diagram first second, Node.second node⟩ : Value D point) :=
  ContextualGraphRealizers.corec second (diagram first second)
    (secondForth first second) (secondBack first second) ⟨rfl⟩

variable {first second} {point : D}

def pair (left right : Value D point) : Value D point :=
  ⟨diagram left.1 right.1, Node.pair left.2 right.2⟩

theorem pair_move {future : D} (arrival : point ⟶ future) (left right : Value D point) :
    move D arrival (pair left right) = pair (move D arrival left) (move D arrival right) := rfl

def pairFirst (left right : Value D point) : Member left (pair left right) :=
  ⟨⟨Node.first left.2, Edge.left left.2 right.2⟩, firstComparison left.1 right.1 point left.2⟩

def pairSecond (left right : Value D point) : Member right (pair left right) :=
  ⟨⟨Node.second right.2, Edge.right left.2 right.2⟩, secondComparison left.1 right.1 point right.2⟩

def pairEliminate {left right value : Value D point} (member : Member value (pair left right)) :
    Equal value left ⊕ Equal value right := by
  rcases member with ⟨⟨node, proof⟩, same⟩
  cases node with
  | first node =>
    have nodeSame : node = left.2 := by cases proof; rfl
    subst node
    exact .inl (same.trans (firstComparison left.1 right.1 point left.2).symm)
  | second node =>
    have nodeSame : node = right.2 := by cases proof; rfl
    subst node
    exact .inr (same.trans (secondComparison left.1 right.1 point right.2).symm)
  | pair first second => exact False.elim (by cases proof)

def pairMemberTransport {left right nextLeft nextRight : Value D point}
    (leftSame : Equal left nextLeft) (rightSame : Equal right nextRight)
    {value : Value D point} (member : Member value (pair left right)) : Member value (pair nextLeft nextRight) :=
  match pairEliminate member with
  | .inl same => Member.transportChild (same.trans leftSame).symm (pairFirst nextLeft nextRight)
  | .inr same => Member.transportChild (same.trans rightSame).symm (pairSecond nextLeft nextRight)

def pairCongr {left right nextLeft nextRight : Value D point}
    (leftSame : Equal left nextLeft) (rightSame : Equal right nextRight) :
    Equal (pair left right) (pair nextLeft nextRight) :=
  extensionality
    (fun _ arrival _ member => pairMemberTransport
      (Equal.restrict arrival leftSame) (Equal.restrict arrival rightSame) member)
    (fun _ arrival _ member => pairMemberTransport
      (Equal.restrict arrival leftSame.symm) (Equal.restrict arrival rightSame.symm) member)

def singleton (value : Value D point) : Value D point := pair value value

def singletonEliminate {value member : Value D point} (proof : Member member (singleton value)) : Equal member value :=
  match pairEliminate proof with
  | .inl same => same
  | .inr same => same

def singletonReflect {first second : Value D point} (same : Equal (singleton first) (singleton second)) :
    Equal first second :=
  singletonEliminate (Member.transportParent same (pairFirst first first))

def pairToSingletonFirst {left right only : Value D point}
    (same : Equal (pair left right) (singleton only)) : Equal left only :=
  singletonEliminate (Member.transportParent same (pairFirst left right))

def pairToSingletonSecond {left right only : Value D point}
    (same : Equal (pair left right) (singleton only)) : Equal right only :=
  singletonEliminate (Member.transportParent same (pairSecond left right))

def pairReflectSecond {left right nextLeft nextRight : Value D point}
    (same : Equal (pair left right) (pair nextLeft nextRight)) (firstSame : Equal left nextLeft) :
    Equal right nextRight :=
  match pairEliminate (Member.transportParent same (pairSecond left right)) with
  | .inr result => result
  | .inl collapsed =>
    match pairEliminate (Member.transportParent same.symm (pairSecond nextLeft nextRight)) with
    | .inl returned => collapsed.trans (firstSame.symm.trans returned.symm)
    | .inr returned => returned.symm

def orderedPair (left right : Value D point) : Value D point := pair (singleton left) (pair left right)

theorem orderedPair_move {future : D} (arrival : point ⟶ future) (left right : Value D point) :
    move D arrival (orderedPair left right) = orderedPair (move D arrival left) (move D arrival right) := rfl

def orderedPairCongr {left right nextLeft nextRight : Value D point}
    (leftSame : Equal left nextLeft) (rightSame : Equal right nextRight) :
    Equal (orderedPair left right) (orderedPair nextLeft nextRight) :=
  pairCongr (pairCongr leftSame leftSame) (pairCongr leftSame rightSame)

def orderedPairReflectFirst {left right nextLeft nextRight : Value D point}
    (same : Equal (orderedPair left right) (orderedPair nextLeft nextRight)) : Equal left nextLeft :=
  match pairEliminate (Member.transportParent same (pairFirst (singleton left) (pair left right))) with
  | .inl equality => singletonReflect equality
  | .inr equality => (pairToSingletonFirst equality.symm).symm

def orderedPairReflectSecond {left right nextLeft nextRight : Value D point}
    (same : Equal (orderedPair left right) (orderedPair nextLeft nextRight)) : Equal right nextRight :=
  let firstSame := orderedPairReflectFirst same
  match pairEliminate (Member.transportParent same (pairSecond (singleton left) (pair left right))) with
  | .inr equality => pairReflectSecond equality firstSame
  | .inl collapsed =>
    let rightSame := pairToSingletonSecond collapsed
    match pairEliminate (Member.transportParent same.symm
      (pairSecond (singleton nextLeft) (pair nextLeft nextRight))) with
    | .inl returned => rightSame.trans (firstSame.symm.trans (pairToSingletonSecond returned).symm)
    | .inr returned => rightSame.trans (pairToSingletonSecond (returned.trans collapsed)).symm

theorem orderedPair_kernel {left right nextLeft nextRight : Value D point} :
    Nonempty (Equal (orderedPair left right) (orderedPair nextLeft nextRight)) ↔
      Nonempty (Equal left nextLeft) ∧ Nonempty (Equal right nextRight) := by
  constructor
  · rintro ⟨same⟩
    exact ⟨⟨orderedPairReflectFirst same⟩, ⟨orderedPairReflectSecond same⟩⟩
  · rintro ⟨⟨leftSame⟩, ⟨rightSame⟩⟩
    exact ⟨orderedPairCongr leftSame rightSame⟩

/-- Two natural element denotations produce a natural ordered-pair
denotation in the same varying universe. -/
def orderedReading {base : D ⥤ Type v}
    (left right : ContextualWitnessCover.NaturalHom base (values D)) :
    ContextualWitnessCover.NaturalHom base (values D) where
  app point parameter := orderedPair (left.app point parameter) (right.app point parameter)
  naturality {source target} arrival parameter := by
    change orderedPair (move D arrival (left.app source parameter))
      (move D arrival (right.app source parameter)) =
      orderedPair (left.app target (base.map arrival parameter)) (right.app target (base.map arrival parameter))
    exact congrArg₂ (fun first second : Value D target => orderedPair first second)
      (left.naturality arrival parameter) (right.naturality arrival parameter)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphOrderedPairs
