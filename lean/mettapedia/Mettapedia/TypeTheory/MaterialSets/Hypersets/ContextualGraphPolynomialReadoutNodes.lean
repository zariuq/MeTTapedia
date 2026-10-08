import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyNodes
import Mettapedia.TypeTheory.ContextualSmallFamilyUniverse

/-!
# Constructed graph nodes for contextual polynomial observations

States have actual label bodies; branch receipts have actual argument
bodies and a natural successor. Finite pairing syntax and its two
component embeddings retain receipt orientations. All body nodes and
their contextual actions are included at the original small bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutNodes

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams
universe u
variable {D : Type u} [Category.{u} D]
variable {states : D ⥤ Type u} (branches : states.Elements ⥤ Type u)
variable (labels : NaturalHom states (values D))
variable (arguments : NaturalHom (total branches) (values D))

def labelNodes : states.Elements ⥤ Type u :=
  restrict (elementMap labels) (ContextualGraphFamilyBodyNodes.family D)

def argumentNodes : (total branches).Elements ⥤ Type u :=
  restrict (elementMap arguments) (ContextualGraphFamilyBodyNodes.family D)

def labelRoots : (labelNodes labels).sections :=
  ⟨fun point => (labels.app point.1 point.2).2,
    fun {_ _} step => (ContextualGraphFamilyBodyNodes.roots D).property ((elementMap labels).map step)⟩

def argumentRoots : (argumentNodes branches arguments).sections :=
  ⟨fun point => (arguments.app point.1 point.2).2,
    fun {_ _} step => (ContextualGraphFamilyBodyNodes.roots D).property ((elementMap arguments).map step)⟩

inductive Node (point : D) : Type u
  | state : states.obj point → Node point
  | collection : states.obj point → Node point
  | branch : (total branches).obj point → Node point
  | label : (total (labelNodes labels)).obj point → Node point
  | argument : (total (argumentNodes branches arguments)).obj point → Node point
  | pair : Node point → Node point → Node point
  | left : Node point → Node point
  | right : Node point → Node point

def advance {first second : D} (arrival : first ⟶ second) :
    Node branches labels arguments first → Node branches labels arguments second
  | .state value => .state (states.map arrival value)
  | .collection value => .collection (states.map arrival value)
  | .branch receipt => .branch ((total branches).map arrival receipt)
  | .label receipt => .label ((total (labelNodes labels)).map arrival receipt)
  | .argument receipt => .argument ((total (argumentNodes branches arguments)).map arrival receipt)
  | .pair left right => .pair (advance arrival left) (advance arrival right)
  | .left value => .left (advance arrival value)
  | .right value => .right (advance arrival value)

theorem advance_identity (point : D) (node : Node branches labels arguments point) :
    advance branches labels arguments (𝟙 point) node = node := by
  induction node with
  | state value => exact congrArg Node.state (states.map_id_apply point value)
  | collection value => exact congrArg Node.collection (states.map_id_apply point value)
  | branch receipt => exact congrArg Node.branch ((total branches).map_id_apply point receipt)
  | label receipt => exact congrArg Node.label ((total (labelNodes labels)).map_id_apply point receipt)
  | argument receipt => exact congrArg Node.argument ((total (argumentNodes branches arguments)).map_id_apply point receipt)
  | pair left right first second => exact congrArg₂ Node.pair first second
  | left value same => exact congrArg Node.left same
  | right value same => exact congrArg Node.right same

theorem advance_composition {first middle last : D} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (node : Node branches labels arguments first) :
    advance branches labels arguments (earlier ≫ later) node =
      advance branches labels arguments later (advance branches labels arguments earlier node) := by
  induction node with
  | state value => exact congrArg Node.state (states.map_comp_apply earlier later value)
  | collection value => exact congrArg Node.collection (states.map_comp_apply earlier later value)
  | branch receipt => exact congrArg Node.branch ((total branches).map_comp_apply earlier later receipt)
  | label receipt => exact congrArg Node.label ((total (labelNodes labels)).map_comp_apply earlier later receipt)
  | argument receipt => exact congrArg Node.argument ((total (argumentNodes branches arguments)).map_comp_apply earlier later receipt)
  | pair left right first second => exact congrArg₂ Node.pair first second
  | left value same => exact congrArg Node.left same
  | right value same => exact congrArg Node.right same

def nodes : D ⥤ Type u where
  obj := Node branches labels arguments
  map arrival := TypeCat.ofHom (advance branches labels arguments arrival)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact advance_identity branches labels arguments point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact advance_composition branches labels arguments earlier later

def labelRoot (point : D) (value : states.obj point) : Node branches labels arguments point :=
  .label ⟨value, (labels.app point value).2⟩

def argumentRoot (point : D) (receipt : (total branches).obj point) : Node branches labels arguments point :=
  .argument ⟨receipt, (arguments.app point receipt).2⟩

theorem labelRoot_natural {first second : D} (arrival : first ⟶ second) (value : states.obj first) :
    advance branches labels arguments arrival (labelRoot branches labels arguments first value) =
      labelRoot branches labels arguments second (states.map arrival value) :=
  congrArg (fun node => (Node.label ⟨states.map arrival value, node⟩ : Node branches labels arguments second))
    ((labelRoots labels).property (CategoryOfElements.homMk (F := states)
      ⟨first, value⟩ ⟨second, states.map arrival value⟩ arrival rfl))

theorem argumentRoot_natural {first second : D} (arrival : first ⟶ second) (receipt : (total branches).obj first) :
    advance branches labels arguments arrival (argumentRoot branches labels arguments first receipt) =
      argumentRoot branches labels arguments second ((total branches).map arrival receipt) :=
  congrArg (fun node => (Node.argument ⟨(total branches).map arrival receipt, node⟩ : Node branches labels arguments second))
    ((argumentRoots branches arguments).property (CategoryOfElements.homMk (F := total branches)
      ⟨first, receipt⟩ ⟨second, (total branches).map arrival receipt⟩ arrival rfl))

variable (successor : NaturalHom (total branches) states)

inductive Edge (point : D) : Node branches labels arguments point → Node branches labels arguments point → Prop
  | stateFirst (value : states.obj point) : Edge point (.state value)
      (.left (.pair (labelRoot branches labels arguments point value) (labelRoot branches labels arguments point value)))
  | stateSecond (value : states.obj point) : Edge point (.state value)
      (.right (.pair (labelRoot branches labels arguments point value) (.collection value)))
  | collect (value : states.obj point) (branch : branches.obj ⟨point, value⟩) :
      Edge point (.collection value) (.branch ⟨value, branch⟩)
  | branchFirst (receipt : (total branches).obj point) : Edge point (.branch receipt)
      (.left (.pair (argumentRoot branches labels arguments point receipt) (argumentRoot branches labels arguments point receipt)))
  | branchSecond (receipt : (total branches).obj point) : Edge point (.branch receipt)
      (.right (.pair (argumentRoot branches labels arguments point receipt) (.state (successor.app point receipt))))
  | label (receipt : states.obj point) {first second : (labelNodes labels).obj ⟨point, receipt⟩}
      (available : (labels.app point receipt).1.edge point first second) :
      Edge point (.label ⟨receipt, first⟩) (.label ⟨receipt, second⟩)
  | argument (receipt : (total branches).obj point) {first second : (argumentNodes branches arguments).obj ⟨point, receipt⟩}
      (available : (arguments.app point receipt).1.edge point first second) :
      Edge point (.argument ⟨receipt, first⟩) (.argument ⟨receipt, second⟩)
  | pairFirst (left right : Node branches labels arguments point) : Edge point (.pair left right) (.left left)
  | pairSecond (left right : Node branches labels arguments point) : Edge point (.pair left right) (.right right)
  | left {parent child : Node branches labels arguments point} (available : Edge point parent child) :
      Edge point (.left parent) (.left child)
  | right {parent child : Node branches labels arguments point} (available : Edge point parent child) :
      Edge point (.right parent) (.right child)

theorem edge_transport {first second : D} (arrival : first ⟶ second)
    {parent child : Node branches labels arguments first} (available : Edge branches labels arguments successor first parent child) :
    Edge branches labels arguments successor second (advance branches labels arguments arrival parent)
      (advance branches labels arguments arrival child) := by
  induction available with
  | stateFirst value =>
    change Edge branches labels arguments successor second (.state (states.map arrival value))
      (.left (.pair (advance branches labels arguments arrival (labelRoot branches labels arguments first value))
        (advance branches labels arguments arrival (labelRoot branches labels arguments first value))))
    rw [labelRoot_natural]
    exact Edge.stateFirst _
  | stateSecond value =>
    change Edge branches labels arguments successor second (.state (states.map arrival value))
      (.right (.pair (advance branches labels arguments arrival (labelRoot branches labels arguments first value))
        (.collection (states.map arrival value))))
    rw [labelRoot_natural]
    exact Edge.stateSecond _
  | collect value branch => exact Edge.collect (states.map arrival value) _
  | branchFirst receipt =>
    change Edge branches labels arguments successor second (.branch ((total branches).map arrival receipt))
      (.left (.pair (advance branches labels arguments arrival (argumentRoot branches labels arguments first receipt))
        (advance branches labels arguments arrival (argumentRoot branches labels arguments first receipt))))
    rw [argumentRoot_natural]
    exact Edge.branchFirst _
  | branchSecond receipt =>
    change Edge branches labels arguments successor second (.branch ((total branches).map arrival receipt))
      (.right (.pair (advance branches labels arguments arrival (argumentRoot branches labels arguments first receipt))
        (.state (states.map arrival (successor.app first receipt)))))
    rw [argumentRoot_natural, successor.naturality]
    exact Edge.branchSecond _
  | label receipt edge =>
    exact Edge.label (states.map arrival receipt)
      (ContextualGraphFamilyBodyNodes.edge_transport D ((elementMap labels).map
        (CategoryOfElements.homMk (F := states) ⟨first, receipt⟩ ⟨second, states.map arrival receipt⟩ arrival rfl)) edge)
  | argument receipt edge =>
    exact Edge.argument ((total branches).map arrival receipt)
      (ContextualGraphFamilyBodyNodes.edge_transport D ((elementMap arguments).map
        (CategoryOfElements.homMk (F := total branches) ⟨first, receipt⟩
          ⟨second, (total branches).map arrival receipt⟩ arrival rfl)) edge)
  | pairFirst left right => exact Edge.pairFirst _ _
  | pairSecond left right => exact Edge.pairSecond _ _
  | left _ moved => exact Edge.left moved
  | right _ moved => exact Edge.right moved

def diagram : Diagram D where
  nodes := nodes branches labels arguments
  edge := Edge branches labels arguments successor
  edge_transport := edge_transport branches labels arguments successor

def value {point : D} (node : Node branches labels arguments point) : Value D point :=
  ⟨diagram branches labels arguments successor, node⟩

def reading : NaturalHom states (values D) where
  app _ node := value branches labels arguments successor (.state node)
  naturality _ _ := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutNodes
