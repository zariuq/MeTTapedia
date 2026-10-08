import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyNodes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyRepresentation

/-!
# Contextual families with actual attached material bodies

Each literal native receipt carries its declared contextual graph body.
The constructed carrier has one root child per receipt and retains every
internal body node and edge. Naturality of the supplied denotation is
used to construct the entire diagram action; no material representative
or small section carrier is selected. Receipt tags and material matching
remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodies

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualGraphDiagrams ContextualSmallFamilyUniverse ContextualRealizedGraphs
universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (native : base.Elements ⥤ Type u) (termReading : NaturalHom (total native) (values D))

def bodyNodes : (total native).Elements ⥤ Type u :=
  restrict (elementMap termReading) (ContextualGraphFamilyBodyNodes.family D)

def bodyRoots : (bodyNodes native termReading).sections :=
  ⟨fun point => (termReading.app point.1 point.2).2,
    fun {_ _} step => (ContextualGraphFamilyBodyNodes.roots D).property ((elementMap termReading).map step)⟩

def bodyReading : NaturalHom (total (bodyNodes native termReading)) (values D) where
  app point receipt := ContextualGraphFamilyBodyNodes.reroot D
    (termReading.app point receipt.1) receipt.2
  naturality {first second} arrival receipt :=
    (ContextualGraphFamilyBodyNodes.reroot_map D
      ((elementMap termReading).map (CategoryOfElements.homMk (F := total native)
        ⟨first, receipt.1⟩ ⟨second, (total native).map arrival receipt.1⟩ arrival rfl)) receipt.2).symm

def nodes : D ⥤ Type u := ContextualSmallMapConstructions.coproduct base (total (bodyNodes native termReading))

inductive Edge (point : D) : (nodes native termReading).obj point → (nodes native termReading).obj point → Prop
  | root (parameter : base.obj point) (term : native.obj ⟨point, parameter⟩) :
      Edge point (.inl parameter) (.inr ⟨⟨parameter, term⟩, (termReading.app point ⟨parameter, term⟩).2⟩)
  | inner (receipt : (total native).obj point) {first second : (bodyNodes native termReading).obj ⟨point, receipt⟩}
      (available : (termReading.app point receipt).1.edge point first second) :
      Edge point (.inr ⟨receipt, first⟩) (.inr ⟨receipt, second⟩)

theorem edge_transport {first second : D} (arrival : first ⟶ second)
    {parent child : (nodes native termReading).obj first} (available : Edge native termReading first parent child) :
    Edge native termReading second ((nodes native termReading).map arrival parent)
      ((nodes native termReading).map arrival child) := by
  cases available with
  | root parameter term =>
    let step := CategoryOfElements.homMk (F := total native) ⟨first, ⟨parameter, term⟩⟩
      ⟨second, (total native).map arrival ⟨parameter, term⟩⟩ arrival rfl
    have rootMoves := (bodyRoots native termReading).property step
    change Edge native termReading second (.inl (base.map arrival parameter))
      (.inr ⟨(total native).map arrival ⟨parameter, term⟩,
        (bodyNodes native termReading).map step (termReading.app first ⟨parameter, term⟩).2⟩)
    change (bodyNodes native termReading).map step (termReading.app first ⟨parameter, term⟩).2 =
      (termReading.app second ((total native).map arrival ⟨parameter, term⟩)).2 at rootMoves
    rw [rootMoves]
    exact Edge.root _ _
  | inner receipt edge =>
    exact Edge.inner ((total native).map arrival receipt)
      (ContextualGraphFamilyBodyNodes.edge_transport D
        ((elementMap termReading).map (CategoryOfElements.homMk (F := total native)
          ⟨first, receipt⟩ ⟨second, (total native).map arrival receipt⟩ arrival rfl)) edge)

def diagram : Diagram D where
  nodes := nodes native termReading
  edge := Edge native termReading
  edge_transport := edge_transport native termReading

def carrier (point : D) (parameter : base.obj point) : Value D point :=
  ⟨diagram native termReading, .inl parameter⟩

def component (point : D) (receipt : (total native).obj point)
    (node : (bodyNodes native termReading).obj ⟨point, receipt⟩) : Value D point :=
  ⟨diagram native termReading, .inr ⟨receipt, node⟩⟩

theorem carrier_move {first second : D} (arrival : first ⟶ second) (parameter : base.obj first) :
    move D arrival (carrier native termReading first parameter) =
      carrier native termReading second (base.map arrival parameter) := rfl

def parent : NaturalHom base (values D) where
  app := carrier native termReading
  naturality := carrier_move native termReading

def literal : base.Elements ⥤ Type u := ContextualGraphReceiptFamilies.along (parent native termReading)

def encode (point : base.Elements) (term : native.obj point) : (literal native termReading).obj point :=
  ⟨.inr ⟨⟨point.2, term⟩, (termReading.app point.1 ⟨point.2, term⟩).2⟩, Edge.root point.2 term⟩

def decode (point : base.Elements) (receipt : (literal native termReading).obj point) : native.obj point := by
  rcases point with ⟨point, parameter⟩
  rcases receipt with ⟨child, edge⟩
  cases child with
  | inl impossible => exact False.elim (by cases edge)
  | inr receipt =>
    rcases receipt with ⟨⟨other, term⟩, node⟩
    have same : other = parameter := by cases edge; rfl
    subst other
    exact term

theorem decode_encode (point : base.Elements) (term : native.obj point) :
    decode native termReading point (encode native termReading point term) = term := rfl

theorem encode_decode (point : base.Elements) (receipt : (literal native termReading).obj point) :
    encode native termReading point (decode native termReading point receipt) = receipt := by
  rcases point with ⟨point, parameter⟩
  rcases receipt with ⟨child, edge⟩
  cases child with
  | inl impossible => exact False.elim (by cases edge)
  | inr receipt =>
    rcases receipt with ⟨⟨other, term⟩, node⟩
    have same : other = parameter := by cases edge; rfl
    subst other
    have atRoot : node = (termReading.app point ⟨parameter, term⟩).2 := by cases edge; rfl
    subst node
    rfl

def decoder (point : base.Elements) : (literal native termReading).obj point ≃ native.obj point where
  toFun := decode native termReading point
  invFun := encode native termReading point
  left_inv := encode_decode native termReading point
  right_inv := decode_encode native termReading point

theorem encode_naturality {first second : base.Elements} (step : first ⟶ second)
    (term : native.obj first) :
    (literal native termReading).map step (encode native termReading first term) =
      encode native termReading second (native.map step term) := by
  rcases first with ⟨first, parameter⟩
  rcases second with ⟨second, other⟩
  rcases step with ⟨arrival, follows⟩
  change first ⟶ second at arrival
  change base.map arrival parameter = other at follows
  subst other
  apply Subtype.ext
  exact congrArg (fun node => (Sum.inr ⟨(total native).map arrival ⟨parameter, term⟩, node⟩ :
      (nodes native termReading).obj second))
    ((bodyRoots native termReading).property
      (CategoryOfElements.homMk (F := total native) ⟨first, ⟨parameter, term⟩⟩
        ⟨second, (total native).map arrival ⟨parameter, term⟩⟩ arrival rfl))

theorem decode_naturality {first second : base.Elements} (step : first ⟶ second)
    (receipt : (literal native termReading).obj first) :
    decode native termReading second ((literal native termReading).map step receipt) =
      native.map step (decode native termReading first receipt) := by
  have transported := encode_naturality native termReading step (decode native termReading first receipt)
  rw [encode_decode] at transported
  exact congrArg (decode native termReading second) transported

def toNative : NaturalHom (literal native termReading) native where
  app := decode native termReading
  naturality step receipt := (decode_naturality native termReading step receipt).symm

def toLiteral : NaturalHom native (literal native termReading) where
  app := encode native termReading
  naturality := encode_naturality native termReading

def sectionDecoder : (literal native termReading).sections ≃ native.sections where
  toFun := (toNative native termReading).mapSection
  invFun := (toLiteral native termReading).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact encode_decode native termReading point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    rfl

def selectionDecoder : native.sections ≃ ContextualGraphReceiptFamilies.Selection (parent native termReading) :=
  (sectionDecoder native termReading).symm.trans (ContextualGraphReceiptFamilies.wholeSectionEquiv (parent native termReading))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodies
