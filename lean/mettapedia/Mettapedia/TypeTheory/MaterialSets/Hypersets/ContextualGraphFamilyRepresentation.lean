import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptFamilies
import Mettapedia.TypeTheory.ContextualSmallMapConstructions

/-!
# Contextual graph representation of arbitrary small dependent receipts

For an original-small parameter functor and family, the diagram contains
the parameters and their actual comprehension. A parameter root has one
literal child per native receipt, and transport is the given functor's
actual action. The decoder is bijective and natural; whole compatible
sections correspond to actual membership selections in the same graph
universe. No material term dictionary or representative selection is used.

Receipt leaves need not have different material values. The construction
represents dependent receipts, not an injective encoding into extensional
hypersets.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyRepresentation

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualGraphDiagrams ContextualSmallFamilyUniverse

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (native : base.Elements ⥤ Type u)

def nodes : D ⥤ Type u := ContextualSmallMapConstructions.coproduct base (total native)

inductive Edge (point : D) : (nodes native).obj point → (nodes native).obj point → Prop
  | receipt (parameter : base.obj point) (value : native.obj ⟨point, parameter⟩) :
      Edge point (.inl parameter) (.inr ⟨parameter, value⟩)

def diagram : Diagram D where
  nodes := nodes native
  edge := Edge native
  edge_transport := by
    intro first second arrival parent child proof
    cases proof with
    | receipt parameter value =>
      exact Edge.receipt (base.map arrival parameter)
        (native.map (CategoryOfElements.homMk (F := base)
          ⟨first, parameter⟩ ⟨second, base.map arrival parameter⟩ arrival rfl) value)

def value (point : D) (parameter : base.obj point) : Value D point :=
  ⟨diagram native, .inl parameter⟩

theorem value_move {first second : D} (arrival : first ⟶ second) (parameter : base.obj first) :
    move D arrival (value native first parameter) = value native second (base.map arrival parameter) := rfl

def parent : NaturalHom base (values D) where
  app := value native
  naturality := value_move native

def literal : base.Elements ⥤ Type u := ContextualGraphReceiptFamilies.along (parent native)

def encode (point : base.Elements) (term : native.obj point) : (literal native).obj point :=
  ⟨.inr ⟨point.2, term⟩, Edge.receipt point.2 term⟩

def decode (point : base.Elements) (receipt : (literal native).obj point) : native.obj point := by
  rcases point with ⟨point, parameter⟩
  rcases receipt with ⟨child, edge⟩
  cases child with
  | inl impossible => exact False.elim (by cases edge)
  | inr receipt =>
    rcases receipt with ⟨other, term⟩
    have same : other = parameter := by cases edge; rfl
    subst other
    exact term

theorem decode_encode (point : base.Elements) (term : native.obj point) :
    decode native point (encode native point term) = term := rfl

theorem encode_decode (point : base.Elements) (receipt : (literal native).obj point) :
    encode native point (decode native point receipt) = receipt := by
  rcases point with ⟨point, parameter⟩
  rcases receipt with ⟨child, edge⟩
  cases child with
  | inl impossible => exact False.elim (by cases edge)
  | inr receipt =>
    rcases receipt with ⟨other, term⟩
    have same : other = parameter := by cases edge; rfl
    subst other
    rfl

def decoder (point : base.Elements) : (literal native).obj point ≃ native.obj point where
  toFun := decode native point
  invFun := encode native point
  left_inv := encode_decode native point
  right_inv := decode_encode native point

/-- The literal action here is the graph's own node transport, as used by
the universal member family, not a newly supplied action on the fibres. -/
theorem encode_naturality {first second : base.Elements} (step : first ⟶ second)
    (term : native.obj first) :
    (literal native).map step (encode native first term) = encode native second (native.map step term) := by
  rcases first with ⟨first, parameter⟩
  rcases second with ⟨second, other⟩
  rcases step with ⟨arrival, follows⟩
  change first ⟶ second at arrival
  change base.map arrival parameter = other at follows
  subst other
  rfl

theorem decode_naturality {first second : base.Elements} (step : first ⟶ second)
    (receipt : (literal native).obj first) :
    decode native second ((literal native).map step receipt) = native.map step (decode native first receipt) := by
  have transported := encode_naturality native step (decode native first receipt)
  rw [encode_decode] at transported
  exact (congrArg (decode native second) transported).trans (decode_encode native second _)

def toNative : NaturalHom (literal native) native where
  app := decode native
  naturality step receipt := (decode_naturality native step receipt).symm

def toLiteral : NaturalHom native (literal native) where
  app := encode native
  naturality := encode_naturality native

theorem decoder_inverse : (toNative native).comp (toLiteral native) =
    ContextualSmallMapConstructions.identity (literal native) := by
  apply NaturalHom.ext
  intro point receipt
  exact encode_decode native point receipt

theorem encoder_inverse : (toLiteral native).comp (toNative native) =
    ContextualSmallMapConstructions.identity native := by
  apply NaturalHom.ext
  intro point term
  exact decode_encode native point term

def sectionDecoder : (literal native).sections ≃ native.sections where
  toFun := (toNative native).mapSection
  invFun := (toLiteral native).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact encode_decode native point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact decode_encode native point (term.val point)

def totalToNative : NaturalHom (total (literal native)) (total native) where
  app point receipt := ⟨receipt.1, decode native ⟨point, receipt.1⟩ receipt.2⟩
  naturality {first second} step receipt :=
    (congrArg (fun value => (⟨base.map step receipt.1, value⟩ : (total native).obj second))
      (decode_naturality native
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1⟩
          ⟨second, base.map step receipt.1⟩ step rfl) receipt.2)).symm

def totalToLiteral : NaturalHom (total native) (total (literal native)) where
  app point receipt := ⟨receipt.1, encode native ⟨point, receipt.1⟩ receipt.2⟩
  naturality {first second} step receipt :=
    congrArg (fun value => (⟨base.map step receipt.1, value⟩ : (total (literal native)).obj second))
      (encode_naturality native
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1⟩
          ⟨second, base.map step receipt.1⟩ step rfl) receipt.2)

theorem total_decoder_inverse : (totalToNative native).comp (totalToLiteral native) =
    ContextualSmallMapConstructions.identity (total (literal native)) := by
  apply NaturalHom.ext
  intro point receipt
  exact congrArg (fun term => (⟨receipt.1, term⟩ : (total (literal native)).obj point))
    (encode_decode native ⟨point, receipt.1⟩ receipt.2)

theorem total_encoder_inverse : (totalToLiteral native).comp (totalToNative native) =
    ContextualSmallMapConstructions.identity (total native) := by
  apply NaturalHom.ext
  intro point receipt
  exact congrArg (fun term => (⟨receipt.1, term⟩ : (total native).obj point))
    (decode_encode native ⟨point, receipt.1⟩ receipt.2)

theorem total_decoder_projection : (totalToNative native).comp (projection native) =
    projection (literal native) := by
  apply NaturalHom.ext
  intro _ _
  rfl

def consumer {other : base.Elements ⥤ Type u} (operation : NaturalHom native other) :
    NaturalHom (literal native) (literal other) :=
  ((toNative native).comp operation).comp (toLiteral other)

theorem consumer_decode {other : base.Elements ⥤ Type u} (operation : NaturalHom native other)
    (point : base.Elements) (receipt : (literal native).obj point) :
    decode other point ((consumer native operation).app point receipt) =
      operation.app point (decode native point receipt) := decode_encode other point _

theorem consumer_identity : consumer native (ContextualSmallMapConstructions.identity native) =
    ContextualSmallMapConstructions.identity (literal native) := decoder_inverse native

theorem consumer_composition {middle last : base.Elements ⥤ Type u}
    (first : NaturalHom native middle) (later : NaturalHom middle last) :
    consumer native (first.comp later) = (consumer native first).comp (consumer middle later) := by
  apply NaturalHom.ext
  intro point receipt
  rfl

def homDecoder (other : base.Elements ⥤ Type u) :
    NaturalHom (literal native) (literal other) ≃ NaturalHom native other where
  toFun operation := ((toLiteral native).comp operation).comp (toNative other)
  invFun := consumer native
  left_inv operation := by
    apply NaturalHom.ext
    intro point receipt
    exact (congrArg (fun input => encode other point (decode other point (operation.app point input)))
      (encode_decode native point receipt)).trans (encode_decode other point (operation.app point receipt))
  right_inv operation := by
    apply NaturalHom.ext
    intro point term
    rfl

/-- Complete native sections, including every context action, correspond
to compatible literal selections through actual material comprehension. -/
def selectionDecoder : native.sections ≃ ContextualGraphReceiptFamilies.Selection (parent native) :=
  (sectionDecoder native).symm.trans (ContextualGraphReceiptFamilies.wholeSectionEquiv (parent native))

def selectedValue (term : native.sections) : NaturalHom base (values D) :=
  ContextualGraphReceiptFamilies.sectionReading (parent native) ((sectionDecoder native).symm term)

def selectedMembership (term : native.sections) (point : D) (parameter : base.obj point) :
    ContextualRealizedGraphs.Member ((selectedValue native term).app point parameter)
      (value native point parameter) :=
  ContextualGraphReceiptFamilies.sectionMembership (parent native) ((sectionDecoder native).symm term) point parameter

def classifier : NaturalHom base universeFamily := ContextualSmallFamilyUniverse.classifier native

theorem decoded_classifier : decodedFamily (classifier native) = native := decoded_classifier_eq native

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyRepresentation
