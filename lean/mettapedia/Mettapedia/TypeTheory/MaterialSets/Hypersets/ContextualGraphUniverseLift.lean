import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptFamilies
import Mettapedia.TypeTheory.ContextualFutureSiteLift

/-!
# Explicit successor universe transport of contextual graphs

Worlds, arrows and nodes are raised once. The actual graph edges and
literal children are retained. Full-future matching is preserved and
reflected by constructed coiterations, so raising the bound neither
identifies nor separates material behaviors. This is a comparison of the
lower image, not a claim that arbitrary upper graphs are lower images.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphUniverseLift

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualGraphDiagrams ContextualRealizedGraphs
universe u
variable {D : Type u} [Category.{u} D]

abbrev Raised := ContextualFutureSiteLift.Raised (D := D)

def diagram (original : Diagram D) : Diagram (Raised (D := D)) where
  nodes := {
    obj point := ULift.{u+1,u} (original.nodes.obj point.down)
    map arrival := TypeCat.ofHom fun node => ULift.up (original.nodes.map arrival.down node.down)
    map_id point := by
      apply ConcreteCategory.hom_ext
      intro node
      exact ULift.ext _ _ (original.nodes.map_id_apply point.down node.down)
    map_comp earlier later := by
      apply ConcreteCategory.hom_ext
      intro node
      exact ULift.ext _ _ (original.nodes.map_comp_apply earlier.down later.down node.down) }
  edge point first second := original.edge point.down first.down second.down
  edge_transport := fun {_ _} arrival {_ _} available => original.edge_transport arrival.down available

def value {point : Raised (D := D)} (original : Value D point.down) : Value (Raised (D := D)) point :=
  ⟨diagram original.1, ULift.up original.2⟩

theorem value_move {first second : Raised (D := D)} (arrival : first ⟶ second)
    (original : Value D first.down) :
    move _ arrival (value original) = value (move D arrival.down original) := rfl

def reading : NaturalHom (ContextualFutureSiteLift.base (values D)) (values (Raised (D := D))) where
  app _ := value
  naturality := value_move

def childDecoder {point : Raised (D := D)} (original : Value D point.down) :
    Child (Raised (D := D)) (value original) ≃ Child D original where
  toFun child := ⟨child.val.down, child.property⟩
  invFun child := ⟨ULift.up child.val, child.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem child_reading {point : Raised (D := D)} (original : Value D point.down)
    (child : Child (Raised (D := D)) (value original)) :
    childValue (Raised (D := D)) (value original) child = value (childValue D original (childDecoder original child)) := rfl

def preserve {point : Raised (D := D)} {first second : Value D point.down}
    (proof : Equal first second) : Equal (value first) (value second) :=
  ContextualGraphRealizers.corec (diagram first.1) (diagram second.1)
    (witness := fun point left right => ContextualGraphRealizers.Realizer first.1 second.1 point.down left.down right.down)
    (fun _ _ _ proof future child =>
      let response := ContextualGraphRealizers.Realizer.forth proof ⟨future.1.down, future.2.down⟩
        ⟨child.val.down, child.property⟩
      ⟨⟨ULift.up response.1.val, response.1.property⟩, response.2⟩)
    (fun _ _ _ proof future child =>
      let response := ContextualGraphRealizers.Realizer.back proof ⟨future.1.down, future.2.down⟩
        ⟨child.val.down, child.property⟩
      ⟨⟨ULift.up response.1.val, response.1.property⟩, response.2⟩)
    proof

def reflect {point : Raised (D := D)} {first second : Value D point.down}
    (proof : Equal (value first) (value second)) : Equal first second :=
  ContextualGraphRealizers.corec first.1 second.1
    (witness := fun point left right => ContextualGraphRealizers.Realizer (diagram first.1) (diagram second.1)
      (PresheafSiteLift.Site.upFunctor.obj point) (ULift.up left) (ULift.up right))
    (fun _ _ _ proof future child =>
      let response := ContextualGraphRealizers.Realizer.forth proof
        ⟨PresheafSiteLift.Site.upFunctor.obj future.1, PresheafSiteLift.Site.upFunctor.map future.2⟩
        ⟨ULift.up child.val, child.property⟩
      ⟨⟨response.1.val.down, response.1.property⟩, response.2⟩)
    (fun _ _ _ proof future child =>
      let response := ContextualGraphRealizers.Realizer.back proof
        ⟨PresheafSiteLift.Site.upFunctor.obj future.1, PresheafSiteLift.Site.upFunctor.map future.2⟩
        ⟨ULift.up child.val, child.property⟩
      ⟨⟨response.1.val.down, response.1.property⟩, response.2⟩)
    proof

theorem matching_iff {point : Raised (D := D)} (first second : Value D point.down) :
    Nonempty (Equal (value first) (value second)) ↔ Nonempty (Equal first second) :=
  ⟨fun ⟨proof⟩ => ⟨reflect proof⟩, fun ⟨proof⟩ => ⟨preserve proof⟩⟩

def memberPreserve {point : Raised (D := D)} {child parent : Value D point.down}
    (proof : Member child parent) : Member (value child) (value parent) :=
  ⟨(childDecoder parent).symm proof.1, preserve proof.2⟩

def memberReflect {point : Raised (D := D)} {child parent : Value D point.down}
    (proof : Member (value child) (value parent)) : Member child parent :=
  ⟨childDecoder parent proof.1, reflect proof.2⟩

theorem membership_iff {point : Raised (D := D)} (child parent : Value D point.down) :
    Nonempty (Member (value child) (value parent)) ↔ Nonempty (Member child parent) :=
  ⟨fun ⟨proof⟩ => ⟨memberReflect proof⟩, fun ⟨proof⟩ => ⟨memberPreserve proof⟩⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphUniverseLift
