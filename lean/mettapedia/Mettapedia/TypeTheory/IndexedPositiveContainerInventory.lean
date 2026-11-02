import Mettapedia.TypeTheory.IndexedPositiveContainerRecursiveSpace

/-!
# Complete inventories of indexed registered constructor codes

The polynomial retains each constructor occurrence and its actual indexed
container output. Equal codes at different ordinals remain different shapes.
Its fixed family is generated from the entire inventory.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.IndexedPositiveContainer
open IndexedPolynomial IndexedPolynomial.Description
universe u
variable {I : Interface.{u}} {registry : Registry I} {parameters : Nat} {context : List I.SortCode}

namespace Inventory

def polynomial (codes : List (Code I registry parameters context)) :
    IndexedPolynomial (Env I.Value context) (fun _ => I.Index) where
  Shape := fun environment index => Σ occurrence : Fin codes.length, Code.Shape (codes.get occurrence) environment index
  Position := fun shape => Code.Position (codes.get shape.1) shape.2
  next := fun shape position => Code.next (codes.get shape.1) shape.2 position

abbrev Family (codes : List (Code I registry parameters context)) := Fix (polynomial codes)

def construct (codes : List (Code I registry parameters context)) {environment : Env I.Value context} {index : I.Index}
    (occurrence : Fin codes.length) (shape : Code.Shape (codes.get occurrence) environment index)
    (children : ∀ position, Family codes environment (Code.next (codes.get occurrence) shape position)) :
    Family codes environment index := Fix.roll ⟨occurrence,shape⟩ children

theorem empty_shape_refused (environment : Env I.Value context) (index : I.Index)
    (shape : (polynomial ([] : List (Code I registry parameters context))).Shape environment index) : False :=
  Fin.elim0 shape.1

theorem empty_family_refused {environment : Env I.Value context} {index : I.Index}
    (tree : Family ([] : List (Code I registry parameters context)) environment index) : False :=
  empty_shape_refused environment index (Fix.out (polynomial []) tree).1

end Inventory

namespace RecursiveSpaceRepresentation

noncomputable def inventoryPresentation (ordered : registry.OrderedFinitary)
    (codes : List (Code I registry parameters context)) :
    IndexedPolynomial.RecursiveSpaceRepresentation.Presentation
      (Base := Env I.Value context) (Index := fun _ => I.Index) where
  polynomial := Inventory.polynomial codes
  coding := fun shape => (codePresentation ordered (codes.get shape.1)).coding shape.2
  tag := fun shape => shape.1.val

theorem inventory_position_order (ordered : registry.OrderedFinitary)
    (codes : List (Code I registry parameters context)) {environment : Env I.Value context} {index : I.Index}
    (shape : (Inventory.polynomial codes).Shape environment index)
    (slot : Fin (Code.orderedPositions ordered (codes.get shape.1) shape.2).length) :
    ((inventoryPresentation ordered codes).coding shape).encode
      (Code.orderedPositionEquiv ordered (codes.get shape.1) shape.2 slot) = slot.val :=
  code_position_order ordered (codes.get shape.1) shape.2 slot

theorem inventory_padding_iff (ordered : registry.OrderedFinitary)
    (codes : List (Code I registry parameters context)) {environment : Env I.Value context} {index : I.Index}
    (shape : (Inventory.polynomial codes).Shape environment index) (slot : Nat) :
    ((inventoryPresentation ordered codes).coding shape).decode slot = none ↔
      (Code.orderedPositions ordered (codes.get shape.1) shape.2).length ≤ slot :=
  code_padding_iff ordered (codes.get shape.1) shape.2 slot

end RecursiveSpaceRepresentation

#print axioms Inventory.empty_family_refused
#print axioms RecursiveSpaceRepresentation.inventory_position_order
end Mettapedia.TypeTheory.IndexedPositiveContainer
