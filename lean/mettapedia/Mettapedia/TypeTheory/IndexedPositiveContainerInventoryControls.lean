import Mettapedia.TypeTheory.IndexedPositiveContainerInventory
import Mathlib.Data.Fintype.Card

/-!
# Complete two-constructor inventory with data-dependent Vector lengths

The inventory has a Boolean answer constructor and the actual registered
Vector branch code. Every branch length is retained in its position fibre.
Separate controls retain duplicate constructor ordinals and refuse missing
constructors, changed lengths and changed constructor occurrences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.IndexedPositiveContainer.InventoryControls
open IndexedPolynomial IndexedPolynomial.Description
open Inventory

def solved : VectorControl.Checked := .data .payload (.result ())
def codes : List VectorControl.Checked := [solved,VectorControl.code]
def polynomial := Inventory.polynomial codes
noncomputable def presentation := RecursiveSpaceRepresentation.inventoryPresentation VectorControl.orderedFinitary codes
def solvedOrdinal : Fin codes.length := ⟨0,by change 0 < 2; decide⟩
def branchOrdinal : Fin codes.length := ⟨1,by change 1 < 2; decide⟩

def solvedShape (answer : Bool) : polynomial.Shape VectorControl.environment () := ⟨solvedOrdinal,answer,⟨⟨rfl⟩⟩⟩
def branchShape (length : Nat) : polynomial.Shape VectorControl.environment () := ⟨branchOrdinal,VectorControl.shapeAt length⟩

def branchPositions (length : Nat) : polynomial.Position (branchShape length) ≃ Fin length := VectorControl.positionEquiv length

theorem dynamic_position_count (length : Nat) :
    (Code.orderedPositions VectorControl.orderedFinitary (codes.get (branchShape length).1) (branchShape length).2).length = length :=
  RecursiveSpaceRepresentation.vector_ordered_length length

theorem dynamic_padding (length slot : Nat) :
    (presentation.coding (branchShape length)).decode slot = none ↔ length ≤ slot := by
  unfold presentation
  exact (RecursiveSpaceRepresentation.code_padding_iff VectorControl.orderedFinitary VectorControl.code
    (VectorControl.shapeAt length) slot).trans
      (congrArg (fun count => count ≤ slot) (dynamic_position_count length)).to_iff

theorem changed_length_positions_refused {first second : Nat} (different : first ≠ second) :
    ¬ Nonempty (polynomial.Position (branchShape first) ≃ polynomial.Position (branchShape second)) := by
  rintro ⟨comparison⟩
  have lengths := Fintype.card_congr ((branchPositions first).symm.trans (comparison.trans (branchPositions second)))
  exact different (by simpa only [Fintype.card_fin] using lengths)

theorem branch_shape_length {first second : Nat} (same : branchShape first = branchShape second) : first = second := by
  have data := eq_of_heq (Sigma.mk.inj same).2
  exact congrArg Sigma.fst data

theorem changed_occurrence_refused (answer : Bool) (length : Nat) : solvedShape answer ≠ branchShape length := by
  intro same
  have tags := congrArg (fun shape => shape.1.val) same
  change (0 : Nat) = 1 at tags
  cases tags

def solvedNode (answer : Bool) : Family codes VectorControl.environment () :=
  Inventory.construct codes solvedOrdinal ⟨answer,⟨⟨rfl⟩⟩⟩ (fun impossible => PEmpty.elim impossible)

def solvedAt (answer : Bool) (index : Unit) : Family codes VectorControl.environment index :=
  match index with | () => solvedNode answer

def branchNode (length : Nat) : Family codes VectorControl.environment () :=
  Inventory.construct codes branchOrdinal (VectorControl.shapeAt length)
    (fun position => solvedAt true (Code.next VectorControl.code (VectorControl.shapeAt length) position))

def constructorOrdinal (tree : Family codes VectorControl.environment ()) : Nat :=
  (Fix.out polynomial tree).1.1.val

theorem solved_ordinal (answer : Bool) : constructorOrdinal (solvedNode answer) = 0 := rfl
theorem branch_ordinal (length : Nat) : constructorOrdinal (branchNode length) = 1 := rfl

theorem both_constructors_inhabited :
    (∃ tree : Family codes VectorControl.environment (), constructorOrdinal tree = 0) ∧
      (∃ tree : Family codes VectorControl.environment (), constructorOrdinal tree = 1) :=
  ⟨⟨solvedNode true,rfl⟩,⟨branchNode 0,rfl⟩⟩

theorem constructed_occurrences_distinct (answer : Bool) (length : Nat) : solvedNode answer ≠ branchNode length := by
  intro same
  have tags := congrArg constructorOrdinal same
  change (0 : Nat) = 1 at tags
  cases tags

theorem branch_length_reflected {first second : Nat} (same : branchNode first = branchNode second) : first = second :=
  branch_shape_length (congrArg (fun tree => (Fix.out polynomial tree).1) same)

theorem changed_length_values_refused {first second : Nat} (different : first ≠ second) : branchNode first ≠ branchNode second :=
  fun same => different (branch_length_reflected same)

def duplicateCodes : List VectorControl.Checked := [solved,solved]
def duplicateZero : Fin duplicateCodes.length := ⟨0,by change 0 < 2; decide⟩
def duplicateOne : Fin duplicateCodes.length := ⟨1,by change 1 < 2; decide⟩
def duplicateFirst (answer : Bool) : (Inventory.polynomial duplicateCodes).Shape VectorControl.environment () :=
  ⟨duplicateZero,answer,⟨⟨rfl⟩⟩⟩
def duplicateSecond (answer : Bool) : (Inventory.polynomial duplicateCodes).Shape VectorControl.environment () :=
  ⟨duplicateOne,answer,⟨⟨rfl⟩⟩⟩

theorem duplicate_ordinals_retained (answer : Bool) : duplicateFirst answer ≠ duplicateSecond answer := by
  intro same
  have tags := congrArg (fun shape => shape.1.val) same
  change (0 : Nat) = 1 at tags
  cases tags

theorem empty_inventory_refused : ¬ Nonempty (Family ([] : List VectorControl.Checked) VectorControl.environment ()) :=
  fun ⟨tree⟩ => Inventory.empty_family_refused tree

#print axioms dynamic_position_count
#print axioms dynamic_padding
#print axioms changed_length_positions_refused
#print axioms constructed_occurrences_distinct
#print axioms changed_length_values_refused
#print axioms duplicate_ordinals_retained
#print axioms empty_inventory_refused
end Mettapedia.TypeTheory.IndexedPositiveContainer.InventoryControls
