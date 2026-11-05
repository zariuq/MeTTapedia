import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorPayloadComparison
import Mettapedia.TypeTheory.IndexedPositiveContainerInventory
import Mathlib.Data.Fintype.Card

/-!
# Non-Boolean payload and structural refusal controls

The same resolved source inventory is interpreted over three-valued,
functional, higher-universe and empty payload carriers. Empty payloads refuse
the solved constructor but still admit the zero-child branch. Separate
controls reject a changed field sort and a changed scoped length reference.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering.PayloadControls

open Mettapedia.TypeTheory
open IndexedPolynomial IndexedPolynomial.Description
open IndexedPositiveContainer

universe u

def codes (Payload : Type u) := Controls.family.codesWithPayload Payload
def polynomial (Payload : Type u) := Inventory.polynomial (codes Payload)
def environment (Payload : Type u) : Env (VectorPayload.value Payload) [] := PUnit.unit
def index (Payload : Type u) : (VectorPayload.interface Payload).Index := ⟨()⟩
def solvedOrdinal (Payload : Type u) : Fin (codes Payload).length := ⟨0, by change 0 < 2; decide⟩
def branchOrdinal (Payload : Type u) : Fin (codes Payload).length := ⟨1, by change 1 < 2; decide⟩

def solvedShape (Payload : Type u) (item : Payload) :
    (polynomial Payload).Shape (environment Payload) (index Payload) :=
  ⟨solvedOrdinal Payload,item,⟨⟨rfl⟩⟩⟩

theorem solvedShape_injective (Payload : Type u) {first second : Payload}
    (same : solvedShape Payload first = solvedShape Payload second) : first = second := by
  have bodies := eq_of_heq (Sigma.mk.inj same).2
  exact congrArg Sigma.fst bodies

def solvedNode (Payload : Type u) (item : Payload) :
    Inventory.Family (codes Payload) (environment Payload) (index Payload) :=
  Inventory.construct (codes Payload) (solvedOrdinal Payload)
    ⟨item,⟨⟨rfl⟩⟩⟩ (fun impossible => PEmpty.elim impossible)

theorem solvedNode_injective (Payload : Type u) {first second : Payload}
    (same : solvedNode Payload first = solvedNode Payload second) : first = second := by
  apply solvedShape_injective Payload
  exact congrArg (fun tree => (Fix.out (polynomial Payload) tree).1) same

theorem three_payload_values_retained (first second : Fin 3)
    (same : solvedNode (Fin 3) first = solvedNode (Fin 3) second) : first = second :=
  solvedNode_injective (Fin 3) same

theorem boolean_payload_cannot_cover_three_values : ¬ Nonempty (Bool ≃ Fin 3) := by
  rintro ⟨comparison⟩
  have cardinality := Fintype.card_congr comparison
  simp at cardinality

theorem higher_universe_payload_values_retained (first second : Fin 3)
    (same : solvedNode (ULift.{1} (Fin 3)) ⟨first⟩ =
      solvedNode (ULift.{1} (Fin 3)) ⟨second⟩) : first = second :=
  congrArg ULift.down (solvedNode_injective (ULift.{1} (Fin 3)) same)

theorem functional_payloads_distinct :
    solvedNode (Nat → Nat) (fun _ => 0) ≠ solvedNode (Nat → Nat) id := by
  intro same
  have functions := solvedNode_injective (Nat → Nat) same
  have values := congrFun functions 1
  change (0 : Nat) = 1 at values
  cases values

def branchShape (Payload : Type u) (length : Nat) :
    (polynomial Payload).Shape (environment Payload) (index Payload) :=
  ⟨branchOrdinal Payload,⟨length⟩,(),⟨⟨rfl⟩⟩⟩

def branchPositions (Payload : Type u) (length : Nat) :
    (polynomial Payload).Position (branchShape Payload length) ≃ Fin length where
  toFun := fun position => match position with
    | .inl value => value
    | .inr impossible => PEmpty.elim impossible
  invFun := Sum.inl
  left_inv := by
    intro position
    cases position with
    | inl value => rfl
    | inr impossible => exact PEmpty.elim impossible
  right_inv := fun _ => rfl

theorem branch_position_order_length (Payload : Type u) (length : Nat) :
    (IndexedPositiveContainer.Code.orderedPositions (VectorPayload.orderedFinitary Payload)
      ((codes Payload).get (branchOrdinal Payload)) (branchShape Payload length).2).length = length := by
  change (((List.ofFn (id : Fin length → Fin length)).map Sum.inl) ++ []).length = length
  simp

def emptyBranch : Inventory.Family (codes Empty) (environment Empty) (index Empty) :=
  Inventory.construct (codes Empty) (branchOrdinal Empty) (branchShape Empty 0).2
    (fun position => Fin.elim0 (branchPositions Empty 0 position))

theorem empty_payload_still_has_zero_child_branch :
    Nonempty (Inventory.Family (codes Empty) (environment Empty) (index Empty)) := ⟨emptyBranch⟩

theorem empty_payload_solved_refused :
    ¬ Nonempty (IndexedPositiveContainer.Code.Shape (Controls.solved.body.eraseWithPayload Empty)
      (environment Empty) (index Empty)) := by
  rintro ⟨shape⟩
  exact Empty.elim shape.1

def allFields : Code [] [] :=
  .data "outer" .length (by decide)
    (.data "payload" .payload (by decide)
      (.data "inner" .length (by decide)
        (.recursive "direct"
          (.vector "recent" .here (.vector "earlier" (.there (.there .here)) .result)))))

def allFieldsShape (Payload : Type u) (item : Payload) :
    IndexedPositiveContainer.Code.Shape (allFields.eraseWithPayload Payload)
      (environment Payload) (index Payload) :=
  ⟨⟨2⟩,item,⟨3⟩,(),(),⟨⟨rfl⟩⟩⟩

theorem all_four_source_forms_retained (Payload : Type u) :
    nativeFieldOrder (allFields.eraseWithPayload Payload) =
      [.data .length,.data .payload,.data .length,.recursive,.nested "Vector",.nested "Vector"] := rfl

theorem all_fields_binders_retained (Payload : Type u) :
    (ResolvedConstructor.mk "all" allFields |>.withPayload Payload).binders =
      ["outer","payload","inner","direct","recent","earlier"] := rfl

theorem boolean_all_fields_roundtrip (item : Bool) :
    BoolComparison.fromShape allFields (environment Bool) (index Bool)
      (BoolComparison.toShape allFields (environment Bool) (index Bool) (allFieldsShape Bool item)) =
      allFieldsShape Bool item := BoolComparison.from_to allFields ..

theorem changed_field_sort_refused (Payload : Type u) :
    ¬ RealizesSpine Payload (.data .length .result)
      (Controls.solved.body.eraseWithPayload Payload) := by
  intro wrong
  have same := RealizesSpine.unique (Controls.solved.body.eraseWithPayload_spine Payload) wrong
  cases same

def recentLength : Code [.length,.length] ["later","earlier"] :=
  .vector "children" .here .result

theorem changed_length_reference_refused (Payload : Type u) :
    ¬ RealizesSpine Payload (.vector (.there .here) .result)
      (recentLength.eraseWithPayload Payload) := by
  intro wrong
  have same := RealizesSpine.unique (recentLength.eraseWithPayload_spine Payload) wrong
  cases same

#print axioms three_payload_values_retained
#print axioms boolean_payload_cannot_cover_three_values
#print axioms higher_universe_payload_values_retained
#print axioms functional_payloads_distinct
#print axioms branch_position_order_length
#print axioms empty_payload_still_has_zero_child_branch
#print axioms empty_payload_solved_refused
#print axioms boolean_all_fields_roundtrip
#print axioms changed_field_sort_refused
#print axioms changed_length_reference_refused

end Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering.PayloadControls
