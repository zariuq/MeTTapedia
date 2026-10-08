import Mettapedia.OSLF.Syntax.SortedCommutativeEquations

/-!
# Complete local readouts of sorted equation classes

Head reconstruction and parallel summation are computed through independently
formed equation classes. Their two readouts prove cancellation and free-head
injectivity. At an undeclared parallel sort the residue carrier is empty, so
its only actual residue acts as the identity without adding equations there.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

open Mettapedia.OSLF.SortedConstructors

universe u v

variable {signature : Signature.{u,v}} {Parallel : signature.Srt → Prop}

theorem inventoryQ_classCut {sort : signature.Srt} (parallel : Parallel sort)
    (first second : Class signature Parallel sort) :
    inventoryQ (classCut parallel first second) = inventoryQ first + inventoryQ second :=
  Quotient.inductionOn₂ first second (fun _ _ => rfl)

theorem Head.inventory_class {sort : signature.Srt}
    (head : Head (signature := signature) (Parallel := Parallel) sort) :
    inventoryQ head.class = {head} := by
  cases head with
  | node constructor arguments =>
    apply congrArg (fun head => ({head} : Multiset _))
    apply congrArg (Head.node constructor)
    funext position
    exact Quotient.out_eq (arguments position)

theorem Head.class_injective {sort : signature.Srt} :
    Function.Injective (Head.class (signature := signature) (Parallel := Parallel) (sort := sort)) := by
  intro first second same
  have inventories := congrArg inventoryQ same
  rw [Head.inventory_class, Head.inventory_class] at inventories
  exact Multiset.singleton_inj.mp inventories

theorem inventoryQ_assemble {sort : signature.Srt} (parallel : Parallel sort)
    (supplied : Multiset (Head (signature := signature) (Parallel := Parallel) sort)) :
    inventoryQ (assemble parallel supplied) = supplied := by
  induction supplied using Multiset.induction_on with
  | empty => rfl
  | cons head tail inductionHypothesis =>
    rw [← Multiset.singleton_add, assemble_add, inventoryQ_classCut]
    have singleton : assemble parallel {head} = head.class := by
      let : Fact (Parallel sort) := ⟨parallel⟩
      simp only [assemble, Multiset.map_singleton, Multiset.sum_singleton]
    rw [singleton, Head.inventory_class, inductionHypothesis]

abbrev ResiduePayload (sort : signature.Srt) :=
  {_head : Head (signature := signature) (Parallel := Parallel) sort // Parallel sort}

def residue {sort : signature.Srt} (supplied : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) sort))
    (value : Class signature Parallel sort) : Class signature Parallel sort := by
  classical
  exact if parallel : Parallel sort then classCut parallel (assemble parallel (supplied.map Subtype.val)) value else value

theorem residue_inventory {sort : signature.Srt}
    (supplied : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) sort))
    (value : Class signature Parallel sort) :
    inventoryQ (residue supplied value) = supplied.map Subtype.val + inventoryQ value := by
  by_cases parallel : Parallel sort
  · rw [residue, dif_pos parallel, inventoryQ_classCut, inventoryQ_assemble]
  · have empty : supplied = 0 := Multiset.eq_zero_of_forall_notMem (fun head _ => parallel head.property)
    rw [residue, dif_neg parallel, empty, Multiset.map_zero, zero_add]

theorem residue_zero {sort : signature.Srt} (value : Class signature Parallel sort) :
    residue 0 value = value := by
  apply inventoryQ_injective
  rw [residue_inventory, Multiset.map_zero, zero_add]

theorem residue_add {sort : signature.Srt}
    (first second : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) sort))
    (value : Class signature Parallel sort) :
    residue (first + second) value = residue first (residue second value) := by
  apply inventoryQ_injective
  rw [residue_inventory, residue_inventory, residue_inventory, Multiset.map_add, add_assoc]

theorem residue_injective {sort : signature.Srt}
    (supplied : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) sort)) :
    Function.Injective (residue supplied) := by
  intro first second same
  apply inventoryQ_injective
  have inventories := congrArg inventoryQ same
  rw [residue_inventory, residue_inventory] at inventories
  exact add_left_cancel inventories

end Mettapedia.OSLF.SortedCommutative
