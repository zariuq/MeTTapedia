import Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofInterpretation

/-!
# Extensional truth fibres and strict native proof decoding

The actual truth fibre of a true sentence is a singleton containing the empty
set. The actual graph product of two such fibres is a different singleton:
its inhabitant is a nonempty function graph. Consequently these particular
codes cannot directly validate the native implication-proof decoder as strict
set equality. Their carriers are nevertheless explicitly equivalent.

This is a boundary of this strict set-code interpretation, not a contradiction
in either source logic and not an obstruction to a separately coherent weak
interpretation or a different choice of semantic proof objects.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofDecoderBoundary

open ZFSetDependentProducts ZFSetHOLProofInterpretation ZFSetHOLTermInterpretation
open ZFSetUniverseClosure ZFSetUniverseInterpretation ZFSetHOLTypeInterpretation

universe u

def unitCode : ZFSet.{u} := {∅}

def unitValue : Elements unitCode.{u} := ⟨∅, ZFSet.mem_singleton.mpr rfl⟩

theorem unit_value_unique (value : Elements unitCode.{u}) : value = unitValue := by
  apply Subtype.ext
  exact ZFSet.mem_singleton.mp value.2

theorem empty_not_function_graph :
    (∅ : ZFSet.{u}) ∉ piSet unitCode (fun _ => unitCode) := by
  intro membership
  obtain ⟨value, member, _⟩ := (mem_piSet.mp membership).1.2
    ∅ (ZFSet.mem_singleton.mpr rfl)
  exact ZFSet.notMem_empty _ member

theorem unit_ne_function_code :
    unitCode.{u} ≠ piSet unitCode (fun _ => unitCode) := by
  intro equal
  have member : (∅ : ZFSet.{u}) ∈ unitCode := ZFSet.mem_singleton.mpr rfl
  rw [equal] at member
  exact empty_not_function_graph member

theorem true_fibre (h : CofinalInaccessibles.{u}) :
    truthFibre h (.top : ClosedFormula UniverseSymbol) emptyValuation = unitCode := by
  apply ZFSet.ext
  intro value
  simp only [mem_truthFibre, interpret, holds_truth, unitCode, ZFSet.mem_singleton,
    and_true]

theorem true_implication_fibre (h : CofinalInaccessibles.{u}) :
    truthFibre h (.imp .top .top : ClosedFormula UniverseSymbol) emptyValuation = unitCode := by
  apply ZFSet.ext
  intro value
  simp only [mem_truthFibre, interpret, holds_truth, unitCode, ZFSet.mem_singleton,
    implies_true, and_true]

/-- The displayed native decoder equation is not equality of these actual
set codes, already at the closed instance `True implies True`. -/
theorem strict_implication_decoder_fails (h : CofinalInaccessibles.{u}) :
    truthFibre h (.imp .top .top : ClosedFormula UniverseSymbol) emptyValuation ≠
      piSet (truthFibre h (.top : ClosedFormula UniverseSymbol) emptyValuation)
        (fun _ => truthFibre h (.top : ClosedFormula UniverseSymbol) emptyValuation) := by
  rw [true_fibre, true_implication_fibre]
  exact unit_ne_function_code

/-! ## The distinction is strict equality, not lack of an equivalence -/

noncomputable def unitGraph : Elements (piSet unitCode.{u} (fun _ => unitCode)) :=
  encodeFunction (fun _ => unitValue)

theorem unit_graph_nonempty : unitGraph.{u}.1 ≠ ∅ := by
  intro equal
  have member := unitGraph.{u}.2
  rw [equal] at member
  exact empty_not_function_graph member

theorem unit_graph_unique (function : Elements (piSet unitCode.{u} (fun _ => unitCode))) :
    function = unitGraph := by
  apply (piEquiv unitCode (fun _ => unitCode)).injective
  funext argument
  change graphValue function argument = graphValue unitGraph argument
  exact (unit_value_unique _).trans (unit_value_unique _).symm

noncomputable def unitFunctionEquiv :
    Elements unitCode.{u} ≃ Elements (piSet unitCode.{u} (fun _ => unitCode.{u})) where
  toFun := fun _ => unitGraph
  invFun := fun _ => unitValue
  left_inv := fun value => (unit_value_unique value).symm
  right_inv := fun function => (unit_graph_unique function).symm

#print axioms empty_not_function_graph
#print axioms unit_ne_function_code
#print axioms strict_implication_decoder_fails
#print axioms unit_graph_nonempty
#print axioms unitFunctionEquiv

end Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofDecoderBoundary
