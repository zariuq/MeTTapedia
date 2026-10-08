import Mettapedia.OSLF.Framework.StructuralFundedAssays

/-!
# Funded structural verdicts and retained payload distinctions

The positive predicate inspects a binary constructor and both of its nullary
children. The negative case has a different second child. Complete received
trees and origins are retained, and an underfunded successful predicate is
distinguished from an actual refutation. A family of depth-zero tests
exercises the traversal-price boundary independently of verdict truth.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InstrumentObservations.AssayControls

open Mettapedia.GSLT.Causality ResourceInteraction ComplementaryAssay

def arity (constructor : Bool) : Nat := if constructor then 2 else 0

def atom : Tree Bool arity := .node false (fun position => Fin.elim0 position)
def paired : Tree Bool arity := .node true (fun _ => atom)
def differentChild : Tree Bool arity :=
  .node true (fun position => if position.val = 0 then atom else paired)

def atomFormula : Formula Bool arity := .headed false (fun _ => .top)
def pairedFormula : Formula Bool arity := .headed true (fun _ => atomFormula)

theorem tests_complete_finite_arguments :
    evaluate pairedFormula paired = true ∧ evaluate pairedFormula differentChild = false := by decide

theorem exact_traversal_prices :
    traversalWork pairedFormula paired = 3 ∧ traversalWork pairedFormula differentChild = 3 := by decide

theorem positive_complete_readout :
    observed (evaluate pairedFormula) (traversalWork pairedFormula) 20 7 (some paired) 3 =
      { (20, .confirm, 7, paired) } := by decide

theorem negative_complete_readout :
    observed (evaluate pairedFormula) (traversalWork pairedFormula) 20 7 (some differentChild) 3 =
      { (20, .refute, 7, differentChild) } := by decide

theorem original_structural_certificates :
    Satisfies pairedFormula paired ∧ ¬ Satisfies pairedFormula differentChild := by
  exact ⟨(evaluate_iff _ _).1 tests_complete_finite_arguments.1,
    (evaluate_false_iff _ _).1 tests_complete_finite_arguments.2⟩

theorem successful_predicate_without_funding_is_quiet :
    evaluate pairedFormula paired = true ∧
      observed (evaluate pairedFormula) (traversalWork pairedFormula) 20 7 (some paired) 2 = 0 := by decide

theorem received_trees_remain_distinct : paired ≠ differentChild := by decide

theorem origins_remain_distinct :
    observed (evaluate pairedFormula) (traversalWork pairedFormula) 20 7 (some paired) 3 ≠
      observed (evaluate pairedFormula) (traversalWork pairedFormula) 20 8 (some paired) 3 := by decide

theorem fixed_depth_can_exceed_any_purse (budget : Nat) :
    ∃ formula : Formula Bool arity,
      structuralDepth formula = 0 ∧ evaluate formula paired = true ∧
        observed (evaluate formula) (traversalWork formula) 20 7 (some paired) budget = 0 := by
  obtain ⟨formula, depth, holds, expensive⟩ := fixed_depth_has_unbounded_work budget paired
  refine ⟨formula, depth, holds, ?_⟩
  rw [observed_some, if_neg (Nat.not_le_of_lt expensive)]

theorem actual_traversal_fee_conserved :
    5 = (rightPart (completed (evaluate pairedFormula) (traversalWork pairedFormula)
      20 (7 : Nat) paired 5)).card + 3 :=
  structural_test_purse_conservation pairedFormula 20 7 paired 5 (by decide)

end Mettapedia.OSLF.Framework.InstrumentObservations.AssayControls
