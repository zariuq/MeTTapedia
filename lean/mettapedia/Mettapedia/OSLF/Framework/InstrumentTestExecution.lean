import Mettapedia.OSLF.Framework.InstrumentTestDecision
import Mathlib.Algebra.BigOperators.Fin

/-!
# Structural inspection with an explicit traversal account

The inspection computes its Boolean answer and the number of visited test
nodes together. Both branches of a conjunction and every requested child
of a matching constructor contribute to this complete traversal. A failed
constructor comparison visits only the current test node.

The two readouts are compared with the independently defined evaluator
and traversal account. This account specifies this inspection procedure;
it does not measure host instructions or prescribe costs for other test
implementations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InstrumentObservations

open scoped BigOperators

universe u

variable {Symbols : Type u} {arity : Symbols → Nat} [DecidableEq Symbols]

def inspect : Formula Symbols arity → Tree Symbols arity → Bool × Nat
  | .top, _ => (true, 1)
  | .neg body, tree =>
      let result := inspect body tree
      (!result.1, 1 + result.2)
  | .conj first second, tree =>
      let left := inspect first tree
      let right := inspect second tree
      (left.1 && right.1, 1 + left.2 + right.2)
  | .headed constructor formulas, .node second arguments =>
      if same : second = constructor then
        let children := List.ofFn (fun position : Fin (arity constructor) =>
          inspect (formulas position)
            (arguments (cast (congrArg (fun symbol => Fin (arity symbol)) same.symm) position)))
        (children.all Prod.fst, 1 + (children.map Prod.snd).sum)
      else (false, 1)

private theorem all_ofFn_readout {count : Nat} (values : Fin count → Bool × Nat) :
    (List.ofFn values).all Prod.fst = decide (∀ position, (values position).1 = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.forall_mem_ofFn_iff, decide_eq_true_eq]

theorem inspect_readout (formula : Formula Symbols arity) (tree : Tree Symbols arity) :
    inspect formula tree = (evaluate formula tree, traversalWork formula tree) := by
  induction formula generalizing tree with
  | top => rfl
  | neg body inductionHypothesis =>
      simp only [inspect, evaluate, traversalWork, inductionHypothesis tree]
  | conj first second firstIH secondIH =>
      simp only [inspect, evaluate, traversalWork, firstIH tree, secondIH tree]
  | headed constructor formulas inductionHypothesis =>
      cases tree with
      | node second arguments =>
          by_cases same : second = constructor
          · subst second
            unfold inspect evaluate traversalWork
            simp only [dif_pos, cast_eq]
            have compared :
                List.ofFn (fun position => inspect (formulas position) (arguments position)) =
                  List.ofFn (fun position =>
                    (evaluate (formulas position) (arguments position),
                      traversalWork (formulas position) (arguments position))) :=
              congrArg List.ofFn (funext (fun position =>
                inductionHypothesis position (arguments position)))
            rw [compared, all_ofFn_readout]
            simp only [List.map_ofFn, Fin.sum_ofFn, Function.comp_apply]
          · simp only [inspect, evaluate, traversalWork, dif_neg same]

theorem inspect_answer_iff (formula : Formula Symbols arity) (tree : Tree Symbols arity) :
    (inspect formula tree).1 = true ↔ Satisfies formula tree := by
  rw [inspect_readout]
  exact evaluate_iff formula tree

theorem inspect_refutation_iff (formula : Formula Symbols arity) (tree : Tree Symbols arity) :
    (inspect formula tree).1 = false ↔ ¬ Satisfies formula tree := by
  rw [inspect_readout]
  exact evaluate_false_iff formula tree

theorem inspect_work (formula : Formula Symbols arity) (tree : Tree Symbols arity) :
    (inspect formula tree).2 = traversalWork formula tree := by
  rw [inspect_readout]

theorem inspection_at_fixed_depth_can_exceed (ceiling : Nat) (tree : Tree Symbols arity) :
    ∃ formula : Formula Symbols arity,
      structuralDepth formula = 0 ∧ (inspect formula tree).1 = true ∧
        ceiling < (inspect formula tree).2 := by
  obtain ⟨formula, depth, holds, work⟩ := fixed_depth_has_unbounded_work ceiling tree
  refine ⟨formula, depth, ?_, ?_⟩
  · simpa only [inspect_readout] using holds
  · simpa only [inspect_readout] using work

end Mettapedia.OSLF.Framework.InstrumentObservations
