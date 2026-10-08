import Mettapedia.OSLF.Framework.InstrumentTreeDecision

/-!
# Complete shape tests of the actual constructor algebra

The formula is constructed recursively from an independently supplied tree.
Its satisfaction theorem characterizes equality of complete finite-arity
trees. Complete instrument availability admits every such formula. The
Boolean equality readout is derived from the independently defined structural
satisfaction and executable evaluator, rather than defining satisfaction by
the expected comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InstrumentObservations

universe u
variable {Symbols : Type u} {arity : Symbols → Nat}

def shapeFormula : Tree Symbols arity → Formula Symbols arity
  | .node constructor arguments => .headed constructor (fun position => shapeFormula (arguments position))

theorem shapeFormula_spec (hypothesis value : Tree Symbols arity) :
    Satisfies (shapeFormula hypothesis) value ↔ hypothesis = value := by
  induction hypothesis generalizing value with
  | node constructor arguments inductionHypothesis =>
      constructor
      · rintro ⟨compared, rfl, holds⟩
        congr 1
        funext position
        exact (inductionHypothesis position (compared position)).1 (holds position)
      · intro same
        subst value
        exact ⟨arguments, rfl, fun position => (inductionHypothesis position (arguments position)).2 rfl⟩

theorem shapeFormula_admitted (opened : Policy Symbols) (complete : ∀ constructor, opened constructor)
    (hypothesis : Tree Symbols arity) : AdmittedFormula opened (shapeFormula hypothesis) := by
  induction hypothesis with
  | node constructor arguments inductionHypothesis =>
      exact .headed constructor _ (complete constructor) inductionHypothesis

variable [DecidableEq Symbols]

theorem shapeFormula_readout (hypothesis value : Tree Symbols arity) :
    evaluate (shapeFormula hypothesis) value = decide (hypothesis = value) := by
  apply Bool.eq_iff_iff.mpr
  rw [evaluate_iff, decide_eq_true_eq]
  exact shapeFormula_spec hypothesis value

theorem shapeFormula_self (hypothesis : Tree Symbols arity) : evaluate (shapeFormula hypothesis) hypothesis = true := by
  rw [shapeFormula_readout, decide_eq_true rfl]

end Mettapedia.OSLF.Framework.InstrumentObservations
