import Mettapedia.Logic.UniversalPrediction.EnumerationBridge
import Mettapedia.Logic.UniversalPrediction.BetaPredictor

/-!
# Machine Enumeration Interface

This file provides a *concrete* enumeration interface that turns the abstract
`PrefixMeasureEnumeration` bridge into a ready-to-use tool:

* given a code type `Code` and an evaluator `eval : Code → PrefixMeasure`,
* define "computable" as "enumerated by some code",
* then all dominance → regret bounds immediately apply.

This keeps the heavy machine-model theorems out of the critical path while
making the dependency explicit and local.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction
namespace MachineEnumeration

open EnumerationBridge
open FiniteHorizon

/-- Build a `PrefixMeasureEnumeration` from any code/eval pair by taking
"computable" to mean "has some code". -/
def ofEval (Code : Type*) [Encodable Code] (eval : Code → PrefixMeasure) :
    PrefixMeasureEnumeration :=
  { Code := Code
    eval := eval
    IsComputable := fun μ => ∃ c : Code, eval c = μ
    surj_eval := by
      intro μ hμ
      exact hμ }

/-- Any enumerated code is immediately "computable" for `ofEval`. -/
lemma isComputable_of_code {Code : Type*} [Encodable Code] (eval : Code → PrefixMeasure)
    (c : Code) : (ofEval Code eval).IsComputable (eval c) :=
  ⟨c, rfl⟩

/-- Regret bound for a *specific code* under the `ofEval` enumeration. -/
theorem relEntropy_le_log_inv_of_code {Code : Type*} [Encodable Code]
    (eval : Code → PrefixMeasure) (c : Code) (n : ℕ) :
    ∃ c' : ENNReal, c' ≠ 0 ∧
      Dominates (PrefixMeasureEnumeration.xi (ofEval Code eval)) (eval c) c' ∧
      relEntropy (eval c) (PrefixMeasureEnumeration.xi (ofEval Code eval)) n ≤
        Real.log (1 / c'.toReal) := by
  simpa using
    (PrefixMeasureEnumeration.relEntropy_le_log_inv_of_IsComputable
      (E := ofEval Code eval) (μ := eval c) (hμ := ⟨c, rfl⟩) (n := n))

/-- Minimal codes for the three standard Beta-family competitors in this repo.

This is useful for demos/tests: it allows applying the regret bound with **no extra hypotheses**
by instantiating `PrefixMeasureEnumeration` as `ofEval BetaCode betaEval`. -/
inductive BetaCode where
  | laplace
  | jeffreys
  | haldane
deriving DecidableEq, Repr, Inhabited, Encodable

namespace BetaCode

/-- Evaluate a `BetaCode` to the corresponding `PrefixMeasure`. -/
def betaEval : BetaCode → PrefixMeasure
  | .laplace => laplacePrefixMeasure
  | .jeffreys => jeffreysPrefixMeasure
  | .haldane => haldanePrefixMeasure

/-- The tiny enumeration containing exactly the three Beta-family competitors. -/
abbrev betaEnum : PrefixMeasureEnumeration :=
  ofEval BetaCode betaEval

theorem relEntropy_le_log_inv_laplace (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Dominates (PrefixMeasureEnumeration.xi betaEnum) laplacePrefixMeasure c ∧
      relEntropy laplacePrefixMeasure (PrefixMeasureEnumeration.xi betaEnum) n ≤
        Real.log (1 / c.toReal) := by
  simpa [betaEnum, betaEval] using
    (relEntropy_le_log_inv_of_code (eval := betaEval) (c := BetaCode.laplace) (n := n))

theorem relEntropy_le_log_inv_jeffreys (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Dominates (PrefixMeasureEnumeration.xi betaEnum) jeffreysPrefixMeasure c ∧
      relEntropy jeffreysPrefixMeasure (PrefixMeasureEnumeration.xi betaEnum) n ≤
        Real.log (1 / c.toReal) := by
  simpa [betaEnum, betaEval] using
    (relEntropy_le_log_inv_of_code (eval := betaEval) (c := BetaCode.jeffreys) (n := n))

theorem relEntropy_le_log_inv_haldane (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Dominates (PrefixMeasureEnumeration.xi betaEnum) haldanePrefixMeasure c ∧
      relEntropy haldanePrefixMeasure (PrefixMeasureEnumeration.xi betaEnum) n ≤
        Real.log (1 / c.toReal) := by
  simpa [betaEnum, betaEval] using
    (relEntropy_le_log_inv_of_code (eval := betaEval) (c := BetaCode.haldane) (n := n))

end BetaCode

end MachineEnumeration
end Mettapedia.Logic.UniversalPrediction
