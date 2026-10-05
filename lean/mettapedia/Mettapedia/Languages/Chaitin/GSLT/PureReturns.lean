import Mettapedia.Languages.Chaitin.GSLT.Correspondence

/-!
# Exact returned values of a total pure expression

A finite natural derivation supplies an actual generated execution. Any
other generated execution returning a value has that same value, by the
historical evaluator's deterministic observations. This is useful for
compiling terminating data procedures without unfolding their executions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.GSLT

open PureEvaluation

theorem pureEval_returns_iff {environment : Environment} {expression expected : SExpr}
    (derivation : PureEval environment expression expected) (value : SExpr) :
    theory.MultiStep (start expression environment) (result value) ↔ value = expected := by
  constructor
  · intro path
    have same := (generated_observed path []).deterministic (derivation.evaluates [])
    exact Result.success.inj (congrArg Observation.result same.1)
  · intro same
    subst value
    exact pureEval_generated derivation

end Mettapedia.Languages.Chaitin.GSLT
