import Mettapedia.Languages.Chaitin.PureEvaluation

/-!
# Compositional evaluation laws

Pure derivations execute in arbitrary caller continuations and preserve input,
output, and debug state. The laws provide finite executable witnesses without
expanding the evaluator inside each proof.
-/

namespace Mettapedia.Languages.Chaitin.PureEvaluation

open Mettapedia.Computability.StreamingInput

theorem InternalSteps.runs_iff {state next : State}
    (steps : InternalSteps state next) (input : List Bool) (observation : Observation)
    (rest : List Bool) :
    Runs machine state input observation rest ↔ Runs machine next input observation rest := by
  induction steps with
  | refl => rfl
  | @tail following last steps observed ih =>
      exact ih.trans (runs_step_iff observed)

/-- A semantic derivation can be executed in any surrounding continuation,
without expanding that computation inside its caller's proof. -/
theorem PureEval.runs_iff {environment expression value}
    (derivation : PureEval environment expression value) (context : State)
    (input : List Bool) (observation : Observation) (rest : List Bool) :
    Runs machine {context with control := .eval expression environment .unlimited}
      input observation rest ↔
    Runs machine {context with control := .returned value} input observation rest :=
  (derivation.steps context).runs_iff input observation rest

/-- Pure evaluation preserves the entire input and produces no output effects. -/
theorem PureEval.evaluates {environment expression value}
    (derivation : PureEval environment expression value) (input : List Bool) :
    Evaluates expression input ⟨.success value, [], []⟩ input .unlimited environment := by
  apply (derivation.runs_iff (initial expression .unlimited environment) input _ input).mpr
  exact .halt rfl

/-- The same derivation supplies a finite executable witness; the input need
not be inspected or unfolded to construct the witness. -/
theorem PureEval.executable {environment expression value}
    (derivation : PureEval environment expression value) (input : List Bool) :
    ∃ fuel, execute fuel expression input .unlimited environment =
      some (⟨.success value, [], []⟩, input) :=
  evaluates_iff_execute.mp (derivation.evaluates input)

theorem PureEval.deterministic {environment expression first second}
    (left : PureEval environment expression first)
    (right : PureEval environment expression second) : first = second := by
  have equal := (left.evaluates []).deterministic (right.evaluates [])
  have result := congrArg Observation.result equal.1
  exact Result.success.inj result

/-- Every proper list takes the permissive function branch after its head has
been evaluated; a quoted lambda is one special case. -/
theorem lambdaDispatch_list (function : List SExpr) (arguments : List SExpr) :
    LambdaDispatch (.list function) arguments := by
  constructor <;> simp [purePrimitive]

theorem eval_symbol (environment : Environment) (name : String) :
    PureEval environment (.symbol name) (lookup environment (.symbol name)) :=
  .atom _ _ rfl

theorem eval_number (environment : Environment) (value : Nat) :
    PureEval environment (.number value) (.number value) :=
  .atom _ _ rfl

theorem eval_nil (environment : Environment) :
    PureEval environment SExpr.nil (lookup environment SExpr.nil) :=
  .atom _ _ rfl

/-- The quote name itself is subject to the language's dynamic lookup. -/
theorem eval_quote {environment : Environment}
    (quoteName : lookup environment (.symbol "'") = .symbol "'") (value : SExpr) :
    PureEval environment (.list [.symbol "'", value]) value := by
  apply PureEval.quote
  simpa only [quoteName] using eval_symbol environment "'"

/-- Application of a quoted lambda reduces to its dynamically bound body. -/
theorem apply_lambda {environment : Environment} (parameters body : SExpr)
    (arguments : List SExpr) {value : SExpr}
    (computed : PureEval (bind parameters (.list arguments) environment) body value) :
    PureApply environment (.list [.symbol "lambda", parameters, body]) arguments value :=
  .lambda (lambdaDispatch_list _ _) computed

/-- A pure application can be replaced by its returned value inside an
arbitrary caller, including callers that subsequently read or write. -/
theorem PureApply.runs_iff {environment function arguments value}
    (derivation : PureApply environment function arguments value) (context : State)
    (input : List Bool) (observation : Observation) (rest : List Bool) :
    Runs machine {context with control := .apply function arguments environment .unlimited}
      input observation rest ↔
    Runs machine {context with control := .returned value} input observation rest :=
  (derivation.steps context).runs_iff input observation rest

end Mettapedia.Languages.Chaitin.PureEvaluation
