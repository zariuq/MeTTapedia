import Mettapedia.Languages.Chaitin.Evaluator
import Mettapedia.Languages.Chaitin.Expressions

/-!
# Historical Lisp observations

These controls exercise the permissive values, evaluation order, dynamic
bindings, clean re-evaluation, and nested private-tape exceptions described
in Chaitin's `examples.l`. They also distinguish a language timeout from an
executor that has not yet returned.
-/

namespace Mettapedia.Languages.Chaitin.RuntimeControls

open Expressions

private def sandbox (limit body input : SExpr) : SExpr :=
  call "try" [limit, quote body, quote input]
private def success (value : SExpr) (output debug : List SExpr := []) : Observation :=
  ⟨.success value, output, debug⟩
private def reported (tag : String) (value : SExpr) (output : List SExpr := []) : SExpr :=
  .list [.symbol tag, value, .list output]

theorem atomic_car : execute 20 (call "car" [quote (.symbol "abc")]) [] =
    some (success (.symbol "abc"), []) := by rfl

theorem atomic_cons : execute 30 (call "cons" [.number 1, .number 2]) [] =
    some (success (.number 1), []) := by rfl

theorem nil_is_true : execute 20 (call "if" [.symbol "nil", .number 1, .number 2]) [] =
    some (success (.number 1), []) := by rfl

theorem only_false_selects_else :
    execute 20 (call "if" [.symbol "false", .number 1, .number 2]) [] =
      some (success (.number 2), []) := by rfl

/-- The unselected branch is not run, even if it would consume unavailable input. -/
theorem conditional_does_not_read :
    execute 20 (call "if" [.symbol "true", .number 7, call "read-bit" []]) [] =
      some (success (.number 7), []) := by rfl

theorem computed_function :
    execute 40 (.list [call "if" [.symbol "true", quote (.symbol "car"), quote (.symbol "cdr")],
      quote (.list [.number 3, .number 4])]) [] = some (success (.number 3), []) := by rfl

/-- Extra arguments are evaluated, though `car` uses only its first value. -/
theorem extra_argument_is_evaluated :
    execute 40 (call "car" [quote (.list [.number 3]), call "display" [.number 4]]) [] =
      some (success (.number 3) [.number 4], []) := by rfl

theorem eager_arguments_in_order :
    execute 60 (call "+" [call "display" [.number 5], call "display" [.number 15]]) [] =
      some (success (.number 20) [.number 5, .number 15], []) := by rfl

theorem numbers_ignore_bindings :
    execute 5 (.number 7) [] .unlimited [(.number 7, .number 8)] =
      some (success (.number 7), []) := by rfl

theorem dynamic_free_name :
    execute 40 (.list [quotedLambda ["y"] (call "cons" [.symbol "x", .symbol "y"]), .symbol "nil"])
      [] .unlimited [(.symbol "x", .number 9), (.symbol "nil", SExpr.nil)] =
        some (success (.list [.number 9]), []) := by rfl

theorem eval_uses_clean_environment :
    execute 20 (call "eval" [quote (.symbol "x")]) [] .unlimited
      [(.symbol "x", .number 9)] = some (success (.symbol "x"), []) := by rfl

/-- A pure primitive succeeds at depth zero. -/
theorem primitive_at_zero_depth :
    execute 30 (call "+" [.number 5, .number 15]) [] (.bounded 0) =
      some (success (.number 20), []) := by rfl

/-- A re-evaluation consumes one nesting level. -/
theorem eval_at_zero_depth :
    execute 30 (call "eval" [quote (.number 7)]) [] (.bounded 0) =
      some (⟨.failure .outOfTime, [], []⟩, []) := by rfl

theorem private_empty_tape_is_caught :
    execute 40 (sandbox (.number 0) (call "read-bit" []) SExpr.nil) [] =
      some (success (reported "failure" (.symbol "out-of-data")), []) := by rfl

theorem private_nonzero_bit :
    execute 40 (sandbox (.number 0) (call "read-bit" []) (.list [.symbol "anything"])) [] =
      some (success (reported "success" (.number 1)), []) := by rfl

theorem debug_is_not_official_output :
    execute 80 (sandbox (.number 0)
      (call "+" [call "display" [.number 5], call "debug" [.number 15]]) SExpr.nil) [] =
        some (success (reported "success" (.number 20) [.number 5]) [] [.number 15], []) := by rfl

/-- A timeout at the same limit as the enclosing computation propagates. -/
theorem equal_nested_limit_propagates :
    execute 80 (sandbox (.number 0) (call "eval" [quote (.number 7)]) SExpr.nil) [] (.bounded 1) =
      some (⟨.failure .outOfTime, [], []⟩, []) := by rfl

/-- A strictly smaller private limit is caught by its own `try`. -/
theorem smaller_nested_limit_is_caught :
    execute 80 (sandbox (.number 0) (call "eval" [quote (.number 7)]) SExpr.nil) [] (.bounded 2) =
      some (success (reported "failure" (.symbol "out-of-time")), []) := by rfl

/-- Returning from a private tape resumes reading the original outer input. -/
theorem private_tape_restores_outer_input :
    execute 100 (call "cons" [sandbox (.number 0) (call "read-bit" []) (.list [.number 0]),
      call "cons" [call "read-bit" [], .symbol "nil"]]) [true] =
        some (success (.list [reported "success" (.number 0), .number 1]), []) := by rfl

/-- An outer input request has no successful return on empty input. -/
theorem outer_empty_read : ¬ ∃ observation rest,
    Mettapedia.Computability.StreamingInput.Runs machine
      { control := .readBit } [] observation rest := by
  rintro ⟨observation, rest, run⟩
  exact Mettapedia.Computability.StreamingInput.not_runs_read_empty rfl run

/-- A small executor budget does not produce the language's timeout value. -/
theorem insufficient_executor_fuel : execute 1 (.number 7) [] = none := rfl

end Mettapedia.Languages.Chaitin.RuntimeControls
