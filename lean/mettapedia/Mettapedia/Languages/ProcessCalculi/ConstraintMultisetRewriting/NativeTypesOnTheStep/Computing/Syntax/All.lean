import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Syntax.Qualified
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Syntax.Readings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Syntax.Settler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Syntax.EvalRow

/-!
# The typed-syntax package, qualified, and its interpreter on the converting step

* `Qualified`: the package with typed syntax and its interpreter is qualified at every level and
  valuation: its computation is the instances of thirty-six rows, a constructor system that passes the
  declaration-time check by kernel evaluation; Church–Rosser, unique normal forms, subject reduction
  and decided typed conversion follow.
* `Readings`: the rows executed. `eval tnum (add (lit 2) (lit 3))` runs to `5` by kernel evaluation,
  its unique answer, typed at the call's declared type `val tnum`; `6` is not an answer; the
  conditional `eval tnum (ite (iszero (lit 0)) (lit 2) (lit 3))` runs to `2`.
* `Settler`: the package's own solver step (its conversion, the newest-unknown dispatcher, no
  refutation), its computable settler, and a three-outcome decision of admission.
* `EvalRow`: the interpreter's addition row and literal row, typed after their match, admitted on the
  converting step by kernel evaluation; the literal row is refused by the present step; a row with the
  wrong value type is refused for every settler.
-/
