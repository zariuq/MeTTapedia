import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Qualified
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.QualifiedControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.AppendReadings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Settler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.SettlerControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.RowsAfterMatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.ValueTypeRow
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.NotUnitary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.FamilyLimits

/-!
# The vectors package, qualified, and dependent programs on the repaired step

* `Qualified`: the package with vectors, their dependent eliminator, declared addition, the order on
  the numbers and the identity eliminator is qualified at every level and valuation: its computation
  is the instances of fourteen rows, a constructor system that passes the declaration-time check;
  Church–Rosser, unique normal forms, subject reduction and decided typed conversion follow.
* `QualifiedControls`: one overlapping row with `add` breaks it; the audit's rigid package is qualified
  only vacuously, and with its rows declared computing it has no setting with its own roles.
* `AppendReadings`: the rows executed; the two readings of `append` agree; `append num 1 1 [2] [3]`
  runs to `[2, 3]` by kernel evaluation, its unique answer, typed at the call's declared type.
* `Settler`: the package's own solver step (its conversion, the newest-unknown dispatcher, no
  refutation), exact and rank-lowering; its computable settler; a three-outcome decision of admission.
* `SettlerControls`: the tower's rigid-clash check fires on `vec A zero ≐ unit`, which this package's
  conversion makes true; the package's family settles it.
* `RowsAfterMatch`: the nil and cons rows of `append` and the cons row of `head`, typed after their
  match, admitted by kernel evaluation; mistyped rows refused for every settler.
* `ValueTypeRow`: the typed interpreter's literal row at the value type `val code`, computed by a large
  elimination.
* `NotUnitary`: canonical forms of numbers; `add x y ≐ 1` has no principal answer.
* `FamilyLimits`: where the recursive family shows, in two unification problems.
-/
