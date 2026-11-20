import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Views
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Clauses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Scoping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwiceAsWritten
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleHolding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwiceAtRunTime
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleComputedValue
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleUnknownHead
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleReturnedFunction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Hosted
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleMap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleCompose
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleDeclared
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ByValue

/-!
# A call through a function variable

A tuple whose head is not a symbol, `($f a)` or `((g) a)`, names no function where it is written. The
elaboration `Elaboration.elabText` calls such a tuple as it stands, so its arguments are held text. This
folder states the readings of such a tuple as clauses of one elaboration, each with its laws, its runs
in the reference semantics `Semantics.Step`, and where it applies the run theorems of the translation
into the step. Nothing here changes `Elaboration`: the elaboration with the clause as a parameter is
`elabH`, on readings that keep a tuple's elements (`Views`), and under the clause that calls the tuple as
it stands it is `Elaboration.elaborate` (`elaborateH_asWritten`).

**The clauses** (`Clauses`).
* `Clause.asWritten`: the tuple is called as it stands.
* `Clause.byValue`: the head is a position that wants a value (a call there is computed first, at its
  own arrow); every argument is evaluated at its own arrow; a `hold` mark passes text.
* `Clause.declared holds`: an argument is held when the type declared for the head variable holds that
  parameter, evaluated otherwise. On `twice` it is the program by value when the declared type holds
  nothing and the program that calls the tuple as it stands when it holds the parameter
  (`ExampleDeclared`).
* `Clause.atRunTime`: the tuple is run as text when the alternative reaches it; the reading of the
  dereferenced text consults the declarations of the head the store has bound.

**The elaboration by value beside `Elaboration.elaborate`** (`ByValue`): `elaborateByValue` and
`elabQueryByValue` are the elaboration under `Clause.byValue`. The two elaborations agree on every program
and query in which no tuple with a head that is not a symbol stands at a position the reading reaches
(`elaborateByValue_agrees`, `elabQueryByValue_agrees`), and differ on the text of `twice`, where the
first answers `(S (S Z))` and the second `(S (inc Z))` (`twice_compared`, `twice_programs_differ`). The
run theorems of the translation apply to the elaboration by value of programs without declarations read
by value (`byValue_runs_forward`, `byValue_answers_hosted`, `byValue_runs_reflected`).

**What separates them.**

| text | as it stands | by value | at run time |
|---|---|---|---|
| `(twice inc Z)`, `(= (twice $f $x) ($f ($f $x)))` | `(S (inc Z))` | `(S (S Z))` | `(S (S Z))` |
| `(twice keep Z)`, `keep` holding its parameter | `(Kept (keep Z))` | `(Kept (Kept Z))` | `(Kept (keep Z))` |
| `(twice Box (mk))`, `(mk)` computing the datum `(one)` | | `(Box (Box (one)))` | `(Box (Box I))` |
| `((get) Z)`, `(= (get) inc)` | `((get) Z)` | `(S Z)` | |

(`ExampleTwice`, `ExampleTwiceAsWritten`, `ExampleTwiceAtRunTime`, `ExampleHolding`,
`ExampleComputedValue`, `ExampleReturnedFunction`; each entry is the bag of a quiescent run.) By value,
`map` with a function argument answers `(Cons (S Z) Nil)` (`ExampleMap`) and `(compose inc dbl Z)` answers
`(S (D Z))`, each call through a variable answered only by the function the store has bound its head to
(`ExampleCompose`).

**Laws.**
* *The clauses differ only on tuples whose head is not a symbol* (`elabH_eq`).
* *A computed value never runs again* under the static clauses (`valuesH_never_run`); the run-time clause
  runs the whole tuple, and a computed value in it runs again (`atRunTime_reruns`,
  `ExampleComputedValue.bags_differ`).
* *Naming a function does not change the code of its call* under a static clause, for a function that
  takes its arguments the way the clause passes them (`naming`, `passOf_byValue`): by value, those are
  the functions of a reading by value that hold no parameter. A function that holds a parameter and is
  called through a variable receives a value under the clause by value
  (`ExampleHolding.byValue_differs`), and its text under the other two.
* *The fragment with arrows is closed under the static clauses that evaluate or pass text*
  (`elabH_arrow`, in `Hosted`), and the code is scoped whenever the elaboration's is, with distinct binder
  sites (`elabH_scoped_of`, `elabH_nodup`, in `Scoping`): for programs without declarations read by value, the
  three run theorems of the translation apply (`static_runs_forward`, `static_answers`,
  `static_runs_reflected`; instances `twice_answers_hosted`, `ExampleTwice.hosted`, `ExampleMap.hosted`).
  The run-time clause leaves that fragment (`ExampleTwiceAtRunTime.not_arrows`). `WellFormed` asks more
  than the run theorems use and is not kept by the added arrows in general (`wellFormed_not_carried`).
* *A head that is unknown when the call is reached is found, not waited for*
  (`ExampleUnknownHead.head_found`, under the clause by value): the call of the reference semantics
  unifies two ways. At run time the reading of a tuple whose head is still a name calls it as it stands,
  and the call finds the head the same way (`ExampleUnknownHead.atRunTime_answers`).
* *The law of extension does not reach a call through a variable*: its condition asks every called
  datum to be separated from the added equation, and a tuple with a name at its head is not
  (`ExampleUnknownHead.not_separated`). Which function answers such a call is decided by what the store
  has bound the head to (`ExampleCompose.dead_inc_inner`, `dead_dbl_outer`).

`Runs` gives the runs of one alternative beside dead ones, by which the runs above are made.
-/
