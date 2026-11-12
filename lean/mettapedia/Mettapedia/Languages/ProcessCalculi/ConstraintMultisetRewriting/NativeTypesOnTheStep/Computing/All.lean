import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Qualification
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.RootDeterminism
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DeclarationCheck
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.TwoReadings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.ValueType
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.VectorFunction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.VectorRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.ListFunction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.HostTables
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.AnswersTyped
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.BudgetedConversion

/-!
# One `=`, two readings: when an equation may compute in types

* `Qualification`: the class of equation sets qualified for the definitional reading (constructor
  system, typed right sides, semantic constants for the typed and the algorithmic equality) and its
  consequences: Church–Rosser with β, subject reduction, conservativity, weak-head normal forms, and
  conversion with η decided by the type-directed algorithm; η is not untyped conversion and does not
  preserve typing as a reduction; the executable package (addition, the iterated power set, the
  iterator, identity elimination, a type family computed with addition) is qualified; an overlapping
  declaration and an untyped leaf are not.
* `RootDeterminism`: root determinism is necessary for the class; declarations that are
  root-deterministic yet overlap below the root, loop, have an ill-typed right side, are partial, or
  read the store.
* `DeclarationCheck`: the syntactic declaration-time check as one Boolean function of the rows
  (constructor patterns at the declared arity, linear, covered, pairwise non-unifiable), sound for
  Church–Rosser; addition and append pass; overlap, nesting, non-linearity and an uncovered variable
  fail; the looping row passes, since termination is a separate check.
* `TwoReadings`: the operational reading (answers reached by firings) agrees with the definitional one
  (conversion normal forms) on Church–Rosser packages; ground calls of the declared addition answer
  exactly once, a numeral typed-equal to the call; the classification with one smallest counterexample
  per cause.
* `ValueType`: the numbers with their recursor are qualified at every level; at level one the value
  type of an interpreter computes and is typed: `val 1 ≡ num → num` at the universe of small types,
  and the identity has type `val 1`.
* `VectorFunction`: append with an inaccessible length argument, with addition, is a constructor
  system; ground calls answer exactly once.
* `VectorRows`: both rows of append are typed after their match at the declared `vec (add m k)`.
* `ListFunction`: the list package (`rev-onto`, `dfa-run`, by structural recursion with a changing
  accumulator) is qualified at every level: its ten rows present its computation and pass the
  syntactic check, and its declaration records give semantic constants for both equalities.
* `HostTables`: a host table may enter conversion when it is a function on ground values; two answers
  identify values; a missing row leaves a stuck call; a host call inside a pattern is no constructor
  pattern.
* `AnswersTyped`: the step's check after the match gives every answer its declared type and refuses a
  mistyped answer for every settler; a type computed through a host table.
* `BudgetedConversion`: a budgeted conversion check with the outcomes equal, different and not decided
  within the budget, sound in all three, monotone in the budget, complete in the limit.
-/
