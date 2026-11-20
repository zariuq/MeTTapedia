import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Compile
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Verdict
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Development
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Acceptance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.OnDefinitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.OnDefinitionsDouble
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Laws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Correspondence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Whole
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Existence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Extension
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.ExtensionRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Agreement

/-!
# A checked definition by rows, as a function

Two constructions of a definition by rows over the vectors package, and how they meet.

**The definition as a constant** (`Extension`): a new constant at the declared type whose rows join the
package's computation, as the package's own addition, `vec` and eliminator do. For a vector parameter
the rule matches the length by `zero`/`succ k` and takes the vector apart by the projections. Proved
for every development whose rules pass the tree's own declaration-time check beside the package's
rows: the extended package is Church–Rosser, contains the package's steps, and is conservative over the
old terms; when the development's names are not declared in the package, every typing and typed equality
of the package holds in the extension. Its qualification (typed right sides, termination) needs the row
checker run over the extended package with the function a declared constant; that is not built here.
The extended package runs its calls by its own table: append over addition by rows takes `[2]` and
`[3]` to `[2, 3]`, its only answer there (`ExtensionRuns`).

**How the two meet** (`Agreement`): reading the constants as their compiled terms is sound for
conversion, for every term, once every rule read at the compiled terms joins; and for a constant
defined by recursion on its call index with saturated recursive calls, or by one row without a call
index, a call of the constant is convertible in the extended package with the same call of the
compiled term, at every numeral index. `DirectedAnswers.Rows` draws the answers from it.

**The definition interpreted in the package without new rules** (`Compile`, `Verdict`, `Whole`,
`Existence`): the definition compiled to an application of the recursor of the numbers, over the
function's own name when the rows do not cover. Proved for every definition whose verdict is a function:
the compiled term is typed at the declared type, every row holds as a conversion at every instance,
every call is typed at its declared type with at most one answer, constructor rows answer by their
body, uncovered calls answer themselves; with the existence check, every call at a numeral and normal
arguments has an answer. This is an interpretation of the new constant in the package: its rules hold
there as conversions.

* `Compile`: the class, call abstraction to the induction hypothesis, the compiled function, the
  filler of uncovered cases, the export of a closed function.
* `Verdict`: the checker of definitions as functions and its generic guarantee.
* `Development`, `Acceptance`, `OnDefinitions`, `OnDefinitionsDouble`: the definitions, the table by
  kernel evaluation, definitions on definitions.
* `Laws`: each condition of the class with its smallest counterexample.
* `Correspondence`: where rows typed after their match give the compiled typing, and where not.
* `Whole`, `Existence`: calls, their answers, the uncovered calls; existence by induction on the numeral.
* `Extension`, `ExtensionRuns`: the definition as a constant of the package, and its calls run by its
  rules.
* `Agreement`: the constant and its compiled term, convertible in the extended package at saturated
  calls; the reading sound for conversion.
-/
