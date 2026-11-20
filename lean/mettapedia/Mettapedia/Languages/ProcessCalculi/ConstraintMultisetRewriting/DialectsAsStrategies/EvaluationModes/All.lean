import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Core
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Designs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Acceptance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.CoreLaws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Weakening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Laws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Separation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Typed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Nested

/-!
# Evaluation modes: what a declared `Atom` and a declared computation type do to evaluation

A parameter declared `Atom` receives its argument as written. When a function returns or uses
such a held argument, the systems of the MeTTa family disagree on whether it runs. This folder puts
every candidate reading into one core and compares them by laws.

* `Core`: one core with explicit quotation (`ret` of a template), running (`run`), sequencing
  (`bind`) and calls; one evaluator with fuel. `CoreLaws`: more fuel changes no finished run, a goal
  has one answer list, weaker result checks change no run that refused nothing.
* `Designs`: the surface (declared parameter and result types, equations) and one elaboration
  `elabC`, parameterized by six choices. Hyperon Experimental, by-name, code value, the withdrawn
  hybrid and the Prime draft are values of `Design`.
* `Acceptance`: each design's elaboration, run by the kernel on the eight measured programs, gives
  its system's measured column (Hyperon Experimental, PeTTa as code value, the Prime draft), and
  the hybrid passes the three test lines of the Prime draft.
* `Weakening`, `Laws`: the laws, proved for every design meeting a stated condition, refuted on
  smallest programs otherwise.
* `Separation`: weakening forces running (for any answer function); the three test lines break
  weakening in every design; the first three laws characterized; with identity insertion, exactly
  the code-value and by-name rules remain, and the choice between them is one bit: the plain
  reading of a returned held parameter (by-name) or inert held text (code value); no design keeps
  both.
* `Typed`: code of a `T`; the exact class of positions that need a default, fixed by weakening;
  HE's `if` typed, with both branches checked against one `$t`.
* `Nested`: heads without a definition, evaluated or held, under by-name and code value; what
  `(pair $x $x)` costs.

## The laws against the designs

| law | HE | by-name | code value | Prime draft | hybrid |
|---|---|---|---|---|---|
| weakening a result type | kept | kept | kept | kept | broken |
| `let` | broken | kept | kept | kept | kept |
| values final | broken | kept | kept | kept | kept |
| plain reading at the root | kept | kept | broken | kept | broken (under `Proc`) |
| plain reading at a field | kept | kept | broken | broken | broken |
| HE's `if` | kept | kept | broken | kept | broken (under `Proc`) |
| identity insertion | broken | kept | kept | broken | broken |
| an `Atom` result builds code | kept | kept | kept | broken | broken |
| an `Atom` result is neutral (no held parameter) | broken | broken | broken | kept | kept |
| substitution of printed values | measured rows | broken | broken | broken | broken |

Each entry is a theorem (`Laws.he_laws`, `Laws.byName_laws`, `Laws.codeValue_laws`,
`Laws.primeToday_laws`, `Separation.hybrid_laws`, `Nested.fieldReading_iff`,
`Laws.atom_result_neutral` with `Laws.atom_result_neutral_rows`), except Hyperon Experimental's
substitution entry, which holds on the measured rows (`Laws.he_substitution_rows`) and is not proved
in general here. The plain reading of an evaluated parameter fails in every design once the
parameter is used at a held position (`Separation.value_param_at_held_position`).

## On the step

On Hyperon Experimental's machine over the step, the entry of an occurrence carries a status,
`active` or `held`, and the machine has a re-entry policy, `reuse` or `reinterpret`. A held
expression under `reuse` is delivered under every transparent demand; an expression is interpreted
when it is active or the policy re-interprets. The designs here are choices of the status a firing
gives the atoms it inserts: the held parameter's text inserted at a computation position (active:
by-name and Hyperon Experimental; held: code value), and a computed value inserted by a `let` or a
parameter (re-interpreted: Hyperon Experimental; held under reuse: every value-final design). The
step's own theorems already prove that the marks change no answer on values of the program
(constructor trees over data atoms) and that a held call of a defined head is not such a value;
that call, `(f a)`, is exactly where the designs here part.
-/
