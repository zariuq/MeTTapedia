import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Elab
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Laws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Embed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Transfer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Choice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Determines
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Adversarial

/-!
# The type of a position decides whether text runs

A typed elaboration over the study's core, in which every position's expected type is computed from
the declarations, and held text (`Atom` or `(Code T)`) is quoted at a position whose type holds and
run at a position of a value type. The family `TDesign` adds two choices to it: the default at
ambiguous positions (`%Undefined%`, an unrelated type variable), and whether plain `Atom` text runs
at all. `byType` is the member that consults only the position's type.

* `Elab`: the family, one elaboration (`elabW`, the decision as data), the definitional facts that
  decide hold or run from the declarations alone.
* `Laws`: weakening a value result holds exactly where the default runs (`resultWeakening_iff`);
  weakening a held annotation to `Atom` holds exactly in `byType` (`heldWeakening_iff`); no answer
  function weakens both `Number` and `(Code Number)` to `%Undefined%` (`no_cross_mode_weakening`);
  `let` and values final in every design and every program; the plain reading at the root in
  `byType`; inertness under held results in every design.
* `Embed`: by-name is `byType` on the study's programs, and code value is `codeOnly`, as equal core
  programs; every `byType` program is the by-name run of its projection.
* `Transfer`: identity insertion, HE's `if` and the field reading hold in `byType` for every typed
  program, from the study's by-name theorems.
* `Choice`: alternatives; a value parameter is one shared choice, held text two independent ones
  (general theorems, and the bags).
* `Determines`: the two weakening laws hold together exactly in `byType`; the rows of the Prime test
  lines, HE's `let` and `if`, and the PeTTa lane's held arguments.
* `Adversarial`: by value against by name (unused, refused and diverging arguments), inspection of
  text against the run that loses it, odd programs, and data handed to a held parameter.

## Boundaries of the model

* By need is not a design of this core: it needs a store of memo cells local to each alternative.
  The tree's call-time-choice calculus has it, with the separating programs proved there.
* Heads that are variables, spaces, `match`, `collapse`, effects and `quote` as a special form are
  outside the core; their rows are measured, not modelled.
* No inline annotation is part of the surface: an annotation honoured when data is run would make
  the run of data containing it differ from the study's designs, so the exact embeddings would need
  an invariant over every run. The explicit hold is the library idiom `(hold $x)`.
-/
