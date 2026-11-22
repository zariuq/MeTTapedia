import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Terms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Language
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Matching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Firings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Possibility
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.GroundInstance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Boundary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Spatial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Knowledge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.EqualityControl
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.TellDetermined

/-!
# The step of a program with unknowns as a presented language

Rules have their own unknowns; the rows of a rule are first-order terms over the signature of rows (`Terms`), and
the step is `RuleSyntax.step` at one frame over the tree's first-order action.

* **The presentation** (`Language`): one rewrite per rule whose metavariables are the rule's unknowns. Its left
  side is the rule's takes beside a rest: the framework's bag matcher picks distinct rows, and its agreement check
  makes an unknown that occurs twice match equal subterms. Its premises are the builtin equality only: each read is
  `rest = {q, ...qⱼ}`, a match of the read pattern against the rest that consumes nothing, so reads may share a
  row and never read a taken one; each tell and guard is `l = r`. Its right side is the made rows beside the rest.
* **Matching is solving, on ground rows** (`Matching`, `Firings`): the framework's step from a store is a firing
  by matching, a ground instantiation of the rule's unknowns (`step_sound`, `step_prefix`); every solution of an
  admitted firing's information reads each unknown a take or read binds as the match does (`solutions_agree`); so
  admitted firings of `RuleSyntax.step` at ground states with trivial knowledge are firings by matching and back
  (`match_of_admitted`, `admitted_of_match`, with the fresh opening `shift`). A result is ground only modulo its
  knowledge: it is read through every solution of its knowledge (`ReadsAs`).
* **Generated possibility is firing possibility** (`Possibility.generated_possibility`) for range-restricted
  positive programs, at ground states with trivial knowledge, with no premise that asks the step. Existence: a rule
  whose unknown occurs twice fires at `(1 1)` and is refused at `(1 2)` (`pair_fires`, `pair_refused`).
* **The ground presentation is the instance at ground rules** (`GroundInstance.semanticStep_ground_iff`).
* **Controls** (`Controls`, `EqualityControl`, `TellDetermined`): consuming and remaking reads is wrong with
  unknowns (`consumeReproduce_refuses`); a guard over an unknown no match binds is a premise that binds where the
  step asks (`freeGuard_steps`, `freeGuard_refused`); matching modulo the knowledge is two-way
  (`unknownRow_fires`, `unknownRow_no_step`); the relation environment must add nothing to the equality
  (`failingGuard_steps`). Range restriction is sufficient, not necessary: a made unknown determined by a tell is
  presented exactly at the empty store (`tellMade_fires`, `tellMade_reads`, `tellMade_steps`).
* **Spatial law** (`Spatial`): the split law, the generated logic's possibility, a firing of a part as a firing of
  the whole in the generated types (`split_possibly_schematic`) and on `RuleSyntax.step` (`fires_beside`).
* **Where it stops** (`Boundary`, `Knowledge`): the class of premises is closed under parallel composition and so
  never presents absence (`schematic_not_absence`), and open bags are needed (`closedBag_not_parClosed`); an
  unknown that survives a firing leaves a result that reads as no store (`survivor_unread`) and a presented term
  that is no store (`survivorTerm_not_store`); a tell that binds a caller's unknown needs the knowledge in the term
  (`knowledge_needed`); with the knowledge in the term and an oracle premise of joint solvability, the tell is
  presented (`knowledge_presents_switch`) and the step is switched off by a parallel component, so no relation
  closed beside is that step (`knowledge_no_context_rule`).
-/
