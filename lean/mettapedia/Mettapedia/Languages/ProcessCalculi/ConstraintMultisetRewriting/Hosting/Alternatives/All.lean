import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Chains
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Named
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Classes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.RuleClasses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Located
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Worlds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Readings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.CanonicalHistories

/-!
# Alternatives of a hosted program: counted by the step, and spaces shared between them

**What an alternative is on the step.** For a program of the first fragment of the hosting
(`ret`, `apply`, `choice`, `fail`):

* every history of the step of the translated program is a chain whose firings each take the row the
  one before made (`hosted_chain`): its causal order is linear, and no two adjacent firings can be
  swapped;
* the readings at the end of a chain are a function of its word of rules (`chain_reads`), so fresh
  names, extensions, openings and row identities never change an answer
  (`same_word_same_answer`);
* **with the program's equations named by their positions, the bag of answers of the configuration a
  complete source run ends in is the bag over the complete classes of named histories**
  (`bag_of_classes`), so it does not depend on the source run (`answers_determined`);
* **when the equations have pairwise distinct schemas, the names add nothing: the bag is the bag over
  the complete classes of histories by rules, read off the step alone** (`bag_of_rule_classes`); with
  two equations of one schema the step has one class where the source counts two
  (`Controls.duplicate_two_classes_one_rule_word`, `Controls.dup_schemas_not_distinct`).

**Spaces shared between alternatives.** Two candidate states, each with the present step as its
one-alternative instance: knowledge located per alternative (`Located`, `one_location_steps`) and
worlds sharing a space whose rows are rules (`Worlds`, `one_world_steps`). Two readings of a shared
space (`Readings`): with one world for all alternatives, the observation of a query is a set of bags
(`shared_race`); with a world per alternative, moves of distinct alternatives commute
(`sep_commute`) and the race ends with one bag (`sep_race`).

Canonical histories (`CanonicalHistories`) cover the first fragment with a plain query whose data
mention no opened name.
- Every named history has a canonical history with the same rule-name word: each firing is the canonical firing of the rule its name denotes. Both last states represent one alternative at one world (`canonical_representative`).
- Every canonical history of the word represents that same alternative, with the same answer, finished status and terminal status (`canonical_every_representative`).
- Canonical histories are named histories (`canonical_chain_named`).
- Complete and finished classes, the class answer and the bag of classes read the same through canonical histories.
- A named history whose last state no canonical history reaches shows that the representative can end elsewhere (`swappedEnd_not_canonical`, `possibly_new_endpoint`). Outside the fragment, a `let` start represents no plain alternative.
-/
