import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Sets
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Bags
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.SameStart

/-!
# The answers of a hosted program, read from the step

* `Sets`: the step alone determines the **set** of answers: `answers_as_sets` (first fragment) and
  `arrow_answers_as_sets` (the fragment with `let`, under the clauses the run theorems use).
* `Bags`: two programs with different bags have one translation (`same_translation`, `p1_answers`,
  `p2_answers`; their start states differ), and the larger bag is read off one reachable state counted
  twice (`one_state_twice`); one reachable state represents two alternatives (`two_alternatives`). A
  frontier's multiplicities are those of the source's live alternatives. That the step does not
  determine the bag, with the same rules and the same start state, is `Answers.SameStart.bags_differ`.
* `SameStart`: two programs with the same rules and the same start state have different bags
  (`bags_differ`); the hypothesis of the bag theorem of `Hosting/Alternatives/` that fails is the one of
  pairwise distinct schemas.
-/
