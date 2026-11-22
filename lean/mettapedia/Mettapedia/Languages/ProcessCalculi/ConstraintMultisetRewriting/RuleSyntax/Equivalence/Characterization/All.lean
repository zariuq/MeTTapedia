import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Atoms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Static
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.StaticIff
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.StaticControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Programs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Instances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.EveryState
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Labels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.AbsorptionCore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.AbsorptionMoves
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.AbsorptionBack
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Absorption
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Reach

/-!
# What the congruence of programs is, at the one-frame first-order instance

The congruence `Congruent` of `Equivalence` is the largest barbed bisimulation closed under every
context. At the one-frame first-order instance (`Equivalence.AtOneFrame`: atoms as terms, identities
`ℕ`, may-barbs) this folder says which systems it relates.

**States** (`Static`, `StaticIff`). The static equivalence `Static s t`: both knowledges unsolvable,
or the identities of `s` renamed so that `s` and `t` are equivalent modulo the knowledge with the same
support (the same rows up to the renaming, knowledges with the same solutions, labels equal at every
solution, the same mentioned unknowns: `static_iff_clauses`).

* `static_iff`: with no rules, two states are congruent exactly when they are statically equivalent;
  `congruent_iff_static`: the same beside any program that leaves a constant unused (`Bounded`; finite
  programs are, `bounded_of_finite`).
* `static_of_congruent`: congruent systems with two such programs, possibly different, have
  statically equivalent states. The solutions are observed by a tell that kills one side, the rows by a
  probe whose witness is a constant no program uses (`mayBarb_swap`), the support by a rule whose
  unknown one side can open as the unknown the other side mentions.
* Corollaries and controls (`StaticControls`): the tautology `y = y`, the row `x` against the row `y`,
  one row `7` against two, each by the clause it breaks; one control per clause; and systems with
  unsolvable knowledge, all congruent, with no bijection of rows (`unsolvable_example`).

**Programs** (`Programs`, `EveryState`).

* `programs_iff_answersUpTo` (every frame action and barb family): two programs are congruent at every
  state exactly when each answers the other's firings, at the same state, with results congruent under
  the first.
* `programs_iff` (one frame, bounded programs): exactly when each answers the other's firings with
  statically equivalent results; `congruent_of_answersStatic` is the sound direction for every pair.
  Absence and count queries are allowed.
* `congruent_iff_static_and_same`: two systems are congruent exactly when their states are statically
  equivalent and the two programs are congruent at the first state; `answers_of_congruent` is the
  per-state necessary condition used to separate programs.
* `congruent_empty_iff`: congruence of programs at the empty store is congruence at every state;
  `separated_by_build`: a firing with no static answer at a state `s` gives the separating context,
  which adds the rows of `s` and tells its knowledge.

**Instances** (`Instances`): Laws 1, 2, 3, 4 and 7 by the characterization; Laws 5 and 6 (whose proofs
in `Equivalence` already answer firing by firing) turned into static answering; static equivalence an
equivalence relation; the folder's separations of programs as firings without a static answer at the
state a context reaches; an equivalent pair outside the seven laws (`subsumed_example`); an
inequivalent pair with its separating context (`touch_separates`).

**The general form** (`Reach`): `congruent_iff_static_and_reachable` (bounded programs): two systems
are congruent exactly when their states are statically equivalent and the two programs, each beside
the rules a context added, answer each other's firings statically at every configuration reachable
from the first state by contexts and joint firings (`Reachable`); `congruent_of_reachable` is the
sound direction for every pair of programs.

**Labels** (`Labels`): an absence-guarded firing has no least enabling tell context
(`no_least_enabling_tell`), because "an unknown is not `9`" is not an equation; with an equation guard
instead, the least enabling tell context exists (`least_enabling_tell_read`).

**The bound is needed, even for positive programs** (`Absorption`, with `AbsorptionCore`,
`AbsorptionMoves`, `AbsorptionBack`): beside the program of every positive rule, which is not bounded,
one row `5` and two rows `5` are congruent and not statically equivalent (`positive_rules_absorb`,
`bounded_needed`): every firing at one side is answered at the other by a positive rule doing the same
with one row `5` more or less.
-/
