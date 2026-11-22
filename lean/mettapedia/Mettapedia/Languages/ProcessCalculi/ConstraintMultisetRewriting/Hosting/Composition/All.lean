import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Systems
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Restriction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Unmatched
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Beside
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Neighbours
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Readback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Unions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.AlongRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.NeighbourControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Knowledge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Readers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.ReadersAlong
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.ReadersClosed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.UnionsFromText
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.UnmatchedControls

/-!
# Composition of hosted programs

A hosted program is its rules **and** its equation rows; the rule for a call that no equation matches
reads those rows by an absence check, the one check of a translation that is not positive.

* `Systems`: the hosted system of a program (`hosted`: the translation and the equation rows) and the
  union of hosted systems; **the hosting of a union is the union of the hostings** (`hosted_union`,
  `start_union`). The correspondence theorems apply to a union because it is a program.
* `Restriction`: a state and some of its rows (`restrict`); what a firing asks of the rows it does not
  select (`admits_restrict`, `admits_extend`, `admits_extend_positive`).
* `Unmatched`: every rule of a translation but the unmatched call's is positive
  (`positive_of_ne_unmatched`, `unmatched_not_positive`); programs and queries with no reachable
  unmatched call (`NoUnmatchedCall`) fire only positive rules (`only_positive`, `only_positive_plain`).
* `Beside`: a state represents an alternative beside other rows (`Beside`); simulation and reflection,
  firing by firing (`simulation_beside`, `reflection_beside`); the unmatched call beside other rows,
  exactly (`unmatched_beside_iff`).
* `Neighbours`: which neighbours a hosted program survives: whole runs both ways beside other rows
  (`runs_forward_beside`, `runs_forward_beside_of_matched`, `runs_reflected_beside`), the answers as a
  set (`answers_beside`, `answers_beside_of_matched`), and the rules of a neighbour, in the reflected
  direction (`firesIn_union`, `Apart`, `beside_after_other`, `runs_reflected_neighbour`).
* `Controls`: one control for each condition, and the pair that separates one firing that reads a
  hosted row from one that takes it (`reading_keeps`, `rule_takes_row`).
* `Readback`: the union of a translated program with a disciplined neighbour's rules reads back to the
  source, the neighbour's firings silent (`neighbourReadback`); the union of the hosted systems of two
  programs answers as the union of the programs (`union_answers`).
* `Unions`: when a program keeps its answers in a union: along its runs no equation of the other
  program matches a call (`SeparateFrom`, `union_conservative`, `union_keeps`).
* `AlongRuns`: the conditions on a neighbour's rules asked at the states a run of the union reaches
  (`DisciplinedAlong`; for both directions `BothWaysAlong`, with the clause that made rows never read as
  equation rows): the union's runs are source runs (`runs_reflected_along`), its answers from the start
  are the source's as a set (`answers_along`), and, for both directions, every move of the represented
  alternative stays one firing after the neighbour has moved.
* `NeighbourControls`: a rule that makes a row read as an equation row meets the reflected condition and
  stops the hosted program (`switched_off`, `answer_lost`); one that makes an unrelated row meets both.
* `Readers`, `ReadersAlong`, `ReadersClosed`: which rules meet the conditions; asking along the runs is
  strictly weaker than asking at every state (`readEqn_strictly_weaker`).
* `Knowledge`: knowledge that binds the query's unknowns gives an instance of the query; knowledge of an
  equation row's private unknown can add an answer; the representation depends only on joint readings.
* `UnionsFromText`: `SeparateFrom` from the program text, for the fragment with `let` (`separate_of_text`).
* `UnmatchedControls`: a row that matches an unmatched call at one solution only, and a row whose
  unknown is shared with the call against one whose unknown is private.
-/
