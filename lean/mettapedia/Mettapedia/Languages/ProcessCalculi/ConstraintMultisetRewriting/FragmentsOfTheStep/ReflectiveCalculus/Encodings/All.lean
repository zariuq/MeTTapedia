import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Criteria
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Barbs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Translation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.FirstHalf
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Compositionality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Barbed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Congruence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.RhoTarget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Strict
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Junk
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.SystemsCalculus
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.DividingLine
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.DividingLineControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Carrier
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Divergence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Gap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Witnesses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.TwoFirings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.GroundCollect
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.MustReading
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Counting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Idempotence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Cancellation

/-!
# The reflective calculus and the step under named criteria

Both directions between the reflective higher-order calculus (closed processes of the sealed carrier,
its reduction modulo its equations) and the step defined by rule syntax, each under a criterion named
in its statement, with the composition of systems named in the statement of the separation.

* `Criteria`: Gorla's five properties for a translation between two calculi (terms, reduction,
  success, equivalence), his homomorphism of parallel composition, and the bridge to the uniform
  criterion of `NullsOnTheStep.ParallelClosed` (`uniform_iff`: homomorphism and success
  sensitiveness); controls on calculi of two points, each failing exactly one operational property.
* `Barbs`: the output barb on the step (the tree's may-barb of `c!(Q)`), barbs through the
  representation, runs both ways, weak barbed bisimilarity, divergence.
* `Translation`: the tensor of states and the translation of closed processes into states as a
  function on syntax, homomorphic on parallel composition on the nose; an input or an output is one
  row determined by the prefix; the single-row translation as a control.
* `FirstHalf`: the translation meets Definition 5.2 and Gorla's Properties 3, 4 and 5, and Property 1
  at parallel composition; the correctness of one communication's contractum
  (`contractum_correct`); Property 2's renaming clause is not shown, and has content here because the
  calculus's names are global.
* `Compositionality`: the translation is not compositional at output or input in Gorla's sense: no
  function of the translated argument gives the translated prefix.
* `Barbed`: full abstraction for barbed bisimilarity indexed by a set of names follows from the
  representation alone (every representing translation is fully abstract); every output is read as a
  barb, against the 2005 definition's outputs of dropped names, and under that literal reading the
  control `index_matters` disappears.
* `Congruence`: weak barbed bisimilarity is not a congruence for the tensor, even on represented
  states; the tensor is neither commutative, associative nor unital on the nose, and is all three up
  to weak barbed bisimilarity on represented states.
* `RhoTarget`: the faithful calculus is persistent, and is a target of the separation for the
  none-guarded and the positive-tell sources of `NullsOnTheStep.ParallelClosed`.
* `Strict`: the strict separation under the uniform criterion, with composition of systems restricted
  to solvable joint knowledge (`strict_separation_solvable`): the reflective calculus embeds into the
  step, and the step does not embed into it, for every relation on the reflective side that respects
  reachable success (`no_translation_any`); the negative half is witnessed by a rule guarded by the
  none queries of a row.
* `Junk`: the control for the restriction: with every pair composable, knowledge without a solution
  switches off every system, the translation of a process included, and the same criterion separates
  the reflective calculus from the states of its own four-rule program
  (`strict_separation_fourRule`).
* `SystemsCalculus`: the calculus of the separation is one of systems, whose composition brings rules:
  the richer criteria fail there up to equality and hold up to a lifted bisimilarity, and the image of
  `0` is not a unit.
* `DividingLine`: in the restricted composition, a system whose rules have only equation checks and
  no collect pattern is switched off by no composable neighbour, whatever the neighbour's rows and
  rules (`succeeds_beside`); so every switch has a none check, a count check or a collect pattern
  in the switched system (`switched_has_guard`). The calculus of such systems is not switchable, and
  is not persistent in the sense of `ParallelClosed`, whose persistence quantifies over every pair.
* `DividingLineControls`: a neighbour's rule takes the system's success row (rules cross; success,
  being may-success, survives); a count check and a collect pattern are each switched off by a
  composable neighbour.
* `Carrier`: what the sealed carrier excludes, and why the first half does not extend there by this
  translation.
* `Divergence`: divergence is preserved as well as reflected, and a self-reproducing process of the
  carrier diverges, so the hypothesis of divergence reflection is met.
* `Gap`: the separation extends to every compositional translation whose parallel context has both
  holes at top level beside a coordinating process; with a guarded hole the argument fails in the
  faithful calculus, and Gorla's Proposition 5.6 is the missing step.
* `Witnesses`: restricting composition strengthens the negative half; a count check and a collect query
  pattern witness the separation as well as none queries.
* `TwoFirings`: an instance of `succeeds_beside` whose success needs two replayed firings, beside a
  rival for the same row.
* `GroundCollect`: a collect query over a ground pattern is switched off by a neighbour whose row has an
  unknown of its own, and not by a ground row.
* `MustReading`: with success read on every maximal run, a positive system is switched off by a
  positive neighbour; `succeeds_beside` is about success that may be reached.
* `Counting`, `Idempotence`, `Cancellation`: under this criterion the systems with no none check,
  count check or collect pattern do not embed into the reflective calculus either, for two reasons
  that come from a program being a set of rules: there are uncountably many programs and countably
  many processes; and a program beside itself is the program, while the equations of the reflective
  calculus cancel a common parallel component (barbed bisimilarity does not).
-/
