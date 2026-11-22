import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.LanguageOnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.ConcurrencySeparation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TakesAreFirings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.MM2ExecStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.PrologOnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.PeTTaAndHE

/-!
# Dialects as strategies on the step

A language is a core step, a strategy over its runs, and an observation.

* `LanguageOnTheStep`: the framework; every strategy sound; schedulers are strategies; handler
  independence for terminating search policies that keep every answer, for what stays reachable
  under schedulers on the monotone fragment, and for orders of independent effects.
* `ConcurrencySeparation`: match then remove is not a take under interleaving (the race); a global
  lock around each deterministic body, with removal of one copy, restores exactly the serial atomic
  runs; in a sequential evaluator the encoding of a take of distinct atoms is exact; atomic firings
  with non-interfering footprints commute.
* `TakesAreFirings`: a ground firing of the step that reads distinct occurrences is, read through
  its labels, an admitted take of its rule with the take's result.
* `MM2ExecStep`: the effect of an MM2 exec step is an admitted ground firing of the step, whose
  admission checks neither the exec's patterns nor that every match was used; byte-least is a
  deterministic scheduler refining the free exec relation; MM2.1 staging is productive.
* `PrologOnTheStep`: depth-first search over leftmost resolution, sound and incomplete; the tree's
  Prolog evaluator is the depth-first handler over its atomic goals on the control-free fragment;
  `Logic.LP`'s SLD refutations are the answers of the leftmost SLD space on ground programs; cut as
  a scoped commit; `\+` operationally without stratification, and stratification as the adequacy
  profile under which an absence below saturated strata stays true; the logical update view of one
  invocation is its pre-state.
* `PeTTaAndHE`: PeTTa's and HE's strategy and observation; the narrowing from the step is open in
  the sequential evaluator and under a lock around each branch, and not open under the interleaving
  model of hyperpose; PeTTa's `with_mutex` and `transaction` commit to the first answer, so around a
  nondeterministic producer they lose answers; host effects and snapshot granularity as
  boundaries.
-/
