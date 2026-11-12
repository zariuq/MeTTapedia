import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.HeatingBisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoChannelFragment
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoPeekOutside
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.NarrowingToRho
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoRedexAmbiguity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.GroundFirings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReadOnlyQuery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.MonotoneInference
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.LinearTake
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RefinedScheduler

/-!
# Fragments of the step

A fragment is a property of rule sets; no rule of the language is forbidden. Each named fragment
carries its theorem and controls just inside and just outside it.

* **Maps of transition systems** (`TransitionMaps`): functional bisimulations, open maps and their
  path lifting, observations with the identity as the whole view, OSLF's possibility and necessity
  types pulled back along them, and bisimilarity read through them in GSLT.
* **Take and make** (`HeatingBisimulation`): every rule set without reads and checks is, through
  heating, strongly bisimilar to reduction modulo associativity, unit and symmetry of composition, on
  the configurations whose knowledge the chosen solution models. The structural congruence enters
  only through heating. On those configurations the absence-guarded `spawn` has no such
  bisimulation, while `make T`, the same rule without its guard, has one.
* **Channel communication** (`RhoChannelFragment`): the rules that take one message and one receiver
  on the same name and make the continuation are strongly bisimilar to rho's communication; the
  reflection rule lies just outside, and so does a receive that keeps its message (`RhoPeekOutside`).
* **The narrowing** (`NarrowingToRho`): reading a heated store as one process is an open map onto
  rho's reduction, whose fibres are heating classes; rho's reduction is the step observed through it.
  Lifts are unique up to heating, not on firings, already on rho's own communication
  (`RhoRedexAmbiguity`). On the ground step, among firings without queries whose checks are none or
  one absence guard, exactly those without a check stay admitted beside every store; no theorem links
  this to the narrowing. Absence is seen by the whole-store view.
* **Read-only queries** (`ReadOnlyQuery`): the store is unchanged and a query is never a cause; both
  orders agree whenever the query's survival of the other firing is entailed, which is discharged
  on ground terms.
* **Monotone inference** (`MonotoneInference`): over ground terms, the facts that stay reachable from
  any run are Datalog's least model, the least fixed point of the immediate-consequence operator,
  whatever the order.
* **Linear take** (`LinearTake`): on the ground step, monotone under union, and independent firings
  without checks interchange.
* **Schedulers** (`RefinedScheduler`): a scheduler fires only firings the step admits, so it is a
  refinement of the step and sound by construction; it need not be complete. CHR's refined
  semantics is not modelled; it would be one such scheduler.
-/
