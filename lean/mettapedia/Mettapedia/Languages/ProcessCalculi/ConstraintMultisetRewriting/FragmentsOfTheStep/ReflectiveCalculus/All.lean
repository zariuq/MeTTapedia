import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Terms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Source
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Bisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Mechanisms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.FirstOrderInstance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.TwinBinders

/-!
# The reflective higher-order calculus on the step

* `Source`: the calculus of Meredith and Radestock (2005) as the tree has it on closed processes,
  read section by section against the paper, with its controls: quote-drop, communication only up
  to name equivalence, and the substitution that separates it from communication with ordinary
  substitution.
* `Terms`: the step's terms, its knowledge, and three rule schemas (communication, heating,
  clearing).
* `Bisimulation`: `reflective_calculus_on_the_step`, a weak bisimulation of unlabelled reductions for
  all closed processes, with administrative firings bounded; output barbs are related by separate
  lemmas (`barbs_agree`, `barbs_after_heating`).
* `Mechanisms`: what the step's unification does (the channel match is a solvability question of
  the knowledge), name equivalence in the knowledge, the bag laws as a breaking point, the ground
  placement as a control, and why heating is needed.
* `FirstOrderInstance`: the firings are the admitted events of the first-order instance of the
  interface.
* `TwinBinders`: with an input binding the received name and its process twin, the calculus's
  substitution is ordinary substitution (`twin_semanticSubstProc`, `twin_contractum`).
-/
