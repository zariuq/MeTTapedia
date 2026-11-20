import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Signature
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Knowledge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Contractum
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Rows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Effects
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Housekeeping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Bisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.ReactComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Runtime
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Decision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Translation

/-!
# The reflective higher-order calculus on the step of a program, by ordinary instantiation

An input binds the received name and its process twin, and a drop of a bound name is the twin. The
calculus is then a program of the step defined by rule syntax whose communication rule makes the
continuation instantiated at the received name and process: the made row is the opened rule's
made pattern, and no former of the term algebra computes a substitution.

* `Signature`: the twin-binder signature (input binds `[nm, pr]`; the only drop former is the drop of
  quoted code) and the read-back into the source's patterns, former by former.
* `Knowledge`: the frame action, the tree's contextual frames of that signature with equality in the
  knowledge "every grounding makes the two terms similar": closed names up to the calculus's
  equations, everything else as written.
* `Contractum`: the instantiated continuation, read back, is structurally congruent to the
  calculus's semantic substitution, and has the canonical form of its contractum.
* `Program`: the four rules (communication, heating, clearing a bag, clearing `0`), their unknowns
  (the continuation is second order), the takes in the tree's pattern class, and the step.
* `Rows`, `Translation`: every closed process is the read-back of a twin term; the translation
  `toTwin` inverts the read-back, which is injective.
* `Effects`, `Housekeeping`: what each firing does to a represented state.
* `Bisimulation`: `reflective_calculus_by_instantiation`, a weak bisimulation for all closed
  processes with housekeeping bounded.
* `ReactComparison`: the comparison with the placement by the `react` former, as theorems; the equality of the knowledge; the `react` placement's made row as a
  normal form of the new one; examples inside and outside the carrier.
* `Decision`: the admission of a communication is decided by the canonical forms of the channels.
* `Runtime`: the programs run on the engine, read through the program's step.
-/
