import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.FramedMachines
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.HEMachine
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.Triangle
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.NamedDifferences

/-!
# HE on the step

* `FramedMachines`: a machine with a world, a control, first-order continuation frames and published
  answers, placed on the step's store with one occurrence per component. For a local machine
  (every transition pops and pushes frames and is the same move over any base of the stack), one
  transition is one firing: a strong bisimulation, with the answer bag and the world as readouts,
  no administrative firings and the same divergence. Without locality the step misses transitions.
* `HEMachine`: HE's retained-control machine, read-only and with a shared world, is local (all its
  transition rules), so it is a fragment of the step.
* `Triangle`: against HE → PeTTa → PeTTa's store projection, the store reached agrees on read-only
  runs; the read word does not (PeTTa records the selected rows, HE's machine reads its whole space).
* `NamedDifferences`: removal, re-evaluation by return type, held arguments under `%Undefined%`, and
  conjunctive match, each a program with HE's and PeTTa's outcomes.
-/
