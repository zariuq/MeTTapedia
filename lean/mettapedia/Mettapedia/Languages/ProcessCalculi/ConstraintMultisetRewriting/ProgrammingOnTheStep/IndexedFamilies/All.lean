import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.AppendOnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.LookupOnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.ClosedCalls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.ImplicitLengths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.RecursiveRun
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsAll

/-!
# Indexed families on the dependent step

Vector programs run by the dependent full step (`Interface.DependentFull.step`) over the package
with vectors, finite types and their eliminators (`TowerVectorsModel.rules`), where the
eliminators and addition compute in conversion.

* **The recursive equation of append** (`AppendOnTheStep`): one firing takes the call
  `append A (succ k) m (pair a v) ys`, makes its result at the call's declared type
  `vec A (add (succ k) m)`, and tells that the call equals its result; it is admitted with every
  variable open. The same firing in the all-rigid package is refused, whatever type its made row
  is given, and the two lengths that are equal here have no common instance there.
* **Lookup by a finite index** (`LookupOnTheStep`): the firing of
  `lookup A (succ k) (pair a w) fz = a`; the frame `i : fin zero` has no closed point, so the
  empty vector has no index.
* **Rules with fresh telescopes on closed calls** (`ClosedCalls`): the recursive equation of
  append fires on `append num 1 1 [2] [3]`, the solution instantiates its telescope, and the made
  row is equal to the value `[2, 3]` at the call's declared type; lookup fires on
  `lookup num 1 [2] fz` with the answer `2`; addition's equations hold in the knowledge.
* **Append with implicit lengths** (`ImplicitLengths`): the lengths of the call are unknowns that
  the knowledge determines; the base equation fires, and its made row has the call's declared
  type, where a package that evaluates addition by firings gives it a type that never meets it.
* **The recursive lookup as a run** (`RecursiveRun`): on `lookup num 2 [1, 2] (fs fz)` the
  recursive equation fires, then the base equation in the state reached; the run's solution reads
  the answer as `2` and solves the whole knowledge.
-/
