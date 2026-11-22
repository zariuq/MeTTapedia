import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.AcceptanceTests
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.Refinement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.VectorPackage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.VectorPrograms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.RecursiveRun
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.UniverseLevels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.SigmaIdentity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.ConversionContrast
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.MicromathConsumer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.SetExtensionality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.TypedInterpreter
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.LargeElimination

/-!
# Programming on the step

Programs run end to end by the dependent full step (`Interface.DependentFull.step`), with the
places where the theory limits them, each proved on the tree's own objects.

* **Acceptance tests** (`AcceptanceTests`): four laws a stronger theorem might state, each refuted on
  the tree's objects with the weaker law that holds: a solvable store with no principal answer;
  absence against framing; pairwise compatibility without a joint wave; solvable without being
  inhabited, also on the dependent full step.
* **Refinement** (`Refinement`): a made row is typed in the frame, before solving; a firing whose made
  row is typed at every solution of its own information is refused.
* **Vectors and finite indices** (`VectorPackage`, `VectorPrograms`): an all-rigid package within the
  tree's normalization model; lookup by a finite index and append with implicit lengths run as
  admitted firings; the recursive `lookup` runs as a two-firing run of the step, the recursive call's
  arguments staying unknowns determined by the knowledge (`RecursiveRun`); a function evaluated by
  firings is invisible to the knowledge, so its equations never identify the types that mention it.
  The recursion equation of addition holds in the knowledge where addition computes in conversion,
  and is refuted where it is evaluated by firings (`ConversionContrast`).
* **Universe levels** (`UniverseLevels`): one unannotated definition is typed and used at two levels
  by one admitted firing; its uses at different levels never match.
* **Dependent pairs and identity types** (`SigmaIdentity`): a dependent pair taken apart by a
  dependent telescope; matching `refl` identifies the endpoints at every solution; an empty identity
  type has no closed inhabitant, its frame is a state of the step, and matching `refl` on it is
  refused.
* **A typed interpreter** (`TypedInterpreter`): `eval tnat (lit 3)` runs to `3`; the answer can never
  be handed to a hole of its declared type `val tnat`, since value types computed by firings are
  rigid and apart from `nat`. With the value type a large elimination computed in conversion
  (`LargeElimination`), the answer has its declared type and the return is solvable.
* **Sets as predicates** (`SetExtensionality`): comprehension is abstraction; two sets with the same
  members, witnessed by two closed swaps, cannot be told equal, since the knowledge is intensional.
* **A proof-system consumer** (`MicromathConsumer`): a Micromath run on the step stores a theorem,
  the consumer's soundness theorem applies to it, and the theory has a two-element model that
  refutes a theorem it does not prove.
-/
