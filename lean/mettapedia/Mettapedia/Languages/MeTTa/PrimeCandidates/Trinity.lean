import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Triangle
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Source
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Operational
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Intensional
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Extensional
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Joined
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Log2.AdmittedBySetSolution
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Arith.Binary
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Arith.Oracle
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream.AdmittedBySetSolution
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream.Joined
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream.Hyperset
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.GradedIdentity.Typed
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.GradedIdentity.Joined
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Reverse.Program
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Reverse.Joined
import Mettapedia.GSLT.Dynamics.DemandAgreement
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Demand.NeedInstance

/-!
# The three faces of a candidate, on a curriculum of small programs

A candidate has three faces: what runs, what is typed, and what a thing is as a set. The
modules collected here treat small programs on all three and prove the links between them.

* `Triangle`: a triangle of three faces from three maps built separately, with their
  agreement as a hypothesis to prove.
* `Append`: the append of two lists of numbers, run by its two equations, typed in the
  judgment, and defined on sets by recursion; `Append.Joined` proves that the three agree and
  that the triangle is not exact.
* `Log2`: a function whose recursion is not structural, admitted with its written equations on
  the evidence of its solution in sets; closed expressions run to numerals, and the three faces
  are joined in a triangle that is not exact (two inputs, one value).
* `Arith.Binary`: positive and natural numbers in binary as declared datatypes over the object
  package, with the successor, the sum digit by digit with its carry, the product and the
  value maps into the unary numbers, each by written equations; the list is admissible with a
  set model, the equations are typed computation rules, and in the model the value of a sum
  or a product is the sum or the product of the values.
* `Arith.Oracle`: the sum and the product computed natively, as an admitted oracle library
  whose meaning is the declared semantics read through the value maps; Lean's natural numbers
  as the model of the backend meet it, a derivation of the judgment and the backend give the
  same numeral, and the agreement of the compiled backend with the model is an explicit
  hypothesis. A backend off by one at a large value meets neither.
* `Stream`: an endless stream as a function from positions, admitted with its written equation
  on the same kind of evidence; among the finite lists the equation has no model.
  `Stream.Joined` reads a stream through its observations, which stop although the stream does
  not, and joins the three faces under its stated model hypotheses. `Stream.Hyperset` records what the hyperset keeps of a
  running program, the branching (`Stream.branching_kept`), and what it forgets, a duplicated
  edge (`Stream.multiplicity_forgotten`) and the length of a cycle (`Stream.shape_forgotten`).
* `GradedIdentity.Typed`: the weight carriers of the shared graded identity declared in a
  package (numbers under a product, evidence counts under a product of packets), their monoid
  laws derived there, with a set model, and the graded program typed as a scoped computation
  whose charges are computed by typed value-to-weight maps.
* `GradedIdentity.Joined`: a graded program whose stored choice is charged once and used
  twice, run by the native weighted machine to a bag of values with coefficients, read as
  annotated occurrences of the stored rows, and meaning the weighted bag; the annotated
  occurrences are the occurrences of the typed programs of `GradedIdentity.Typed`. Value
  erasure, the set of values and the linear total each forget something the bag keeps.
* `Reverse`: two reversals of a list, plain and onto an accumulator. `Reverse.Program` runs
  them, with a quadratic and a linear number of steps, and types them, with the proof that
  they agree; `Reverse.Joined` defines both on sets, where they are one function, joins the
  three faces, and proves that the cost is not a function of the set.
* `Demand`: when eager, lazy, and resampling evaluation agree on answers. The general laws
  live in `GSLT.Dynamics.DemandAgreement`, since they hold of any evaluator. Discarding agrees
  over bags exactly when there is one answer, and over supports exactly when there is at
  least one. Copying agrees over bags exactly when there is at most one answer, and over
  supports exactly when the support has at most one element. Several uses of one binding
  follow those two lines. `Demand.NeedInstance` runs the reference machine: a literal demanded
  twice agrees with a resampled demand, a choice of `1` and `2` does not, and an effect leaves
  the value bag unchanged while the event trace differs.
-/
