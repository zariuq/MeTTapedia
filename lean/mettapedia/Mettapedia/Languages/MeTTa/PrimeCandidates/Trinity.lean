import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Triangle
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Source
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Operational
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Intensional
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Extensional
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Joined
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Log2.AdmittedBySetSolution
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream.AdmittedBySetSolution

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
  the evidence of its solution in sets.
* `Stream`: an endless stream as a function from positions, admitted with its written equation
  on the same kind of evidence; among the finite lists the equation has no model.
-/
