import Mettapedia.GSLT.Scope.WorldModel
import Mettapedia.GSLT.Scope.Simulation
import Mettapedia.GSLT.Scope.SimpleFragment
import Mettapedia.GSLT.Scope.SimpleFragmentExecutable
import Mettapedia.GSLT.Scope.SimpleFragmentBeckChevalley
import Mettapedia.GSLT.Scope.SimpleFragmentObjectCompleteness
import Mettapedia.GSLT.Scope.RevisionWorkflow
import Mettapedia.GSLT.Scope.Provenance
import Mettapedia.Cybernetics.MindWorldBisimulation
import Mettapedia.Cybernetics.MindWorldApproximation

/-!
# The scope algebra on existing connections

The laws of `Mettapedia.GSLT.ScopeAlgebra` applied to structures already in
the library.

* `Scope.WorldModel`: the observational quotient of a world-model reading is
  a view; agreement is transport of every family over it, revision is an
  update square supported exactly under the calculus's compositionality law,
  and reading morphisms that cover the target queries satisfy the forth law.
* `Scope.Simulation`: transition systems as GSLTs; functional simulations are
  operational translations and functional bisimulations (bounded morphisms)
  are covered translations; nondeterministic support is a kernel
  bisimulation; update squares are complete abstractions in the sense of
  abstract interpretation; bounded morphisms preserve and reflect
  Hennessy–Milner formulas.
* `Scope.SimpleFragment`: the four kinds of scope change on the candidate's
  simple fragment: erasure as a conservative translation over the
  candidate's conversion, the slice gaining strong normalization, η as a
  non-conservative carve, and forgetting to βη.
* `Scope.SimpleFragmentExecutable`: the sealed tower's steps and the
  executable package's reduction coincide on pure λ-terms and differ off
  them; erasure is a bounded morphism into the executable package, so
  strong normalization and bisimulation hold in one relation on the slice.
* `Scope.SimpleFragmentBeckChevalley`: erasure against the β and βη
  observers; which squares commute (the typed slice) and which fail (all
  raw terms, erasures of every type, one-sided forgetting); the typed
  η-equality on erasures is βη, and descent transfers along the commuting
  squares.
* `Scope.RevisionWorkflow`: world revision, abstraction change, strategy
  change and implementation refinement on a road map, with the results that
  survive each change and each pair of changes.
* `Scope.Provenance`: a path program over any commutative semiring; the
  provenance polynomials are universal, and consumers descend to the
  Boolean, tropical and counting images exactly when they factor through
  them.
* `Cybernetics.MindWorldBisimulation`: exact mind–world correspondences over
  a view are functional simulations; update squares are exactly the
  operationally realized correspondences.
* `Cybernetics.MindWorldApproximation`: approximate bisimulation measures
  observations, correspondence defects measure non-functoriality, update
  squares give bounded defects on process arrows, and goal weighting can
  hide a defect.
-/
