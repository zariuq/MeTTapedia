import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeControlChanges
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradeControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeAccumulatorBounds
import Mettapedia.GSLT.Core.KeyOrder
import Mettapedia.GSLT.Core.PortfolioController
import Mettapedia.GSLT.Core.SourceExecutionCosts
import Mettapedia.GSLT.Core.BoundedSelection
import Mettapedia.GSLT.Core.WeightOrderedSelection
import Mettapedia.GSLT.Core.PriorityKeyOrder
import Mettapedia.Algorithms.PositivePathSearch
import Mettapedia.GSLT.Parsing.ClassAwarePackedForestKBestControls
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingBatch
import Mettapedia.Languages.ProcessCalculi.MORK.MM2GivenClause
import Mettapedia.Languages.ProcessCalculi.MORK.MM2OccurrenceSupport
import Mettapedia.Languages.ProcessCalculi.MORK.MM2QueueFairness

/-!
# Native priority and demand integration

This entry point assembles authored Need computation, captured advisory
grades, demand and joint selection, owned revision, exact k-best extraction,
protected scheduling and the independently specified MM2 execution bridge.
Each theorem keeps its fragment, finiteness, cost and observation assumptions.

The executable reference and the native runtime are distinct realizations.
Runtime differential qualification does not establish a C refinement theorem.
Surface weight syntax and physical parallel execution are not fixed here.
-/
