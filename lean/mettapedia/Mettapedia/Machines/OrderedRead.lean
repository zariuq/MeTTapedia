import Mettapedia.Machines.OrderedRead.Sequences
import Mettapedia.Machines.OrderedRead.BinarySeek
import Mettapedia.Machines.OrderedRead.RankTournamentCosts
import Mettapedia.Machines.OrderedRead.OrderedDemand
import Mettapedia.Machines.OrderedRead.DenseRankScatter

/-!
# Declared-order reads and demand-sensitive access paths

Lazy reads preserve captured occurrence sequences, least-first reads sort the
matched bag, and nested fixed reads have lexicographic occurrence order.
The cached rank tournament supplies an executable ordered provider with
exact residuals, linear rank acquisition and logarithmic pop charges.

Ordered rent-or-buy prepays complete ordered acquisition. Incremental
alternatives instead have a resumable prefix-race bound; ignoring deferred
heap delivery has a counterexample family. The comparison-tree lower bound
applies to total comparison work, not to every reply. Dense supplied ranks
support a different, linear direct-addressing algorithm.

An implementation must supply its term-view order, matching, captured-view,
rank-service and memory adapters. Candidate delivery costs are not claimed
answer-delay bounds when semantic filtering can reject candidates.
-/
