import Mettapedia.GSLT.Core.CostBoundedReachability
import Mettapedia.GSLT.Dynamics.MultiScaleExpenditure
import Mettapedia.GSLT.Causality.TraceCostValuation
import Mettapedia.Algebra.LevelSchedule
import Mettapedia.GSLT.Dynamics.CostChannelSeparation
import Mettapedia.GSLT.Dynamics.NeedCostAccounting
import Mettapedia.GSLT.Core.ResourceAwareControl
import Mettapedia.GSLT.Dynamics.ParallelExecutionAuthority
import Mettapedia.GSLT.Dynamics.ParallelFuelContractionRefund
import Mettapedia.Machines.BranchLocalNeed.CacheLaws

/-!
# The cost-and-parallelism contract, as one build target

The new laws and the existing developments they connect, imported together so
one target checks that they compose.

* ordered expenditure and budgets — `CostBoundedReachability`, with the
  multiscale expenditure grading as an instance (`MultiScaleExpenditure`);
* trace-invariant costs — `TraceCostValuation`;
* work, span and rounds — `LevelSchedule`, related to `WorkSpan` and kept apart
  from reservations, signed potential and search effort by
  `CostChannelSeparation`;
* demand and sharing — `NeedCostAccounting` over `ProofRelevantNeed`, beside
  the reference machine's cache laws;
* resource separation, observer-relative serialization, parallel admission and
  fuel leases — the existing `ResourceAwareControl`,
  `ParallelExecutionAuthority` and `ParallelFuelContractionRefund`.
-/
