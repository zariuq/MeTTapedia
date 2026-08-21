import Mettapedia.GSLT.LanguageDef.CostStaticPlanParallelChildren
import Mettapedia.GSLT.LanguageDef.CostStaticPlanProducers

/-!
# Canonical alignment of static-plan abstractions

Aggregator kept at the historical module name so consumers need no change.
The content now lives in four modules, split along compilation seams:
`CostStaticPlanStopCarriers` (provenance records), `CostStaticPlanLockstep`
(the heavy mutual transport), `CostStaticPlanParallelChildren` (strict child
alignment beneath a bare parallel), and `CostStaticPlanProducers` (the public
entry points).
-/
