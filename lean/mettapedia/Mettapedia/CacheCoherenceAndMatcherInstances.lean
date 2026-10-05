import Mettapedia.GSLT.Dynamics.CacheCoherence
import Mettapedia.GSLT.Dynamics.CacheCoherenceContract
import Mettapedia.Machines.OrderedDependencyCacheKeys
import Mettapedia.Languages.MeTTa.HE.ModuleCacheKeys
import Mettapedia.Languages.MM0.ServiceInferenceCache
import Mettapedia.Computability.RegularLanguages.PrioritizedSpanFactorization

/-!
# Index: scoped cache coherence and span-aware matching

The shared cache-coherence core and its bridge to reused computed evidence;
its instances for ordered dependency stores, HE module observations and the
MM0 service's inference cache; and the factorization of prioritized,
span-aware matching through consumer letters, assertion bits and UTF-8
boundaries.
-/
