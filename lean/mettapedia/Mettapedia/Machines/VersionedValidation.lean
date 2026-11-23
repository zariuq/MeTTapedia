import Mettapedia.Machines.VersionedValidation.Clock
import Mettapedia.Machines.VersionedValidation.Versions
import Mettapedia.Machines.VersionedValidation.Granularity
import Mettapedia.Machines.VersionedValidation.PushPull
import Mettapedia.Machines.VersionedValidation.ConcurrentStamps

/-!
# Version-guarded reuse of retained decisions

One theory over the finite histories of `ReadWindowCuts`.

* `Clock`: the base: steps of a history, the one ordering law
  `sound_of_delayed_bumps` with the sample-first law as its synchronous instance
  and its necessity, and the one cost model `queryWork` with refreshing and epoch
  references.
* `Versions`: class versionings as the single-region discipline, stamps,
  soundness of reuse, the validating strategy and its exactness, the counting
  versioning, and the bridge to revision environments.
* `Granularity`: refinement of class maps never adds an alarm; the global and
  per-key extremes; the exact fast path; footprints of several regions; partial
  class maps are unsound.
* `PushPull`: push decides as pull; pull, push, the hybrid check and the
  validating strategy as instances of `queryWork`; neither push nor pull
  dominates.
* `ConcurrentStamps`: the double collect as a joint cut; the single write as the
  delayed single-region instance of the ordering law, and the necessity of
  publishing first.
-/
