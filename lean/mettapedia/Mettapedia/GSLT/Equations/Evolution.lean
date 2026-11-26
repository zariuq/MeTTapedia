import Mettapedia.GSLT.Equations.CallabilityGrowth
import Mettapedia.GSLT.Equations.SelectedEffects
import Mettapedia.GSLT.Equations.OccurrenceReadouts

/-! # Changing equation views

The three layers here are independent: reachability of callable heads as
declarations grow, compatibility of entry selection with later effects,
and exact refresh of a scalar readout of raw occurrences. No implementation
of a lock, epoch counter, or physical index is part of these statements.
-/
