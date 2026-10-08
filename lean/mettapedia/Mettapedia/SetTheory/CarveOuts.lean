import Mettapedia.SetTheory.CarveOuts.WellFoundedBubble
import Mettapedia.SetTheory.CarveOuts.GraphValues
import Mettapedia.SetTheory.CarveOuts.HOTGCoverage
import Mettapedia.SetTheory.CarveOuts.HereditarilyFinite
import Mettapedia.SetTheory.CarveOuts.HeytingValued.Names
import Mettapedia.SetTheory.CarveOuts.HeytingValued.Points
import Mettapedia.SetTheory.CarveOuts.HeytingValued.DoubleNegation
import Mettapedia.SetTheory.CarveOuts.HeytingValued.Gunky
import Mettapedia.SetTheory.CarveOuts.HeytingValued.FreePoint
import Mettapedia.SetTheory.CarveOuts.Distinctions

/-!
# Carve-outs of the set-theoretic tops

* `WellFoundedBubble`: the bubble of any membership, induction as a theorem about it, the
  hyperset bubble as `ZFSet`, and the agreement of every view on well-founded graphs.
* `GraphValues`: the hyperset values of the ordinal three and of the nest.
* `HOTGCoverage`: the HOTG laws in `ZFSet`, with their commitments.
* `HereditarilyFinite`: the bubble's laws hold in `V_ω`, which has no closed universe.
* `HeytingValued`: sets valued in a frame; points and the principal collapse; the
  double-negation part and a constructive witness; gunky frames; a free point.
* `Distinctions`: what each carve-out keeps.
-/
