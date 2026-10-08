import Mettapedia.SetTheory.CarveOuts.Sites.Bridge
import Mettapedia.SetTheory.CarveOuts.Sites.GSets
import Mettapedia.SetTheory.CarveOuts.Sites.ProductSite
import Mettapedia.SetTheory.CarveOuts.Sites.SiteProjections
import Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps

/-!
# A site-based top: contexts and regions of perspectives

* `Bridge`: the truth values of contextual forcing are cosieves; over a preorder of stages they
  are the frame `Persistent P`; the reading by reachable stages breaks for parallel arrows and
  for a non-identity endomorphism.
* `GSets`: sets and `G`-sets have the same truth values and different objects; the frame
  reading forgets the action.
* `ProductSite`: Kripke–Joyal forcing on contexts times the regions of a frame, its
  persistence, locality and soundness, and its frame reading at a context.
* `SiteProjections`: the two projections, to contextual forcing and to Heyting-valued names;
  covers and excluded middle on Cantor space.
* `SmallMaps`: the basic axioms on a class of small maps, which the final coalgebra of the
  power-class functor needs of that class; those that hold on presheaves over the Cantor
  product site.
-/
