import Mettapedia.GSLT.Logic.SaturatedRelativeBisimilarity
import Mettapedia.GSLT.Logic.SaturatedRelativeBisimilarityControls
import Mettapedia.GSLT.Logic.ObserverDetermination
import Mettapedia.GSLT.Logic.TypedObservationRelation
import Mettapedia.GSLT.Logic.ProbeDial
import Mettapedia.GSLT.Logic.ObserverBubble
import Mettapedia.GSLT.GraphTheory.BudgetedBetaObserver
import Mettapedia.GSLT.GraphTheory.BetaEtaConfluence
import Mettapedia.GSLT.GraphTheory.BudgetedBetaEtaObserver
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannelCalculus
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannelDetermination
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannelBubbles
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PayloadQuoteBoundary

/-!
# Observer-indexed equivalence

* `SaturatedRelativeBisimilarity`: the saturated equivalence of an admissible
  class of contexts; congruence for the class without relative pushouts,
  antitonicity in the class, and the coarsest-bisimulation-congruence
  characterisation; the contextual variant; least-enabler bisimilarity is
  contained in the saturated equivalence when it is a congruence.
* `SaturatedRelativeBisimilarityControls`: the saturated equivalence is not
  contained in least-enabler bisimilarity; the contextual variant can be
  strictly coarser; preservation of a relation is of mixed variance and
  determination is not monotone.
* `ObserverDetermination`: the class of contexts preserving an equivalence,
  the two-step determination from mandatory interaction contexts as a fixed
  point and as the largest class with its equivalence, and the criterion for
  conservative and strict extensions of an observer class.
* `TypedObservationRelation`: observation relations at higher types,
  admissible operations, and the inadmissibility of quotation, with the pair
  that witnesses it when quotation absorbs drops.
* `ProbeDial`: probe contexts adjoined to an observer class, the monotone
  dial, and the separation of two inert constants by a probe.
* `ObserverBubble`: bubbles (observer class, commitments, verdicts), decision
  on a fragment as a restriction of a strong relation, budgeted normal-form
  observers, and class observations.
* `BudgetedBetaObserver`: β-conversion decided on a normalising fragment by
  budgeted normalisation, with a budgeted verdict and its controls.
* `BetaEtaConfluence`: βη-reduction is Church–Rosser, by Hindley and Rosen.
* `BudgetedBetaEtaObserver`: βη-conversion decided on a normalising fragment
  by budgeted β-normalisation followed by η-normalisation; on `λx. y x` against
  `y` the β-observer refutes and the βη-observer establishes.
* `QuotedChannelCalculus`, `QuotedChannelDetermination`,
  `QuotedChannelBubbles`: a quoted-channel calculus in which output payloads
  are delayed quotes, the observer class determined by parallel interaction,
  and sealed and open bubbles over it.
* `PayloadQuoteBoundary`: the payload position of the rho quote-free class is
  a delayed quote, checked at the rule level.
-/
