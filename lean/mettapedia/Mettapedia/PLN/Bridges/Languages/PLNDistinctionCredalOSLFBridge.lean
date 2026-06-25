import Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge
import Mettapedia.OSLF.Framework.DistinctionGraph

/-!
# OSLF Distinction-Credal Bridge

This file specializes the generic setoid-based distinction/credal bridge to
OSLF observational indistinguishability. The point is deliberately modest:
when an observer still identifies two distinct patterns, the singleton query
for one pattern can retain genuine credal width; when the observer-equivalence
class collapses to a singleton, that same query becomes point-valued.
-/

namespace Mettapedia.PLN.Bridges.Languages.PLNDistinctionCredalOSLFBridge

open Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge
open Mettapedia.OSLF.Framework.DistinctionGraph
open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-- If the observer still identifies a distinct pattern `q` with `p`, then the
singleton query for `p` has genuine credal width in the observation-induced
credal set. -/
theorem indistObs_indicatorGamble_has_strict_width
    [Fintype Pat] [DecidableEq Pat]
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem} {p q : Pat}
    (hIndist : indistObs R I q p) (hNe : q ≠ p) :
    lowerProb
        (observationCredalSet (indistObs_setoid R I) p)
        (indicatorGamble p) <
      upperProb
        (observationCredalSet (indistObs_setoid R I) p)
        (indicatorGamble p) :=
  observationCredalSet_indicatorGamble_has_strict_width_of_related_ne
    (r := indistObs_setoid R I) hIndist hNe

/-- If the observer-equivalence class of `p` is already singleton, the
singleton query for `p` collapses to a point-valued envelope. -/
theorem indistObs_indicatorGamble_collapses_of_class_subsingleton
    [Fintype Pat] [DecidableEq Pat]
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem} (p : Pat)
    (hClass : ∀ q : Pat, indistObs R I q p → q = p) :
    lowerProb
        (observationCredalSet (indistObs_setoid R I) p)
        (indicatorGamble p) =
      upperProb
        (observationCredalSet (indistObs_setoid R I) p)
        (indicatorGamble p) :=
  observationCredalSet_indicatorGamble_collapses_of_class_subsingleton
    (r := indistObs_setoid R I) p hClass

end Mettapedia.PLN.Bridges.Languages.PLNDistinctionCredalOSLFBridge
