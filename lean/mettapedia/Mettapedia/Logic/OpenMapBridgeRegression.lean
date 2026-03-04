import Mettapedia.Logic.WeightedOpenMaps
import Mettapedia.Logic.OSLFOpenMapBridge

/-!
# Logic Open-Map Bridge Regression

Small theorem-level checks for weighted and OSLF bridge exports.
-/

namespace Mettapedia.Logic.OpenMapBridgeRegression

open Mettapedia.CategoryTheory.GeneralizedOpenMaps
open Mettapedia.Logic.WeightedOpenMaps
open Mettapedia.Logic.OSLFOpenMapBridge

universe u v w

variable {Q : Type u} [CompleteLattice Q]
variable {S : Type v} {Act : Type w}

theorem weighted_equiv_regression
    (qlts : Mettapedia.Logic.ModalQuantaleSemantics.QLTS Q S Act) (s t : S) :
    WeightedBisim qlts s t ↔ WeightedGOpenSpanBisim qlts s t := by
  simpa using weightedBisim_iff_gopen_span qlts s t

abbrev Pat := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

theorem pathBisim_to_bisimilar_regression
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem}
    {p q : Pat} :
    PathBisim (OSLFInst R I) p q → Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar R p q :=
  pathBisim_implies_bisimilar

theorem fullOpenWitness_obsEq_regression
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem}
    (w : FullOpenWitness R I) {p q : Pat} (hpq : w.rel p q) :
    Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq R I p q :=
  fullOpenWitness_implies_obsEq w hpq

theorem fullOpenWitness_not_distinguished_regression
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem}
    (w : FullOpenWitness R I) {p q : Pat} (hpq : w.rel p q) :
    ¬ Mettapedia.Logic.OSLFDistinctionGraph.distinguished R I p q :=
  fullOpenWitness_not_distinguished w hpq

end Mettapedia.Logic.OpenMapBridgeRegression
