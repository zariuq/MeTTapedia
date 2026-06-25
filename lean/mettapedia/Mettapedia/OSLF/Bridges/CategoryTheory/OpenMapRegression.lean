import Mettapedia.CategoryTheory.GeneralizedOpenMaps.Weighted
import Mettapedia.OSLF.Bridges.CategoryTheory.OpenMap

/-!
# OSLF Open-Map Bridge Regression

Small theorem-level checks for weighted and OSLF bridge exports.
-/

namespace Mettapedia.OSLF.Bridges.CategoryTheory.OpenMapRegression

open Mettapedia.CategoryTheory.GeneralizedOpenMaps
open Mettapedia.CategoryTheory.GeneralizedOpenMaps.Weighted
open Mettapedia.OSLF.Bridges.CategoryTheory.OpenMap

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
    PathBisim (OSLFInst R I) p q → Mettapedia.OSLF.Framework.KSUnificationSketch.Bisimilar R p q :=
  pathBisim_implies_bisimilar

theorem fullOpenWitness_obsEq_regression
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem}
    (w : FullOpenWitness R I) {p q : Pat} (hpq : w.rel p q) :
    Mettapedia.OSLF.Framework.KSUnificationSketch.OSLFObsEq R I p q :=
  fullOpenWitness_implies_obsEq w hpq

theorem fullOpenWitness_not_distinguished_regression
    {R : Pat → Pat → Prop} {I : Mettapedia.OSLF.Formula.AtomSem}
    (w : FullOpenWitness R I) {p q : Pat} (hpq : w.rel p q) :
    ¬ Mettapedia.OSLF.Framework.DistinctionGraph.distinguished R I p q :=
  fullOpenWitness_not_distinguished w hpq

end Mettapedia.OSLF.Bridges.CategoryTheory.OpenMapRegression
