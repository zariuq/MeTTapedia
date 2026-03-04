import Mathlib.Logic.Relation
import Mettapedia.CategoryTheory.GeneralizedOpenMaps
import Mettapedia.Logic.ModalQuantaleSemantics

/-!
# Weighted/Probabilistic Open-Map Bridge

Instantiates the generalized open-map core for quantale-labeled transition systems.
-/

namespace Mettapedia.Logic.WeightedOpenMaps

open Mettapedia.CategoryTheory.GeneralizedOpenMaps
open Mettapedia.Logic.ModalQuantaleSemantics

universe u v w

variable {Q : Type u} [CompleteLattice Q]
variable {S : Type v} {Act : Type w}

/-- Underlying weighted transition step: there exists an action with non-bottom weight. -/
def qltsStep (qlts : QLTS Q S Act) (s t : S) : Prop :=
  ∃ a : Act, qlts.trans s a t ≠ ⊥

/-- Saturated weighted step relation via reflexive-transitive closure. -/
def qltsStepStar (qlts : QLTS Q S Act) : S → S → Prop :=
  Relation.ReflTransGen (qltsStep qlts)

/-- Generic open-map kit induced by a `QLTS`. -/
def QLTSInst (qlts : QLTS Q S Act) : BisimulationKit S Act where
  step := qltsStep qlts
  stepStar := qltsStepStar qlts
  step_sub_star := by
    intro x y hxy
    exact Relation.ReflTransGen.single hxy
  observable := fun s a => ∃ t : S, qlts.trans s a t ≠ ⊥

/-- Weighted bisimilarity phrased through generalized path bisim. -/
def WeightedBisim (qlts : QLTS Q S Act) (s t : S) : Prop :=
  PathBisim (QLTSInst qlts) s t

/-- Weighted bisimilarity phrased through generalized-open-map span witness. -/
def WeightedGOpenSpanBisim (qlts : QLTS Q S Act) (s t : S) : Prop :=
  ESBisimilar (QLTSInst qlts) s t

theorem weightedBisim_iff_gopen_span
    (qlts : QLTS Q S Act) (s t : S) :
    WeightedBisim qlts s t ↔ WeightedGOpenSpanBisim qlts s t :=
  pathBisim_iff_esBisimilar (QLTSInst qlts) s t

end Mettapedia.Logic.WeightedOpenMaps
