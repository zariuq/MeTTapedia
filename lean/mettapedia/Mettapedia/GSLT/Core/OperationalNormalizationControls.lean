import Mettapedia.GSLT.Core.OperationalNormalization
import Mettapedia.GSLT.Core.GSLTConstructions

/-!
# Empty implementation blocks can hide a real infinite execution

The existing tick system has a genuine always-enabled transition. Its
finite prefixes can all be fused to the empty path of a discrete target.
That comparison meets finite operational correspondence while changing
normalization. Finite correspondence therefore needs a further progress
condition to reflect normalization; positive blocks supply such a condition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalNormalizationControls

open Mettapedia.GSLT

def target : GSLT := GSLT.discrete Unit

/-- A deliberately empty realization of the existing clock, used only to
separate finite correspondence from preservation of infinite execution. -/
def zeroBlockTicks : OperationalCorrespondence GSLT.tickSystem target where
  related := Eq
  readStep := by
    intro origin current next related impossible
    exact False.elim impossible
  forward := by
    intro origin after current related firing
    exact ⟨current, ⟨.refl current⟩, @Subsingleton.elim Unit _ after current⟩

theorem target_accessible : Acc (fun next state => target.Step state next) () :=
  .intro () (fun _ impossible => False.elim impossible)

theorem clock_not_accessible :
    ¬ Acc (fun next state => GSLT.tickSystem.Step state next) () :=
  not_acc_iff_exists_descending_chain.mpr ⟨fun _ => (), rfl, fun _ => trivial⟩

/-- Finite correspondence by itself does not reflect strong normalization. -/
theorem empty_blocks_change_normalization :
    zeroBlockTicks.related () () ∧
      Acc (fun next state => target.Step state next) () ∧
      ¬ Acc (fun next state => GSLT.tickSystem.Step state next) () :=
  ⟨rfl, target_accessible, clock_not_accessible⟩

/-- The positive-block hypothesis cannot be supplied for this genuine
finite correspondence, even though every source step has an empty image. -/
theorem positive_blocks_unavailable :
    ¬ (∀ {origin after : GSLT.tickSystem.Term} {current : target.Term},
      zeroBlockTicks.related origin current → GSLT.tickSystem.Step origin after →
      ∃ final, ∃ path : ExecutionPath target current final,
        0 < path.length ∧ zeroBlockTicks.related after final) := by
  intro positive
  exact clock_not_accessible
    (zeroBlockTicks.normalization_reflected positive rfl target_accessible)

end Mettapedia.GSLT.IndexedOperational.OperationalNormalizationControls
