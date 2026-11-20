import Mettapedia.GSLT.Core.OccurrenceObservationGrowth

/-!
# Transporting occurrence consumption and its residual frame

Preserving the selected count establishes take admission. Preserving the
physical update additionally requires the selected image to stay apart from
the residual image. The separation condition below is necessary and
sufficient for finite-set consumption to commute with transport.

No global injectivity is imposed. World-local injectivity supplies separation,
and the count theorem needs injectivity only on the selection. Labels and
regions keep their independent interpretation map. Complete bag observations
and commits with makes or exact predicate queries need their additional laws.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OccurrenceObservationGrowth

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionTakes

universe uO uP uT uU

variable {O : Type uO} {P : Type uP} {T : Type uT} {U : Type uU}
variable [DecidableEq O] [DecidableEq P]

/-- Consumption commutes with a map exactly when no selected image also
represents a surviving source occurrence. -/
theorem image_remove_iff_separates (world chosen : Finset O) (map : O → P) :
    (world \ chosen).image map = world.image map \ chosen.image map ↔
      Disjoint ((world \ chosen).image map) (chosen.image map) := by
  constructor
  · intro commutes
    apply Finset.disjoint_left.mpr
    intro target residual selected
    rw [commutes] at residual
    exact (Finset.mem_sdiff.mp residual).2 selected
  · intro separates
    apply Finset.Subset.antisymm
    · intro target member
      obtain ⟨source, residual, rfl⟩ := Finset.mem_image.mp member
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_image.mpr ⟨source, (Finset.mem_sdiff.mp residual).1, rfl⟩,
          fun selected => Finset.disjoint_left.mp separates member selected⟩
    · intro target member
      obtain ⟨present, notSelected⟩ := Finset.mem_sdiff.mp member
      obtain ⟨source, inWorld, rfl⟩ := Finset.mem_image.mp present
      refine Finset.mem_image.mpr ⟨source, Finset.mem_sdiff.mpr ⟨inWorld, ?_⟩, rfl⟩
      intro selected
      exact notSelected (Finset.mem_image.mpr ⟨source, selected, rfl⟩)

/-- Faithfulness on this world supplies the residual separation. Values
outside the world remain unconstrained. -/
theorem separates_of_world_faithful {world chosen : Finset O} {map : O → P}
    (within : chosen ⊆ world) (faithful : Set.InjOn map (world : Set O)) :
    Disjoint ((world \ chosen).image map) (chosen.image map) := by
  apply Finset.disjoint_left.mpr
  intro target residual selected
  obtain ⟨left, surviving, sameLeft⟩ := Finset.mem_image.mp residual
  obtain ⟨right, taken, sameRight⟩ := Finset.mem_image.mp selected
  have same := faithful (Finset.mem_sdiff.mp surviving).1 (within taken)
    (sameLeft.trans sameRight.symm)
  exact (Finset.mem_sdiff.mp surviving).2 (same ▸ taken)

/-- The actual take-only commit has both its admitted target selection and
its commuting physical update when these two independent obligations hold. -/
theorem take_admission_and_effects
    {label : O → T} {targetLabel : P → U} {world chosen : Finset O}
    {region : T → Bool} {targetRegion : U → Bool} {lo : Nat} {hi : Option Nat}
    (takes : TakesBetween label world region lo hi chosen) (map : O → P)
    (faithful : Set.InjOn map (chosen : Set O))
    (regions : ∀ occurrence ∈ chosen,
      targetRegion (targetLabel (map occurrence)) = region (label occurrence))
    (separates : Disjoint ((world \ chosen).image map) (chosen.image map)) :
    TakesBetween targetLabel (world.image map) targetRegion lo hi (chosen.image map) ∧
      (fire world (takeOf (T := T) chosen)).image map =
        fire (world.image map) (takeOf (T := U) (chosen.image map)) := by
  refine ⟨takesBetween_image takes map faithful regions, ?_⟩
  simpa only [fire_takeOf] using (image_remove_iff_separates world chosen map).2 separates

#print axioms image_remove_iff_separates
#print axioms separates_of_world_faithful
#print axioms take_admission_and_effects

end Mettapedia.GSLT.OccurrenceObservationGrowth
