import Mettapedia.GSLT.Core.OccurrenceObservationEffects
import Mettapedia.GSLT.Core.OccurrenceObservationGrowthControls

/-!
# A preserved selection count and a lost residual occurrence

Collapsing two source identities preserves the admission of a singleton
selection but erases its surviving frame. A map injective on the observed
world transports admission and firing, even though it identifies other values.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OccurrenceObservationGrowth.Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionTakes

def smallWorld : Finset Nat := {0, 1}
def selected : Finset Nat := {0}

theorem singleton_take : TakesBetween label smallWorld region 1 (some 1) selected := by
  refine ⟨?_, by decide, ?_⟩
  · simp [smallWorld, selected, regionOf, region]
  · intro h same
    have : h = 1 := Option.some.inj same.symm
    subst h
    decide

theorem collapse_faithful_on_selection : Set.InjOn collapse (selected : Set Nat) := by
  intro first inFirst second inSecond _
  exact (Finset.mem_singleton.mp inFirst).trans (Finset.mem_singleton.mp inSecond).symm

theorem collapsed_singleton_admitted :
    TakesBetween label (smallWorld.image collapse) region 1 (some 1) (selected.image collapse) :=
  takesBetween_image singleton_take collapse collapse_faithful_on_selection (fun _ _ => rfl)

theorem collapsed_frame_not_separate :
    ¬ Disjoint ((smallWorld \ selected).image collapse) (selected.image collapse) := by
  intro apart
  exact Finset.disjoint_left.mp apart
    (Finset.mem_image.mpr ⟨1, by decide, rfl⟩)
    (Finset.mem_image.mpr ⟨0, by decide, rfl⟩)

/-- Count admission by itself does not provide a commuting firing. -/
theorem collapsed_firing_disagrees :
    (fire smallWorld (takeOf (T := Unit) selected)).image collapse ≠
      fire (smallWorld.image collapse) (takeOf (T := Unit) (selected.image collapse)) := by
  intro commutes
  apply collapsed_frame_not_separate
  apply (image_remove_iff_separates smallWorld selected collapse).1
  simpa only [fire_takeOf] using commutes

def localRename (occurrence : Nat) : Nat := if occurrence = 0 then 10 else 11

theorem rename_world_faithful : Set.InjOn localRename (smallWorld : Set Nat) := by
  intro first inFirst second inSecond same
  have casesFirst : first = 0 ∨ first = 1 := by simpa [smallWorld] using inFirst
  have casesSecond : second = 0 ∨ second = 1 := by simpa [smallWorld] using inSecond
  rcases casesFirst with rfl | rfl <;> rcases casesSecond with rfl | rfl <;>
    simp_all [localRename]

theorem rename_not_globally_injective : ¬ Function.Injective localRename := by
  intro faithful
  have same : (1 : Nat) = 2 := faithful (by decide)
  exact (by decide : (1 : Nat) ≠ 2) same

/-- World-local faithfulness suffices; no restriction is imposed on the
map's collisions outside the observed world. -/
theorem local_rename_transports :
    TakesBetween label (smallWorld.image localRename) region 1 (some 1) (selected.image localRename) ∧
      (fire smallWorld (takeOf (T := Unit) selected)).image localRename =
        fire (smallWorld.image localRename) (takeOf (T := Unit) (selected.image localRename)) := by
  have within : selected ⊆ smallWorld := by simp [selected, smallWorld]
  exact take_admission_and_effects singleton_take localRename
    (rename_world_faithful.mono within) (fun _ _ => rfl)
    (separates_of_world_faithful within rename_world_faithful)

#print axioms collapsed_singleton_admitted
#print axioms collapsed_firing_disagrees
#print axioms rename_not_globally_injective
#print axioms local_rename_transports

end Mettapedia.GSLT.OccurrenceObservationGrowth.Controls
