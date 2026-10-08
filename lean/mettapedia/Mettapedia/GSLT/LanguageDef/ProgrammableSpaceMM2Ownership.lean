import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorControls
import Mettapedia.GSLT.Logic.ProgrammableSpaceMM2KeyReadings
import Mettapedia.Languages.ProcessCalculi.MORK.SupportedExecErasure

/-!
# Logical support and an agenda-owned directive

A selected MM2 instruction can leave the physical live store while the
agenda retains ownership of it. Reinserting that retained atom recovers
the logical support exactly when its key was present before selection.
Consequently private logical stuttering does not imply unchanged physical
live storage. These are explicit observations of the source checkpoint,
not a verification of the native selection/capture/retry implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Ownership

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open ProgrammableSpaceMM2RowMajorWrites (support)

structure StoreView where
  live : List Atom
  owned : Option Atom

def StoreView.reconstruct (view : StoreView) : List Atom :=
  match view.owned with
  | none => view.live
  | some atom => morkInsertSupport view.live atom

def take (space : List Atom) (selected : Atom) : StoreView :=
  ⟨morkEraseSupport space selected, some selected⟩

/-- Reconstruction preserves support exactly when the selected key existed.
Literal representatives and list positions are not reconstructed by this law. -/
theorem reconstruction_iff_present (space : List Atom) (selected : Atom) :
    support (take space selected).reconstruct = support space ↔
      morkSupportKey selected ∈ support space := by
  change support (morkInsertSupport (morkEraseSupport space selected) selected) = _ ↔ _
  rw [ProgrammableSpaceMM2RowMajorWrites.support_insert,
    ProgrammableSpaceMM2RowMajorWrites.support_remove]
  constructor
  · intro same
    rw [← same]
    exact Finset.mem_insert_self _ _
  · intro member
    exact Finset.insert_erase member

theorem taken_key_is_not_live (space : List Atom) (selected : Atom) :
    morkSupportKey selected ∉ support (take space selected).live := by
  change morkSupportKey selected ∉ support (morkEraseSupport space selected)
  rw [ProgrammableSpaceMM2RowMajorWrites.support_remove]
  simp

theorem physical_support_changes (space : List Atom) (selected : Atom)
    (present : morkSupportKey selected ∈ support space) :
    support (take space selected).live ≠ support space := by
  intro same
  exact taken_key_is_not_live space selected (same.symm ▸ present)

theorem selected_atom_present (space : List Atom) (directive : SourceExecFact)
    (selected : MM2MatchingBatch.SelectedFor .leaveInert space directive) :
    directive.atom ∈ space :=
  sourceExecFact_atom_mem_of_mem_supported (selectNextScheduled_mem selected)

theorem selected_reconstruction (space : List Atom) (directive : SourceExecFact)
    (selected : MM2MatchingBatch.SelectedFor .leaveInert space directive) :
    support (take space directive.atom).reconstruct = support space := by
  apply (reconstruction_iff_present space directive.atom).mpr
  exact List.mem_toFinset.mpr (List.mem_map.mpr
    ⟨directive.atom, selected_atom_present space directive selected, rfl⟩)

def observe : ProgrammableSpaceMM2RowMajorResumable.Residual → StoreView
  | .matching checkpoint => take checkpoint.before checkpoint.request.directive.atom
  | .committed receipt => ⟨ProgrammableSpaceMM2RowMajor.after receipt, none⟩

theorem matching_reconstruction
    (checkpoint : ProgrammableSpaceMM2RowMajorResumable.Checkpoint)
    (selected : MM2MatchingBatch.SelectedFor .leaveInert
      checkpoint.before checkpoint.request.directive) :
    support (observe (.matching checkpoint)).reconstruct = support checkpoint.before :=
  selected_reconstruction checkpoint.before checkpoint.request.directive selected

theorem private_step_retains_logical_support
    {space target : List Atom}
    {before after : ProgrammableSpaceMM2RowMajorResumable.Residual}
    {receipt : ProgrammableSpaceMM2RowMajorResumable.Receipt}
    (step : ProgrammableSpaceMM2RowMajorResumable.Advance .leaveInert
      space before receipt target after)
    (privateStep : receipt.publication = none) :
    support (observe before).reconstruct = support space ∧
      support (observe after).reconstruct = support space := by
  cases step with
  | pause checkpoint grant spent packet selected paused =>
      exact ⟨matching_reconstruction checkpoint selected,
        matching_reconstruction (checkpoint.afterPause grant spent packet paused) selected⟩
  | commit => cases privateStep

theorem selected_material_reconstruction (space : List Atom) (directive : SourceExecFact)
    (selected : MM2MatchingBatch.SelectedFor .leaveInert space directive) :
    Mettapedia.GSLT.Logic.ProgrammableSpaceMM2KeyReadings.keySupport
        (take space directive.atom).reconstruct =
      Mettapedia.GSLT.Logic.ProgrammableSpaceMM2KeyReadings.keySupport space :=
  (Mettapedia.GSLT.Logic.ProgrammableSpaceMM2KeyReadings.keySupport_eq_iff_support _ _).mpr
    (selected_reconstruction space directive selected)

namespace Controls
open ProgrammableSpaceMM2RowMajorControls (source request checkpoint10 nativeAfter)

theorem actual_owned_view :
    (observe (.matching checkpoint10)).live =
      ProgrammableSpaceMM2RowMajorControls.facts ∧
    (observe (.matching checkpoint10)).owned = some request.directive.atom := by
  decide +kernel

theorem actual_reconstruction :
    support (observe (.matching checkpoint10)).reconstruct = support source :=
  matching_reconstruction checkpoint10 ProgrammableSpaceMM2RowMajorControls.selected

theorem actual_live_support_is_different :
    support (observe (.matching checkpoint10)).live ≠ support source := by
  apply physical_support_changes source request.directive.atom
  exact List.mem_toFinset.mpr (List.mem_map.mpr
    ⟨request.directive.atom,
      selected_atom_present source request.directive ProgrammableSpaceMM2RowMajorControls.selected,
      rfl⟩)

theorem actual_private_reconstruction :
    support (observe (.matching ProgrammableSpaceMM2RowMajorControls.start)).reconstruct =
      support source ∧
    support (observe (.matching checkpoint10)).reconstruct = support source :=
  private_step_retains_logical_support
    ProgrammableSpaceMM2RowMajorControls.actual_private_step rfl

theorem actual_publication_releases_owned_directive :
    (observe (.committed ⟨request, source, ProgrammableSpaceMM2RowMajorControls.actualRows⟩)).live =
      nativeAfter ∧
    (observe (.committed ⟨request, source, ProgrammableSpaceMM2RowMajorControls.actualRows⟩)).owned =
      none :=
  ⟨ProgrammableSpaceMM2RowMajorControls.native_finalization, rfl⟩

end Controls
end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Ownership
