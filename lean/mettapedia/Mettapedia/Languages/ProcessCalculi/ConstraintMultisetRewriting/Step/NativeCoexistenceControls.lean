import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeCoexistence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceSystemsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextInterpretation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextResultControls

/-! # Native interpretation fibres can be empty, while scoped coexistence remains available -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.NativeCoexistenceControls

open Coexistence.Controls (singleCell no_common_native_frame)
open Coexistence.SystemsControls (disconnected)

theorem no_native_pair_for_two_cells : ¬Nonempty (singleCell.NativePair 0 1) := by
  rintro ⟨pair⟩
  have count := congrArg Finset.card pair.present
  change ({pair.state} : Finset Nat).card = (({0} : Finset Nat) ∪ {1}).card at count
  norm_num at count

theorem no_native_pair_across_disconnected_frames : ¬Nonempty (disconnected.NativePair false true) := by
  rintro ⟨pair⟩
  exact no_common_native_frame ⟨disconnected.frame pair.state, ⟨pair.leftMap⟩, ⟨pair.rightMap⟩⟩

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Helpers.ContextResultControls (placed)

theorem contextual_scopes_realize_shared_interface :
    (Frames.contextual Helpers.Consumer.tiny).Equivalent placed.state.knowledge
      (EffectCore.Systems.realize Helpers.scopedHelperEffect
        [(false, Helpers.Consumer.start), (true, Helpers.ContextResultControls.context)]
        placed.nativePair.scopedPlacement).equations := placed.nativePair.scoped_snapshot.1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.NativeCoexistenceControls
