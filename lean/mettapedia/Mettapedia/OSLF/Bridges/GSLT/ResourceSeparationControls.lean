import Mettapedia.OSLF.Bridges.GSLT.ResourceSeparation
import Mettapedia.GSLT.Logic.ResourceFrameControls

/-!
# Native spatial/modal frame controls

A persistent receiver supplied by the frame permits a step which cannot occur
on the message alone. Consequently the native diamond frame entailment has no
unconditional converse. The actual complete footprint, including the read
receiver, does have its expected native successor.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.GSLT.ResourceSeparationControls

open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.ResourceInteraction.Controls
open Mettapedia.GSLT.Logic.ResourceFrame
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Bridges.GSLT.ResourceSeparation

/-- The received value, as a predicate in the system's generated native logic. -/
def receivedOne : EquationPredicate persistentReceiver.theory :=
  nativePredicate persistentReceiver (fun target => target = {Res.received 1})

/-- The persistent receiver as the assertion of the frame's exact bag. -/
def receiverFrame : EquationPredicate persistentReceiver.theory :=
  nativePredicate persistentReceiver (fun target => target = {Res.receiver})

/-- There is no firing on a message with its required receiver absent. -/
theorem no_step_without_read (target : Multiset Res) :
    ¬ persistentReceiver.theory.rewrites ({Res.message 1} : Multiset Res) target := by
  rintro ⟨site, value, enabled, _⟩
  have receiverPresent : Res.receiver ∈ ({Res.message 1} : Multiset Res) :=
    Multiset.mem_of_le enabled (by simp [persistentReceiver])
  simp at receiverPresent

/-- Supplying the receiver in the frame makes the specified native successor
possible, and retains that very read resource. -/
theorem framed_native_successor :
    (semanticDiamond persistentReceiver.theory
      (nativeStar persistentReceiver receivedOne receiverFrame)).1
      (({Res.message 1} : Multiset Res) + {Res.receiver}) := by
  have enabled : persistentReceiver.Enables ({Res.message 1} + {Res.receiver})
      (takeAgain 1) := by unfold System.Enables; decide
  apply (nativeDiamond_iff persistentReceiver _ _).mpr
  refine ⟨persistentReceiver.fire ({Res.message 1} + {Res.receiver}) (takeAgain 1),
    ⟨(), takeAgain 1, enabled, rfl⟩, ?_⟩
  refine ⟨{Res.received 1}, {Res.receiver}, trivial, ?_, rfl, rfl⟩
  unfold System.fire
  decide

/-- The converse frame entailment fails: splitting off the receiver leaves a
local bag with no step at all. -/
theorem native_frame_converse_fails :
    ¬ sepConj (α := Multiset Res)
      (semanticDiamond persistentReceiver.theory receivedOne).1 receiverFrame.1
      ({Res.message 1} + {Res.receiver}) := by
  rintro ⟨owned, extension, _, split, possible, rfl⟩
  have same : owned = ({Res.message 1} : Multiset Res) := add_right_cancel split.symm
  obtain ⟨target, step, _⟩ := (nativeDiamond_iff persistentReceiver _ _).mp possible
  exact no_step_without_read target (same ▸ step)

/-- The full read-inclusive native footprint succeeds as the frame rules
predict. This uses the generated modality of the real resource GSLT. -/
theorem complete_native_footprint :
    (semanticDiamond persistentReceiver.theory
      (nativePredicate persistentReceiver
        (fun target => target = {Res.receiver, Res.received 1}))).1
      ({Res.message 1, Res.receiver} : Multiset Res) := by
  simpa [demand, persistentReceiver, takeAgain] using
    footprint_nativeDiamond persistentReceiver ⟨(), takeAgain 1⟩

end Mettapedia.OSLF.Bridges.GSLT.ResourceSeparationControls
