import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoSpatial

/-!
# Spatial compiler controls

An actual sender and receiver admit a cut by their individual component
predicates. Two equal senders remain two occurrences. A dropped-name frame
distinguishes source and target wands, while both observations use the same
canonical resource algebra.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoSpatialControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoSpatial
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.GSLT.RhoBagReactiveSystem
open Mettapedia.OSLF.StructuralModal.SeparatingConjunction

def sender : RhoSpatial.Atom := ⟨.output "mailbox" "message", trivial⟩
def receiver : RhoSpatial.Atom := ⟨.input "mailbox" "received" .nil, trivial⟩

/-- The actual compilation admits the sender/receiver resource partition. -/
theorem sender_receiver_cut (namespaceName valueName : String) :
    SepConj Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence .hashBag
      (fun term => components term = {atomImage namespaceName valueName sender})
      (fun term => components term = {atomImage namespaceName valueName receiver})
      (encode (RhoEndpoint.assemble [sender.1, receiver.1]) namespaceName valueName) := by
  apply (encode_assemble_cut_iff [sender, receiver] namespaceName valueName
    (fun bag => bag = {atomImage namespaceName valueName sender})
    (fun bag => bag = {atomImage namespaceName valueName receiver})).mpr
  exact ⟨{sender}, {receiver}, trivial, rfl, rfl, rfl⟩

/-- Equal senders are retained as two resources by the existing compiler. -/
theorem equal_senders_keep_multiplicity (namespaceName valueName : String) :
    (components (RhoEndpoint.networkPattern [sender.1, sender.1]
      namespaceName valueName)).card = 2 :=
  compiledBag_card [sender, sender] namespaceName valueName

def droppedFrame : Multiset Pattern := {.apply "PDrop" [.fvar "ambient"]}

private theorem droppedFrame_not_image (namespaceName valueName : String)
    (source : Multiset RhoSpatial.Atom) :
    resourceMap namespaceName valueName source ≠ droppedFrame := by
  intro equal
  have member : .apply "PDrop" [.fvar "ambient"] ∈
      source.map (atomImage namespaceName valueName) := by
    change .apply "PDrop" [.fvar "ambient"] ∈ resourceMap namespaceName valueName source
    rw [equal]
    exact Multiset.mem_singleton_self _
  obtain ⟨atom, _, image⟩ := Multiset.mem_map.mp member
  exact atomImage_ne_drop atom namespaceName valueName "ambient" image

/-- The source wand sees only translated communication extensions, and
therefore does not see the dropped-name counterexample. -/
theorem source_dropped_wand (namespaceName valueName : String) :
    wand ((resourceMap namespaceName valueName).pull (fun bag => bag = droppedFrame))
      ((resourceMap namespaceName valueName).pull (fun _ => False))
      (0 : Multiset RhoSpatial.Atom) := by
  intro extension _ image
  exact droppedFrame_not_image namespaceName valueName extension image

/-- The target wand quantifies the additional rho frame and is false. -/
theorem target_dropped_wand_fails :
    ¬ wand (fun bag : Multiset Pattern => bag = droppedFrame) (fun _ => False) 0 := by
  intro holds
  exact holds droppedFrame trivial rfl

/-- A concrete source/target observation difference, using the empty source
and a compatible actual rho component. -/
theorem dropped_frame_discriminates (namespaceName valueName : String) :
    wand ((resourceMap namespaceName valueName).pull (fun bag => bag = droppedFrame))
      ((resourceMap namespaceName valueName).pull (fun _ => False))
      (0 : Multiset RhoSpatial.Atom) ∧
    ¬ (resourceMap namespaceName valueName).pull
      (wand (fun bag => bag = droppedFrame) (fun _ => False))
      (0 : Multiset RhoSpatial.Atom) := by
  refine ⟨source_dropped_wand namespaceName valueName, ?_⟩
  change ¬ wand (fun bag => bag = droppedFrame) (fun _ => False)
    (resourceMap namespaceName valueName 0)
  rw [(resourceMap namespaceName valueName).map_zero]
  exact target_dropped_wand_fails

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoSpatialControls
