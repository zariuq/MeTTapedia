import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.FamilyInformationControls

/-!
# Actual packet admission and the native output-shape licence

The positive has an unresolved shared capture and a private activation local.
The malformed control changes only the original rule's output list. Its
packet is still admitted, whereas the native firing is refused. Thus native
output alignment is a necessary external formation licence for this prepared
one-match comparison; it is not inferred from packet admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketStepControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidualExample (tiny bit)
open FamilyInformationControls (state)
open NativePacketStep

def good : LiveFiring state := FamilyInformationControls.maker 0 false

abbrev actualNative := native (S := tiny) (O := Nat) (Γ := []) (sort := ())

theorem good_realized : good.toNative.Realized := FamilyInformationControls.maker_realized 0 false

theorem good_shapes : actualNative.Shapes good.toNative := ((native_admits_iff (S := tiny) good.toNative).mp good_realized).1

abbrev compiledStep (f : LiveFiring state) :=
  RuleSyntax.step (RuleSyntax.OneFrame.frames (packetAction (S := tiny) (O := Nat) (Γ := []) (sort := ())))
    (Ports Nat) (RuleSyntax.OneFrame.ext (packetAction (S := tiny) (O := Nat) (Γ := []) (sort := ()))) (program f 1)

theorem good_admitted : (compiledStep good).Admits (s := source good 0 1) (firing good 1) :=
  (unguarded_admission_iff good (by decide : (0 : Nat) ≠ 1) good_shapes rfl rfl).mpr good_realized

theorem actual_physical_result :
    ((firing good 1).result (RuleSyntax.OneFrame.frames
      (packetAction (S := tiny) (O := Nat) (Γ := []) (sort := ()))) (source good 0 1)).present =
      insert (.inr ()) ((actualNative.result good.toNative good_realized).state.present.image Sum.inl) :=
  result_present good 0 1 good_realized

theorem actual_output_closure :
    ((firing good 1).result (RuleSyntax.OneFrame.frames
      (packetAction (S := tiny) (O := Nat) (Γ := []) (sort := ()))) (source good 0 1)).label (.inl 0) =
      outputRow good 1 0 := result_output good 0 1 0 (by simp [good,FamilyInformationControls.maker])

def malformed : LiveFiring state := { good with rule := { good.rule with produce := [] } }

theorem malformed_packet_still_admitted :
    (compiledStep malformed).Admits (s := source malformed 0 1) (firing malformed 1) := by
  change (compiledStep good).Admits (s := source good 0 1) (firing good 1)
  exact good_admitted

theorem malformed_native_refused : ¬ malformed.toNative.Realized := by
  intro accepted
  have outputs := ((native_admits_iff (S := tiny) malformed.toNative).mp accepted).1.2.2.2.2
  change [bit _ false] = [] at outputs
  cases outputs

theorem malformed_shapes_fail : ¬ actualNative.Shapes malformed.toNative := by
  intro shapes
  have outputs := shapes.2.2.2.2
  change [bit _ false] = [] at outputs
  cases outputs

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketStepControls
