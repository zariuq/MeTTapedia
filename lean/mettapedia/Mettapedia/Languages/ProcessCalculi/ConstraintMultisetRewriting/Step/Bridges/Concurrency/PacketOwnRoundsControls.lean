import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.PacketOwnRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketRoundsControls

/-!
# Actual symbolic schema families exercise the own-bag comparison

The two admitted members read the same generative row, retain its latent
equation and share unresolved captured names. Tying the private body to a
captured name instead leaves each member admitted alone but refuses the
actual joint own bag. The positive bag yields actual native runs in every
order, with exact event count and selections.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketOwnRounds.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open RuleSyntax RuleSyntax.JointFirings
open NativeResidualExample (tiny)
open NativePacketRoundsControls (members state reader_shapes)

private abbrev action := NativePacketStep.packetAction (S := tiny) (O := Nat) (Γ := []) (sort := ())

theorem generative_own_bag :
    (bagOf action (NativePacketRounds.memberList (members false))).AdmitsOwn
      (OneFrame.frames action) (NativePacketRounds.source (members false)) :=
  (own_iff_round (members false)).mpr NativePacketRoundsControls.open_round

theorem generative_output_licence (index : Fin (members false).length) :
    StepWeb.Rounds.KeepsLabels action (NativePacketRounds.label (members false))
      (NativePacketRounds.member (members false) index) :=
  keeps_of_own (members false) generative_own_bag index

theorem tied_own_bag_refused :
    ¬ (bagOf action (NativePacketRounds.memberList (members true))).AdmitsOwn
      (OneFrame.frames action) (NativePacketRounds.source (members true)) :=
  fun own => NativePacketRoundsControls.tied_no_round ((own_iff_round (members true)).mp own)

theorem every_order_of_actual_own {order : List (LiveFiring (state false))}
    (permutes : order.Perm (members false)) :
    ∃ last, ∃ witness : NativeRoundExecution.Witness (state false) order last,
      witness.toRun.last = last ∧ witness.toRun.word.length = 2 ∧
        witness.toRun.word.map (fun event => event.2.selection) = order.map (fun event => event.selection) :=
  native_every_order_of_own (members false) (by simp [members]) (reader_shapes false)
    (fun index => by fin_cases index <;> rfl) (fun index => by fin_cases index <;> rfl)
    generative_own_bag permutes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketOwnRounds.Controls
