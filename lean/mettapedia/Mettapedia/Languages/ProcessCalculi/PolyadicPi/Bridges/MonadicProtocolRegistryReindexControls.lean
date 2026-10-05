import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRegistryReindex

/-!
# Ambient aliases and retained private tuple owners

An ambient map may identify two public names. Even then the allocated
private capabilities remain distinct and the original tuple continuation
and phase debt are retained. Such a name map need not reflect source
communications: identifying different public subjects can enable a firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RegistryReindexControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Capabilities Ownership RuntimeState

abbrev Public : Ctx sig := [.nm, .nm]
abbrev Aliased : Ctx sig := [.nm]

def identify : Ren sig Public Aliased := fun _ name => by
  cases name with
  | zero => exact .zero
  | succ name => cases name with
    | zero => exact .zero
    | succ impossible => cases impossible

def originalCall : Call Public :=
  ⟨.var .zero, .var (.succ .zero), out1 (.var .zero) (.var (.succ .zero))⟩

theorem ordered_fields_become_equal :
    (originalCall.rename identify).first = (originalCall.rename identify).second := rfl

theorem original_fields_are_distinct : originalCall.first ≠ originalCall.second := by
  intro same
  cases Term.var.inj same

theorem payload_and_original_guard_retained :
    rename identify (readback originalCall) =
      readback (originalCall.rename identify) :=
  readback_rename originalCall identify

theorem two_pending_occurrences_keep_their_keys (first second : Fin 2)
    (firstPort secondPort : Port) :
    liftRen identify (privatePrefix 2) .nm (key (Γ := Public) 2 first firstPort) =
        liftRen identify (privatePrefix 2) .nm (key (Γ := Public) 2 second secondPort) ↔
      first = second ∧ firstPort = secondPort := by
  rw [key_reindex, key_reindex]
  constructor
  · exact key_injective 2 first second firstPort secondPort
  · rintro ⟨rfl, rfl⟩
    rfl

theorem private_subjects_do_not_alias_public (owner : Fin 2) (port : Port)
    (publicName : Var Public .nm) :
    liftRen identify (privatePrefix 2) .nm (key (Γ := Public) 2 owner port) ≠
      liftRen identify (privatePrefix 2) .nm (ambient 2 .nm publicName) := by
  rw [key_reindex, ambient_reindex]
  exact key_ne_ambient 2 owner port (identify .nm publicName)

theorem pending_field_phase_debt_retained :
    ((Slot.pending .first originalCall).rename identify).remaining = 2 := rfl

def mismatched : Proc Public :=
  par (out1 (.var .zero) (.var .zero)) (inp1 (.var (.succ .zero)) nil)

theorem original_has_no_raw_step {target : Proc Public} : ¬ Step mismatched target := by
  apply mismatched_unary_channel_no_step
  intro same
  cases Term.var.inj same

theorem identifying_public_names_enables_a_real_step :
    Step (rename identify mismatched) nil := by
  exact .comm1 (.var .zero) (.var .zero) nil

theorem this_reindexing_does_not_reflect_raw_steps :
    ¬ (∀ (source target : Proc Public),
      Step (rename identify source) (rename identify target) → Step source target) := by
  intro reflection
  exact original_has_no_raw_step
    (reflection mismatched nil identifying_public_names_enables_a_real_step)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RegistryReindexControls
