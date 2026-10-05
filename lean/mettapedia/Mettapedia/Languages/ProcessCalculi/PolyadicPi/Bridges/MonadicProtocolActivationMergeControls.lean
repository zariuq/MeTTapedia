import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolActivationMerge
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRetirement

/-!
# Continuation activation and duplicate-owner retirement controls

A genuinely private binary output enters the occurrence registry when its
continuation becomes active. Existing pending calls have nonempty binary
readbacks, but remain pending; activation does not inspect their suspended
readbacks. Retiring one released call leaves another equal call's occurrence,
actual target state and remaining communication debt intact.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.ActivationMergeControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open MonadicProtocol Capabilities Ownership RuntimeState Initialization ScopedActiveFrontier

abbrev context : Ctx sig := [.nm, .nm, .nm]
def subject : Name context := .var .zero
def first : Name context := .var (.succ .zero)
def second : Name context := .var (.succ (.succ .zero))
def message : Proc context := out2 subject first second

def continuation : Proc context :=
  nu (out2 (.var .zero) (weaken first) (weaken second))
theorem continuation_guarded : Guarded continuation := .nu (.out2 _ _ _)
def entry := guarded_entry continuation_guarded

theorem actual_private_continuation_adds_one_offer : entry.offers.length = 1 := by
  change (offers (normalize (nu (out2 (.var .zero) (weaken first) (weaken second)))).atoms).length = 1
  rw [normalize_nu, normalize_out2]
  rfl

theorem actual_private_continuation_has_no_idle_frame : entry.residual = [] := by
  change frameAtoms (normalize (nu (out2 (.var .zero) (weaken first) (weaken second)))).atoms = []
  rw [normalize_nu, normalize_out2]
  rfl

def repeatedCall : Call context :=
  ⟨first, second,
    out2 (weaken (weaken subject)) (.var .zero) (.var (.succ .zero))⟩

theorem repeated_readback_is_an_actual_binary_output : readback repeatedCall = message := rfl
theorem repeated_readback_is_not_nil : readback repeatedCall ≠ nil := by
  rw [repeated_readback_is_an_actual_binary_output]
  intro same
  cases same

def pendingRegistry : Fin 2 → Slot context := fun _ => .pending .callback repeatedCall

/-- The old calls' source readouts contain binary outputs. They are still
literal pending slots after activation; only the new continuation is entered. -/
theorem old_pending_calls_remain_pending (owner : Fin 2) :
    ActivationMerge.expanded pendingRegistry entry (Fin.natAdd entry.offers.length owner) =
      .pending .callback (repeatedCall.rename entry.scope.inclusion) :=
  ActivationMerge.activation_old pendingRegistry entry owner

theorem old_owners_are_injective :
    Function.Injective (Fin.natAdd entry.offers.length : Fin 2 → Fin (entry.offers.length + 2)) :=
  ActivationMerge.old_owners_retained _ _

theorem both_pending_readbacks_are_binary (owner : Fin 2) : (pendingRegistry owner).source = message :=
  repeated_readback_is_an_actual_binary_output

theorem pending_debt_is_six : registryRemaining pendingRegistry = 6 := rfl

theorem activation_does_not_charge_pending_calls :
    registryRemaining (ActivationMerge.expanded pendingRegistry entry) = 6 :=
  (ActivationMerge.activation_remaining pendingRegistry entry).trans pending_debt_is_six

theorem actual_activation_source_equation :
    StructuralEq (par (registrySource pendingRegistry (parallel [])) continuation)
      (entry.scope.close
        (registrySource (ActivationMerge.expanded pendingRegistry entry)
          (parallel (ActivationMerge.residual entry [])))) :=
  ActivationMerge.activation_source pendingRegistry [] entry

theorem actual_activation_closed_target_equation :
    StructuralEq
      (par ((privateScope 2).close (registryTarget pendingRegistry (parallel []))) (lower continuation))
      (entry.scope.close ((privateScope (entry.offers.length + 2)).close
        (registryTarget (ActivationMerge.expanded pendingRegistry entry)
          (parallel (ActivationMerge.residual entry []))))) :=
  ActivationMerge.activation_target pendingRegistry [] entry

def finishedOwner : Fin 2 := ⟨0, by decide⟩
def pendingOwner : Fin 2 := ⟨1, by decide⟩
def beforeRetirement : Fin 2 → Slot context :=
  Fin.cases (.released repeatedCall) (fun _ => .pending .callback repeatedCall)
def afterRetirement : Fin 2 → Slot context :=
  Retirement.registry beforeRetirement finishedOwner repeatedCall

theorem equal_calls_have_distinct_owners : pendingOwner ≠ finishedOwner := by
  intro same
  have positions := congrArg Fin.val same
  cases positions

theorem retirement_keeps_the_other_equal_call :
    afterRetirement pendingOwner = .pending .callback repeatedCall :=
  Retirement.other_retained beforeRetirement finishedOwner pendingOwner repeatedCall
    equal_calls_have_distinct_owners

theorem retirement_debt_is_three :
    registryRemaining beforeRetirement = 3 ∧ registryRemaining afterRetirement = 3 := by
  have before : registryRemaining beforeRetirement = 3 := rfl
  exact ⟨before, (Retirement.release_remaining beforeRetirement finishedOwner repeatedCall rfl).trans before⟩

theorem actual_retirement_source_equation :
    StructuralEq (registrySource beforeRetirement (nil : Proc context))
      (par (registrySource afterRetirement nil) message) := by
  simpa only [afterRetirement, repeated_readback_is_an_actual_binary_output] using
    Retirement.release_source beforeRetirement finishedOwner repeatedCall nil rfl

theorem actual_retirement_closed_target_equation :
    StructuralEq ((privateScope 2).close (registryTarget beforeRetirement (nil : Proc context)))
      (par ((privateScope 2).close (registryTarget afterRetirement nil)) (lower message)) := by
  simpa only [afterRetirement, repeated_readback_is_an_actual_binary_output] using
    Retirement.release_target beforeRetirement finishedOwner repeatedCall nil rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.ActivationMergeControls
