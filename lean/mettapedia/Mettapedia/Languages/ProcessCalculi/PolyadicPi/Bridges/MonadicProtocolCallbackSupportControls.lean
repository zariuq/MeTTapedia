import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolCallbackSupport

/-!
# Whole-term private callback support controls

The selected callback remains absent from another owner's pending code and
from duplicate retained occurrences. A callback hidden below an input guard
still contributes to whole-term support. A pending occurrence uses its own
callback, so the different-owner condition cannot be discarded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.CallbackSupport.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Capabilities Ownership RuntimeState ScopedActiveFrontier

abbrev context : Ctx sig := [.nm]
abbrev selected : Fin 2 := ⟨1, by decide⟩
abbrev other : Fin 2 := ⟨0, by decide⟩

def call : Call context :=
  ⟨.var .zero, .var .zero,
    inp1 (.var .zero) (out1 (.var .zero) (.var (.succ (.succ .zero))))⟩

theorem other_pending_whole_support_absent (phase : Phase) :
    countVar (key (Γ := context) 2 selected .callback)
      ((Slot.pending phase call).placed 2 other) = 0 :=
  other_slot_full_count_zero 2 selected other (by decide) .callback (.pending phase call)

def registry : Fin 2 → Slot context := fun _ => .pending .callback call

/-- Duplicate list entries remain separate occurrences in the actual term. -/
theorem duplicate_other_occurrences_absent :
    countVar (key (Γ := context) 2 selected .callback)
      (parallel ([other, other].map (fun owner => (registry owner).placed 2 owner))) = 0 := by
  apply other_slots_full_count_zero
  intro owner member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst owner
  decide

theorem offered_own_callback_absent :
    countVar (key (Γ := context) 2 selected .callback)
      ((Slot.offered (.var .zero) (.var .zero) (.var .zero)).placed 2 selected) = 0 :=
  offered_callback_full_count_zero 2 selected _ _ _

theorem sender_remainder_callback_absent :
    countVar (key (Γ := context) 2 selected .callback)
      (rename (placement 2 selected) (weaken (t := Srt.nm)
        (sendFields (.var .zero) (.var .zero)))) = 0 :=
  sender_remaining_callback_full_count_zero 2 selected _ _

def hidden : Proc (.nm :: .nm :: context) :=
  inp1 (.var (.succ .zero)) (out1 (.var .zero) (.var (.succ .zero)))

theorem own_callback_below_guard_is_counted :
    countVar (key (Γ := context) 2 selected .callback)
      (rename (placement 2 selected) hidden) = 1 := rfl

theorem other_callback_below_guard_absent :
    countVar (key (Γ := context) 2 selected .callback)
      (rename (placement 2 other) hidden) = 0 :=
  other_template_full_count_zero 2 selected other (by decide) .callback hidden

theorem own_pending_callback_is_used :
    countVar (key (Γ := context) 2 selected .callback)
      ((Slot.pending .callback call).placed 2 selected) = 2 := by
  simp only [Slot.placed, Slot.template, contents, loweredCall, call,
    lower_inp1, lower_out1]
  rfl

theorem own_pending_callback_not_absent :
    countVar (key (Γ := context) 2 selected .callback)
      ((Slot.pending .callback call).placed 2 selected) ≠ 0 := by
  rw [own_pending_callback_is_used]
  decide

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.CallbackSupport.Controls
