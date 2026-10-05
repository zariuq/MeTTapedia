import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolCallbackReuse
import Mettapedia.OSLF.Syntax.VariableIdentity

/-!
# Full support excludes another occurrence's callback

The absence facts count the entire supplied process, including payloads and
guard bodies. A placed slot uses only its own two private positions and ambient
source names. An offered slot does not yet use even its own callback position.
These facts justify bound-callback reuse in the complete framed public reduct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.CallbackSupport

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Capabilities Ownership RuntimeState ScopedActiveFrontier

theorem sameVar_other_key_false {Γ : Ctx sig} (n : Nat) (selected other : Fin n)
    (selectedPort otherPort : Port) (different : selected ≠ other ∨ selectedPort ≠ otherPort) :
    sameVar (key (Γ := Γ) n selected selectedPort) (key n other otherPort) = false := by
  apply (sameVar_eq_false_iff _ _).mpr
  intro equal
  obtain ⟨owners, ports⟩ := key_injective n selected other selectedPort otherPort equal
  rcases different with different | different
  · exact different owners
  · exact different ports

/-- No part of another occurrence's arbitrary template can mention the
selected private key, including code below all its own binders. -/
theorem other_template_full_count_zero {Γ : Ctx sig} (n : Nat) (selected other : Fin n)
    (different : selected ≠ other) (port : Port) (template : Proc (.nm :: .nm :: Γ)) :
    countVar (key n selected port) (rename (placement n other) template) = 0 := by
  apply countVar_rename_of_miss
  intro sort name
  cases name with
  | zero => exact sameVar_other_key_false n selected other port .callback (Or.inl different)
  | succ name => cases name with
    | zero => exact sameVar_other_key_false n selected other port .session (Or.inl different)
    | succ name =>
        exact sameVar_prefix_ambient (privatePrefix n) Γ
          (privateVar n selected port) name

/-- Offered, pending and released slots all exclude another owner's callback. -/
theorem other_slot_full_count_zero {Γ : Ctx sig} (n : Nat) (selected other : Fin n)
    (different : selected ≠ other) (port : Port) (slot : Slot Γ) :
    countVar (key n selected port) (slot.placed n other) = 0 :=
  other_template_full_count_zero n selected other different port slot.template

theorem session_placement_misses_callback {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (sort : Srt) (name : Var (.nm :: Γ) sort) :
    sameVar (key n owner .callback) (placement n owner sort (Var.succ name)) = false := by
  cases name with
  | zero => exact sameVar_other_key_false n owner owner .callback .session (Or.inr (by decide))
  | succ name =>
      exact sameVar_prefix_ambient (privatePrefix n) Γ
        (privateVar n owner .callback) name

/-- An arbitrary sender remainder can mention its own session and every
source name while its reserved callback is still absent. -/
theorem unused_callback_template_full_count_zero {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (template : Proc (.nm :: Γ)) :
    countVar (key n owner .callback)
      (rename (placement n owner) (weaken (t := Srt.nm) template)) = 0 := by
  rw [weaken, rename_comp]
  exact countVar_rename_of_miss _ _ (session_placement_misses_callback n owner) template

/-- The reserved callback of the offered occurrence itself remains unused.
The sender's local input variable is a separate bound callback. -/
theorem offered_callback_full_count_zero {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (channel first second : Name Γ) :
    countVar (key n owner .callback)
      ((Slot.offered channel first second).placed n owner) = 0 :=
  unused_callback_template_full_count_zero n owner _

theorem sender_remaining_callback_full_count_zero {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (first second : Name Γ) :
    countVar (key n owner .callback)
      (rename (placement n owner) (weaken (t := Srt.nm) (sendFields first second))) = 0 :=
  unused_callback_template_full_count_zero n owner _

/-- A newly bound callback and the selected old session can both occur in
the exact receiver body without using the old reserved callback. -/
theorem fresh_session_template_full_count_zero {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (body : Proc (.nm :: .nm :: Γ)) :
    countVar (Var.succ (key n owner .callback) : Var (.nm :: World n Γ) .nm)
      (rename (liftRen (fun sort name => placement n owner sort (Var.succ name)) [.nm]) body) = 0 :=
  countVar_rename_of_miss _ _
    (sameVar_weakenVar_liftRen (S := sig) _ _
      (session_placement_misses_callback n owner) [Srt.nm]) body

theorem frame_full_count_zero {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (port : Port) (frame : Proc Γ) :
    countVar (key n owner port) (rename (ambient n) (lower frame)) = 0 :=
  ambient_has_no_private n owner port _

/-- Full support absence is retained when another binder is introduced. -/
theorem fresh_frame_full_count_zero {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (port : Port) (frame : Proc Γ) :
    countVar (Var.succ (key n owner port) : Var (.nm :: World n Γ) .nm)
      (weaken (t := Srt.nm) (rename (ambient n) (lower frame))) = 0 := by
  rw [weaken]
  exact (countVar_rename_of_reflect
    (fun _ name => Var.succ name : Ren sig (World n Γ) (.nm :: World n Γ)) (key n owner port)
    (by intro sort name; rfl) _).trans (frame_full_count_zero n owner port frame)

/-- A finite list retains all other slot occurrences, including duplicates. -/
theorem other_slots_full_count_zero {Γ : Ctx sig} (n : Nat) (selected : Fin n)
    (port : Port) (registry : Fin n → Slot Γ) (owners : List (Fin n))
    (others : ∀ owner ∈ owners, selected ≠ owner) :
    countVar (key n selected port)
      (parallel (owners.map (fun owner => (registry owner).placed n owner))) = 0 := by
  induction owners with
  | nil => rfl
  | cons owner rest ih =>
      simp only [List.map_cons, parallel, par, countVar, countVarArgs,
        weakenVar, Nat.add_zero]
      rw [other_slot_full_count_zero n selected owner
        (others owner (List.mem_cons_self ..)) port (registry owner), Nat.zero_add]
      exact ih (fun next member => others next (List.mem_cons_of_mem _ member))

theorem other_slots_frame_full_count_zero {Γ : Ctx sig} (n : Nat) (selected : Fin n)
    (port : Port) (registry : Fin n → Slot Γ) (owners : List (Fin n))
    (others : ∀ owner ∈ owners, selected ≠ owner) (frame : Proc Γ) :
    countVar (key n selected port)
      (par (parallel (owners.map (fun owner => (registry owner).placed n owner)))
        (rename (ambient n) (lower frame))) = 0 := by
  simp only [par, countVar, countVarArgs, weakenVar, Nat.add_zero]
  rw [other_slots_full_count_zero n selected port registry owners others,
    frame_full_count_zero n selected port frame, Nat.zero_add]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.CallbackSupport
