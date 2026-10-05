import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeWitness
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolActivationMerge

/-!
# Runtime metadata after a real continuation is released

Only the actually activated body is normalized. Its new offers are appended
to the retained registry; pending readouts of other calls stay suspended.
Both endpoint equations, the opened channel roles, literal frame occurrences,
and all old occurrence indices are carried through the new source telescope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeActivation

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Ownership RuntimeState RuntimeActors RuntimeWitness ScopedActiveFrontier NamePassingChannelRoles

theorem live_rename {Γ Δ : Ctx sig} {slot : Slot Γ} (live : Live slot)
    (environment : Ren sig Γ Δ) : Live (slot.rename environment) := by
  cases slot with
  | offered | pending => trivial
  | released call =>
      change readback (call.rename environment) = nil
      rw [← readback_rename, live]
      rfl

theorem expanded_live {Γ : Ctx sig} {n : Nat} {body : Proc Γ}
    (registry : Fin n → Slot Γ) (entry : Initialization.Entry body)
    (live : ∀ owner, Live (registry owner)) :
    ∀ owner, Live (ActivationMerge.expanded registry entry owner) := by
  intro owner
  induction owner using Fin.addCases with
  | left owner =>
      rw [ActivationMerge.expanded, ActivationMerge.append_first]
      trivial
  | right owner =>
      rw [ActivationMerge.activation_old]
      exact live_rename (live owner) entry.scope.inclusion

theorem expanded_guards {Γ : Ctx sig} {n : Nat} {body : Proc Γ}
    (registry : Fin n → Slot Γ) (entry : Initialization.Entry body)
    (guards : ∀ owner, SlotGuarded (registry owner)) :
    ∀ owner, SlotGuarded (ActivationMerge.expanded registry entry owner) := by
  intro owner
  induction owner using Fin.addCases with
  | left owner =>
      rw [ActivationMerge.expanded, ActivationMerge.append_first]
      exact .offered _ _ _
  | right owner =>
      rw [ActivationMerge.activation_old]
      exact (guards owner).rename entry.scope.inclusion

theorem residual_heads {Γ : Ctx sig} {body : Proc Γ} (entry : Initialization.Entry body)
    (frame : List (Proc Γ)) (heads : ∀ atom ∈ frame, IdleFrame.Head atom) :
    ∀ atom ∈ ActivationMerge.residual entry frame, IdleFrame.Head atom := by
  intro atom member
  rcases List.mem_append.mp member with fresh | retained
  · exact IdleFrame.entry_heads entry atom fresh
  · obtain ⟨old, oldMember, same⟩ := List.mem_map.mp retained
    subst atom
    exact (heads old oldMember).rename entry.scope.inclusion

/-- Rebuilding the canonical inventory uses the independently proved
activation equations and source typing. No runtime firing is assumed here. -/
theorem activated {Γ Δ : Ctx sig} {source target : Proc Γ} (scope : Scope Γ Δ)
    {n : Nat} (registry : Fin n → Slot Δ) (frame : List (Proc Δ))
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    (live : ∀ owner, Live (registry owner))
    (guards : ∀ owner, SlotGuarded (registry owner))
    (roles : Roles Δ) (body : Proc Δ) (guarded : Guarded body)
    (typed : Typed roles (par (registrySource registry (parallel frame)) body))
    (sourceEqual : StructuralEq source
      (scope.close (par (registrySource registry (parallel frame)) body)))
    (targetEqual : StructuralEq target
      (scope.close (par ((privateScope n).close (registryTarget registry (parallel frame))) (lower body)))) :
    ∃ after : Witness source target, after.debt = registryRemaining registry := by
  let entry := Initialization.guarded_entry guarded
  have sourceBody := ActivationMerge.activation_source registry frame entry
  have targetBody := ActivationMerge.activation_target registry frame entry
  have bodyTyped := (Typed.structural_iff roles sourceBody).mp typed
  obtain ⟨opened, _, openedTyped⟩ := EntryRoles.scope_opening entry.scope _ roles bodyTyped
  have sourceFinal := sourceEqual.trans (scope.congr sourceBody)
  have targetFinal := targetEqual.trans (scope.congr targetBody)
  rw [← Scope.close_append] at sourceFinal targetFinal
  let after : Witness source target :=
    ⟨entry.world, scope.append entry.scope, entry.offers.length + n,
      ActivationMerge.expanded registry entry, ActivationMerge.residual entry frame,
      residual_heads entry frame heads, expanded_live registry entry live,
      expanded_guards registry entry guards, opened, openedTyped, sourceFinal, targetFinal⟩
  exact ⟨after, ActivationMerge.activation_remaining registry entry⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeActivation
