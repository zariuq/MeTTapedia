import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeActivation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimePrivateUpdate
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRetirement

/-!
# Reconstructing the witness after a supplied private receipt

The private endpoint inversion supplies the advanced registry. Callback and
first-field receipts retain its guarded inventory directly. A final receipt
retires only its selected occurrence and activates that call's real guard.
The supplied target remains fixed through the structural comparisons; the
source readout is unchanged and exactly one unit of private debt is spent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePrivateTransition

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Ownership RuntimeState RuntimeActors RuntimeWitness ScopedActiveFrontier NamePassingChannelRoles
open RuntimePrivateUpdate

theorem advanced_guards {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (guards : ∀ owner, SlotGuarded (registry owner)) (owner : Fin n)
    (phase : Phase) (call : Call Γ) (committed : registry owner = .pending phase call) :
    ∀ other, SlotGuarded (advance registry owner phase call other) := by
  intro other
  by_cases same : other = owner
  · subst other
    rw [advance, Function.update_self]
    have body := guards owner
    rw [committed] at body
    have original := body.pending_body
    cases phase with
    | callback | first => exact .pending _ _ original
    | second => exact .released _ original
  · rw [advance, Function.update_of_ne same]
    exact guards other

theorem advanced_live {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (live : ∀ owner, Live (registry owner)) (owner : Fin n)
    (phase : Phase) (call : Call Γ) (notLast : phase ≠ .second) :
    ∀ other, Live (advance registry owner phase call other) := by
  intro other
  by_cases same : other = owner
  · subst other
    rw [advance, Function.update_self]
    cases phase with
    | callback | first => trivial
    | second => exact False.elim (notLast rfl)
  · rw [advance, Function.update_of_ne same]
    exact live other

theorem quiet_updated {Γ : Ctx sig} {source current after : Proc Γ}
    (before : Witness source current) (owner : Fin before.n)
    (phase : Phase) (call : Call before.world)
    (committed : before.registry owner = .pending phase call) (notLast : phase ≠ .second)
    (supplied : StructuralEq after (before.scope.close ((privateScope before.n).close
      (registryTarget (advance before.registry owner phase call) (parallel before.frame))))) :
    ∃ witness : Witness source after, witness.debt + 1 = before.debt := by
  have unchanged := RuntimePrivateUpdate.source_unchanged before.registry (parallel before.frame)
    owner phase call committed
  let witness : Witness source after :=
    ⟨before.world, before.scope, before.n, advance before.registry owner phase call,
      before.frame, before.heads, advanced_live before.registry before.live owner phase call notLast,
      advanced_guards before.registry before.guards owner phase call committed,
      before.roles, unchanged.symm ▸ before.typed, unchanged.symm ▸ before.source, supplied⟩
  exact ⟨witness, remaining_decreases before.registry owner phase call committed⟩

theorem released_updated {Γ : Ctx sig} {source current after : Proc Γ}
    (before : Witness source current) (owner : Fin before.n) (call : Call before.world)
    (committed : before.registry owner = .pending .second call)
    (supplied : StructuralEq after (before.scope.close ((privateScope before.n).close
      (registryTarget (advance before.registry owner .second call) (parallel before.frame))))) :
    ∃ witness : Witness source after, witness.debt + 1 = before.debt := by
  let advanced := advance before.registry owner .second call
  let retired := Retirement.registry advanced owner call
  have selected : advanced owner = .released call := Function.update_self _ _ _
  have others : ∀ other, other ≠ owner → retired other = before.registry other := by
    intro other different
    exact (Retirement.other_retained advanced owner other call different).trans
      (Function.update_of_ne different _ _)
  have live : ∀ other, Live (retired other) := by
    intro other
    by_cases same : other = owner
    · subst other
      change Live (Retirement.registry advanced owner call owner)
      rw [Retirement.selected_retired]
      rfl
    · rw [others other same]
      exact before.live other
  have guards : ∀ other, SlotGuarded (retired other) := by
    intro other
    by_cases same : other = owner
    · subst other
      change SlotGuarded (Retirement.registry advanced owner call owner)
      rw [Retirement.selected_retired]
      exact .released _ .nil
    · rw [others other same]
      exact before.guards other
  have unchanged := RuntimePrivateUpdate.source_unchanged before.registry (parallel before.frame)
    owner .second call committed
  have releasedSource := Retirement.release_source advanced owner call (parallel before.frame) selected
  have releasedTarget := Retirement.release_target advanced owner call (parallel before.frame) selected
  have sourceEqual := before.source.trans (before.scope.congr
    (unchanged ▸ releasedSource))
  have targetEqual := supplied.trans (before.scope.congr releasedTarget)
  have joinedTyped := (Typed.structural_iff before.roles releasedSource).mp
    (unchanged.symm ▸ before.typed)
  have guarded := before.guards owner
  rw [committed] at guarded
  obtain ⟨witness, counted⟩ := RuntimeActivation.activated before.scope retired before.frame
    before.heads live guards before.roles (readback call)
    (guarded.pending_body.openPair call.first call.second) joinedTyped sourceEqual targetEqual
  refine ⟨witness, ?_⟩
  rw [counted, Retirement.release_remaining advanced owner call selected]
  exact remaining_decreases before.registry owner .second call committed

/-- The helper consumes the independently inverted actual endpoint. It
activates a body only for the real final private receipt, never for another
pending slot's already committed source readout. -/
theorem updated {Γ : Ctx sig} {source current after : Proc Γ}
    (before : Witness source current) (owner : Fin before.n)
    (phase : Phase) (call : Call before.world)
    (committed : before.registry owner = .pending phase call)
    (supplied : StructuralEq after (before.scope.close ((privateScope before.n).close
      (registryTarget (advance before.registry owner phase call) (parallel before.frame))))) :
    ∃ witness : Witness source after, witness.debt + 1 = before.debt := by
  cases phase with
  | callback => exact quiet_updated before owner .callback call committed (by decide) supplied
  | first => exact quiet_updated before owner .first call committed (by decide) supplied
  | second => exact released_updated before owner call committed supplied

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePrivateTransition
