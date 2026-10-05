import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeActors
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolEntryRoles
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRegistryReindex

/-!
# Source-derived witnesses for mixed tuple execution

The occurrence registry and idle frame are interpreted by the original
process syntax. Both supplied endpoints are compared by its structural
equations. Guards and channel roles come from the original source; the
witness contains no assumed execution reflection or scheduler contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeWitness

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Ownership RuntimeState RuntimeActors ScopedActiveFrontier NamePassingChannelRoles

inductive SlotGuarded : {Γ : Ctx sig} → Slot Γ → Prop where
  | offered {Γ} (channel first second : Name Γ) :
      SlotGuarded (.offered channel first second)
  | pending {Γ} (phase : Phase) (call : Call Γ) :
      Guarded call.body → SlotGuarded (.pending phase call)
  | released {Γ} (call : Call Γ) :
      Guarded call.body → SlotGuarded (.released call)

theorem SlotGuarded.source {Γ : Ctx sig} {slot : Slot Γ}
    (guarded : SlotGuarded slot) : Guarded slot.source := by
  cases guarded with
  | offered => exact .out2 _ _ _
  | pending _ call body | released call body => exact body.openPair call.first call.second

theorem SlotGuarded.pending_body {Γ : Ctx sig} {phase : Phase} {call : Call Γ}
    (guarded : SlotGuarded (.pending phase call)) : Guarded call.body := by
  cases guarded with
  | pending _ _ body => exact body

theorem SlotGuarded.released_body {Γ : Ctx sig} {call : Call Γ}
    (guarded : SlotGuarded (.released call)) : Guarded call.body := by
  cases guarded with
  | released _ body => exact body

theorem SlotGuarded.rename {Γ Δ : Ctx sig} {slot : Slot Γ}
    (guarded : SlotGuarded slot) (environment : Ren sig Γ Δ) :
    SlotGuarded (slot.rename environment) := by
  cases guarded with
  | offered => exact .offered _ _ _
  | pending phase call body => exact .pending phase _ (body.rename (liftRen environment [.nm, .nm]))
  | released call body => exact .released _ (body.rename (liftRen environment [.nm, .nm]))

/-- Every slot index and every idle-list occurrence is retained, including
equal copies. The source readout commits when the public receiver is selected;
pending slots retain the original guard until its actual final receipt. -/
structure Witness {Γ : Ctx sig} (source target : Proc Γ) where
  world : Ctx sig
  scope : Scope Γ world
  n : Nat
  registry : Fin n → Slot world
  frame : List (Proc world)
  heads : ∀ atom ∈ frame, IdleFrame.Head atom
  live : ∀ owner, Live (registry owner)
  guards : ∀ owner, SlotGuarded (registry owner)
  roles : Roles world
  typed : Typed roles (registrySource registry (parallel frame))
  source : StructuralEq source (scope.close (registrySource registry (parallel frame)))
  target : StructuralEq target
    (scope.close ((privateScope n).close (registryTarget registry (parallel frame))))

def Witness.debt {Γ : Ctx sig} {source target : Proc Γ}
    (witness : Witness source target) : Nat := registryRemaining witness.registry

/-- Only a supplied structural equation changes the endpoint representation. -/
def Witness.changeSource {Γ : Ctx sig} {source source' target : Proc Γ}
    (witness : Witness source target) (equal : StructuralEq source' source) :
    Witness source' target := { witness with source := equal.trans witness.source }

def Witness.changeTarget {Γ : Ctx sig} {source target target' : Proc Γ}
    (witness : Witness source target) (equal : StructuralEq target' target) :
    Witness source target' := { witness with target := equal.trans witness.target }

theorem initialized {Γ : Ctx sig} {process : Proc Γ} (guarded : Guarded process)
    (roles : Roles Γ) (typed : Typed roles process) :
    Nonempty (Witness process (lower process)) := by
  let entry := Initialization.guarded_entry guarded
  obtain ⟨opened, _, sourceTyped, _, _⟩ := EntryRoles.entry_roles entry roles typed
  refine ⟨⟨entry.world, entry.scope, entry.offers.length,
    Initialization.offeredRegistry entry.offers, entry.residual,
    IdleFrame.entry_heads entry, ?_, ?_, opened, sourceTyped, entry.source, entry.target⟩⟩
  · intro owner
    change Live (.offered _ _ _)
    trivial
  · intro owner
    exact .offered _ _ _

/-- Choosing roles selects from the independently proved source typing
and actual normalization; it does not choose a communication partner. -/
noncomputable def initial {Γ : Ctx sig} {process : Proc Γ} (guarded : Guarded process)
    (roles : Roles Γ) (typed : Typed roles process) : Witness process (lower process) :=
  Classical.choice (initialized guarded roles typed)

theorem initialized_debt_zero {Γ : Ctx sig} {process : Proc Γ}
    (guarded : Guarded process) (roles : Roles Γ) (typed : Typed roles process) :
    ∃ witness : Witness process (lower process), witness.debt = 0 := by
  let entry := Initialization.guarded_entry guarded
  obtain ⟨opened, _, sourceTyped, _, _⟩ := EntryRoles.entry_roles entry roles typed
  let witness : Witness process (lower process) :=
    ⟨entry.world, entry.scope, entry.offers.length,
      Initialization.offeredRegistry entry.offers, entry.residual,
      IdleFrame.entry_heads entry, fun _ => trivial, fun _ => .offered _ _ _,
      opened, sourceTyped, entry.source, entry.target⟩
  refine ⟨witness, ?_⟩
  change ((List.finRange entry.offers.length).map (fun _ => 0)).sum = 0
  simp

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeWitness
