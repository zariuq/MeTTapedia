import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeState

/-!
# Reindexing retained tuple occurrences across source scopes

The original calls, offered messages and protocol templates all move along
the supplied ambient name map. Their private callback and session positions
remain fixed. The same law applies to the actual placed registry and its
frame, while each phase retains its remaining communication debt.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Capabilities Ownership RuntimeState ScopedActiveFrontier

theorem Call.rename_id {Γ : Ctx sig} (call : Call Γ) :
    call.rename (fun _ name => name) = call := by
  cases call
  dsimp only [Call.rename]
  rw [Mettapedia.OSLF.Binding.liftRen_id (S := sig),
    Mettapedia.OSLF.Binding.rename_id (S := sig),
    Mettapedia.OSLF.Binding.rename_id (S := sig),
    Mettapedia.OSLF.Binding.rename_id (S := sig)]

theorem Call.rename_comp {Γ Δ Θ : Ctx sig} (call : Call Γ)
    (first : Ren sig Γ Δ) (second : Ren sig Δ Θ) :
    (call.rename first).rename second = call.rename (fun sort name => second sort (first sort name)) := by
  cases call
  dsimp only [Call.rename]
  rw [Mettapedia.OSLF.Binding.rename_comp (S := sig),
    Mettapedia.OSLF.Binding.rename_comp (S := sig),
    Mettapedia.OSLF.Binding.rename_comp (S := sig),
    ← Mettapedia.OSLF.Binding.liftRen_comp (S := sig)]

theorem readback_rename {Γ Δ : Ctx sig} (call : Call Γ) (environment : Ren sig Γ Δ) :
    rename environment (readback call) = readback (call.rename environment) :=
  rename_openPair environment call.body call.first call.second

theorem loweredCall_rename {Γ Δ : Ctx sig} (call : Call Γ) (environment : Ren sig Γ Δ) :
    (loweredCall call).rename environment = loweredCall (call.rename environment) := by
  cases call
  simp only [loweredCall, Call.rename, lower_rename]

/-- The received first field and suspended second-field binder commute
with reindexing all original source names. -/
theorem secondBody_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (first : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
    rename (liftRen (liftRen environment [.nm, .nm]) [.nm]) (secondBody first body) =
      secondBody (rename environment first) (rename (liftRen environment [.nm, .nm]) body) := by
  simp only [secondBody, rename_bind, bind_rename, rename_comp]
  congr 1
  funext sort name
  cases first with
  | op operator _ => cases operator
  | var first =>
      cases name with
      | zero => rfl
      | succ name => cases name <;> rfl

private theorem prefix_fixed {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) :
    ∀ (binders : Ctx sig) {sort : Srt} (name : Var binders sort),
      liftRen environment binders sort (injPrefix (Γ := Γ) binders name) =
        injPrefix (Γ := Δ) binders name
  | [], _, name => nomatch name
  | _ :: _rest, _, .zero => rfl
  | _ :: rest, _, .succ name => congrArg Var.succ (prefix_fixed environment rest name)

/-- Occurrence owners and their two allocated capabilities are unchanged
when only the original source context is reindexed. -/
theorem key_reindex {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (n : Nat) (owner : Fin n) (port : Port) :
    liftRen environment (privatePrefix n) .nm (key (Γ := Γ) n owner port) =
      key (Γ := Δ) n owner port :=
  prefix_fixed environment _ _

theorem ambient_reindex {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (n : Nat) (sort : Srt) (name : Var Γ sort) :
    liftRen environment (privatePrefix n) sort (ambient n sort name) =
      ambient n sort (environment sort name) :=
  liftRen_weakenVar environment name _

theorem placement_reindex {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (n : Nat) (owner : Fin n) (sort : Srt) (name : Var (Srt.nm :: Srt.nm :: Γ) sort) :
    liftRen environment (privatePrefix n) sort (placement n owner sort name) =
      placement n owner sort (liftRen environment [.nm, .nm] sort name) := by
  cases name with
  | zero => exact key_reindex environment n owner .callback
  | succ name => cases name with
    | zero => exact key_reindex environment n owner .session
    | succ name => exact ambient_reindex environment n _ name

theorem placed_template_reindex {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (n : Nat) (owner : Fin n) (template : Proc (.nm :: .nm :: Γ)) :
    rename (liftRen environment (privatePrefix n)) (rename (placement n owner) template) =
      rename (placement n owner) (rename (liftRen environment [.nm, .nm]) template) := by
  simp only [rename_comp]
  congr 1
  funext sort name
  exact placement_reindex environment n owner sort name

theorem ambient_term_reindex {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (n : Nat) (process : Proc Γ) :
    rename (liftRen environment (privatePrefix n)) (rename (ambient n) process) =
      rename (ambient n) (rename environment process) := by
  simp only [rename_comp]
  congr 1
  funext sort name
  exact ambient_reindex environment n sort name

/-- All three real private phases reindex their original tuple and guard;
the two allocated private binders retain their identities. -/
theorem contents_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (phase : Phase) (call : Call Γ) :
    rename (liftRen environment [.nm, .nm]) (contents phase call) =
      contents phase (call.rename environment) := by
  cases phase with
  | callback => exact callback_contents_natural environment call
  | first =>
      simp only [contents, Call.rename, rename_par, rename_out1]
      rw [receiveFields_rename]
      rw [← liftRen_two environment Srt.nm Srt.nm,
        rename_weaken (S := sig) (fresh := Srt.nm) (liftRen environment [.nm]),
        rename_weaken (S := sig) (fresh := Srt.nm) environment,
        rename_weaken (S := sig) (fresh := Srt.nm) (liftRen environment [.nm]),
        rename_weaken (S := sig) (fresh := Srt.nm) environment]
      rfl
  | second =>
      simp only [contents, Call.rename, rename_par, rename_out1, rename_inp1]
      rw [secondBody_rename]
      rw [← liftRen_two environment Srt.nm Srt.nm,
        rename_weaken (S := sig) (fresh := Srt.nm) (liftRen environment [.nm]),
        rename_weaken (S := sig) (fresh := Srt.nm) environment]
      rfl

namespace RuntimeState

def Slot.rename {Γ Δ : Ctx sig} (slot : Slot Γ) (environment : Ren sig Γ Δ) : Slot Δ :=
  match slot with
  | .offered channel first second =>
      .offered (Mettapedia.OSLF.Binding.rename environment channel)
        (Mettapedia.OSLF.Binding.rename environment first)
        (Mettapedia.OSLF.Binding.rename environment second)
  | .pending phase call => .pending phase (call.rename environment)
  | .released call => .released (call.rename environment)

theorem Slot.rename_id {Γ : Ctx sig} (slot : Slot Γ) :
    slot.rename (fun _ name => name) = slot := by
  cases slot with
  | offered =>
      dsimp only [Slot.rename]
      rw [Mettapedia.OSLF.Binding.rename_id (S := sig),
        Mettapedia.OSLF.Binding.rename_id (S := sig),
        Mettapedia.OSLF.Binding.rename_id (S := sig)]
  | pending | released => simp only [Slot.rename, Call.rename_id]

theorem Slot.rename_comp {Γ Δ Θ : Ctx sig} (slot : Slot Γ)
    (first : Ren sig Γ Δ) (second : Ren sig Δ Θ) :
    (slot.rename first).rename second = slot.rename (fun sort name => second sort (first sort name)) := by
  cases slot with
  | offered =>
      dsimp only [Slot.rename]
      rw [Mettapedia.OSLF.Binding.rename_comp (S := sig),
        Mettapedia.OSLF.Binding.rename_comp (S := sig),
        Mettapedia.OSLF.Binding.rename_comp (S := sig)]
  | pending | released => simp only [Slot.rename, Call.rename_comp]

theorem Slot.source_rename {Γ Δ : Ctx sig} (slot : Slot Γ) (environment : Ren sig Γ Δ) :
    Mettapedia.OSLF.Binding.rename environment slot.source = (slot.rename environment).source := by
  cases slot with
  | offered => exact rename_out2 environment _ _ _
  | pending | released => exact readback_rename _ environment

theorem Slot.template_rename {Γ Δ : Ctx sig} (slot : Slot Γ) (environment : Ren sig Γ Δ) :
    Mettapedia.OSLF.Binding.rename (liftRen environment [.nm, .nm]) slot.template =
      (slot.rename environment).template := by
  cases slot with
  | offered channel first second =>
      simp only [Slot.template, Slot.rename]
      rw [← liftRen_two environment Srt.nm Srt.nm,
        rename_weaken (S := sig) (fresh := Srt.nm) (liftRen environment [.nm]),
        rename_par, rename_out1,
        rename_weaken (S := sig) (fresh := Srt.nm) environment, sendFields_rename]
      rfl
  | pending phase call =>
      change Mettapedia.OSLF.Binding.rename (liftRen environment [.nm, .nm])
        (contents phase (loweredCall call)) = contents phase (loweredCall (call.rename environment))
      rw [contents_rename, loweredCall_rename]
  | released call =>
      simp only [Slot.template, Slot.rename]
      rw [← liftRen_two environment Srt.nm Srt.nm,
        rename_weaken (S := sig) (fresh := Srt.nm) (liftRen environment [.nm]),
        rename_weaken (S := sig) (fresh := Srt.nm) environment,
        lower_rename, readback_rename]

theorem Slot.closed_rename {Γ Δ : Ctx sig} (slot : Slot Γ) (environment : Ren sig Γ Δ) :
    Mettapedia.OSLF.Binding.rename environment slot.closed = (slot.rename environment).closed := by
  simp only [Slot.closed, rename_nu]
  rw [liftRen_two, Slot.template_rename]

theorem Slot.placed_rename {Γ Δ : Ctx sig} (slot : Slot Γ) (environment : Ren sig Γ Δ)
    (n : Nat) (owner : Fin n) :
    Mettapedia.OSLF.Binding.rename (liftRen environment (privatePrefix n)) (slot.placed n owner) =
      (slot.rename environment).placed n owner := by
  rw [Slot.placed, placed_template_reindex, Slot.template_rename]
  rfl

theorem Slot.remaining_rename {Γ Δ : Ctx sig} (slot : Slot Γ) (environment : Ren sig Γ Δ) :
    (slot.rename environment).remaining = slot.remaining := by
  cases slot <;> rfl

theorem registrySource_rename {Γ Δ : Ctx sig} {n : Nat}
    (registry : Fin n → Slot Γ) (frame : Proc Γ) (environment : Ren sig Γ Δ) :
    rename environment (registrySource registry frame) =
      registrySource (fun owner => (registry owner).rename environment) (rename environment frame) := by
  simp only [registrySource, rename_par, parallel_rename, List.map_map, Function.comp_def,
    Slot.source_rename]

theorem registryTarget_rename {Γ Δ : Ctx sig} {n : Nat}
    (registry : Fin n → Slot Γ) (frame : Proc Γ) (environment : Ren sig Γ Δ) :
    rename (liftRen environment (privatePrefix n)) (registryTarget registry frame) =
      registryTarget (fun owner => (registry owner).rename environment) (rename environment frame) := by
  simp only [registryTarget, rename_par, parallel_rename, List.map_map, Function.comp_def]
  rw [ambient_term_reindex, lower_rename]
  apply congrArg (fun values => par (parallel values)
    (rename (ambient n) (lower (rename environment frame))))
  apply List.map_congr_left
  intro owner _
  exact (registry owner).placed_rename environment n owner

theorem registryRemaining_rename {Γ Δ : Ctx sig} {n : Nat}
    (registry : Fin n → Slot Γ) (environment : Ren sig Γ Δ) :
    registryRemaining (fun owner => (registry owner).rename environment) = registryRemaining registry := by
  simp only [registryRemaining, Slot.remaining_rename]

/-- Closing the same allocated private positions commutes literally with
the ambient name map, before taking any structural quotient. -/
theorem privateScope_close_reindex {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) :
    ∀ (n : Nat) (body : Proc (World n Γ)),
      rename environment ((privateScope (Γ := Γ) n).close body) =
        (privateScope (Γ := Δ) n).close
          (rename (liftRen environment (privatePrefix n)) body)
  | 0, _ => rfl
  | n + 1, body => by
      rw [privateScope, Scope.close_append, privateScope, Scope.close_append]
      change rename environment ((privateScope n).close (nu (nu body))) =
        (privateScope n).close (nu (nu (rename (liftRen environment (privatePrefix (n + 1))) body)))
      rw [privateScope_close_reindex environment n]
      dsimp only [World, privatePrefix] at body ⊢
      rw [rename_nu, rename_nu]
      have same : liftRen (liftRen (liftRen environment (privatePrefix n)) [.nm]) [.nm] =
          liftRen environment (.nm :: .nm :: privatePrefix n) := by
        funext sort name
        cases name with
        | zero => rfl
        | succ name => cases name <;> rfl
      rw [same]

theorem registryClosed_rename {Γ Δ : Ctx sig} {n : Nat}
    (registry : Fin n → Slot Γ) (frame : Proc Γ) (environment : Ren sig Γ Δ) :
    rename environment ((privateScope n).close (registryTarget registry frame)) =
      (privateScope n).close (registryTarget
        (fun owner => (registry owner).rename environment) (rename environment frame)) := by
  rw [privateScope_close_reindex, registryTarget_rename]

theorem next_rename {Γ Δ : Ctx sig} (phase : Phase) (call : Call Γ)
    (environment : Ren sig Γ Δ) :
    (next phase call).rename environment = next phase (call.rename environment) := by
  cases phase <;> rfl

end RuntimeState

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol
