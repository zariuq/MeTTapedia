import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolInitialization
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles

/-!
# Channel roles at source-derived protocol entry

Opening the actual normalized restriction telescope recovers role assignments
for its private names while preserving every ambient role. The source equation
then supplies typing for each offered output and every residual occurrence.
The roles concern the original unary/binary source; the private unary protocol
has its own communication phases and is not assigned these public arities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.EntryRoles

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingChannelRoles ScopedActiveFrontier Initialization RuntimeState

/-- All ambient names retain their roles after the physical telescope opens.
Roles of its actual private names are obtained from the typing derivation. -/
def PreservesScope {Γ Δ : Ctx sig} (scope : Scope Γ Δ)
    (original : Roles Γ) (opened : Roles Δ) : Prop :=
  ∀ name, opened (scope.inclusion _ name) = original name

/-- Scope opening inverts the existing restriction typing constructor,
without choosing a role for a private name independently of its body. -/
theorem scope_opening : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ)
    (body : Proc Δ) (original : Roles Γ),
    Typed original (scope.close body) →
      ∃ opened : Roles Δ, PreservesScope scope original opened ∧ Typed opened body
  | _, _, .nil, body, original, typed => ⟨original, fun _ => rfl, typed⟩
  | _, _, .bind rest, body, original, typed => by
      cases typed with
      | nu fresh bodyTyped =>
          obtain ⟨opened, preserved, typed⟩ := scope_opening rest body
            (extendRole fresh original) bodyTyped
          exact ⟨opened, fun name => preserved (.succ name), typed⟩

/-- Conversely, the same opened roles close to the original ambient judgment.
No private assignment or field order is discarded during this reconstruction. -/
theorem scope_closing : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ)
    (body : Proc Δ) (original : Roles Γ) (opened : Roles Δ),
    PreservesScope scope original opened → Typed opened body →
      Typed original (scope.close body)
  | _, _, .nil, body, original, opened, preserved, typed => by
      have same : opened = original := funext preserved
      exact same ▸ typed
  | _, _, .bind rest, body, original, opened, preserved, typed => by
      let middle : Roles _ := fun name => opened (rest.inclusion _ name)
      have restTyped := scope_closing rest body middle opened (fun _ => rfl) typed
      have rolesEqual : middle = extendRole (middle .zero) original := by
        funext name
        cases name with
        | zero => rfl
        | succ old => exact preserved old
      exact .nu (middle .zero) (rolesEqual ▸ restTyped)

theorem scope_typing_iff {Γ Δ : Ctx sig} (scope : Scope Γ Δ)
    (body : Proc Δ) (original : Roles Γ) :
    Typed original (scope.close body) ↔
      ∃ opened : Roles Δ, PreservesScope scope original opened ∧ Typed opened body :=
  ⟨scope_opening scope body original,
    fun ⟨opened, preserved, typed⟩ => scope_closing scope body original opened preserved typed⟩

/-- Parallel typing is about every supplied list occurrence. Repeated equal
atoms remain present in the list used by protocol initialization. -/
theorem parallel_typing_iff {Γ : Ctx sig} (roles : Roles Γ) (atoms : List (Proc Γ)) :
    Typed roles (parallel atoms) ↔ ∀ atom ∈ atoms, Typed roles atom := by
  induction atoms with
  | nil =>
      constructor
      · intro _ atom member
        exact False.elim (List.not_mem_nil member)
      · intro _
        exact .nil _
  | cons first rest ih =>
      constructor
      · intro typed
        cases typed with
        | par head tail =>
            intro atom member
            rcases List.mem_cons.mp member with equal | member
            · exact equal ▸ head
            · exact ih.mp tail atom member
      · intro each
        exact .par (each first List.mem_cons_self)
          (ih.mpr (fun atom member => each atom (List.mem_cons_of_mem _ member)))

/-- Registry-source typing characterizes each retained slot and the idle
source frame; it never types the private unary handshake as a binary call. -/
theorem registry_source_typing_iff {Γ : Ctx sig} {n : Nat}
    (roles : Roles Γ) (registry : Fin n → Slot Γ) (frame : Proc Γ) :
    Typed roles (registrySource registry frame) ↔
      (∀ owner, Typed roles (registry owner).source) ∧ Typed roles frame := by
  rw [registrySource, Typed.par_iff, parallel_typing_iff]
  constructor
  · rintro ⟨slots, frame⟩
    exact ⟨fun owner => slots _ (List.mem_map.mpr ⟨owner, List.mem_finRange owner, rfl⟩), frame⟩
  · rintro ⟨slots, frame⟩
    refine ⟨?_, frame⟩
    intro atom member
    obtain ⟨owner, _, equal⟩ := List.mem_map.mp member
    exact equal ▸ slots owner

/-- The role witness for an actual entry is derived from the original
source equation and the existing static typing invariance theorem. -/
theorem entry_roles {Γ : Ctx sig} {process : Proc Γ} (entry : Entry process)
    (original : Roles Γ) (typed : Typed original process) :
    ∃ opened : Roles entry.world,
      PreservesScope entry.scope original opened ∧
      Typed opened (registrySource (offeredRegistry entry.offers) (parallel entry.residual)) ∧
      (∀ owner, Typed opened (offeredRegistry entry.offers owner).source) ∧
      (∀ atom ∈ entry.residual, Typed opened atom) := by
  have closedTyped := (Typed.structural_iff original entry.source).mp typed
  obtain ⟨opened, preserved, sourceTyped⟩ := scope_opening entry.scope _ original closedTyped
  obtain ⟨slots, frame⟩ := (registry_source_typing_iff opened _ _).mp sourceTyped
  exact ⟨opened, preserved, sourceTyped, slots, (parallel_typing_iff opened _).mp frame⟩

/-- An offered output retains its actual public subject and both actual
ordered names, with call/reference/call roles obtained from source typing. -/
theorem offered_fields {Γ : Ctx sig} (roles : Roles Γ) (offer : Offer Γ)
    (typed : Typed roles offer.source) :
    ∃ channel first second : Var Γ .nm,
      offer.channel = .var channel ∧ offer.first = .var first ∧ offer.second = .var second ∧
      roles channel = .call ∧ roles first = .reference ∧ roles second = .call := by
  rcases offer with ⟨channel, first, second⟩
  cases channel with
  | op op _ => cases op
  | var channel =>
      cases first with
      | op op _ => cases op
      | var first =>
          cases second with
          | op op _ => cases op
          | var second =>
              exact ⟨channel, first, second, rfl, rfl, rfl,
                binary_output_roles roles channel first second typed⟩

/-- Every source expression has a concrete role-qualified protocol entry
when its external return name is fresh. No source expression is preselected. -/
theorem fresh_result_entry_roles {Γ : Ctx sig} (term : NamePassingLambda.Expr Γ) :
    let entry := guarded_entry (guarded_compiler_image term (fun _ name => .succ name) .zero)
    ∃ opened : Roles entry.world,
      PreservesScope entry.scope (canonicalRoles Γ) opened ∧
      Typed opened (registrySource (offeredRegistry entry.offers) (parallel entry.residual)) ∧
      (∀ owner, Typed opened (offeredRegistry entry.offers owner).source) ∧
      (∀ atom ∈ entry.residual, Typed opened atom) :=
  entry_roles _ _ (fresh_result_compile_typed term)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.EntryRoles
