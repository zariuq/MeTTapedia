import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolEntryRoles

/-!
# Concrete public-role qualification at protocol entry

A definition with a pending application opens two private source names. Its
one binary offer and two residual occurrences receive a common role assignment.
An aliased reference/result request cannot receive that assignment; physical
scope opening does not turn an ill-typed request into a typed one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.EntryRoles.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingChannelRoles ScopedActiveFrontier Initialization RuntimeState

abbrev context : Ctx sig := [.nm]

def expression : Expr context :=
  .defn (.lam (.var .zero)) (.app (.var .zero) (.succ .zero))

def entry : Entry (compile expression (fun _ name => .succ name) .zero) :=
  guarded_entry (guarded_compiler_image expression (fun _ name => .succ name) .zero)

theorem one_uncommitted_offer : entry.offers.length = 1 := by
  simp only [entry, guarded_entry, expression, compile]
  rw [ScopedActiveFrontier.normalize_nu, ScopedActiveFrontier.normalize_par,
    ScopedActiveFrontier.normalize_nu, ScopedActiveFrontier.normalize_par,
    ScopedActiveFrontier.normalize_out1, ScopedActiveFrontier.normalize_out2,
    ScopedActiveFrontier.normalize_rep]
  rfl

theorem two_residual_occurrences : entry.residual.length = 2 := by
  simp only [entry, guarded_entry, expression, compile]
  rw [ScopedActiveFrontier.normalize_nu, ScopedActiveFrontier.normalize_par,
    ScopedActiveFrontier.normalize_nu, ScopedActiveFrontier.normalize_par,
    ScopedActiveFrontier.normalize_out1, ScopedActiveFrontier.normalize_out2,
    ScopedActiveFrontier.normalize_rep]
  rfl

/-- Both source private names open before public roles classify the offer
and residual listener/request in their one actual shared source context. -/
theorem definition_application_entry_roles :
    ∃ opened : Roles entry.world,
      PreservesScope entry.scope (canonicalRoles context) opened ∧
      Typed opened (registrySource (offeredRegistry entry.offers) (parallel entry.residual)) ∧
      (∀ owner, Typed opened (offeredRegistry entry.offers owner).source) ∧
      (∀ atom ∈ entry.residual, Typed opened atom) :=
  entry_roles entry _ (fresh_result_compile_typed expression)

theorem offer_has_ordered_reference_call_fields :
    ∃ opened : Roles entry.world,
      PreservesScope entry.scope (canonicalRoles context) opened ∧
      ∀ owner : Fin entry.offers.length,
        ∃ channel first second : Var entry.world .nm,
          entry.offers[owner.val].channel = .var channel ∧
          entry.offers[owner.val].first = .var first ∧
          entry.offers[owner.val].second = .var second ∧
          opened channel = .call ∧ opened first = .reference ∧ opened second = .call := by
  obtain ⟨opened, preserved, _, slots, _⟩ := definition_application_entry_roles
  exact ⟨opened, preserved, fun owner => offered_fields opened _ (slots owner)⟩

theorem opened_ambient_result_role :
    ∃ opened : Roles entry.world,
      opened (entry.scope.inclusion _ .zero) = .call ∧
      opened (entry.scope.inclusion _ (.succ .zero)) = .reference := by
  obtain ⟨opened, preserved, _, _, _⟩ := definition_application_entry_roles
  exact ⟨opened, preserved .zero, preserved (.succ .zero)⟩

/-- Result separation is needed for the public arity discipline, independently
of whether an untyped compiler image has an operational readback. -/
theorem aliased_reference_result_has_no_roles (roles : Roles context) :
    ¬ Typed roles (compile (.var (.zero : Var context .nm)) (fun _ name => name) .zero) := by
  intro typed
  obtain ⟨reference, call⟩ := unary_output_roles roles .zero .zero typed
  rw [reference] at call
  cases call

theorem opening_a_bad_private_request_cannot_supply_roles (roles : Roles []) :
    ¬ Typed roles (nu (out1 (.var .zero) (.var .zero))) := by
  intro typed
  obtain ⟨opened, _, bodyTyped⟩ := scope_opening (.bind .nil) _ roles typed
  obtain ⟨reference, call⟩ := unary_output_roles opened .zero .zero bodyTyped
  rw [reference] at call
  cases call

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.EntryRoles.Controls
