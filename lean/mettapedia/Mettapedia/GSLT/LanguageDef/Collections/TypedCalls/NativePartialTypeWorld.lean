import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraphSafety
import Mettapedia.Machines.ReadOnlyQueryPartialComposition

/-!
# World congruence of partially available type plans

Only the replies actually present in the partial store must be resource-safe.
First-local matching derives the safety of its selected substitution. Both
the returned status and the entire ordered read certificate agree; unavailable
observations remain unavailable, not a fabricated empty typing list.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativePartialTypeWorld

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlyQueryPartialComposition
open Mettapedia.Machines.ReadOnlyQuerySafety
open TypeDependencyAdmission TypeScopeMatcher NativeTypeDemand NativeTypeCallGraphSafety
open RetainedTypePayloads (ExternalView)

abbrev Store := Question Atom → Option (ViewReply Atom Atom)

def StoreSafe (available : Store) : Prop :=
  ∀ key reply, available key = some reply → ReplySafe reply

theorem argsPlan_world (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (available : Store)
    (repliesSafe : StoreSafe available) :
    ∀ formals values state, resourceFreeList formals = true → SafeState state →
      run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
        (NativeTypeDemand.argsPlan (ops first normalizeFirst subtypesFirst) formals values state)) =
      run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
        (NativeTypeDemand.argsPlan (ops second normalizeSecond subtypesSecond) formals values state))
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | formal :: formals, value :: values, state, formalsSafe, stateSafe => by
      simp only [resourceFreeList, Bool.and_eq_true] at formalsSafe
      have expectedSafe := substitute_resourceFree state stateSafe formal formalsSafe.1
      simp only [NativeTypeDemand.argsPlan, Mettapedia.Machines.ReadOnlyQueryDemand.demand, run]
      cases kindRead : available (.kind value) with
      | none => rfl
      | some reply =>
          cases reply with
          | class_ _ | types _ => rfl
          | kind kind =>
              simp only [ops]
              cases metaReply : metaCheckAtom (substA state formal) kind with
              | some answer =>
                  cases answer with
                  | false => rfl
                  | true =>
                      dsimp only
                      have restEq := argsPlan_world first second normalizeFirst normalizeSecond subtypesFirst subtypesSecond
                        available repliesSafe formals values state formalsSafe.2 stateSafe
                      dsimp only [ops] at restEq
                      rw [restEq]
              | none =>
                  simp only [NativeTypeDemand.typesRead, Mettapedia.Machines.ReadOnlyQueryDemand.demand, run]
                  cases typeRead : available (.inferred value) with
                  | none => rfl
                  | some reply =>
                      cases reply with
                      | class_ _ | kind _ => rfl
                      | types actuals =>
                          dsimp only
                          have actualsSafe : resourceFreeList actuals = true := repliesSafe _ _ typeRead
                          have chosenEq := firstResult_congr_on
                            (fun actual => unify first state actual (substA state formal))
                            (fun actual => unify second state actual (substA state formal)) actuals
                            (fun actual present => unify_world first second state stateSafe actual (substA state formal)
                              ((resourceFreeList_iff _).mp actualsSafe actual present) expectedSafe)
                          rw [chosenEq]
                          cases chosen : StampInference.firstResult
                              (fun actual => unify second state actual (substA state formal)) actuals with
                          | none => rfl
                          | some next =>
                              dsimp only
                              have nextSafe := firstResult_preserves second state stateSafe (substA state formal)
                                expectedSafe actuals actualsSafe next chosen
                              have restEq := argsPlan_world first second normalizeFirst normalizeSecond subtypesFirst subtypesSecond
                                available repliesSafe formals values next formalsSafe.2 nextSafe
                              dsimp only [ops] at restEq
                              rw [restEq]

theorem argsPlan_selected_safe (world : ExternalView) (normalize : Atom → Atom)
    (subtypes : List Atom → List Atom) (available : Store) (repliesSafe : StoreSafe available)
    (formals values : List Atom) (state selected : TypeScopeMatcher.State)
    (formalsSafe : resourceFreeList formals = true) (stateSafe : SafeState state)
    (returned : (run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeDemand.argsPlan (ops world normalize subtypes) formals values state))).answer =
        some (.ok (some selected))) : SafeState selected := by
  exact completed_sound (fun _ => True) ReplySafe (OnSuccess BindingSafe) _
    (NativeTypeCallGraphSafety.argsPlan world normalize subtypes formals values state formalsSafe stateSafe)
    available (fun key _ reply found => repliesSafe key reply found) _ returned

theorem rowsPlan_world (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizers : ∀ type_, resourceFree type_ = true → normalizeFirst type_ = normalizeSecond type_)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (available : Store)
    (repliesSafe : StoreSafe available) (values : List Atom) :
    ∀ rows, resourceFreeList rows = true →
      run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
        (NativeTypeDemand.rowsPlan (ops first normalizeFirst subtypesFirst) values rows)) =
      run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
        (NativeTypeDemand.rowsPlan (ops second normalizeSecond subtypesSecond) values rows))
  | [], _ => rfl
  | row :: rows, rowsSafe => by
      simp only [resourceFreeList, Bool.and_eq_true] at rowsSafe
      have rest := rowsPlan_world first second normalizeFirst normalizeSecond normalizers
        subtypesFirst subtypesSecond available repliesSafe values rows rowsSafe.2
      have arrowEq : (ops first normalizeFirst subtypesFirst).arrow row =
          (ops second normalizeSecond subtypesSecond).arrow row := rfl
      simp only [NativeTypeDemand.rowsPlan, ← arrowEq]
      cases arrow : (ops first normalizeFirst subtypesFirst).arrow row with
      | none => exact rest
      | some signature =>
          obtain ⟨formals, range⟩ := signature
          have parts := arrow_resourceFree first normalizeFirst subtypesFirst rowsSafe.1 arrow
          apply run_demand_bind_congr
          · exact argsPlan_world first second normalizeFirst normalizeSecond subtypesFirst subtypesSecond
              available repliesSafe formals values Atom.var parts.1 (fun _ => rfl)
          · intro answer returned
            cases answer with
            | error _ => rfl
            | ok selected =>
                cases selected with
                | none => exact rest
                | some state =>
                    have safe := argsPlan_selected_safe first normalizeFirst subtypesFirst available repliesSafe
                      formals values Atom.var state parts.1 (fun _ => rfl) returned
                    have rangeSafe := substitute_resourceFree state safe range parts.2
                    simp only [run_demand_map]
                    rw [rest]
                    simp only [ops, normalizers _ rangeSafe]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativePartialTypeWorld
