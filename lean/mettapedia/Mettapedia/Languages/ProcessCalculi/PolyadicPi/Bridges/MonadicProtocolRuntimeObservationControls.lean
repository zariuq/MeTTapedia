import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeValueObservation

/-!
# Current and delayed function observations in real protocol states

A publicly committed call can already return a source function while the
actual target still has three private receipts to perform. Those private
listeners do not masquerade as a public function. Completion reaches its
public result listener in exactly three real communication steps. If result
and reference names are deliberately aliased, an inactive stored function can
produce a misleading public unary listener in the unrestricted lowering.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeObservationControls

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors RuntimeWitness RuntimeObservations RuntimeValueObservation
open ScopedActiveFrontier ActiveObservation NamePassingChannelRoles NamePassingLambda

abbrev context : Ctx sig := [.nm, .nm]
abbrev result : Var context .nm := .zero
abbrev reference : Var context .nm := .succ .zero
def roles : Roles context := fun name => match name with
  | .zero => .call
  | .succ .zero => .reference

def value : Proc context :=
  inp2 (.var result) (out1 (.var .zero) (.var (.succ .zero)))

def returned : Expr ([] : Ctx sig) := .lam (.var .zero)
def emptyEnvironment : Ren sig [] context := fun _ name => nomatch name

theorem value_is_the_actual_compiler_image : compile returned emptyEnvironment result = value := by
  rw [returned, compile, compile]
  rfl

def call : Call context :=
  ⟨.var reference, .var result,
    inp2 (.var (.succ (.succ result))) (out1 (.var .zero) (.var (.succ .zero)))⟩

theorem retained_readback_is_function : readback call = value := rfl

def registry : Fin 1 → Slot context := fun _ => .pending .callback call
def source : Proc context := registrySource registry (parallel [])
def target : Proc context := (privateScope 1).close (registryTarget registry (parallel []))

theorem source_is_exact_function : StructuralEq source value :=
  (StructuralEq.parUnit _).trans (.parUnit value)

theorem source_roles : Typed roles source :=
  .par (.par (.inp2 result rfl (.out1 _ _ rfl rfl)) (.nil _)) (.nil _)

def pendingWitness : Witness source target where
  world := context
  scope := .nil
  n := 1
  registry := registry
  frame := []
  heads := by intro atom member; cases member
  live := fun _ => trivial
  guards := fun _ => .pending .callback call (.inp2 _ (.out1 _ _))
  roles := roles
  typed := source_roles
  source := .refl _
  target := .refl _

theorem exact_pending_debt : pendingWitness.debt = 3 := rfl

theorem target_is_actual_callback_phase :
    StructuralEq target (callbackState call.first call.second (lower call.body)) := by
  have compared := Initialization.registry_closed 1 registry (parallel [])
  change StructuralEq target
    (par (par (Slot.closed (.pending .callback call)) nil) (lower nil)) at compared
  rw [lower_nil] at compared
  exact compared.trans ((StructuralEq.parUnit _).trans (.parUnit _))

/-- The delayed state is reached by the original unary public rendezvous,
not merely declared to be a phase of an abstract execution. -/
theorem actual_public_prefix :
    StepModulo (invocation (.var result) call.first call.second (lower call.body)) target :=
  modulo_target_equation (session_fires (.var result) call.first call.second (lower call.body))
    target_is_actual_callback_phase.symm

/-- Even though the retained source has returned, every active target
listener is still on an actual private protocol key. -/
theorem private_receipts_are_not_public_return : ¬ PublicHeader .input1 result target := by
  intro observed
  have opened := (publicHeader_scope_iff (privateScope 1) .input1 result _).mp observed
  rw [privateScope_inclusion] at opened
  have assembled := ((predicate .input1 _).2 (registry_equation registry (parallel [])
    (fun _ => trivial))).mp opened
  have framed := assembly_input_from_frame registry (parallel []) result assembled
  change PublicHeader .input1 result (lower nil) at framed
  rw [lower_nil] at framed
  simp only [PublicHeader, HasHeader, observations, nil,
    ActiveSyntaxMarking.mark, ActiveMarkedNames.observe, Set.mem_empty_iff_false, exists_false] at framed

/-- The delay is the outstanding real phase work, with no function-body
execution or additional source event included in the path. -/
theorem returned_function_realized_after_three_receipts :
    ∃ endpoint, ∃ path : ExecutionPath (NativeTypes.operationalTheory context) target endpoint,
      PublicHeader .input1 result endpoint ∧ path.length = 3 := by
  have represented : StructuralEq source (compile returned emptyEnvironment result) := by
    rw [value_is_the_actual_compiler_image]
    exact source_is_exact_function
  exact current_return_realized returned emptyEnvironment result (fun name => nomatch name)
    pendingWitness represented ⟨.lam (.var .zero)⟩

abbrev aliasedContext : Ctx sig := [.nm]
def aliasEnvironment : Ren sig aliasedContext aliasedContext := fun _ name => name
def stored : Expr aliasedContext := .carrier .zero (.lam (.var .zero)) (.var .zero)

theorem stored_function_is_not_returned :
    ¬ Nonempty (NamePassing.Environment.ReturningLambda stored) := by
  intro returning
  cases returning with
  | intro returning => cases returning with
    | carrier _ _ impossible => cases impossible

/-- The source reference carrier is visible when the result is deliberately
the same name. This unrestricted observation needs the fresh-result boundary. -/
theorem aliased_carrier_has_unary_result_listener :
    PublicHeader .input1 (.zero : Var aliasedContext .nm)
      (lower (compile stored aliasEnvironment .zero)) := by
  simp [stored, compile, lower_par, lower_out1, lower_inp1, PublicHeader, aliasEnvironment,
    hasHeader_par, hasHeader_out1, hasHeader_inp1, ActiveMarkedNames.nameKey]

theorem aliased_result_not_fresh :
    ¬ (∀ name : Var aliasedContext .nm, aliasEnvironment .nm name ≠ (.zero : Var aliasedContext .nm)) := by
  intro fresh
  exact fresh .zero rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeObservationControls
