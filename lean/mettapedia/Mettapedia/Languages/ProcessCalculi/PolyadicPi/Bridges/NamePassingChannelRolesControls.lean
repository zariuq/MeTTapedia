import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentControls

/-!
# Nonvacuous compiler-image channel controls

The existing closed retained-definition program realizes the role discipline,
including its private application channel and environment server. Aliasing the
return channel with a reference cannot satisfy the judgment. The binary binder
order and public mixed-arity obstruction are distinguished independently.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentControls

/-- The already executed closed definition program has a typed compiler image,
with a call-only external interface and independently introduced local roles. -/
theorem closed_environment_compiler_typed :
    Typed (canonicalRoles []) (compile loopingDefinition closedNames returnName) :=
  compile_typed loopingDefinition closedNames returnName (canonicalRoles [])
    (fun name => nomatch name) rfl

theorem closed_released_compiler_typed :
    Typed (canonicalRoles []) (compile releasedCall closedNames returnName) :=
  compile_typed releasedCall closedNames returnName (canonicalRoles [])
    (fun name => nomatch name) rfl

/-- A real source lookup changes the compiled program at its supplied endpoint,
and both actual compiler images meet the role discipline. -/
theorem retained_definition_execution_typed :
    Typed (canonicalRoles []) (compile loopingDefinition closedNames returnName) ∧
      StepModulo (compile loopingDefinition closedNames returnName)
        (compile releasedCall closedNames returnName) ∧
      Typed (canonicalRoles []) (compile releasedCall closedNames returnName) :=
  ⟨closed_environment_compiler_typed, private_channel_fetch_executes, closed_released_compiler_typed⟩

/-- The role invariant reaches the actual supplied execution endpoint even
when the proof does not recognize that endpoint as another compiler image. -/
theorem retained_definition_subject_reduction :
    Typed (canonicalRoles []) (compile releasedCall closedNames returnName) :=
  closed_environment_compiler_typed.modulo_step private_channel_fetch_executes

/-- The existing retained-definition execution is a nonempty path of the
actual operational theory; its lookup fires below the private application. -/
def retainedDefinitionPath : Mettapedia.GSLT.IndexedOperational.ExecutionPath
    (NativeTypes.operationalTheory [Srt.nm])
    (compile loopingDefinition closedNames returnName)
    (compile releasedCall closedNames returnName) :=
  .cons ⟨private_channel_fetch_executes⟩ (.refl _)

theorem retained_definition_path_roles :
    Typed (canonicalRoles []) (compile releasedCall closedNames returnName) :=
  fresh_result_compilation_execution_roles loopingDefinition retainedDefinitionPath

theorem retained_definition_visited_roles {middle : Proc [Srt.nm]}
    (earlier : Mettapedia.GSLT.IndexedOperational.ExecutionPath
      (NativeTypes.operationalTheory [Srt.nm])
      (compile loopingDefinition closedNames returnName) middle)
    (later : Mettapedia.GSLT.IndexedOperational.ExecutionPath
      (NativeTypes.operationalTheory [Srt.nm]) middle
      (compile releasedCall closedNames returnName))
    (split : retainedDefinitionPath = earlier.append later) :
    Typed (canonicalRoles []) middle :=
  closed_environment_compiler_typed.execution_visited retainedDefinitionPath earlier later split

/-- Exchanging private binders also exchanges their different roles. The
name transported in a unary lookup remains call-typed after the exchange. -/
theorem different_private_roles_exchange :
    Typed (canonicalRoles [])
      (nu (nu (Mettapedia.OSLF.Binding.rename swapRen
        (out1 (.var .zero) (.var (.succ .zero)))))) :=
  (show Typed (canonicalRoles [])
    (nu (nu (out1 (.var .zero) (.var (.succ .zero))))) from
      .nu .call (.nu .reference (.out1 _ _ rfl rfl))).private_exchange

theorem nested_definition_compiler_typed :
    Typed (canonicalRoles []) (compile nestedDefinitions closedNames returnName) :=
  compile_typed nestedDefinitions closedNames returnName (canonicalRoles [])
    (fun name => nomatch name) rfl

/-- The new lambda reference and call/result binders are distinct and carry
the authored binary order, rather than an inferred ordering of equal sorts. -/
theorem binary_binder_roles {Γ : Ctx sig} (roles : Roles Γ) :
    pairRoles roles .zero = .reference ∧ pairRoles roles (.succ .zero) = .call :=
  ⟨rfl, rfl⟩

theorem wrong_binary_binder_order_rejected {Γ : Ctx sig} (roles : Roles Γ) :
    ¬ Typed (pairRoles roles)
      (out1 (.var (.succ .zero)) (.var .zero)) := by
  intro typed
  have reference := (unary_output_roles _ _ _ typed).1
  cases reference

/-- The compiler's application allocates a call role independently of all
ambient reference names. -/
theorem application_fresh_call_role {Γ : Ctx sig} (roles : Roles Γ) :
    extendRole .call roles .zero = .call ∧
      ∀ name : Var Γ .nm, extendRole .call roles (.succ name) = roles name :=
  ⟨rfl, fun _ => rfl⟩

theorem definition_fresh_reference_role {Γ : Ctx sig} (roles : Roles Γ) :
    extendRole .reference roles .zero = .reference ∧
      ∀ name : Var Γ .nm, extendRole .reference roles (.succ name) = roles name :=
  ⟨rfl, fun _ => rfl⟩

/-- Looking up a reference and returning on that same name is not an image
with a separated reference/call interface, for any proposed role assignment. -/
theorem reference_result_alias_rejected {Γ : Ctx sig} (roles : Roles Γ) (name : Var Γ .nm) :
    ¬ Typed roles (translate (.var name) name) := by
  intro typed
  have fields := unary_output_roles roles name name typed
  rw [fields.1] at fields
  cases fields.2

def twoNames : Ctx sig := [Srt.nm, Srt.nm]

def referenceName : Var twoNames .nm := .succ .zero
def resultName : Var twoNames .nm := .zero

def separatedRoles : Roles twoNames := canonicalRoles [Srt.nm]

/-- An ordinary open lookup has the required unary role without conflating
its reference with the independently supplied result. -/
theorem separated_lookup_typed :
    Typed separatedRoles (translate (.var referenceName) resultName) :=
  .out1 _ _ rfl rfl

theorem mixed_arity_same_name_rejected :
    ¬ Typed separatedRoles
      (par (out1 (.var referenceName) (.var resultName))
        (inp2 (.var referenceName) nil)) :=
  no_mixed_arity_pair _ _ _ _

theorem binary_call_typed :
    Typed separatedRoles
      (out2 (.var resultName) (.var referenceName) (.var resultName)) :=
  .out2 _ _ _ rfl rfl rfl

def binaryEchoBody : Proc (.nm :: .nm :: twoNames) :=
  out1 (.var .zero) (.var (.succ .zero))

theorem binary_echo_source_typed :
    Typed separatedRoles
      (par (out2 (.var resultName) (.var referenceName) (.var resultName))
        (inp2 (.var resultName) binaryEchoBody)) :=
  .par binary_call_typed (.inp2 _ rfl (.out1 _ _ rfl rfl))

/-- An actual binary COMM supplies its reference and return names in the
typed order. The resulting unary lookup retains the same ambient roles. -/
theorem binary_echo_fires :
    Step (par (out2 (.var resultName) (.var referenceName) (.var resultName))
      (inp2 (.var resultName) binaryEchoBody))
      (out1 (.var referenceName) (.var resultName)) :=
  .comm2 _ _ _ _

theorem raw_communication_retains_roles :
    Typed separatedRoles (out1 (.var referenceName) (.var resultName)) :=
  binary_echo_source_typed.raw_step binary_echo_fires

/-- Reference/call roles constrain arity, not name injectivity: two distinct
source references may still collapse onto the same target reference. -/
def collapsedReferenceEnvironment : Ren sig [Srt.nm, Srt.nm] twoNames := fun _ name =>
  match name with
  | .zero => referenceName
  | .succ .zero => referenceName
  | .succ (.succ impossible) => nomatch impossible

theorem collapsed_reference_roles_preserved :
    ReferenceEnvironment separatedRoles collapsedReferenceEnvironment := by
  intro name
  cases name with
  | zero => rfl
  | succ name => cases name with
      | zero => rfl
      | succ impossible => nomatch impossible

theorem collapsed_references_not_injective :
    ¬ Function.Injective (collapsedReferenceEnvironment Srt.nm) := by
  intro injective
  have equal := injective (show collapsedReferenceEnvironment _ .zero =
    collapsedReferenceEnvironment _ (.succ .zero) from rfl)
  cases equal

theorem collapsed_reference_compiler_typed (term : Expr [Srt.nm, Srt.nm]) :
    Typed separatedRoles (compile term collapsedReferenceEnvironment resultName) :=
  compile_typed term _ _ _ collapsed_reference_roles_preserved rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles.Controls
