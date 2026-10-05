import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryForward

/-!
# Repeated persistent-service controls for the concrete rho compiler

The source execution is supplied independently of the compiler. Its first
endpoint explicitly retains a receiver copy produced by server unfolding;
the second request leaves two equal replies and the same persistent server.
The target paths are executions of the actual authored rho theory, and their
witnesses represent the supplied endpoints, including that retained copy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryForwardControls

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler RhoUnaryEnvironment RhoUnaryCode RhoUnaryWorld RhoUnaryReadback RhoUnaryActive
open ScopedActiveFrontier

abbrev context : Ctx sig := [.nm, .nm, .nm]
abbrev channel : Var context .nm := .zero
abbrev reply : Var context .nm := .succ .zero
abbrev datum : Var context .nm := .succ (.succ .zero)

def body : Proc (.nm :: context) := out1 (.var (.succ reply)) (.var .zero)
def listener : Proc context := inp1 (.var channel) body
def server : Proc context := rep listener
def message : Proc context := out1 (.var channel) (.var datum)
def returned : Proc context := out1 (.var reply) (.var datum)

theorem body_guarded : GuardedUnary body := .out1 _ _
theorem payload_returned : inst body (.var datum) = returned := rfl

def initial : Proc context := parallel [message, server, message]
def oneCanonical : Proc context := par returned (par server (parallel [message]))
def oneExpanded : Proc context :=
  par returned (par (par listener server) (parallel [message]))
def twoReturned : Proc context := par returned (par returned (par server nil))

theorem initial_guarded : GuardedUnary initial :=
  .par (.out1 _ _) (.par (.server _ body_guarded) (.par (.out1 _ _) .nil))

theorem first_endpoint_unfolded : StructuralEq oneCanonical oneExpanded :=
  .par (.refl _) (.par (.repUnfold _) (.refl _))

/-- The first actual source communication has a supplied endpoint with an
extra ordinary receiver from the retained persistent server. -/
theorem first_source_step : (NativeTypes.operationalTheory context).Step initial oneExpanded := by
  have selected := Frontier.unary_server (⟨context, .nil, [message, server, message]⟩ : Frontier context)
    (.var channel) (.var datum) body [message] (List.Perm.refl _)
  change StepModulo initial oneCanonical at selected
  obtain ⟨redex, contractum, before, firing, after⟩ := selected
  exact ⟨redex, contractum, before, firing, after.trans first_endpoint_unfolded⟩

/-- The same original server answers the second equal message. Both equal
replies survive at the exact supplied source endpoint. -/
theorem second_source_step : (NativeTypes.operationalTheory context).Step oneExpanded twoReturned := by
  have selected := Frontier.unary_server (⟨context, .nil, [server, message]⟩ : Frontier context)
    (.var channel) (.var datum) body [] (List.Perm.swap _ _ [])
  obtain ⟨redex, contractum, before, firing, after⟩ := selected
  exact ⟨par returned redex, par returned contractum,
    first_endpoint_unfolded.symm.trans (.par (.refl _) before),
    .parR returned firing, .par (.refl _) after⟩

/-- Restoring unused server copies cannot erase the returned messages. -/
theorem replies_are_not_server_copies : ¬ StructuralEq twoReturned server := by
  intro equal
  have observed := ActiveHeaderInvariant.visible_structural .output1 equal
  simp [twoReturned, returned, server, listener, par, rep, inp1, out1, nil,
    ActiveHeaderInvariant.visible] at observed

def world : SeedWorld context := RhoUnaryWorld.initial context
noncomputable def code : Code 0 := compiled initial_guarded world.world

theorem supplied_compilation : compile world.world initial = some code :=
  compiled_spec initial_guarded world.world

private theorem initial_credit : RhoUnaryCredit.work initial = 4 := by
  simp [initial, message, server, listener, parallel, par, nil, rep, inp1, out1, RhoUnaryCredit.work]

/-- A nonempty authored execution realizes both independently supplied
source endpoints; the first block includes exactly four installation
communications and one public request. -/
theorem both_requests_realized :
    ∃ first final : TargetProcess,
    ∃ firstPath : ExecutionPath Target (runtimeProcess code world.available) first,
    ∃ secondPath : ExecutionPath Target first final,
      firstPath.length = 5 ∧ 0 < secondPath.length ∧
      Related world oneExpanded first ∧ Related world twoReturned final := by
  obtain ⟨before, credit⟩ := initial_witness initial_guarded world code supplied_compilation
  obtain ⟨first, firstPath, ⟨middle⟩, firstLength⟩ := RhoUnaryForward.forward before first_source_step
  obtain ⟨final, secondPath, preserved, secondLength⟩ := RhoUnaryForward.forward middle second_source_step
  refine ⟨first, final, firstPath, secondPath, ?_, ?_, ⟨middle⟩, preserved⟩
  · exact firstLength.trans (congrArg (fun count => count + 1) (credit.trans initial_credit))
  · have positive : 0 < middle.credit + 1 := Nat.zero_lt_succ _
    exact secondLength.symm ▸ positive

/-- Composition retains a real two-request authored path and its exact
duplicate-reply endpoint, rather than merely another reachable outcome. -/
theorem repeated_service_path :
    ∃ final : TargetProcess,
    ∃ path : ExecutionPath Target (runtimeProcess code world.available) final,
      6 ≤ path.length ∧ Related world twoReturned final := by
  obtain ⟨first, final, firstPath, secondPath, firstLength, secondPositive, _, preserved⟩ :=
    both_requests_realized
  refine ⟨final, firstPath.append secondPath, ?_, preserved⟩
  have length := Route.length_append firstPath secondPath
  omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryForwardControls
