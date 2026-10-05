import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryWorld
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

/-!+# Concrete active headers of the scoped unary compiler

Each activity names an existing source constructor or an actual suspended
implementation phase. Rendering gives core-rho input/output headers with
independently proved sorting and binder scope. Pending source restrictions
and server installations retain their continuations. Request messages remain
separate occurrences because a shared reply address does not associate the
next reply with the oldest request.

The ordinary handler is obtained from the concrete option-valued compiler;
its equation below identifies it with any supplied successful compiler
result. No source transition relation authorizes the rendered rho steps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryActive

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryClosing RhoUnaryNaturality
open RhoUnaryEnvironment RhoUnaryExecution RhoUnaryWorld
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

noncomputable def compiled {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process)
    {depth : Nat} (world : World Γ depth) : Code depth :=
  Classical.choose (compile_guarded guarded world)

theorem compiled_spec {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process)
    {depth : Nat} (world : World Γ depth) :
    compile world process = some (compiled guarded world) :=
  Classical.choose_spec (compile_guarded guarded world)

theorem compiled_eq {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process)
    {depth : Nat} (world : World Γ depth) (code : Code depth)
    (supplied : compile world process = some code) : compiled guarded world = code :=
  Option.some.inj ((compiled_spec guarded world).symm.trans supplied)

noncomputable def ordinary {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : World Γ 0) : Code 1 :=
  compiled guarded (liftWorld world)

noncomputable def installBody {Γ : Ctx sig} (channel : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : World Γ 0) : Code 1 :=
  waitingServer (world channel) (compiled guarded (serverHandlerWorld world))
    (compiled guarded (storedHandlerWorld world))

noncomputable def stored {Γ : Ctx sig} (channel : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : World Γ 0)
    (self : Nat) : Pattern :=
  GuardedReplication.code (allocatedName self) (world channel).term (ordinary guarded world).term

noncomputable def readyBody {Γ : Ctx sig} (channel : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : World Γ 0)
    (self : Nat) : Pattern :=
  RhoScopedServers.parallel [send (allocatedName self) (stored channel guarded world self),
    stored channel guarded world self, (ordinary guarded world).term]

/-- The activities expose only input/output guards. Ordinary pi input
continuations, including all nested scopes and servers, remain suspended. -/
inductive Activity (Γ : Ctx sig) where
  | output (channel datum : Var Γ .nm)
  | input (channel : Var Γ .nm) (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body)
  | privateScope (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body)
  | install (channel : Var Γ .nm) (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body)
  | ready (channel : Var Γ .nm) (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body) (self : Nat)
  | rearm (channel : Var Γ .nm) (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body) (self : Nat)
  | sendCode (channel : Var Γ .nm) (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body) (self : Nat)
  | request
  | reply (seed : Nat)
  | allocatorReady
  | allocatorRearm
  | allocatorSendCode
  | seedInput
  | token (seed : Nat)

def Activity.source {Γ : Ctx sig} : Activity Γ → Proc Γ
  | .output channel datum => out1 (.var channel) (.var datum)
  | .input channel body _ => inp1 (.var channel) body
  | .privateScope body _ => nu body
  | .install channel body _ | .ready channel body _ _ | .rearm channel body _ _ =>
      rep (inp1 (.var channel) body)
  | _ => nil

theorem Activity.source_guarded {Γ : Ctx sig} (activity : Activity Γ) :
    GuardedUnary activity.source := by
  cases activity with
  | output channel datum => exact .out1 _ _
  | input channel body guarded => exact .inp1 _ guarded
  | privateScope body guarded => exact .nu guarded
  | install channel body guarded | ready channel body guarded self | rearm channel body guarded self =>
      exact .server _ guarded
  | sendCode channel body guarded self | request | reply seed | allocatorReady |
    allocatorRearm | allocatorSendCode | seedInput | token seed => exact .nil

noncomputable def Activity.header {Γ : Ctx sig} (world : World Γ 0) : Activity Γ → Header
  | .output channel datum => .output (world channel).term (world datum).payload
  | .input channel _ guarded => .input (world channel).term (ordinary guarded world).term
  | .privateScope _ guarded => .input allocatorReply.term (ordinary guarded world).term
  | .install channel _ guarded => .input allocatorReply.term (installBody channel guarded world).term
  | .ready channel _ guarded self => .input (world channel).term (readyBody channel guarded world self)
  | .rearm channel _ guarded self => .input (allocatedName self)
      (GuardedReplication.body (allocatedName self) (world channel).term (ordinary guarded world).term)
  | .sendCode channel _ guarded self => .output (allocatedName self) (stored channel guarded world self)
  | .request => .output allocatorRequest.term (NameValue.reserved Reserved.reply : NameValue 0).payload
  | .reply seed => .output allocatorReply.term (seedCode seed)
  | .allocatorReady => .input allocatorRequest.term
      (RhoScopedServers.parallel [send allocatorSelf.term
        (GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term),
        GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term,
        (allocationHandler allocatorState).term])
  | .allocatorRearm => .input allocatorSelf.term
      (GuardedReplication.body allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term)
  | .allocatorSendCode => .output allocatorSelf.term
      (GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term)
  | .seedInput => .input allocatorState.term
      (RhoScopedServers.parallel [send (.apply "NQuote" [.apply "PDrop" [allocatorReply.term]]) (drop 0),
        send allocatorState.term (send (.bvar 0) RhoScopedAllocation.zero)])
  | .token seed => .output allocatorState.term (seedCode seed)

private theorem typed_input_body {channel body : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext [] (receive channel body)) :
    Header.Typed rhoAtomicNameContext (.input channel body) :=
  (rho_input_wellSorted_inv typed).2

private theorem safe_input_body {channel body : Pattern}
    (safe : binderSafeAt "NQuote" 0 (receive channel body) = true) :
    Header.Safe (.input channel body) := by
  simpa [Header.Safe, receive, binderSafeAt, binderSafeListAt, Bool.and_eq_true] using safe

/-- The rendered headers meet the concrete authored matcher and
canonical-stepper formation conditions. -/
theorem Activity.header_typed {Γ : Ctx sig} (world : World Γ 0) (activity : Activity Γ) :
    (activity.header world).Typed rhoAtomicNameContext := by
  cases activity with
  | output channel datum => exact ⟨(world channel).typed, (world datum).payload_typed⟩
  | input channel body guarded => exact ⟨(world channel).typed, (ordinary guarded world).typed⟩
  | privateScope body guarded => exact ⟨allocatorReply.typed, (ordinary guarded world).typed⟩
  | install channel body guarded => exact ⟨allocatorReply.typed, (installBody channel guarded world).typed⟩
  | ready channel body guarded self =>
      exact typed_input_body (idle_typed (seedChannel rhoAtomicNameContext self)
        (world channel).channel (ordinary guarded world).handler)
  | rearm channel body guarded self =>
      exact typed_input_body (code_typed (seedChannel rhoAtomicNameContext self)
        (world channel).channel (ordinary guarded world).handler)
  | sendCode channel body guarded self =>
      exact ⟨.quote (seedCode_typed rhoAtomicNameContext self),
        code_typed (seedChannel rhoAtomicNameContext self) (world channel).channel
          (ordinary guarded world).handler⟩
  | request => exact ⟨allocatorRequest.typed, .drop allocatorReply.typed⟩
  | reply seed => exact ⟨allocatorReply.typed, seedCode_typed rhoAtomicNameContext seed⟩
  | allocatorReady =>
      exact typed_input_body (idle_typed allocatorSelf allocatorRequest (allocationHandler allocatorState))
  | allocatorRearm =>
      exact typed_input_body (code_typed allocatorSelf allocatorRequest (allocationHandler allocatorState))
  | allocatorSendCode =>
      exact ⟨allocatorSelf.typed, code_typed allocatorSelf allocatorRequest (allocationHandler allocatorState)⟩
  | seedInput => exact typed_input_body (seedReceiver_typed allocatorState allocatorReply)
  | token seed => exact ⟨allocatorState.typed, seedCode_typed rhoAtomicNameContext seed⟩

theorem Activity.header_safe {Γ : Ctx sig} (world : World Γ 0) (activity : Activity Γ) :
    (activity.header world).Safe := by
  cases activity with
  | output channel datum => exact ⟨(world channel).safe, (world datum).payload_safe⟩
  | input channel body guarded => exact ⟨(world channel).safe, (ordinary guarded world).safe⟩
  | privateScope body guarded => exact ⟨allocatorReply.safe, (ordinary guarded world).safe⟩
  | install channel body guarded => exact ⟨allocatorReply.safe, (installBody channel guarded world).safe⟩
  | ready channel body guarded self =>
      exact safe_input_body (idle_safe (seedChannel rhoAtomicNameContext self)
        (world channel).channel (ordinary guarded world).handler)
  | rearm channel body guarded self =>
      exact safe_input_body (code_safe (seedChannel rhoAtomicNameContext self)
        (world channel).channel (ordinary guarded world).handler)
  | sendCode channel body guarded self =>
      exact ⟨(seedChannel rhoAtomicNameContext self).safe,
        code_safe (seedChannel rhoAtomicNameContext self) (world channel).channel
          (ordinary guarded world).handler⟩
  | request => exact ⟨allocatorRequest.safe, (NameValue.reserved Reserved.reply : NameValue 0).payload_safe⟩
  | reply seed => exact ⟨allocatorReply.safe, seedCode_safe seed 0⟩
  | allocatorReady =>
      exact safe_input_body (idle_safe allocatorSelf allocatorRequest (allocationHandler allocatorState))
  | allocatorRearm =>
      exact safe_input_body (code_safe allocatorSelf allocatorRequest (allocationHandler allocatorState))
  | allocatorSendCode =>
      exact ⟨allocatorSelf.safe, code_safe allocatorSelf allocatorRequest (allocationHandler allocatorState)⟩
  | seedInput => exact safe_input_body (seedReceiver_safe allocatorState allocatorReply)
  | token seed => exact ⟨allocatorState.safe, seedCode_safe seed 0⟩

noncomputable def headers {Γ : Ctx sig} (world : World Γ 0) (activities : List (Activity Γ)) :
    List Header := activities.map (Activity.header world)

noncomputable def actual {Γ : Ctx sig} (world : World Γ 0) (activities : List (Activity Γ)) : Pattern :=
  HeaderInversion.parallel (headers world activities)

def source {Γ : Ctx sig} (activities : List (Activity Γ)) : Proc Γ :=
  ScopedActiveFrontier.parallel (activities.map Activity.source)

theorem headers_typed {Γ : Ctx sig} (world : World Γ 0) (activities : List (Activity Γ)) :
    ∀ header ∈ headers world activities, header.Typed rhoAtomicNameContext := by
  intro header member
  obtain ⟨activity, _, rfl⟩ := List.mem_map.mp member
  exact activity.header_typed world

theorem headers_safe {Γ : Ctx sig} (world : World Γ 0) (activities : List (Activity Γ)) :
    ∀ header ∈ headers world activities, header.Safe := by
  intro header member
  obtain ⟨activity, _, rfl⟩ := List.mem_map.mp member
  exact activity.header_safe world

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryActive
