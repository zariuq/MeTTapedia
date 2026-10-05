import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryRoles

/-!
# Exact contractums of every unary compiler phase

Public receipt opens the supplied source continuation immediately. Restoring
the same persistent listener is a later administrative communication. Private
scope consumes the actual returned seed; it does not assume which request
produced that reply. All equations are computed using the core rho COMM
substitution and the concrete compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPhase

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryClosing RhoUnaryNaturality
open RhoUnaryEnvironment RhoUnaryExecution RhoUnaryWorld RhoUnaryActive RhoUnaryRoles
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open RhoEncodingTyping RhoScopedServers RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem inst_guarded {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (datum : Var Γ .nm) :
    GuardedUnary (inst body (.var datum)) := by
  rw [inst_variable]
  exact guarded.rename (nameRen datum)

/-- A user receipt is the compiler's own exact source opening. -/
theorem ordinary_received {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) (datum : Var Γ .nm) :
    semanticCommSubst (ordinary guarded world.world).term (world.world datum).payload =
      (compiled (inst_guarded guarded datum) world.world).term := by
  obtain ⟨after, afterEq, received⟩ := continuation_received guarded world.world datum
    (world.index datum) rfl (ordinary guarded world.world) (compiled_spec guarded _)
  rw [← compiled_eq (inst_guarded guarded datum) world.world after afterEq] at received
  exact received

/-- A private binder receives this supplied allocator reply, including a
reply consumed ahead of a different pending binder. -/
theorem private_received {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : World Γ 0) (seed : Nat) :
    semanticCommSubst (ordinary guarded world).term (seedCode seed) =
      (compiled guarded (allocatedWorld world seed)).term := by
  obtain ⟨after, afterEq, substituted⟩ := compile_closeSeed guarded (liftWorld world) seed
    (ordinary guarded world) (compiled_spec guarded _)
  rw [closeWorld_lift_ground] at afterEq
  rw [← compiled_eq guarded (allocatedWorld world seed) after afterEq] at substituted
  simpa only [semanticCommSubst, seedCode_normalized, allocatedName] using substituted

/-- The server allocation reply installs the same handler as ordinary
input compilation, despite the additional stored-code binder scopes. -/
theorem install_received {Γ : Ctx sig} (channel : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : World Γ 0) (seed : Nat) :
    semanticCommSubst (installBody channel guarded world).term (seedCode seed) =
      GuardedReplication.idle (allocatedName seed) (world channel).term (ordinary guarded world).term := by
  obtain ⟨handlerSame, storedSame⟩ := serverHandler_same guarded world
    (ordinary guarded world) (compiled guarded (serverHandlerWorld world))
    (compiled guarded (storedHandlerWorld world))
    (compiled_spec guarded _) (compiled_spec guarded _) (compiled_spec guarded _)
  exact server_install_received (world channel) seed (ordinary guarded world)
    (compiled guarded (serverHandlerWorld world)) (compiled guarded (storedHandlerWorld world))
    handlerSame storedSame

/-- The public COMM commits the source request. Its supplied endpoint
already contains the opened source body beside the actual rearm pair. -/
theorem persistent_received {Γ : Ctx sig} (channel : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : SeedWorld Γ)
    (self : Nat) (datum : Var Γ .nm) :
    semanticCommSubst (readyBody channel guarded world.world self) (world.world datum).payload =
      RhoScopedServers.parallel [
        (Activity.sendCode channel body guarded self).header world.world |>.pattern,
        (Activity.rearm channel body guarded self).header world.world |>.pattern,
        (compiled (inst_guarded guarded datum) world.world).term] := by
  have released := RhoScopedServers.request_received
    (seedChannel rhoAtomicNameContext self) (world.world channel).channel
    (ordinary guarded world.world).handler (world.world datum).payload
  change semanticCommSubst (readyBody channel guarded world.world self) (world.world datum).payload =
      RhoScopedServers.parallel [send (allocatedName self) (stored channel guarded world.world self),
        stored channel guarded world.world self,
        semanticCommSubst (ordinary guarded world.world).term (world.world datum).payload] at released
  rw [ordinary_received guarded world datum] at released
  exact released

/-- Restoring code is administrative and keeps the same source listener. -/
theorem persistent_rearmed {Γ : Ctx sig} (channel : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : World Γ 0) (self : Nat) :
    semanticCommSubst
        (GuardedReplication.body (allocatedName self) (world channel).term (ordinary guarded world).term)
        (stored channel guarded world self) =
      ((Activity.ready channel body guarded self).header world).pattern :=
  RhoScopedServers.code_received (seedChannel rhoAtomicNameContext self)
    (world channel).channel (ordinary guarded world).handler

/-- The allocator's public request starts rearm and seed receipt. -/
theorem allocator_received {Γ : Ctx sig} (world : World Γ 0) :
    semanticCommSubst
        (RhoScopedServers.parallel [send allocatorSelf.term
          (GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term),
          GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term,
          (allocationHandler allocatorState).term])
        (NameValue.reserved Reserved.reply : NameValue 0).payload =
      RhoScopedServers.parallel [
        ((Activity.allocatorSendCode : Activity Γ).header world).pattern,
        (Activity.allocatorRearm.header world).pattern,
        (Activity.seedInput.header world).pattern] := by
  have released := RhoScopedServers.request_received allocatorSelf allocatorRequest
    (allocationHandler allocatorState) (NameValue.reserved Reserved.reply : NameValue 0).payload
  have opened := request_activated allocatorState allocatorReply
  change semanticCommSubst (allocationHandler allocatorState).term
    (NameValue.reserved Reserved.reply : NameValue 0).payload = seedReceiver allocatorState allocatorReply at opened
  rw [opened] at released
  exact released

theorem allocator_rearmed {Γ : Ctx sig} (world : World Γ 0) :
    semanticCommSubst
        (GuardedReplication.body allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term)
        (GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term) =
      ((Activity.allocatorReady : Activity Γ).header world).pattern :=
  RhoScopedServers.code_received allocatorSelf allocatorRequest (allocationHandler allocatorState)

/-- The real state transfer returns exactly the old seed and installs the
next token. Multiplicity of waiting receivers and replies is retained. -/
theorem token_received {Γ : Ctx sig} (world : World Γ 0) (seed : Nat) :
    semanticCommSubst
        (RhoScopedServers.parallel [send (.apply "NQuote" [.apply "PDrop" [allocatorReply.term]]) (drop 0),
          send allocatorState.term (send (.bvar 0) RhoScopedAllocation.zero)])
        (seedCode seed) =
      RhoScopedServers.parallel [
        ((Activity.reply seed : Activity Γ).header world).pattern,
        (Activity.token (seed + 1) |>.header world).pattern] :=
  seed_received allocatorState allocatorReply seed

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPhase
