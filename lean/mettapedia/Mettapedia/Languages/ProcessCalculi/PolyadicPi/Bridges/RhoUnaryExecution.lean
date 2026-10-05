import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryEnvironment

/-!
# Concrete communication and scope blocks of the unary-to-rho compiler

The supplied compiler output, continuation and allocator token determine the
actual endpoints. No operational simulation premise is accepted. Ordinary
name communication opens the compiled source continuation; private scope
performs the shared allocator's three service communications and the client's
reply communication. The allocator remains present with its advancing token.

These are selected blocks. Global image closure under arbitrary target
interleavings, private-scope equations and external quotation observers are
additional contracts and are not asserted by these endpoint theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryExecution

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCode
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCompiler
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryClosing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNaturality
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryEnvironment
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

/-- Extend the source name environment by the actual received fresh seed. -/
def allocatedWorld {Γ : Ctx sig} (world : World Γ 0) (seed : Nat) : World (.nm :: Γ) 0
  | .zero => .allocated seed
  | .succ old => world old

@[simp] theorem closeSeed_ground (seed : Nat) (name : NameValue 0) :
    closeSeed seed name.weaken = name := by
  cases name with
  | bound index => exact Fin.elim0 index
  | atom label | allocated index | reserved channel => rfl

@[simp] theorem closeWorld_lift_ground {Γ : Ctx sig} (world : World Γ 0) (seed : Nat) :
    closeWorld seed (liftWorld world) = allocatedWorld world seed := by
  funext name
  cases name with
  | zero => simp [closeWorld, liftWorld, closeSeed, allocatedWorld]
  | succ old => simp [closeWorld, liftWorld, allocatedWorld]

/-- Receiving a source variable naming this seed selects the same source
binder substitution and target environment extension. -/
theorem pullWorld_allocated {Γ : Ctx sig} (world : World Γ 0) (datum : Var Γ .nm) (seed : Nat)
    (datumEq : world datum = .allocated seed) :
    pullWorld world (nameRen datum) = allocatedWorld world seed := by
  funext name
  cases name with
  | zero => exact datumEq
  | succ old => rfl

/-- The real semantic COMM substitution returns the compiled *supplied*
source continuation. Nested private scopes and persistent inputs are allowed. -/
theorem continuation_received {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : World Γ 0) (datum : Var Γ .nm) (seed : Nat)
    (datumEq : world datum = .allocated seed) (bodyCode : Code 1)
    (compiled : compile (liftWorld world) body = some bodyCode) :
    ∃ after : Code 0, compile world (inst body (.var datum)) = some after ∧
      semanticCommSubst bodyCode.term (seedCode seed) = after.term := by
  obtain ⟨after, afterEq, substituted⟩ := compile_closeSeed guarded (liftWorld world) seed bodyCode compiled
  rw [closeWorld_lift_ground] at afterEq
  refine ⟨after, ?_, ?_⟩
  · rw [compile_inst_variable guarded, pullWorld_allocated world datum seed datumEq]
    exact afterEq
  · simpa only [semanticCommSubst, seedCode_normalized, allocatedName] using substituted

/-- An ordinary source communication compiles to one actual core COMM with
its exact compiled continuation; no pure-RF body restriction is imposed. -/
theorem communication_reduces {Γ : Ctx sig} (channel : Name Γ) (datum : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (world : World Γ 0) (seed : Nat) (datumEq : world datum = .allocated seed) :
    ∃ before after : Code 0,
      compile world (par (out1 channel (.var datum)) (inp1 channel body)) = some before ∧
      compile world (inst body (.var datum)) = some after ∧
      Nonempty (Reduces before.term after.term) := by
  obtain ⟨bodyCode, bodyEq⟩ := compile_guarded guarded (liftWorld world)
  obtain ⟨after, afterEq, received⟩ := continuation_received guarded world datum seed datumEq bodyCode bodyEq
  let before := Code.par (Code.sendName (evalName world channel) (evalName world (.var datum)))
    (Code.listen (evalName world channel) bodyCode)
  refine ⟨before, after, ?_, afterEq, ?_⟩
  · simp [before, compile, par, out1, inp1, bodyEq]
  · have raw := Reduces.comm (n := (evalName world channel).term) (q := seedCode seed)
      (p := bodyCode.term) (rest := [])
    rw [received] at raw
    exact ⟨.equiv (by simp [before, Code.par, Code.sendName, Code.emit, Code.datum,
      Code.listen, evalName, datumEq, NameValue.payload]; exact .refl _)
      raw (StructuralCongruence.par_singleton _)⟩

/-- The primitive authored rule also fires on this actual compiler output. -/
theorem communication_authored {Γ : Ctx sig} (channel : Name Γ) (datum : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (world : World Γ 0) (seed : Nat) (datumEq : world datum = .allocated seed)
    (bodyCode : Code 1) (compiled : compile (liftWorld world) body = some bodyCode) :
    ∃ after : Code 0,
      compile world (inst body (.var datum)) = some after ∧
      RhoStepAt 1
        (parallel [send (evalName world channel).term (seedCode seed),
          receive (evalName world channel).term bodyCode.term])
        (parallel [after.term]) := by
  obtain ⟨after, afterEq, received⟩ := continuation_received guarded world datum seed datumEq bodyCode compiled
  refine ⟨after, afterEq, ?_⟩
  have fired := authored_comm_at
    (elements := [send (evalName world channel).term (seedCode seed),
      receive (evalName world channel).term bodyCode.term])
    (inputIndex := 1) (outputIndex := 0) (by simp) (by simp)
    (by rfl) (by rfl) bodyCode.typed (seedCode_typed rhoAtomicNameContext seed)
  simpa [received] using fired

abbrev allocatorSelf := reservedChannel .code
abbrev allocatorState := reservedChannel .state
abbrev allocatorRequest := reservedChannel .request
abbrev allocatorReply := reservedChannel .reply

/-- One shared allocator and its exact state token accompany the guest code. -/
def runtime (code : Code 0) (seed : Nat) : Pattern :=
  parallel [code.term, server allocatorSelf allocatorState allocatorRequest, stateToken allocatorState seed]

/-- Allocating scope is an actual four-COMM implementation block for any
compiled guarded continuation, with the same shared allocator retained. -/
theorem reserve_reduces (bodyCode : Code 1) (seed : Nat) :
    Nonempty (ReducesN 4 (runtime (Code.reserve bodyCode) seed)
      (parallel [server allocatorSelf allocatorState allocatorRequest,
        stateToken allocatorState (seed + 1), semanticCommSubst bodyCode.term (seedCode seed)])) := by
  obtain ⟨path⟩ := client_reduces allocatorSelf allocatorState allocatorRequest allocatorReply bodyCode.handler seed
  have before : StructuralCongruence (runtime (Code.reserve bodyCode) seed)
      (clientInvocation allocatorSelf allocatorState allocatorRequest allocatorReply bodyCode.handler seed) := by
    refine .trans _ _ _ (Context.par_flatten_head _ _) ?_
    apply StructuralCongruence.par_perm
    exact List.Perm.cons _ (List.perm_append_comm (l₁ := [receive allocatorReply.term bodyCode.term])
      (l₂ := [server allocatorSelf allocatorState allocatorRequest, stateToken allocatorState seed]))
  exact ⟨path.transport before (.refl _)⟩

/-- The compiler's private-scope clause connects to the allocator's exact
received name and exact next token, including recursive scopes in the body. -/
theorem private_scope_reduces {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : World Γ 0) (seed : Nat) :
    ∃ before after : Code 0,
      compile world (nu body) = some before ∧
      compile (allocatedWorld world seed) body = some after ∧
      Nonempty (ReducesN 4 (runtime before seed) (runtime after (seed + 1))) := by
  obtain ⟨bodyCode, bodyEq⟩ := compile_guarded guarded (liftWorld world)
  obtain ⟨after, afterEq, substituted⟩ := compile_closeSeed guarded (liftWorld world) seed bodyCode bodyEq
  rw [closeWorld_lift_ground] at afterEq
  have received : semanticCommSubst bodyCode.term (seedCode seed) = after.term := by
    simpa only [semanticCommSubst, seedCode_normalized, allocatedName] using substituted
  refine ⟨Code.reserve bodyCode, after, by simp [compile, nu, bodyEq], afterEq, ?_⟩
  obtain ⟨path⟩ := reserve_reduces bodyCode seed
  rw [received] at path
  have reorder : StructuralCongruence
      (parallel [server allocatorSelf allocatorState allocatorRequest,
        stateToken allocatorState (seed + 1), after.term]) (runtime after (seed + 1)) := by
    apply StructuralCongruence.par_perm
    simpa using (List.perm_append_comm
      (l₁ := [server allocatorSelf allocatorState allocatorRequest, stateToken allocatorState (seed + 1)])
      (l₂ := [after.term]))
  exact ⟨path.transport (.refl _) reorder⟩

private theorem weaken_ground_three (name : NameValue 0) :
    name.weaken.weaken.weaken.term = name.term := by
  exact (weaken_eq (weaken_eq (weaken_ground name))).trans
    ((weaken_eq (weaken_ground name)).trans (weaken_ground name))

/-- Closing the server's allocated self name restores the ordinary stored
code template; the unrelated source-request binder remains untouched. -/
theorem storedCode_installed (channel : NameValue 0) (seed : Nat)
    (ordinary : Code 1) (stored : Code 4) (storedEq : stored.term = ordinary.term) :
    semanticSubstProc 1 (allocatedName seed) (storedCode channel stored).term =
      GuardedReplication.code (allocatedName seed) channel.term ordinary.term := by
  have requestInert := channel.channel.inert 2 (allocatedName seed)
  change semanticSubstName 2 (allocatedName seed) channel.term = channel.term at requestInert
  have handlerInert := ordinary.handler.inertAbove (by omega : 1 ≤ 3) (allocatedName seed)
  change semanticSubstProc 3 (allocatedName seed) ordinary.term = ordinary.term at handlerInert
  simp only [storedCode, Code.listen, Code.triple, Code.sendName, Code.emit, Code.datum,
    weaken_ground_three, storedEq, semanticSubstProc, semanticSubstProcList]
  rw [requestInert, handlerInert]
  simp [NameValue.term, NameValue.payload, semanticSubstProc, semanticSubstName,
    semanticSubstNameMark, semanticNormalizeName,
    GuardedReplication.code, GuardedReplication.body]

/-- The compiler's installation continuation produces the actual guarded
rho server with the source-dependent handler, not a synthetic replication. -/
theorem server_install_received (channel : NameValue 0) (seed : Nat)
    (ordinary : Code 1) (handler : Code 2) (stored : Code 4)
    (handlerEq : handler.term = ordinary.term) (storedEq : stored.term = ordinary.term) :
    semanticCommSubst (waitingServer channel handler stored).term (seedCode seed) =
      GuardedReplication.idle (allocatedName seed) channel.term ordinary.term := by
  have requestInert := channel.channel.inert 0 (allocatedName seed)
  change semanticSubstName 0 (allocatedName seed) channel.term = channel.term at requestInert
  have handlerInert := ordinary.handler.inertAbove (by omega : 1 ≤ 1) (allocatedName seed)
  change semanticSubstProc 1 (allocatedName seed) ordinary.term = ordinary.term at handlerInert
  unfold semanticCommSubst
  rw [seedCode_normalized]
  change semanticSubstProc 0 (allocatedName seed) (waitingServer channel handler stored).term = _
  simp only [waitingServer, Code.listen, Code.triple, Code.emit, weaken_ground,
    semanticSubstProc, semanticSubstProcList, handlerEq]
  rw [requestInert, storedCode_installed channel seed ordinary stored storedEq, handlerInert]
  simp [NameValue.term, semanticSubstName, semanticSubstNameMark,
    semanticNormalizeName, GuardedReplication.idle]

/-- A source persistent receiver's own compiler result installs a retained
core-rho server through exactly four allocator/client communications. -/
theorem persistent_install_reduces {Γ : Ctx sig} (channel : Name Γ)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : World Γ 0) (seed : Nat) :
    ∃ before : Code 0, ∃ ordinary : Code 1,
      compile world (rep (inp1 channel body)) = some before ∧
      compile (liftWorld world) body = some ordinary ∧
      Nonempty (ReducesN 4 (runtime before seed)
        (parallel [server allocatorSelf allocatorState allocatorRequest,
          stateToken allocatorState (seed + 1),
          GuardedReplication.idle (allocatedName seed) (evalName world channel).term ordinary.term])) := by
  obtain ⟨ordinary, ordinaryEq⟩ := compile_guarded guarded (liftWorld world)
  obtain ⟨handler, handlerEq⟩ := compile_guarded guarded (serverHandlerWorld world)
  obtain ⟨stored, storedEq⟩ := compile_guarded guarded (storedHandlerWorld world)
  obtain ⟨handlerSame, storedSame⟩ := serverHandler_same guarded world ordinary handler stored
    ordinaryEq handlerEq storedEq
  refine ⟨Code.reserve (waitingServer (evalName world channel) handler stored), ordinary,
    by simp [compile, rep, inp1, handlerEq, storedEq], ordinaryEq, ?_⟩
  obtain ⟨path⟩ := reserve_reduces (waitingServer (evalName world channel) handler stored) seed
  rw [server_install_received _ seed ordinary handler stored handlerSame storedSame] at path
  exact ⟨path⟩

/-- An installed persistent receiver releases the exact compiled source
continuation and retains the *same* allocated self-code channel. -/
theorem persistent_communication_reduces {Γ : Ctx sig} (channel : Name Γ) (datum : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : World Γ 0)
    (selfSeed datumSeed : Nat) (datumEq : world datum = .allocated datumSeed)
    (ordinary : Code 1) (ordinaryEq : compile (liftWorld world) body = some ordinary) :
    ∃ after : Code 0,
      compile world (inst body (.var datum)) = some after ∧
      Nonempty (ReducesN 2
        (parallel [send (evalName world channel).term (seedCode datumSeed),
          GuardedReplication.idle (allocatedName selfSeed) (evalName world channel).term ordinary.term])
        (parallel [GuardedReplication.idle (allocatedName selfSeed) (evalName world channel).term ordinary.term,
          after.term])) := by
  obtain ⟨after, afterEq, received⟩ := continuation_received guarded world datum datumSeed datumEq ordinary ordinaryEq
  obtain ⟨path⟩ := Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers.request_reduces
    ((NameValue.allocated selfSeed : NameValue 0).channel) (evalName world channel).channel ordinary.handler
    (seedCode datumSeed)
  change ReducesN 2
    (parallel [send (evalName world channel).term (seedCode datumSeed),
      GuardedReplication.idle (allocatedName selfSeed) (evalName world channel).term ordinary.term])
    (parallel [GuardedReplication.idle (allocatedName selfSeed) (evalName world channel).term ordinary.term,
      semanticCommSubst ordinary.term (seedCode datumSeed)]) at path
  rw [received] at path
  exact ⟨after, afterEq, ⟨path⟩⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryExecution
