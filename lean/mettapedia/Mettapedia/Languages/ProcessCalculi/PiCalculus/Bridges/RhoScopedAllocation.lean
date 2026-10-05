import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers

/-!
# A stateful name allocator implemented in the rho core

One guarded server receives a reply address and then consumes the current
seed token. It returns the quoted seed and replaces the token with code whose
quote is the next left increment. The same waiting server is retained.
Each selected request uses three core communications: receipt, rearming, and
the seed transfer. No restriction or replication primitive participates.

The generated names are pairwise inequivalent under the existing rho
equations. This establishes non-repetition within the allocator's stream;
privacy from external observers requires a separate namespace contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint

abbrev zero : Pattern := .apply "PZero" []

/-- Code for the allocator's seed: the next code sends zero on the previous
seed's quoted name. -/
def seedCode : Nat → Pattern
  | 0 => zero
  | index + 1 => send (.apply "NQuote" [seedCode index]) zero

def allocatedName (index : Nat) : Pattern := .apply "NQuote" [seedCode index]

theorem seedCode_typed (free : FreeSortContext) (index : Nat) :
    ProcWellSorted rhoReflectivePresentation free [] (seedCode index) := by
  induction index with
  | zero => exact .unit
  | succ index ih => exact .output (.quote ih) .unit

theorem seedCode_safe (index depth : Nat) :
    binderSafeAt "NQuote" depth (seedCode index) = true := by
  induction index generalizing depth with
  | zero => rfl
  | succ index ih => simp [seedCode, binderSafeAt, binderSafeListAt, ih]

private theorem seedCode_not_drop (index : Nat) (name : Pattern) :
    seedCode index ≠ .apply "PDrop" [name] := by
  cases index <;> simp [seedCode]

theorem seedCode_normalized (index : Nat) :
    semanticNormalizeProc (seedCode index) = seedCode index := by
  induction index with
  | zero => rfl
  | succ index ih =>
      change semanticNormalizeProc (send (.apply "NQuote" [seedCode index]) zero) = _
      rw [semanticNormalizeProc.eq_3,
        semanticNormalizeName.eq_4 _ (fun name equality => seedCode_not_drop index name equality), ih]
      rfl

/-- The next generated name has one more input/output constructor in its
quoted code. This measure is invariant under the rho equations. -/
theorem seedCode_ioCount (index : Nat) : ioCount (seedCode index) = index := by
  induction index with
  | zero => simp [seedCode, zero, ioCount]
  | succ index ih => simp [seedCode, send, zero, ioCount, ih, Nat.add_comm]

theorem allocatedName_ioCount (index : Nat) : ioCount (allocatedName index) = index := by
  simp [allocatedName, ioCount, seedCode_ioCount]

/-- Allocations at different stream positions cannot be name-equivalent
through rho structural congruence. -/
theorem allocatedName_equiv_iff (first second : Nat) :
    RhoCalculus.StructuralCongruence (allocatedName first) (allocatedName second) ↔
      first = second := by
  constructor
  · intro equations
    simpa [allocatedName_ioCount] using ioCount_SC equations
  · rintro rfl
    exact .refl _

theorem allocatedName_normalized (index : Nat) :
    semanticNormalizeName (allocatedName index) = allocatedName index := by
  rw [allocatedName,
    semanticNormalizeName.eq_4 _ (fun name equality => seedCode_not_drop index name equality),
    seedCode_normalized]

/-- A stream starting above the communication count of every public name
remains disjoint from those names at every later allocation. -/
theorem fresh_above_namespace_bound (publicNames : List Pattern) (first index : Nat)
    (publicBound : ∀ name ∈ publicNames, ioCount name < first)
    (later : first ≤ index) :
    ∀ name ∈ publicNames,
      ¬ RhoCalculus.StructuralCongruence (allocatedName index) name := by
  intro name member equations
  have sameCount := ioCount_SC equations
  rw [allocatedName_ioCount] at sameCount
  have below := publicBound name member
  omega

/-- Previously returned names are disjoint from every later stream position. -/
theorem fresh_after_prefix (index previous : Nat) (earlier : previous < index) :
    ¬ RhoCalculus.StructuralCongruence (allocatedName index) (allocatedName previous) := by
  intro equations
  exact (Nat.ne_of_gt earlier) ((allocatedName_equiv_iff index previous).mp equations)

def seedChannel (free : FreeSortContext) (index : Nat) : Channel free where
  term := allocatedName index
  typed := .quote (seedCode_typed free index)
  safe := by simpa [allocatedName, binderSafeAt] using seedCode_safe index 0
  normalized := allocatedName_normalized index

section Service

variable {free : FreeSortContext}

/-- The request supplies the reply address. The inner binder supplies the
seed; these are indices one and zero respectively in its released body. -/
def allocationHandler (state : Channel free) : Handler free where
  term := receive state.term
    (parallel [send (.bvar 1) (drop 0), send state.term (send (.bvar 0) zero)])
  typed := by
    apply ProcWellSorted.input (state.typedAt ["Name"])
    apply ProcWellSorted.parallel
    exact .cons (.output (.bvar (by rfl)) (.drop (.bvar (by rfl))))
      (.cons (.output (state.typedAt ["Name", "Name"])
        (.output (.bvar (by rfl)) .unit)) .nil)
  safe := by
    simp [binderSafeAt, binderSafeListAt, state.safeAt]
  normalized := by
    simp [semanticNormalizeProc, semanticNormalizeProcList,
      semanticNormalizeName, state.normalized]

def server (self state request : Channel free) : Pattern :=
  GuardedReplication.idle self.term request.term (allocationHandler state).term

def stateToken (state : Channel free) (index : Nat) : Pattern :=
  send state.term (seedCode index)

def invocation (self state request reply : Channel free) (index : Nat) : Pattern :=
  parallel [send request.term (.apply "PDrop" [reply.term]),
    server self state request, stateToken state index]

def returned (self state request reply : Channel free) (index : Nat) : Pattern :=
  parallel [server self state request, send reply.term (seedCode index), stateToken state (index + 1)]

/-- The code awaiting the seed already remembers the received reply address. -/
def seedReceiver (state reply : Channel free) : Pattern :=
  receive state.term
    (parallel [send (.apply "NQuote" [.apply "PDrop" [reply.term]]) (drop 0),
      send state.term (send (.bvar 0) zero)])

theorem request_activated (state reply : Channel free) :
    semanticCommSubst (allocationHandler state).term (.apply "PDrop" [reply.term]) =
      seedReceiver state reply := by
  simp only [allocationHandler, seedReceiver, semanticCommSubst,
    semanticNormalizeProc, reply.normalized, semanticSubstProc, semanticSubstProcList,
    state.inert]
  simp [semanticSubstName, semanticSubstNameMark, semanticNormalizeName, zero, semanticSubstProc]

private theorem quote_drop_inert (channel : Channel free) (index : Nat) (replacement : Pattern) :
    semanticSubstName index replacement (.apply "NQuote" [.apply "PDrop" [channel.term]]) =
      channel.term := by
  change semanticSubstName index replacement channel.term = channel.term
  exact channel.inert index replacement

theorem seed_received (state reply : Channel free) (index : Nat) :
    semanticCommSubst
      (parallel [send (.apply "NQuote" [.apply "PDrop" [reply.term]]) (drop 0),
        send state.term (send (.bvar 0) zero)]) (seedCode index) =
      parallel [send reply.term (seedCode index), stateToken state (index + 1)] := by
  simp only [semanticCommSubst, seedCode_normalized, semanticSubstProc, semanticSubstProcList,
    quote_drop_inert, state.inert]
  simp [semanticSubstName, semanticSubstNameMark,
    semanticNormalizeName, stateToken, seedCode, zero, semanticSubstProc]

theorem seedReceiver_typed (state reply : Channel free) :
    ProcWellSorted rhoReflectivePresentation free [] (seedReceiver state reply) := by
  rw [← request_activated]
  exact ((allocationHandler state).activated_typed_safe
    (ProcWellSorted.drop reply.typed) (by
      simp [binderSafeAt, binderSafeListAt, reply.safe])).1

theorem seedReceiver_safe (state reply : Channel free) :
    binderSafeAt "NQuote" 0 (seedReceiver state reply) = true := by
  rw [← request_activated]
  exact ((allocationHandler state).activated_typed_safe
    (ProcWellSorted.drop reply.typed) (by
      simp [binderSafeAt, binderSafeListAt, reply.safe])).2

theorem invocation_typed (self state request reply : Channel free) (index : Nat) :
    ProcWellSorted rhoReflectivePresentation free [] (invocation self state request reply index) :=
  .parallel (.cons (.output request.typed (.drop reply.typed))
    (.cons (idle_typed self request (allocationHandler state))
      (.cons (.output state.typed (seedCode_typed free index)) .nil)))

theorem invocation_safe (self state request reply : Channel free) (index : Nat) :
    binderSafeAt "NQuote" 0 (invocation self state request reply index) = true := by
  simp [invocation, server, stateToken, binderSafeAt, binderSafeListAt,
    request.safe, reply.safe, state.safe, seedCode_safe,
    idle_safe self request (allocationHandler state)]

/-- The state transfer has a separately checked authored COMM, retaining the
same guarded server in the residual bag. -/
theorem seed_authored (self state request reply : Channel free) (index : Nat) :
    RhoStepAt 1
      (parallel [server self state request, seedReceiver state reply, stateToken state index])
      (parallel [parallel [send reply.term (seedCode index), stateToken state (index + 1)],
        server self state request]) := by
  have bodyTyped := (rho_input_wellSorted_inv (seedReceiver_typed state reply)).2.2
  have fired := authored_comm_at
    (elements := [server self state request, seedReceiver state reply, stateToken state index])
    (inputIndex := 1) (outputIndex := 1) (by simp) (by simp)
    (by rfl) (by rfl) bodyTyped (seedCode_typed free index)
  simpa [seed_received state reply index] using fired

/-- The first request firing retains the old seed token untouched. -/
theorem request_authored (self state request reply : Channel free) (index : Nat) :
    RhoStepAt 1 (invocation self state request reply index)
      (parallel [RhoScopedServers.requestStage self request (allocationHandler state)
        (.apply "PDrop" [reply.term]), stateToken state index]) := by
  have bodyTyped :=
    (rho_input_wellSorted_inv (idle_typed self request (allocationHandler state))).2.2
  have fired := authored_comm_at
    (elements := [send request.term (.apply "PDrop" [reply.term]),
      server self state request, stateToken state index])
    (inputIndex := 1) (outputIndex := 0) (by simp) (by simp)
    (by rfl) (by rfl) bodyTyped (ProcWellSorted.drop reply.typed)
  simpa [invocation, RhoScopedServers.requestStage,
    RhoScopedServers.request_received self request (allocationHandler state),
    rhoReflectivePresentation] using fired

/-- The rearming state retains both the waiting seed receiver and the exact
old state token as separate parallel occurrences. -/
def rearmState (self state request reply : Channel free) (index : Nat) : Pattern :=
  parallel [send self.term
      (GuardedReplication.code self.term request.term (allocationHandler state).term),
    GuardedReplication.code self.term request.term (allocationHandler state).term,
    seedReceiver state reply, stateToken state index]

theorem rearm_authored (self state request reply : Channel free) (index : Nat) :
    RhoStepAt 1 (rearmState self state request reply index)
      (parallel [server self state request, seedReceiver state reply, stateToken state index]) := by
  have bodyTyped :=
    (rho_input_wellSorted_inv (code_typed self request (allocationHandler state))).2.2
  have fired := authored_comm_at
    (elements := [send self.term
        (GuardedReplication.code self.term request.term (allocationHandler state).term),
      GuardedReplication.code self.term request.term (allocationHandler state).term,
      seedReceiver state reply, stateToken state index])
    (inputIndex := 1) (outputIndex := 0) (by simp) (by simp)
    (by rfl) (by rfl) bodyTyped (code_typed self request (allocationHandler state))
  simpa [rearmState, server,
    code_received self request (allocationHandler state)] using fired

theorem rearmState_typed (self state request reply : Channel free) (index : Nat) :
    ProcWellSorted rhoReflectivePresentation free [] (rearmState self state request reply index) :=
  .parallel (.cons (.output self.typed (code_typed self request (allocationHandler state)))
    (.cons (code_typed self request (allocationHandler state))
      (.cons (seedReceiver_typed state reply)
        (.cons (.output state.typed (seedCode_typed free index)) .nil))))

theorem rearmState_safe (self state request reply : Channel free) (index : Nat) :
    binderSafeAt "NQuote" 0 (rearmState self state request reply index) = true := by
  simp [rearmState, stateToken, binderSafeAt, binderSafeListAt, self.safe, state.safe,
    code_safe self request (allocationHandler state), seedReceiver_safe, seedCode_safe]

/-- Three authored firings, linked through rho's proved canonical section,
return the supplied seed and the next token at the supplied final endpoint. -/
theorem request_canonical (self state request reply : Channel free) (index : Nat) :
    ∃ first second,
      CanonicalFiring (Canonical.canonicalize (invocation self state request reply index)) first ∧
      CanonicalFiring first second ∧
      CanonicalFiring second (Canonical.canonicalize (returned self state request reply index)) := by
  have payloadTyped : ProcWellSorted rhoReflectivePresentation free []
      (.apply "PDrop" [reply.term]) := .drop reply.typed
  have payloadSafe : binderSafeAt "NQuote" 0 (.apply "PDrop" [reply.term]) = true := by
    simpa [binderSafeAt, binderSafeListAt] using reply.safe
  have oldTokenTyped : ProcWellSorted rhoReflectivePresentation free [] (stateToken state index) :=
    .output state.typed (seedCode_typed free index)
  have firstTargetTyped : ProcWellSorted rhoReflectivePresentation free []
      (parallel [RhoScopedServers.requestStage self request (allocationHandler state)
        (.apply "PDrop" [reply.term]), stateToken state index]) :=
    .parallel (.cons (requestStage_typed self request (allocationHandler state) payloadTyped payloadSafe)
      (.cons oldTokenTyped .nil))
  have firstEquations : RhoCalculus.StructuralCongruence
      (parallel [RhoScopedServers.requestStage self request (allocationHandler state)
        (.apply "PDrop" [reply.term]), stateToken state index])
      (rearmState self state request reply index) := by
    simp only [RhoScopedServers.requestStage, request_activated]
    exact RhoCalculus.Context.par_flatten_head _ _
  have firstCanonical := Canonical.canonicalize_eq_of_structuralCongruence firstEquations
    (rhoProcWellSorted_hashSetFree firstTargetTyped)
    (rhoProcWellSorted_hashSetFree (rearmState_typed self state request reply index))
  obtain ⟨firstContractum, first, firstEndpoint⟩ := canonicalStep_complete_of_rhoStep
    (invocation_typed self state request reply index) (invocation_safe self state request reply index)
    ⟨1, request_authored self state request reply index⟩
  obtain ⟨secondContractum, second, secondEndpoint⟩ := canonicalStep_complete_of_rhoStep
    (rearmState_typed self state request reply index) (rearmState_safe self state request reply index)
    ⟨1, rearm_authored self state request reply index⟩
  have secondSourceTyped : ProcWellSorted rhoReflectivePresentation free []
      (parallel [server self state request, seedReceiver state reply, stateToken state index]) :=
    .parallel (.cons (idle_typed self request (allocationHandler state))
      (.cons (seedReceiver_typed state reply) (.cons oldTokenTyped .nil)))
  have secondSourceSafe : binderSafeAt "NQuote" 0
      (parallel [server self state request, seedReceiver state reply, stateToken state index]) = true := by
    simp [server, stateToken, binderSafeAt, binderSafeListAt, state.safe, seedCode_safe,
      idle_safe self request (allocationHandler state), seedReceiver_safe]
  obtain ⟨thirdContractum, third, thirdEndpoint⟩ := canonicalStep_complete_of_rhoStep
    secondSourceTyped secondSourceSafe ⟨1, seed_authored self state request reply index⟩
  have thirdEquations : RhoCalculus.StructuralCongruence
      (parallel [parallel [send reply.term (seedCode index), stateToken state (index + 1)],
        server self state request]) (returned self state request reply index) := by
    refine .trans _ _ _ (RhoCalculus.Context.par_flatten_head _ _) ?_
    apply RhoCalculus.StructuralCongruence.par_perm
    exact List.perm_append_comm
  have nextTokenTyped : ProcWellSorted rhoReflectivePresentation free [] (stateToken state (index + 1)) :=
    .output state.typed (seedCode_typed free (index + 1))
  have replyTyped : ProcWellSorted rhoReflectivePresentation free [] (send reply.term (seedCode index)) :=
    .output reply.typed (seedCode_typed free index)
  have thirdTargetTyped : ProcWellSorted rhoReflectivePresentation free []
      (parallel [parallel [send reply.term (seedCode index), stateToken state (index + 1)],
        server self state request]) :=
    .parallel (.cons (.parallel (.cons replyTyped (.cons nextTokenTyped .nil)))
      (.cons (idle_typed self request (allocationHandler state)) .nil))
  have returnedTyped : ProcWellSorted rhoReflectivePresentation free [] (returned self state request reply index) :=
    .parallel (.cons (idle_typed self request (allocationHandler state))
      (.cons replyTyped (.cons nextTokenTyped .nil)))
  have thirdCanonical := Canonical.canonicalize_eq_of_structuralCongruence thirdEquations
    (rhoProcWellSorted_hashSetFree thirdTargetTyped) (rhoProcWellSorted_hashSetFree returnedTyped)
  exact ⟨_, _, ⟨firstContractum, first, firstEndpoint.trans firstCanonical⟩,
    ⟨secondContractum, second, secondEndpoint⟩,
    ⟨thirdContractum, third, thirdEndpoint.trans thirdCanonical⟩⟩

/-- One selected request consumes exactly three ordinary core communications,
returns this seed, and replaces the unique state token with the next seed. -/
theorem request_reduces (self state request reply : Channel free) (index : Nat) :
    Nonempty (ReducesN 3 (invocation self state request reply index)
      (returned self state request reply index)) := by
  obtain ⟨firstTwo⟩ := RhoScopedServers.request_reduces self request (allocationHandler state)
    (.apply "PDrop" [reply.term])
  have framed := firstTwo.splice [] [stateToken state index]
  rw [request_activated state reply] at framed
  have raw := RhoCalculus.Reduction.Reduces.comm (n := state.term) (q := seedCode index)
    (p := parallel [send (.apply "NQuote" [.apply "PDrop" [reply.term]]) (drop 0),
      send state.term (send (.bvar 0) zero)]) (rest := [server self state request])
  rw [seed_received state reply index] at raw
  have before : RhoCalculus.StructuralCongruence
      (parallel [server self state request, seedReceiver state reply, stateToken state index])
      (parallel [stateToken state index, seedReceiver state reply, server self state request]) := by
    apply RhoCalculus.StructuralCongruence.par_perm
    simpa using (List.reverse_perm
      [server self state request, seedReceiver state reply, stateToken state index]).symm
  have after : RhoCalculus.StructuralCongruence
      (parallel [parallel [send reply.term (seedCode index), stateToken state (index + 1)],
        server self state request]) (returned self state request reply index) := by
    refine .trans _ _ _ (RhoCalculus.Context.par_flatten_head _ _) ?_
    apply RhoCalculus.StructuralCongruence.par_perm
    exact List.perm_append_comm
  have third : CoreReduces
      (parallel [server self state request, seedReceiver state reply, stateToken state index])
      (returned self state request reply index) := .equiv before raw after
  exact ⟨reducesN_concat framed (.succ third (.zero _))⟩

/-- A client requests a name and binds the answer in its own scoped body. -/
def clientInvocation (self state request reply : Channel free) (body : Handler free)
    (index : Nat) : Pattern :=
  parallel [send request.term (.apply "PDrop" [reply.term]),
    server self state request, stateToken state index, receive reply.term body.term]

def clientReturned (self state request : Channel free) (body : Handler free)
    (index : Nat) : Pattern :=
  parallel [server self state request, stateToken state (index + 1),
    semanticCommSubst body.term (seedCode index)]

/-- The client's reply communication is an actual authored rule application
and opens its supplied continuation with this allocator's supplied seed. -/
theorem client_reply_authored (self state request reply : Channel free)
    (body : Handler free) (index : Nat) :
    RhoStepAt 1
      (parallel [server self state request, send reply.term (seedCode index),
        stateToken state (index + 1), receive reply.term body.term])
      (parallel [semanticCommSubst body.term (seedCode index),
        server self state request, stateToken state (index + 1)]) := by
  have fired := authored_comm_at
    (elements := [server self state request, send reply.term (seedCode index),
      stateToken state (index + 1), receive reply.term body.term])
    (inputIndex := 3) (outputIndex := 1) (by simp) (by simp)
    (by rfl) (by rfl) body.typed (seedCode_typed free index)
  simpa using fired

/-- The service and the client's binding use four core communications. The
retained endpoint includes both the same server and the next state token. -/
theorem client_reduces (self state request reply : Channel free)
    (body : Handler free) (index : Nat) :
    Nonempty (ReducesN 4 (clientInvocation self state request reply body index)
      (clientReturned self state request body index)) := by
  obtain ⟨firstThree⟩ := request_reduces self state request reply index
  have framed := firstThree.splice [] [receive reply.term body.term]
  have raw := RhoCalculus.Reduction.Reduces.comm
    (n := reply.term) (q := seedCode index) (p := body.term)
    (rest := [server self state request, stateToken state (index + 1)])
  have before : RhoCalculus.StructuralCongruence
      (parallel [server self state request, send reply.term (seedCode index),
        stateToken state (index + 1), receive reply.term body.term])
      (parallel [send reply.term (seedCode index), receive reply.term body.term,
        server self state request, stateToken state (index + 1)]) := by
    apply RhoCalculus.StructuralCongruence.par_perm
    exact (List.Perm.swap _ _ _).trans
      (List.Perm.cons _ (List.perm_middle (a := receive reply.term body.term)
        (l₁ := [server self state request, stateToken state (index + 1)]) (l₂ := [])))
  have after : RhoCalculus.StructuralCongruence
      (parallel [semanticCommSubst body.term (seedCode index),
        server self state request, stateToken state (index + 1)])
      (clientReturned self state request body index) := by
    apply RhoCalculus.StructuralCongruence.par_perm
    simpa using (List.perm_append_comm (l₁ := [semanticCommSubst body.term (seedCode index)])
      (l₂ := [server self state request, stateToken state (index + 1)]))
  have fourth : CoreReduces
      (parallel [server self state request, send reply.term (seedCode index),
        stateToken state (index + 1), receive reply.term body.term])
      (clientReturned self state request body index) := .equiv before raw after
  exact ⟨reducesN_concat framed (.succ fourth (.zero _))⟩

end Service

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation
