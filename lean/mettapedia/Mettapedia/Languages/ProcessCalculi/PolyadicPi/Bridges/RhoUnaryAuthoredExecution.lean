import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadback
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderExecution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextPaths

/-!
# Selected authored scope and persistent-service blocks

The primitive selections are constructed directly from the core rho headers.
The four allocation communications preserve every supplied frame occurrence,
retain the allocator, and deliver the exact issued seed to the supplied client.
These finite paths belong to the existing equation-saturated authored theory;
their step counts do not rely on the separate handwritten reduction relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAuthoredExecution

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryClosing RhoUnaryNaturality
open RhoUnaryEnvironment RhoUnaryExecution RhoUnaryWorld RhoUnaryActive RhoUnaryReadback
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open RhoScopedServers RhoScopedAllocation RhoEncodingTyping

private noncomputable def infrastructure (activity : Activity []) : Header :=
  activity.header (RhoUnaryWorld.initial ([] : Ctx sig)).world

private theorem infrastructure_typed (activity : Activity []) :
    (infrastructure activity).Typed rhoAtomicNameContext :=
  Activity.header_typed (RhoUnaryWorld.initial ([] : Ctx sig)).world activity

private theorem infrastructure_safe (activity : Activity []) :
    (infrastructure activity).Safe := Activity.header_safe (RhoUnaryWorld.initial ([] : Ctx sig)).world activity

private noncomputable def client (body : Code 1) : Header := .input allocatorReply.term body.term

private theorem client_typed (body : Code 1) : (client body).Typed rhoAtomicNameContext :=
  ⟨allocatorReply.typed, body.typed⟩

private theorem client_safe (body : Code 1) : (client body).Safe :=
  ⟨allocatorReply.safe, body.safe⟩

private noncomputable def start (body : Code 1) (seed : Nat) (frame : List Header) : List Header :=
  [infrastructure .request, client body, infrastructure .allocatorReady,
    infrastructure (.token seed)] ++ frame

private noncomputable def requestSent (body : Code 1) (seed : Nat) (frame : List Header) : List Header :=
  [infrastructure .allocatorSendCode, infrastructure .allocatorRearm,
    infrastructure .seedInput, client body, infrastructure (.token seed)] ++ frame

private noncomputable def rearmed (body : Code 1) (seed : Nat) (frame : List Header) : List Header :=
  [infrastructure .allocatorReady, infrastructure .seedInput, client body,
    infrastructure (.token seed)] ++ frame

private noncomputable def issued (body : Code 1) (seed : Nat) (frame : List Header) : List Header :=
  [infrastructure (.reply seed), infrastructure (.token (seed + 1)),
    infrastructure .allocatorReady, client body] ++ frame

private theorem start_typed (body : Code 1) (seed : Nat) (frame : List Header)
    (typed : ∀ head ∈ frame, head.Typed rhoAtomicNameContext) :
    ∀ head ∈ start body seed frame, head.Typed rhoAtomicNameContext := by
  intro head member
  simp only [start, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl) | member
  · exact infrastructure_typed _
  · exact client_typed _
  · exact infrastructure_typed _
  · exact infrastructure_typed _
  · exact typed head member

private theorem start_safe (body : Code 1) (seed : Nat) (frame : List Header)
    (safe : ∀ head ∈ frame, head.Safe) : ∀ head ∈ start body seed frame, head.Safe := by
  intro head member
  simp only [start, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl) | member
  · exact infrastructure_safe _
  · exact client_safe _
  · exact infrastructure_safe _
  · exact infrastructure_safe _
  · exact safe head member

private theorem requestSent_typed (body : Code 1) (seed : Nat) (frame : List Header)
    (typed : ∀ head ∈ frame, head.Typed rhoAtomicNameContext) :
    ∀ head ∈ requestSent body seed frame, head.Typed rhoAtomicNameContext := by
  intro head member
  simp only [requestSent, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl | rfl) | member
  · exact infrastructure_typed _
  · exact infrastructure_typed _
  · exact infrastructure_typed _
  · exact client_typed _
  · exact infrastructure_typed _
  · exact typed head member

private theorem requestSent_safe (body : Code 1) (seed : Nat) (frame : List Header)
    (safe : ∀ head ∈ frame, head.Safe) : ∀ head ∈ requestSent body seed frame, head.Safe := by
  intro head member
  simp only [requestSent, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl | rfl) | member
  · exact infrastructure_safe _
  · exact infrastructure_safe _
  · exact infrastructure_safe _
  · exact client_safe _
  · exact infrastructure_safe _
  · exact safe head member

private theorem rearmed_typed (body : Code 1) (seed : Nat) (frame : List Header)
    (typed : ∀ head ∈ frame, head.Typed rhoAtomicNameContext) :
    ∀ head ∈ rearmed body seed frame, head.Typed rhoAtomicNameContext := by
  intro head member
  simp only [rearmed, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl) | member
  · exact infrastructure_typed _
  · exact infrastructure_typed _
  · exact client_typed _
  · exact infrastructure_typed _
  · exact typed head member

private theorem rearmed_safe (body : Code 1) (seed : Nat) (frame : List Header)
    (safe : ∀ head ∈ frame, head.Safe) : ∀ head ∈ rearmed body seed frame, head.Safe := by
  intro head member
  simp only [rearmed, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl) | member
  · exact infrastructure_safe _
  · exact infrastructure_safe _
  · exact client_safe _
  · exact infrastructure_safe _
  · exact safe head member

private theorem issued_typed (body : Code 1) (seed : Nat) (frame : List Header)
    (typed : ∀ head ∈ frame, head.Typed rhoAtomicNameContext) :
    ∀ head ∈ issued body seed frame, head.Typed rhoAtomicNameContext := by
  intro head member
  simp only [issued, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl) | member
  · exact infrastructure_typed _
  · exact infrastructure_typed _
  · exact infrastructure_typed _
  · exact client_typed _
  · exact typed head member

private theorem issued_safe (body : Code 1) (seed : Nat) (frame : List Header)
    (safe : ∀ head ∈ frame, head.Safe) : ∀ head ∈ issued body seed frame, head.Safe := by
  intro head member
  simp only [issued, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl) | member
  · exact infrastructure_safe _
  · exact infrastructure_safe _
  · exact infrastructure_safe _
  · exact client_safe _
  · exact safe head member

private noncomputable def requestSelection (body : Code 1) (seed : Nat) (frame : List Header) :
    Selection (start body seed frame) where
  inputIndex := 2
  inputBound := by simp [start]
  outputIndex := 0
  outputBound := by simp [start]
  inputChannel := allocatorRequest.term
  body := RhoScopedServers.parallel [send allocatorSelf.term
    (GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term),
    GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term,
    (allocationHandler allocatorState).term]
  outputChannel := allocatorRequest.term
  payload := (NameValue.reserved Reserved.reply : NameValue 0).payload
  inputEq := rfl
  outputEq := rfl
  channels := rfl

private noncomputable def rearmSelection (body : Code 1) (seed : Nat) (frame : List Header) :
    Selection (requestSent body seed frame) where
  inputIndex := 1
  inputBound := by simp [requestSent]
  outputIndex := 0
  outputBound := by simp [requestSent]
  inputChannel := allocatorSelf.term
  body := GuardedReplication.body allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term
  outputChannel := allocatorSelf.term
  payload := GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term
  inputEq := rfl
  outputEq := rfl
  channels := rfl

private noncomputable def tokenSelection (body : Code 1) (seed : Nat) (frame : List Header) :
    Selection (rearmed body seed frame) where
  inputIndex := 1
  inputBound := by simp [rearmed]
  outputIndex := 2
  outputBound := by simp [rearmed]
  inputChannel := allocatorState.term
  body := RhoScopedServers.parallel [send (.apply "NQuote" [.apply "PDrop" [allocatorReply.term]]) (drop 0),
    send allocatorState.term (send (.bvar 0) RhoScopedAllocation.zero)]
  outputChannel := allocatorState.term
  payload := seedCode seed
  inputEq := rfl
  outputEq := rfl
  channels := rfl

private noncomputable def replySelection (body : Code 1) (seed : Nat) (frame : List Header) :
    Selection (issued body seed frame) where
  inputIndex := 3
  inputBound := by simp [issued]
  outputIndex := 0
  outputBound := by simp [issued]
  inputChannel := allocatorReply.term
  body := body.term
  outputChannel := allocatorReply.term
  payload := seedCode seed
  inputEq := rfl
  outputEq := rfl
  channels := rfl

private theorem request_endpoint (body : Code 1) (seed : Nat) (frame : List Header) :
    StructuralCongruence (requestSelection body seed frame).contractum
      (HeaderInversion.parallel (requestSent body seed frame)) := by
  change StructuralCongruence
    (RhoScopedServers.parallel (semanticCommSubst _ _ ::
      (client body :: infrastructure (.token seed) :: frame).map Header.pattern)) _
  dsimp only [requestSelection]
  rw [RhoUnaryPhase.allocator_received (RhoUnaryWorld.initial ([] : Ctx sig)).world]
  exact Context.par_flatten_head _ _

private theorem rearm_endpoint (body : Code 1) (seed : Nat) (frame : List Header) :
    (rearmSelection body seed frame).contractum = HeaderInversion.parallel (rearmed body seed frame) := by
  change RhoScopedServers.parallel (semanticCommSubst _ _ ::
    (infrastructure .seedInput :: client body :: infrastructure (.token seed) :: frame).map Header.pattern) = _
  dsimp only [rearmSelection]
  rw [RhoUnaryPhase.allocator_rearmed (RhoUnaryWorld.initial ([] : Ctx sig)).world]
  rfl

private theorem token_endpoint (body : Code 1) (seed : Nat) (frame : List Header) :
    StructuralCongruence (tokenSelection body seed frame).contractum
      (HeaderInversion.parallel (issued body seed frame)) := by
  change StructuralCongruence
    (RhoScopedServers.parallel (semanticCommSubst _ _ ::
      (infrastructure .allocatorReady :: client body :: frame).map Header.pattern)) _
  dsimp only [tokenSelection]
  rw [RhoUnaryPhase.token_received (RhoUnaryWorld.initial ([] : Ctx sig)).world seed]
  exact Context.par_flatten_head _ _

/-- The exact activated handler, retained service and untouched frame form
the final supplied target of the allocation block. -/
noncomputable def deliveredProcess (body : Code 1) (seed : Nat) (frame : List Header)
    (typed : ∀ head ∈ frame, head.Typed rhoAtomicNameContext)
    (safe : ∀ head ∈ frame, head.Safe) : TargetProcess :=
  HeaderExecution.contractumProcess (issued body seed frame)
    (issued_typed body seed frame typed) (issued_safe body seed frame safe)
    (replySelection body seed frame)

/-- One selected allocation has four actual authored receipts, including
the client's seed receipt. All frame occurrences remain present literally. -/
theorem allocation_block (body : Code 1) (seed : Nat) (frame : List Header)
    (typed : ∀ head ∈ frame, head.Typed rhoAtomicNameContext)
    (safe : ∀ head ∈ frame, head.Safe) :
    ∃ path : ExecutionPath Target
      (HeaderExecution.headerProcess (start body seed frame)
        (start_typed body seed frame typed) (start_safe body seed frame safe))
      (deliveredProcess body seed frame typed safe), path.length = 4 := by
  have first := HeaderExecution.supplied_selection_step (start body seed frame)
    (start_typed body seed frame typed) (start_safe body seed frame safe)
    (requestSelection body seed frame)
    (HeaderExecution.headerProcess (start body seed frame)
      (start_typed body seed frame typed) (start_safe body seed frame safe))
    (HeaderExecution.headerProcess (requestSent body seed frame)
      (requestSent_typed body seed frame typed) (requestSent_safe body seed frame safe))
    (.refl _) (request_endpoint body seed frame)
  have second := HeaderExecution.supplied_selection_step (requestSent body seed frame)
    (requestSent_typed body seed frame typed) (requestSent_safe body seed frame safe)
    (rearmSelection body seed frame)
    (HeaderExecution.headerProcess (requestSent body seed frame)
      (requestSent_typed body seed frame typed) (requestSent_safe body seed frame safe))
    (HeaderExecution.headerProcess (rearmed body seed frame)
      (rearmed_typed body seed frame typed) (rearmed_safe body seed frame safe))
    (.refl _) (.alpha _ _ (rearm_endpoint body seed frame))
  have third := HeaderExecution.supplied_selection_step (rearmed body seed frame)
    (rearmed_typed body seed frame typed) (rearmed_safe body seed frame safe)
    (tokenSelection body seed frame)
    (HeaderExecution.headerProcess (rearmed body seed frame)
      (rearmed_typed body seed frame typed) (rearmed_safe body seed frame safe))
    (HeaderExecution.headerProcess (issued body seed frame)
      (issued_typed body seed frame typed) (issued_safe body seed frame safe))
    (.refl _) (token_endpoint body seed frame)
  have fourth := HeaderExecution.selection_step (issued body seed frame)
    (issued_typed body seed frame typed) (issued_safe body seed frame safe)
    (replySelection body seed frame)
  exact ⟨.cons ⟨first⟩ (.cons ⟨second⟩ (.cons ⟨third⟩ (.cons ⟨fourth⟩ (.refl _)))), rfl⟩

/-- The literal guest reservation is accompanied by the same service and
token. The frame is an occurrence list, so repeated headers remain repeated. -/
def reservation (body : Code 1) (seed : Nat) (frame : List Header) : Pattern :=
  RhoScopedServers.parallel ([(Code.reserve body).term,
    server allocatorSelf allocatorState allocatorRequest,
    stateToken allocatorState seed] ++ frame.map Header.pattern)

/-- Delivery activates the supplied handler beside the advancing allocator. -/
def delivery (body : Code 1) (seed : Nat) (frame : List Header) : Pattern :=
  RhoScopedServers.parallel ([semanticCommSubst body.term (seedCode seed),
    server allocatorSelf allocatorState allocatorRequest,
    stateToken allocatorState (seed + 1)] ++ frame.map Header.pattern)

private theorem reservation_equation (body : Code 1) (seed : Nat) (frame : List Header) :
    StructuralCongruence (reservation body seed frame) (HeaderInversion.parallel (start body seed frame)) := by
  exact Context.par_flatten_head _ _

private theorem delivery_equation (body : Code 1) (seed : Nat) (frame : List Header) :
    StructuralCongruence (replySelection body seed frame).contractum (delivery body seed frame) := by
  apply StructuralCongruence.par_perm
  change (semanticCommSubst body.term (seedCode seed) ::
    stateToken allocatorState (seed + 1) :: server allocatorSelf allocatorState allocatorRequest ::
      frame.map Header.pattern).Perm
    (semanticCommSubst body.term (seedCode seed) ::
      server allocatorSelf allocatorState allocatorRequest :: stateToken allocatorState (seed + 1) ::
      frame.map Header.pattern)
  exact List.Perm.cons _ (List.Perm.swap _ _ _)

/-- Any independently supplied sorted representatives of the reservation
and delivery are linked by these four concrete authored communications. -/
theorem reservation_path (body : Code 1) (seed : Nat) (frame : List Header)
    (typed : ∀ head ∈ frame, head.Typed rhoAtomicNameContext)
    (safe : ∀ head ∈ frame, head.Safe) (before after : TargetProcess)
    (sourceEquation : StructuralCongruence before.1 (reservation body seed frame))
    (targetEquation : StructuralCongruence (delivery body seed frame) after.1) :
    ∃ path : ExecutionPath Target before after, path.length = 4 := by
  have first := HeaderExecution.supplied_selection_step (start body seed frame)
    (start_typed body seed frame typed) (start_safe body seed frame safe)
    (requestSelection body seed frame) before
    (HeaderExecution.headerProcess (requestSent body seed frame)
      (requestSent_typed body seed frame typed) (requestSent_safe body seed frame safe))
    (.trans _ _ _ sourceEquation (reservation_equation body seed frame))
    (request_endpoint body seed frame)
  have second := HeaderExecution.supplied_selection_step (requestSent body seed frame)
    (requestSent_typed body seed frame typed) (requestSent_safe body seed frame safe)
    (rearmSelection body seed frame)
    (HeaderExecution.headerProcess (requestSent body seed frame)
      (requestSent_typed body seed frame typed) (requestSent_safe body seed frame safe))
    (HeaderExecution.headerProcess (rearmed body seed frame)
      (rearmed_typed body seed frame typed) (rearmed_safe body seed frame safe))
    (.refl _) (.alpha _ _ (rearm_endpoint body seed frame))
  have third := HeaderExecution.supplied_selection_step (rearmed body seed frame)
    (rearmed_typed body seed frame typed) (rearmed_safe body seed frame safe)
    (tokenSelection body seed frame)
    (HeaderExecution.headerProcess (rearmed body seed frame)
      (rearmed_typed body seed frame typed) (rearmed_safe body seed frame safe))
    (HeaderExecution.headerProcess (issued body seed frame)
      (issued_typed body seed frame typed) (issued_safe body seed frame safe))
    (.refl _) (token_endpoint body seed frame)
  have fourth := HeaderExecution.supplied_selection_step (issued body seed frame)
    (issued_typed body seed frame typed) (issued_safe body seed frame safe)
    (replySelection body seed frame)
    (HeaderExecution.headerProcess (issued body seed frame)
      (issued_typed body seed frame typed) (issued_safe body seed frame safe)) after
    (.refl _) (.trans _ _ _ (delivery_equation body seed frame) targetEquation)
  exact ⟨.cons ⟨first⟩ (.cons ⟨second⟩ (.cons ⟨third⟩ (.cons ⟨fourth⟩ (.refl _)))), rfl⟩

/-- Compiling a source private binder determines both endpoints of the
authored four-step allocation block, including the same next cursor token. -/
theorem private_scope_path {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : World Γ 0) (seed : Nat) :
    ∃ before after : Code 0,
      compile world (nu body) = some before ∧
      compile (allocatedWorld world seed) body = some after ∧
      ∃ path : ExecutionPath Target (runtimeProcess before seed) (runtimeProcess after (seed + 1)),
        path.length = 4 := by
  obtain ⟨bodyCode, compiled⟩ := compile_guarded guarded (liftWorld world)
  obtain ⟨after, afterEq, substituted⟩ := compile_closeSeed guarded (liftWorld world) seed bodyCode compiled
  rw [closeWorld_lift_ground] at afterEq
  have received : semanticCommSubst bodyCode.term (seedCode seed) = after.term := by
    simpa only [semanticCommSubst, seedCode_normalized, allocatedName] using substituted
  refine ⟨Code.reserve bodyCode, after, by simp [compile, nu, compiled], afterEq, ?_⟩
  apply reservation_path bodyCode seed [] (by simp) (by simp)
    (runtimeProcess (Code.reserve bodyCode) seed) (runtimeProcess after (seed + 1))
  · exact .refl _
  · simp only [delivery, List.map_nil, List.append_nil, received]
    exact .refl _

/-- Nested private binders compose their actual implementation receipts.
The two contexts receive consecutive, distinct allocator seeds. -/
theorem nested_private_scope_path {Γ : Ctx sig} {body : Proc (.nm :: .nm :: Γ)}
    (guarded : GuardedUnary body) (world : World Γ 0) (seed : Nat) :
    ∃ before after : Code 0,
      compile world (nu (nu body)) = some before ∧
      compile (allocatedWorld (allocatedWorld world seed) (seed + 1)) body = some after ∧
      ∃ path : ExecutionPath Target (runtimeProcess before seed) (runtimeProcess after (seed + 2)),
        path.length = 8 := by
  obtain ⟨before, middle, beforeEq, middleEq, first, firstCount⟩ :=
    private_scope_path (.nu guarded) world seed
  obtain ⟨middle', after, middleEq', afterEq, second, secondCount⟩ :=
    private_scope_path guarded (allocatedWorld world seed) (seed + 1)
  have same : middle = middle' := Option.some.inj (middleEq.symm.trans middleEq')
  subst middle'
  refine ⟨before, after, beforeEq, afterEq, first.append second, ?_⟩
  exact (Route.length_append first second).trans
    (show first.length + second.length = 8 by rw [firstCount, secondCount])

/-- The installed guest server is actual guarded core code with the
supplied payload-dependent handler and the same live allocation service. -/
def installedRuntimeProcess (channel : NameValue 0) (self : Nat) (body : Code 1)
    (cursor : Nat) : TargetProcess := by
  refine ⟨RhoScopedServers.parallel [
    GuardedReplication.idle (allocatedName self) channel.term body.term,
    server allocatorSelf allocatorState allocatorRequest, stateToken allocatorState cursor],
    (ParameterizedRewriteSystem.process_iff _ _).mpr ⟨?_, ?_⟩⟩
  · exact .parallel (.cons (idle_typed (seedChannel rhoAtomicNameContext self) channel.channel body.handler)
      (.cons (idle_typed allocatorSelf allocatorRequest (allocationHandler allocatorState))
        (.cons (.output allocatorState.typed (seedCode_typed rhoAtomicNameContext cursor)) .nil)))
  · have guestSafe := idle_safe (seedChannel rhoAtomicNameContext self) channel.channel body.handler
    change binderSafeAt "NQuote" 0 (GuardedReplication.idle (allocatedName self) channel.term body.term) = true at guestSafe
    simp only [server, stateToken, send, binderSafeAt,
      binderSafeListAt, guestSafe,
      idle_safe allocatorSelf allocatorRequest (allocationHandler allocatorState),
      allocatorState.safe, seedCode_safe, Bool.and_self]

/-- The persistent source clause installs its own handler through four
authored communications; the self seed is the actual allocator reply. -/
theorem persistent_install_path {Γ : Ctx sig} (channel : Name Γ)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : World Γ 0) (seed : Nat) :
    ∃ before : Code 0, ∃ ordinary : Code 1,
      compile world (rep (inp1 channel body)) = some before ∧
      compile (liftWorld world) body = some ordinary ∧
      ∃ path : ExecutionPath Target (runtimeProcess before seed)
        (installedRuntimeProcess (evalName world channel) seed ordinary (seed + 1)), path.length = 4 := by
  obtain ⟨ordinary, ordinaryEq⟩ := compile_guarded guarded (liftWorld world)
  obtain ⟨handler, handlerEq⟩ := compile_guarded guarded (serverHandlerWorld world)
  obtain ⟨stored, storedEq⟩ := compile_guarded guarded (storedHandlerWorld world)
  obtain ⟨handlerSame, storedSame⟩ := serverHandler_same guarded world ordinary handler stored
    ordinaryEq handlerEq storedEq
  let waiting := waitingServer (evalName world channel) handler stored
  refine ⟨Code.reserve waiting, ordinary,
    by simp [waiting, compile, rep, inp1, handlerEq, storedEq], ordinaryEq, ?_⟩
  apply reservation_path waiting seed [] (by simp) (by simp)
    (runtimeProcess (Code.reserve waiting) seed)
    (installedRuntimeProcess (evalName world channel) seed ordinary (seed + 1))
  · exact .refl _
  · dsimp only [delivery, waiting]
    rw [server_install_received _ seed ordinary handler stored handlerSame storedSame]
    exact .refl _

private noncomputable def persistentInput (channel self : Nat) (body : Code 1) : Header :=
  .input (allocatedName channel) (RhoScopedServers.parallel [
    send (allocatedName self) (GuardedReplication.code (allocatedName self) (allocatedName channel) body.term),
    GuardedReplication.code (allocatedName self) (allocatedName channel) body.term, body.term])

private theorem persistentInput_typed (channel self : Nat) (body : Code 1) :
    (persistentInput channel self body).Typed rhoAtomicNameContext :=
  (rho_input_wellSorted_inv
    (idle_typed (seedChannel rhoAtomicNameContext self) (seedChannel rhoAtomicNameContext channel) body.handler)).2

private theorem persistentInput_safe (channel self : Nat) (body : Code 1) :
    (persistentInput channel self body).Safe := by
  have safe := idle_safe (seedChannel rhoAtomicNameContext self) (seedChannel rhoAtomicNameContext channel) body.handler
  change binderSafeAt "NQuote" 0 (persistentInput channel self body).pattern = true at safe
  change binderSafeAt "NQuote" 0 (allocatedName channel) = true ∧ binderSafeAt "NQuote" 1
    (RhoScopedServers.parallel [send (allocatedName self)
      (GuardedReplication.code (allocatedName self) (allocatedName channel) body.term),
      GuardedReplication.code (allocatedName self) (allocatedName channel) body.term, body.term]) = true
  simpa only [persistentInput, Header.pattern, binderSafeAt, binderSafeListAt,
    Bool.and_eq_true, and_true] using safe

private noncomputable def persistentHeads (channel self : Nat) (body : Code 1)
    (datum : Nat) (frame : List Header) : List Header :=
  [Header.output (allocatedName channel) (seedCode datum), persistentInput channel self body] ++ frame

private theorem persistentHeads_typed (channel self : Nat) (body : Code 1) (datum : Nat)
    (frame : List Header) (typed : ∀ head ∈ frame, head.Typed rhoAtomicNameContext) :
    ∀ head ∈ persistentHeads channel self body datum frame, head.Typed rhoAtomicNameContext := by
  intro head member
  simp only [persistentHeads, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | member
  · exact ⟨(NameValue.allocated channel : NameValue 0).typed, seedCode_typed rhoAtomicNameContext datum⟩
  · exact persistentInput_typed channel self body
  · exact typed head member

private theorem persistentHeads_safe (channel self : Nat) (body : Code 1) (datum : Nat)
    (frame : List Header) (safe : ∀ head ∈ frame, head.Safe) :
    ∀ head ∈ persistentHeads channel self body datum frame, head.Safe := by
  intro head member
  simp only [persistentHeads, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | member
  · exact ⟨(NameValue.allocated channel : NameValue 0).safe, seedCode_safe datum 0⟩
  · exact persistentInput_safe channel self body
  · exact safe head member

private noncomputable def persistentSelection (channel self : Nat) (body : Code 1)
    (datum : Nat) (frame : List Header) : Selection (persistentHeads channel self body datum frame) where
  inputIndex := 1
  inputBound := by simp [persistentHeads]
  outputIndex := 0
  outputBound := by simp [persistentHeads]
  inputChannel := allocatedName channel
  body := RhoScopedServers.parallel [
    send (allocatedName self) (GuardedReplication.code (allocatedName self) (allocatedName channel) body.term),
    GuardedReplication.code (allocatedName self) (allocatedName channel) body.term, body.term]
  outputChannel := allocatedName channel
  payload := seedCode datum
  inputEq := rfl
  outputEq := rfl
  channels := (seed_match_iff channel channel).mpr rfl

private def requestStageProcess (channel self : Nat) (body : Code 1) (datum : Nat) : TargetProcess :=
  ⟨RhoScopedServers.requestStage (seedChannel rhoAtomicNameContext self)
    (seedChannel rhoAtomicNameContext channel) body.handler (seedCode datum),
    (ParameterizedRewriteSystem.process_iff _ _).mpr
      ⟨requestStage_typed (seedChannel rhoAtomicNameContext self) (seedChannel rhoAtomicNameContext channel)
          body.handler (seedCode_typed rhoAtomicNameContext datum) (seedCode_safe datum 0),
        requestStage_safe (seedChannel rhoAtomicNameContext self) (seedChannel rhoAtomicNameContext channel)
          body.handler (seedCode_typed rhoAtomicNameContext datum) (seedCode_safe datum 0)⟩⟩

private def framedProcess (guest : TargetProcess) (frame : List Header)
    (typed : ∀ head ∈ frame, head.Typed rhoAtomicNameContext)
    (safe : ∀ head ∈ frame, head.Safe) : TargetProcess := by
  have guestFormed := (ParameterizedRewriteSystem.process_iff _ _).mp guest.2
  refine ⟨RhoScopedServers.parallel (guest.1 :: frame.map Header.pattern),
    (ParameterizedRewriteSystem.process_iff _ _).mpr ⟨?_, ?_⟩⟩
  · apply ProcWellSorted.parallel
    apply ProcListWellSorted.cons guestFormed.1
    apply procListWellSorted_iff_forall_mem.mpr
    intro pattern member
    obtain ⟨head, belongs, rfl⟩ := List.mem_map.mp member
    exact Header.pattern_typed (typed head belongs)
  · change binderSafeListAt "NQuote" 0 (guest.1 :: frame.map Header.pattern) = true
    apply (binderSafeListAt_eq_true_iff _ _ _).mpr
    intro pattern member
    rcases List.mem_cons.mp member with rfl | member
    · exact guestFormed.2
    · obtain ⟨head, belongs, rfl⟩ := List.mem_map.mp member
      exact Header.pattern_safe (safe head belongs)

private theorem primitive_step_after (before after : TargetProcess) {target : Pattern}
    (firing : DerivedContextualStep.RhoStep before.1 target)
    (equation : StructuralCongruence target after.1) : Target.Step before after := by
  let contractum := ParameterizedRewriteSystem.stepTarget before firing
  exact ParameterizedRewriteSystem.step_iff.mpr ⟨before, contractum, rfl, firing,
    (ParameterizedRewriteSystem.equations_iff_structuralCongruence contractum after).mpr equation⟩

def persistentInvocation (channel self : Nat) (body : Code 1) (datum : Nat)
    (frame : List Header) : Pattern :=
  RhoScopedServers.parallel ([send (allocatedName channel) (seedCode datum),
    GuardedReplication.idle (allocatedName self) (allocatedName channel) body.term] ++ frame.map Header.pattern)

def persistentReturn (channel self : Nat) (body : Code 1) (datum : Nat)
    (frame : List Header) : Pattern :=
  RhoScopedServers.parallel ([GuardedReplication.idle (allocatedName self) (allocatedName channel) body.term,
    semanticCommSubst body.term (seedCode datum)] ++ frame.map Header.pattern)

/-- A selected public receipt and one subsequent rearm are two authored
firings, with the exact body activation and the same persistent listener. -/
theorem persistent_path (channel self : Nat) (body : Code 1) (datum : Nat)
    (frame : List Header) (typed : ∀ head ∈ frame, head.Typed rhoAtomicNameContext)
    (safe : ∀ head ∈ frame, head.Safe) (before after : TargetProcess)
    (sourceEquation : StructuralCongruence before.1 (persistentInvocation channel self body datum frame))
    (targetEquation : StructuralCongruence (persistentReturn channel self body datum frame) after.1) :
    ∃ path : ExecutionPath Target before after, path.length = 2 := by
  let middle := framedProcess (requestStageProcess channel self body datum) frame typed safe
  have firstEndpoint : StructuralCongruence (persistentSelection channel self body datum frame).contractum middle.1 := by
    change StructuralCongruence
      (RhoScopedServers.parallel (semanticCommSubst _ _ :: frame.map Header.pattern)) _
    dsimp only [persistentSelection]
    have released := request_received (seedChannel rhoAtomicNameContext self)
      (seedChannel rhoAtomicNameContext channel) body.handler (seedCode datum)
    dsimp only [seedChannel, Code.handler] at released
    rw [released]
    exact .refl _
  have first := HeaderExecution.supplied_selection_step (persistentHeads channel self body datum frame)
    (persistentHeads_typed channel self body datum frame typed)
    (persistentHeads_safe channel self body datum frame safe)
    (persistentSelection channel self body datum frame) before middle sourceEquation firstEndpoint
  have secondFiring := DerivedContextualStep.RhoStep.par (frame.map Header.pattern)
    ⟨1, rearm_authored (seedChannel rhoAtomicNameContext self)
      (seedChannel rhoAtomicNameContext channel) body.handler (seedCode datum)⟩
  have second : Target.Step middle after := primitive_step_after middle after secondFiring
    (.trans _ _ _ (Context.par_flatten_head _ _) targetEquation)
  exact ⟨.cons ⟨first⟩ (.cons ⟨second⟩ (.refl _)), rfl⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAuthoredExecution
