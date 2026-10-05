import Mettapedia.Languages.ProcessCalculi.RhoCalculus.GuardedReplication
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSubstitutionInert
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpointOperational

/-!
# Request-dependent persistent servers in the authored rho core

The existing reflective guarded server is used without a replication
primitive. Its handler has one request binder. The stored code binder is
outside that scope, so restoring the server leaves the handler template
unchanged. Receiving a request substitutes its actual payload into the
released handler. Initialization uses one communication and each request
uses two, retaining the same waiting server at the supplied endpoint.

The channel and handler records contain only sorting, scope, and semantic
normalization data. The operational contracts are proved from these data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSubstitutionInert
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint

abbrev CoreReduces := Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces

abbrev parallel (processes : List Pattern) : Pattern := .collection .hashBag processes none
abbrev send (channel payload : Pattern) : Pattern := .apply "POutput" [channel, payload]
abbrev receive (channel body : Pattern) : Pattern := .apply "PInput" [channel, .lambda none body]
abbrev drop (index : Nat) : Pattern := .apply "PDrop" [.bvar index]

/-- A closed rho name in semantic normal form. Free names retain their
declared sorts; closedness here concerns de Bruijn binders. -/
structure Channel (free : FreeSortContext) where
  term : Pattern
  typed : NameWellSorted rhoReflectivePresentation free [] term
  safe : binderSafeAt "NQuote" 0 term = true
  normalized : semanticNormalizeName term = term

/-- A normalized handler template depending on the received name. -/
structure Handler (free : FreeSortContext) where
  term : Pattern
  typed : ProcWellSorted rhoReflectivePresentation free ["Name"] term
  safe : binderSafeAt "NQuote" 1 term = true
  normalized : semanticNormalizeProc term = term

namespace Channel

theorem typedAt {free : FreeSortContext} (channel : Channel free) (bound : List String) :
    NameWellSorted rhoReflectivePresentation free bound channel.term := by
  simpa using channel.typed.weakenBoundRight bound

theorem safeAt {free : FreeSortContext} (channel : Channel free) (depth : Nat) :
    binderSafeAt "NQuote" depth channel.term = true :=
  binderSafeAt_mono "NQuote" channel.safe (Nat.zero_le depth)

theorem inert {free : FreeSortContext} (channel : Channel free)
    (index : Nat) (replacement : Pattern) :
    semanticSubstName index replacement channel.term = channel.term :=
  closed_name_inert channel.typed channel.safe channel.normalized index replacement

end Channel

namespace Handler

theorem inertAbove {free : FreeSortContext} (handler : Handler free)
    {index : Nat} (above : 1 ≤ index) (replacement : Pattern) :
    semanticSubstProc index replacement handler.term = handler.term :=
  one_binder_inert handler.typed handler.safe handler.normalized above replacement

/-- Actual request substitution produces a closed, correctly sorted handler. -/
theorem activated_typed_safe {free : FreeSortContext} (handler : Handler free)
    {payload : Pattern}
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload)
    (payloadSafe : binderSafeAt "NQuote" 0 payload = true) :
    ProcWellSorted rhoReflectivePresentation free []
        (semanticCommSubst handler.term payload) ∧
      binderSafeAt "NQuote" 0 (semanticCommSubst handler.term payload) = true :=
  semanticCommSubst_preserves handler.typed handler.safe payloadTyped payloadSafe

end Handler

section Server

variable {free : FreeSortContext}
variable (self request : Channel free) (handler : Handler free)

theorem code_normalized :
    semanticNormalizeProc (GuardedReplication.code self.term request.term handler.term) =
      GuardedReplication.code self.term request.term handler.term :=
  GuardedReplication.normalize_code self.normalized request.normalized handler.normalized

theorem code_inert (index : Nat) (replacement : Pattern) :
    semanticSubstProc index replacement (GuardedReplication.code self.term request.term handler.term) =
      GuardedReplication.code self.term request.term handler.term := by
  simp [GuardedReplication.code, GuardedReplication.body, semanticSubstProc, semanticSubstProcList,
    self.inert, request.inert, handler.inertAbove (by omega : 1 ≤ index + 1 + 1),
    semanticSubstNameMark, semanticNormalizeName]

theorem code_received :
    semanticCommSubst (GuardedReplication.body self.term request.term handler.term)
        (GuardedReplication.code self.term request.term handler.term) =
      GuardedReplication.idle self.term request.term handler.term := by
  simp [semanticCommSubst, code_normalized self request handler,
    GuardedReplication.body, GuardedReplication.idle, semanticSubstProc, semanticSubstProcList,
    self.inert, request.inert, handler.inertAbove (by omega : 1 ≤ 1),
    semanticSubstNameMark, semanticNormalizeName]

theorem request_received (payload : Pattern) :
    semanticCommSubst
        (parallel [send self.term (GuardedReplication.code self.term request.term handler.term),
          GuardedReplication.code self.term request.term handler.term, handler.term]) payload =
      parallel [send self.term (GuardedReplication.code self.term request.term handler.term),
        GuardedReplication.code self.term request.term handler.term,
        semanticCommSubst handler.term payload] := by
  simp [semanticCommSubst, semanticSubstProc, semanticSubstProcList,
    self.inert, code_inert self request handler]

theorem code_typed :
    ProcWellSorted rhoReflectivePresentation free []
      (GuardedReplication.code self.term request.term handler.term) := by
  apply ProcWellSorted.input self.typed
  apply ProcWellSorted.input (request.typedAt ["Name"])
  apply ProcWellSorted.parallel
  apply ProcListWellSorted.cons
  · exact .output (self.typedAt ["Name", "Name"])
      (.drop (.bvar (by rfl)))
  apply ProcListWellSorted.cons
  · exact .drop (.bvar (by rfl))
  exact .cons (by simpa [rhoReflectivePresentation] using
    handler.typed.weakenBoundRight ["Name"]) .nil

theorem idle_typed :
    ProcWellSorted rhoReflectivePresentation free []
      (GuardedReplication.idle self.term request.term handler.term) := by
  apply ProcWellSorted.input request.typed
  apply ProcWellSorted.parallel
  apply ProcListWellSorted.cons
  · exact .output (self.typedAt ["Name"])
      (by simpa [rhoReflectivePresentation] using
        (code_typed self request handler).weakenBoundRight ["Name"])
  apply ProcListWellSorted.cons
  · simpa [rhoReflectivePresentation] using
      (code_typed self request handler).weakenBoundRight ["Name"]
  exact .cons handler.typed .nil

theorem start_typed :
    ProcWellSorted rhoReflectivePresentation free []
      (GuardedReplication.start self.term request.term handler.term) := by
  exact .parallel (.cons (.output self.typed (code_typed self request handler))
    (.cons (code_typed self request handler) .nil))

theorem code_safe :
    binderSafeAt "NQuote" 0 (GuardedReplication.code self.term request.term handler.term) = true := by
  have handlerSafe : binderSafeAt "NQuote" 2 handler.term = true :=
    binderSafeAt_mono "NQuote" handler.safe (by omega)
  simp [GuardedReplication.code, GuardedReplication.body, binderSafeAt, binderSafeListAt,
    self.safeAt, request.safeAt, handlerSafe]

theorem idle_safe :
    binderSafeAt "NQuote" 0 (GuardedReplication.idle self.term request.term handler.term) = true := by
  have storedSafe : binderSafeAt "NQuote" 1
      (GuardedReplication.code self.term request.term handler.term) = true :=
    binderSafeAt_mono "NQuote" (code_safe self request handler) (by omega)
  simp [GuardedReplication.idle, binderSafeAt, binderSafeListAt, request.safeAt, self.safeAt,
    storedSafe, handler.safe]

theorem start_safe :
    binderSafeAt "NQuote" 0 (GuardedReplication.start self.term request.term handler.term) = true := by
  simp [GuardedReplication.start, binderSafeAt, binderSafeListAt, self.safe,
    code_safe self request handler]

/-- Initialization takes one actual core communication. -/
theorem start_reduces :
    Nonempty (CoreReduces (GuardedReplication.start self.term request.term handler.term)
      (GuardedReplication.idle self.term request.term handler.term)) := by
  have raw := RhoCalculus.Reduction.Reduces.comm (n := self.term)
    (q := GuardedReplication.code self.term request.term handler.term)
    (p := GuardedReplication.body self.term request.term handler.term) (rest := [])
  rw [code_received self request handler] at raw
  exact ⟨.equiv (.refl _) raw (RhoCalculus.StructuralCongruence.par_singleton _)⟩

/-- Receiving a request and rearming preserves the server and releases the
handler instantiated with this request's actual payload. -/
theorem request_reduces (payload : Pattern) :
    Nonempty (ReducesN 2
      (parallel [send request.term payload, GuardedReplication.idle self.term request.term handler.term])
      (parallel [GuardedReplication.idle self.term request.term handler.term,
        semanticCommSubst handler.term payload])) := by
  have raw := RhoCalculus.Reduction.Reduces.comm (n := request.term) (q := payload)
    (p := parallel [send self.term (GuardedReplication.code self.term request.term handler.term),
      GuardedReplication.code self.term request.term handler.term, handler.term]) (rest := [])
  rw [request_received self request handler] at raw
  have first : CoreReduces
      (parallel [send request.term payload, GuardedReplication.idle self.term request.term handler.term])
      (parallel [GuardedReplication.start self.term request.term handler.term,
        semanticCommSubst handler.term payload]) := by
    refine .equiv (.refl _) raw ?_
    refine .trans _ _ _ (RhoCalculus.StructuralCongruence.par_singleton _) ?_
    exact .symm _ _ (RhoCalculus.Context.par_flatten_head _ _)
  obtain ⟨second⟩ := start_reduces self request handler
  exact ⟨.succ first (.succ (.par second) (.zero _))⟩

/-- The stored code cannot run until an external request reaches its guard. -/
theorem idle_normal (names : List String)
    (unmentioned : RhoCalculus.Reduction.nameCount names request.term = 0) :
    NormalForm (GuardedReplication.idle self.term request.term handler.term) :=
  GuardedReplication.idle_normal self.term request.term handler.term names unmentioned

private theorem empty_nameCount (pattern : Pattern) :
    RhoCalculus.Reduction.nameCount [] pattern = 0 := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ | hfvar _ => simp [RhoCalculus.Reduction.nameCount]
  | happly constructor arguments ih =>
      simp only [RhoCalculus.Reduction.nameCount]
      have allZero : arguments.map (RhoCalculus.Reduction.nameCount []) =
          arguments.map (fun _ => 0) :=
        List.map_congr_left fun argument membership => ih argument membership
      rw [allZero]
      simp
  | hlambda _ _ ih | hmultiLambda _ _ _ ih =>
      simpa [RhoCalculus.Reduction.nameCount] using ih
  | hsubst _ _ first second => simp [RhoCalculus.Reduction.nameCount, first, second]
  | hcollection collectionType elements rest ih =>
      simp only [RhoCalculus.Reduction.nameCount]
      have allZero : elements.map (RhoCalculus.Reduction.nameCount []) =
          elements.map (fun _ => 0) :=
        List.map_congr_left fun element membership => ih element membership
      rw [allZero]
      simp

/-- For every handler and channel, the installed server has no autonomous
core reduction. The body remains below its input guard. -/
theorem idle_blocked : NormalForm (GuardedReplication.idle self.term request.term handler.term) :=
  idle_normal self request handler [] (empty_nameCount request.term)

/-- An authored COMM at selected bag positions, with independently proved
sorting for the actual body and payload. -/
theorem authored_comm_at
    {elements : List Pattern} {inputIndex outputIndex : Nat}
    (inputBound : inputIndex < elements.length)
    (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
    {channel body payload : Pattern}
    (inputEq : elements[inputIndex] = receive channel body)
    (outputEq : (elements.eraseIdx inputIndex)[outputIndex] = send channel payload)
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free ["Name"] body)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload) :
    RhoStepAt 1 (parallel elements)
      (parallel (semanticCommSubst body payload ::
        (elements.eraseIdx inputIndex).eraseIdx outputIndex)) := by
  have matching : rhoCanonicalEquivalent channel channel = true := by
    simp [rhoCanonicalEquivalent,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalEquivalent]
  have fired := rhoStepAt_one_comm inputBound outputBound inputEq outputEq matching
  rw [apply_commBindingsAt bodyTyped payloadTyped] at fired
  exact fired

/-- The initialization is accepted by the authored matcher and application
at its actual positions in the stored-code bag. -/
theorem start_authored :
    RhoStepAt 1 (GuardedReplication.start self.term request.term handler.term)
      (parallel [GuardedReplication.idle self.term request.term handler.term]) := by
  have bodyTyped := (rho_input_wellSorted_inv (code_typed self request handler)).2.2
  have fired := authored_comm_at
    (elements := [send self.term (GuardedReplication.code self.term request.term handler.term),
      GuardedReplication.code self.term request.term handler.term])
    (inputIndex := 1) (outputIndex := 0) (by simp) (by simp)
    (by rfl) (by rfl) bodyTyped (code_typed self request handler)
  simpa [GuardedReplication.start, code_received self request handler] using fired

/-- Initialization remains an actual authored firing after applying the
runtime's existing canonical section. -/
theorem start_canonical :
    CanonicalFiring
      (Canonical.canonicalize (GuardedReplication.start self.term request.term handler.term))
      (Canonical.canonicalize (GuardedReplication.idle self.term request.term handler.term)) := by
  obtain ⟨target, fired, endpoint⟩ := canonicalStep_complete_of_rhoStep
    (start_typed self request handler) (start_safe self request handler)
    ⟨1, start_authored self request handler⟩
  exact ⟨target, fired, endpoint.trans (Canonical.canonicalize_parallel_singleton _)⟩

/-- The intermediate state retains the code output and input while the
request-dependent handler has already been released. -/
def requestStage (payload : Pattern) : Pattern :=
  parallel [send self.term (GuardedReplication.code self.term request.term handler.term),
    GuardedReplication.code self.term request.term handler.term,
    semanticCommSubst handler.term payload]

theorem requestStage_typed {payload : Pattern}
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload)
    (payloadSafe : binderSafeAt "NQuote" 0 payload = true) :
    ProcWellSorted rhoReflectivePresentation free []
      (requestStage self request handler payload) :=
  .parallel (.cons (.output self.typed (code_typed self request handler))
    (.cons (code_typed self request handler)
      (.cons (handler.activated_typed_safe payloadTyped payloadSafe).1 .nil)))

theorem requestStage_safe {payload : Pattern}
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload)
    (payloadSafe : binderSafeAt "NQuote" 0 payload = true) :
    binderSafeAt "NQuote" 0 (requestStage self request handler payload) = true := by
  have activated := (handler.activated_typed_safe payloadTyped payloadSafe).2
  simp [requestStage, binderSafeAt, binderSafeListAt, self.safe,
    code_safe self request handler, activated]

/-- The request firing itself, before the canonical section. -/
theorem request_authored {payload : Pattern}
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload) :
    RhoStepAt 1
      (parallel [send request.term payload,
        GuardedReplication.idle self.term request.term handler.term])
      (parallel [requestStage self request handler payload]) := by
  have bodyTyped := (rho_input_wellSorted_inv (idle_typed self request handler)).2.2
  have fired := authored_comm_at
    (elements := [send request.term payload,
      GuardedReplication.idle self.term request.term handler.term])
    (inputIndex := 1) (outputIndex := 0) (by simp) (by simp)
    (by rfl) (by rfl) bodyTyped payloadTyped
  simpa [requestStage, request_received self request handler] using fired

/-- Restoring the same server is also an actual authored firing. -/
theorem rearm_authored (payload : Pattern) :
    RhoStepAt 1 (requestStage self request handler payload)
      (parallel [GuardedReplication.idle self.term request.term handler.term,
        semanticCommSubst handler.term payload]) := by
  have bodyTyped := (rho_input_wellSorted_inv (code_typed self request handler)).2.2
  have fired := authored_comm_at
    (elements := [send self.term (GuardedReplication.code self.term request.term handler.term),
      GuardedReplication.code self.term request.term handler.term,
      semanticCommSubst handler.term payload])
    (inputIndex := 1) (outputIndex := 0) (by simp) (by simp)
    (by rfl) (by rfl) bodyTyped (code_typed self request handler)
  simpa [requestStage, code_received self request handler] using fired

/-- Two actual authored firings restore the waiting server and retain the
handler for this supplied request. There is no derived replication step. -/
theorem request_canonical {payload : Pattern}
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload)
    (payloadSafe : binderSafeAt "NQuote" 0 payload = true) :
    ∃ intermediate,
      CanonicalFiring
        (Canonical.canonicalize
          (parallel [send request.term payload,
            GuardedReplication.idle self.term request.term handler.term])) intermediate ∧
      CanonicalFiring intermediate
        (Canonical.canonicalize
          (parallel [GuardedReplication.idle self.term request.term handler.term,
            semanticCommSubst handler.term payload])) := by
  have sourceTyped : ProcWellSorted rhoReflectivePresentation free []
      (parallel [send request.term payload,
        GuardedReplication.idle self.term request.term handler.term]) :=
    .parallel (.cons (.output request.typed payloadTyped)
      (.cons (idle_typed self request handler) .nil))
  have sourceSafe : binderSafeAt "NQuote" 0
      (parallel [send request.term payload,
        GuardedReplication.idle self.term request.term handler.term]) = true := by
    simp [binderSafeAt, binderSafeListAt, request.safe, payloadSafe,
      idle_safe self request handler]
  obtain ⟨firstTarget, first, firstEndpoint⟩ := canonicalStep_complete_of_rhoStep
    sourceTyped sourceSafe ⟨1, request_authored self request handler payloadTyped⟩
  obtain ⟨secondTarget, second, secondEndpoint⟩ := canonicalStep_complete_of_rhoStep
    (requestStage_typed self request handler payloadTyped payloadSafe)
    (requestStage_safe self request handler payloadTyped payloadSafe)
    ⟨1, rearm_authored self request handler payload⟩
  refine ⟨Canonical.canonicalize (requestStage self request handler payload), ?_, ?_⟩
  · exact ⟨firstTarget, first,
      firstEndpoint.trans (Canonical.canonicalize_parallel_singleton _)⟩
  · exact ⟨secondTarget, second, secondEndpoint⟩

end Server

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers
