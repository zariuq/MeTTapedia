import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedNamed
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingNotSignatureMap

/-!
# Controls for scoped rho servers and dynamic allocation

The positive controls retain a reusable server, distinguish two reply
addresses, and bind a generated name into a running client. The negative
controls expose the maintained wrapper's syntax boundary, the ill-sorted
historical seed update and restriction request, and the observer that knows a
generated structured name. These do not establish unrestricted target-context
reflection for the selected execution blocks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedNamed
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

private def replyBody : Process := .output "r" "answer"
private theorem replyBody_free : RestrictionFree replyBody := trivial

private def replyServer : Pattern :=
  namedServer replyBody_free "self" "service" "r" "ns" "value"

private def requestTo (reply : String) : Pattern := send (.fvar "service") (.apply "PDrop" [.fvar reply])
private def responseTo (reply : String) : Pattern := send (.fvar reply) (.apply "PDrop" [.fvar "answer"])

/-- Two different request payloads produce two different reply destinations,
with the same server retained after both activations. -/
theorem two_requests_retain_server :
    Nonempty (ReducesN 4
      (parallel [requestTo "alice", replyServer, requestTo "bob"])
      (parallel [replyServer, responseTo "alice", responseTo "bob"])) := by
  obtain ⟨first⟩ := named_request_reduces replyBody_free
    "self" "service" "r" "alice" "ns" "value" (by decide) trivial
  obtain ⟨second⟩ := named_request_reduces replyBody_free
    "self" "service" "r" "bob" "ns" "value" (by decide) trivial
  have first' : ReducesN 2 (parallel [requestTo "alice", replyServer])
      (parallel [replyServer, responseTo "alice"]) := by
    simpa [replyBody, Process.substitute_output, encode, rhoOutput, rhoDrop,
      piNameToRhoName, responseTo, requestTo, replyServer] using first
  have second' : ReducesN 2 (parallel [requestTo "bob", replyServer])
      (parallel [replyServer, responseTo "bob"]) := by
    simpa [replyBody, Process.substitute_output, encode, rhoOutput, rhoDrop,
      piNameToRhoName, responseTo, requestTo, replyServer] using second
  have firstFramed := first'.splice [] [requestTo "bob"]
  have secondFramed := second'.splice [] [responseTo "alice"]
  have sourcePermutation : RhoCalculus.StructuralCongruence
      (parallel [replyServer, responseTo "alice", requestTo "bob"])
      (parallel [requestTo "bob", replyServer, responseTo "alice"]) := by
    apply RhoCalculus.StructuralCongruence.par_perm
    simpa using (List.perm_middle (a := requestTo "bob")
      (l₁ := [replyServer, responseTo "alice"]) (l₂ := []))
  have targetPermutation : RhoCalculus.StructuralCongruence
      (parallel [replyServer, responseTo "bob", responseTo "alice"])
      (parallel [replyServer, responseTo "alice", responseTo "bob"]) := by
    apply RhoCalculus.StructuralCongruence.par_perm
    exact (List.Perm.swap _ _ []).cons _
  have secondAligned := secondFramed.transport sourcePermutation targetPermutation
  exact ⟨reducesN_concat firstFramed secondAligned⟩

private def allocatorSelf := atomicChannel "allocator-code"
private def allocatorState := atomicChannel "allocator-state"
private def allocatorRequest := atomicChannel "allocate"
private def allocatorReply := atomicChannel "allocation-reply"

/-- Allocating and receiving a name puts that very structured name in the
client's running output subject and retains the next token. -/
theorem allocation_binds_client_subject :
    Nonempty (ReducesN 4
      (RhoScopedAllocation.clientInvocation allocatorSelf allocatorState allocatorRequest allocatorReply
        (namedHandler replyBody_free "r" "ns" "value") 7)
      (parallel [RhoScopedAllocation.server allocatorSelf allocatorState allocatorRequest,
        RhoScopedAllocation.stateToken allocatorState 8,
        send (RhoScopedAllocation.allocatedName 7) (.apply "PDrop" [.fvar "answer"])])) := by
  have released :
      semanticCommSubst (namedHandler replyBody_free "r" "ns" "value").term
          (RhoScopedAllocation.seedCode 7) =
        send (RhoScopedAllocation.allocatedName 7) (.apply "PDrop" [.fvar "answer"]) := by
    simp [namedHandler, replyBody, encode, rhoOutput, rhoDrop, piNameToRhoName,
      closeFVar, semanticCommSubst, RhoScopedAllocation.seedCode_normalized,
      semanticSubstProc, semanticSubstName, semanticSubstNameMark,
      semanticNormalizeName, RhoScopedAllocation.allocatedName]
  obtain ⟨path⟩ := RhoScopedAllocation.client_reduces
    allocatorSelf allocatorState allocatorRequest allocatorReply
    (namedHandler replyBody_free "r" "ns" "value") 7
  simp only [RhoScopedAllocation.clientReturned, released] at path
  exact ⟨path⟩

/-- Old and new state names differ even modulo the rho equations. -/
theorem successive_allocations_differ :
    ¬ RhoCalculus.StructuralCongruence (RhoScopedAllocation.allocatedName 7)
      (RhoScopedAllocation.allocatedName 8) := by
  rw [RhoScopedAllocation.allocatedName_equiv_iff]
  decide

/-- The old wrapper does not become an authored rho term by being called a
replication encoding. The existing signature obstruction is reused. -/
theorem legacy_replication_outside_authored_core :
    ¬ Mettapedia.GSLT.LanguageDef.WellSorted.HasType rhoCalc
      (fun _ => none) [] (encode (.replicate "service" "r" replyBody) "ns" "value")
      (.base "Proc") :=
  encode_replicate_untypable _ _ _ _ _ _ _ _

/-- The old restriction request sends a name in a process payload position. -/
theorem legacy_restriction_request_ill_sorted :
    ¬ ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext []
      (encode (.nu "x" .nil) "ns" "value") := by
  intro typed
  have shape : encode (.nu "x" .nil) "ns" "value" =
      parallel [send (.fvar "value") (.fvar "ns"),
        receive (.fvar "ns") (parallel [])] := by
    simp [encode, rhoNil, rhoPar, rhoOutput, rhoInput, closeFVar]
  rw [shape] at typed
  cases typed with
  | parallel elementsTyped =>
      have outputTyped := elementsTyped.getElem 0 (by simp)
      have badPayload := (rho_output_wellSorted_inv outputTyped).2
      cases badPayload with
      | fvar lookup => simp [rhoAtomicNameContext, rhoReflectivePresentation] at lookup

/-- Quotation consumes a process. The historical constant double quote in
the seed update places a name where that process is required. -/
theorem legacy_seed_update_ill_sorted (free : FreeSortContext) (bound : List String) :
    ¬ NameWellSorted rhoReflectivePresentation free bound
      (.apply "NQuote" [.apply "NQuote" [rhoNil]]) := by
  intro typed
  generalize shape : (.apply "NQuote" [.apply "NQuote" [rhoNil]] : Pattern) = name at typed
  cases typed <;> simp [rhoReflectivePresentation] at shape
  rename_i process processTyped
  cases shape
  generalize innerShape : (.apply "NQuote" [rhoNil] : Pattern) = process at processTyped
  cases processTyped <;> simp [rhoReflectivePresentation] at innerShape

/-- Without a seed token, the released seed receiver and the retained service
are both blocked; replication alone does not supply allocation state. -/
theorem allocator_without_token_blocked :
    NormalForm (parallel [RhoScopedAllocation.server allocatorSelf allocatorState allocatorRequest,
      RhoScopedAllocation.seedReceiver allocatorState allocatorReply]) := by
  rintro ⟨target, ⟨step⟩⟩
  have separated : RhoCalculus.Reduction.separation []
      (parallel [RhoScopedAllocation.server allocatorSelf allocatorState allocatorRequest,
        RhoScopedAllocation.seedReceiver allocatorState allocatorReply]) = 0 := by
    simp [RhoCalculus.Reduction.separation, RhoCalculus.Reduction.separationHead,
      RhoCalculus.Reduction.nameCount, RhoScopedAllocation.server,
      RhoScopedAllocation.seedReceiver, GuardedReplication.idle,
      allocatorSelf, allocatorState, allocatorRequest, allocatorReply, atomicChannel]
  exact (not_reduces_of_separation_eq_zero [] separated target).false step

/-- An unrestricted target observer can construct the allocator's quoted name
and receive on it. Non-repetition is therefore not an observer-privacy law. -/
theorem observer_can_receive_on_generated_name :
    RhoStepAt 1
      (parallel [send (RhoScopedAllocation.allocatedName 7) RhoScopedAllocation.zero,
        receive (RhoScopedAllocation.allocatedName 7) (parallel [])])
      (parallel [parallel []]) := by
  have fired := authored_comm_at
    (elements := [send (RhoScopedAllocation.allocatedName 7) RhoScopedAllocation.zero,
      receive (RhoScopedAllocation.allocatedName 7) (parallel [])])
    (inputIndex := 1) (outputIndex := 0) (free := rhoAtomicNameContext)
    (by simp) (by simp) (by rfl) (by rfl) (.parallel .nil) .unit
  simpa [semanticCommSubst, semanticSubstProc, semanticSubstProcList,
    rhoReflectivePresentation] using fired

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedControls
