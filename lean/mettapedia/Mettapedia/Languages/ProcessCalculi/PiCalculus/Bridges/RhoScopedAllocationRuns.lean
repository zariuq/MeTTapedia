import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation

/-!
# Retained finite service runs of the core rho allocator

The supplied list determines a selected request order. Its entries are actual
reply channels, including repeated entries. Each request contributes an
ordinary output to the request bag; each reply retains the seed at that
request's position. Three primitive communications per entry leave the same
waiting server, one advanced seed token, and every reply output.

The theorem constructs executions of the existing core reduction relation.
It does not assert that every target schedule selects this request order or
that an observer cannot interfere with the server's channels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocationRuns

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation

variable {free : FreeSortContext}

/-- One actual output for every supplied reply address. A list retains
multiple requests even when their addresses coincide. -/
def requestMessages (request : Channel free) (replies : List (Channel free)) : List Pattern :=
  replies.map (fun reply => send request.term (.apply "PDrop" [reply.term]))

/-- The returned process payloads, in the selected service order. Receiving
the payload at position `i` binds the name `allocatedName (index + i)`. -/
def replyMessages (index : Nat) : List (Channel free) → List Pattern
  | [] => []
  | reply :: rest => send reply.term (seedCode index) :: replyMessages (index + 1) rest

/-- The concrete initial bag contains all requests beside the installed
server and its current seed token. -/
def pending (self state request : Channel free) (index : Nat)
    (replies : List (Channel free)) : Pattern :=
  parallel (requestMessages request replies ++ [server self state request, stateToken state index])

/-- The concrete final bag contains the same server, the token advanced by
the number of requests, and the position-indexed reply outputs. -/
def settled (self state request : Channel free) (index : Nat)
    (replies : List (Channel free)) : Pattern :=
  parallel ([server self state request, stateToken state (index + replies.length)] ++
    replyMessages index replies)

@[simp] theorem requestMessages_length (request : Channel free) (replies : List (Channel free)) :
    (requestMessages request replies).length = replies.length := by
  simp [requestMessages]

@[simp] theorem replyMessages_length (index : Nat) (replies : List (Channel free)) :
    (replyMessages index replies).length = replies.length := by
  induction replies generalizing index with
  | nil => rfl
  | cons reply rest ih => simp [replyMessages, ih]

/-- Every returned occurrence has the supplied reply address and its own
stream position. This distinguishes response association from mere counts. -/
theorem replyMessages_getElem (index : Nat) (replies : List (Channel free))
    (position : Nat) (bound : position < replies.length) :
    (replyMessages index replies)[position]'(by simpa using bound) =
      send replies[position].term (seedCode (index + position)) := by
  induction replies generalizing index position with
  | nil => simp at bound
  | cons reply rest ih =>
      cases position with
      | zero => simp [replyMessages]
      | succ position =>
          have inRest : position < rest.length := by simpa using bound
          change (replyMessages (index + 1) rest)[position]'(by simpa using inRest) =
            send rest[position].term (seedCode (index + (position + 1)))
          have sameIndex : index + 1 + position = index + (position + 1) := by omega
          rw [← sameIndex]
          exact ih (index + 1) position inRest

/-- Even at the same reply address, different stream positions retain
inequivalent payload-bearing outputs under the rho equations. -/
theorem same_reply_equiv_iff (reply : Channel free) (first second : Nat) :
    RhoCalculus.StructuralCongruence (send reply.term (seedCode first))
      (send reply.term (seedCode second)) ↔ first = second := by
  constructor
  · intro equations
    have count := ioCount_SC equations
    simp [send, ioCount, seedCode_ioCount] at count
    omega
  · rintro rfl
    exact .refl _

/-- The real request prefix remains well-sorted before any independently
well-sorted frame. -/
theorem requestMessages_typed (request : Channel free) (replies : List (Channel free))
    (suffix : List Pattern)
    (suffixTyped : ProcListWellSorted rhoReflectivePresentation free [] suffix) :
    ProcListWellSorted rhoReflectivePresentation free []
      (requestMessages request replies ++ suffix) := by
  induction replies with
  | nil => simpa [requestMessages] using suffixTyped
  | cons reply rest ih =>
      exact .cons (.output request.typed (.drop reply.typed)) ih

theorem replyMessages_typed (index : Nat) (replies : List (Channel free)) :
    ProcListWellSorted rhoReflectivePresentation free [] (replyMessages index replies) := by
  induction replies generalizing index with
  | nil => exact .nil
  | cons reply rest ih =>
      exact .cons (.output reply.typed (seedCode_typed free index)) (ih (index + 1))

theorem requestMessages_safe (request : Channel free) (replies : List (Channel free)) :
    binderSafeListAt "NQuote" 0 (requestMessages request replies) = true := by
  induction replies with
  | nil => rfl
  | cons reply rest ih =>
      simp only [requestMessages] at ih ⊢
      simp [List.map_cons, binderSafeAt, binderSafeListAt, request.safe, reply.safe, ih]

theorem replyMessages_safe (index : Nat) (replies : List (Channel free)) :
    binderSafeListAt "NQuote" 0 (replyMessages index replies) = true := by
  induction replies generalizing index with
  | nil => rfl
  | cons reply rest ih =>
      simp only [replyMessages, binderSafeListAt, Bool.and_eq_true]
      exact ⟨by simp [binderSafeAt, binderSafeListAt, reply.safe, seedCode_safe], ih (index + 1)⟩

theorem pending_typed (self state request : Channel free) (index : Nat)
    (replies : List (Channel free)) :
    ProcWellSorted rhoReflectivePresentation free [] (pending self state request index replies) := by
  exact .parallel (requestMessages_typed request replies _
    (.cons (idle_typed self request (allocationHandler state))
      (.cons (.output state.typed (seedCode_typed free index)) .nil)))

theorem settled_typed (self state request : Channel free) (index : Nat)
    (replies : List (Channel free)) :
    ProcWellSorted rhoReflectivePresentation free [] (settled self state request index replies) := by
  exact .parallel (.cons (idle_typed self request (allocationHandler state))
    (.cons (.output state.typed (seedCode_typed free (index + replies.length)))
      (replyMessages_typed index replies)))

theorem pending_safe (self state request : Channel free) (index : Nat)
    (replies : List (Channel free)) :
    binderSafeAt "NQuote" 0 (pending self state request index replies) = true := by
  change binderSafeListAt "NQuote" 0 (requestMessages request replies ++
    [server self state request, stateToken state index]) = true
  rw [binderSafeListAt_eq_true_iff]
  intro process member
  rcases List.mem_append.mp member with message | retained
  · exact (binderSafeListAt_eq_true_iff "NQuote" 0 _).mp
      (requestMessages_safe request replies) process message
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at retained
    rcases retained with rfl | rfl
    · exact idle_safe self request (allocationHandler state)
    · simp [stateToken, binderSafeAt, binderSafeListAt, state.safe, seedCode_safe]

theorem settled_safe (self state request : Channel free) (index : Nat)
    (replies : List (Channel free)) :
    binderSafeAt "NQuote" 0 (settled self state request index replies) = true := by
  change binderSafeListAt "NQuote" 0
    (server self state request :: stateToken state (index + replies.length) ::
      replyMessages index replies) = true
  simp only [binderSafeListAt, Bool.and_eq_true]
  exact ⟨idle_safe self request (allocationHandler state),
    by simp [stateToken, binderSafeAt, binderSafeListAt, state.safe, seedCode_safe],
    replyMessages_safe index replies⟩

/-- The accumulator is an unchanged parallel frame. Previously returned
outputs remain in the final bag in their existing order. -/
theorem service_reduces_retaining (self state request : Channel free)
    (index : Nat) (replies : List (Channel free)) (earlier : List Pattern) :
    Nonempty (ReducesN (3 * replies.length)
      (parallel (requestMessages request replies ++
        [server self state request, stateToken state index] ++ earlier))
      (parallel ([server self state request, stateToken state (index + replies.length)] ++
        (earlier ++ replyMessages index replies)))) := by
  induction replies generalizing index earlier with
  | nil =>
      simp only [requestMessages, List.map_nil, List.length_nil, Nat.mul_zero,
        List.nil_append, Nat.add_zero, replyMessages, List.append_nil]
      exact ⟨.zero _⟩
  | cons reply rest ih =>
      obtain ⟨block⟩ := request_reduces self state request reply index
      have framed := block.splice [] (requestMessages request rest ++ earlier)
      let response := send reply.term (seedCode index)
      have before : RhoCalculus.StructuralCongruence
          (parallel (requestMessages request (reply :: rest) ++
            [server self state request, stateToken state index] ++ earlier))
          (parallel ([send request.term (.apply "PDrop" [reply.term]),
            server self state request, stateToken state index] ++
            (requestMessages request rest ++ earlier))) := by
        apply RhoCalculus.StructuralCongruence.par_perm
        simpa [requestMessages, List.append_assoc] using
          ((List.perm_append_comm (l₁ := requestMessages request rest)
            (l₂ := [server self state request, stateToken state index])).cons
              (send request.term (.apply "PDrop" [reply.term]))).append_right earlier
      have after : RhoCalculus.StructuralCongruence
          (parallel ([server self state request, response, stateToken state (index + 1)] ++
            (requestMessages request rest ++ earlier)))
          (parallel (requestMessages request rest ++
            [server self state request, stateToken state (index + 1)] ++ (earlier ++ [response]))) := by
        apply RhoCalculus.StructuralCongruence.par_perm
        have moveResponse := (List.perm_middle (a := response)
          (l₁ := [stateToken state (index + 1)] ++ requestMessages request rest ++ earlier)
          (l₂ := [])).symm.cons (server self state request)
        have moveRequests := (List.perm_append_comm
          (l₁ := [server self state request, stateToken state (index + 1)])
          (l₂ := requestMessages request rest)).append_right (earlier ++ [response])
        refine List.Perm.trans
          (l₂ := [server self state request, stateToken state (index + 1)] ++
            requestMessages request rest ++ earlier ++ [response]) ?_ ?_
        · simpa only [List.append_assoc, List.append_nil, List.singleton_append,
            List.cons_append] using moveResponse
        · simpa only [List.append_assoc] using moveRequests
      have selected := framed.transport before after
      obtain ⟨remaining⟩ := ih (index + 1) (earlier ++ [response])
      have combined := reducesN_concat selected remaining
      have sameCount : 3 + 3 * rest.length = 3 * (reply :: rest).length := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
      have sameSeed : index + 1 + rest.length = index + (reply :: rest).length := by
        simp only [List.length_cons]
        omega
      rw [sameCount, sameSeed] at combined
      exact ⟨by simpa only [response, replyMessages, List.append_assoc,
        List.singleton_append] using combined⟩

/-- A finite list of real request messages has a selected execution with
exactly three core communications per occurrence and the supplied endpoint. -/
theorem service_reduces (self state request : Channel free) (index : Nat)
    (replies : List (Channel free)) :
    Nonempty (ReducesN (3 * replies.length)
      (pending self state request index replies) (settled self state request index replies)) := by
  simpa [pending, settled] using service_reduces_retaining self state request index replies []

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocationRuns
