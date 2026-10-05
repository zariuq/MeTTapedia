import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocationRuns
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedControls

/-!
# Finite allocator runs with repeated reply addresses

Two identical request messages are retained as two occurrences and produce
two inequivalent seed payloads at the same reply channel. The resulting
server and token can serve another request while retaining both earlier
reply outputs. The imported controls also expose missing-token blocking and
the unrestricted quotation-observer boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocationRunsControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedNamed
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocationRuns

private def self := atomicChannel "allocator-code"
private def state := atomicChannel "allocator-state"
private def request := atomicChannel "allocate"
private def reply := atomicChannel "same-reply"

/-- Identical requests are two real messages in the initial bag. -/
theorem identical_requests_retain_multiplicity :
    requestMessages request [reply, reply] =
      [send request.term (.apply "PDrop" [reply.term]),
        send request.term (.apply "PDrop" [reply.term])] := rfl

/-- Six actual communications retain one server and advance the token
twice, producing both distinct responses on the same supplied address. -/
theorem two_requests_same_reply :
    Nonempty (ReducesN 6
      (parallel [send request.term (.apply "PDrop" [reply.term]),
        send request.term (.apply "PDrop" [reply.term]),
        server self state request, stateToken state 3])
      (parallel [server self state request, stateToken state 5,
        send reply.term (seedCode 3), send reply.term (seedCode 4)])) := by
  simpa only [pending, settled, requestMessages, List.map_cons, List.map_nil,
    List.append_nil, List.cons_append, List.nil_append, replyMessages,
    List.length_cons, List.length_nil, Nat.reduceMul, Nat.reduceAdd] using
    service_reduces self state request 3 [reply, reply]

/-- Reusing the resulting service preserves both old reply outputs while
the third request receives the next seed and leaves the next token. -/
theorem third_request_retains_previous_replies :
    Nonempty (ReducesN 3
      (parallel [send request.term (.apply "PDrop" [reply.term]),
        server self state request, stateToken state 5,
        send reply.term (seedCode 3), send reply.term (seedCode 4)])
      (parallel [server self state request, stateToken state 6,
        send reply.term (seedCode 3), send reply.term (seedCode 4),
        send reply.term (seedCode 5)])) := by
  simpa only [requestMessages, List.map_cons, List.map_nil, List.append_nil,
    List.cons_append, List.nil_append, replyMessages, List.length_cons,
    List.length_nil, Nat.reduceMul, Nat.reduceAdd] using
    service_reduces_retaining self state request 5 [reply]
      [send reply.term (seedCode 3), send reply.term (seedCode 4)]

/-- Sharing the reply address does not identify the two returned outputs
through the rho equations. -/
theorem same_reply_distinct_seed_outputs :
    ¬ RhoCalculus.StructuralCongruence (send reply.term (seedCode 3))
      (send reply.term (seedCode 4)) := by
  rw [same_reply_equiv_iff]
  decide

/-- No requests require no communication and retain the same service and
current token by literal endpoint equality. -/
theorem zero_requests_need_no_firing :
    Nonempty (ReducesN 0
      (parallel [server self state request, stateToken state 3])
      (parallel [server self state request, stateToken state 3])) := by
  simpa only [pending, settled, requestMessages, List.map_nil, List.nil_append,
    List.append_nil, replyMessages, List.length_nil, Nat.mul_zero, Nat.add_zero] using
    service_reduces self state request 3 []

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocationRunsControls
