import Mettapedia.GSLT.Core.GivenClauseLoop

/-!
# Authorized mind-agent admission into a shared continuation store

A background service may recommend work, but only an authored authorization
witness may mutate the foreground passive store.  The runtime-facing operation
in this module is deliberately small: append one exact occurrence to the shared
live frontier, update every complete queue view through its own discipline, and
preserve all prior observations, selections, activations, and controller state.

The runtime transports the authorization witness without interpreting its
domain-specific proposition.  Premise selection, attention, valuation, and
payment can therefore live above this seam without becoming mutation authority.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.MindAgentStoreAdmission

open Mettapedia.GSLT.Core.GivenClauseLoop
open Mettapedia.GSLT.Core.WeightedOccurrenceControl

universe uToken uNode uAnswer

/-- A domain policy authorizes one exact token/occurrence pair.  Keeping both
indices in the type prevents a receipt for one proposal from admitting another
occurrence. -/
structure AdmissionWitness
    {Token : Type uToken} {Node : Type uNode}
    (Authorized : Token → Node → Prop) (token : Token) (occurrence : Node) where
  authorized : Authorized token occurrence

private def extendFrontier {Node : Type uNode} {count : Nat}
    (disciplines : Fin count → QueueDiscipline Node)
    (frontier : PortfolioFrontier Node count) (occurrence : Node) :
    PortfolioFrontier Node count where
  live := frontier.live ++ [occurrence]
  queues lane :=
    (disciplines lane).integrate (frontier.queues lane) [occurrence]
  queue_complete lane := by
    exact ((disciplines lane).integrate_complete _ _).trans
      ((frontier.queue_complete lane).append_right [occurrence])

/-- The single runtime mutation operation.  Its domain-specific authority is
supplied as an indexed witness; the store mechanism only preserves occurrence
and queue accounting. -/
def applyAdmission
    {Token : Type uToken} {Node : Type uNode} {Answer : Type uAnswer}
    {count : Nat} {Authorized : Token → Node → Prop}
    {token : Token} {occurrence : Node}
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count)
    (_receipt : AdmissionWitness Authorized token occurrence) :
    Snapshot Node Answer count where
  events := snapshot.events
  selections := snapshot.selections
  processed := snapshot.processed
  passive := extendFrontier disciplines snapshot.passive occurrence
  cursor := snapshot.cursor

/-- The admitted occurrence appears exactly once at the end of the semantic
live store. -/
theorem applyAdmission_live
    {Token : Type uToken} {Node : Type uNode} {Answer : Type uAnswer}
    {count : Nat} {Authorized : Token → Node → Prop}
    {token : Token} {occurrence : Node}
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count)
    (receipt : AdmissionWitness Authorized token occurrence) :
    (applyAdmission disciplines snapshot receipt).passive.live =
      snapshot.passive.live ++ [occurrence] :=
  rfl

/-- Existing execution receipts and activation state survive admission
unchanged. -/
theorem applyAdmission_preserves_history
    {Token : Type uToken} {Node : Type uNode} {Answer : Type uAnswer}
    {count : Nat} {Authorized : Token → Node → Prop}
    {token : Token} {occurrence : Node}
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count)
    (receipt : AdmissionWitness Authorized token occurrence) :
    (applyAdmission disciplines snapshot receipt).events = snapshot.events ∧
      (applyAdmission disciplines snapshot receipt).selections = snapshot.selections ∧
      (applyAdmission disciplines snapshot receipt).processed = snapshot.processed ∧
      (applyAdmission disciplines snapshot receipt).cursor = snapshot.cursor :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Every scheduler lane remains a complete permutation view of the same
semantic live occurrence store after admission. -/
theorem applyAdmission_queue_complete
    {Token : Type uToken} {Node : Type uNode} {Answer : Type uAnswer}
    {count : Nat} {Authorized : Token → Node → Prop}
    {token : Token} {occurrence : Node}
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count)
    (receipt : AdmissionWitness Authorized token occurrence)
    (lane : Fin count) :
    ((applyAdmission disciplines snapshot receipt).passive.queues lane).Perm
      (applyAdmission disciplines snapshot receipt).passive.live :=
  (applyAdmission disciplines snapshot receipt).passive.queue_complete lane

/-! ## Capability canaries -/

namespace Canary

def Allows (token occurrence : Bool) : Prop :=
  token = true ∧ occurrence = true

def accepted : AdmissionWitness Allows true true where
  authorized := ⟨rfl, rfl⟩

/-- Positive control: an exact policy witness inhabits the capability. -/
theorem accepted_pair_has_witness :
    Nonempty (AdmissionWitness Allows true true) :=
  ⟨accepted⟩

/-- Negative control: possessing a token value is not enough when it does not
authorize the requested occurrence. -/
theorem rejected_pair_has_no_witness :
    IsEmpty (AdmissionWitness Allows false true) := by
  constructor
  intro receipt
  exact Bool.noConfusion receipt.authorized.1

end Canary

#print axioms applyAdmission_live
#print axioms applyAdmission_preserves_history
#print axioms applyAdmission_queue_complete
#print axioms Canary.accepted_pair_has_witness
#print axioms Canary.rejected_pair_has_no_witness

end Mettapedia.CognitiveArchitecture.MindAgentStoreAdmission
