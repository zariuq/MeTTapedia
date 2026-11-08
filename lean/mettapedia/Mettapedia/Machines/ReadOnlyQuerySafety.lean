import Mettapedia.Machines.ReadOnlyQueryDemand

/-!
# Result invariants of partially available adaptive queries

The logical relation follows the query's control tree. A read continuation
only owes its invariant for valid replies; missing replies stop admission.
Sequential composition transports the intermediate invariant to the selected
continuation. The soundness theorem concerns actually completed executions,
without demanding observations from branches that were not visited.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadOnlyQuerySafety

open ReadOnlyQuery ReadOnlyQueryDemand

variable {Key Reply Answer Other : Type}

inductive Guarantees (validKey : Key → Prop) (validReply : Reply → Prop) (validAnswer : Answer → Prop) :
    Program Key Reply Answer → Prop where
  | pure {answer : Answer} : validAnswer answer → Guarantees validKey validReply validAnswer (.pure answer)
  | read {key : Key} {next : Reply → Program Key Reply Answer} :
      validKey key → (∀ reply, validReply reply → Guarantees validKey validReply validAnswer (next reply)) →
      Guarantees validKey validReply validAnswer (.read key next)

theorem completed_sound (validKey : Key → Prop) (validReply : Reply → Prop) (validAnswer : Answer → Prop)
    (program : Program Key Reply Answer) (derivation : Guarantees validKey validReply validAnswer program)
    (available : Key → Option Reply)
    (valid : ∀ key, validKey key → ∀ reply, available key = some reply → validReply reply)
    (answer : Answer) (completed : (run available (demand program)).answer = some answer) :
    validAnswer answer := by
  induction derivation with
  | pure good => exact (Option.some.inj completed) ▸ good
  | @read key next keySafe children ih =>
      cases found : available key with
      | none => simp [demand, run, found] at completed
      | some reply =>
          exact ih reply (valid key keySafe reply found) (by simpa [demand, run, found] using completed)

theorem bind_guarantees (validKey : Key → Prop) (validReply : Reply → Prop) (firstGood : Answer → Prop) (lastGood : Other → Prop)
    (program : Program Key Reply Answer) (first : Guarantees validKey validReply firstGood program)
    (next : Answer → Program Key Reply Other)
    (later : ∀ answer, firstGood answer → Guarantees validKey validReply lastGood (next answer)) :
    Guarantees validKey validReply lastGood (bind program next) := by
  induction first with
  | pure good => exact later _ good
  | read keySafe children ih => exact .read keySafe (fun reply safe => ih reply safe)

theorem map_guarantees (validKey : Key → Prop) (validReply : Reply → Prop) (firstGood : Answer → Prop) (lastGood : Other → Prop)
    (program : Program Key Reply Answer) (first : Guarantees validKey validReply firstGood program)
    (convert : Answer → Other) (preserves : ∀ answer, firstGood answer → lastGood (convert answer)) :
    Guarantees validKey validReply lastGood (map convert program) :=
  bind_guarantees validKey validReply firstGood lastGood program first _
    (fun answer good => .pure (preserves answer good))

theorem reads_valid (validKey : Key → Prop) (validReply : Reply → Prop) (validAnswer : Answer → Prop)
    (program : Program Key Reply Answer) (derivation : Guarantees validKey validReply validAnswer program)
    (available : Key → Option Reply)
    (valid : ∀ key, validKey key → ∀ reply, available key = some reply → validReply reply) :
    ∀ read ∈ (run available (demand program)).reads, validKey read.1 := by
  induction derivation with
  | pure good => intro read member; cases member
  | @read key next keySafe children ih =>
      cases found : available key with
      | none =>
          intro read member
          simp only [demand, run, found, List.mem_singleton] at member
          cases member
          exact keySafe
      | some reply =>
          intro read member
          simp only [demand, run, found, List.mem_cons] at member
          rcases member with rfl | member
          · exact keySafe
          · exact ih reply (valid key keySafe reply found) read member

def OnSuccess (good : Answer → Prop) : Except Unit Answer → Prop
  | .error _ => True
  | .ok answer => good answer

end Mettapedia.Machines.ReadOnlyQuerySafety
