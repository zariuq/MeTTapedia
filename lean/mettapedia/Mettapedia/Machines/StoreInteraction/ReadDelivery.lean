import Mettapedia.Machines.Cursor.ReadAdmissionProfiles

/-!
# Historical and live delivery under an effectful but noninterfering client

The client runs between answers and may change the store. If it preserves
the remaining offered occurrences, the existing historical and live readers
have exactly the same observed answer list and final store. This concerns
these retained candidates and a total state-transforming client; it is not
an equivalence for arbitrary source continuations or changed match frontiers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoreInteraction.ReadDelivery

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)
open Mettapedia.Machines.Cursor
open ReadAdmissionProfiles (Offer current captured kept)
open StampedSnapshots (Store)

variable {Value Answer : Type}

/-- Observe a trace while a caller changes the world after each answer. -/
def consume (client : Answer → Store Value → Store Value) :
    Trace (Store Value) Answer → List Answer × Store Value
  | .done store => ([], store)
  | .answer value store rest =>
    let later := consume client (rest (client value store))
    (value :: later.1, later.2)

theorem captured_is_the_entry_list (entries : List (Offer Value))
    (client : Offer Value → Store Value → Store Value) (store : Store Value) :
    consume client (captured entries store) =
      (entries, entries.foldl (fun world offered => client offered world) store) := by
  induction entries generalizing store with
  | nil => rfl
  | cons offered rest ih =>
    exact congrArg (fun pair : List (Offer Value) × Store Value =>
      (offered :: pair.1, pair.2)) (ih (client offered store))

variable [DecidableEq Value]

/-- Positive occurrence dependencies, not equality of whole worlds. -/
def Live (entries : List (Offer Value)) (store : Store Value) : Prop :=
  ∀ offered ∈ entries, current store offered.1 = some offered

/-- Each callback preserves only dependencies still due after its own answer.
Already delivered occurrences may be removed. A repeated occurrence still due
later remains a dependency. -/
def Preserves : List (Offer Value) → (Offer Value → Store Value → Store Value) → Prop
  | [], _ => True
  | used :: later, client =>
    (∀ store offered, offered ∈ later → current store offered.1 = some offered →
      current (client used store) offered.1 = some offered) ∧ Preserves later client

theorem live_and_historical_delivery_agree (entries : List (Offer Value))
    (client : Offer Value → Store Value → Store Value) (store : Store Value)
    (live : Live entries store) (frame : Preserves entries client) :
    consume client (kept entries store) = consume client (captured entries store) := by
  induction entries generalizing store with
  | nil => rfl
  | cons offered rest ih =>
    have here := live offered List.mem_cons_self
    have laterLive : Live rest (client offered store) := by
      intro later member
      exact frame.1 store later member
        (live later (List.mem_cons_of_mem _ member))
    simp only [kept, here, ↓reduceIte]
    exact congrArg (fun pair : List (Offer Value) × Store Value =>
      (offered :: pair.1, pair.2)) (ih _ laterLive frame.2)

namespace Controls

open ReadAdmissionProfiles.Controls (entry entryRows)

def addUnrelated (offered : Offer Nat) (store : Store Nat) : Store Nat :=
  StampedSnapshots.add store (offered.2 + 100)

theorem effectful_caller_can_keep_both_read_contracts :
    consume addUnrelated (kept entryRows entry) =
      consume addUnrelated (captured entryRows entry) := by rfl

theorem caller_really_added_rows :
    let after := (consume addUnrelated (captured entryRows entry)).2
    after.next = 4 ∧ current after 2 = some (2, 110) ∧ current after 3 = some (3, 120) := by decide

def removeDelivered (offered : Offer Nat) (store : Store Nat) : Store Nat :=
  StampedSnapshots.remove store offered.1

theorem deleting_delivered_rows_can_preserve_delivery :
    consume removeDelivered (kept entryRows entry) =
      consume removeDelivered (captured entryRows entry) := by rfl

theorem delivered_rows_really_were_removed :
    let after := (consume removeDelivered (kept entryRows entry)).2
    current after 0 = none ∧ current after 1 = none := by decide

def removeLater (_ : Offer Nat) (store : Store Nat) : Store Nat :=
  StampedSnapshots.remove store 1

theorem an_interfering_caller_separates_delivery :
    (consume removeLater (captured entryRows entry)).1 = [(0, 10), (1, 20)] ∧
      (consume removeLater (kept entryRows entry)).1 = [(0, 10)] := by decide

end Controls

end Mettapedia.Machines.StoreInteraction.ReadDelivery
