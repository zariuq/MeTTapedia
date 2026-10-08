import Mettapedia.Evidence.SourceScoped
import Mathlib.Data.List.AList
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Prod

/-!
An idempotent delivery protocol over the existing association-list store.
Equal source and payload deliveries retain one packet; a changed payload is
refused unless explicitly replaced. This protocol concerns source identity,
and does not assert probabilistic independence of distinct sources.
-/

namespace Mettapedia.Evidence.SourcePacketStore

universe u v
variable {Source : Type u} {Payload : Type v} [DecidableEq Source]

abbrev Store (Source : Type u) (Payload : Type v) := AList (fun _ : Source => Payload)

structure Packet (Source : Type u) (Payload : Type v) where
  source : Source
  payload : Payload
  deriving DecidableEq

instance : SourceScoped (Packet Source Payload) Source where
  sourceScope packet := {packet.source}

def deliver [DecidableEq Payload] (store : Store Source Payload) (packet : Packet Source Payload) :
    Option (Store Source Payload) :=
  match store.lookup packet.source with
  | none => some (store.insert packet.source packet.payload)
  | some previous => if previous = packet.payload then some store else none

def ingest [DecidableEq Payload] (store : Store Source Payload) :
    List (Packet Source Payload) → Option (Store Source Payload)
  | [] => some store
  | packet :: rest => (deliver store packet).bind (fun next => ingest next rest)

theorem delivered_lookup [DecidableEq Payload] {store next : Store Source Payload}
    {packet : Packet Source Payload} (accepted : deliver store packet = some next) :
    next.lookup packet.source = some packet.payload := by
  cases previous : store.lookup packet.source with
  | none =>
      simp only [deliver, previous] at accepted
      cases accepted
      exact AList.lookup_insert store
  | some old =>
      by_cases same : old = packet.payload
      · simp only [deliver, previous, if_pos same, Option.some.injEq] at accepted
        subst next
        simpa [same] using previous
      · simp [deliver, previous, same] at accepted

theorem delivered_other [DecidableEq Payload] {store next : Store Source Payload}
    {packet : Packet Source Payload} (accepted : deliver store packet = some next)
    {other : Source} (different : other ≠ packet.source) :
    next.lookup other = store.lookup other := by
  cases previous : store.lookup packet.source with
  | none =>
      simp only [deliver, previous, Option.some.injEq] at accepted
      subst next
      exact AList.lookup_insert_ne different
  | some old =>
      by_cases same : old = packet.payload
      · simp only [deliver, previous, if_pos same, Option.some.injEq] at accepted
        subst next
        rfl
      · simp [deliver, previous, same] at accepted

theorem deliver_existing [DecidableEq Payload] (store : Store Source Payload)
    (packet : Packet Source Payload) (present : store.lookup packet.source = some packet.payload) :
    deliver store packet = some store := by simp [deliver, present]

theorem deliver_conflict [DecidableEq Payload] (store : Store Source Payload)
    (packet : Packet Source Payload) (previous : Payload)
    (present : store.lookup packet.source = some previous) (changed : previous ≠ packet.payload) :
    deliver store packet = none := by simp [deliver, present, changed]

theorem deliver_idempotent [DecidableEq Payload] (store : Store Source Payload)
    (packet : Packet Source Payload) :
    (deliver store packet).bind (fun next => deliver next packet) = deliver store packet := by
  cases outcome : deliver store packet with
  | none => simp
  | some next =>
      simp only [Option.bind_some]
      exact deliver_existing next packet (delivered_lookup outcome)

theorem duplicate_head [DecidableEq Payload] (store : Store Source Payload)
    (packet : Packet Source Payload) (rest : List (Packet Source Payload)) :
    ingest store (packet :: packet :: rest) = ingest store (packet :: rest) := by
  simp only [ingest]
  rw [← Option.bind_assoc, deliver_idempotent]

theorem retract_replacement (store : Store Source Payload) (source : Source) (payload : Payload) :
    (store.insert source payload).erase source = store.erase source := by
  apply AList.ext
  simp [AList.erase, AList.entries_insert, List.kerase_cons_eq]

def counts (store : Store Source (ℕ × ℕ)) : ℕ × ℕ :=
  (store.entries.map (fun entry => entry.2)).sum

theorem counts_insert (store : Store Source (ℕ × ℕ)) (source : Source) (payload : ℕ × ℕ) :
    counts (store.insert source payload) = payload + counts (store.erase source) := by
  simp [counts, AList.entries_insert, AList.erase]

theorem repeated_counts (store : Store Source (ℕ × ℕ)) (packet : Packet Source (ℕ × ℕ))
    (present : store.lookup packet.source = some packet.payload) :
    (deliver store packet).map counts = some (counts store) := by
  rw [deliver_existing store packet present]
  rfl

theorem conflicting_delivery_refused :
    ingest (∅ : Store ℕ (ℕ × ℕ)) [⟨1, (3, 1)⟩, ⟨1, (2, 2)⟩] = none := by decide

theorem repeated_delivery_not_additive :
    (ingest (∅ : Store ℕ (ℕ × ℕ)) [⟨1, (3, 1)⟩, ⟨1, (3, 1)⟩]).map counts = some (3, 1) := by decide

end Mettapedia.Evidence.SourcePacketStore
