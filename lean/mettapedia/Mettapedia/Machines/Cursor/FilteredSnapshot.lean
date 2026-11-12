import Mettapedia.Machines.Cursor.Sequence

/-!
# Demand-driven filtering of a retained array snapshot

Opening a reader retains an existing array and two bounds. A pull inspects
only the prefix ending at its next accepted row, decoding that row alone.
The independently defined meaning filters the complete retained slice.
The provider hom preserves that meaning for every adaptive cursor client.

The inspection meter counts existing array cells tested, not instructions or
predicate complexity. The decoding meter counts calls to the supplied pure
decoder. Building the backing array, retaining its native lifetime, and
concurrent publication are separate implementation obligations. One pull may
inspect many rejected rows; its answer quota is not an internal work budget.
The backing array is retained in full; this is not constant total retention.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.FilteredSnapshot

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

variable {Row Item : Type}

structure Search (Row Item : Type) where
  answer : Option Item
  rest : Sequence.Slice Row
  inspected : Nat

/-- A recursive array walk. Rejected rows advance the retained offset rather
than becoming a private list of candidates. No cell after a successful row
is inspected by this call. -/
def search (accept : Row → Bool) (decode : Row → Item) (storage : Array Row) :
    Nat → Nat → Search Row Item
  | offset, 0 => ⟨none, ⟨storage, offset, 0⟩, 0⟩
  | offset, remaining + 1 =>
      match storage[offset]? with
      | none => ⟨none, ⟨storage, offset, remaining + 1⟩, 0⟩
      | some row =>
          if accept row then
            ⟨some (decode row), ⟨storage, offset + 1, remaining⟩, 1⟩
          else
            let later := search accept decode storage (offset + 1) remaining
            { later with inspected := 1 + later.inspected }

def meaning (accept : Row → Bool) (decode : Row → Item)
    (view : Sequence.Slice Row) : List Item :=
  ((view.storage.toList.drop view.offset).take view.remaining).filterMap
    (fun row => if accept row then some (decode row) else none)

def provider (accept : Row → Bool) (decode : Row → Item) :
    Provider (Sequence.protocol Item) where
  State _ _ := Sequence.Slice Row
  step view _ :=
    let found := search accept decode view.storage view.offset view.remaining
    ⟨found.answer, found.rest⟩

/-- The initial representation retains the input array; it does not run a
filter, copy its rows, or decode any answer. -/
def start (storage : Array Row) : Sequence.Slice Row := ⟨storage, 0, storage.size⟩

@[simp] theorem meaning_open (accept : Row → Bool) (decode : Row → Item)
    (storage : Array Row) :
    meaning accept decode (start storage) = storage.toList.filterMap
      (fun row => if accept row then some (decode row) else none) := by
  simp only [meaning, start, List.drop_zero]
  rw [Array.size_eq_length_toList, List.take_length]

theorem search_correct (accept : Row → Bool) (decode : Row → Item)
    (storage : Array Row) (remaining offset : Nat) :
    (⟨(search accept decode storage offset remaining).answer,
        meaning accept decode (search accept decode storage offset remaining).rest⟩ :
        Option Item × List Item) =
      match meaning accept decode ⟨storage, offset, remaining⟩ with
      | [] => (none, [])
      | first :: rest => (some first, rest) := by
  induction remaining generalizing offset with
  | zero => simp [search, meaning]
  | succ remaining ih =>
      cases found : storage[offset]? with
      | none =>
          have empty : storage.toList.drop offset = [] := by
            apply List.drop_eq_nil_iff.mpr
            simpa using (Array.getElem?_eq_none_iff.mp found)
          simp [search, found, meaning, empty]
      | some row =>
          have listed : storage.toList[offset]? = some row := by simpa using found
          obtain ⟨within, atRow⟩ := List.getElem?_eq_some_iff.mp listed
          have head := List.drop_eq_getElem_cons within
          rw [atRow] at head
          by_cases accepted : accept row = true
          · simp [search, found, accepted, meaning, head]
          · simpa [search, found, accepted, meaning, head] using
              ih (offset + 1)

/-- This is earned from the array walk, not an assumed equality between two
implementations. Order, duplicates, exhaustion and the residual all survive. -/
def refinement (accept : Row → Bool) (decode : Row → Item) :
    Hom (provider accept decode) (Sequence.tails Item) where
  map := meaning accept decode
  step view request := by
    rcases view with ⟨storage, offset, remaining⟩
    cases request
    have result := search_correct accept decode storage remaining offset
    change (⟨(search accept decode storage offset remaining).answer,
        meaning accept decode (search accept decode storage offset remaining).rest⟩ :
        Sigma fun _ : Option Item => List Item) = _
    cases semantic : meaning accept decode ⟨storage, offset, remaining⟩ with
    | nil =>
        simp only [semantic] at result
        exact Sigma.ext (congrArg Prod.fst result) (heq_of_eq (congrArg Prod.snd result))
    | cons first rest =>
        simp only [semantic] at result
        exact Sigma.ext (congrArg Prod.fst result) (heq_of_eq (congrArg Prod.snd result))

def inspections (accept : Row → Bool) (decode : Row → Item) :
    Charge (provider accept decode) := fun view _ =>
  (search accept decode view.storage view.offset view.remaining).inspected

def decodings (accept : Row → Bool) (decode : Row → Item) :
    Charge (provider accept decode) := fun view _ =>
  if (search accept decode view.storage view.offset view.remaining).answer.isSome then 1 else 0

/-- Every inspected existing row is removed from the residual interval.
Malformed views preserve the inaccessible remainder rather than claiming to
have inspected nonexistent cells. -/
theorem search_conservation (accept : Row → Bool) (decode : Row → Item)
    (storage : Array Row) (remaining offset : Nat) :
    (search accept decode storage offset remaining).inspected +
        (search accept decode storage offset remaining).rest.remaining = remaining := by
  induction remaining generalizing offset with
  | zero => rfl
  | succ remaining ih =>
      cases found : storage[offset]? with
      | none => simp [search, found]
      | some row =>
          by_cases accepted : accept row = true
          · simp [search, found, accepted, Nat.add_comm]
          · simp only [search, found, accepted, Bool.false_eq_true, ↓reduceIte]
            have conserved := ih (offset + 1)
            omega

theorem search_keeps_storage (accept : Row → Bool) (decode : Row → Item)
    (storage : Array Row) (remaining offset : Nat) :
    (search accept decode storage offset remaining).rest.storage = storage := by
  induction remaining generalizing offset with
  | zero => rfl
  | succ remaining ih =>
      cases found : storage[offset]? with
      | none => simp [search, found]
      | some row =>
          by_cases accepted : accept row = true
          · simp [search, found, accepted]
          · simpa [search, found, accepted] using ih (offset + 1)

theorem search_offset (accept : Row → Bool) (decode : Row → Item)
    (storage : Array Row) (remaining offset : Nat) :
    (search accept decode storage offset remaining).rest.offset =
      offset + (search accept decode storage offset remaining).inspected := by
  induction remaining generalizing offset with
  | zero => simp [search]
  | succ remaining ih =>
      cases found : storage[offset]? with
      | none => simp [search, found]
      | some row =>
          by_cases accepted : accept row = true
          · simp [search, found, accepted]
          · simpa [search, found, accepted, Nat.add_assoc] using ih (offset + 1)

variable {Return : Unit → Unit → Type}

def remainingPotential (accept : Row → Bool) (decode : Row → Item) :
    Potential (provider accept decode) := fun view => view.remaining

/-- Every adaptive client sees the same ordered replies and the same semantic
residual, whether it stops, suspends, or continues after an earlier reply. -/
theorem advance_observation (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (control : C.V () ()) (storage : Array Row) :
    (refinement accept decode).outcome C
        (advance (provider accept decode) C (inspections accept decode) fuel
          ⟨(), control, start storage⟩).2 =
      (advance (Sequence.tails Item) C (Sequence.requested Item) fuel
        ⟨(), control, storage.toList.filterMap
          (fun row => if accept row then some (decode row) else none)⟩).2 := by
  simpa only [Hom.packet, refinement, meaning_open] using
    Hom.advance C (refinement accept decode) (inspections accept decode)
      (Sequence.requested Item) fuel ⟨(), control, start storage⟩

/-- An exact prefix account: inspections plus the actual retained remainder
equal the initial interval length. It includes failed probes, not just answers. -/
theorem advance_conservation (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (packet : Packet (provider accept decode) C ()) :
    (advance (provider accept decode) C (inspections accept decode) fuel packet).1 +
        outcomePotential C (remainingPotential accept decode)
          (advance (provider accept decode) C (inspections accept decode) fuel packet).2 =
      packet.2.2.remaining := by
  induction fuel generalizing packet with
  | zero => simp [advance, outcomePotential, remainingPotential]
  | succ fuel ih =>
      rcases packet with ⟨⟨⟩, control, view⟩
      cases layer : C.str () () control with
      | mk shape children =>
          cases shape with
          | inl answer => simp [advance, layer, outcomePotential, remainingPotential]
          | inr request =>
              dsimp only [withHoles] at children
              have later := ih ⟨(), children
                  ((provider accept decode).step view request).1,
                ((provider accept decode).step view request).2⟩
              have conserved := search_conservation accept decode view.storage
                view.remaining view.offset
              simp only [advance, layer]
              dsimp only [withHoles]
              dsimp only [provider, inspections, remainingPotential, Sequence.protocol] at later ⊢
              omega

theorem advance_inspections_le (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (packet : Packet (provider accept decode) C ()) :
    (advance (provider accept decode) C (inspections accept decode) fuel packet).1 ≤
      packet.2.2.remaining := by
  have conserved := advance_conservation accept decode C fuel packet
  omega

/-- Splitting the run does not buy another scan of the retained prefix.
The old account and the actual continuation are passed to `resume`. -/
theorem resumed_inspections_le (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (first second : Nat) (packet : Packet (provider accept decode) C ()) :
    (resume (provider accept decode) C (inspections accept decode) second
      (advance (provider accept decode) C (inspections accept decode) first packet)).1 ≤
      packet.2.2.remaining := by
  rw [← advance_add]
  exact advance_inspections_le accept decode C (first + second) packet

theorem decodings_exact (accept : Row → Bool) (decode : Row → Item)
    (view : Sequence.Slice Row) :
    decodings accept decode (base := ()) (index := ()) view () =
      Sequence.requested Item (base := ()) (index := ()) (meaning accept decode view) () := by
  rcases view with ⟨storage, offset, remaining⟩
  have correct := congrArg Prod.fst (search_correct accept decode storage remaining offset)
  cases semantic : meaning accept decode ⟨storage, offset, remaining⟩ with
  | nil => simp [semantic] at correct; simp [decodings, correct, Sequence.requested]
  | cons first rest =>
      simp [semantic] at correct
      simp [decodings, correct, Sequence.requested]

/-- Decoding is charged only for answers actually delivered to the client,
including an arbitrary stopped or suspended prefix. -/
theorem advance_decodings_exact (accept : Row → Bool) (decode : Row → Item)
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (packet : Packet (provider accept decode) C ()) :
    (advance (provider accept decode) C (decodings accept decode) fuel packet).1 =
      (advance (Sequence.tails Item) C (Sequence.requested Item) fuel
        ((refinement accept decode).packet C packet)).1 := by
  apply Hom.advance_charge C (refinement accept decode) (decodings accept decode)
    (Sequence.requested Item) ?_ fuel packet
  intro base index view request
  cases base; cases index; cases request
  exact decodings_exact accept decode view

end Mettapedia.Machines.Cursor.FilteredSnapshot
