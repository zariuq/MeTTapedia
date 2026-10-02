import Mettapedia.Languages.ProcessCalculi.MORK.MM2GivenClause
import Mettapedia.Languages.ProcessCalculi.MORK.MM2FiniteListMembership

/-!
# Retaining generated occurrences in MM2 support storage

A generated value is stored together with its owned occurrence trace. The
existing MM2 nested-list representation carries the trace, using finite
symbolic counters rather than host-grounded integers. This is an explicit
encoding protocol: forgetting the tags AFTER support storage recovers the
occurrence bag when identities are fresh. Storing untagged values first loses
that information. Reusing an identity remains idempotent; ordinary support
union is not a faithful implementation of unrestricted bag addition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2OccurrenceSupport

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Core.InferenceControl (WorkOccurrence)
open MM2GivenClause (Node)
open MM2FiniteListMembership (encodedListAtom encodedListAtom_injective)

def counter (n : Nat) : Atom := encodedListAtom (List.replicate n (.symbol "tick"))

def traceAtom (trace : List Nat) : Atom := encodedListAtom (trace.map counter)

def encode (occurrence : Node) : Atom :=
  .expression [.symbol "occurrence", traceAtom occurrence.trace, occurrence.state]

def erase : Atom → Atom
  | .expression [.symbol "occurrence", _, value] => value
  | other => other

def support (occurrences : List Node) : Space := (occurrences.map encode).toFinset

/-- The shared linked-list syntax has bounded arity at every node and retains
the incoming variable environment when its elements do. -/
theorem list_encoding (environment : List String) (items : List Atom)
    (elements : ∀ item ∈ items, ∃ bytes,
      morkCompactEncodeAtom environment item = some (bytes, environment)) :
    ∃ bytes, morkCompactEncodeAtom environment (encodedListAtom items) =
      some (bytes, environment) := by
  induction items with
  | nil => exact ⟨[1, 198, 109, 109, 45, 110, 105, 108], rfl⟩
  | cons head tail ih =>
      obtain ⟨headBytes, headExact⟩ := elements head (by simp)
      obtain ⟨tailBytes, tailExact⟩ := ih (fun item member => elements item (by simp [member]))
      refine ⟨[3, 199, 109, 109, 45, 99, 111, 110, 115] ++ headBytes ++ tailBytes, ?_⟩
      simp only [encodedListAtom, MM2FiniteListMembership.consAtom, morkCompactEncodeAtom]
      rw [if_pos (by simp)]
      simp only [morkCompactEncodeAtom.encodeList]
      have consExact : morkCompactEncodeAtom environment (.symbol "mm-cons") =
          some ([199, 109, 109, 45, 99, 111, 110, 115], environment) := rfl
      rw [consExact]
      simp only
      rw [headExact]
      simp only
      rw [tailExact]
      simp

theorem counter_encoding (environment : List String) (n : Nat) :
    ∃ bytes, morkCompactEncodeAtom environment (counter n) = some (bytes, environment) := by
  apply list_encoding
  intro item member
  have same : item = .symbol "tick" := (List.mem_replicate.mp member).2
  subst item
  exact ⟨[196, 116, 105, 99, 107], rfl⟩

theorem trace_encoding (environment : List String) (trace : List Nat) :
    ∃ bytes, morkCompactEncodeAtom environment (traceAtom trace) = some (bytes, environment) := by
  apply list_encoding
  intro item member
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp member
  exact counter_encoding environment n

/-- Tags introduce neither host-grounded values nor unsupported variable
indices. Any already representable payload stays representable. -/
theorem encode_representable (occurrence : Node)
    (payload : MorkCompactRepresentable occurrence.state) :
    MorkCompactRepresentable (encode occurrence) := by
  obtain ⟨key, exactKey⟩ := payload
  unfold morkCompactKey? at exactKey
  obtain ⟨⟨bytes, after⟩, encoded, _⟩ := Option.map_eq_some_iff.mp exactKey
  obtain ⟨traceBytes, traceExact⟩ := trace_encoding [] occurrence.trace
  refine ⟨[3, 202, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101] ++ traceBytes ++ bytes, ?_⟩
  simp only [morkCompactKey?, encode, morkCompactEncodeAtom]
  rw [if_pos (by simp)]
  simp only [morkCompactEncodeAtom.encodeList]
  have tagExact : morkCompactEncodeAtom [] (.symbol "occurrence") =
      some ([202, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101], []) := rfl
  rw [tagExact]
  simp only
  rw [traceExact]
  simp only
  rw [encoded]
  simp

def nilBytes : List Nat := [1, 198, 109, 109, 45, 110, 105, 108]
def cellBytes : List Nat := [3, 199, 109, 109, 45, 99, 111, 110, 115]
def tickBytes : List Nat := [196, 116, 105, 99, 107]

def counterBytes : Nat → List Nat
  | 0 => nilBytes
  | n + 1 => cellBytes ++ tickBytes ++ counterBytes n

def traceBytes : List Nat → List Nat
  | [] => nilBytes
  | n :: rest => cellBytes ++ counterBytes n ++ traceBytes rest

theorem counter_encoding_exact (environment : List String) (n : Nat) :
    morkCompactEncodeAtom environment (counter n) = some (counterBytes n, environment) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change morkCompactEncodeAtom environment
        (MM2FiniteListMembership.consAtom (.symbol "tick") (counter n)) = _
      simp only [MM2FiniteListMembership.consAtom, morkCompactEncodeAtom]
      rw [if_pos (by simp)]
      simp only [morkCompactEncodeAtom.encodeList]
      have consExact : morkCompactEncodeAtom environment (.symbol "mm-cons") =
          some (cellBytes.tail, environment) := rfl
      rw [consExact]
      simp only
      have tickExact : morkCompactEncodeAtom environment (.symbol "tick") =
          some (tickBytes, environment) := rfl
      rw [tickExact]
      simp only
      rw [ih]
      simp [counterBytes, cellBytes, tickBytes]

theorem trace_encoding_exact (environment : List String) (trace : List Nat) :
    morkCompactEncodeAtom environment (traceAtom trace) = some (traceBytes trace, environment) := by
  induction trace with
  | nil => rfl
  | cons n rest ih =>
      change morkCompactEncodeAtom environment
        (MM2FiniteListMembership.consAtom (counter n) (traceAtom rest)) = _
      simp only [MM2FiniteListMembership.consAtom, morkCompactEncodeAtom]
      rw [if_pos (by simp)]
      simp only [morkCompactEncodeAtom.encodeList]
      have consExact : morkCompactEncodeAtom environment (.symbol "mm-cons") =
          some (cellBytes.tail, environment) := rfl
      rw [consExact]
      simp only
      rw [counter_encoding_exact]
      simp only
      rw [ih]
      simp [traceBytes, cellBytes]

/-- Counter encodings delimit themselves before any following payload. -/
theorem counter_bytes_delimited (left right : Nat) (tailLeft tailRight : List Nat)
    (equal : counterBytes left ++ tailLeft = counterBytes right ++ tailRight) :
    left = right ∧ tailLeft = tailRight := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => simpa [counterBytes, nilBytes] using equal
      | succ right => simp [counterBytes, nilBytes, cellBytes] at equal
  | succ left ih =>
      cases right with
      | zero => simp [counterBytes, nilBytes, cellBytes] at equal
      | succ right =>
          have smaller : counterBytes left ++ tailLeft = counterBytes right ++ tailRight := by
            simpa [counterBytes, cellBytes, tickBytes, List.append_assoc] using equal
          obtain ⟨rfl, tails⟩ := ih right smaller
          exact ⟨rfl, tails⟩

/-- Trace encodings delimit themselves even when payload bytes differ. -/
theorem trace_bytes_delimited (left right : List Nat) (tailLeft tailRight : List Nat)
    (equal : traceBytes left ++ tailLeft = traceBytes right ++ tailRight) :
    left = right ∧ tailLeft = tailRight := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => simpa [traceBytes, nilBytes] using equal
      | cons n rest => simp [traceBytes, nilBytes, cellBytes] at equal
  | cons n rest ih =>
      cases right with
      | nil => simp [traceBytes, nilBytes, cellBytes] at equal
      | cons m later =>
          have inner : counterBytes n ++ (traceBytes rest ++ tailLeft) =
              counterBytes m ++ (traceBytes later ++ tailRight) := by
            simpa [traceBytes, cellBytes, List.append_assoc] using equal
          obtain ⟨rfl, smaller⟩ := counter_bytes_delimited n m _ _ inner
          obtain ⟨rfl, tails⟩ := ih later smaller
          exact ⟨rfl, tails⟩

theorem encoded_key_prefix (occurrence : Node) (key : List Nat)
    (encoded : morkCompactKey? (encode occurrence) = some key) :
    ∃ payload, key = [3, 202, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101] ++
      traceBytes occurrence.trace ++ payload := by
  simp only [morkCompactKey?, encode, morkCompactEncodeAtom] at encoded
  rw [if_pos (by simp)] at encoded
  simp only [morkCompactEncodeAtom.encodeList] at encoded
  have tagExact : morkCompactEncodeAtom [] (.symbol "occurrence") =
      some ([202, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101], []) := rfl
  rw [tagExact] at encoded
  simp only at encoded
  rw [trace_encoding_exact] at encoded
  simp only at encoded
  cases payloadExact : morkCompactEncodeAtom [] occurrence.state with
  | none => simp [payloadExact] at encoded
  | some payload =>
      rcases payload with ⟨bytes, environment⟩
      simp only [payloadExact, List.append_nil, Option.map_some, Option.some.injEq] at encoded
      exact ⟨bytes, by simpa [List.append_assoc] using encoded.symm⟩

/-- Fresh occurrence paths remain distinct in the actual compact byte store,
including when their payloads have the same value or alpha-equivalent syntax. -/
theorem physical_keys_keep_traces (left right : Node) (key : List Nat)
    (leftEncoded : morkCompactKey? (encode left) = some key)
    (rightEncoded : morkCompactKey? (encode right) = some key) :
    left.trace = right.trace := by
  obtain ⟨leftBytes, leftExact⟩ := encoded_key_prefix left key leftEncoded
  obtain ⟨rightBytes, rightExact⟩ := encoded_key_prefix right key rightEncoded
  have same : traceBytes left.trace ++ leftBytes = traceBytes right.trace ++ rightBytes := by
    simpa [List.append_assoc] using leftExact.symm.trans rightExact
  exact (trace_bytes_delimited _ _ _ _ same).1

theorem counter_injective : Function.Injective counter := by
  intro left right equal
  have same := congrArg List.length (encodedListAtom_injective equal)
  simpa using same

theorem traceAtom_injective : Function.Injective traceAtom := by
  intro left right equal
  exact List.map_injective_iff.mpr counter_injective (encodedListAtom_injective equal)

theorem encode_injective : Function.Injective encode := by
  rintro ⟨left, leftTrace⟩ ⟨right, rightTrace⟩ equal
  simp only [encode, Atom.expression.injEq, List.cons.injEq, true_and] at equal
  obtain ⟨traces, values, _⟩ := equal
  have tracesEqual := traceAtom_injective traces
  cases tracesEqual
  cases values
  rfl

@[simp] theorem erase_encode (occurrence : Node) : erase (encode occurrence) = occurrence.state := rfl

theorem encoded_nodup (occurrences : List Node)
    (fresh : (occurrences.map WorkOccurrence.trace).Nodup) :
    (occurrences.map encode).Nodup := by
  exact (List.Nodup.of_map WorkOccurrence.trace fresh).map encode_injective

/-- The physical trie also retains every fresh, representable occurrence.
This does not assume injectivity of compact keys on arbitrary variable syntax. -/
theorem physical_keys_nodup (occurrences : List Node)
    (fresh : (occurrences.map WorkOccurrence.trace).Nodup)
    (payloads : ∀ occurrence ∈ occurrences, MorkCompactRepresentable occurrence.state) :
    (occurrences.map (fun occurrence => totalMorkCompactKey (encode occurrence))).Nodup := by
  refine List.Nodup.map_on ?_ (List.Nodup.of_map WorkOccurrence.trace fresh)
  intro left leftMember right rightMember same
  obtain ⟨leftKey, leftExact⟩ := encode_representable left (payloads left leftMember)
  obtain ⟨rightKey, rightExact⟩ := encode_representable right (payloads right rightMember)
  simp only [totalMorkCompactKey, leftExact, rightExact, Option.getD_some] at same
  subst rightKey
  have sameTrace := physical_keys_keep_traces left right leftKey leftExact rightExact
  exact List.inj_on_of_nodup_map fresh leftMember rightMember sameTrace

theorem physical_support_card (occurrences : List Node)
    (fresh : (occurrences.map WorkOccurrence.trace).Nodup)
    (payloads : ∀ occurrence ∈ occurrences, MorkCompactRepresentable occurrence.state) :
    (occurrences.map (fun occurrence => totalMorkCompactKey (encode occurrence))).toFinset.card =
      occurrences.length := by
  simpa using List.toFinset_card_of_nodup (physical_keys_nodup occurrences fresh payloads)

theorem support_card (occurrences : List Node)
    (fresh : (occurrences.map WorkOccurrence.trace).Nodup) :
    (support occurrences).card = occurrences.length := by
  simpa [support] using List.toFinset_card_of_nodup (encoded_nodup occurrences fresh)

/-- Fresh identities allow support storage while preserving an answer bag.
The equality is in `Multiset`, so no physical iteration order is promised. -/
theorem erase_support_bag (occurrences : List Node)
    (fresh : (occurrences.map WorkOccurrence.trace).Nodup) :
    (support occurrences).val.map erase =
      ((occurrences.map WorkOccurrence.state : List Atom) : Multiset Atom) := by
  unfold support
  rw [List.toFinset_val, List.dedup_eq_self.mpr (encoded_nodup occurrences fresh)]
  simp [Function.comp_def]

theorem generated_bag_survives_storage (given : Node) (conclusion : Atom)
    (rows : List MM2MatchingCursor.Row) (first : Nat) :
    (support (MM2GivenClause.children given conclusion rows first)).val.map erase =
      (((MM2GivenClause.children given conclusion rows first).map WorkOccurrence.state :
        List Atom) : Multiset Atom) := by
  exact erase_support_bag _ (MM2GivenClause.children_occurrence_nodup _ _ _ _)

/-- Support deduplicates repeated uses of the same identity; callers must
allocate fresh occurrence paths when performing bag addition. -/
theorem repeated_identity_remains_idempotent (occurrence : Node) :
    support [occurrence, occurrence] = support [occurrence] := by simp [support]

namespace Controls
open MM2GivenClause.Controls

theorem two_route_occurrences_survive :
    (support ((MM2GivenClause.system premises conclusion).generate root processed)).card = 2 := by
  rw [two_derivations_one_value]
  decide

theorem untagged_support_loses_one_occurrence :
    (((MM2GivenClause.system premises conclusion).generate root processed).map
      WorkOccurrence.state).toFinset.card = 1 := by
  rw [two_derivations_one_value]
  decide

theorem actual_compact_keys_distinguish_routes :
    (morkCompactKey? (encode ⟨answer, [7, 0]⟩)).isSome = true ∧
      (morkCompactKey? (encode ⟨answer, [7, 1]⟩)).isSome = true ∧
      morkCompactKey? (encode ⟨answer, [7, 0]⟩) ≠
        morkCompactKey? (encode ⟨answer, [7, 1]⟩) := by decide

end Controls

#print axioms physical_keys_keep_traces
#print axioms physical_support_card
#print axioms encode_representable
#print axioms encode_injective
#print axioms erase_support_bag
#print axioms generated_bag_survives_storage
#print axioms Controls.actual_compact_keys_distinguish_routes

end Mettapedia.Languages.ProcessCalculi.MORK.MM2OccurrenceSupport
