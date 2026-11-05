import Mettapedia.Machines.VariableInventory

/-!
# Staging decoded declarations and growing a paired variable scope

The reference decodes an ordered batch before semantic publication. The target
accumulates a private reversed image; resource refusal discards that image and
never enters a fallback reader. Both preserve the actual decoder world,
including any internally owned interning prefix or consumed fresh identities.

The paired-buffer algorithm distinguishes physical allocation extents from the
common capacity authorized for writes. A successful first realloc may remain
owned after the second refuses. The common bound changes only after both have
succeeded. Existing VariableInventory entries/lookup represent scoped names.

This models preparation and reservation algorithms, not the byte codec, C
allocation/free, finite VarId overflow, term-universe ownership or publication
allocation. Publication after preparation is a total semantic append here.
Nonresource fallback is distinct; the separate lowered/tree path is not
qualified by the resource-refusal law.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.DecoderPreparation

variable {Input Row World : Type}

inductive Fault where
  | resource | unsupported
  deriving DecidableEq, Repr

abbrev Decoder (World Input Row : Type) := World → Input → World × Except Fault Row
abbrev Prepared (World Row : Type) := World × Except Fault (List Row)
abbrev Published (World Row : Type) := World × List Row × Except Fault Unit

namespace Reference

/-- The source builds its ordered list from returned heads and later results. -/
def decode (read : Decoder World Input Row) : List Input → World → Prepared World Row
  | [], world => (world, .ok [])
  | input :: rest, world =>
      let first := read world input
      match first.2 with
      | .error fault => (first.1, .error fault)
      | .ok row =>
          let later := decode read rest first.1
          (later.1, later.2.map (row :: ·))

end Reference

namespace Native

/-- The private array is represented in reverse construction order. An error
does not return that candidate in its error channel; its world remains opaque. -/
def stage (read : Decoder World Input Row) : List Input → World → List Row → Prepared World Row
  | [], world, reversed => (world, .ok reversed.reverse)
  | input :: rest, world, reversed =>
      let first := read world input
      match first.2 with
      | .error fault => (first.1, .error fault)
      | .ok row => stage read rest first.1 (row :: reversed)

def publish (keep : Row → Bool) (before : List Row) (prepared : Prepared World Row)
    (fallback : World → List Row → Published World Row) : Published World Row :=
  match prepared.2 with
  | .ok rows => (prepared.1, before ++ rows.filter keep, .ok ())
  | .error .resource => (prepared.1, before, .error .resource)
  | .error .unsupported => fallback prepared.1 before

def load (read : Decoder World Input Row) (keep : Row → Bool) (inputs : List Input)
    (world : World) (before : List Row) (fallback : World → List Row → Published World Row) :
    Published World Row := publish keep before (stage read inputs world []) fallback

end Native

theorem staging_refines (read : Decoder World Input Row) (inputs : List Input)
    (world : World) (reversed : List Row) :
    Native.stage read inputs world reversed =
      let decoded := Reference.decode read inputs world
      (decoded.1, decoded.2.map (reversed.reverse ++ ·)) := by
  induction inputs generalizing world reversed with
  | nil => simp [Native.stage, Reference.decode, Except.map]
  | cons input rest ih =>
      cases first : read world input with
      | mk after result =>
          cases result with
          | error fault => simp [Native.stage, Reference.decode, first, Except.map]
          | ok row =>
              rw [Native.stage, first]
              simp only
              rw [ih]
              cases later : Reference.decode read rest after with
              | mk final result => cases result <;>
                  simp [Reference.decode, first, later, Except.map, List.reverse_cons, List.append_assoc]

theorem prepared_batch_refines (read : Decoder World Input Row) (inputs : List Input) (world : World) :
    Native.stage read inputs world [] = Reference.decode read inputs world := by
  have staged := staging_refines read inputs world []
  cases decoded : Reference.decode read inputs world with
  | mk after result => cases result <;> simpa [decoded, Except.map] using staged

/-- Resource refusal is independent of every possible fallback reader, even
one that would change the world or publish rows. Internal effects remain. -/
theorem resource_refusal_preserves_publication (read : Decoder World Input Row)
    (inputs : List Input) (world after : World) (before : List Row) (keep : Row → Bool)
    (failed : Reference.decode read inputs world = (after, .error .resource))
    (fallback : World → List Row → Published World Row) :
    Native.load read keep inputs world before fallback = (after, before, .error .resource) := by
  simp [Native.load, prepared_batch_refines, failed, Native.publish]

theorem successful_publication_is_ordered (read : Decoder World Input Row)
    (inputs : List Input) (world after : World) (before rows : List Row) (keep : Row → Bool)
    (decoded : Reference.decode read inputs world = (after, .ok rows))
    (fallback : World → List Row → Published World Row) :
    Native.load read keep inputs world before fallback = (after, before ++ rows.filter keep, .ok ()) := by
  simp [Native.load, prepared_batch_refines, decoded, Native.publish]

theorem source_append (read : Decoder World Input Row) (first later : List Input) (world : World) :
    Reference.decode read (first ++ later) world =
      let prepared := Reference.decode read first world
      match prepared.2 with
      | .error fault => (prepared.1, .error fault)
      | .ok rows =>
          let rest := Reference.decode read later prepared.1
          (rest.1, rest.2.map (rows ++ ·)) := by
  induction first generalizing world with
  | nil =>
      cases decoded : Reference.decode read later world with
      | mk after result => cases result <;> simp [Reference.decode, decoded, Except.map]
  | cons input first ih =>
      cases current : read world input with
      | mk next result =>
          cases result with
          | error fault => simp [Reference.decode, current]
          | ok row =>
              simp only [List.cons_append, Reference.decode, current]
              rw [ih]
              cases before : Reference.decode read first next with
              | mk middle result =>
                  cases result with
                  | error fault => simp [Except.map]
                  | ok prefixRows =>
                      cases rest : Reference.decode read later middle with
                      | mk final result => cases result <;> simp [Except.map, rest]

theorem late_resource_refusal_keeps_actual_world (read : Decoder World Input Row)
    (earlier later : List Input) (input : Input) (world middle after : World) (decoded : List Row)
    (built : Reference.decode read earlier world = (middle, .ok decoded))
    (failed : read middle input = (after, .error .resource)) (before : List Row) (keep : Row → Bool)
    (fallback : World → List Row → Published World Row) :
    Native.load read keep (earlier ++ input :: later) world before fallback = (after, before, .error .resource) := by
  apply resource_refusal_preserves_publication
  simp [source_append, built, Reference.decode, failed, Except.map]

namespace Paired

variable {Name : Type}

structure Buffers (Name : Type) where
  entries : List (VariableInventory.Entry Name Nat)
  nextId : Nat
  common : Nat
  namesAllocated : Nat
  idsAllocated : Nat
  deriving DecidableEq, Repr

structure Allocations where
  names : Bool
  ids : Bool
  deriving DecidableEq, Repr

def Valid (buffers : Buffers Name) : Prop :=
  buffers.entries.length ≤ buffers.common ∧ buffers.common ≤ buffers.namesAllocated ∧
    buffers.idsAllocated = buffers.common

def logical (buffers : Buffers Name) := (buffers.entries, buffers.nextId, buffers.common)

def referenceReserve (requested : Nat) (allowed : Allocations) (buffers : Buffers Name) :
    (List (VariableInventory.Entry Name Nat) × Nat × Nat) × Bool :=
  if buffers.entries.length < buffers.common then (logical buffers, true)
  else if allowed.names && allowed.ids then ((buffers.entries, buffers.nextId, requested), true)
  else (logical buffers, false)

/-- The first returned allocation remains owned when the second refuses;
the shared write bound stays at its old value. -/
def reserve (requested : Nat) (allowed : Allocations) (buffers : Buffers Name) : Buffers Name × Bool :=
  if buffers.entries.length < buffers.common then (buffers, true) else
    if allowed.names then
      let first := {buffers with namesAllocated := requested}
      if allowed.ids then ({first with idsAllocated := requested, common := requested}, true)
      else (first, false)
    else (buffers, false)

theorem reserve_refines (requested : Nat) (allowed : Allocations) (buffers : Buffers Name) :
    let result := reserve requested allowed buffers
    (logical result.1, result.2) = referenceReserve requested allowed buffers := by
  by_cases room : buffers.entries.length < buffers.common <;>
    cases allowed <;> rename_i names ids <;> cases names <;> cases ids <;>
      simp [reserve, referenceReserve, logical, room]

theorem reserve_preserves_scope (requested : Nat) (allowed : Allocations) (buffers : Buffers Name) :
    (reserve requested allowed buffers).1.entries = buffers.entries ∧
      (reserve requested allowed buffers).1.nextId = buffers.nextId := by
  by_cases room : buffers.entries.length < buffers.common <;>
    cases allowed <;> rename_i names ids <;> cases names <;> cases ids <;> simp [reserve, room]

theorem reserve_preserves_validity (requested : Nat) (allowed : Allocations) (buffers : Buffers Name)
    (valid : Valid buffers) (growth : buffers.common ≤ requested) :
    Valid (reserve requested allowed buffers).1 := by
  obtain ⟨length, names, ids⟩ := valid
  by_cases room : buffers.entries.length < buffers.common <;>
    cases allowed <;> rename_i allowNames allowIds <;> cases allowNames <;> cases allowIds <;>
      simp [reserve, room, Valid] <;> omega

theorem ready_authorizes_both_array_writes (requested : Nat) (allowed : Allocations) (buffers : Buffers Name)
    (valid : Valid buffers) (growth : buffers.common < requested)
    (ready : (reserve requested allowed buffers).2 = true) :
    (reserve requested allowed buffers).1.entries.length < (reserve requested allowed buffers).1.namesAllocated ∧
      (reserve requested allowed buffers).1.entries.length < (reserve requested allowed buffers).1.idsAllocated := by
  obtain ⟨length, names, ids⟩ := valid
  by_cases room : buffers.entries.length < buffers.common <;>
    cases allowed <;> rename_i allowNames allowIds <;> cases allowNames <;> cases allowIds <;>
      simp [reserve, room] at ready ⊢ <;> omega

theorem second_refusal_and_retry (requested : Nat) (buffers : Buffers Name)
    (full : buffers.entries.length = buffers.common) :
    reserve requested ⟨true, false⟩ buffers = ({buffers with namesAllocated := requested}, false) ∧
      reserve requested ⟨true, true⟩ (reserve requested ⟨true, false⟩ buffers).1 =
        ({buffers with namesAllocated := requested, idsAllocated := requested, common := requested}, true) := by
  simp [reserve, full]

variable [DecidableEq Name]

def lookup (buffers : Buffers Name) (name : Name) : Option Nat :=
  (VariableInventory.scan buffers.entries name).map Prod.snd

theorem reservation_preserves_existing_ids (requested : Nat) (allowed : Allocations)
    (buffers : Buffers Name) (name : Name) :
    lookup (reserve requested allowed buffers).1 name = lookup buffers name := by
  simp only [lookup, (reserve_preserves_scope requested allowed buffers).1]

def intern (requested : Nat) (allowed : Allocations) (canMint : Bool) (buffers : Buffers Name) (name : Name) :
    Buffers Name × Except Fault Nat :=
  match VariableInventory.scan buffers.entries name with
  | some entry => (buffers, .ok entry.2)
  | none =>
      let grown := reserve requested allowed buffers
      if grown.2 && canMint then
        ({grown.1 with entries := buffers.entries ++ [(name, buffers.nextId)], nextId := buffers.nextId + 1}, .ok buffers.nextId)
      else (grown.1, .error .resource)

theorem cached_spelling_never_mints_or_reserves (requested : Nat) (allowed : Allocations) (canMint : Bool)
    (buffers : Buffers Name) (name : Name) (entry : VariableInventory.Entry Name Nat)
    (found : VariableInventory.scan buffers.entries name = some entry) :
    intern requested allowed canMint buffers name = (buffers, .ok entry.2) := by
  simp [intern, found]

theorem fresh_append_is_functional_update (entries : List (VariableInventory.Entry Name Nat))
    (name query : Name) (id : Nat) (absent : VariableInventory.scan entries name = none) :
    (VariableInventory.scan (entries ++ [(name, id)]) query).map Prod.snd =
      if query = name then some id else (VariableInventory.scan entries query).map Prod.snd := by
  unfold VariableInventory.scan at absent ⊢
  rw [List.find?_append]
  by_cases same : query = name
  · subst query
    simp [absent]
  · cases prior : entries.find? (fun entry => decide (entry.1 = query)) <;>
      simp [same, Ne.symm same]

theorem successful_insert_updates_logical_lookup (requested : Nat) (allowed : Allocations)
    (buffers : Buffers Name) (name query : Name)
    (absent : VariableInventory.scan buffers.entries name = none)
    (ready : (reserve requested allowed buffers).2 = true) :
    lookup (intern requested allowed true buffers name).1 query =
      if query = name then some buffers.nextId else lookup buffers query := by
  simp only [intern, absent, ready, Bool.and_self, if_true, lookup]
  exact fresh_append_is_functional_update buffers.entries name query buffers.nextId absent

theorem inserted_spelling_is_shared_without_another_mint (requested laterRequested : Nat)
    (allowed laterAllowed : Allocations) (buffers : Buffers Name) (name : Name)
    (absent : VariableInventory.scan buffers.entries name = none)
    (ready : (reserve requested allowed buffers).2 = true) :
    let first := intern requested allowed true buffers name
    intern laterRequested laterAllowed false first.1 name = (first.1, .ok buffers.nextId) := by
  have foundAgain : VariableInventory.scan (buffers.entries ++ [(name, buffers.nextId)]) name =
      some (name, buffers.nextId) := by
    unfold VariableInventory.scan at absent ⊢
    rw [List.find?_append, absent]
    simp
  simp [intern, absent, ready, foundAgain]

omit [DecidableEq Name] in
theorem new_identity_differs_from_every_prior_identity (buffers : Buffers Name)
    (bounded : ∀ entry ∈ buffers.entries, entry.2 < buffers.nextId)
    (entry : VariableInventory.Entry Name Nat) (present : entry ∈ buffers.entries) : buffers.nextId ≠ entry.2 := by
  have := bounded entry present
  omega

theorem intern_preserves_fresh_identity_bound (requested : Nat) (allowed : Allocations) (canMint : Bool)
    (buffers : Buffers Name) (name : Name)
    (bounded : ∀ entry ∈ buffers.entries, entry.2 < buffers.nextId) :
    ∀ entry ∈ (intern requested allowed canMint buffers name).1.entries,
      entry.2 < (intern requested allowed canMint buffers name).1.nextId := by
  cases found : VariableInventory.scan buffers.entries name with
  | some entry => simpa [intern, found] using bounded
  | none =>
      cases available : ((reserve requested allowed buffers).2 && canMint) with
      | true =>
          simp only [intern, found, available, if_true]
          intro entry member
          rcases List.mem_append.mp member with earlier | fresh
          · have := bounded entry earlier
            omega
          · have same := List.mem_singleton.mp fresh
            subst entry
            omega
      | false =>
          have unchanged := reserve_preserves_scope requested allowed buffers
          simpa only [intern, found, available, Bool.false_eq_true, if_false, unchanged.1, unchanged.2] using bounded

end Paired

namespace Controls

def read (world : List Nat) (input : Nat) : List Nat × Except Fault Nat :=
  (world ++ [input], if input = 13 then .error .resource
    else if input = 17 then .error .unsupported else .ok input)

def fallback (world : List Nat) (before : List Nat) : Published (List Nat) Nat :=
  (world ++ [777], before ++ [88], .ok ())

/-- This mutant publishes each prefix row before the decoder can refuse. -/
def publishWhileDecoding : List Nat → List Nat → List Nat → Published (List Nat) Nat
  | [], world, before => (world, before, .ok ())
  | input :: rest, world, before =>
      let next := read world input
      match next.2 with
      | .error fault => (next.1, before, .error fault)
      | .ok row => publishWhileDecoding rest next.1 (before ++ [row])

def fallbackOnEveryError (inputs : List Nat) : Published (List Nat) Nat :=
  let prepared := Native.stage read inputs [] []
  match prepared.2 with
  | .ok rows => (prepared.1, rows, .ok ())
  | .error _ => fallback prepared.1 []

theorem late_resource_refusal_keeps_internal_progress_but_publishes_nothing :
    Native.load read (fun _ => true) [1, 13, 2] [] [99] fallback =
      ([1, 13], [99], .error .resource) := by decide

theorem premature_publication_changes_the_visible_prefix :
    publishWhileDecoding [1, 13, 2] [] [99] = ([1, 13], [99, 1], .error .resource) ∧
      publishWhileDecoding [1, 13, 2] [] [99] ≠
        Native.load read (fun _ => true) [1, 13, 2] [] [99] fallback := by decide

theorem resource_fallback_changes_both_world_and_publication :
    fallbackOnEveryError [1, 13, 2] = ([1, 13, 777], [88], .ok ()) ∧
      fallbackOnEveryError [1, 13, 2] ≠ Native.load read (fun _ => true) [1, 13, 2] [] [] fallback := by decide

theorem nonresource_fallback_is_still_distinctly_allowed :
    Native.load read (fun _ => true) [1, 17, 2] [] [99] fallback =
      ([1, 17, 777], [99, 88], .ok ()) := by decide

theorem successful_rows_keep_order_duplicates_and_selection :
    Native.load read (fun row => row != 0) [1, 0, 1, 2] [] [99] fallback =
      ([1, 0, 1, 2], [99, 1, 1, 2], .ok ()) := by decide

def emptyScope (next : Nat) : Paired.Buffers Nat := ⟨[], next, 0, 0, 0⟩
def fullScope : Paired.Buffers Nat := ⟨[(10, 5), (20, 6)], 7, 2, 2, 2⟩

theorem failed_second_array_keeps_common_bound_and_owned_first_growth :
    let failed := Paired.reserve 4 ⟨true, false⟩ fullScope
    failed.2 = false ∧ failed.1.namesAllocated = 4 ∧ failed.1.idsAllocated = 2 ∧
      failed.1.common = 2 ∧ Paired.lookup failed.1 10 = some 5 ∧ Paired.lookup failed.1 20 = some 6 ∧
        Paired.Valid failed.1 := by
  unfold Paired.Valid
  decide

theorem retry_after_second_array_refusal_restores_safe_write_room :
    let failed := Paired.reserve 16 ⟨true, false⟩ (emptyScope 5)
    let retried := Paired.reserve 16 ⟨true, true⟩ failed.1
    retried.2 = true ∧ retried.1.common = 16 ∧ retried.1.idsAllocated = 16 ∧
      retried.1.entries = [] ∧ retried.1.nextId = 5 ∧ Paired.Valid retried.1 := by
  unfold Paired.Valid
  decide

/-- This mutant publishes the first array's extent as the shared bound. -/
def publishFirstCapacity (buffers : Paired.Buffers Nat) : Paired.Buffers Nat :=
  {buffers with common := buffers.namesAllocated}

theorem premature_capacity_skips_the_missing_second_allocation :
    let failed := Paired.reserve 16 ⟨true, false⟩ (emptyScope 5)
    let invalid := publishFirstCapacity failed.1
    let retried := Paired.reserve 16 ⟨true, true⟩ invalid
    ¬Paired.Valid invalid ∧ retried.2 = true ∧
      ¬retried.1.entries.length < retried.1.idsAllocated := by
  unfold Paired.Valid
  decide

/-- Missing the lookup mints a new identity for a repeated spelling. -/
def mintEveryOccurrence (buffers : Paired.Buffers Nat) (name : Nat) : Paired.Buffers Nat × Nat :=
  ({buffers with entries := buffers.entries ++ [(name, buffers.nextId)], nextId := buffers.nextId + 1}, buffers.nextId)

theorem repeated_spelling_is_shared_and_duplicate_minting_is_detected :
    let first := Paired.intern 16 ⟨true, true⟩ true (emptyScope 5) 10
    let again := Paired.intern 16 ⟨false, false⟩ false first.1 10
    first.2 = .ok 5 ∧ again.2 = .ok 5 ∧ again.1.nextId = 6 ∧
      (mintEveryOccurrence first.1 10).2 = 6 := by decide

theorem distinct_spellings_and_top_level_scopes_keep_distinct_identities :
    let first := Paired.intern 16 ⟨true, true⟩ true (emptyScope 5) 10
    let other := Paired.intern 16 ⟨true, true⟩ true first.1 20
    let nextScope := Paired.intern 16 ⟨true, true⟩ true (emptyScope other.1.nextId) 10
    first.2 = .ok 5 ∧ other.2 = .ok 6 ∧ nextScope.2 = .ok 7 ∧
      other.1.entries = [(10, 5), (20, 6)] ∧ nextScope.1.entries = [(10, 7)] := by decide

end Controls

end Mettapedia.Machines.DecoderPreparation
