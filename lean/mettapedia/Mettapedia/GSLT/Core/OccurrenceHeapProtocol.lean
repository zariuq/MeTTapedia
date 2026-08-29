import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Occurrence-preserving heap protocol

A compact proof machine needs two operations that must not be conflated with
value equality: reading one indexed occurrence and saving that very occurrence
at a fresh heap position.  This module presents those operations as a small
GSLT, independently of any proof language, byte encoding, or runtime syntax.

The protocol is owner-scoped, has explicit missing-index and wrong-owner
faults, and exposes the intermediate holding state.  That state is the seam
through which a caller may request a save after a successful lookup.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OccurrenceHeapProtocol

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational

variable {Owner Identity Value Other : Type}
variable {Owner' Identity' Value' Other' : Type}
variable {Owner'' Identity'' Value'' Other'' : Type}

/-- A value together with the identity of the occurrence that produced it. -/
structure Occurrence (Identity Value : Type) where
  identity : Identity
  value : Value
deriving DecidableEq

namespace Occurrence

def map (mapIdentity : Identity → Identity') (mapValue : Value → Value')
    (occurrence : Occurrence Identity Value) : Occurrence Identity' Value' :=
  ⟨mapIdentity occurrence.identity, mapValue occurrence.value⟩

@[simp] theorem map_identity (mapIdentity : Identity → Identity')
    (mapValue : Value → Value') (occurrence : Occurrence Identity Value) :
    (occurrence.map mapIdentity mapValue).identity =
      mapIdentity occurrence.identity := by
  rfl

@[simp] theorem map_value (mapIdentity : Identity → Identity')
    (mapValue : Value → Value') (occurrence : Occurrence Identity Value) :
    (occurrence.map mapIdentity mapValue).value = mapValue occurrence.value := by
  rfl

end Occurrence

/-- A heterogeneous heap position.  Proof occurrences and guest-specific
opaque entries share one index space, as they do in compressed Metamath. -/
inductive Entry (Identity Value Other : Type) where
  | occurrence (value : Occurrence Identity Value)
  | opaque (value : Other)
deriving DecidableEq

namespace Entry

def map (mapIdentity : Identity → Identity') (mapValue : Value → Value')
    (mapOther : Other → Other') :
    Entry Identity Value Other → Entry Identity' Value' Other'
  | @Entry.occurrence _ _ _ item =>
      Entry.occurrence (Other := Other')
        (item.map mapIdentity mapValue)
  | @Entry.opaque _ _ _ value => Entry.opaque (Identity := Identity')
      (Value := Value') (mapOther value)

@[simp] theorem map_comp
    (firstIdentity : Identity → Identity')
    (secondIdentity : Identity' → Identity'')
    (firstValue : Value → Value') (secondValue : Value' → Value'')
    (firstOther : Other → Other') (secondOther : Other' → Other'')
    (entry : Entry Identity Value Other) :
    Entry.map secondIdentity secondValue secondOther
        (Entry.map firstIdentity firstValue firstOther entry) =
      Entry.map (secondIdentity ∘ firstIdentity)
        (secondValue ∘ firstValue) (secondOther ∘ firstOther) entry := by
  cases entry <;> rfl

end Entry

/-- Explicit failure observations of the abstract protocol. -/
inductive Fault (Owner : Type) where
  | wrongOwner (requested resident : Owner)
  | missingIndex (owner : Owner) (index : Nat)
  | wrongEntryKind (owner : Owner) (index : Nat)
deriving DecidableEq

/-- Control states of lookup followed, optionally, by a fresh save. -/
inductive Control (Owner Identity Value : Type) where
  | lookup (owner : Owner) (index : Nat)
  | holding (owner : Owner) (index : Nat)
      (occurrence : Occurrence Identity Value)
  | save (owner : Owner) (occurrence : Occurrence Identity Value)
  | saved (owner : Owner) (index : Nat)
      (occurrence : Occurrence Identity Value)
  | fault (failure : Fault Owner)
deriving DecidableEq

/-- One owner-scoped heterogeneous heap and its current protocol control.  The
list index is the heap position, so opaque entries retain their place and two
equal proof values remain different when their occurrence identities differ. -/
structure State (Owner Identity Value Other : Type) where
  owner : Owner
  heap : List (Entry Identity Value Other)
  control : Control Owner Identity Value
deriving DecidableEq

/-- Exact heap protocol.  A missing or cross-owner request produces an
explicit fault rather than becoming a silent normal form. -/
inductive Step :
    State Owner Identity Value Other →
      State Owner Identity Value Other → Prop where
  | lookupHit (owner : Owner) (heap : List (Entry Identity Value Other))
      (index : Nat) (occurrence : Occurrence Identity Value)
      (found : heap[index]? = some (.occurrence occurrence)) :
      Step ⟨owner, heap, .lookup owner index⟩
        ⟨owner, heap, .holding owner index occurrence⟩
  | lookupMissing (owner : Owner) (heap : List (Entry Identity Value Other))
      (index : Nat) (missing : heap[index]? = none) :
      Step ⟨owner, heap, .lookup owner index⟩
        ⟨owner, heap, .fault (.missingIndex owner index)⟩
  | lookupOpaque (owner : Owner) (heap : List (Entry Identity Value Other))
      (index : Nat) (value : Other)
      (found : heap[index]? = some (.opaque value)) :
      Step ⟨owner, heap, .lookup owner index⟩
        ⟨owner, heap, .fault (.wrongEntryKind owner index)⟩
  | lookupWrongOwner (resident requested : Owner)
      (heap : List (Entry Identity Value Other)) (index : Nat)
      (different : requested ≠ resident) :
      Step ⟨resident, heap, .lookup requested index⟩
        ⟨resident, heap, .fault (.wrongOwner requested resident)⟩
  | beginSave (owner : Owner) (heap : List (Entry Identity Value Other))
      (index : Nat) (occurrence : Occurrence Identity Value) :
      Step ⟨owner, heap, .holding owner index occurrence⟩
        ⟨owner, heap, .save owner occurrence⟩
  | save (owner : Owner) (heap : List (Entry Identity Value Other))
      (occurrence : Occurrence Identity Value) :
      Step ⟨owner, heap, .save owner occurrence⟩
        ⟨owner, heap ++ [.occurrence occurrence],
          .saved owner heap.length occurrence⟩
  | saveWrongOwner (resident requested : Owner)
      (heap : List (Entry Identity Value Other))
      (occurrence : Occurrence Identity Value)
      (different : requested ≠ resident) :
      Step ⟨resident, heap, .save requested occurrence⟩
        ⟨resident, heap, .fault (.wrongOwner requested resident)⟩

/-- Native GSLT of the owner-scoped occurrence heap. -/
def gslt (Owner Identity Value Other : Type) : GSLT where
  Term := State Owner Identity Value Other
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- A successful lookup returns the exact stored occurrence, not merely an
equal underlying value. -/
theorem lookupHit_exact (owner : Owner)
    (heap : List (Entry Identity Value Other)) (index : Nat)
    (occurrence : Occurrence Identity Value)
    (found : heap[index]? = some (.occurrence occurrence)) :
    Step ⟨owner, heap, .lookup owner index⟩
      ⟨owner, heap, .holding owner index occurrence⟩ :=
  Step.lookupHit owner heap index occurrence found

/-- Lookup, handoff, and save compose into one proof-relevant path. -/
def lookupThenSavePath (owner : Owner)
    (heap : List (Entry Identity Value Other)) (index : Nat)
    (occurrence : Occurrence Identity Value)
    (found : heap[index]? = some (.occurrence occurrence)) :
    (gslt Owner Identity Value Other).RewritePath
      ⟨owner, heap, .lookup owner index⟩
      ⟨owner, heap ++ [.occurrence occurrence],
        .saved owner heap.length occurrence⟩ :=
  .cons (Step.lookupHit owner heap index occurrence found)
    (.cons (Step.beginSave owner heap index occurrence)
      (.cons (Step.save owner heap occurrence)
        (.nil _)))

@[simp] theorem lookupThenSavePath_length (owner : Owner)
    (heap : List (Entry Identity Value Other)) (index : Nat)
    (occurrence : Occurrence Identity Value)
    (found : heap[index]? = some (.occurrence occurrence)) :
    (lookupThenSavePath owner heap index occurrence found).length = 3 := by
  rfl

/-- A wrong-owner lookup cannot be mistaken for a hit. -/
theorem wrongOwner_lookup_cannot_hit (resident requested : Owner)
    (heap : List (Entry Identity Value Other)) (index : Nat)
    (different : requested ≠ resident) :
    ¬ ∃ occurrence, Step
      ⟨resident, heap, .lookup requested index⟩
      ⟨resident, heap, .holding requested index occurrence⟩ := by
  rintro ⟨occurrence, step⟩
  cases step
  exact different rfl

/-- An out-of-range lookup takes the explicit missing-index branch and cannot
produce an occurrence. -/
theorem missing_lookup_cannot_hit (owner : Owner)
    (heap : List (Entry Identity Value Other)) (index : Nat)
    (missing : heap[index]? = none) :
    ¬ ∃ occurrence, Step
      ⟨owner, heap, .lookup owner index⟩
      ⟨owner, heap, .holding owner index occurrence⟩ := by
  rintro ⟨occurrence, step⟩
  cases step
  simp_all

/-- An opaque entry occupies its index but cannot masquerade as a proof
occurrence. -/
theorem opaque_lookup_cannot_hit (owner : Owner)
    (heap : List (Entry Identity Value Other)) (index : Nat) (value : Other)
    (found : heap[index]? = some (.opaque value)) :
    ¬ ∃ occurrence, Step
      ⟨owner, heap, .lookup owner index⟩
      ⟨owner, heap, .holding owner index occurrence⟩ := by
  rintro ⟨occurrence, step⟩
  cases step
  simp_all

/-- Equal values at different occurrence identities remain distinguishable by
heap lookup and by the subsequent saved occurrence. -/
theorem equal_values_keep_distinct_occurrences :
    let first : Occurrence Nat Nat := ⟨0, 7⟩
    let second : Occurrence Nat Nat := ⟨1, 7⟩
    let heap : List (Entry Nat Nat Unit) :=
      [.occurrence first, .occurrence second]
    (heap[0]? = some (.occurrence first)) ∧
      (heap[1]? = some (.occurrence second)) ∧ first ≠ second := by
  decide

/-! ## Functorial renaming

The protocol depends only on owner equality and occurrence structure.  An
injective owner renaming and arbitrary maps of identity and value transport
every step, yielding a reusable GSLT-to-GSLT translation.
-/

def Fault.map (mapOwner : Owner → Owner') : Fault Owner → Fault Owner'
  | .wrongOwner requested resident =>
      .wrongOwner (mapOwner requested) (mapOwner resident)
  | .missingIndex owner index => .missingIndex (mapOwner owner) index
  | .wrongEntryKind owner index => .wrongEntryKind (mapOwner owner) index

@[simp] theorem Fault.map_comp (first : Owner → Owner')
    (second : Owner' → Owner'') (failure : Fault Owner) :
    (failure.map first).map second = failure.map (second ∘ first) := by
  cases failure <;> rfl

def Control.map (mapOwner : Owner → Owner')
    (mapIdentity : Identity → Identity') (mapValue : Value → Value') :
    Control Owner Identity Value → Control Owner' Identity' Value'
  | .lookup owner index => .lookup (mapOwner owner) index
  | .holding owner index occurrence =>
      .holding (mapOwner owner) index (occurrence.map mapIdentity mapValue)
  | .save owner occurrence =>
      .save (mapOwner owner) (occurrence.map mapIdentity mapValue)
  | .saved owner index occurrence =>
      .saved (mapOwner owner) index (occurrence.map mapIdentity mapValue)
  | .fault failure => .fault (failure.map mapOwner)

@[simp] theorem Control.map_comp
    (firstOwner : Owner → Owner') (secondOwner : Owner' → Owner'')
    (firstIdentity : Identity → Identity')
    (secondIdentity : Identity' → Identity'')
    (firstValue : Value → Value') (secondValue : Value' → Value'')
    (control : Control Owner Identity Value) :
    (control.map firstOwner firstIdentity firstValue).map
        secondOwner secondIdentity secondValue =
      control.map (secondOwner ∘ firstOwner)
        (secondIdentity ∘ firstIdentity) (secondValue ∘ firstValue) := by
  cases control <;> simp [Control.map, Occurrence.map, Function.comp_def]

def State.map (mapOwner : Owner → Owner')
    (mapIdentity : Identity → Identity') (mapValue : Value → Value')
    (mapOther : Other → Other') (state : State Owner Identity Value Other) :
    State Owner' Identity' Value' Other' :=
  { owner := mapOwner state.owner
    heap := state.heap.map (Entry.map mapIdentity mapValue mapOther)
    control := state.control.map mapOwner mapIdentity mapValue }

@[simp] theorem State.map_comp
    (firstOwner : Owner → Owner') (secondOwner : Owner' → Owner'')
    (firstIdentity : Identity → Identity')
    (secondIdentity : Identity' → Identity'')
    (firstValue : Value → Value') (secondValue : Value' → Value'')
    (firstOther : Other → Other') (secondOther : Other' → Other'')
    (state : State Owner Identity Value Other) :
    (state.map firstOwner firstIdentity firstValue firstOther).map
        secondOwner secondIdentity secondValue secondOther =
      state.map (secondOwner ∘ firstOwner)
        (secondIdentity ∘ firstIdentity) (secondValue ∘ firstValue)
        (secondOther ∘ firstOther) := by
  cases state
  simp [State.map, List.map_map, Function.comp_def]

/-- Renaming transports every protocol step.  Owner injectivity is exactly
the structure needed to retain wrong-owner faults. -/
theorem map_step (mapOwner : Owner → Owner')
    (mapIdentity : Identity → Identity') (mapValue : Value → Value')
    (mapOther : Other → Other')
    (ownerInjective : Function.Injective mapOwner)
    {source target : State Owner Identity Value Other}
    (step : Step source target) :
    Step (source.map mapOwner mapIdentity mapValue mapOther)
      (target.map mapOwner mapIdentity mapValue mapOther) := by
  cases step with
  | lookupHit owner heap index occurrence found =>
      apply Step.lookupHit
      simpa [State.map, Control.map, Entry.map, Occurrence.map,
        List.getElem?_map] using
        congrArg (Option.map (Entry.map mapIdentity mapValue mapOther)) found
  | lookupMissing owner heap index missing =>
      apply Step.lookupMissing
      simpa [State.map, Control.map, List.getElem?_map] using
        congrArg (Option.map (Entry.map mapIdentity mapValue mapOther)) missing
  | lookupOpaque owner heap index value found =>
      apply Step.lookupOpaque
      simpa [State.map, Control.map, Entry.map, List.getElem?_map] using
        congrArg (Option.map (Entry.map mapIdentity mapValue mapOther)) found
  | lookupWrongOwner resident requested heap index different =>
      exact Step.lookupWrongOwner _ _ _ _ (ownerInjective.ne different)
  | beginSave owner heap index occurrence =>
      exact Step.beginSave _ _ _ _
  | save owner heap occurrence =>
      simpa [State.map, Control.map, Entry.map, Occurrence.map,
        List.map_append] using
        (Step.save (mapOwner owner)
          (heap.map (Entry.map mapIdentity mapValue mapOther))
          (occurrence.map mapIdentity mapValue))
  | saveWrongOwner resident requested heap occurrence different =>
      exact Step.saveWrongOwner _ _ _ _ (ownerInjective.ne different)

/-- Reusable operational GSLT transformation induced by representation maps. -/
def mapTranslation (mapOwner : Owner → Owner')
    (mapIdentity : Identity → Identity') (mapValue : Value → Value')
    (mapOther : Other → Other')
    (ownerInjective : Function.Injective mapOwner) :
    OperationalTranslation (gslt Owner Identity Value Other)
      (gslt Owner' Identity' Value' Other') where
  mapTerm := State.map mapOwner mapIdentity mapValue mapOther
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := map_step mapOwner mapIdentity mapValue mapOther ownerInjective

/-- Proof-relevant paths transport through the same representation map. -/
def mapPath (mapOwner : Owner → Owner')
    (mapIdentity : Identity → Identity') (mapValue : Value → Value')
    (mapOther : Other → Other')
    (ownerInjective : Function.Injective mapOwner)
    {source target : State Owner Identity Value Other} :
    (gslt Owner Identity Value Other).RewritePath source target →
      (gslt Owner' Identity' Value' Other').RewritePath
        (source.map mapOwner mapIdentity mapValue mapOther)
        (target.map mapOwner mapIdentity mapValue mapOther)
  | .nil state =>
      @GSLT.RewritePath.nil (gslt Owner' Identity' Value' Other')
        (state.map mapOwner mapIdentity mapValue mapOther)
  | .cons step remaining =>
      .cons
        (map_step mapOwner mapIdentity mapValue mapOther ownerInjective step)
        (mapPath mapOwner mapIdentity mapValue mapOther ownerInjective remaining)

@[simp] theorem mapPath_length (mapOwner : Owner → Owner')
    (mapIdentity : Identity → Identity') (mapValue : Value → Value')
    (mapOther : Other → Other')
    (ownerInjective : Function.Injective mapOwner)
    {source target : State Owner Identity Value Other} :
    (path : (gslt Owner Identity Value Other).RewritePath source target) →
      (mapPath mapOwner mapIdentity mapValue mapOther ownerInjective path).length =
        path.length
  | .nil _ => rfl
  | .cons _ remaining => by
      simp only [mapPath, GSLT.RewritePath.length]
      rw [mapPath_length mapOwner mapIdentity mapValue mapOther
        ownerInjective remaining]

/-- Representation changes compose as ordinary GSLT transformations.  This
is the reusable stage law: introducing an intermediate representation neither
changes the guest heap protocol nor authorizes a parallel semantics. -/
theorem mapTranslation_comp
    (firstOwner : Owner → Owner') (secondOwner : Owner' → Owner'')
    (firstIdentity : Identity → Identity')
    (secondIdentity : Identity' → Identity'')
    (firstValue : Value → Value') (secondValue : Value' → Value'')
    (firstOther : Other → Other') (secondOther : Other' → Other'')
    (firstOwnerInjective : Function.Injective firstOwner)
    (secondOwnerInjective : Function.Injective secondOwner) :
    (mapTranslation firstOwner firstIdentity firstValue firstOther
      firstOwnerInjective).comp
        (mapTranslation secondOwner secondIdentity secondValue secondOther
          secondOwnerInjective) =
      mapTranslation (secondOwner ∘ firstOwner)
        (secondIdentity ∘ firstIdentity) (secondValue ∘ firstValue)
        (secondOther ∘ firstOther)
        (secondOwnerInjective.comp firstOwnerInjective) := by
  apply OperationalTranslation.ext
  funext state
  exact State.map_comp firstOwner secondOwner firstIdentity secondIdentity
    firstValue secondValue firstOther secondOther state

#print axioms lookupHit_exact
#print axioms lookupThenSavePath_length
#print axioms wrongOwner_lookup_cannot_hit
#print axioms missing_lookup_cannot_hit
#print axioms opaque_lookup_cannot_hit
#print axioms equal_values_keep_distinct_occurrences
#print axioms map_step
#print axioms mapTranslation
#print axioms mapPath
#print axioms mapPath_length
#print axioms mapTranslation_comp

end Mettapedia.GSLT.OccurrenceHeapProtocol
