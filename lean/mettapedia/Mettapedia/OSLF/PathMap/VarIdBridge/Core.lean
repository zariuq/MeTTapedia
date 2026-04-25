import Mettapedia.OSLF.PathMap.CanonicalUniverse
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.PathMapMatcherInstance
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mathlib.Data.List.Perm.Basic

/-!
# VarId Bridge Interface

This module states the variable-identity contract for a PathMap/MM2-style
structural store without introducing a separate public index.

The current bridge shape is modeled as:

* an exact CeTTa-side term with `VarId`s;
* a structural store term with local slots;
* an interface map from `VarId` to slot and a left inverse from slot to `VarId`;
* an optional presentation witness carried with variable-bearing rows when exact
  identity must be recovered after structural storage.

The future locally nameless shape is connected to the existing MeTTaIL open/close
theorems: bound variables are de Bruijn indices, while free/meta variables remain
named at the interface.
-/

namespace Mettapedia.OSLF.PathMap.VarIdBridge

open Mettapedia.OSLF.PathMap.CanonicalUniverse
open Mettapedia.OSLF.PathMap.Trie

abbrev Slot := Nat
abbrev Spelling := String

/-! ## Current bridge surface: exact terms and structural slot terms -/

/-- A small exact term language carrying CeTTa `VarId`s. -/
inductive ExactTerm where
  | symbol : String → ExactTerm
  | var : VarId → ExactTerm
  | grounded : GroundedKind → ExactTerm
  | app : ExactTerm → ExactTerm → ExactTerm
  deriving DecidableEq, Repr

/-- The same shape after lowering variables to local structural slots. -/
inductive SlotTerm where
  | symbol : String → SlotTerm
  | slot : Slot → SlotTerm
  | grounded : GroundedKind → SlotTerm
  | app : SlotTerm → SlotTerm → SlotTerm
  deriving DecidableEq, Repr

/-- Lower exact variables to structural slots. -/
def encodeWith (slotOf : VarId → Slot) : ExactTerm → SlotTerm
  | .symbol s => .symbol s
  | .var v => .slot (slotOf v)
  | .grounded g => .grounded g
  | .app f x => .app (encodeWith slotOf f) (encodeWith slotOf x)

/-- Raise structural slots back to exact variables. -/
def decodeWith (varOf : Slot → VarId) : SlotTerm → ExactTerm
  | .symbol s => .symbol s
  | .slot n => .var (varOf n)
  | .grounded g => .grounded g
  | .app f x => .app (decodeWith varOf f) (decodeWith varOf x)

/-- A slot interface is faithful when decoding is a left inverse of encoding. -/
structure SlotInterface where
  slotOf : VarId → Slot
  varOf : Slot → VarId
  recovers : ∀ v, varOf (slotOf v) = v

/-- Exact-to-slot-to-exact round trip. -/
@[simp]
theorem decode_encode_id (ι : SlotInterface) :
    ∀ t, decodeWith ι.varOf (encodeWith ι.slotOf t) = t
  | .symbol _ => rfl
  | .var v => by simp [encodeWith, decodeWith, ι.recovers v]
  | .grounded _ => rfl
  | .app f x => by
      simp [encodeWith, decodeWith, decode_encode_id ι f, decode_encode_id ι x]

/-- Structural equality under a faithful interface implies exact equality. -/
theorem encode_injective (ι : SlotInterface) :
    Function.Injective (encodeWith ι.slotOf) := by
  intro a b h
  have h' := congrArg (decodeWith ι.varOf) h
  simpa using h'

/-- Co-reference is preserved and reflected by the slot interface. -/
theorem slot_eq_iff_var_eq (ι : SlotInterface) (v₁ v₂ : VarId) :
    ι.slotOf v₁ = ι.slotOf v₂ ↔ v₁ = v₂ := by
  constructor
  · intro h
    have h' := congrArg ι.varOf h
    simpa [ι.recovers v₁, ι.recovers v₂] using h'
  · intro h
    simp [h]

/-- Distinct variables occupy distinct slots in a faithful interface. -/
theorem slot_ne_of_var_ne (ι : SlotInterface) {v₁ v₂ : VarId}
    (h : v₁ ≠ v₂) :
    ι.slotOf v₁ ≠ ι.slotOf v₂ :=
  fun hs => h ((slot_eq_iff_var_eq ι v₁ v₂).mp hs)

def structuralEq (slotOf : VarId → Slot) (a b : ExactTerm) : Prop :=
  encodeWith slotOf a = encodeWith slotOf b

def exactEq (a b : ExactTerm) : Prop := a = b

/-- Exact equality always implies structural equality. -/
theorem exact_implies_structural (slotOf : VarId → Slot) {a b : ExactTerm}
    (h : exactEq a b) :
    structuralEq slotOf a b := by
  simpa [exactEq, structuralEq] using congrArg (encodeWith slotOf) h

/-- Under a faithful interface, structural equality is not weaker than exact equality. -/
theorem structural_implies_exact (ι : SlotInterface) {a b : ExactTerm}
    (h : structuralEq ι.slotOf a b) :
    exactEq a b := by
  exact encode_injective ι h

/-! ## Negative example: structural slots alone can collapse identity -/

def exampleVarA : VarId := { base := 1, epoch := 7 }
def exampleVarB : VarId := { base := 2, epoch := 7 }

/-- The two running example variables are genuinely distinct. -/
theorem exampleVarA_ne_exampleVarB : exampleVarA ≠ exampleVarB := by
  intro h
  have hb := congrArg VarId.base h
  simp [exampleVarA, exampleVarB] at hb

/-- Positive example: any faithful interface separates the distinct example variables. -/
theorem faithful_interface_distinguishes_example_vars (ι : SlotInterface) :
    ι.slotOf exampleVarA ≠ ι.slotOf exampleVarB :=
  slot_ne_of_var_ne ι exampleVarA_ne_exampleVarB

def collapsedSlot (_ : VarId) : Slot := 0

/-- A non-injective slot assignment identifies distinct variables structurally. -/
theorem collapsed_slots_identify_distinct_vars :
    structuralEq collapsedSlot (.var exampleVarA) (.var exampleVarB) := rfl

/-- The structurally collapsed variables are still not exact-equal. -/
theorem collapsed_slots_not_exact :
    ¬ exactEq (.var exampleVarA) (.var exampleVarB) := by
  intro h
  have hb := congrArg
    (fun t =>
      match t with
      | ExactTerm.var v => v.base
      | _ => 0) h
  simp [exampleVarA, exampleVarB] at hb

/-! ## Presentation witnesses for variable-bearing rows -/

/-- Exact presentation data for one local slot. -/
structure VarPresentation where
  slot : Slot
  var : VarId
  spelling : Spelling
  deriving DecidableEq, Repr

/-- The per-row identity payload needed to recover exact `VarId`s after structural storage. -/
structure IdentityPayload where
  entries : List VarPresentation
  deriving DecidableEq, Repr

/-- The key that preserves exact identity for variable-bearing rows. -/
def presentationKey (slotOf : VarId → Slot) (t : ExactTerm) (payload : IdentityPayload) :
    SlotTerm × IdentityPayload :=
  (encodeWith slotOf t, payload)

/-- Different payloads are different exact presentation keys, even with the same structural term. -/
theorem presentation_key_ne_of_payload_ne (slotOf : VarId → Slot) (t : ExactTerm)
    {p₁ p₂ : IdentityPayload} (h : p₁ ≠ p₂) :
    presentationKey slotOf t p₁ ≠ presentationKey slotOf t p₂ := by
  intro hkey
  exact h (congrArg Prod.snd hkey)

def payloadA : IdentityPayload :=
  { entries := [{ slot := 0, var := exampleVarA, spelling := "x" }] }

def payloadB : IdentityPayload :=
  { entries := [{ slot := 0, var := exampleVarB, spelling := "x" }] }

/-- The payload prevents collapsed structural slots from becoming collapsed exact rows. -/
theorem collapsed_presentation_keys_distinct :
    presentationKey collapsedSlot (.var exampleVarA) payloadA ≠
    presentationKey collapsedSlot (.var exampleVarB) payloadB := by
  intro h
  have hp := congrArg Prod.snd h
  simp [presentationKey, payloadA, payloadB, exampleVarA, exampleVarB] at hp

/-! ## List-shaped `CAtom` bridge surface -/

/-- A structural atom with local slots and list-shaped expressions. -/
inductive SlotAtom where
  | symbol : String → SlotAtom
  | slot : Slot → SlotAtom
  | grounded : GroundedKind → SlotAtom
  | expression : List SlotAtom → SlotAtom

mutual
  /-- Lower a CeTTa-aware `CAtom` to a structural slot atom. -/
  def encodeCAtomWith (slotOf : VarId → Slot) : CAtom → SlotAtom
    | .symbol s => .symbol s
    | .var v => .slot (slotOf v)
    | .grounded g => .grounded g
    | .expression es => .expression (encodeCAtomListWith slotOf es)

  /-- Lower a list of CeTTa-aware atoms. -/
  def encodeCAtomListWith (slotOf : VarId → Slot) : List CAtom → List SlotAtom
    | [] => []
    | a :: as => encodeCAtomWith slotOf a :: encodeCAtomListWith slotOf as
end

mutual
  /-- Raise a structural slot atom back to a CeTTa-aware `CAtom`. -/
  def decodeSlotAtomWith (varOf : Slot → VarId) : SlotAtom → CAtom
    | .symbol s => .symbol s
    | .slot n => .var (varOf n)
    | .grounded g => .grounded g
    | .expression es => .expression (decodeSlotAtomListWith varOf es)

  /-- Raise a list of structural slot atoms. -/
  def decodeSlotAtomListWith (varOf : Slot → VarId) : List SlotAtom → List CAtom
    | [] => []
    | a :: as => decodeSlotAtomWith varOf a :: decodeSlotAtomListWith varOf as
end

mutual
  /-- Exact `CAtom` round-trip through a faithful slot interface. -/
  @[simp]
  theorem decode_encode_catom_id (ι : SlotInterface) :
      ∀ a, decodeSlotAtomWith ι.varOf (encodeCAtomWith ι.slotOf a) = a
    | .symbol _ => rfl
    | .var v => by simp [encodeCAtomWith, decodeSlotAtomWith, ι.recovers v]
    | .grounded _ => rfl
    | .expression es => by
        simp [encodeCAtomWith, decodeSlotAtomWith, decode_encode_catom_list_id ι es]

  /-- Exact list round-trip through a faithful slot interface. -/
  @[simp]
  theorem decode_encode_catom_list_id (ι : SlotInterface) :
      ∀ as, decodeSlotAtomListWith ι.varOf (encodeCAtomListWith ι.slotOf as) = as
    | [] => rfl
    | a :: as => by
        simp [encodeCAtomListWith, decodeSlotAtomListWith,
          decode_encode_catom_id ι a, decode_encode_catom_list_id ι as]
end

/-- Encoding `CAtom`s with a faithful interface is injective. -/
theorem encodeCAtom_injective (ι : SlotInterface) :
    Function.Injective (encodeCAtomWith ι.slotOf) := by
  intro a b h
  have h' := congrArg (decodeSlotAtomWith ι.varOf) h
  simpa using h'

def catomStructuralEq (slotOf : VarId → Slot) (a b : CAtom) : Prop :=
  encodeCAtomWith slotOf a = encodeCAtomWith slotOf b

/-- Under a faithful interface, structural equality of list-shaped atoms reflects exact equality. -/
theorem catom_structural_implies_exact (ι : SlotInterface) {a b : CAtom}
    (h : catomStructuralEq ι.slotOf a b) :
    a = b :=
  encodeCAtom_injective ι h

/-- Collapsed slots identify distinct `CAtom` variables structurally. -/
theorem collapsed_slots_identify_distinct_catoms :
    catomStructuralEq collapsedSlot (.var exampleVarA) (.var exampleVarB) := rfl

/-- The same collapsed variables are not exact-equal as `CAtom`s. -/
theorem collapsed_catoms_not_exact :
    (.var exampleVarA : CAtom) ≠ .var exampleVarB := by
  intro h
  have hb := congrArg
    (fun a =>
      match a with
      | CAtom.var v => v.base
      | _ => 0) h
  simp [exampleVarA, exampleVarB] at hb

/-! ## Abstract packet contract -/

/-- ABI-independent packet model: structural payload plus exact presentation payload. -/
structure BridgePacket where
  structural : SlotAtom
  identity : IdentityPayload

/-- Encode a list-shaped atom into the abstract packet contract. -/
def encodePacket (slotOf : VarId → Slot) (a : CAtom) (identity : IdentityPayload) :
    BridgePacket :=
  { structural := encodeCAtomWith slotOf a, identity := identity }

/-- Decode the structural part of an abstract packet. -/
def decodePacket (varOf : Slot → VarId) (packet : BridgePacket) : CAtom :=
  decodeSlotAtomWith varOf packet.structural

/-- Packet decode after encode recovers the original atom under a faithful interface. -/
@[simp]
theorem decode_encode_packet_atom (ι : SlotInterface) (a : CAtom) (identity : IdentityPayload) :
    decodePacket ι.varOf (encodePacket ι.slotOf a identity) = a := by
  simp [decodePacket, encodePacket]

/-- Distinct identity payloads give distinct packets for the same atom. -/
theorem packet_ne_of_identity_ne (slotOf : VarId → Slot) (a : CAtom)
    {p₁ p₂ : IdentityPayload} (h : p₁ ≠ p₂) :
    encodePacket slotOf a p₁ ≠ encodePacket slotOf a p₂ := by
  intro hp
  exact h (congrArg BridgePacket.identity hp)

def catomPayloadA : IdentityPayload :=
  { entries := [{ slot := 0, var := exampleVarA, spelling := "x" }] }

def catomPayloadB : IdentityPayload :=
  { entries := [{ slot := 0, var := exampleVarB, spelling := "x" }] }

/-- The packet contract distinguishes exact variable identity even when structural slots collapse. -/
theorem collapsed_catom_packets_distinct :
    encodePacket collapsedSlot (.var exampleVarA) catomPayloadA ≠
    encodePacket collapsedSlot (.var exampleVarB) catomPayloadB := by
  intro h
  have hp := congrArg BridgePacket.identity h
  simp [encodePacket, catomPayloadA, catomPayloadB, exampleVarA, exampleVarB] at hp

/-! ## Payload-based packet decoding and query preservation -/

/-- Lookup a slot in a payload entry list. -/
def varOfEntries? : List VarPresentation → Slot → Option VarId
  | [], _ => none
  | entry :: rest, n =>
      if entry.slot == n then some entry.var else varOfEntries? rest n

namespace IdentityPayload

/-- Lookup the exact `VarId` carried for a structural slot. -/
def varOf? (payload : IdentityPayload) (slot : Slot) : Option VarId :=
  varOfEntries? payload.entries slot

end IdentityPayload

mutual
  /-- Decode a structural slot atom using its packet-local identity payload. -/
  def decodeSlotAtomWithPayload? (payload : IdentityPayload) : SlotAtom → Option CAtom
    | .symbol s => some (.symbol s)
    | .slot n =>
        match payload.varOf? n with
        | some v => some (.var v)
        | none => none
    | .grounded g => some (.grounded g)
    | .expression es =>
        match decodeSlotAtomListWithPayload? payload es with
        | some as => some (.expression as)
        | none => none

  /-- Decode a list of structural slot atoms using a packet-local identity payload. -/
  def decodeSlotAtomListWithPayload? (payload : IdentityPayload) :
      List SlotAtom → Option (List CAtom)
    | [] => some []
    | a :: as =>
        match decodeSlotAtomWithPayload? payload a,
          decodeSlotAtomListWithPayload? payload as with
        | some a', some as' => some (a' :: as')
        | _, _ => none
end

mutual
  /-- Payload decoding recovers an encoded atom when the payload covers the slots used. -/
  @[simp]
  theorem decode_payload_encode_catom_id
      (slotOf : VarId → Slot) (payload : IdentityPayload)
      (hrec : ∀ v, payload.varOf? (slotOf v) = some v) :
      ∀ a, decodeSlotAtomWithPayload? payload (encodeCAtomWith slotOf a) = some a
    | .symbol _ => rfl
    | .var v => by simp [encodeCAtomWith, decodeSlotAtomWithPayload?, hrec v]
    | .grounded _ => rfl
    | .expression es => by
        simp [encodeCAtomWith, decodeSlotAtomWithPayload?,
          decode_payload_encode_catom_list_id slotOf payload hrec es]

  /-- Payload decoding recovers an encoded atom list when the payload covers the slots used. -/
  @[simp]
  theorem decode_payload_encode_catom_list_id
      (slotOf : VarId → Slot) (payload : IdentityPayload)
      (hrec : ∀ v, payload.varOf? (slotOf v) = some v) :
      ∀ as, decodeSlotAtomListWithPayload? payload (encodeCAtomListWith slotOf as) = some as
    | [] => rfl
    | a :: as => by
        simp [encodeCAtomListWith, decodeSlotAtomListWithPayload?,
          decode_payload_encode_catom_id slotOf payload hrec a,
          decode_payload_encode_catom_list_id slotOf payload hrec as]
end

/-- Decode a packet using its identity payload rather than a global slot decoder. -/
def decodePacketWithPayload? (packet : BridgePacket) : Option CAtom :=
  decodeSlotAtomWithPayload? packet.identity packet.structural

/-- Packet-local payload decoding after encoding recovers the original atom. -/
@[simp]
theorem decode_payload_encode_packet_atom
    (slotOf : VarId → Slot) (a : CAtom) (payload : IdentityPayload)
    (hrec : ∀ v, payload.varOf? (slotOf v) = some v) :
    decodePacketWithPayload? (encodePacket slotOf a payload) = some a := by
  simp [decodePacketWithPayload?, encodePacket, decode_payload_encode_catom_id slotOf payload hrec a]

/-- ABI-independent raw packet contract. The byte-level format supplies `Raw`; the law is round-trip. -/
structure PacketABI (Raw : Type*) where
  encodeRaw : BridgePacket → Raw
  decodeRaw? : Raw → Option BridgePacket
  roundTrip : ∀ packet, decodeRaw? (encodeRaw packet) = some packet

/-- Decode raw ABI bytes through the abstract packet contract. -/
def decodeRawPacketWithPayload? {Raw : Type*} (abi : PacketABI Raw) (raw : Raw) :
    Option CAtom :=
  match abi.decodeRaw? raw with
  | some packet => decodePacketWithPayload? packet
  | none => none

/-- Raw ABI encode/decode preserves atom decoding when the abstract packet payload is faithful. -/
theorem raw_packet_roundtrip_decodes_exact {Raw : Type*} (abi : PacketABI Raw)
    (slotOf : VarId → Slot) (a : CAtom) (payload : IdentityPayload)
    (hrec : ∀ v, payload.varOf? (slotOf v) = some v) :
    decodeRawPacketWithPayload? abi (abi.encodeRaw (encodePacket slotOf a payload)) = some a := by
  simp [decodeRawPacketWithPayload?, abi.roundTrip,
    decode_payload_encode_packet_atom slotOf a payload hrec]

/-! ## Shared opening-context packet contract -/

abbrev ContextId := Nat

/-- A scoped opening context recovers exact CeTTa variables from structural slots. -/
structure OpeningContext where
  varOf? : Slot → Option VarId
  spellingOf? : Slot → Option Spelling

namespace OpeningContext

/-- A context recovers all variables used by a slot assignment. -/
def Recovers (ctx : OpeningContext) (slotOf : VarId → Slot) : Prop :=
  ∀ v, ctx.varOf? (slotOf v) = some v

mutual
  /-- Support-local coverage for one exact atom. Unlike `Recovers`, this only
  requires context entries for variables that actually occur in the atom. -/
  def CoversAtom (ctx : OpeningContext) (slotOf : VarId → Slot) : CAtom → Prop
    | .symbol _ => True
    | .var v => ctx.varOf? (slotOf v) = some v
    | .grounded _ => True
    | .expression es => CoversAtomList ctx slotOf es

  /-- Support-local coverage for an atom list. -/
  def CoversAtomList (ctx : OpeningContext) (slotOf : VarId → Slot) :
      List CAtom → Prop
    | [] => True
    | a :: as => CoversAtom ctx slotOf a ∧ CoversAtomList ctx slotOf as
end

mutual
  /-- Global recovery implies support-local atom coverage. -/
  theorem recovers_covers_atom
      (ctx : OpeningContext) (slotOf : VarId → Slot)
      (hrec : ctx.Recovers slotOf) :
      ∀ a, ctx.CoversAtom slotOf a
    | .symbol _ => trivial
    | .var v => hrec v
    | .grounded _ => trivial
    | .expression es => recovers_covers_atom_list ctx slotOf hrec es

  /-- Global recovery implies support-local list coverage. -/
  theorem recovers_covers_atom_list
      (ctx : OpeningContext) (slotOf : VarId → Slot)
      (hrec : ctx.Recovers slotOf) :
      ∀ as, ctx.CoversAtomList slotOf as
    | [] => trivial
    | a :: as =>
        ⟨recovers_covers_atom ctx slotOf hrec a,
          recovers_covers_atom_list ctx slotOf hrec as⟩
end

/-- A row-local payload can be viewed as a one-row opening context. -/
def ofPayload (payload : IdentityPayload) : OpeningContext :=
  { varOf? := payload.varOf?
    spellingOf? := fun _ => none }

end OpeningContext

/-- A packet-level context table shared by many structural rows. -/
structure OpeningContextTable where
  contextOf? : ContextId → Option OpeningContext

namespace OpeningContextTable

/-- A table entry recovers all variables used by a slot assignment. -/
def RecoversAt (table : OpeningContextTable) (context : ContextId)
    (slotOf : VarId → Slot) : Prop :=
  ∃ ctx, table.contextOf? context = some ctx ∧ ctx.Recovers slotOf

/-- A table entry covers exactly the variables occurring in one atom. -/
def CoversAtomAt (table : OpeningContextTable) (context : ContextId)
    (slotOf : VarId → Slot) (a : CAtom) : Prop :=
  ∃ ctx, table.contextOf? context = some ctx ∧ ctx.CoversAtom slotOf a

/-- Global table recovery implies support-local coverage for any atom. -/
theorem recoversAt_coversAtomAt
    (table : OpeningContextTable) (context : ContextId)
    (slotOf : VarId → Slot) (a : CAtom)
    (hrec : table.RecoversAt context slotOf) :
    table.CoversAtomAt context slotOf a := by
  rcases hrec with ⟨ctx, hctx, hrecCtx⟩
  exact ⟨ctx, hctx, OpeningContext.recovers_covers_atom ctx slotOf hrecCtx a⟩

end OpeningContextTable


/-- ABI-independent packet model using structural payload plus a shared context reference. -/
structure ContextualBridgePacket where
  context : ContextId
  structural : SlotAtom

mutual
  /-- Decode a structural slot atom by opening its slots through a scoped context. -/
  def decodeSlotAtomWithContext? (ctx : OpeningContext) : SlotAtom → Option CAtom
    | .symbol s => some (.symbol s)
    | .slot n =>
        match ctx.varOf? n with
        | some v => some (.var v)
        | none => none
    | .grounded g => some (.grounded g)
    | .expression es =>
        match decodeSlotAtomListWithContext? ctx es with
        | some as => some (.expression as)
        | none => none

  /-- Decode a list of structural slot atoms through a scoped context. -/
  def decodeSlotAtomListWithContext? (ctx : OpeningContext) :
      List SlotAtom → Option (List CAtom)
    | [] => some []
    | a :: as =>
        match decodeSlotAtomWithContext? ctx a,
          decodeSlotAtomListWithContext? ctx as with
        | some a', some as' => some (a' :: as')
        | _, _ => none
end

mutual
  /-- Context decoding recovers an encoded atom when the context covers exactly
  the atom's variable support. -/
  @[simp]
  theorem decode_context_encode_catom_id_of_covers
      (slotOf : VarId → Slot) (ctx : OpeningContext) :
      ∀ a, ctx.CoversAtom slotOf a →
        decodeSlotAtomWithContext? ctx (encodeCAtomWith slotOf a) = some a
    | .symbol _, _ => rfl
    | .var v, hcover => by
        change ctx.varOf? (slotOf v) = some v at hcover
        simp [encodeCAtomWith, decodeSlotAtomWithContext?, hcover]
    | .grounded _, _ => rfl
    | .expression es, hcover => by
        change ctx.CoversAtomList slotOf es at hcover
        simp [encodeCAtomWith, decodeSlotAtomWithContext?,
          decode_context_encode_catom_list_id_of_covers slotOf ctx es hcover]

  /-- Context decoding recovers an encoded list when the context covers exactly
  the list's variable support. -/
  @[simp]
  theorem decode_context_encode_catom_list_id_of_covers
      (slotOf : VarId → Slot) (ctx : OpeningContext) :
      ∀ as, ctx.CoversAtomList slotOf as →
        decodeSlotAtomListWithContext? ctx (encodeCAtomListWith slotOf as) = some as
    | [], _ => rfl
    | a :: as, hcover => by
        change ctx.CoversAtom slotOf a ∧ ctx.CoversAtomList slotOf as at hcover
        simp [encodeCAtomListWith, decodeSlotAtomListWithContext?,
          decode_context_encode_catom_id_of_covers slotOf ctx a hcover.1,
          decode_context_encode_catom_list_id_of_covers slotOf ctx as hcover.2]
end

mutual
  /-- Context decoding recovers an encoded atom when the context covers the slots used. -/
  @[simp]
  theorem decode_context_encode_catom_id
      (slotOf : VarId → Slot) (ctx : OpeningContext)
      (hrec : ctx.Recovers slotOf) :
      ∀ a, decodeSlotAtomWithContext? ctx (encodeCAtomWith slotOf a) = some a
    | a =>
        decode_context_encode_catom_id_of_covers slotOf ctx a
          (OpeningContext.recovers_covers_atom ctx slotOf hrec a)

  /-- Context decoding recovers an encoded atom list when the context covers the slots used. -/
  @[simp]
  theorem decode_context_encode_catom_list_id
      (slotOf : VarId → Slot) (ctx : OpeningContext)
      (hrec : ctx.Recovers slotOf) :
      ∀ as, decodeSlotAtomListWithContext? ctx (encodeCAtomListWith slotOf as) = some as
    | as =>
        decode_context_encode_catom_list_id_of_covers slotOf ctx as
          (OpeningContext.recovers_covers_atom_list ctx slotOf hrec as)
end

/-- Encode an exact atom into the shared-context packet contract. -/
def encodeContextualPacket (context : ContextId) (slotOf : VarId → Slot) (a : CAtom) :
    ContextualBridgePacket :=
  { context := context
    structural := encodeCAtomWith slotOf a }

/-- Decode a contextual packet by first selecting its shared opening context. -/
def decodeContextualPacket? (table : OpeningContextTable)
    (packet : ContextualBridgePacket) : Option CAtom :=
  match table.contextOf? packet.context with
  | some ctx => decodeSlotAtomWithContext? ctx packet.structural
  | none => none

/-- Shared-context decoding after encoding recovers the original exact atom. -/
@[simp]
theorem decode_contextual_encode_packet_exact_of_covers
    (table : OpeningContextTable) (context : ContextId) (slotOf : VarId → Slot)
    (a : CAtom)
    (hcover : table.CoversAtomAt context slotOf a) :
    decodeContextualPacket? table (encodeContextualPacket context slotOf a) = some a := by
  rcases hcover with ⟨ctx, hctx, hcoverCtx⟩
  simp [decodeContextualPacket?, encodeContextualPacket, hctx,
    decode_context_encode_catom_id_of_covers slotOf ctx a hcoverCtx]

/-- Shared-context decoding after encoding recovers the original exact atom.
This global recovery form is retained as a convenience wrapper around the
support-local theorem. -/
@[simp]
theorem decode_contextual_encode_packet_exact
    (table : OpeningContextTable) (context : ContextId) (slotOf : VarId → Slot)
    (a : CAtom)
    (hrec : table.RecoversAt context slotOf) :
    decodeContextualPacket? table (encodeContextualPacket context slotOf a) = some a := by
  exact decode_contextual_encode_packet_exact_of_covers table context slotOf a
    (OpeningContextTable.recoversAt_coversAtomAt table context slotOf a hrec)

/-- Without the referenced context, contextual packet decoding fails before opening slots. -/
theorem decode_contextual_packet_missing_context
    (table : OpeningContextTable) (packet : ContextualBridgePacket)
    (hmissing : table.contextOf? packet.context = none) :
    decodeContextualPacket? table packet = none := by
  simp [decodeContextualPacket?, hmissing]

/-! ## Shared-context query packet shape and exact binding recovery -/

/-- One query binding row entry whose value is opened through a shared context table. -/
structure ContextualQueryBindingPacket where
  querySlot : Slot
  value : ContextualBridgePacket

/-- A contextual query result row is a list of variable bindings. -/
structure ContextualQueryRowPacket where
  bindings : List ContextualQueryBindingPacket

/-- The abstract decoded contextual query result packet. -/
structure ContextualQueryPacket where
  rows : List ContextualQueryRowPacket

/-- Decode one contextual query binding. -/
def decodeContextualQueryBinding? (queryContext : OpeningContext)
    (table : OpeningContextTable) (binding : ContextualQueryBindingPacket) :
    Option (VarId × CAtom) :=
  match queryContext.varOf? binding.querySlot,
    decodeContextualPacket? table binding.value with
  | some v, some a => some (v, a)
  | _, _ => none

/-- Decode a contextual query row. -/
def decodeContextualQueryRow? (queryContext : OpeningContext)
    (table : OpeningContextTable) (row : ContextualQueryRowPacket) :
    List (Option (VarId × CAtom)) :=
  row.bindings.map (decodeContextualQueryBinding? queryContext table)

/-- Decode a contextual query packet row-by-row. -/
def decodeContextualQueryPacket? (queryContext : OpeningContext)
    (table : OpeningContextTable) (packet : ContextualQueryPacket) :
    List (List (Option (VarId × CAtom))) :=
  packet.rows.map (decodeContextualQueryRow? queryContext table)

/-- Encode one exact binding into the shared-context query binding contract. -/
def encodeContextualQueryBindingPacket
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (key : VarId) (value : CAtom) : ContextualQueryBindingPacket :=
  { querySlot := querySlotOf key
    value := encodeContextualPacket valueContext valueSlotOf value }

/-- Decoding an encoded contextual query binding recovers the exact key and value. -/
@[simp]
theorem decode_encode_contextual_query_binding_packet
    (querySlotOf valueSlotOf : VarId → Slot)
    (queryContext : OpeningContext) (table : OpeningContextTable)
    (valueContext : ContextId)
    (hquery : queryContext.Recovers querySlotOf)
    (hvalue : table.RecoversAt valueContext valueSlotOf)
    (key : VarId) (value : CAtom) :
    decodeContextualQueryBinding? queryContext table
      (encodeContextualQueryBindingPacket querySlotOf valueSlotOf valueContext key value) =
      some (key, value) := by
  simp [decodeContextualQueryBinding?, encodeContextualQueryBindingPacket, hquery key,
    decode_contextual_encode_packet_exact table valueContext valueSlotOf value hvalue]

/-- If a contextual query binding decodes, its key came from the query opening context. -/
theorem decoded_contextual_query_binding_key_preserved
    (queryContext : OpeningContext) (table : OpeningContextTable)
    (binding : ContextualQueryBindingPacket)
    {key : VarId} {value : CAtom}
    (hdecode : decodeContextualQueryBinding? queryContext table binding = some (key, value)) :
    queryContext.varOf? binding.querySlot = some key := by
  unfold decodeContextualQueryBinding? at hdecode
  cases hslot : queryContext.varOf? binding.querySlot with
  | none =>
      simp [hslot] at hdecode
  | some recovered =>
      cases hvalue : decodeContextualPacket? table binding.value with
      | none =>
          simp [hslot, hvalue] at hdecode
      | some decoded =>
          simp [hslot, hvalue] at hdecode
          exact congrArg some hdecode.1

/-- If a contextual decoded row contains a key/value pair, a source binding recovered it. -/
theorem decoded_contextual_query_row_entry_preserved
    (queryContext : OpeningContext) (table : OpeningContextTable)
    (row : ContextualQueryRowPacket)
    {key : VarId} {value : CAtom}
    (hmem : some (key, value) ∈ decodeContextualQueryRow? queryContext table row) :
    ∃ binding ∈ row.bindings,
      queryContext.varOf? binding.querySlot = some key ∧
      decodeContextualPacket? table binding.value = some value := by
  unfold decodeContextualQueryRow? at hmem
  obtain ⟨binding, hbinding, hdecode⟩ := List.mem_map.mp hmem
  refine ⟨binding, hbinding, ?_, ?_⟩
  · exact decoded_contextual_query_binding_key_preserved queryContext table binding hdecode
  · unfold decodeContextualQueryBinding? at hdecode
    cases hslot : queryContext.varOf? binding.querySlot with
    | none =>
        simp [hslot] at hdecode
    | some recovered =>
        cases hvalue : decodeContextualPacket? table binding.value with
        | none =>
            simp [hslot, hvalue] at hdecode
        | some decoded =>
            simp [hslot, hvalue] at hdecode
            exact congrArg some hdecode.2


/-! ## Structural PathMap lookup contract -/

/-- A packet is a structural hit for `query` when its structural payload equals the encoded query. -/
def StructuralHit (slotOf : VarId → Slot) (query : CAtom) (packet : BridgePacket) : Prop :=
  packet.structural = encodeCAtomWith slotOf query

/-- A packet identity payload recovers all variables in the given slot interface. -/
def PacketPayloadRecovers (slotOf : VarId → Slot) (packet : BridgePacket) : Prop :=
  ∀ v, packet.identity.varOf? (slotOf v) = some v

/-- A structural packet store: PathMap lookup is represented by a finite byte trie. -/
structure StructuralPacketStore where
  pathOf : SlotAtom → List UInt8
  trie : FTrie BridgePacket

namespace StructuralPacketStore

/-- Look up a structural packet by the encoded structural atom path. -/
def lookup? (store : StructuralPacketStore) (structural : SlotAtom) :
    Option BridgePacket :=
  store.trie.lookup (store.pathOf structural)

/-- Look up the packet corresponding to an exact query after structural lowering. -/
def lookupExact? (store : StructuralPacketStore) (slotOf : VarId → Slot) (query : CAtom) :
    Option BridgePacket :=
  store.lookup? (encodeCAtomWith slotOf query)

/-- A structural packet store is sound when every lookup result carries the queried structural key. -/
def Sound (store : StructuralPacketStore) : Prop :=
  ∀ structural packet, store.lookup? structural = some packet → packet.structural = structural

end StructuralPacketStore

/-- A trie lookup hit for an exact query, stated against the structural store. -/
def TrieLookupHit (store : StructuralPacketStore) (slotOf : VarId → Slot)
    (query : CAtom) (packet : BridgePacket) : Prop :=
  store.lookupExact? slotOf query = some packet

/-- A lookup hit from a structural packet store decodes exactly when the payload recovers slots. -/
theorem trie_lookup_hit_decodes_exact
    (store : StructuralPacketStore) (slotOf : VarId → Slot)
    {query : CAtom} {packet : BridgePacket}
    (_hlookup : TrieLookupHit store slotOf query packet)
    (hstruct : StructuralHit slotOf query packet)
    (hrec : PacketPayloadRecovers slotOf packet) :
    decodePacketWithPayload? packet = some query := by
  unfold decodePacketWithPayload? StructuralHit at *
  rw [hstruct]
  exact decode_payload_encode_catom_id slotOf packet.identity hrec query

/-- Sound structural lookup plus payload recovery decodes to the exact queried atom. -/
theorem sound_trie_lookup_hit_decodes_exact
    (store : StructuralPacketStore) (slotOf : VarId → Slot)
    {query : CAtom} {packet : BridgePacket}
    (hsound : store.Sound)
    (hlookup : TrieLookupHit store slotOf query packet)
    (hrec : PacketPayloadRecovers slotOf packet) :
    decodePacketWithPayload? packet = some query := by
  apply trie_lookup_hit_decodes_exact store slotOf hlookup
  · exact hsound (encodeCAtomWith slotOf query) packet hlookup
  · exact hrec

/-- Negative example: a trie hit alone is not enough to recover exact identity. -/
theorem trie_lookup_hit_without_payload_can_decode_none
    (store : StructuralPacketStore) (slotOf : VarId → Slot)
    {query : CAtom} {packet : BridgePacket}
    (_hlookup : TrieLookupHit store slotOf query packet)
    (hdecode : decodePacketWithPayload? packet = none) :
    decodePacketWithPayload? packet ≠ some query := by
  intro hsome
  rw [hdecode] at hsome
  cases hsome

/-- Structural lookup hit plus payload recovery decodes to the exact query. -/
theorem structural_hit_decodes_exact (slotOf : VarId → Slot)
    {query : CAtom} {packet : BridgePacket}
    (hrec : PacketPayloadRecovers slotOf packet)
    (hhit : StructuralHit slotOf query packet) :
    decodePacketWithPayload? packet = some query := by
  unfold decodePacketWithPayload? StructuralHit at *
  rw [hhit]
  exact decode_payload_encode_catom_id slotOf packet.identity hrec query

/-- Every decoded result from a structurally sound lookup is the exact queried atom. -/
theorem decoded_structural_hits_are_exact (slotOf : VarId → Slot)
    (query : CAtom) (packets : List BridgePacket)
    (hrec : ∀ packet ∈ packets, PacketPayloadRecovers slotOf packet)
    (hhit : ∀ packet ∈ packets, StructuralHit slotOf query packet) :
    ∀ a, some a ∈ packets.map decodePacketWithPayload? → a = query := by
  intro a ha
  obtain ⟨packet, hpacket, hdecode⟩ := List.mem_map.mp ha
  have hq := structural_hit_decodes_exact slotOf (hrec packet hpacket) (hhit packet hpacket)
  rw [hq] at hdecode
  cases hdecode
  rfl

/-! ## Shared-context structural lookup contract -/

/-- A contextual packet is a structural hit for `query` when its payload equals the encoded query. -/
def ContextualStructuralHit (slotOf : VarId → Slot) (query : CAtom)
    (packet : ContextualBridgePacket) : Prop :=
  packet.structural = encodeCAtomWith slotOf query

/-- A contextual packet recovers exact variables through its referenced opening context. -/
def ContextualPacketRecovers (table : OpeningContextTable) (slotOf : VarId → Slot)
    (packet : ContextualBridgePacket) : Prop :=
  table.RecoversAt packet.context slotOf

/-- Structural lookup plus contextual recovery decodes to the exact queried atom. -/
theorem contextual_structural_hit_decodes_exact
    (table : OpeningContextTable) (slotOf : VarId → Slot)
    {query : CAtom} {packet : ContextualBridgePacket}
    (hrec : ContextualPacketRecovers table slotOf packet)
    (hhit : ContextualStructuralHit slotOf query packet) :
    decodeContextualPacket? table packet = some query := by
  rcases hrec with ⟨ctx, hctx, hrecCtx⟩
  unfold decodeContextualPacket? ContextualStructuralHit at *
  rw [hctx, hhit]
  exact decode_context_encode_catom_id slotOf ctx hrecCtx query

/-- A structural contextual packet store: PathMap lookup is represented by a finite byte trie. -/
structure ContextualPacketStore where
  contexts : OpeningContextTable
  pathOf : SlotAtom → List UInt8
  trie : FTrie ContextualBridgePacket

namespace ContextualPacketStore

/-- Look up a contextual packet by the encoded structural atom path. -/
def lookup? (store : ContextualPacketStore) (structural : SlotAtom) :
    Option ContextualBridgePacket :=
  store.trie.lookup (store.pathOf structural)

/-- Look up the contextual packet corresponding to an exact query after structural lowering. -/
def lookupExact? (store : ContextualPacketStore) (slotOf : VarId → Slot) (query : CAtom) :
    Option ContextualBridgePacket :=
  store.lookup? (encodeCAtomWith slotOf query)

/-- A contextual packet store is sound when lookup results carry the queried structural key. -/
def Sound (store : ContextualPacketStore) : Prop :=
  ∀ structural packet, store.lookup? structural = some packet → packet.structural = structural

end ContextualPacketStore

/-- A contextual trie lookup hit for an exact query. -/
def ContextualTrieLookupHit (store : ContextualPacketStore) (slotOf : VarId → Slot)
    (query : CAtom) (packet : ContextualBridgePacket) : Prop :=
  store.lookupExact? slotOf query = some packet

/-- Sound structural lookup plus shared-context recovery decodes to the exact queried atom. -/
theorem contextual_sound_trie_lookup_hit_decodes_exact
    (store : ContextualPacketStore) (slotOf : VarId → Slot)
    {query : CAtom} {packet : ContextualBridgePacket}
    (hsound : store.Sound)
    (hlookup : ContextualTrieLookupHit store slotOf query packet)
    (hrec : ContextualPacketRecovers store.contexts slotOf packet) :
    decodeContextualPacket? store.contexts packet = some query := by
  apply contextual_structural_hit_decodes_exact store.contexts slotOf hrec
  exact hsound (encodeCAtomWith slotOf query) packet hlookup

/-- Every decoded contextual result from a structurally sound lookup is the exact queried atom. -/
theorem decoded_contextual_structural_hits_are_exact
    (table : OpeningContextTable) (slotOf : VarId → Slot)
    (query : CAtom) (packets : List ContextualBridgePacket)
    (hrec : ∀ packet ∈ packets, ContextualPacketRecovers table slotOf packet)
    (hhit : ∀ packet ∈ packets, ContextualStructuralHit slotOf query packet) :
    ∀ a, some a ∈ packets.map (decodeContextualPacket? table) → a = query := by
  intro a ha
  obtain ⟨packet, hpacket, hdecode⟩ := List.mem_map.mp ha
  have hq := contextual_structural_hit_decodes_exact table slotOf
    (hrec packet hpacket) (hhit packet hpacket)
  rw [hq] at hdecode
  cases hdecode
  rfl

/-! ## Shared-context PathMap candidate/query preservation -/

/-- The native rematcher used after PathMap candidate selection. -/
structure ContextualNativeMatcher where
  isMatch : CAtom → CAtom → Bool

/-- A boundary projection from CeTTa-aware `CAtom`s into the concrete HE atom
language. The projection itself belongs to the implementation boundary. -/
structure CAtomHEProjection where
  toHE : CAtom → Mettapedia.Languages.MeTTa.OSLFCore.Atom

namespace ContextualNativeMatcher

/-- Instantiate the contextual matcher with the concrete HE `matchAtoms` matcher
after projecting exact `CAtom`s into HE atoms. -/
def fromHEProjection (projection : CAtomHEProjection) (fuel : Nat) :
    ContextualNativeMatcher :=
  { isMatch := fun query atom =>
      Mettapedia.OSLF.PathMap.PathMapMatcherInstance.heIsMatch fuel
        (projection.toHE query) (projection.toHE atom) }

end ContextualNativeMatcher

/-- A logical exact atom space used to state direct-query semantics. -/
structure ContextualExactSpace where
  atomSupport : List CAtom

/-- PathMap candidate selection after structural lookup and contextual opening. -/
structure ContextualCandidateSelector where
  candidates : CAtom → List CAtom

namespace ContextualCandidateSelector

/-- Candidate selection is sound when every direct match is present among candidates. -/
def Sound (sel : ContextualCandidateSelector) (matcher : ContextualNativeMatcher)
    (space : ContextualExactSpace) : Prop :=
  ∀ query a,
    a ∈ space.atomSupport →
    matcher.isMatch query a = true →
    a ∈ sel.candidates query

/-- Candidate selection has no decoded rows outside the logical exact space. -/
def SubsetOf (sel : ContextualCandidateSelector)
    (space : ContextualExactSpace) : Prop :=
  ∀ query a, a ∈ sel.candidates query → a ∈ space.atomSupport

/-- Candidate selection preserves support multiplicity when its candidate list
is a permutation of the logical exact support for each query. This is stronger
than membership soundness and is the right contract for result-row counts. -/
def MultiplicityExact (sel : ContextualCandidateSelector)
    (space : ContextualExactSpace) : Prop :=
  ∀ query, (sel.candidates query).Perm space.atomSupport

end ContextualCandidateSelector

/-- Two-phase query: PathMap candidates followed by native rematch. -/
def contextualTwoPhaseQuery (sel : ContextualCandidateSelector)
    (matcher : ContextualNativeMatcher) (query : CAtom) : List CAtom :=
  (sel.candidates query).filter (fun a => matcher.isMatch query a)

/-- Direct query semantics over the exact logical space. -/
def contextualDirectQuery (matcher : ContextualNativeMatcher)
    (space : ContextualExactSpace) (query : CAtom) : List CAtom :=
  space.atomSupport.filter (fun a => matcher.isMatch query a)

/-- If contextual candidate selection is sound and has no spurious decoded atoms,
then candidate selection plus native rematch preserves direct match semantics. -/
theorem contextual_twoPhase_mem_iff_direct
    (sel : ContextualCandidateSelector) (matcher : ContextualNativeMatcher)
    (space : ContextualExactSpace) (query a : CAtom)
    (hsound : sel.Sound matcher space)
    (hsubset : sel.SubsetOf space) :
    a ∈ contextualTwoPhaseQuery sel matcher query ↔
      a ∈ contextualDirectQuery matcher space query := by
  constructor
  · intro h
    simp [contextualTwoPhaseQuery] at h
    simp [contextualDirectQuery, hsubset query a h.1, h.2]
  · intro h
    simp [contextualDirectQuery] at h
    simp [contextualTwoPhaseQuery, hsound query a h.1 h.2, h.2]

/-- If candidate selection preserves multiplicity before rematching, then
two-phase query results are permutation-equivalent to direct query results.
This is the list-level result-row contract: duplicates are preserved up to order. -/
theorem contextual_twoPhase_perm_direct
    (sel : ContextualCandidateSelector) (matcher : ContextualNativeMatcher)
    (space : ContextualExactSpace) (query : CAtom)
    (hmult : sel.MultiplicityExact space) :
    (contextualTwoPhaseQuery sel matcher query).Perm
      (contextualDirectQuery matcher space query) := by
  exact (hmult query).filter (fun a => matcher.isMatch query a)

/-- Decode a packet candidate list by opening each packet through the shared context table. -/
def decodeContextualPacketCandidates (table : OpeningContextTable)
    (packets : List ContextualBridgePacket) : List CAtom :=
  packets.filterMap (decodeContextualPacket? table)

/-- A PathMap candidate selector before contextual opening. -/
structure ContextualPacketCandidateSelector where
  packetCandidates : CAtom → List ContextualBridgePacket

/-- Interpret packet candidates as exact candidates by opening with a context table. -/
def ContextualPacketCandidateSelector.asDecodedSelector
    (table : OpeningContextTable) (sel : ContextualPacketCandidateSelector) :
    ContextualCandidateSelector :=
  { candidates := fun query =>
      decodeContextualPacketCandidates table (sel.packetCandidates query) }

/-- Packet-level candidate selection preserves direct-query semantics whenever its
decoded candidate selector is sound and subset-bounded for the exact space. -/
theorem contextual_packet_twoPhase_mem_iff_direct
    (table : OpeningContextTable)
    (sel : ContextualPacketCandidateSelector) (matcher : ContextualNativeMatcher)
    (space : ContextualExactSpace) (query a : CAtom)
    (hsound : (sel.asDecodedSelector table).Sound matcher space)
    (hsubset : (sel.asDecodedSelector table).SubsetOf space) :
    a ∈ contextualTwoPhaseQuery (sel.asDecodedSelector table) matcher query ↔
      a ∈ contextualDirectQuery matcher space query :=
  contextual_twoPhase_mem_iff_direct (sel.asDecodedSelector table) matcher space
    query a hsound hsubset

/-- Packet-level candidate selection preserves result-row multiplicity whenever
the decoded packet candidates preserve exact support multiplicity. -/
theorem contextual_packet_twoPhase_perm_direct
    (table : OpeningContextTable)
    (sel : ContextualPacketCandidateSelector) (matcher : ContextualNativeMatcher)
    (space : ContextualExactSpace) (query : CAtom)
    (hmult : (sel.asDecodedSelector table).MultiplicityExact space) :
    (contextualTwoPhaseQuery (sel.asDecodedSelector table) matcher query).Perm
      (contextualDirectQuery matcher space query) :=
  contextual_twoPhase_perm_direct (sel.asDecodedSelector table) matcher space query hmult

/-- Contextual packet candidates also preserve result-row multiplicity when the
native rematch is the concrete HE matcher reached through a boundary projection. -/
theorem contextual_packet_heProjected_twoPhase_perm_direct
    (table : OpeningContextTable)
    (sel : ContextualPacketCandidateSelector) (projection : CAtomHEProjection)
    (fuel : Nat) (space : ContextualExactSpace) (query : CAtom)
    (hmult : (sel.asDecodedSelector table).MultiplicityExact space) :
    (contextualTwoPhaseQuery (sel.asDecodedSelector table)
      (ContextualNativeMatcher.fromHEProjection projection fuel) query).Perm
      (contextualDirectQuery
        (ContextualNativeMatcher.fromHEProjection projection fuel) space query) :=
  contextual_packet_twoPhase_perm_direct table sel
    (ContextualNativeMatcher.fromHEProjection projection fuel) space query hmult

/-! ## Future bridge surface: locally nameless open/close laws -/

namespace LocallyNameless

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-- Existing locally nameless law: closing a fresh free variable after opening recovers the term. -/
theorem close_open_interface (k : Nat) (x : String) (p : Pattern)
    (hfresh : x ∉ freeVars p) :
    closeFVar k x (openBVar k (.fvar x) p) = p :=
  close_open_id k x p hfresh

/-- Existing locally nameless law: opening after closing a locally closed term recovers the term. -/
theorem open_close_interface (k : Nat) (x : String) (p : Pattern)
    (hlc : lc_at k p = true) :
    openBVar k (.fvar x) (closeFVar k x p) = p :=
  open_close_id k x p hlc

end LocallyNameless


end Mettapedia.OSLF.PathMap.VarIdBridge
