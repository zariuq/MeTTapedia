import Mettapedia.OSLF.PathMap.VarIdBridge.Core

namespace Mettapedia.OSLF.PathMap.VarIdBridge

open Mettapedia.OSLF.PathMap.CanonicalUniverse
open Mettapedia.OSLF.PathMap.Trie

/-! ## Current query packet shape and exact binding recovery -/

/-- One query binding row entry: a query variable slot and its structural value packet. -/
structure QueryBindingPacket where
  querySlot : Slot
  value : BridgePacket

/-- A query result row is a list of variable bindings. -/
structure QueryRowPacket where
  bindings : List QueryBindingPacket

/-- The abstract decoded query result packet. -/
structure QueryPacket where
  rows : List QueryRowPacket

/-- Decode one query binding through the query-slot payload and the value payload. -/
def decodeQueryBinding? (queryIdentity : IdentityPayload)
    (binding : QueryBindingPacket) : Option (VarId × CAtom) :=
  match queryIdentity.varOf? binding.querySlot,
    decodePacketWithPayload? binding.value with
  | some v, some a => some (v, a)
  | _, _ => none

/-- Decode a query result row. -/
def decodeQueryRow? (queryIdentity : IdentityPayload)
    (row : QueryRowPacket) : List (Option (VarId × CAtom)) :=
  row.bindings.map (decodeQueryBinding? queryIdentity)

/-- Decode a query packet row-by-row. -/
def decodeQueryPacket? (queryIdentity : IdentityPayload)
    (packet : QueryPacket) : List (List (Option (VarId × CAtom))) :=
  packet.rows.map (decodeQueryRow? queryIdentity)

/-- Encode one exact binding into the abstract query binding packet contract. -/
def encodeQueryBindingPacket (querySlotOf valueSlotOf : VarId → Slot)
    (key : VarId) (value : CAtom) (valueIdentity : IdentityPayload) :
    QueryBindingPacket :=
  { querySlot := querySlotOf key
    value := encodePacket valueSlotOf value valueIdentity }

/-- Decoding an encoded query binding recovers the exact key and value identities. -/
@[simp]
theorem decode_encode_query_binding_packet
    (querySlotOf valueSlotOf : VarId → Slot)
    (queryIdentity valueIdentity : IdentityPayload)
    (hquery : ∀ v, queryIdentity.varOf? (querySlotOf v) = some v)
    (hvalue : ∀ v, valueIdentity.varOf? (valueSlotOf v) = some v)
    (key : VarId) (value : CAtom) :
    decodeQueryBinding? queryIdentity
      (encodeQueryBindingPacket querySlotOf valueSlotOf key value valueIdentity) =
      some (key, value) := by
  simp [decodeQueryBinding?, encodeQueryBindingPacket, hquery key,
    decode_payload_encode_packet_atom valueSlotOf value valueIdentity hvalue]

/-- Positive example: a query binding with exact payloads decodes to the intended key/value. -/
theorem query_binding_exact_recovery_example :
    decodeQueryBinding? payloadA
      (encodeQueryBindingPacket collapsedSlot collapsedSlot
        exampleVarA (.var exampleVarA) payloadA) =
      some (exampleVarA, (.var exampleVarA)) := by
  rfl

/-- If a query binding decodes, its key was recovered from the query identity payload. -/
theorem decoded_query_binding_key_preserved
    (queryIdentity : IdentityPayload) (binding : QueryBindingPacket)
    {key : VarId} {value : CAtom}
    (hdecode : decodeQueryBinding? queryIdentity binding = some (key, value)) :
    queryIdentity.varOf? binding.querySlot = some key := by
  unfold decodeQueryBinding? at hdecode
  cases hslot : queryIdentity.varOf? binding.querySlot with
  | none =>
      simp [hslot] at hdecode
  | some recovered =>
      cases hvalue : decodePacketWithPayload? binding.value with
      | none =>
          simp [hslot, hvalue] at hdecode
      | some decoded =>
          simp [hslot, hvalue] at hdecode
          exact congrArg some hdecode.1

/-- If a decoded row contains a key/value pair, some source binding recovered that key and value. -/
theorem decoded_query_row_entry_preserved
    (queryIdentity : IdentityPayload) (row : QueryRowPacket)
    {key : VarId} {value : CAtom}
    (hmem : some (key, value) ∈ decodeQueryRow? queryIdentity row) :
    ∃ binding ∈ row.bindings,
      queryIdentity.varOf? binding.querySlot = some key ∧
      decodePacketWithPayload? binding.value = some value := by
  unfold decodeQueryRow? at hmem
  obtain ⟨binding, hbinding, hdecode⟩ := List.mem_map.mp hmem
  refine ⟨binding, hbinding, ?_, ?_⟩
  · exact decoded_query_binding_key_preserved queryIdentity binding hdecode
  · unfold decodeQueryBinding? at hdecode
    cases hslot : queryIdentity.varOf? binding.querySlot with
    | none =>
        simp [hslot] at hdecode
    | some recovered =>
        cases hvalue : decodePacketWithPayload? binding.value with
        | none =>
            simp [hslot, hvalue] at hdecode
        | some decoded =>
            simp [hslot, hvalue] at hdecode
            exact congrArg some hdecode.2

/-- Current C bridge query-only v2 magic (`CTBR`). -/
def queryOnlyV2Magic : Nat := 0x43544252

def queryOnlyV2Version : Nat := 2
def multiRefV3Version : Nat := 3
def queryKeysOnlyFlag : Nat := 0x0001
def rawExprBytesFlag : Nat := 0x0002
def multiRefGroupsFlag : Nat := 0x0004
def directMultiplicitiesFlag : Nat := 0x0008
def wideTokensFlag : Nat := 0x0010
def queryOnlyV2Flags : Nat := queryKeysOnlyFlag + rawExprBytesFlag
def queryOnlyV2WideFlags : Nat := queryOnlyV2Flags + wideTokensFlag
def multiRefV3GroupFlags : Nat := queryOnlyV2Flags + multiRefGroupsFlag
def multiRefV3GroupWideFlags : Nat := multiRefV3GroupFlags + wideTokensFlag
def multiRefV3DirectFlags : Nat := queryOnlyV2Flags + directMultiplicitiesFlag
def multiRefV3DirectWideFlags : Nat := multiRefV3DirectFlags + wideTokensFlag

/-- The current query-only v2 packet shape consumed by the C bridge, abstracting byte parsing. -/
structure QueryOnlyV2Raw where
  magic : Nat
  version : Nat
  flags : Nat
  rowCount : Nat
  rows : List QueryRowPacket

namespace QueryOnlyV2Raw

/-- Header validity for the current query-only v2 packet family. -/
def Valid (raw : QueryOnlyV2Raw) : Prop :=
  raw.magic = queryOnlyV2Magic ∧
  raw.version = queryOnlyV2Version ∧
  (raw.flags = queryOnlyV2Flags ∨ raw.flags = queryOnlyV2WideFlags) ∧
  raw.rowCount = raw.rows.length

instance (raw : QueryOnlyV2Raw) : Decidable raw.Valid := by
  unfold Valid
  infer_instance

end QueryOnlyV2Raw

/-- Build a current-layout query-only v2 raw packet from abstract rows. -/
def encodeQueryOnlyV2Raw (rows : List QueryRowPacket) : QueryOnlyV2Raw :=
  { magic := queryOnlyV2Magic
    version := queryOnlyV2Version
    flags := queryOnlyV2Flags
    rowCount := rows.length
    rows := rows }

/-- Decode a current-layout query-only v2 packet after header validation. -/
def decodeQueryOnlyV2Raw? (raw : QueryOnlyV2Raw) : Option QueryPacket :=
  if _ : raw.Valid then some { rows := raw.rows } else none

/-- The abstract query-only v2 encoder satisfies the current header contract. -/
theorem encodeQueryOnlyV2Raw_valid (rows : List QueryRowPacket) :
    (encodeQueryOnlyV2Raw rows).Valid := by
  simp [encodeQueryOnlyV2Raw, QueryOnlyV2Raw.Valid, queryOnlyV2Flags]

/-- Query-only v2 raw encode/decode round-trips at the validated packet layer. -/
@[simp]
theorem decode_encode_queryOnlyV2Raw (rows : List QueryRowPacket) :
    decodeQueryOnlyV2Raw? (encodeQueryOnlyV2Raw rows) = some { rows := rows } := by
  unfold decodeQueryOnlyV2Raw?
  rw [dif_pos (encodeQueryOnlyV2Raw_valid rows)]
  rfl

/-- Decoding a valid current-layout query-only v2 packet preserves its row count. -/
theorem decodeQueryOnlyV2Raw_row_count
    (raw : QueryOnlyV2Raw) (packet : QueryPacket)
    (hvalid : raw.Valid)
    (hdecode : decodeQueryOnlyV2Raw? raw = some packet) :
    packet.rows.length = raw.rowCount := by
  unfold decodeQueryOnlyV2Raw? at hdecode
  rw [dif_pos hvalid] at hdecode
  cases hdecode
  exact hvalid.2.2.2.symm

/-- The current multi-ref v3 packet shape consumed by the C bridge, abstracting byte parsing. -/
structure MultiRefV3Raw where
  magic : Nat
  version : Nat
  flags : Nat
  factorCount : Nat
  rowCount : Nat
  rows : List QueryRowPacket

namespace MultiRefV3Raw

/-- Header validity for the current multi-ref v3 packet family. -/
def Valid (raw : MultiRefV3Raw) : Prop :=
  raw.magic = queryOnlyV2Magic ∧
  raw.version = multiRefV3Version ∧
  (raw.flags = multiRefV3GroupFlags ∨
    raw.flags = multiRefV3GroupWideFlags ∨
    raw.flags = multiRefV3DirectFlags ∨
    raw.flags = multiRefV3DirectWideFlags) ∧
  raw.rowCount = raw.rows.length

instance (raw : MultiRefV3Raw) : Decidable raw.Valid := by
  unfold Valid
  infer_instance

end MultiRefV3Raw

/-- Build a current-layout multi-ref v3 raw packet from abstract rows. -/
def encodeMultiRefV3Raw (factorCount : Nat) (rows : List QueryRowPacket) : MultiRefV3Raw :=
  { magic := queryOnlyV2Magic
    version := multiRefV3Version
    flags := multiRefV3DirectFlags
    factorCount := factorCount
    rowCount := rows.length
    rows := rows }

/-- Decode a current-layout multi-ref v3 packet after header validation. -/
def decodeMultiRefV3Raw? (raw : MultiRefV3Raw) : Option QueryPacket :=
  if _ : raw.Valid then some { rows := raw.rows } else none

/-- The abstract multi-ref v3 encoder satisfies the current header contract. -/
theorem encodeMultiRefV3Raw_valid (factorCount : Nat) (rows : List QueryRowPacket) :
    (encodeMultiRefV3Raw factorCount rows).Valid := by
  simp [encodeMultiRefV3Raw, MultiRefV3Raw.Valid, multiRefV3DirectFlags]

/-- Multi-ref v3 raw encode/decode round-trips at the validated packet layer. -/
@[simp]
theorem decode_encode_multiRefV3Raw (factorCount : Nat) (rows : List QueryRowPacket) :
    decodeMultiRefV3Raw? (encodeMultiRefV3Raw factorCount rows) = some { rows := rows } := by
  unfold decodeMultiRefV3Raw?
  rw [dif_pos (encodeMultiRefV3Raw_valid factorCount rows)]
  rfl

/-- Decoding a valid current-layout multi-ref v3 packet preserves its row count. -/
theorem decodeMultiRefV3Raw_row_count
    (raw : MultiRefV3Raw) (packet : QueryPacket)
    (hvalid : raw.Valid)
    (hdecode : decodeMultiRefV3Raw? raw = some packet) :
    packet.rows.length = raw.rowCount := by
  unfold decodeMultiRefV3Raw? at hdecode
  rw [dif_pos hvalid] at hdecode
  cases hdecode
  exact hvalid.2.2.2.symm

/-! ## Current v2/v3 value provenance versus proposed contextual packets -/

def valueExprGroundFlag : Nat := 0x01

abbrev ProvenanceEnv := Nat

/-- The current C/Rust binding entry has a `valueEnv` field, but that field is
provenance in the present ABI rather than an exact opening-context reference. -/
structure CurrentProvenanceBindingEntry where
  querySlot : Slot
  valueEnv : ProvenanceEnv
  valueFlags : Nat
  expr : SlotAtom

/-- The current exact-decoding semantics can inspect the query slot, flags, and
structural value expression; it must not treat `valueEnv` as exact identity. -/
structure CurrentBindingSemanticView where
  querySlot : Slot
  valueFlags : Nat
  expr : SlotAtom

namespace CurrentProvenanceBindingEntry

/-- Erase current provenance before exact-opening reasoning. -/
def semanticView (entry : CurrentProvenanceBindingEntry) :
    CurrentBindingSemanticView :=
  { querySlot := entry.querySlot
    valueFlags := entry.valueFlags
    expr := entry.expr }

end CurrentProvenanceBindingEntry

/-- Current `valueEnv` is provenance-only for exact semantic views: changing it
does not change the value expression, query slot, or flags seen by the current
semantic layer. -/
theorem current_valueEnv_is_provenance_only
    (querySlot : Slot) (valueFlags : Nat) (expr : SlotAtom)
    (env₁ env₂ : ProvenanceEnv) :
    (CurrentProvenanceBindingEntry.semanticView
      { querySlot := querySlot, valueEnv := env₁,
        valueFlags := valueFlags, expr := expr }) =
    (CurrentProvenanceBindingEntry.semanticView
      { querySlot := querySlot, valueEnv := env₂,
        valueFlags := valueFlags, expr := expr }) := rfl

/-- One proposed contextual binding entry:
`query_slot`, an exact value-context id, `value_flags`, and structural
expression bytes. Do not identify this proposed `valueEnv` with the current
v2/v3 provenance field. -/
structure ContextualRawBindingEntry where
  querySlot : Slot
  valueEnv : ContextId
  valueFlags : Nat
  expr : SlotAtom

namespace ContextualRawBindingEntry

/-- The current bridge only gives semantic meaning to the ground-expression bit. -/
def ValidFlags (entry : ContextualRawBindingEntry) : Prop :=
  entry.valueFlags = 0 ∨ entry.valueFlags = valueExprGroundFlag

instance (entry : ContextualRawBindingEntry) : Decidable entry.ValidFlags := by
  unfold ValidFlags
  infer_instance

end ContextualRawBindingEntry

/-- Interpret one current raw binding entry as a shared-context query binding. -/
def ContextualRawBindingEntry.toBinding
    (entry : ContextualRawBindingEntry) : ContextualQueryBindingPacket :=
  { querySlot := entry.querySlot
    value := { context := entry.valueEnv, structural := entry.expr } }

/-- Encode one exact binding into the current C/Rust raw binding layout. -/
def encodeContextualRawBindingEntry
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (valueFlags : Nat) (key : VarId) (value : CAtom) :
    ContextualRawBindingEntry :=
  { querySlot := querySlotOf key
    valueEnv := valueContext
    valueFlags := valueFlags
    expr := encodeCAtomWith valueSlotOf value }

/-- Decoding a current raw binding entry recovers the exact key and value
when the query context and value opening context recover their slot maps. -/
@[simp]
theorem decode_encode_contextual_raw_binding_entry
    (querySlotOf valueSlotOf : VarId → Slot)
    (queryContext : OpeningContext) (table : OpeningContextTable)
    (valueContext : ContextId) (valueFlags : Nat)
    (hquery : queryContext.Recovers querySlotOf)
    (hvalue : table.RecoversAt valueContext valueSlotOf)
    (key : VarId) (value : CAtom) :
    decodeContextualQueryBinding? queryContext table
      ((encodeContextualRawBindingEntry querySlotOf valueSlotOf valueContext
        valueFlags key value).toBinding) =
      some (key, value) := by
  have hdecodeValue :
      decodeContextualPacket? table
        { context := valueContext, structural := encodeCAtomWith valueSlotOf value } =
        some value := by
    simpa [encodeContextualPacket] using
      decode_contextual_encode_packet_exact table valueContext valueSlotOf value hvalue
  simp [encodeContextualRawBindingEntry, ContextualRawBindingEntry.toBinding,
    decodeContextualQueryBinding?, hquery key, hdecodeValue]

/-- A current C/Rust query row carries a parsed `binding_count` plus raw entries. -/
structure ContextualRawQueryRow where
  bindingCount : Nat
  bindings : List ContextualRawBindingEntry

namespace ContextualRawQueryRow

/-- The parsed row count agrees with the number of parsed binding entries. -/
def BindingCountValid (row : ContextualRawQueryRow) : Prop :=
  row.bindingCount = row.bindings.length

instance (row : ContextualRawQueryRow) : Decidable row.BindingCountValid := by
  unfold BindingCountValid
  infer_instance

end ContextualRawQueryRow

/-- Build a current raw query row from parsed binding entries. -/
def encodeContextualRawQueryRow
    (bindings : List ContextualRawBindingEntry) : ContextualRawQueryRow :=
  { bindingCount := bindings.length
    bindings := bindings }

/-- Encoding a raw query row records the binding count exactly. -/
theorem encodeContextualRawQueryRow_binding_count
    (bindings : List ContextualRawBindingEntry) :
    (encodeContextualRawQueryRow bindings).BindingCountValid := by
  rfl

/-- Interpret one current raw row as the abstract shared-context query row. -/
def ContextualRawQueryRow.toRow
    (row : ContextualRawQueryRow) : ContextualQueryRowPacket :=
  { bindings := row.bindings.map ContextualRawBindingEntry.toBinding }

/-- The current query-only v2 packet layout with shared opening contexts. -/
structure ContextualQueryOnlyV2Raw where
  magic : Nat
  version : Nat
  flags : Nat
  rowCount : Nat
  rows : List ContextualRawQueryRow

namespace ContextualQueryOnlyV2Raw

/-- Header validity for the current contextual query-only v2 packet family. -/
def Valid (raw : ContextualQueryOnlyV2Raw) : Prop :=
  raw.magic = queryOnlyV2Magic ∧
  raw.version = queryOnlyV2Version ∧
  (raw.flags = queryOnlyV2Flags ∨ raw.flags = queryOnlyV2WideFlags) ∧
  raw.rowCount = raw.rows.length

instance (raw : ContextualQueryOnlyV2Raw) : Decidable raw.Valid := by
  unfold Valid
  infer_instance

end ContextualQueryOnlyV2Raw

/-- Build a current contextual query-only v2 raw packet from raw rows. -/
def encodeContextualQueryOnlyV2Raw
    (rows : List ContextualRawQueryRow) : ContextualQueryOnlyV2Raw :=
  { magic := queryOnlyV2Magic
    version := queryOnlyV2Version
    flags := queryOnlyV2Flags
    rowCount := rows.length
    rows := rows }

/-- Decode a current contextual query-only v2 packet after header validation. -/
def decodeContextualQueryOnlyV2Raw?
    (raw : ContextualQueryOnlyV2Raw) : Option ContextualQueryPacket :=
  if _ : raw.Valid then some { rows := raw.rows.map ContextualRawQueryRow.toRow } else none

/-- The contextual query-only v2 encoder satisfies the current header contract. -/
theorem encodeContextualQueryOnlyV2Raw_valid (rows : List ContextualRawQueryRow) :
    (encodeContextualQueryOnlyV2Raw rows).Valid := by
  simp [encodeContextualQueryOnlyV2Raw, ContextualQueryOnlyV2Raw.Valid, queryOnlyV2Flags]

/-- Contextual query-only v2 raw encode/decode round-trips at the validated packet layer. -/
@[simp]
theorem decode_encode_contextualQueryOnlyV2Raw
    (rows : List ContextualRawQueryRow) :
    decodeContextualQueryOnlyV2Raw? (encodeContextualQueryOnlyV2Raw rows) =
      some { rows := rows.map ContextualRawQueryRow.toRow } := by
  unfold decodeContextualQueryOnlyV2Raw?
  rw [dif_pos (encodeContextualQueryOnlyV2Raw_valid rows)]
  rfl

/-- Decoding a valid current contextual query-only v2 packet preserves its row count. -/
theorem decodeContextualQueryOnlyV2Raw_row_count
    (raw : ContextualQueryOnlyV2Raw) (packet : ContextualQueryPacket)
    (hvalid : raw.Valid)
    (hdecode : decodeContextualQueryOnlyV2Raw? raw = some packet) :
    packet.rows.length = raw.rowCount := by
  unfold decodeContextualQueryOnlyV2Raw? at hdecode
  rw [dif_pos hvalid] at hdecode
  cases hdecode
  simp [hvalid.2.2.2]

/-- The current multi-ref v3 packet layout with shared opening contexts. -/
structure ContextualMultiRefV3Raw where
  magic : Nat
  version : Nat
  flags : Nat
  factorCount : Nat
  rowCount : Nat
  rows : List ContextualRawQueryRow

namespace ContextualMultiRefV3Raw

/-- Header validity for the current contextual multi-ref v3 packet family. -/
def Valid (raw : ContextualMultiRefV3Raw) : Prop :=
  raw.magic = queryOnlyV2Magic ∧
  raw.version = multiRefV3Version ∧
  (raw.flags = multiRefV3GroupFlags ∨
    raw.flags = multiRefV3GroupWideFlags ∨
    raw.flags = multiRefV3DirectFlags ∨
    raw.flags = multiRefV3DirectWideFlags) ∧
  raw.rowCount = raw.rows.length

instance (raw : ContextualMultiRefV3Raw) : Decidable raw.Valid := by
  unfold Valid
  infer_instance

end ContextualMultiRefV3Raw

/-- Build a current contextual multi-ref v3 raw packet from raw rows. -/
def encodeContextualMultiRefV3Raw
    (factorCount : Nat) (rows : List ContextualRawQueryRow) :
    ContextualMultiRefV3Raw :=
  { magic := queryOnlyV2Magic
    version := multiRefV3Version
    flags := multiRefV3DirectFlags
    factorCount := factorCount
    rowCount := rows.length
    rows := rows }

/-- Decode a current contextual multi-ref v3 packet after header validation. -/
def decodeContextualMultiRefV3Raw?
    (raw : ContextualMultiRefV3Raw) : Option ContextualQueryPacket :=
  if _ : raw.Valid then some { rows := raw.rows.map ContextualRawQueryRow.toRow } else none

/-- The contextual multi-ref v3 encoder satisfies the current header contract. -/
theorem encodeContextualMultiRefV3Raw_valid
    (factorCount : Nat) (rows : List ContextualRawQueryRow) :
    (encodeContextualMultiRefV3Raw factorCount rows).Valid := by
  simp [encodeContextualMultiRefV3Raw, ContextualMultiRefV3Raw.Valid, multiRefV3DirectFlags]

/-- Contextual multi-ref v3 raw encode/decode round-trips at the validated packet layer. -/
@[simp]
theorem decode_encode_contextualMultiRefV3Raw
    (factorCount : Nat) (rows : List ContextualRawQueryRow) :
    decodeContextualMultiRefV3Raw?
      (encodeContextualMultiRefV3Raw factorCount rows) =
      some { rows := rows.map ContextualRawQueryRow.toRow } := by
  unfold decodeContextualMultiRefV3Raw?
  rw [dif_pos (encodeContextualMultiRefV3Raw_valid factorCount rows)]
  rfl

/-- Decoding a valid current contextual multi-ref v3 packet preserves its row count. -/
theorem decodeContextualMultiRefV3Raw_row_count
    (raw : ContextualMultiRefV3Raw) (packet : ContextualQueryPacket)
    (hvalid : raw.Valid)
    (hdecode : decodeContextualMultiRefV3Raw? raw = some packet) :
    packet.rows.length = raw.rowCount := by
  unfold decodeContextualMultiRefV3Raw? at hdecode
  rw [dif_pos hvalid] at hdecode
  cases hdecode
  simp [hvalid.2.2.2]

/-! ## Detailed current v3 factor-reference and multiplicity layout -/

/-- The per-factor payload before the row bindings in a current multi-ref v3 row. -/
inductive ContextualV3FactorPayload where
  | refGroups : List (List Nat) → ContextualV3FactorPayload
  | directMultiplicities : List Nat → ContextualV3FactorPayload
  deriving DecidableEq, Repr

/-- Product of direct v3 multiplicity factors. The empty factor vector has
neutral multiplicity one. -/
def natListProduct : List Nat → Nat
  | [] => 1
  | n :: ns => n * natListProduct ns

/-- A positive direct-multiplicity vector expands to a positive count. -/
theorem natListProduct_pos_of_all_pos :
    ∀ multiplicities : List Nat,
      (∀ multiplicity ∈ multiplicities, multiplicity > 0) →
      natListProduct multiplicities > 0
  | [], _ => by simp [natListProduct]
  | n :: ns, hpos => by
      have hn : n > 0 := hpos n (by simp)
      have hns : ∀ multiplicity ∈ ns, multiplicity > 0 := by
        intro multiplicity hmem
        exact hpos multiplicity (by simp [hmem])
      exact Nat.mul_pos hn (natListProduct_pos_of_all_pos ns hns)

namespace ContextualV3FactorPayload

/-- The direct-multiplicity flag family from the current v3 header. -/
def DirectFlags (flags : Nat) : Prop :=
  flags = multiRefV3DirectFlags ∨ flags = multiRefV3DirectWideFlags

/-- The per-factor reference-group flag family from the current v3 header. -/
def GroupFlags (flags : Nat) : Prop :=
  flags = multiRefV3GroupFlags ∨ flags = multiRefV3GroupWideFlags

/-- Current C parser validity for a v3 factor payload under the header mode. -/
def ValidFor (flags factorCount : Nat) : ContextualV3FactorPayload → Prop
  | .directMultiplicities multiplicities =>
      DirectFlags flags ∧
      multiplicities.length = factorCount ∧
      ∀ multiplicity ∈ multiplicities, multiplicity > 0
  | .refGroups groups =>
      GroupFlags flags ∧ groups.length = factorCount

/-- Direct v3 rows carry their logical output count explicitly as a product of
factor multiplicities. Ref-group rows need separate factor-table semantics. -/
def directWeight? : ContextualV3FactorPayload → Option Nat
  | .directMultiplicities multiplicities => some (natListProduct multiplicities)
  | .refGroups _ => none

instance (flags factorCount : Nat) (payload : ContextualV3FactorPayload) :
    Decidable (payload.ValidFor flags factorCount) := by
  cases payload <;> unfold ValidFor DirectFlags GroupFlags <;> infer_instance

end ContextualV3FactorPayload

/-- A detailed current v3 row: factor refs or direct multiplicities, followed by bindings. -/
structure ContextualDetailedMultiRefV3Row where
  factors : ContextualV3FactorPayload
  row : ContextualRawQueryRow

/-- Abstract semantics for current v3 ref-group factors. The concrete ABI can
instantiate this by explaining how a factor index and its reference group
determine one multiplicity factor. -/
structure ContextualV3RefGroupTable where
  weightOf : Nat → List Nat → Nat

namespace ContextualV3RefGroupTable

/-- Interpret ref-groups as multiplicity factors, preserving the factor index
so future ABI semantics can be factor-sensitive. -/
def weightsFrom (table : ContextualV3RefGroupTable) :
    Nat → List (List Nat) → List Nat
  | _, [] => []
  | factorIndex, group :: groups =>
      table.weightOf factorIndex group ::
        weightsFrom table (factorIndex + 1) groups

/-- The logical multiplicity represented by a row's ref-groups under an
abstract factor table. -/
def weightOfGroups (table : ContextualV3RefGroupTable)
    (groups : List (List Nat)) : Nat :=
  natListProduct (table.weightsFrom 0 groups)

/-- Interpreting ref-groups does not change their factor count. -/
theorem weightsFrom_length (table : ContextualV3RefGroupTable) :
    ∀ factorIndex groups, (table.weightsFrom factorIndex groups).length = groups.length
  | _, [] => rfl
  | factorIndex, _group :: groups => by
      simp [weightsFrom, weightsFrom_length table (factorIndex + 1) groups]

end ContextualV3RefGroupTable

namespace ContextualV3FactorPayload

/-- Interpret either direct multiplicities or ref-groups once an abstract
ref-group table is supplied. -/
def weightWithRefGroups (table : ContextualV3RefGroupTable) :
    ContextualV3FactorPayload → Nat
  | .directMultiplicities multiplicities => natListProduct multiplicities
  | .refGroups groups => table.weightOfGroups groups

end ContextualV3FactorPayload

namespace ContextualDetailedMultiRefV3Row

/-- Detailed row validity combines factor-mode validity and binding-count validity. -/
def Valid (flags factorCount : Nat) (row : ContextualDetailedMultiRefV3Row) : Prop :=
  row.factors.ValidFor flags factorCount ∧ row.row.BindingCountValid

instance (flags factorCount : Nat) (row : ContextualDetailedMultiRefV3Row) :
    Decidable (row.Valid flags factorCount) := by
  unfold Valid
  infer_instance

/-- Forget factor provenance and expose the decoded query row shape. -/
def toRow (row : ContextualDetailedMultiRefV3Row) : ContextualQueryRowPacket :=
  row.row.toRow

/-- Expand one detailed row when its current v3 factors are direct
multiplicities. -/
def expandDirect? (row : ContextualDetailedMultiRefV3Row) :
    Option (List ContextualQueryRowPacket) :=
  match row.factors.directWeight? with
  | some weight => some (List.replicate weight row.toRow)
  | none => none

/-- Expand a list of direct-multiplicity detailed rows, concatenating their
logical result-row repetitions. A ref-group row makes this direct-only
expansion fail. -/
def expandDirectRows? : List ContextualDetailedMultiRefV3Row →
    Option (List ContextualQueryRowPacket)
  | [] => some []
  | row :: rows =>
      match row.expandDirect?, expandDirectRows? rows with
      | some expanded, some rest => some (expanded ++ rest)
      | _, _ => none

/-- Expand one detailed row after supplying semantics for ref-groups. Direct
rows keep their existing direct product semantics. -/
def expandWithRefGroups (table : ContextualV3RefGroupTable)
    (row : ContextualDetailedMultiRefV3Row) :
    List ContextualQueryRowPacket :=
  List.replicate (row.factors.weightWithRefGroups table) row.toRow

/-- Expand detailed rows after supplying semantics for ref-groups. -/
def expandRowsWithRefGroups (table : ContextualV3RefGroupTable) :
    List ContextualDetailedMultiRefV3Row → List ContextualQueryRowPacket
  | [] => []
  | row :: rows => row.expandWithRefGroups table ++ expandRowsWithRefGroups table rows

/-- Direct current v3 multiplicities expand to repeated logical rows. -/
@[simp]
theorem expandDirect?_directMultiplicities
    (multiplicities : List Nat) (row : ContextualRawQueryRow) :
    ({ factors := .directMultiplicities multiplicities
       row := row } : ContextualDetailedMultiRefV3Row).expandDirect? =
      some (List.replicate (natListProduct multiplicities) row.toRow) := rfl

/-- Ref-group current v3 rows are not expanded by the direct-multiplicity rule. -/
@[simp]
theorem expandDirect?_refGroups
    (groups : List (List Nat)) (row : ContextualRawQueryRow) :
    ({ factors := .refGroups groups
       row := row } : ContextualDetailedMultiRefV3Row).expandDirect? = none := rfl

/-- With an abstract ref-group table, direct rows still expand by their direct
multiplicity product. -/
@[simp]
theorem expandWithRefGroups_directMultiplicities
    (table : ContextualV3RefGroupTable)
    (multiplicities : List Nat) (row : ContextualRawQueryRow) :
    ({ factors := .directMultiplicities multiplicities
       row := row } : ContextualDetailedMultiRefV3Row).expandWithRefGroups table =
      List.replicate (natListProduct multiplicities) row.toRow := rfl

/-- With an abstract ref-group table, ref-group rows expand by the table's
factor-sensitive group weight. -/
@[simp]
theorem expandWithRefGroups_refGroups
    (table : ContextualV3RefGroupTable)
    (groups : List (List Nat)) (row : ContextualRawQueryRow) :
    ({ factors := .refGroups groups
       row := row } : ContextualDetailedMultiRefV3Row).expandWithRefGroups table =
      List.replicate (table.weightOfGroups groups) row.toRow := rfl

/-- Counted direct expansion has length equal to the product of its direct
multiplicity factors. -/
theorem expandDirect?_length
    (row : ContextualDetailedMultiRefV3Row) (expanded : List ContextualQueryRowPacket)
    (h : row.expandDirect? = some expanded) :
    expanded.length =
      match row.factors.directWeight? with
      | some weight => weight
      | none => 0 := by
  unfold expandDirect? at h
  cases hweight : row.factors.directWeight? with
  | none =>
      rw [hweight] at h
      contradiction
  | some weight =>
      rw [hweight] at h
      cases h
      simp

end ContextualDetailedMultiRefV3Row

/-- Build a current direct-multiplicity v3 row from multiplicities and bindings. -/
def encodeContextualDirectV3Row
    (multiplicities : List Nat) (bindings : List ContextualRawBindingEntry) :
    ContextualDetailedMultiRefV3Row :=
  { factors := .directMultiplicities multiplicities
    row := encodeContextualRawQueryRow bindings }

/-- Build a current ref-group v3 row from factor reference groups and bindings. -/
def encodeContextualRefGroupV3Row
    (groups : List (List Nat)) (bindings : List ContextualRawBindingEntry) :
    ContextualDetailedMultiRefV3Row :=
  { factors := .refGroups groups
    row := encodeContextualRawQueryRow bindings }

/-- Encoding a direct-multiplicity v3 row exposes the counted expansion as a
list of repeated decoded rows. -/
@[simp]
theorem expand_encodeContextualDirectV3Row
    (multiplicities : List Nat) (bindings : List ContextualRawBindingEntry) :
    (encodeContextualDirectV3Row multiplicities bindings).expandDirect? =
      some (List.replicate (natListProduct multiplicities)
        (encodeContextualRawQueryRow bindings).toRow) := rfl

/-- Direct-multiplicity expansion is permutation-equivalent to the same
replicated decoded row list. This is the shape used later for row-result
equivalence theorems. -/
theorem expand_encodeContextualDirectV3Row_perm
    (multiplicities : List Nat) (bindings : List ContextualRawBindingEntry) :
    ∃ expanded,
      (encodeContextualDirectV3Row multiplicities bindings).expandDirect? = some expanded ∧
      expanded.Perm
        (List.replicate (natListProduct multiplicities)
          (encodeContextualRawQueryRow bindings).toRow) := by
  refine ⟨List.replicate (natListProduct multiplicities)
    (encodeContextualRawQueryRow bindings).toRow, ?_, ?_⟩
  · rfl
  · exact List.Perm.refl _

/-- Encode a list of direct-multiplicity v3 row specs. -/
def encodeContextualDirectV3Rows
    (rows : List (List Nat × List ContextualRawBindingEntry)) :
    List ContextualDetailedMultiRefV3Row :=
  rows.map fun row => encodeContextualDirectV3Row row.1 row.2

/-- Expected semantic expansion for a list of direct-multiplicity v3 row specs. -/
def expandContextualDirectV3RowSpecs
    : List (List Nat × List ContextualRawBindingEntry) →
      List ContextualQueryRowPacket
  | [] => []
  | row :: rows =>
      List.replicate (natListProduct row.1) (encodeContextualRawQueryRow row.2).toRow ++
      expandContextualDirectV3RowSpecs rows

/-- Direct-multiplicity v3 row-list expansion matches concatenated repeated
result-row semantics. -/
@[simp]
theorem expand_encodeContextualDirectV3Rows
    (rows : List (List Nat × List ContextualRawBindingEntry)) :
    ContextualDetailedMultiRefV3Row.expandDirectRows?
      (encodeContextualDirectV3Rows rows) =
      some (expandContextualDirectV3RowSpecs rows) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have htailDecode := ih
      change
        ContextualDetailedMultiRefV3Row.expandDirectRows?
          (List.map (fun row => encodeContextualDirectV3Row row.1 row.2) rows) =
          some (expandContextualDirectV3RowSpecs rows) at htailDecode
      simp [encodeContextualDirectV3Rows, expandContextualDirectV3RowSpecs,
        ContextualDetailedMultiRefV3Row.expandDirectRows?,
        expand_encodeContextualDirectV3Row row.1 row.2]
      rw [htailDecode]

/-- Encode a list of ref-group v3 row specs. -/
def encodeContextualRefGroupV3Rows
    (rows : List (List (List Nat) × List ContextualRawBindingEntry)) :
    List ContextualDetailedMultiRefV3Row :=
  rows.map fun row => encodeContextualRefGroupV3Row row.1 row.2

/-- Expected semantic expansion for a list of ref-group v3 row specs once an
abstract factor table is supplied. -/
def expandContextualRefGroupV3RowSpecs
    (table : ContextualV3RefGroupTable) :
    List (List (List Nat) × List ContextualRawBindingEntry) →
      List ContextualQueryRowPacket
  | [] => []
  | row :: rows =>
      List.replicate (table.weightOfGroups row.1)
        (encodeContextualRawQueryRow row.2).toRow ++
      expandContextualRefGroupV3RowSpecs table rows

/-- Ref-group v3 row-list expansion matches concatenated repeated result-row
semantics after an abstract factor table is supplied. -/
@[simp]
theorem expand_encodeContextualRefGroupV3Rows
    (table : ContextualV3RefGroupTable)
    (rows : List (List (List Nat) × List ContextualRawBindingEntry)) :
    ContextualDetailedMultiRefV3Row.expandRowsWithRefGroups table
      (encodeContextualRefGroupV3Rows rows) =
      expandContextualRefGroupV3RowSpecs table rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have htailDecode := ih
      change
        ContextualDetailedMultiRefV3Row.expandRowsWithRefGroups table
          (List.map (fun row => encodeContextualRefGroupV3Row row.1 row.2) rows) =
          expandContextualRefGroupV3RowSpecs table rows at htailDecode
      simp [encodeContextualRefGroupV3Row] at htailDecode
      simp [encodeContextualRefGroupV3Rows, expandContextualRefGroupV3RowSpecs,
        ContextualDetailedMultiRefV3Row.expandRowsWithRefGroups,
        encodeContextualRefGroupV3Row]
      rw [htailDecode]

/-- Direct-multiplicity row encoding satisfies the detailed row contract when
the multiplicity vector matches the factor count and contains no zero factor. -/
theorem encodeContextualDirectV3Row_valid
    (factorCount : Nat) (multiplicities : List Nat)
    (bindings : List ContextualRawBindingEntry)
    (hlen : multiplicities.length = factorCount)
    (hpos : ∀ multiplicity ∈ multiplicities, multiplicity > 0) :
    (encodeContextualDirectV3Row multiplicities bindings).Valid
      multiRefV3DirectFlags factorCount := by
  constructor
  · exact ⟨Or.inl rfl, hlen, hpos⟩
  · rfl

/-- Ref-group row encoding satisfies the detailed row contract when the group
vector matches the packet factor count. -/
theorem encodeContextualRefGroupV3Row_valid
    (factorCount : Nat) (groups : List (List Nat))
    (bindings : List ContextualRawBindingEntry)
    (hlen : groups.length = factorCount) :
    (encodeContextualRefGroupV3Row groups bindings).Valid
      multiRefV3GroupFlags factorCount := by
  simp [encodeContextualRefGroupV3Row, ContextualDetailedMultiRefV3Row.Valid,
    ContextualV3FactorPayload.ValidFor, ContextualV3FactorPayload.GroupFlags,
    encodeContextualRawQueryRow_binding_count, hlen]

/-- Detailed current multi-ref v3 packet layout, including factor payload rows. -/
structure ContextualDetailedMultiRefV3Raw where
  magic : Nat
  version : Nat
  flags : Nat
  factorCount : Nat
  rowCount : Nat
  rows : List ContextualDetailedMultiRefV3Row

namespace ContextualDetailedMultiRefV3Raw

/-- Header and row validity for the detailed current multi-ref v3 packet family. -/
def Valid (raw : ContextualDetailedMultiRefV3Raw) : Prop :=
  raw.magic = queryOnlyV2Magic ∧
  raw.version = multiRefV3Version ∧
  raw.rowCount = raw.rows.length ∧
  ∀ row ∈ raw.rows, row.Valid raw.flags raw.factorCount

instance (raw : ContextualDetailedMultiRefV3Raw) : Decidable raw.Valid := by
  unfold Valid
  infer_instance

end ContextualDetailedMultiRefV3Raw

/-- Decode a detailed current v3 packet after validating header, factor rows,
and binding counts. -/
def decodeContextualDetailedMultiRefV3Raw?
    (raw : ContextualDetailedMultiRefV3Raw) : Option ContextualQueryPacket :=
  if _ : raw.Valid then
    some { rows := raw.rows.map ContextualDetailedMultiRefV3Row.toRow }
  else
    none

/-- Build a detailed current v3 raw packet from already-formed detailed rows. -/
def encodeContextualDetailedMultiRefV3Raw
    (flags factorCount : Nat) (rows : List ContextualDetailedMultiRefV3Row) :
    ContextualDetailedMultiRefV3Raw :=
  { magic := queryOnlyV2Magic
    version := multiRefV3Version
    flags := flags
    factorCount := factorCount
    rowCount := rows.length
    rows := rows }

/-- The detailed current v3 encoder satisfies the packet contract when every row
satisfies the selected factor mode and binding-count contract. -/
theorem encodeContextualDetailedMultiRefV3Raw_valid
    (flags factorCount : Nat) (rows : List ContextualDetailedMultiRefV3Row)
    (hrows : ∀ row ∈ rows, row.Valid flags factorCount) :
    (encodeContextualDetailedMultiRefV3Raw flags factorCount rows).Valid := by
  exact ⟨rfl, rfl, rfl, hrows⟩

/-- Detailed current v3 raw encode/decode round-trips at the validated packet layer. -/
@[simp]
theorem decode_encode_contextualDetailedMultiRefV3Raw
    (flags factorCount : Nat) (rows : List ContextualDetailedMultiRefV3Row)
    (hrows : ∀ row ∈ rows, row.Valid flags factorCount) :
    decodeContextualDetailedMultiRefV3Raw?
      (encodeContextualDetailedMultiRefV3Raw flags factorCount rows) =
      some { rows := rows.map ContextualDetailedMultiRefV3Row.toRow } := by
  unfold decodeContextualDetailedMultiRefV3Raw?
  rw [dif_pos (encodeContextualDetailedMultiRefV3Raw_valid flags factorCount rows hrows)]
  rfl

/-- Decoding a valid detailed current v3 packet preserves its row count. -/
theorem decodeContextualDetailedMultiRefV3Raw_row_count
    (raw : ContextualDetailedMultiRefV3Raw) (packet : ContextualQueryPacket)
    (hvalid : raw.Valid)
    (hdecode : decodeContextualDetailedMultiRefV3Raw? raw = some packet) :
    packet.rows.length = raw.rowCount := by
  unfold decodeContextualDetailedMultiRefV3Raw? at hdecode
  rw [dif_pos hvalid] at hdecode
  cases hdecode
  simp [hvalid.2.2.1]

/-! ## Query-result row multiplicity contract -/

/-- A logical exact query-row space used to state result-row multiplicity
semantics independently from atom-candidate selection. -/
structure ContextualExactQueryRowSpace where
  rowSupport : List ContextualQueryRowPacket

/-- Query-row candidate selection after packet decoding and multiplicity
expansion. -/
structure ContextualQueryRowSelector where
  candidates : CAtom → List ContextualQueryRowPacket

/-- The row rematcher used after query-row candidate selection. It is kept
abstract here because row satisfaction depends on the concrete query semantics
at the implementation boundary. -/
structure ContextualQueryRowMatcher where
  isMatch : CAtom → ContextualQueryRowPacket → Bool

namespace ContextualQueryRowSelector

/-- Query-row selection is sound when every directly matching row appears among
the selected candidates. -/
def Sound (sel : ContextualQueryRowSelector) (matcher : ContextualQueryRowMatcher)
    (space : ContextualExactQueryRowSpace) : Prop :=
  ∀ query row,
    row ∈ space.rowSupport →
    matcher.isMatch query row = true →
    row ∈ sel.candidates query

/-- Query-row selection has no decoded rows outside the logical exact row
support. -/
def SubsetOf (sel : ContextualQueryRowSelector)
    (space : ContextualExactQueryRowSpace) : Prop :=
  ∀ query row, row ∈ sel.candidates query → row ∈ space.rowSupport

/-- Query-row selection preserves multiplicity when each candidate row list is a
permutation of the logical exact row support. -/
def MultiplicityExact (sel : ContextualQueryRowSelector)
    (space : ContextualExactQueryRowSpace) : Prop :=
  ∀ query, (sel.candidates query).Perm space.rowSupport

end ContextualQueryRowSelector

/-- Two-phase query-row semantics: expanded packet candidates followed by a row
rematcher. -/
def contextualTwoPhaseQueryRows (sel : ContextualQueryRowSelector)
    (matcher : ContextualQueryRowMatcher) (query : CAtom) :
    List ContextualQueryRowPacket :=
  (sel.candidates query).filter (fun row => matcher.isMatch query row)

/-- Direct query-row semantics over the exact logical result-row space. -/
def contextualDirectQueryRows (matcher : ContextualQueryRowMatcher)
    (space : ContextualExactQueryRowSpace) (query : CAtom) :
    List ContextualQueryRowPacket :=
  space.rowSupport.filter (fun row => matcher.isMatch query row)

/-- If query-row candidate selection is sound and subset-bounded, then
candidate selection plus row rematching preserves direct row membership. -/
theorem contextual_queryRow_twoPhase_mem_iff_direct
    (sel : ContextualQueryRowSelector) (matcher : ContextualQueryRowMatcher)
    (space : ContextualExactQueryRowSpace) (query : CAtom)
    (row : ContextualQueryRowPacket)
    (hsound : sel.Sound matcher space)
    (hsubset : sel.SubsetOf space) :
    row ∈ contextualTwoPhaseQueryRows sel matcher query ↔
      row ∈ contextualDirectQueryRows matcher space query := by
  constructor
  · intro h
    simp [contextualTwoPhaseQueryRows] at h
    simp [contextualDirectQueryRows, hsubset query row h.1, h.2]
  · intro h
    simp [contextualDirectQueryRows] at h
    simp [contextualTwoPhaseQueryRows, hsound query row h.1 h.2, h.2]

/-- If query-row candidate selection preserves multiplicity before rematching,
then two-phase query-row results are permutation-equivalent to direct query-row
results. This is the full list-level result-row contract after rematching. -/
theorem contextual_queryRow_twoPhase_perm_direct
    (sel : ContextualQueryRowSelector) (matcher : ContextualQueryRowMatcher)
    (space : ContextualExactQueryRowSpace) (query : CAtom)
    (hmult : sel.MultiplicityExact space) :
    (contextualTwoPhaseQueryRows sel matcher query).Perm
      (contextualDirectQueryRows matcher space query) := by
  exact (hmult query).filter (fun row => matcher.isMatch query row)

/-- Build a query-row selector from a fixed expanded result-row support. This is
the selector induced by a direct-multiplicity packet once structural query
matching has selected that packet. -/
def directExpandedQueryRowSelector
    (rows : List ContextualQueryRowPacket) : ContextualQueryRowSelector :=
  { candidates := fun _query => rows }

/-- Direct-multiplicity expansion induces exact query-row multiplicity for the
expanded row support. -/
theorem direct_expanded_query_row_selector_multiplicityExact
    (rows : List ContextualQueryRowPacket) :
    (directExpandedQueryRowSelector rows).MultiplicityExact
      { rowSupport := rows } := by
  intro _query
  exact List.Perm.refl rows

/-- If a direct-multiplicity v3 row list expands, the induced row selector
preserves the expanded query-row multiplicities exactly. -/
theorem direct_v3_expansion_implies_query_row_multiplicityExact
    (rows : List ContextualDetailedMultiRefV3Row)
    (expanded : List ContextualQueryRowPacket)
    (_hexpand : ContextualDetailedMultiRefV3Row.expandDirectRows? rows = some expanded) :
    (directExpandedQueryRowSelector expanded).MultiplicityExact
      { rowSupport := expanded } := by
  exact direct_expanded_query_row_selector_multiplicityExact expanded

/-- Encoded direct-multiplicity v3 row specs induce exact query-row
multiplicity for their semantic expansion. -/
theorem encoded_direct_v3_rows_imply_query_row_multiplicityExact
    (rows : List (List Nat × List ContextualRawBindingEntry)) :
    (directExpandedQueryRowSelector
      (expandContextualDirectV3RowSpecs rows)).MultiplicityExact
      { rowSupport := expandContextualDirectV3RowSpecs rows } := by
  exact direct_expanded_query_row_selector_multiplicityExact
    (expandContextualDirectV3RowSpecs rows)

/-- Encoded direct-multiplicity v3 rows give two-phase query-row results
permutation-equivalent to direct query-row results after any row rematcher. -/
theorem encoded_direct_v3_rows_twoPhase_perm_direct
    (rows : List (List Nat × List ContextualRawBindingEntry))
    (matcher : ContextualQueryRowMatcher) (query : CAtom) :
    (contextualTwoPhaseQueryRows
      (directExpandedQueryRowSelector (expandContextualDirectV3RowSpecs rows))
      matcher query).Perm
      (contextualDirectQueryRows matcher
        { rowSupport := expandContextualDirectV3RowSpecs rows } query) := by
  exact contextual_queryRow_twoPhase_perm_direct
    (directExpandedQueryRowSelector (expandContextualDirectV3RowSpecs rows))
    matcher { rowSupport := expandContextualDirectV3RowSpecs rows } query
    (encoded_direct_v3_rows_imply_query_row_multiplicityExact rows)

/-- Encoded ref-group v3 rows induce exact query-row multiplicity once an
abstract ref-group factor table is supplied. -/
theorem encoded_refGroup_v3_rows_imply_query_row_multiplicityExact
    (table : ContextualV3RefGroupTable)
    (rows : List (List (List Nat) × List ContextualRawBindingEntry)) :
    (directExpandedQueryRowSelector
      (expandContextualRefGroupV3RowSpecs table rows)).MultiplicityExact
      { rowSupport := expandContextualRefGroupV3RowSpecs table rows } := by
  exact direct_expanded_query_row_selector_multiplicityExact
    (expandContextualRefGroupV3RowSpecs table rows)

/-- Encoded ref-group v3 rows give two-phase query-row results
permutation-equivalent to direct query-row results after any row rematcher,
provided the abstract ref-group factor table is the intended interpretation. -/
theorem encoded_refGroup_v3_rows_twoPhase_perm_direct
    (table : ContextualV3RefGroupTable)
    (rows : List (List (List Nat) × List ContextualRawBindingEntry))
    (matcher : ContextualQueryRowMatcher) (query : CAtom) :
    (contextualTwoPhaseQueryRows
      (directExpandedQueryRowSelector (expandContextualRefGroupV3RowSpecs table rows))
      matcher query).Perm
      (contextualDirectQueryRows matcher
        { rowSupport := expandContextualRefGroupV3RowSpecs table rows } query) := by
  exact contextual_queryRow_twoPhase_perm_direct
    (directExpandedQueryRowSelector (expandContextualRefGroupV3RowSpecs table rows))
    matcher { rowSupport := expandContextualRefGroupV3RowSpecs table rows } query
    (encoded_refGroup_v3_rows_imply_query_row_multiplicityExact table rows)


end Mettapedia.OSLF.PathMap.VarIdBridge
