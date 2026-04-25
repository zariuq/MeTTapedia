import Mettapedia.OSLF.PathMap.VarIdBridge.Core

namespace Mettapedia.OSLF.PathMap.VarIdBridge

open Mettapedia.OSLF.PathMap.CanonicalUniverse
open Mettapedia.OSLF.PathMap.Trie

/-! ## Proposed origin-aware v4 opening contexts -/

/-- A v4 opening entry is either an exact stored variable or a reference back
to a query slot whose exact CeTTa identity is known on the C side. -/
inductive OpenVarRef where
  | exact : VarId → Spelling → OpenVarRef
  | querySlot : Slot → OpenVarRef
  deriving DecidableEq, Repr

/-- Proposed v4 opening context. This is distinct from current v2/v3
`value_env` provenance; it is the future exact/mixed opening interface. -/
structure OpeningContextV4 where
  refOf? : Slot → Option OpenVarRef

namespace OpeningContextV4

mutual
  /-- Exact-row coverage: every variable in this atom is opened from an
  `exact` entry. -/
  def CoversExactAtom (ctx : OpeningContextV4) (slotOf : VarId → Slot) :
      CAtom → Prop
    | .symbol _ => True
    | .var v => ∃ spelling, ctx.refOf? (slotOf v) = some (.exact v spelling)
    | .grounded _ => True
    | .expression es => CoversExactAtomList ctx slotOf es

  /-- Exact-row coverage for atom lists. -/
  def CoversExactAtomList (ctx : OpeningContextV4) (slotOf : VarId → Slot) :
      List CAtom → Prop
    | [] => True
    | a :: as => CoversExactAtom ctx slotOf a ∧ CoversExactAtomList ctx slotOf as
end

mutual
  /-- Decode a v4 structural atom through a value context and a query context.
  Exact entries recover stored variables; query-slot refs recover query vars. -/
  def decodeSlotAtomWithOrigin? (queryCtx : OpeningContext)
      (ctx : OpeningContextV4) : SlotAtom → Option CAtom
    | .symbol s => some (.symbol s)
    | .slot n =>
        match ctx.refOf? n with
        | some (.exact v _spelling) => some (.var v)
        | some (.querySlot q) =>
            match queryCtx.varOf? q with
            | some v => some (.var v)
            | none => none
        | none => none
    | .grounded g => some (.grounded g)
    | .expression es =>
        match decodeSlotAtomListWithOrigin? queryCtx ctx es with
        | some as => some (.expression as)
        | none => none

  /-- Decode a v4 structural atom list through origin-aware contexts. -/
  def decodeSlotAtomListWithOrigin? (queryCtx : OpeningContext)
      (ctx : OpeningContextV4) : List SlotAtom → Option (List CAtom)
    | [] => some []
    | a :: as =>
        match decodeSlotAtomWithOrigin? queryCtx ctx a,
          decodeSlotAtomListWithOrigin? queryCtx ctx as with
        | some a', some as' => some (a' :: as')
        | _, _ => none
end

mutual
  /-- Exact v4 context decoding recovers an encoded atom when the context
  covers the atom's support with exact entries. -/
  @[simp]
  theorem decode_origin_encode_catom_id_of_exact_covers
      (queryCtx : OpeningContext) (slotOf : VarId → Slot)
      (ctx : OpeningContextV4) :
      ∀ a, ctx.CoversExactAtom slotOf a →
        decodeSlotAtomWithOrigin? queryCtx ctx (encodeCAtomWith slotOf a) = some a
    | .symbol _, _ => rfl
    | .var v, hcover => by
        change ∃ spelling, ctx.refOf? (slotOf v) = some (OpenVarRef.exact v spelling) at hcover
        rcases hcover with ⟨spelling, href⟩
        simp [encodeCAtomWith, decodeSlotAtomWithOrigin?, href]
    | .grounded _, _ => rfl
    | .expression es, hcover => by
        change ctx.CoversExactAtomList slotOf es at hcover
        simp [encodeCAtomWith, decodeSlotAtomWithOrigin?,
          decode_origin_encode_catom_list_id_of_exact_covers queryCtx slotOf ctx es hcover]

  /-- Exact v4 context decoding recovers encoded atom lists under support-local
  exact coverage. -/
  @[simp]
  theorem decode_origin_encode_catom_list_id_of_exact_covers
      (queryCtx : OpeningContext) (slotOf : VarId → Slot)
      (ctx : OpeningContextV4) :
      ∀ as, ctx.CoversExactAtomList slotOf as →
        decodeSlotAtomListWithOrigin? queryCtx ctx (encodeCAtomListWith slotOf as) = some as
    | [], _ => rfl
    | a :: as, hcover => by
        change ctx.CoversExactAtom slotOf a ∧ ctx.CoversExactAtomList slotOf as at hcover
        simp [encodeCAtomListWith, decodeSlotAtomListWithOrigin?,
          decode_origin_encode_catom_id_of_exact_covers queryCtx slotOf ctx a hcover.1,
          decode_origin_encode_catom_list_id_of_exact_covers queryCtx slotOf ctx as hcover.2]
end

mutual
  /-- Mixed-value coverage: every variable in this value atom is opened either
  from an exact stored-variable entry or from a query-slot reference that the
  query context can open to the same `VarId`. -/
  def CoversMixedAtom (queryCtx : OpeningContext) (ctx : OpeningContextV4)
      (slotOf : VarId → Slot) : CAtom → Prop
    | .symbol _ => True
    | .var v =>
        (∃ spelling, ctx.refOf? (slotOf v) = some (.exact v spelling)) ∨
        (∃ querySlot,
          ctx.refOf? (slotOf v) = some (.querySlot querySlot) ∧
          queryCtx.varOf? querySlot = some v)
    | .grounded _ => True
    | .expression es => CoversMixedAtomList queryCtx ctx slotOf es

  /-- Mixed-value coverage for atom lists. -/
  def CoversMixedAtomList (queryCtx : OpeningContext) (ctx : OpeningContextV4)
      (slotOf : VarId → Slot) : List CAtom → Prop
    | [] => True
    | a :: as =>
        CoversMixedAtom queryCtx ctx slotOf a ∧
        CoversMixedAtomList queryCtx ctx slotOf as
end

mutual
  /-- Origin-aware v4 decoding recovers an encoded atom under support-local
  mixed coverage. This covers values that contain both exact stored variables
  and references back to query variables. -/
  @[simp]
  theorem decode_origin_encode_catom_id_of_mixed_covers
      (queryCtx : OpeningContext) (slotOf : VarId → Slot)
      (ctx : OpeningContextV4) :
      ∀ a, ctx.CoversMixedAtom queryCtx slotOf a →
        decodeSlotAtomWithOrigin? queryCtx ctx (encodeCAtomWith slotOf a) = some a
    | .symbol _, _ => rfl
    | .var v, hcover => by
        change
          (∃ spelling, ctx.refOf? (slotOf v) = some (OpenVarRef.exact v spelling)) ∨
          (∃ querySlot,
            ctx.refOf? (slotOf v) = some (OpenVarRef.querySlot querySlot) ∧
            queryCtx.varOf? querySlot = some v) at hcover
        rcases hcover with hexact | hquery
        · rcases hexact with ⟨spelling, href⟩
          simp [encodeCAtomWith, decodeSlotAtomWithOrigin?, href]
        · rcases hquery with ⟨querySlot, href, hquerySlot⟩
          simp [encodeCAtomWith, decodeSlotAtomWithOrigin?, href, hquerySlot]
    | .grounded _, _ => rfl
    | .expression es, hcover => by
        change ctx.CoversMixedAtomList queryCtx slotOf es at hcover
        simp [encodeCAtomWith, decodeSlotAtomWithOrigin?,
          decode_origin_encode_catom_list_id_of_mixed_covers queryCtx slotOf ctx es hcover]

  /-- Origin-aware v4 decoding recovers encoded atom lists under support-local
  mixed coverage. -/
  @[simp]
  theorem decode_origin_encode_catom_list_id_of_mixed_covers
      (queryCtx : OpeningContext) (slotOf : VarId → Slot)
      (ctx : OpeningContextV4) :
      ∀ as, ctx.CoversMixedAtomList queryCtx slotOf as →
        decodeSlotAtomListWithOrigin? queryCtx ctx (encodeCAtomListWith slotOf as) = some as
    | [], _ => rfl
    | a :: as, hcover => by
        change
          ctx.CoversMixedAtom queryCtx slotOf a ∧
          ctx.CoversMixedAtomList queryCtx slotOf as at hcover
        simp [encodeCAtomListWith, decodeSlotAtomListWithOrigin?,
          decode_origin_encode_catom_id_of_mixed_covers queryCtx slotOf ctx a hcover.1,
          decode_origin_encode_catom_list_id_of_mixed_covers queryCtx slotOf ctx as hcover.2]
end

/-- Positive mixed-provenance example: a value slot may refer back to a query
slot, and decoding uses the query context to recover the query-side `VarId`. -/
theorem query_slot_ref_decodes_from_query_context
    (queryCtx : OpeningContext) (ctx : OpeningContextV4)
    (valueSlot querySlot : Slot) (v : VarId)
    (href : ctx.refOf? valueSlot = some (.querySlot querySlot))
    (hquery : queryCtx.varOf? querySlot = some v) :
    decodeSlotAtomWithOrigin? queryCtx ctx (.slot valueSlot) = some (.var v) := by
  simp [decodeSlotAtomWithOrigin?, href, hquery]

/-- Negative exact-mode example: an unmentioned slot fails to decode instead
of silently synthesizing a fresh variable. -/
theorem missing_origin_context_entry_decodes_none
    (queryCtx : OpeningContext) (ctx : OpeningContextV4) (slot : Slot)
    (hmissing : ctx.refOf? slot = none) :
    decodeSlotAtomWithOrigin? queryCtx ctx (.slot slot) = none := by
  simp [decodeSlotAtomWithOrigin?, hmissing]

end OpeningContextV4

/-! ## Proposed v4 packet semantics over origin-aware context tables -/

/-- Proposed v4 context table shared by exact row packets and query packets. -/
structure OpeningContextTableV4 where
  contextOf? : ContextId → Option OpeningContextV4

namespace OpeningContextTableV4

/-- A v4 table entry covers the variables of one exact atom through exact refs. -/
def CoversExactAtomAt (table : OpeningContextTableV4) (context : ContextId)
    (slotOf : VarId → Slot) (a : CAtom) : Prop :=
  ∃ ctx, table.contextOf? context = some ctx ∧ ctx.CoversExactAtom slotOf a

/-- A v4 table entry covers the variables of one value atom through a mix of
exact refs and query-slot refs. -/
def CoversMixedAtomAt (table : OpeningContextTableV4) (context : ContextId)
    (queryCtx : OpeningContext) (slotOf : VarId → Slot) (a : CAtom) : Prop :=
  ∃ ctx, table.contextOf? context = some ctx ∧ ctx.CoversMixedAtom queryCtx slotOf a

end OpeningContextTableV4

/-- Proposed exact row packet v4: one structural row plus a packet-level context
reference and logical multiplicity. -/
structure ExactRowPacketV4 where
  context : ContextId
  multiplicity : Nat
  structural : SlotAtom

/-- Encode an exact row into the proposed v4 semantic packet layer. -/
def encodeExactRowPacketV4 (context : ContextId) (multiplicity : Nat)
    (slotOf : VarId → Slot) (a : CAtom) : ExactRowPacketV4 :=
  { context := context
    multiplicity := multiplicity
    structural := encodeCAtomWith slotOf a }

/-- Decode an exact row packet through its v4 table entry. The query context is
present because v4 value contexts can also be mixed in query packets; exact row
proofs below use only exact entries. -/
def decodeExactRowPacketV4? (queryCtx : OpeningContext)
    (table : OpeningContextTableV4) (packet : ExactRowPacketV4) :
    Option CAtom :=
  match table.contextOf? packet.context with
  | some ctx => OpeningContextV4.decodeSlotAtomWithOrigin? queryCtx ctx packet.structural
  | none => none

/-- Decode a v4 exact row and expand its logical multiplicity. -/
def decodeExpandExactRowPacketV4? (queryCtx : OpeningContext)
    (table : OpeningContextTableV4) (packet : ExactRowPacketV4) :
    Option (List CAtom) :=
  match decodeExactRowPacketV4? queryCtx table packet with
  | some atom => some (List.replicate packet.multiplicity atom)
  | none => none

/-- Decode and expand a list of v4 exact rows, concatenating each row's
logical multiplicity expansion. -/
def decodeExpandExactRowPacketListV4? (queryCtx : OpeningContext)
    (table : OpeningContextTableV4) :
    List ExactRowPacketV4 → Option (List CAtom)
  | [] => some []
  | packet :: packets =>
      match decodeExpandExactRowPacketV4? queryCtx table packet,
        decodeExpandExactRowPacketListV4? queryCtx table packets with
      | some expanded, some rest => some (expanded ++ rest)
      | _, _ => none

/-- Encode a list of proposed v4 exact rows sharing one opening context. -/
def encodeExactRowPacketListV4 (context : ContextId)
    (slotOf : VarId → Slot) (rows : List (Nat × CAtom)) :
    List ExactRowPacketV4 :=
  rows.map fun row => encodeExactRowPacketV4 context row.1 slotOf row.2

/-- Expected semantic expansion for a list of v4 exact row specs. -/
def expandExactRowSpecsV4 : List (Nat × CAtom) → List CAtom
  | [] => []
  | row :: rows => List.replicate row.1 row.2 ++ expandExactRowSpecsV4 rows

/-- Proposed exact-row v4 encode/decode round trip, assuming support-local exact
coverage in the referenced table context. -/
@[simp]
theorem decode_encode_exact_row_packet_v4_of_covers
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (context multiplicity : Nat) (slotOf : VarId → Slot) (a : CAtom)
    (hcover : table.CoversExactAtomAt context slotOf a) :
    decodeExactRowPacketV4? queryCtx table
      (encodeExactRowPacketV4 context multiplicity slotOf a) = some a := by
  rcases hcover with ⟨ctx, hctx, hcoverCtx⟩
  simp [decodeExactRowPacketV4?, encodeExactRowPacketV4, hctx,
    OpeningContextV4.decode_origin_encode_catom_id_of_exact_covers
      queryCtx slotOf ctx a hcoverCtx]

/-- Missing v4 row context is a hard exact-decoding failure. -/
theorem decode_exact_row_packet_v4_missing_context
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (packet : ExactRowPacketV4)
    (hmissing : table.contextOf? packet.context = none) :
    decodeExactRowPacketV4? queryCtx table packet = none := by
  simp [decodeExactRowPacketV4?, hmissing]

/-- Proposed v4 exact-row multiplicity expands to repeated exact atoms after
successful context-table decoding. -/
@[simp]
theorem decode_expand_encode_exact_row_packet_v4_of_covers
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (context multiplicity : Nat) (slotOf : VarId → Slot) (a : CAtom)
    (hcover : table.CoversExactAtomAt context slotOf a) :
    decodeExpandExactRowPacketV4? queryCtx table
      (encodeExactRowPacketV4 context multiplicity slotOf a) =
      some (List.replicate multiplicity a) := by
  unfold decodeExpandExactRowPacketV4?
  rw [decode_encode_exact_row_packet_v4_of_covers
    queryCtx table context multiplicity slotOf a hcover]
  rfl

/-- Missing v4 row context also prevents multiplicity expansion. -/
theorem decode_expand_exact_row_packet_v4_missing_context
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (packet : ExactRowPacketV4)
    (hmissing : table.contextOf? packet.context = none) :
    decodeExpandExactRowPacketV4? queryCtx table packet = none := by
  simp [decodeExpandExactRowPacketV4?,
    decode_exact_row_packet_v4_missing_context queryCtx table packet hmissing]

/-- Proposed v4 exact-row list expansion matches the concatenated repeated
row semantics. -/
@[simp]
theorem decode_expand_encode_exact_row_packet_list_v4_of_covers
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (context : ContextId) (slotOf : VarId → Slot)
    (rows : List (Nat × CAtom))
    (hcover : ∀ row ∈ rows, table.CoversExactAtomAt context slotOf row.2) :
    decodeExpandExactRowPacketListV4? queryCtx table
      (encodeExactRowPacketListV4 context slotOf rows) =
      some (expandExactRowSpecsV4 rows) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have hhead : table.CoversExactAtomAt context slotOf row.2 :=
        hcover row (by simp)
      have htail :
          ∀ row' ∈ rows, table.CoversExactAtomAt context slotOf row'.2 := by
        intro row' hmem
        exact hcover row' (by simp [hmem])
      have htailDecode := ih htail
      change
        decodeExpandExactRowPacketListV4? queryCtx table
          (List.map (fun row => encodeExactRowPacketV4 context row.1 slotOf row.2) rows) =
          some (expandExactRowSpecsV4 rows) at htailDecode
      simp [decodeExpandExactRowPacketListV4?, encodeExactRowPacketListV4,
        expandExactRowSpecsV4,
        decode_expand_encode_exact_row_packet_v4_of_covers
          queryCtx table context row.1 slotOf row.2 hhead]
      rw [htailDecode]

/-- Proposed v4 query binding: key is a query slot; value is structural bytes
opened through a v4 value context. -/
structure QueryBindingPacketV4 where
  querySlot : Slot
  valueContext : ContextId
  value : SlotAtom

/-- Decode one proposed v4 query binding. The key comes from the C-side query
context; the value context may contain exact stored refs or query-slot refs. -/
def decodeQueryBindingV4? (queryCtx : OpeningContext)
    (table : OpeningContextTableV4) (binding : QueryBindingPacketV4) :
    Option (VarId × CAtom) :=
  match queryCtx.varOf? binding.querySlot,
    table.contextOf? binding.valueContext with
  | some key, some valueCtx =>
      match OpeningContextV4.decodeSlotAtomWithOrigin? queryCtx valueCtx binding.value with
      | some value => some (key, value)
      | none => none
  | _, _ => none

/-- Encode an exact-valued v4 query binding. Mixed query-slot-valued bindings
use the same packet shape but a context containing `OpenVarRef.querySlot`
entries. -/
def encodeExactValueQueryBindingV4
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (key : VarId) (value : CAtom) : QueryBindingPacketV4 :=
  { querySlot := querySlotOf key
    valueContext := valueContext
    value := encodeCAtomWith valueSlotOf value }

/-- Proposed v4 query binding round trip for the exact-valued case. -/
@[simp]
theorem decode_encode_exact_value_query_binding_v4
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (key : VarId) (value : CAtom)
    (hquery : queryCtx.varOf? (querySlotOf key) = some key)
    (hvalue : table.CoversExactAtomAt valueContext valueSlotOf value) :
    decodeQueryBindingV4? queryCtx table
      (encodeExactValueQueryBindingV4 querySlotOf valueSlotOf valueContext key value) =
      some (key, value) := by
  rcases hvalue with ⟨valueCtx, hctx, hcoverCtx⟩
  simp [decodeQueryBindingV4?, encodeExactValueQueryBindingV4, hquery, hctx,
    OpeningContextV4.decode_origin_encode_catom_id_of_exact_covers
      queryCtx valueSlotOf valueCtx value hcoverCtx]

/-- Proposed v4 query binding round trip for values whose opening context may
mix exact stored variables with query-slot references. -/
@[simp]
theorem decode_encode_mixed_value_query_binding_v4
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (key : VarId) (value : CAtom)
    (hquery : queryCtx.varOf? (querySlotOf key) = some key)
    (hvalue : table.CoversMixedAtomAt valueContext queryCtx valueSlotOf value) :
    decodeQueryBindingV4? queryCtx table
      (encodeExactValueQueryBindingV4 querySlotOf valueSlotOf valueContext key value) =
      some (key, value) := by
  rcases hvalue with ⟨valueCtx, hctx, hcoverCtx⟩
  simp [decodeQueryBindingV4?, encodeExactValueQueryBindingV4, hquery, hctx,
    OpeningContextV4.decode_origin_encode_catom_id_of_mixed_covers
      queryCtx valueSlotOf valueCtx value hcoverCtx]

/-- Semantically neutral name for v4 query-binding encoding. Exact and mixed
values use the same packet shape; the value context determines how slots open. -/
def encodeQueryBindingV4
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (key : VarId) (value : CAtom) : QueryBindingPacketV4 :=
  encodeExactValueQueryBindingV4 querySlotOf valueSlotOf valueContext key value

/-- Proposed v4 query binding round trip using the neutral encoder name. -/
@[simp]
theorem decode_encode_query_binding_v4_of_mixed_covers
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (key : VarId) (value : CAtom)
    (hquery : queryCtx.varOf? (querySlotOf key) = some key)
    (hvalue : table.CoversMixedAtomAt valueContext queryCtx valueSlotOf value) :
    decodeQueryBindingV4? queryCtx table
      (encodeQueryBindingV4 querySlotOf valueSlotOf valueContext key value) =
      some (key, value) := by
  exact decode_encode_mixed_value_query_binding_v4
    queryCtx table querySlotOf valueSlotOf valueContext key value hquery hvalue

/-- Missing v4 value context makes query-binding decode fail rather than
silently synthesizing variables. -/
theorem decode_query_binding_v4_missing_value_context
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (binding : QueryBindingPacketV4)
    (hmissing : table.contextOf? binding.valueContext = none) :
    decodeQueryBindingV4? queryCtx table binding = none := by
  unfold decodeQueryBindingV4?
  cases queryCtx.varOf? binding.querySlot <;> simp [hmissing]

/-- A proposed v4 query result row is a list of variable bindings. -/
structure QueryRowPacketV4 where
  bindings : List QueryBindingPacketV4

/-- A proposed v4 query result packet is a list of result rows. -/
structure QueryPacketV4 where
  rows : List QueryRowPacketV4

/-- Decode a v4 binding list, failing the whole list if any binding lacks a
query variable or value opening context. -/
def decodeQueryBindingListV4? (queryCtx : OpeningContext)
    (table : OpeningContextTableV4) :
    List QueryBindingPacketV4 → Option (List (VarId × CAtom))
  | [] => some []
  | binding :: bindings =>
      match decodeQueryBindingV4? queryCtx table binding,
        decodeQueryBindingListV4? queryCtx table bindings with
      | some binding', some bindings' => some (binding' :: bindings')
      | _, _ => none

/-- Decode one proposed v4 query row with all-or-none exactness. -/
def decodeQueryRowV4? (queryCtx : OpeningContext)
    (table : OpeningContextTableV4) (row : QueryRowPacketV4) :
    Option (List (VarId × CAtom)) :=
  decodeQueryBindingListV4? queryCtx table row.bindings

/-- Decode a v4 row list, failing the whole packet if any row fails. -/
def decodeQueryRowListV4? (queryCtx : OpeningContext)
    (table : OpeningContextTableV4) :
    List QueryRowPacketV4 → Option (List (List (VarId × CAtom)))
  | [] => some []
  | row :: rows =>
      match decodeQueryRowV4? queryCtx table row,
        decodeQueryRowListV4? queryCtx table rows with
      | some row', some rows' => some (row' :: rows')
      | _, _ => none

/-- Decode a proposed v4 query packet with all-or-none exactness. -/
def decodeQueryPacketV4? (queryCtx : OpeningContext)
    (table : OpeningContextTableV4) (packet : QueryPacketV4) :
    Option (List (List (VarId × CAtom))) :=
  decodeQueryRowListV4? queryCtx table packet.rows

/-- Encode a proposed v4 query row from exact key/value pairs. -/
def encodeQueryRowV4
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (bindings : List (VarId × CAtom)) : QueryRowPacketV4 :=
  { bindings := bindings.map fun binding =>
      encodeQueryBindingV4 querySlotOf valueSlotOf valueContext binding.1 binding.2 }

/-- Encode a proposed v4 query packet from exact key/value rows. -/
def encodeQueryPacketV4
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (rows : List (List (VarId × CAtom))) : QueryPacketV4 :=
  { rows := rows.map fun row =>
      encodeQueryRowV4 querySlotOf valueSlotOf valueContext row }

/-- Mixed v4 binding-list round trip. -/
@[simp]
theorem decode_encode_query_binding_list_v4_of_mixed_covers
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (bindings : List (VarId × CAtom))
    (hquery : ∀ key, queryCtx.varOf? (querySlotOf key) = some key)
    (hvalues :
      ∀ binding ∈ bindings,
        table.CoversMixedAtomAt valueContext queryCtx valueSlotOf binding.2) :
    decodeQueryBindingListV4? queryCtx table
      (bindings.map fun binding =>
        encodeQueryBindingV4 querySlotOf valueSlotOf valueContext binding.1 binding.2) =
      some bindings := by
  induction bindings with
  | nil => rfl
  | cons binding bindings ih =>
      have hhead :
          table.CoversMixedAtomAt valueContext queryCtx valueSlotOf binding.2 :=
        hvalues binding (by simp)
      have htail :
          ∀ binding' ∈ bindings,
            table.CoversMixedAtomAt valueContext queryCtx valueSlotOf binding'.2 := by
        intro binding' hmem
        exact hvalues binding' (by simp [hmem])
      simp [decodeQueryBindingListV4?,
        decode_encode_query_binding_v4_of_mixed_covers
          queryCtx table querySlotOf valueSlotOf valueContext
          binding.1 binding.2 (hquery binding.1) hhead,
        ih htail]

/-- Mixed v4 query-row round trip. -/
@[simp]
theorem decode_encode_query_row_v4_of_mixed_covers
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (bindings : List (VarId × CAtom))
    (hquery : ∀ key, queryCtx.varOf? (querySlotOf key) = some key)
    (hvalues :
      ∀ binding ∈ bindings,
        table.CoversMixedAtomAt valueContext queryCtx valueSlotOf binding.2) :
    decodeQueryRowV4? queryCtx table
      (encodeQueryRowV4 querySlotOf valueSlotOf valueContext bindings) =
      some bindings := by
  exact decode_encode_query_binding_list_v4_of_mixed_covers
    queryCtx table querySlotOf valueSlotOf valueContext bindings hquery hvalues

/-- Mixed v4 row-list round trip. -/
@[simp]
theorem decode_encode_query_row_list_v4_of_mixed_covers
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (rows : List (List (VarId × CAtom)))
    (hquery : ∀ key, queryCtx.varOf? (querySlotOf key) = some key)
    (hvalues :
      ∀ row ∈ rows, ∀ binding ∈ row,
        table.CoversMixedAtomAt valueContext queryCtx valueSlotOf binding.2) :
    decodeQueryRowListV4? queryCtx table
      (rows.map fun row => encodeQueryRowV4 querySlotOf valueSlotOf valueContext row) =
      some rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have hrow :
          ∀ binding ∈ row,
            table.CoversMixedAtomAt valueContext queryCtx valueSlotOf binding.2 := by
        intro binding hmem
        exact hvalues row (by simp) binding hmem
      have htail :
          ∀ row' ∈ rows, ∀ binding ∈ row',
            table.CoversMixedAtomAt valueContext queryCtx valueSlotOf binding.2 := by
        intro row' hrow' binding hmem
        exact hvalues row' (by simp [hrow']) binding hmem
      simp [decodeQueryRowListV4?,
        decode_encode_query_row_v4_of_mixed_covers
          queryCtx table querySlotOf valueSlotOf valueContext row hquery hrow,
        ih htail]

/-- Mixed v4 query-packet round trip. -/
@[simp]
theorem decode_encode_query_packet_v4_of_mixed_covers
    (queryCtx : OpeningContext) (table : OpeningContextTableV4)
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (rows : List (List (VarId × CAtom)))
    (hquery : ∀ key, queryCtx.varOf? (querySlotOf key) = some key)
    (hvalues :
      ∀ row ∈ rows, ∀ binding ∈ row,
        table.CoversMixedAtomAt valueContext queryCtx valueSlotOf binding.2) :
    decodeQueryPacketV4? queryCtx table
      (encodeQueryPacketV4 querySlotOf valueSlotOf valueContext rows) =
      some rows := by
  exact decode_encode_query_row_list_v4_of_mixed_covers
    queryCtx table querySlotOf valueSlotOf valueContext rows hquery hvalues

/-! ## Proposed Rust/C v4 field-level packet layout -/

/-- Proposed v4 packet magic at the field level. The concrete byte ABI should
encode this in big-endian form, as current v2/v3 packets do. -/
def rawV4Magic : Nat := 0x43544252

/-- Proposed exact-row v4 packet version. -/
def rawExactRowsV4Version : Nat := 4

/-- Proposed query-binding v4 packet version. -/
def rawQueryBindingsV4Version : Nat := 4

def rawExactRowsV4Flags : Nat := 0
def rawQueryBindingsV4Flags : Nat := 0
def rawQueryBindingValueFlags : Nat := 0
def rawGroundValueFlagV4 : Nat := 0x01

/-- One proposed raw v4 context-table entry. This models the Rust/C fields
after endian decoding, not the byte parser itself. -/
structure RawOpeningContextEntryV4 where
  slot : Slot
  ref : OpenVarRef

/-- Lookup a slot in a raw v4 context entry list. First matching entry wins,
matching the natural single-pass decoder shape. -/
def rawV4RefOfEntries? : List RawOpeningContextEntryV4 → Slot → Option OpenVarRef
  | [], _ => none
  | entry :: entries, slot =>
      if entry.slot == slot then some entry.ref else rawV4RefOfEntries? entries slot

/-- One proposed raw v4 opening context with an explicit `context_id`. -/
structure RawOpeningContextV4 where
  context : ContextId
  entries : List RawOpeningContextEntryV4

/-- Interpret a raw v4 context entry list as an origin-aware opening context. -/
def RawOpeningContextV4.toContext (raw : RawOpeningContextV4) : OpeningContextV4 :=
  { refOf? := rawV4RefOfEntries? raw.entries }

/-- Lookup a context id in the proposed raw v4 context table. -/
def rawV4ContextOf? : List RawOpeningContextV4 → ContextId → Option OpeningContextV4
  | [], _ => none
  | ctx :: contexts, context =>
      if ctx.context == context then some ctx.toContext else rawV4ContextOf? contexts context

/-- Interpret a proposed raw v4 context table as the semantic v4 opening table. -/
def rawV4ContextTable (contexts : List RawOpeningContextV4) : OpeningContextTableV4 :=
  { contextOf? := rawV4ContextOf? contexts }

/-- Field-level proposed exact-row v4 packet. -/
structure RawExactRowsV4 where
  magic : Nat
  version : Nat
  flags : Nat
  rowCount : Nat
  contextCount : Nat
  contexts : List RawOpeningContextV4
  rows : List ExactRowPacketV4

namespace RawExactRowsV4

/-- Header/count validity for proposed exact-row v4 packets. -/
def Valid (raw : RawExactRowsV4) : Prop :=
  raw.magic = rawV4Magic ∧
  raw.version = rawExactRowsV4Version ∧
  raw.flags = rawExactRowsV4Flags ∧
  raw.rowCount = raw.rows.length ∧
  raw.contextCount = raw.contexts.length

instance (raw : RawExactRowsV4) : Decidable raw.Valid := by
  unfold Valid
  infer_instance

end RawExactRowsV4

/-- Build a proposed field-level exact-row v4 packet from semantic rows. -/
def encodeRawExactRowsV4
    (contexts : List RawOpeningContextV4) (rows : List ExactRowPacketV4) :
    RawExactRowsV4 :=
  { magic := rawV4Magic
    version := rawExactRowsV4Version
    flags := rawExactRowsV4Flags
    rowCount := rows.length
    contextCount := contexts.length
    contexts := contexts
    rows := rows }

/-- Decode a proposed field-level exact-row v4 packet through its context table. -/
def decodeRawExactRowsV4? (queryCtx : OpeningContext) (raw : RawExactRowsV4) :
    Option (List CAtom) :=
  if _ : raw.Valid then
    decodeExpandExactRowPacketListV4? queryCtx (rawV4ContextTable raw.contexts) raw.rows
  else
    none

/-- Invalid proposed exact-row v4 packets are rejected before semantic decoding. -/
theorem decodeRawExactRowsV4?_of_invalid
    (queryCtx : OpeningContext) (raw : RawExactRowsV4)
    (hinvalid : ¬ raw.Valid) :
    decodeRawExactRowsV4? queryCtx raw = none := by
  unfold decodeRawExactRowsV4?
  rw [dif_neg hinvalid]

/-- The proposed exact-row v4 field-level encoder satisfies header/count validity. -/
theorem encodeRawExactRowsV4_valid
    (contexts : List RawOpeningContextV4) (rows : List ExactRowPacketV4) :
    (encodeRawExactRowsV4 contexts rows).Valid := by
  simp [encodeRawExactRowsV4, RawExactRowsV4.Valid]

/-- Proposed exact-row v4 field-level packets decode according to the semantic
exact-row packet theorem. -/
@[simp]
theorem decode_encode_raw_exact_rows_v4_of_covers
    (queryCtx : OpeningContext) (contexts : List RawOpeningContextV4)
    (context : ContextId) (slotOf : VarId → Slot)
    (rows : List (Nat × CAtom))
    (hcover :
      ∀ row ∈ rows,
        (rawV4ContextTable contexts).CoversExactAtomAt context slotOf row.2) :
    decodeRawExactRowsV4? queryCtx
      (encodeRawExactRowsV4 contexts
        (encodeExactRowPacketListV4 context slotOf rows)) =
      some (expandExactRowSpecsV4 rows) := by
  unfold decodeRawExactRowsV4?
  rw [dif_pos (encodeRawExactRowsV4_valid contexts
    (encodeExactRowPacketListV4 context slotOf rows))]
  exact decode_expand_encode_exact_row_packet_list_v4_of_covers
    queryCtx (rawV4ContextTable contexts) context slotOf rows hcover

/-- One proposed raw v4 query binding. `valueFlags` is retained as a raw
implementation field; the semantic v4 decoder opens `value` through
`valueContext`. -/
structure RawQueryBindingV4 where
  querySlot : Slot
  valueContext : ContextId
  valueFlags : Nat
  value : SlotAtom

namespace RawQueryBindingV4

/-- The current contextual query ABI reserves `valueFlags`; accepted packets
must set it to zero. -/
def ValueFlagsValid (raw : RawQueryBindingV4) : Prop :=
  raw.valueFlags = rawQueryBindingValueFlags

instance (raw : RawQueryBindingV4) : Decidable raw.ValueFlagsValid := by
  unfold ValueFlagsValid
  infer_instance

end RawQueryBindingV4

/-- Interpret a raw v4 query binding as the semantic binding packet. -/
def RawQueryBindingV4.toBinding (raw : RawQueryBindingV4) : QueryBindingPacketV4 :=
  { querySlot := raw.querySlot
    valueContext := raw.valueContext
    value := raw.value }

/-- Encode a semantic v4 query binding into the proposed raw field layout. -/
def encodeRawQueryBindingV4 (valueFlags : Nat)
    (binding : QueryBindingPacketV4) : RawQueryBindingV4 :=
  { querySlot := binding.querySlot
    valueContext := binding.valueContext
    valueFlags := valueFlags
    value := binding.value }

@[simp]
theorem rawQueryBindingV4_toBinding_encode
    (valueFlags : Nat) (binding : QueryBindingPacketV4) :
    (encodeRawQueryBindingV4 valueFlags binding).toBinding = binding := by
  cases binding
  rfl

/-- One proposed raw v4 query row. -/
structure RawQueryRowV4 where
  bindingCount : Nat
  bindings : List RawQueryBindingV4

namespace RawQueryRowV4

/-- The parsed raw binding count agrees with the number of raw entries. -/
def BindingCountValid (row : RawQueryRowV4) : Prop :=
  row.bindingCount = row.bindings.length

/-- Every raw query binding uses the currently accepted reserved flag value. -/
def BindingFlagsValid (row : RawQueryRowV4) : Prop :=
  ∀ binding ∈ row.bindings, binding.ValueFlagsValid

/-- Field validity for one raw query row. -/
def Valid (row : RawQueryRowV4) : Prop :=
  row.BindingCountValid ∧ row.BindingFlagsValid

instance (row : RawQueryRowV4) : Decidable row.Valid := by
  unfold Valid BindingCountValid BindingFlagsValid RawQueryBindingV4.ValueFlagsValid
  infer_instance

end RawQueryRowV4

/-- Interpret one proposed raw v4 query row as a semantic v4 row. -/
def RawQueryRowV4.toRow (raw : RawQueryRowV4) : QueryRowPacketV4 :=
  { bindings := raw.bindings.map RawQueryBindingV4.toBinding }

/-- Encode a semantic v4 query row into the proposed raw field layout. -/
def encodeRawQueryRowV4 (valueFlags : Nat) (row : QueryRowPacketV4) : RawQueryRowV4 :=
  { bindingCount := row.bindings.length
    bindings := row.bindings.map (encodeRawQueryBindingV4 valueFlags) }

@[simp]
theorem rawQueryRowV4_toRow_encode
    (valueFlags : Nat) (row : QueryRowPacketV4) :
    (encodeRawQueryRowV4 valueFlags row).toRow = row := by
  cases row
  simp [encodeRawQueryRowV4, RawQueryRowV4.toRow, Function.comp_def]

/-- Encoding a raw query row records the binding count exactly. -/
theorem encodeRawQueryRowV4_binding_count
    (valueFlags : Nat) (row : QueryRowPacketV4) :
    (encodeRawQueryRowV4 valueFlags row).BindingCountValid := by
  simp [encodeRawQueryRowV4, RawQueryRowV4.BindingCountValid]

/-- Encoding a raw query row is valid when the reserved binding flags use the
current accepted value. -/
theorem encodeRawQueryRowV4_valid
    (valueFlags : Nat) (row : QueryRowPacketV4)
    (hflags : valueFlags = rawQueryBindingValueFlags) :
    (encodeRawQueryRowV4 valueFlags row).Valid := by
  constructor
  · simp [encodeRawQueryRowV4, RawQueryRowV4.BindingCountValid]
  · intro binding hmem
    rcases List.mem_map.mp hmem with ⟨source, _hsource, hbinding⟩
    subst binding
    simp [encodeRawQueryBindingV4, RawQueryBindingV4.ValueFlagsValid, hflags]

/-- Field-level proposed query-binding v4 packet. -/
structure RawQueryPacketV4 where
  magic : Nat
  version : Nat
  flags : Nat
  rowCount : Nat
  contextCount : Nat
  contexts : List RawOpeningContextV4
  rows : List RawQueryRowV4

namespace RawQueryPacketV4

/-- Header/count validity for proposed query-binding v4 packets. -/
def Valid (raw : RawQueryPacketV4) : Prop :=
  raw.magic = rawV4Magic ∧
  raw.version = rawQueryBindingsV4Version ∧
  raw.flags = rawQueryBindingsV4Flags ∧
  raw.rowCount = raw.rows.length ∧
  raw.contextCount = raw.contexts.length ∧
  ∀ row ∈ raw.rows, row.Valid

instance (raw : RawQueryPacketV4) : Decidable raw.Valid := by
  unfold Valid
  infer_instance

end RawQueryPacketV4

/-- Interpret a proposed raw v4 query packet as a semantic v4 query packet. -/
def RawQueryPacketV4.toPacket (raw : RawQueryPacketV4) : QueryPacketV4 :=
  { rows := raw.rows.map RawQueryRowV4.toRow }

/-- Build a proposed field-level query-binding v4 packet from semantic rows. -/
def encodeRawQueryPacketV4
    (contexts : List RawOpeningContextV4) (valueFlags : Nat) (packet : QueryPacketV4) :
    RawQueryPacketV4 :=
  { magic := rawV4Magic
    version := rawQueryBindingsV4Version
    flags := rawQueryBindingsV4Flags
    rowCount := packet.rows.length
    contextCount := contexts.length
    contexts := contexts
    rows := packet.rows.map (encodeRawQueryRowV4 valueFlags) }

@[simp]
theorem rawQueryPacketV4_toPacket_encode
    (contexts : List RawOpeningContextV4) (valueFlags : Nat)
    (packet : QueryPacketV4) :
    (encodeRawQueryPacketV4 contexts valueFlags packet).toPacket = packet := by
  cases packet
  simp [encodeRawQueryPacketV4, RawQueryPacketV4.toPacket, Function.comp_def]

/-- Decode a proposed field-level query-binding v4 packet through its context table. -/
def decodeRawQueryPacketV4? (queryCtx : OpeningContext) (raw : RawQueryPacketV4) :
    Option (List (List (VarId × CAtom))) :=
  if _ : raw.Valid then
    decodeQueryPacketV4? queryCtx (rawV4ContextTable raw.contexts) raw.toPacket
  else
    none

/-- Invalid proposed query-binding v4 packets are rejected before semantic decoding. -/
theorem decodeRawQueryPacketV4?_of_invalid
    (queryCtx : OpeningContext) (raw : RawQueryPacketV4)
    (hinvalid : ¬ raw.Valid) :
    decodeRawQueryPacketV4? queryCtx raw = none := by
  unfold decodeRawQueryPacketV4?
  rw [dif_neg hinvalid]

/-- The proposed query-binding v4 field-level encoder satisfies header/count validity. -/
theorem encodeRawQueryPacketV4_valid
    (contexts : List RawOpeningContextV4) (valueFlags : Nat) (packet : QueryPacketV4)
    (hflags : valueFlags = rawQueryBindingValueFlags) :
    (encodeRawQueryPacketV4 contexts valueFlags packet).Valid := by
  unfold encodeRawQueryPacketV4 RawQueryPacketV4.Valid
  simp [encodeRawQueryRowV4_valid, hflags]

/-- Proposed query-binding v4 field-level packets decode according to the
semantic mixed query-packet theorem. -/
@[simp]
theorem decode_encode_raw_query_packet_v4_of_mixed_covers
    (queryCtx : OpeningContext) (contexts : List RawOpeningContextV4)
    (valueFlags : Nat)
    (hflags : valueFlags = rawQueryBindingValueFlags)
    (querySlotOf valueSlotOf : VarId → Slot) (valueContext : ContextId)
    (rows : List (List (VarId × CAtom)))
    (hquery : ∀ key, queryCtx.varOf? (querySlotOf key) = some key)
    (hvalues :
      ∀ row ∈ rows, ∀ binding ∈ row,
        (rawV4ContextTable contexts).CoversMixedAtomAt
          valueContext queryCtx valueSlotOf binding.2) :
    decodeRawQueryPacketV4? queryCtx
      (encodeRawQueryPacketV4 contexts valueFlags
        (encodeQueryPacketV4 querySlotOf valueSlotOf valueContext rows)) =
      some rows := by
  unfold decodeRawQueryPacketV4?
  rw [dif_pos (encodeRawQueryPacketV4_valid contexts valueFlags
    (encodeQueryPacketV4 querySlotOf valueSlotOf valueContext rows) hflags)]
  simp
  exact decode_encode_query_packet_v4_of_mixed_covers
    queryCtx (rawV4ContextTable contexts) querySlotOf valueSlotOf valueContext
    rows hquery hvalues


end Mettapedia.OSLF.PathMap.VarIdBridge
