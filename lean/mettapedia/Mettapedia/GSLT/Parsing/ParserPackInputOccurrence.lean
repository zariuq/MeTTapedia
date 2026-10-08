import Mettapedia.GSLT.Parsing.ParserPackSliceCertificate
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
import Init.Data.String.Basic

/-!
# Byte and scalar occurrences for ParserPack evidence

The neutral forest carries scalar values and byte offsets independently. This
module checks both against the exact source bytes with Lean's existing UTF-8
codec, and checks a fragment witness's embedding before reusing the established
scalar-slice certificate transport. The fragment and global EOF remain distinct.

Ordered inclusion pieces copy bytes from physical source-file entries. Their
checker preserves occurrence order, multiplicity and explicit seams. It does
not authorize imports, canonical paths, cycles or omissions from a source file;
those remain obligations of the source-inclusion execution which supplies the
pieces. Parser completeness and source-production agreement are also separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ParserPackInputOccurrence

open ClassAwareParserPackCertificate
open ClassAwareParserPackCorrespondence
open ParserPackSelectedValue
open ParserPackSliceCertificate
open ParserProfileSemantics (ParserProfileLayer)
open PresentationExprSemantics (CST)

structure InputView where
  bytes : List UInt8
  codepoints : List Nat
  byteOffsets : List Nat
  deriving DecidableEq, Repr

noncomputable def utf8Bytes (characters : List Char) : List UInt8 :=
  characters.utf8Encode.data.toList

/-- Linear prefix scan, including both physical endpoints. -/
def byteOffsetsFrom (base : Nat) : List Char → List Nat
  | [] => [base]
  | character :: rest => base :: byteOffsetsFrom (base + character.utf8Size) rest

def byteOffsets (characters : List Char) : List Nat := byteOffsetsFrom 0 characters

def InputAgreement (view : InputView) (characters : List Char) : Prop :=
  view.bytes = utf8Bytes characters ∧
    view.codepoints = characters.map Char.toNat ∧
    view.byteOffsets = byteOffsets characters

/-- Decode the supplied bytes, then compare both independently supplied native
tables. An invalid encoding or a changed scalar/offset row is refused. -/
def checkedInput? (view : InputView) : Option (List Char) := do
  let characters ← (ByteArray.mk view.bytes.toArray).utf8Decode?
  let decoded := characters.toList
  if view.codepoints == decoded.map Char.toNat && view.byteOffsets == byteOffsets decoded
    then some decoded else none

private theorem decoded_reencodes {bytes : List UInt8} {characters : Array Char}
    (decoded : (ByteArray.mk bytes.toArray).utf8Decode? = some characters) :
    bytes = utf8Bytes characters.toList := by
  have complete := ByteArray.utf8Encode_get_utf8Decode?
    (b := ByteArray.mk bytes.toArray) (h := by simp [decoded])
  simp only [decoded, Option.get_some] at complete
  have same := congrArg (fun value : ByteArray => value.data.toList) complete
  simpa [utf8Bytes] using same.symm

theorem checkedInput?_sound {view : InputView} {characters : List Char}
    (accepted : checkedInput? view = some characters) :
    InputAgreement view characters := by
  unfold checkedInput? at accepted
  cases decoded : (ByteArray.mk view.bytes.toArray).utf8Decode? with
  | none => simp [decoded] at accepted
  | some decodedCharacters =>
      simp only [decoded, Option.bind_eq_bind, Option.bind_some] at accepted
      split at accepted
      · rename_i exactTables
        have same : decodedCharacters.toList = characters := Option.some.inj accepted
        subst characters
        rcases Bool.and_eq_true_iff.mp exactTables with ⟨scalarExact, offsetExact⟩
        exact ⟨decoded_reencodes decoded, by simpa using scalarExact, by simpa using offsetExact⟩
      · contradiction

theorem checkedInput?_complete {view : InputView} {characters : List Char}
    (agreement : InputAgreement view characters) :
    checkedInput? view = some characters := by
  rcases agreement with ⟨bytesExact, scalarExact, offsetExact⟩
  have reconstructed : ByteArray.mk (utf8Bytes characters).toArray = characters.utf8Encode := by
    simp only [utf8Bytes, Array.toArray_toList]
  simp only [checkedInput?, bytesExact, reconstructed, List.utf8Decode?_utf8Encode,
    Option.bind_eq_bind, Option.bind_some, scalarExact, offsetExact,
    beq_self_eq_true, Bool.and_self, ↓reduceIte]

theorem checkedInput?_iff (view : InputView) (characters : List Char) :
    checkedInput? view = some characters ↔ InputAgreement view characters :=
  ⟨checkedInput?_sound, checkedInput?_complete⟩

def inputValid (view : InputView) : Bool := (checkedInput? view).isSome

theorem inputValid_iff (view : InputView) :
    inputValid view = true ↔ ∃ characters, InputAgreement view characters := by
  simp only [inputValid, Option.isSome_iff_exists]
  constructor
  · rintro ⟨characters, accepted⟩
    exact ⟨characters, checkedInput?_sound accepted⟩
  · rintro ⟨characters, agreement⟩
    exact ⟨characters, checkedInput?_complete agreement⟩

@[simp] theorem byteOffsetsFrom_length (base : Nat) (characters : List Char) :
    (byteOffsetsFrom base characters).length = characters.length + 1 := by
  induction characters generalizing base with
  | nil => simp [byteOffsetsFrom]
  | cons character rest inductionHypothesis => simp [byteOffsetsFrom, inductionHypothesis]

private theorem utf8_size_cons (character : Char) (rest : List Char) :
    (character :: rest).utf8Encode.size = character.utf8Size + rest.utf8Encode.size := by
  rw [List.utf8Encode_cons, ByteArray.size_append, List.utf8Encode_singleton,
    List.size_toByteArray, String.length_utf8EncodeChar]

theorem byteOffsetsFrom_lookup (base : Nat) (characters : List Char) (cursor : Nat)
    (bounded : cursor ≤ characters.length) :
    (byteOffsetsFrom base characters)[cursor]? =
      some (base + (characters.take cursor).utf8Encode.size) := by
  induction characters generalizing base cursor with
  | nil =>
      have cursorZero : cursor = 0 := by simpa using bounded
      subst cursor
      simp [byteOffsetsFrom]
  | cons character rest inductionHypothesis =>
      cases cursor with
      | zero => simp [byteOffsetsFrom]
      | succ cursor =>
          have restBounded : cursor ≤ rest.length := by simpa using bounded
          simpa [byteOffsetsFrom, utf8_size_cons, Nat.add_assoc] using
            inductionHypothesis (base + character.utf8Size) cursor restBounded

theorem InputAgreement.offset_length {view : InputView} {characters : List Char}
    (agreement : InputAgreement view characters) :
    view.byteOffsets.length = view.codepoints.length + 1 := by
  rw [agreement.2.1, agreement.2.2]
  simp [byteOffsets]

theorem InputAgreement.offset_lookup {view : InputView} {characters : List Char}
    (agreement : InputAgreement view characters) {cursor : Nat}
    (bounded : cursor ≤ view.codepoints.length) :
    view.byteOffsets[cursor]? = some (characters.take cursor).utf8Encode.size := by
  have charsBounded : cursor ≤ characters.length := by simpa [agreement.2.1] using bounded
  simpa [agreement.2.2, byteOffsets] using byteOffsetsFrom_lookup 0 characters cursor charsBounded

theorem InputAgreement.offset_zero {view : InputView} {characters : List Char}
    (agreement : InputAgreement view characters) : view.byteOffsets[0]? = some 0 := by
  simpa using agreement.offset_lookup (Nat.zero_le _)

theorem InputAgreement.offset_end {view : InputView} {characters : List Char}
    (agreement : InputAgreement view characters) :
    view.byteOffsets[view.codepoints.length]? = some view.bytes.length := by
  have endpoint := agreement.offset_lookup (Nat.le_refl view.codepoints.length)
  simpa [agreement.1, agreement.2.1, utf8Bytes] using endpoint

/-- Every decoded scalar occupies a positive number of source bytes. -/
theorem utf8_prefix_strict (characters : List Char) {left right : Nat}
    (ordered : left < right) (bounded : right ≤ characters.length) :
    (characters.take left).utf8Encode.size < (characters.take right).utf8Encode.size := by
  induction characters generalizing left right with
  | nil => simp only [List.length_nil] at bounded; omega
  | cons character rest inductionHypothesis =>
      cases left with
      | zero =>
          cases right with
          | zero => omega
          | succ right =>
              have positive := character.utf8Size_pos
              simp only [List.take_zero, List.utf8Encode_nil, ByteArray.size_empty,
                List.take_succ_cons, utf8_size_cons]
              omega
      | succ left =>
          cases right with
          | zero => omega
          | succ right =>
              have restOrdered : left < right := by omega
              have restBounded : right ≤ rest.length := by simpa using bounded
              have strict := inductionHypothesis restOrdered restBounded
              simpa only [List.take_succ_cons, utf8_size_cons, Nat.add_lt_add_iff_left] using strict

theorem InputAgreement.offset_injective {view : InputView} {characters : List Char}
    (agreement : InputAgreement view characters) {left right offset : Nat}
    (leftBounded : left ≤ view.codepoints.length) (rightBounded : right ≤ view.codepoints.length)
    (leftAt : view.byteOffsets[left]? = some offset)
    (rightAt : view.byteOffsets[right]? = some offset) : left = right := by
  have leftExact := agreement.offset_lookup leftBounded
  have rightExact := agreement.offset_lookup rightBounded
  have samePrefix : (characters.take left).utf8Encode.size = (characters.take right).utf8Encode.size := by
    rw [leftAt] at leftExact
    rw [rightAt] at rightExact
    exact (Option.some.inj leftExact).symm.trans (Option.some.inj rightExact)
  have leftCharsBounded : left ≤ characters.length := by simpa [agreement.2.1] using leftBounded
  have rightCharsBounded : right ≤ characters.length := by simpa [agreement.2.1] using rightBounded
  by_cases before : left < right
  · have strict := utf8_prefix_strict characters before rightCharsBounded
    omega
  · by_cases after : right < left
    · have strict := utf8_prefix_strict characters after leftCharsBounded
      omega
    · omega

/-- Physical byte EOF and scalar EOF coincide only at the full input's end. -/
theorem InputAgreement.eof_iff {view : InputView} {characters : List Char}
    (agreement : InputAgreement view characters) {cursor offset : Nat}
    (bounded : cursor ≤ view.codepoints.length)
    (atOffset : view.byteOffsets[cursor]? = some offset) :
    cursor = view.codepoints.length ↔ offset = view.bytes.length := by
  constructor
  · intro endpoint
    rw [endpoint, agreement.offset_end] at atOffset
    exact (Option.some.inj atOffset).symm
  · intro endpoint
    rw [endpoint] at atOffset
    exact agreement.offset_injective bounded (Nat.le_refl _) atOffset agreement.offset_end

structure Occurrence where
  scalarStart : Nat
  scalarStop : Nat
  byteStart : Nat
  byteStop : Nat
  deriving DecidableEq, Repr

/-- Exact fragment embedding data, with no parser or production authority. -/
structure CheckedOccurrence (full fragment : InputView) (occurrence : Occurrence) : Type where
  fullCharacters : List Char
  localCharacters : List Char
  fullAgreement : InputAgreement full fullCharacters
  localAgreement : InputAgreement fragment localCharacters
  ordered : occurrence.scalarStart ≤ occurrence.scalarStop
  bounded : occurrence.scalarStop ≤ full.codepoints.length
  bytesOrdered : occurrence.byteStart ≤ occurrence.byteStop
  bytesBounded : occurrence.byteStop ≤ full.bytes.length
  leftOffset : full.byteOffsets[occurrence.scalarStart]? = some occurrence.byteStart
  rightOffset : full.byteOffsets[occurrence.scalarStop]? = some occurrence.byteStop
  scalarExact : fragment.codepoints = full.codepoints.extract occurrence.scalarStart occurrence.scalarStop
  bytesExact : fragment.bytes = full.bytes.extract occurrence.byteStart occurrence.byteStop

def occurrenceValid (full fragment : InputView) (occurrence : Occurrence) : Bool :=
  inputValid full && inputValid fragment &&
    decide (occurrence.scalarStart ≤ occurrence.scalarStop) &&
    decide (occurrence.scalarStop ≤ full.codepoints.length) &&
    decide (occurrence.byteStart ≤ occurrence.byteStop) &&
    decide (occurrence.byteStop ≤ full.bytes.length) &&
    full.byteOffsets[occurrence.scalarStart]? == some occurrence.byteStart &&
    full.byteOffsets[occurrence.scalarStop]? == some occurrence.byteStop &&
    fragment.codepoints == full.codepoints.extract occurrence.scalarStart occurrence.scalarStop &&
    fragment.bytes == full.bytes.extract occurrence.byteStart occurrence.byteStop

def occurrenceValid_sound {full fragment : InputView} {occurrence : Occurrence}
    (accepted : occurrenceValid full fragment occurrence = true) :
    CheckedOccurrence full fragment occurrence := by
  simp only [occurrenceValid, Bool.and_eq_true_iff, beq_iff_eq, decide_eq_true_eq] at accepted
  rcases accepted with ⟨⟨⟨⟨⟨⟨⟨⟨⟨fullValid, localValid⟩, ordered⟩, bounded⟩,
    bytesOrdered⟩, bytesBounded⟩, leftOffset⟩, rightOffset⟩, scalarExact⟩, bytesExact⟩
  cases fullRead : checkedInput? full with
  | none => simp [inputValid, fullRead] at fullValid
  | some fullCharacters =>
      cases fragmentRead : checkedInput? fragment with
      | none => simp [inputValid, fragmentRead] at localValid
      | some localCharacters =>
          exact ⟨fullCharacters, localCharacters, checkedInput?_sound fullRead,
            checkedInput?_sound fragmentRead, ordered, bounded, bytesOrdered, bytesBounded,
            leftOffset, rightOffset, scalarExact, bytesExact⟩

theorem occurrenceValid_complete {full fragment : InputView} {occurrence : Occurrence}
    (checked : CheckedOccurrence full fragment occurrence) :
    occurrenceValid full fragment occurrence = true := by
  have fullValid := (inputValid_iff full).mpr ⟨checked.fullCharacters, checked.fullAgreement⟩
  have localValid := (inputValid_iff fragment).mpr ⟨checked.localCharacters, checked.localAgreement⟩
  simp [occurrenceValid, fullValid, localValid, checked.ordered, checked.bounded,
    checked.bytesOrdered, checked.bytesBounded, checked.leftOffset, checked.rightOffset,
    checked.scalarExact, checked.bytesExact]

theorem occurrenceValid_iff (full fragment : InputView) (occurrence : Occurrence) :
    occurrenceValid full fragment occurrence = true ↔ Nonempty (CheckedOccurrence full fragment occurrence) :=
  ⟨fun accepted => ⟨occurrenceValid_sound accepted⟩,
    fun ⟨checked⟩ => occurrenceValid_complete checked⟩

def CheckedOccurrence.slice {full fragment : InputView} {occurrence : Occurrence}
    (checked : CheckedOccurrence full fragment occurrence) : Slice full.codepoints :=
  ⟨occurrence.scalarStart, occurrence.scalarStop, checked.ordered, checked.bounded⟩

theorem CheckedOccurrence.slice_input {full fragment : InputView} {occurrence : Occurrence}
    (checked : CheckedOccurrence full fragment occurrence) :
    checked.slice.input = fragment.codepoints := checked.scalarExact.symm

theorem CheckedOccurrence.fragment_length {full fragment : InputView} {occurrence : Occurrence}
    (checked : CheckedOccurrence full fragment occurrence) :
    fragment.codepoints.length = occurrence.scalarStop - occurrence.scalarStart := by
  rw [← checked.slice_input]
  exact checked.slice.length

theorem CheckedOccurrence.fragment_byte_length {full fragment : InputView}
    {occurrence : Occurrence} (checked : CheckedOccurrence full fragment occurrence) :
    fragment.bytes.length = occurrence.byteStop - occurrence.byteStart := by
  have bounded := checked.bytesBounded
  rw [checked.bytesExact]
  simp [List.extract_eq_take_drop, List.length_take, List.length_drop]
  omega

theorem CheckedOccurrence.eof_iff {full fragment : InputView} {occurrence : Occurrence}
    (checked : CheckedOccurrence full fragment occurrence) :
    occurrence.scalarStop = full.codepoints.length ↔ occurrence.byteStop = full.bytes.length :=
  checked.fullAgreement.eof_iff checked.bounded checked.rightOffset

def CheckedOccurrence.shift? {full fragment : InputView} {occurrence : Occurrence}
    (checked : CheckedOccurrence full fragment occurrence) (certificate : Certificate) :
    Option Certificate := checkedShift? full.codepoints checked.slice certificate

theorem CheckedOccurrence.shift_sound {full fragment : InputView} {occurrence : Occurrence}
    (checked : CheckedOccurrence full fragment occurrence) {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {certificate shifted : Certificate}
    {sort : String} {start stop : Nat} {tree : CST}
    (replay : Replays profile plan fragment.codepoints certificate sort start stop tree)
    (accepted : checked.shift? certificate = some shifted) :
    shifted = shiftCertificate occurrence.scalarStart certificate ∧
      positions shifted = positions certificate ∧
      Nonempty (Replays profile plan full.codepoints shifted sort
        (occurrence.scalarStart + start) (occurrence.scalarStart + stop)
        (shiftTree occurrence.scalarStart tree)) := by
  have localReplay : Replays profile plan checked.slice.input certificate sort start stop tree := by
    simpa only [checked.slice_input] using replay
  exact checkedShift_sound checked.slice localReplay accepted

theorem CheckedOccurrence.shift_value {full fragment : InputView} {occurrence : Occurrence}
    (checked : CheckedOccurrence full fragment occurrence) (actions : ActionTable)
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {certificate shifted : Certificate} {sort : String} {start stop : Nat} {tree : CST}
    (replay : Replays profile plan fragment.codepoints certificate sort start stop tree)
    (accepted : checked.shift? certificate = some shifted) :
    certificateValue? actions full.codepoints shifted =
      certificateValue? actions fragment.codepoints certificate := by
  have localReplay : Replays profile plan checked.slice.input certificate sort start stop tree := by
    simpa only [checked.slice_input] using replay
  simpa only [checked.slice_input] using checkedShift_value checked.slice actions localReplay accepted

/-- A whole local root embeds at the exact exported absolute endpoints. -/
theorem CheckedOccurrence.shift_root {full fragment : InputView} {occurrence : Occurrence}
    (checked : CheckedOccurrence full fragment occurrence) {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {certificate shifted : Certificate}
    {sort : String} {tree : CST}
    (replay : Replays profile plan fragment.codepoints certificate sort 0 fragment.codepoints.length tree)
    (accepted : checked.shift? certificate = some shifted) :
    Nonempty (Replays profile plan full.codepoints shifted sort
      occurrence.scalarStart occurrence.scalarStop (shiftTree occurrence.scalarStart tree)) := by
  obtain ⟨_, _, shiftedReplay⟩ := checked.shift_sound replay accepted
  have endpoint : occurrence.scalarStart + fragment.codepoints.length = occurrence.scalarStop := by
    have exactLength := checked.fragment_length
    have ordered := checked.ordered
    omega
  simpa only [Nat.add_zero, endpoint] using shiftedReplay

/-- The complete supplied catalogue retains its ordered action values.
Its local replay evidence and global EOF checks are explicit; completeness
of the supplied catalogue remains a separate parser obligation. -/
theorem CheckedOccurrence.evaluate_catalogue {full fragment : InputView}
    {occurrence : Occurrence} (checked : CheckedOccurrence full fragment occurrence)
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (actions : ActionTable) (rows : Catalogue)
    (replays : ∀ row ∈ rows, Nonempty (Replays profile plan fragment.codepoints row.1
      plan.lexical.startSort 0 fragment.codepoints.length row.2))
    (safe : ∀ row ∈ rows,
      certificateEndSafe occurrence.scalarStart full.codepoints.length row.1 = true) :
    evaluateCatalogue? actions full.codepoints (shiftCatalogue occurrence.scalarStart rows) =
      evaluateCatalogue? actions fragment.codepoints rows := by
  have sliceReplays : ∀ row ∈ rows, Nonempty (Replays profile plan checked.slice.input row.1
      plan.lexical.startSort 0 checked.slice.input.length row.2) := by
    simpa only [checked.slice_input] using replays
  simpa only [checked.slice_input] using
    evaluateCatalogue_shift checked.slice actions rows sliceReplays safe

/-- Apply the existing distinct-action-value policy after byte/scalar
embedding, preserving every supplied certificate occurrence. -/
theorem CheckedOccurrence.select_catalogue {full fragment : InputView}
    {occurrence : Occurrence} (checked : CheckedOccurrence full fragment occurrence)
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (actions : ActionTable) (rows : Catalogue)
    (replays : ∀ row ∈ rows, Nonempty (Replays profile plan fragment.codepoints row.1
      plan.lexical.startSort 0 fragment.codepoints.length row.2))
    (safe : ∀ row ∈ rows,
      certificateEndSafe occurrence.scalarStart full.codepoints.length row.1 = true) :
    selectCatalogue? actions full.codepoints (shiftCatalogue occurrence.scalarStart rows) =
      selectCatalogue? actions fragment.codepoints rows := by
  unfold selectCatalogue?
  rw [checked.evaluate_catalogue actions rows replays safe]

/-! ## Physical neutral-forest occurrences -/

def forestInput (bytes : List UInt8)
    (view : ClassAwareNativeForestContract.ForestView) : InputView :=
  ⟨bytes, view.codepoints, view.byteOffsets⟩

def nodeOccurrence (node : ClassAwareNativeForestContract.Node) : Occurrence :=
  ⟨node.scalarStart, node.scalarStop, node.byteStart, node.byteStop⟩

/-- A physical node index is looked up, rather than replaced by a reported
label or a neighboring node with an equal payload. -/
def nodeOccurrenceValid (source : List UInt8)
    (view : ClassAwareNativeForestContract.ForestView)
    (fragment : InputView) (nodeIndex : Nat) : Bool :=
  match view.nodes[nodeIndex]? with
  | none => false
  | some node => occurrenceValid (forestInput source view) fragment (nodeOccurrence node)

theorem nodeOccurrenceValid_iff (source : List UInt8)
    (view : ClassAwareNativeForestContract.ForestView)
    (fragment : InputView) (nodeIndex : Nat) :
    nodeOccurrenceValid source view fragment nodeIndex = true ↔
      ∃ node, view.nodes[nodeIndex]? = some node ∧
        Nonempty (CheckedOccurrence (forestInput source view) fragment (nodeOccurrence node)) := by
  cases selected : view.nodes[nodeIndex]? with
  | none => simp [nodeOccurrenceValid, selected]
  | some node => simp [nodeOccurrenceValid, selected, occurrenceValid_iff]

/-- A zero-width witness leaf records the body's separate consumed span.
Matching the witness number establishes an occurrence link; the guard plan
must separately license the terminal identity and the body's source meaning. -/
def zeroWidthBodyValid (source : List UInt8)
    (view : ClassAwareNativeForestContract.ForestView) (fragment : InputView)
    (nodeIndex witnessId : Nat) (body : Occurrence) : Bool :=
  match view.nodes[nodeIndex]? with
  | none => false
  | some node =>
      match node.kind with
      | .terminal _ (.witness identifier) =>
          identifier == witnessId && node.scalarStart == node.scalarStop &&
            node.byteStart == node.byteStop && node.scalarStart == body.scalarStart &&
            node.byteStart == body.byteStart &&
            occurrenceValid (forestInput source view) fragment body
      | _ => false

structure ZeroWidthBodyEmbedding (source : List UInt8)
    (view : ClassAwareNativeForestContract.ForestView) (fragment : InputView)
    (nodeIndex witnessId : Nat) (body : Occurrence) : Type where
  node : ClassAwareNativeForestContract.Node
  terminalId : Nat
  selected : view.nodes[nodeIndex]? = some node
  kindExact : node.kind = .terminal terminalId (.witness witnessId)
  scalarZero : node.scalarStart = node.scalarStop
  byteZero : node.byteStart = node.byteStop
  scalarAtBody : node.scalarStart = body.scalarStart
  byteAtBody : node.byteStart = body.byteStart
  checkedBody : CheckedOccurrence (forestInput source view) fragment body

def zeroWidthBodyValid_sound {source : List UInt8}
    {view : ClassAwareNativeForestContract.ForestView} {fragment : InputView}
    {nodeIndex witnessId : Nat} {body : Occurrence}
    (accepted : zeroWidthBodyValid source view fragment nodeIndex witnessId body = true) :
    ZeroWidthBodyEmbedding source view fragment nodeIndex witnessId body := by
  unfold zeroWidthBodyValid at accepted
  cases selected : view.nodes[nodeIndex]? with
  | none => simp [selected] at accepted
  | some node =>
      simp only [selected] at accepted
      cases kind : node.kind with
      | epsilon | symbol _ | intermediate _ _ => simp [kind] at accepted
      | terminal terminalId value =>
          cases value with
          | scalar _ | eof => simp [kind] at accepted
          | witness identifier =>
              simp only [kind, Bool.and_eq_true_iff, beq_iff_eq] at accepted
              rcases accepted with ⟨⟨⟨⟨⟨identifierExact, scalarZero⟩, byteZero⟩,
                scalarAtBody⟩, byteAtBody⟩, bodyAccepted⟩
              subst identifier
              exact ⟨node, terminalId, selected, kind, scalarZero, byteZero,
                scalarAtBody, byteAtBody, occurrenceValid_sound bodyAccepted⟩

theorem zeroWidthBodyValid_complete {source : List UInt8}
    {view : ClassAwareNativeForestContract.ForestView} {fragment : InputView}
    {nodeIndex witnessId : Nat} {body : Occurrence}
    (embedding : ZeroWidthBodyEmbedding source view fragment nodeIndex witnessId body) :
    zeroWidthBodyValid source view fragment nodeIndex witnessId body = true := by
  simp only [zeroWidthBodyValid, embedding.selected, embedding.kindExact,
    Bool.and_eq_true_iff, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨True.intro, embedding.scalarZero⟩, embedding.byteZero⟩, embedding.scalarAtBody⟩,
    embedding.byteAtBody⟩, occurrenceValid_complete embedding.checkedBody⟩

theorem zeroWidthBodyValid_iff (source : List UInt8)
    (view : ClassAwareNativeForestContract.ForestView) (fragment : InputView)
    (nodeIndex witnessId : Nat) (body : Occurrence) :
    zeroWidthBodyValid source view fragment nodeIndex witnessId body = true ↔
      Nonempty (ZeroWidthBodyEmbedding source view fragment nodeIndex witnessId body) :=
  ⟨fun accepted => ⟨zeroWidthBodyValid_sound accepted⟩,
    fun ⟨embedding⟩ => zeroWidthBodyValid_complete embedding⟩

/-! ## Ordered source-byte copies -/

abbrev SourceFiles := List (List UInt8)

structure SourcePiece where
  sourceFile : Nat
  sourceStart : Nat
  sourceStop : Nat
  expandedStart : Nat
  expandedStop : Nat
  deriving DecidableEq, Repr

/-- The byte-copy relation retains exact source-file indices and explicit
expanded seams. Equal source content never merges physical occurrences. -/
inductive PiecesCopy (files : SourceFiles) : Nat → List SourcePiece → List UInt8 → Prop where
  | nil (cursor : Nat) : PiecesCopy files cursor [] []
  | copy {cursor : Nat} {piece : SourcePiece} {pieces : List SourcePiece}
      {source rest : List UInt8}
      (fileAt : files[piece.sourceFile]? = some source)
      (ordered : piece.sourceStart ≤ piece.sourceStop)
      (bounded : piece.sourceStop ≤ source.length)
      (leftExact : piece.expandedStart = cursor)
      (rightExact : piece.expandedStop = cursor + (piece.sourceStop - piece.sourceStart))
      (tail : PiecesCopy files piece.expandedStop pieces rest) :
      PiecesCopy files cursor (piece :: pieces)
        (source.extract piece.sourceStart piece.sourceStop ++ rest)

def copyPieces? (files : SourceFiles) (cursor : Nat) :
    List SourcePiece → Option (List UInt8)
  | [] => some []
  | piece :: pieces => do
      let source ← files[piece.sourceFile]?
      if piece.sourceStart ≤ piece.sourceStop ∧ piece.sourceStop ≤ source.length ∧
          piece.expandedStart = cursor ∧
          piece.expandedStop = cursor + (piece.sourceStop - piece.sourceStart) then
        let rest ← copyPieces? files piece.expandedStop pieces
        pure (source.extract piece.sourceStart piece.sourceStop ++ rest)
      else none

theorem copyPieces?_sound {files : SourceFiles} {cursor : Nat}
    {pieces : List SourcePiece} {expanded : List UInt8}
    (accepted : copyPieces? files cursor pieces = some expanded) :
    PiecesCopy files cursor pieces expanded := by
  induction pieces generalizing cursor expanded with
  | nil =>
      simp [copyPieces?] at accepted
      subst expanded
      exact .nil cursor
  | cons piece pieces inductionHypothesis =>
      simp only [copyPieces?] at accepted
      cases fileAt : files[piece.sourceFile]? with
      | none => simp [fileAt] at accepted
      | some source =>
          simp only [fileAt, Option.bind_eq_bind, Option.bind_some] at accepted
          split at accepted
          · rename_i fields
            rcases fields with ⟨ordered, bounded, leftExact, rightExact⟩
            cases tailAccepted : copyPieces? files piece.expandedStop pieces with
            | none => simp [tailAccepted] at accepted
            | some rest =>
                simp only [tailAccepted, Option.bind_some,
                  pure, Option.some.injEq] at accepted
                subst expanded
                exact .copy fileAt ordered bounded leftExact rightExact
                  (inductionHypothesis tailAccepted)
          · contradiction

theorem copyPieces?_complete {files : SourceFiles} {cursor : Nat}
    {pieces : List SourcePiece} {expanded : List UInt8}
    (copied : PiecesCopy files cursor pieces expanded) :
    copyPieces? files cursor pieces = some expanded := by
  induction copied with
  | nil cursor => rfl
  | copy fileAt ordered bounded leftExact rightExact _tail inductionHypothesis =>
      simp only [copyPieces?, fileAt, Option.bind_eq_bind, Option.bind_some]
      rw [if_pos ⟨ordered, bounded, leftExact, rightExact⟩, inductionHypothesis]
      rfl

theorem copyPieces?_iff (files : SourceFiles) (cursor : Nat)
    (pieces : List SourcePiece) (expanded : List UInt8) :
    copyPieces? files cursor pieces = some expanded ↔ PiecesCopy files cursor pieces expanded :=
  ⟨copyPieces?_sound, copyPieces?_complete⟩

def inclusionValid (files : SourceFiles) (pieces : List SourcePiece)
    (expanded : List UInt8) : Bool := copyPieces? files 0 pieces == some expanded

theorem inclusionValid_iff (files : SourceFiles) (pieces : List SourcePiece)
    (expanded : List UInt8) :
    inclusionValid files pieces expanded = true ↔ PiecesCopy files 0 pieces expanded := by
  simp only [inclusionValid, beq_iff_eq]
  exact copyPieces?_iff files 0 pieces expanded

def pieceEnd (cursor : Nat) : List SourcePiece → Nat
  | [] => cursor
  | piece :: rest => pieceEnd piece.expandedStop rest

private theorem extract_length {α : Type} (source : List α) {start stop : Nat}
    (_ordered : start ≤ stop) (bounded : stop ≤ source.length) :
    (source.extract start stop).length = stop - start := by
  simp [List.extract_eq_take_drop, List.length_take, List.length_drop]
  omega

/-- The explicit last seam equals the complete copied byte extent. -/
theorem PiecesCopy.extent {files : SourceFiles} {cursor : Nat}
    {pieces : List SourcePiece} {expanded : List UInt8}
    (copied : PiecesCopy files cursor pieces expanded) :
    pieceEnd cursor pieces = cursor + expanded.length := by
  induction copied with
  | nil cursor => simp [pieceEnd]
  | @copy cursor piece pieces source rest _ ordered bounded _ rightExact _ inductionHypothesis =>
      have sizeExact := extract_length source ordered bounded
      simp only [pieceEnd, List.length_append]
      rw [inductionHypothesis, rightExact, sizeExact]
      omega

/-- Each retained piece has an actual source-file occurrence and an exact
expanded byte occurrence. The prefix keeps its ordered physical position. -/
theorem PiecesCopy.occurrence {files : SourceFiles} {cursor : Nat}
    {pieces : List SourcePiece} {expanded : List UInt8}
    (copied : PiecesCopy files cursor pieces expanded)
    {piece : SourcePiece} (member : piece ∈ pieces) :
    ∃ source leading suffix,
      files[piece.sourceFile]? = some source ∧
      piece.sourceStart ≤ piece.sourceStop ∧ piece.sourceStop ≤ source.length ∧
      expanded = leading ++ source.extract piece.sourceStart piece.sourceStop ++ suffix ∧
      piece.expandedStart = cursor + leading.length ∧
      piece.expandedStop = piece.expandedStart +
        (source.extract piece.sourceStart piece.sourceStop).length := by
  induction copied with
  | nil cursor => simp at member
  | @copy cursor head pieces headSource rest fileAt ordered bounded leftExact rightExact
      _tail inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with same | tailMember
      · subst piece
        refine ⟨headSource, [], rest, fileAt, ordered, bounded, ?_, ?_, ?_⟩
        · simp
        · simpa using leftExact
        · rw [leftExact, extract_length headSource ordered bounded]
          exact rightExact
      · obtain ⟨source, leading, suffix, sourceAt, sourceOrdered, sourceBounded,
          expandedExact, startExact, stopExact⟩ := inductionHypothesis tailMember
        refine ⟨source, headSource.extract head.sourceStart head.sourceStop ++ leading,
          suffix, sourceAt, sourceOrdered, sourceBounded, ?_, ?_, stopExact⟩
        · simp [expandedExact, List.append_assoc]
        · rw [List.length_append, extract_length headSource ordered bounded]
          omega

/-- Project an expanded byte occurrence back to its physical source file.
The offsets are relative to the supplied copy's initial cursor. -/
theorem PiecesCopy.projection {files : SourceFiles} {cursor : Nat}
    {pieces : List SourcePiece} {expanded : List UInt8}
    (copied : PiecesCopy files cursor pieces expanded)
    {piece : SourcePiece} (member : piece ∈ pieces) :
    ∃ source,
      files[piece.sourceFile]? = some source ∧
      piece.sourceStart ≤ piece.sourceStop ∧ piece.sourceStop ≤ source.length ∧
      cursor ≤ piece.expandedStart ∧ piece.expandedStop ≤ cursor + expanded.length ∧
      expanded.extract (piece.expandedStart - cursor) (piece.expandedStop - cursor) =
        source.extract piece.sourceStart piece.sourceStop := by
  obtain ⟨source, leading, suffix, fileAt, ordered, bounded,
    expandedExact, startExact, stopExact⟩ := copied.occurrence member
  refine ⟨source, fileAt, ordered, bounded, by omega, ?_, ?_⟩
  · have lengthExact := congrArg List.length expandedExact
    simp only [List.length_append] at lengthExact
    omega
  · have startRelative : piece.expandedStart - cursor = leading.length := by omega
    have stopRelative : piece.expandedStop - cursor = leading.length +
        (source.extract piece.sourceStart piece.sourceStop).length := by omega
    rw [expandedExact, startRelative, stopRelative]
    simp only [List.extract_eq_take_drop, List.append_assoc, List.drop_append_length,
      Nat.add_sub_cancel_left, List.take_append_length]

/-- A source inclusion receipt begins at byte zero, so its exported byte
spans select the original bytes without any coordinate normalization. -/
theorem PiecesCopy.source_bytes {files : SourceFiles} {pieces : List SourcePiece}
    {expanded : List UInt8} (copied : PiecesCopy files 0 pieces expanded)
    {piece : SourcePiece} (member : piece ∈ pieces) :
    ∃ source,
      files[piece.sourceFile]? = some source ∧
      piece.sourceStart ≤ piece.sourceStop ∧ piece.sourceStop ≤ source.length ∧
      piece.expandedStop ≤ expanded.length ∧
      expanded.extract piece.expandedStart piece.expandedStop =
        source.extract piece.sourceStart piece.sourceStop := by
  obtain ⟨source, fileAt, ordered, bounded, _, stopBounded, bytesExact⟩ :=
    copied.projection member
  exact ⟨source, fileAt, ordered, bounded, by simpa using stopBounded,
    by simpa using bytesExact⟩

/-! ## Byte, occurrence and inclusion controls -/

private def controlFull : InputView := {
  bytes := [65, 206, 178, 240, 159, 153, 130, 0, 13, 10]
  codepoints := [65, 946, 128578, 0, 13, 10]
  byteOffsets := [0, 1, 3, 7, 8, 9, 10]
}

private def controlFragment : InputView := {
  bytes := [206, 178]
  codepoints := [946]
  byteOffsets := [0, 2]
}

private def controlOccurrence : Occurrence := ⟨1, 2, 1, 3⟩

theorem control_exact_utf8_scalars_and_offsets :
    checkedInput? controlFull =
      some ['A', Char.ofNat 946, Char.ofNat 128578, Char.ofNat 0, '\r', '\n'] := by decide

theorem control_changed_scalar_table_refused :
    inputValid {controlFull with codepoints := [65, 947, 128578, 0, 13, 10]} = false := by decide

theorem control_changed_byte_offset_refused :
    inputValid {controlFull with byteOffsets := [0, 1, 2, 7, 8, 9, 10]} = false := by decide

theorem control_overlong_utf8_refused :
    inputValid ⟨[192, 175], [47], [0, 2]⟩ = false := by decide

theorem control_truncated_utf8_refused :
    inputValid ⟨[240, 159, 153], [128578], [0, 3]⟩ = false := by decide

theorem control_encoded_surrogate_refused :
    inputValid ⟨[237, 160, 128], [55296], [0, 3]⟩ = false := by decide

theorem control_above_unicode_limit_refused :
    inputValid ⟨[244, 144, 128, 128], [1114112], [0, 4]⟩ = false := by decide

theorem control_large_nat_does_not_alias_scalar :
    inputValid ⟨[65], [4294967361], [0, 1]⟩ = false := by decide

theorem control_unicode_occurrence :
    occurrenceValid controlFull controlFragment controlOccurrence = true := by decide

private def controlChecked : CheckedOccurrence controlFull controlFragment controlOccurrence :=
  occurrenceValid_sound control_unicode_occurrence

theorem control_local_offsets_are_normalized :
    occurrenceValid controlFull {controlFragment with byteOffsets := [1, 3]}
      controlOccurrence = false := by decide

theorem control_middle_of_utf8_scalar_refused :
    occurrenceValid controlFull controlFragment {controlOccurrence with byteStart := 2} = false := by decide

theorem control_changed_local_bytes_refused :
    occurrenceValid controlFull ⟨[206, 179], [947], [0, 2]⟩ controlOccurrence = false := by decide

theorem control_crlf_suffix_occurrence :
    occurrenceValid controlFull ⟨[13, 10], [13, 10], [0, 1, 2]⟩ ⟨4, 6, 8, 10⟩ = true := by decide

theorem control_crlf_is_not_collapsed :
    occurrenceValid controlFull ⟨[10], [10], [0, 1]⟩ ⟨4, 6, 8, 10⟩ = false := by decide

private def controlProfile : ParserProfileLayer := {
  name := "InputOccurrence"
  startSort := "Value"
  classes := []
  states := []
}

private def controlPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "InputOccurrence"
    startSort := "Value"
    classes := []
    productions := [{ label := "unicode", resultSort := "Value", matcher := .char 946, childSlots := [0] }]
  }
  structural := []
}

private def controlCertificate : Certificate := .lexical 0 (.char 946) 0 1

private def controlTree : CST := .node "unicode" 0 1 [.terminal [946] 0 1]

private def controlLocalReplay :
    Replays controlProfile controlPlan controlFragment.codepoints controlCertificate
      "Value" 0 1 controlTree :=
  .lexical 0 (by decide) rfl rfl rfl ⟨.char (by decide), rfl⟩

theorem control_certificate_absolute_unicode_span :
    controlChecked.shift? controlCertificate = some (.lexical 0 (.char 946) 1 2) := by decide

theorem control_unicode_root_replays_in_full_input :
    Nonempty (Replays controlProfile controlPlan controlFull.codepoints
      (.lexical 0 (.char 946) 1 2) "Value" 1 2 (shiftTree 1 controlTree)) :=
  controlChecked.shift_root controlLocalReplay control_certificate_absolute_unicode_span

theorem control_local_eof_is_not_global_eof :
    controlChecked.shift? (.lexical 0 .eof 1 1) = none := by decide

private def controlSuffixChecked : CheckedOccurrence controlFull
    ⟨[13, 10], [13, 10], [0, 1, 2]⟩ ⟨4, 6, 8, 10⟩ :=
  occurrenceValid_sound control_crlf_suffix_occurrence

theorem control_real_global_eof_transport :
    controlSuffixChecked.shift? (.lexical 0 .eof 2 2) = some (.lexical 0 .eof 6 6) := by decide

private def controlConsumingNode : ClassAwareNativeForestContract.Node := {
  kind := .terminal 9 (.scalar 946)
  scalarStart := 1
  scalarStop := 2
  byteStart := 1
  byteStop := 3
  choiceBegin := 0
  choiceCount := 0
}

private def controlWitnessNode : ClassAwareNativeForestContract.Node := {
  kind := .terminal 10 (.witness 7)
  scalarStart := 1
  scalarStop := 1
  byteStart := 1
  byteStop := 1
  choiceBegin := 0
  choiceCount := 0
}

private def controlView : ClassAwareNativeForestContract.ForestView := {
  codepoints := controlFull.codepoints
  byteOffsets := controlFull.byteOffsets
  nodes := [controlConsumingNode, controlWitnessNode]
  choices := []
  roots := []
}

theorem control_physical_native_node_occurrence :
    nodeOccurrenceValid controlFull.bytes controlView controlFragment 0 = true := by decide

theorem control_wrong_native_node_refused :
    nodeOccurrenceValid controlFull.bytes controlView controlFragment 1 = false ∧
      nodeOccurrenceValid controlFull.bytes controlView controlFragment 2 = false := by decide

theorem control_zero_width_body_embedding :
    zeroWidthBodyValid controlFull.bytes controlView controlFragment 1 7 controlOccurrence = true := by decide

theorem control_changed_guard_witness_refused :
    zeroWidthBodyValid controlFull.bytes controlView controlFragment 1 8 controlOccurrence = false := by decide

theorem control_consuming_leaf_is_not_zero_width :
    zeroWidthBodyValid controlFull.bytes
      {controlView with nodes := [{controlWitnessNode with scalarStop := 2, byteStop := 3}]}
      controlFragment 0 7 controlOccurrence = false := by decide

theorem control_wrong_guard_byte_cursor_refused :
    zeroWidthBodyValid controlFull.bytes
      {controlView with nodes := [{controlWitnessNode with byteStart := 2, byteStop := 2}]}
      controlFragment 0 7 controlOccurrence = false := by decide

private def controlFiles : SourceFiles := [[65, 66, 67, 68], [206, 178, 13, 10], [65, 66, 67, 68]]

private def controlPieces : List SourcePiece := [
  ⟨0, 0, 1, 0, 1⟩,
  ⟨1, 0, 4, 1, 5⟩,
  ⟨0, 3, 4, 5, 6⟩,
  ⟨2, 0, 1, 6, 7⟩
]

private def controlExpanded : List UInt8 := [65, 206, 178, 13, 10, 68, 65]

theorem control_ordered_inclusion_bytes :
    inclusionValid controlFiles controlPieces controlExpanded = true := by decide

theorem control_all_inclusion_occurrences_retained :
    controlPieces.length = 4 ∧ pieceEnd 0 controlPieces = controlExpanded.length := by decide

theorem control_unknown_source_file_refused :
    copyPieces? controlFiles 0 [⟨3, 0, 1, 0, 1⟩] = none := by decide

theorem control_source_bounds_refused :
    copyPieces? controlFiles 0 [⟨0, 0, 5, 0, 5⟩] = none ∧
      copyPieces? controlFiles 0 [⟨0, 2, 1, 0, 0⟩] = none := by decide

theorem control_inclusion_gap_refused :
    copyPieces? controlFiles 0 [⟨0, 0, 1, 0, 1⟩, ⟨1, 0, 4, 2, 6⟩] = none := by decide

theorem control_inclusion_overlap_refused :
    copyPieces? controlFiles 0 [⟨0, 0, 1, 0, 1⟩, ⟨1, 0, 4, 0, 4⟩] = none := by decide

theorem control_changed_expanded_end_refused :
    copyPieces? controlFiles 0 [⟨0, 0, 1, 0, 2⟩] = none := by decide

theorem control_reordered_inclusion_refused :
    inclusionValid controlFiles controlPieces.reverse controlExpanded = false := by decide

theorem control_changed_expanded_line_ending_refused :
    inclusionValid controlFiles controlPieces [65, 206, 178, 13, 13, 68, 65] = false := by decide

theorem control_empty_pieces_keep_multiplicity :
    copyPieces? controlFiles 0 [⟨0, 1, 1, 0, 0⟩, ⟨0, 1, 1, 0, 0⟩] = some [] := by decide

theorem control_equal_source_content_keeps_distinct_file_indices :
    PiecesCopy controlFiles 0 [⟨0, 0, 1, 0, 1⟩, ⟨2, 0, 1, 1, 2⟩] [65, 65] :=
  copyPieces?_sound (by decide)

end Mettapedia.GSLT.Parsing.ParserPackInputOccurrence
