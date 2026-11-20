import Init.Data.UInt.Bitwise
import Mettapedia.Machines.IncrementalConformance.InternProbe
import Mettapedia.GSLT.LanguageDef.NativeOpsByteViews
import Mettapedia.Machines.CMemory.Array
import Mettapedia.Machines.CMemory.EffectStatements
import Mettapedia.Machines.CMemory.Tactic
import Mettapedia.Machines.CMemory.ProductiveBlocks
import Mettapedia.GSLT.LanguageDef.NativeOpsCLexSegments
import Mettapedia.GSLT.LanguageDef.NativeOpsCStatement
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceEval
import Mettapedia.GSLT.LanguageDef.NativeRecordAccess
import Mettapedia.Languages.MeTTa.MetavariableFrameLineage
import Mettapedia.Data.Fin.OptionSequence
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mettapedia.Languages.MeTTa.MetavariableFrameStoreEscape
import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.Cursor.ReadOnlyQuery
import Mettapedia.Machines.ReadCertifiedQueryReuse

/-!
# Native framed bindings and the common binding store

Checked record readers admit packed frame identities, complete directories,
contextual payloads and activation views into the existing common frame store.
They preserve null slots, write versions, selected scope identity and ordered
source inventories. Readback is independent of Need-cache histories; the Need
adapter imports these bindings rather than defining a second carrier.

This adapter updates a checked native frame inventory independently of the
common store operation, then proves that decoding commutes with a slot write.
It preserves contextual payload tags, source identities, presentation,
activation boundaries and every other slot. The finite native write clock
must have room for the new version.

Root alias resolution combines these frames with a checked ordinary-row
inventory and uses the shared read-only query, cursor and cache protocols.
Its alias allowance is distinct from cursor fuel. The native helper's
bound-metadata calculation, no-bindings fast path, signed lookup-index result
and encompassing physical execution remain separate joins. The selected
current-slot copy block is admitted from C text and executed through the shared
physical memory model. It copies the complete contextual value and joins its
readback to the current frame, including pauses during the copy. The contiguous source-slot branch selects
exactly the interval coordinate while retaining the output on either range
refusal. The sorted suffix is read from the actual C text and executed through
physical schema and embedded-array reads. An independently sorted inventory
proves its search terminates at the unique slot or returns false without
changing the output. Its source declarations restore older local bindings;
scheduler suspension retains performed reads and writes. The directory's
actual hash and lookup bodies are read from C text; their physical loop keeps
pointer tests, epoch reads, wrap updates and restored local bindings. An
independent power-of-two, half-load inventory earns its finite search bound.
Owning-row and full-epoch laws connect the finite probe to shared frame reads.
The decoder's parts and handle/generation bodies execute through checked
source-to-physical-operation laws, including owned automatic regions and retained
partial writes. The directory call now composes the actual handle helper and
by-value Ref validation with its finite probe and final full-epoch comparison.
Its retained completion and reflection preserve every helper receipt and restore
shadowed parameters and locals. Native byte layout, automatic-storage lifetime,
obtaining the enclosing directory and the later mode/entry guards remain explicit
component obligations.

The input is a borrowed readback of the caller's current frame. Directory
detachment, obtaining exclusive storage, updating native bound/private counts
and retaining the payload are prerequisites, not consequences of the readback
model. This module does not establish execution of the encompassing C helper.
An abstract refusal retains its supplied image. A native refusal may follow
directory or slot-storage detachment, so native callers must reacquire borrowed
views and establish preservation of the logical image separately.

Physical Atom observations use the same scalar-cell memory model and checked
C-expression reader. They preserve full variable identities, expression
pointer positions and the selected physical field values. Their borrowed-memory
profile requires live, unforwarded storage; byte-layout and lifetime transport
remain explicit component obligations. Managed spelling helpers retain the actual pointer tests, two forwarding
passes, explicit length and unsigned-byte storage. Their selected source
expressions are checked separately from the surrounding C call ABI. Exact
bytes and checked UTF-8 source interpretation live in the downstream
contextual payload adapter.

The native symbol forwarding helper is admitted from its exact C body. Its
short-circuit guard, active forwarding-arm read and local pointer assignment
execute through the same physical memory operations. A finite live forwarding
path determines its exact terminal pointer and preserves the whole heap;
suspension retains the executed reads. Native byte layout, borrowed lifetime
and the later symbol-spelling APIs remain separate component boundaries.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback

open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.GSLT.LanguageDef.NativeOps

/-! ## Checked native frame identities

The packed word is the native lexical identity, independent of the containing
binding image. This codec retains the native generation without translating
allocator transitions. Its four classes use the runtime's prefix spelling,
class-specific generation limits and disjoint global handle ranges. Successful
decoding proves representability, not live
ownership, borrowed-storage validity, or permission to retain a frame.
-/

namespace NativeFrames

open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Token)

def handleRadix : Nat := 2 ^ 20
def classOneFirst : Nat := 2 ^ 20
def classTwoFirst : Nat := 2 ^ 20 + 2 ^ 24
def classThreeFirst : Nat := 2 ^ 20 + 2 ^ 24 + 2 ^ 26
def handleLimit : Nat := 2 ^ 20 + 2 ^ 24 + 2 * 2 ^ 26

def generationMax (handle : Nat) : Nat :=
  if handle < classOneFirst then 2046
  else if handle < classTwoFirst then 62
  else if handle < classThreeFirst then 6 else 2

def Representable (token : Token) : Prop :=
  0 < token.handle ∧ token.handle < handleLimit ∧
    0 < token.generation ∧ token.generation ≤ generationMax token.handle

instance (token : Token) : Decidable (Representable token) := by
  unfold Representable; infer_instance

def unpackHandle (word : Nat) : Nat :=
  if word < 2 ^ 31 then word % 2 ^ 20
  else if word < 3 * 2 ^ 30 then classOneFirst + word % 2 ^ 24
  else if word < 7 * 2 ^ 29 then classTwoFirst + word % 2 ^ 26
  else if word < 15 * 2 ^ 28 then classThreeFirst + word % 2 ^ 26
  else handleLimit + word % 2 ^ 28

def unpackGeneration (word : Nat) : Nat :=
  if word < 2 ^ 31 then word / 2 ^ 20
  else if word < 3 * 2 ^ 30 then word / 2 ^ 24 % 64
  else if word < 7 * 2 ^ 29 then word / 2 ^ 26 % 8
  else if word < 15 * 2 ^ 28 then word / 2 ^ 26 % 4 else 0

def packedHandle (word : BitVec 64) : Nat := unpackHandle word.toNat
def packedGeneration (word : BitVec 64) : Nat := unpackGeneration word.toNat

def encoding (token : Token) : Nat :=
  if token.handle < classOneFirst then token.generation * 2 ^ 20 + token.handle
  else if token.handle < classTwoFirst then
    2 ^ 31 + token.generation * 2 ^ 24 + (token.handle - classOneFirst)
  else if token.handle < classThreeFirst then
    3 * 2 ^ 30 + token.generation * 2 ^ 26 + (token.handle - classTwoFirst)
  else 7 * 2 ^ 29 + token.generation * 2 ^ 26 + (token.handle - classThreeFirst)

def encode (token : Token) : BitVec 64 := BitVec.ofNat 64 (encoding token)
def decode? (word : BitVec 64) : Option Token :=
  let token : Token := ⟨packedHandle word, packedGeneration word⟩
  if word.toNat < 2 ^ 32 ∧ Representable token then some token else none

theorem encoding_bounds {token : Token} (valid : Representable token) :
    0 < encoding token ∧ encoding token < 15 * 2 ^ 28 := by
  unfold Representable generationMax encoding classOneFirst classTwoFirst classThreeFirst handleLimit at *
  split_ifs at * <;> omega

theorem encode_toNat {token : Token} (valid : Representable token) :
    (encode token).toNat = encoding token := by
  rw [encode, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := (encoding_bounds valid).2; omega)

theorem encode_fits_uint32 {token : Token} (valid : Representable token) :
    (encode token).toNat < 2 ^ 32 := by
  rw [encode_toNat valid]
  have := (encoding_bounds valid).2
  omega

theorem unpack_encoding {token : Token} (valid : Representable token) :
    unpackHandle (encoding token) = token.handle ∧
      unpackGeneration (encoding token) = token.generation := by
  by_cases first : token.handle < classOneFirst
  · have gen : token.generation ≤ 2046 := by simpa [generationMax, first] using valid.2.2.2
    have bound : token.generation * 2 ^ 20 + token.handle < 2 ^ 31 := by
      dsimp [classOneFirst] at first; omega
    simp only [encoding, first, ↓reduceIte, unpackHandle, unpackGeneration, bound]
    dsimp [classOneFirst] at first
    constructor <;> omega
  · by_cases second : token.handle < classTwoFirst
    · have gen : token.generation ≤ 62 := by simpa [generationMax, first, second] using valid.2.2.2
      have lower : 2 ^ 31 ≤ 2 ^ 31 + token.generation * 2 ^ 24 + (token.handle - classOneFirst) := by omega
      have upper : 2 ^ 31 + token.generation * 2 ^ 24 + (token.handle - classOneFirst) < 3 * 2 ^ 30 := by
        dsimp [classOneFirst, classTwoFirst] at *; omega
      simp only [encoding, first, second, ↓reduceIte, unpackHandle, unpackGeneration,
        Nat.not_lt.mpr lower, upper]
      dsimp [classOneFirst, classTwoFirst] at *
      constructor <;> omega
    · by_cases third : token.handle < classThreeFirst
      · have gen : token.generation ≤ 6 := by simpa [generationMax, first, second, third] using valid.2.2.2
        have lower : 3 * 2 ^ 30 ≤ 3 * 2 ^ 30 + token.generation * 2 ^ 26 + (token.handle - classTwoFirst) := by omega
        have lower0 : 2 ^ 31 ≤ 3 * 2 ^ 30 + token.generation * 2 ^ 26 + (token.handle - classTwoFirst) := by omega
        have upper : 3 * 2 ^ 30 + token.generation * 2 ^ 26 + (token.handle - classTwoFirst) < 7 * 2 ^ 29 := by
          dsimp [classTwoFirst, classThreeFirst] at *; omega
        simp only [encoding, first, second, third, ↓reduceIte, unpackHandle, unpackGeneration,
          Nat.not_lt.mpr lower, Nat.not_lt.mpr lower0, upper]
        dsimp [classOneFirst, classTwoFirst, classThreeFirst] at *
        constructor <;> omega
      · have gen : token.generation ≤ 2 := by simpa [generationMax, first, second, third] using valid.2.2.2
        have last := valid.2.1
        have lower : 7 * 2 ^ 29 ≤ 7 * 2 ^ 29 + token.generation * 2 ^ 26 + (token.handle - classThreeFirst) := by omega
        have lower0 : 2 ^ 31 ≤ 7 * 2 ^ 29 + token.generation * 2 ^ 26 + (token.handle - classThreeFirst) := by omega
        have lower1 : 3 * 2 ^ 30 ≤ 7 * 2 ^ 29 + token.generation * 2 ^ 26 + (token.handle - classThreeFirst) := by omega
        have upper : 7 * 2 ^ 29 + token.generation * 2 ^ 26 + (token.handle - classThreeFirst) < 15 * 2 ^ 28 := by
          dsimp [classThreeFirst, handleLimit] at *; omega
        simp only [encoding, first, second, third, ↓reduceIte, unpackHandle, unpackGeneration,
          Nat.not_lt.mpr lower, Nat.not_lt.mpr lower0, Nat.not_lt.mpr lower1, upper]
        dsimp [classOneFirst, classTwoFirst, classThreeFirst, handleLimit] at *
        constructor <;> omega

theorem packedHandle_encode {token : Token} (valid : Representable token) :
    packedHandle (encode token) = token.handle := by
  rw [packedHandle, encode_toNat valid]
  exact (unpack_encoding valid).1

theorem packedGeneration_encode {token : Token} (valid : Representable token) :
    packedGeneration (encode token) = token.generation := by
  rw [packedGeneration, encode_toNat valid]
  exact (unpack_encoding valid).2

theorem decode_encode {token : Token} (valid : Representable token) :
    decode? (encode token) = some token := by
  have pair : (⟨packedHandle (encode token), packedGeneration (encode token)⟩ : Token) = token := by
    cases token
    simp_all [packedHandle_encode valid, packedGeneration_encode valid]
  simp only [decode?, pair, encode_fits_uint32 valid, valid, and_self, if_true]

theorem encoding_unpack {word : Nat} (width : word < 2 ^ 32)
    (valid : Representable ⟨unpackHandle word, unpackGeneration word⟩) :
    encoding ⟨unpackHandle word, unpackGeneration word⟩ = word := by
  by_cases first : word < 2 ^ 31
  · have h : word % 2 ^ 20 < classOneFirst := by dsimp [classOneFirst]; omega
    simp only [unpackHandle, unpackGeneration, first, ↓reduceIte, encoding, h]
    omega
  · by_cases second : word < 3 * 2 ^ 30
    · have no0 : ¬classOneFirst + word % 2 ^ 24 < classOneFirst := by omega
      have h : classOneFirst + word % 2 ^ 24 < classTwoFirst := by
        dsimp [classOneFirst, classTwoFirst]; omega
      simp only [unpackHandle, unpackGeneration, first, second, ↓reduceIte, encoding, no0, h]
      dsimp [classOneFirst, classTwoFirst] at *
      omega
    · by_cases third : word < 7 * 2 ^ 29
      · have no0 : ¬classTwoFirst + word % 2 ^ 26 < classOneFirst := by
          dsimp [classOneFirst, classTwoFirst]; omega
        have no1 : ¬classTwoFirst + word % 2 ^ 26 < classTwoFirst := by omega
        have h : classTwoFirst + word % 2 ^ 26 < classThreeFirst := by
          dsimp [classTwoFirst, classThreeFirst]; omega
        simp only [unpackHandle, unpackGeneration, first, second, third, ↓reduceIte,
          encoding, no0, no1, h]
        dsimp [classTwoFirst, classThreeFirst] at *
        omega
      · by_cases fourth : word < 15 * 2 ^ 28
        · have no0 : ¬classThreeFirst + word % 2 ^ 26 < classOneFirst := by
            dsimp [classOneFirst, classThreeFirst]; omega
          have no1 : ¬classThreeFirst + word % 2 ^ 26 < classTwoFirst := by
            dsimp [classTwoFirst, classThreeFirst]; omega
          have no2 : ¬classThreeFirst + word % 2 ^ 26 < classThreeFirst := by omega
          simp only [unpackHandle, unpackGeneration, first, second, third, fourth, ↓reduceIte,
            encoding, no0, no1, no2]
          dsimp [classThreeFirst] at *
          omega
        · have invalid := valid.2.1
          simp only [unpackHandle, first, second, third, fourth, ↓reduceIte] at invalid
          omega

theorem encode_of_decode {word : BitVec 64} {token : Token}
    (decoded : decode? word = some token) : encode token = word := by
  unfold decode? at decoded
  dsimp only at decoded
  split at decoded
  · rename_i admitted
    cases Option.some.inj decoded
    apply BitVec.eq_of_toNat_eq
    rw [encode_toNat admitted.2]
    exact encoding_unpack admitted.1 admitted.2
  · cases decoded

/-- The branch tests, shifts and masks used by `cetta_frame_identity_parts`.
The width premise is the actual `uint32_t` input boundary. -/
theorem packedHandle_eq_native_bits (word : BitVec 64) (width : word.toNat < 2 ^ 32) :
    packedHandle word =
      if word.toNat >>> 31 = 0 then word.toNat &&& (2 ^ 20 - 1)
      else if word.toNat >>> 30 = 2 then classOneFirst + (word.toNat &&& (2 ^ 24 - 1))
      else if word.toNat >>> 29 = 6 then classTwoFirst + (word.toNat &&& (2 ^ 26 - 1))
      else if word.toNat >>> 28 = 14 then classThreeFirst + (word.toNat &&& (2 ^ 26 - 1))
      else handleLimit + (word.toNat &&& (2 ^ 28 - 1)) := by
  simp only [packedHandle, unpackHandle, Nat.shiftRight_eq_div_pow,
    Nat.and_two_pow_sub_one_eq_mod]
  split_ifs <;> omega

theorem packedGeneration_eq_native_bits (word : BitVec 64)
    (width : word.toNat < 2 ^ 32) :
    packedGeneration word =
      if word.toNat >>> 31 = 0 then word.toNat >>> 20
      else if word.toNat >>> 30 = 2 then (word.toNat >>> 24) &&& (2 ^ 6 - 1)
      else if word.toNat >>> 29 = 6 then (word.toNat >>> 26) &&& (2 ^ 3 - 1)
      else if word.toNat >>> 28 = 14 then (word.toNat >>> 26) &&& (2 ^ 2 - 1)
      else 0 := by
  simp only [packedGeneration, unpackGeneration, Nat.shiftRight_eq_div_pow,
    Nat.and_two_pow_sub_one_eq_mod]
  split_ifs <;> omega

private theorem pack_or {bits low : Nat} (bound : low < 2 ^ bits) (high : Nat) :
    high * 2 ^ bits + low = (high <<< bits) ||| low := by
  simpa [Nat.shiftLeft_eq, Nat.mul_comm] using Nat.two_pow_add_eq_or_of_lt bound high

private theorem pack_three {bits genBits generation offset : Nat}
    (low : offset < 2 ^ bits) (gen : generation < 2 ^ genBits) (tag : Nat) :
    tag * 2 ^ (bits + genBits) + generation * 2 ^ bits + offset =
      (tag <<< (bits + genBits)) ||| (generation <<< bits) ||| offset := by
  have middle : generation * 2 ^ bits < 2 ^ (bits + genBits) := by
    simpa [Nat.pow_add, Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right gen (Nat.two_pow_pos bits)
  have top := pack_or middle tag
  have bottom := pack_or low (tag * 2 ^ genBits + generation)
  simp only [Nat.shiftLeft_eq] at top bottom ⊢
  rw [← top]
  have factor : (tag * 2 ^ genBits + generation) * 2 ^ bits =
      tag * 2 ^ (bits + genBits) + generation * 2 ^ bits := by
    rw [Nat.add_mul, Nat.pow_add]
    ac_rfl
  rw [factor] at bottom
  exact bottom

/-- Native packing uses class prefixes and non-overlapping generation/local bits. -/
def nativeSpelling (token : Token) : Nat :=
  if token.handle < classOneFirst then (token.generation <<< 20) ||| token.handle
  else if token.handle < classTwoFirst then
    (2 <<< 30) ||| (token.generation <<< 24) ||| (token.handle - classOneFirst)
  else if token.handle < classThreeFirst then
    (6 <<< 29) ||| (token.generation <<< 26) ||| (token.handle - classTwoFirst)
  else (14 <<< 28) ||| (token.generation <<< 26) ||| (token.handle - classThreeFirst)

theorem encoding_eq_nativeSpelling {token : Token} (valid : Representable token) :
    encoding token = nativeSpelling token := by
  by_cases first : token.handle < classOneFirst
  · simpa [encoding, nativeSpelling, first] using pack_or first token.generation
  · by_cases second : token.handle < classTwoFirst
    · have gen : token.generation < 2 ^ 6 := by
        have := valid.2.2.2; simp only [generationMax, first, second, ↓reduceIte] at this; omega
      have low : token.handle - classOneFirst < 2 ^ 24 := by
        dsimp [classOneFirst, classTwoFirst] at *; omega
      simpa [encoding, nativeSpelling, first, second] using pack_three low gen 2
    · by_cases third : token.handle < classThreeFirst
      · have gen : token.generation < 2 ^ 3 := by
          have := valid.2.2.2; simp only [generationMax, first, second, third, ↓reduceIte] at this; omega
        have low : token.handle - classTwoFirst < 2 ^ 26 := by
          dsimp [classTwoFirst, classThreeFirst] at *; omega
        simpa [encoding, nativeSpelling, first, second, third] using pack_three low gen 6
      · have gen : token.generation < 2 ^ 2 := by
          have := valid.2.2.2; simp only [generationMax, first, second, third, ↓reduceIte] at this; omega
        have low : token.handle - classThreeFirst < 2 ^ 26 := by
          have last := valid.2.1; dsimp [classThreeFirst, handleLimit] at *; omega
        simpa [encoding, nativeSpelling, first, second, third] using pack_three low gen 14

theorem encode_eq_shift_or {token : Token} (valid : Representable token) :
    encode token = BitVec.ofNat 64 (nativeSpelling token) := by
  rw [encode, encoding_eq_nativeSpelling valid]

theorem all_four_classes_roundtrip :
    decode? (encode ⟨1, 2046⟩) = some ⟨1, 2046⟩ ∧
    decode? (encode ⟨classOneFirst, 62⟩) = some ⟨classOneFirst, 62⟩ ∧
    decode? (encode ⟨classTwoFirst, 6⟩) = some ⟨classTwoFirst, 6⟩ ∧
    decode? (encode ⟨classThreeFirst, 2⟩) = some ⟨classThreeFirst, 2⟩ := by decide

theorem old_flat_code_is_not_current_class_zero :
    decode? 4293918719 = none ∧
    ¬ Representable ⟨1048575, 4094⟩ := by decide


/-- Identity-only inventory names retain all bits; source-ID width and schema
admission remain separate. Presentation spelling does not enter this encoder. -/
def sourceIdName (word : BitVec 64) : String :=
  String.ofList ((List.range 64).map
    (fun index => if word.getLsbD index then '1' else '0'))

theorem sourceIdName_injective : Function.Injective sourceIdName := by
  intro first second same
  have bits := String.ofList_injective same
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  have characters := congrArg (fun rows : List Char => rows[index]?) bits
  simp only [List.getElem?_map, List.getElem?_range bound, Option.map_some] at characters
  have observed := Option.some.inj characters
  exact (by decide : Function.Injective (fun bit : Bool => if bit then '1' else '0')) observed

theorem sourceIdName_length (word : BitVec 64) : (sourceIdName word).length = 64 := by
  simp [sourceIdName, ← String.length_toList]

/-- Equal presentations cannot merge distinct source identities. -/
theorem distinct_source_ids_have_distinct_names :
    sourceIdName 17 ≠ sourceIdName 25 := by
  intro same
  have words := sourceIdName_injective same
  exact (by decide : (17 : BitVec 64) ≠ 25) words

theorem decode?_some_iff (word : BitVec 64) (token : Token) :
    decode? word = some token ↔
      word.toNat < 2 ^ 32 ∧ Representable token ∧
        token.handle = packedHandle word ∧ token.generation = packedGeneration word := by
  unfold decode?
  dsimp only
  split
  · next valid =>
    constructor
    · intro same
      cases Option.some.inj same
      exact ⟨valid.1, valid.2, rfl, rfl⟩
    · rintro ⟨_, _, handle, generation⟩
      congr 1
      cases token
      simp_all
  · next invalid =>
    constructor
    · simp
    · rintro ⟨width, tokenValid, handle, generation⟩
      apply False.elim
      apply invalid
      refine ⟨width, ?_⟩
      simpa [Representable, handle, generation] using tokenValid

theorem decoded_representable {word : BitVec 64} {token : Token}
    (decoded : decode? word = some token) : Representable token :=
  ((decode?_some_iff word token).mp decoded).2.1

theorem encode_injective {first second : Token}
    (firstValid : Representable first) (secondValid : Representable second)
    (same : encode first = encode second) : first = second := by
  have decoded := congrArg decode? same
  rw [decode_encode firstValid, decode_encode secondValid] at decoded
  exact Option.some.inj decoded

theorem decode?_none_of_upper_bits {word : BitVec 64} (wide : 2 ^ 32 ≤ word.toNat) :
    decode? word = none := by
  unfold decode?
  dsimp only
  rw [if_neg (fun valid => (Nat.not_lt.mpr wide) valid.1)]

theorem decode?_none_of_zero_handle {word : BitVec 64} (zero : packedHandle word = 0) :
    decode? word = none := by
  simp [decode?, Representable, zero]

theorem decode?_none_of_zero_generation {word : BitVec 64}
    (zero : packedGeneration word = 0) : decode? word = none := by
  simp [decode?, Representable, zero]

theorem decode?_none_of_reserved_generation {word : BitVec 64}
    (reserved : generationMax (packedHandle word) < packedGeneration word) : decode? word = none := by
  simp [decode?, Representable, Nat.not_le.mpr reserved]

/-- Each issued class retains both its first and last admitted spelling. -/
theorem codec_native_endpoints :
    decode? 0x00100001 = some ⟨1, 1⟩ ∧
    decode? 0x7fefffff = some ⟨classOneFirst - 1, 2046⟩ ∧
    decode? 0x81000000 = some ⟨classOneFirst, 1⟩ ∧
    decode? 0xbeffffff = some ⟨classTwoFirst - 1, 62⟩ ∧
    decode? 0xc4000000 = some ⟨classTwoFirst, 1⟩ ∧
    decode? 0xdbffffff = some ⟨classThreeFirst - 1, 6⟩ ∧
    decode? 0xe4000000 = some ⟨classThreeFirst, 1⟩ ∧
    decode? 0xebffffff = some ⟨handleLimit - 1, 2⟩ := by decide

theorem codec_rejects_each_class_reserved_generation :
    decode? 0x7ff00001 = none ∧ decode? 0xbf000000 = none ∧
    decode? 0xdc000000 = none ∧ decode? 0xec000000 = none ∧
    decode? 0xf0000000 = none ∧ decode? 0x80000000 = none ∧
    decode? 0xc0000000 = none ∧ decode? 0xe0000000 = none := by decide

theorem codec_rejects_ambient_and_malformed :
    decode? 0 = none ∧ decode? 1 = none ∧
      decode? (BitVec.ofNat 64 1048576) = none ∧
      decode? (BitVec.ofNat 64 4293918721) = none ∧
      decode? (BitVec.ofNat 64 4294967297) = none := by decide

/-- A previous generation is still representable. Decoding keeps it distinct;
the containing image or an ownership authority must determine staleness. -/
theorem codec_keeps_previous_generation_distinct :
    decode? (encode ⟨17, 1⟩) = some ⟨17, 1⟩ ∧
      decode? (encode ⟨17, 2⟩) = some ⟨17, 2⟩ ∧
      encode ⟨17, 1⟩ ≠ encode ⟨17, 2⟩ := by decide

private def currentGenerationImage :
    Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.ImageOf Nat :=
  ⟨(Array.replicate 18 none).setIfInBounds 17
      (some (Mettapedia.Languages.MeTTa.MetavariableFrameStore.EntryOf.initial
        2 ["x"] (fun _ => some 7))), 0⟩

/-- Structural decoding accepts the old token; the existing image rejects its
generation while reading the current incarnation. No allocator is synthesized. -/
theorem codec_stale_token_rejected_by_image :
    (decode? (encode ⟨17, 1⟩)).bind
      (fun token => currentGenerationImage.lookup (token.ref 0)) = none ∧
    (decode? (encode ⟨17, 2⟩)).bind
      (fun token => currentGenerationImage.lookup (token.ref 0)) = some (some 7) := by decide

/-! ## Borrowed current-frame readback

These readers consume the logical record layouts of `match.h`. They retain
raw pointer aliases and value tags; they neither traverse Atom storage nor
acquire an owner. A complete frame inventory is checked against its advertised
slot count. A collection of such frames is not yet a complete binding world:
directory enumeration, unchanged-image validity, unframed bindings and
constraints remain separate obligations.
-/

open Mettapedia.Languages.MeTTa.MetavariableFrameStore

def bindingValueFields : List Parameter :=
  [⟨"skeleton", .ref (.named "Atom")⟩, ⟨"epoch", .word⟩, ⟨"kind", .word⟩]

def frameDirectoryFields : List Parameter :=
  [⟨"bindings", .ref (.named "Bindings")⟩,
   ⟨"directory", .ref (.named "BindingsFrameIndex")⟩,
   ⟨"frame_count", .word⟩, ⟨"schema_revision", .word⟩, ⟨"write_clock", .word⟩]

def frameStateFields : List Parameter :=
  [⟨"bindings", .ref (.named "Bindings")⟩,
   ⟨"directory", .ref (.named "BindingsFrameIndex")⟩,
   ⟨"ref", .named "BindingsFrameRef"⟩,
   ⟨"slot_count", .word⟩, ⟨"schema_slot_count", .word⟩,
   ⟨"schema_revision", .word⟩, ⟨"write_clock", .word⟩,
   ⟨"activation_write_boundary", .word⟩,
   ⟨"has_activation_write_boundary", .bool⟩,
   ⟨"schema_complete", .bool⟩, ⟨"owns_identity", .bool⟩]

def frameSlotFields : List Parameter :=
  [⟨"source_id", .word⟩, ⟨"var_id", .word⟩, ⟨"spelling", .word⟩,
   ⟨"name_key", .ref (.named "Atom")⟩, ⟨"declared_in_schema", .bool⟩,
   ⟨"value", .named "BindingValue"⟩, ⟨"write_version", .word⟩]

/-- Even a null skeleton retains its raw epoch and kind in the sidecar. -/
structure BindingValueView where
  skeleton : Option Address
  epoch : BitVec 64
  kind : BitVec 64
  deriving DecidableEq, Repr

def BindingValueView.Admissible (value : BindingValueView) : Prop :=
  value.epoch.toNat < 2 ^ 32 ∧ value.kind.toNat ≤ 2

instance (value : BindingValueView) : Decidable value.Admissible := by
  unfold BindingValueView.Admissible
  infer_instance

def readBindingValue? : TargetValue → Option BindingValueView
  | .record "BindingValue" [.reference skeleton, .word epoch, .word kind] =>
      let value : BindingValueView := ⟨skeleton, epoch, kind⟩
      if value.Admissible then some value else none
  | _ => none

/-- The ordered logical record used at by-value C invocation boundaries.
This preserves a null skeleton's epoch and tag without acquiring ownership. -/
def BindingValueView.toTarget (value : BindingValueView) : TargetValue :=
  .record "BindingValue" [.reference value.skeleton, .word value.epoch, .word value.kind]

theorem readBindingValue?_toTarget (value : BindingValueView) :
    readBindingValue? value.toTarget =
      if value.Admissible then some value else none := by
  cases value
  rfl

/-- A successful decoder retains the complete input record, rather than
projecting only its pointer or changing its contextual tag. -/
theorem readBindingValue?_representation {record : TargetValue} {value : BindingValueView}
    (read : readBindingValue? record = some value) : value.toTarget = record := by
  unfold readBindingValue? at read
  split at read
  · dsimp only at read
    split at read
    · cases Option.some.inj read
      rfl
    · simp at read
  · simp at read

/-- Boundness depends only on the skeleton, independently of contextual tags. -/
def BindingValueView.payload (value : BindingValueView) : Option BindingValueView :=
  if value.skeleton.isSome then some value else none

@[simp] theorem BindingValueView.payload_unbound (epoch kind : BitVec 64) :
    (⟨none, epoch, kind⟩ : BindingValueView).payload = none := rfl

@[simp] theorem BindingValueView.payload_bound (address : Address) (epoch kind : BitVec 64) :
    (⟨some address, epoch, kind⟩ : BindingValueView).payload =
      some ⟨some address, epoch, kind⟩ := rfl

/-- Directory readings do not depend on the existence of a frame row. -/
structure FrameDirectoryView where
  bindings : Address
  directory : Option Address
  frameCount : Nat
  schemaRevision : Nat
  writeClock : Nat
  deriving DecidableEq, Repr

def FrameDirectoryView.Admissible (view : FrameDirectoryView) : Prop :=
  view.frameCount < 2 ^ 32 ∧ view.schemaRevision < 2 ^ 64 ∧
    view.writeClock < 2 ^ 64 ∧
    (view.directory = none → view.frameCount = 0 ∧
      view.schemaRevision = 0 ∧ view.writeClock = 0)

instance (view : FrameDirectoryView) : Decidable view.Admissible := by
  unfold FrameDirectoryView.Admissible
  infer_instance

def readFrameDirectory? : TargetValue → Option FrameDirectoryView
  | .record "BindingsFrameDirectoryStateView"
      [.reference (some bindings), .reference directory, .word count,
       .word revision, .word clock] =>
      let view : FrameDirectoryView :=
        ⟨bindings, directory, count.toNat, revision.toNat, clock.toNat⟩
      if view.Admissible then some view else none
  | _ => none

structure FrameStateView where
  bindings : Address
  directory : Address
  token : Token
  slotCount : Nat
  schemaSlotCount : Nat
  schemaRevision : Nat
  writeClock : Nat
  activationWriteBoundary : Nat
  hasActivationWriteBoundary : Bool
  schemaComplete : Bool
  ownsIdentity : Bool
  deriving DecidableEq, Repr

def FrameStateView.Admissible (view : FrameStateView) : Prop :=
  Representable view.token ∧ 0 < view.schemaSlotCount ∧
    view.schemaSlotCount ≤ view.slotCount ∧ view.slotCount < 2 ^ 32 ∧
    view.schemaRevision < 2 ^ 64 ∧ view.writeClock < 2 ^ 64 ∧
    view.activationWriteBoundary < 2 ^ 64

instance (view : FrameStateView) : Decidable view.Admissible := by
  unfold FrameStateView.Admissible
  infer_instance

def FrameStateView.boundary (view : FrameStateView) : Option Nat :=
  if view.hasActivationWriteBoundary then some view.activationWriteBoundary else none

def readFrameState? : TargetValue → Option FrameStateView
  | .record "BindingsFrameStateView"
      [.reference (some bindings), .reference (some directory),
       .record "BindingsFrameRef" [.word identity], .word slots, .word schemaSlots,
       .word revision, .word clock, .word boundary, .bool hasBoundary,
       .bool complete, .bool owns] => do
      let token ← decode? identity
      let view : FrameStateView := ⟨bindings, directory, token, slots.toNat,
        schemaSlots.toNat, revision.toNat, clock.toNat, boundary.toNat,
        hasBoundary, complete, owns⟩
      if view.Admissible then some view else none
  | _ => none

structure FrameSlotView where
  sourceId : BitVec 64
  varId : BitVec 64
  spelling : BitVec 64
  nameKey : Option Address
  declaredInSchema : Bool
  value : BindingValueView
  writeVersion : Nat
  deriving DecidableEq, Repr

def FrameSlotView.Admissible (slot : FrameSlotView) : Prop :=
  0 < slot.sourceId.toNat ∧ slot.sourceId.toNat < 2 ^ 32 ∧
    slot.spelling.toNat < 2 ^ 32 ∧ slot.value.Admissible ∧ slot.writeVersion < 2 ^ 64

instance (slot : FrameSlotView) : Decidable slot.Admissible := by
  unfold FrameSlotView.Admissible
  infer_instance

def readFrameSlot? : TargetValue → Option FrameSlotView
  | .record "BindingsFrameSlotStateView"
      [.word sourceId, .word varId, .word spelling, .reference nameKey,
       .bool declared, value, .word version] => do
      let value ← readBindingValue? value
      let slot : FrameSlotView := ⟨sourceId, varId, spelling, nameKey,
        declared, value, version.toNat⟩
      if slot.Admissible then some slot else none
  | _ => none

/-- Qualification uses the full packed epoch shifted by 32, not the handle
bits or the iterator position. Grown inventories are dense from source ID 1. -/
def FrameSlotView.Agrees (view : FrameStateView) (index : Nat) (slot : FrameSlotView) : Prop :=
  slot.Admissible ∧ index < view.slotCount ∧
    slot.varId.toNat = (encode view.token).toNat * 2 ^ 32 + slot.sourceId.toNat ∧
    slot.declaredInSchema = decide (index < view.schemaSlotCount) ∧
    (view.schemaSlotCount < view.slotCount → slot.sourceId.toNat = index + 1) ∧
    (view.schemaSlotCount ≤ index → slot.spelling = 0 ∧ slot.nameKey = none)

instance (view : FrameStateView) (index : Nat) (slot : FrameSlotView) :
    Decidable (slot.Agrees view index) := by
  unfold FrameSlotView.Agrees
  infer_instance

def InventoryAgrees (view : FrameStateView) (slots : List FrameSlotView) : Prop :=
  view.Admissible ∧ slots.length = view.slotCount ∧
    slots.Pairwise (fun first second => first.sourceId.toNat < second.sourceId.toNat) ∧
    ∀ index : Fin slots.length, (slots[index.val]).Agrees view index.val

instance (view : FrameStateView) (slots : List FrameSlotView) :
    Decidable (InventoryAgrees view slots) := by
  unfold InventoryAgrees
  infer_instance

/-- Raw slots remain available beside the common carrier, including metadata
of null payloads and presentation absent from grown slots. -/
structure FrameReadback where
  view : FrameStateView
  slots : List FrameSlotView
  admitted : InventoryAgrees view slots

def readFrameSlots? : List TargetValue → Option (List FrameSlotView)
  | [] => some []
  | value :: rest => do
      let slot ← readFrameSlot? value
      let slots ← readFrameSlots? rest
      some (slot :: slots)

def readFrame? (header : TargetValue) (rows : List TargetValue) : Option FrameReadback := do
  let view ← readFrameState? header
  let slots ← readFrameSlots? rows
  if admitted : InventoryAgrees view slots then some ⟨view, slots, admitted⟩ else none

/-- Coordinates retain native source identity; presentation is not identity. -/
def FrameReadback.toEntry (readback : FrameReadback) : EntryOf BindingValueView where
  generation := readback.view.token.generation
  frame := readback.slots.map (fun slot => sourceIdName slot.sourceId)
  values := (readback.slots.map (fun slot => slot.value.payload)).toArray
  size_eq := by simp
  writeVersions := (readback.slots.map FrameSlotView.writeVersion).toArray
  versions_size_eq := by simp
  activationBoundary := readback.view.boundary

theorem FrameReadback.inventory_count (readback : FrameReadback) :
    readback.slots.length = readback.view.slotCount := readback.admitted.2.1

theorem FrameReadback.slot_agrees (readback : FrameReadback) (index : Fin readback.slots.length) :
    readback.slots[index.val].Agrees readback.view index.val := readback.admitted.2.2.2 index

/-- The constructed common entry reads the exact raw value option and lineage
at every supplied slot. Unbound values retain their separate write versions. -/
theorem FrameReadback.toEntry_readSlot (readback : FrameReadback)
    (index : Fin readback.slots.length) :
    readback.toEntry.readSlot? readback.view.writeClock index.val =
      some ⟨readback.slots[index.val].value.payload,
        readback.slots[index.val].writeVersion, readback.view.writeClock,
        readback.view.boundary⟩ := by
  simp [FrameReadback.toEntry, EntryOf.readSlot?, index.isLt]

theorem FrameReadback.toEntry_generation (readback : FrameReadback) :
    readback.toEntry.generation = readback.view.token.generation := rfl

theorem FrameReadback.toEntry_frame_nodup (readback : FrameReadback) :
    readback.toEntry.frame.Nodup := by
  have sources : (readback.slots.map FrameSlotView.sourceId).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    apply List.Pairwise.imp ?_ readback.admitted.2.2.1
    intro first second ordered same
    have sameNat := congrArg BitVec.toNat same
    omega
  have names := List.Nodup.map (f := sourceIdName) sourceIdName_injective sources
  simpa only [FrameReadback.toEntry, List.map_map, Function.comp_def] using names

theorem readBindingValue?_sound {record : TargetValue} {value : BindingValueView}
    (read : readBindingValue? record = some value) : value.Admissible := by
  unfold readBindingValue? at read
  split at read
  · dsimp only at read
    split at read
    · next valid => cases Option.some.inj read; exact valid
    · simp at read
  · simp at read

theorem readFrameSlots?_length {rows : List TargetValue} {slots : List FrameSlotView}
    (read : readFrameSlots? rows = some slots) : slots.length = rows.length := by
  induction rows generalizing slots with
  | nil => simpa [readFrameSlots?] using read.symm
  | cons value rest ih =>
    obtain ⟨slot, _, read⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨tail, parsed, same⟩ := Option.bind_eq_some_iff.mp read
    cases Option.some.inj same
    simpa only [List.length_cons] using congrArg Nat.succ (ih parsed)

/-- Accepted records contain exactly the advertised number of supplied rows.
This does not turn an arbitrary supplied frame list into a complete directory. -/
theorem readFrame?_count {header : TargetValue} {rows : List TargetValue}
    {readback : FrameReadback} (read : readFrame? header rows = some readback) :
    rows.length = readback.view.slotCount := by
  obtain ⟨view, _, read⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨slots, parsed, read⟩ := Option.bind_eq_some_iff.mp read
  split at read
  · next admitted =>
    cases Option.some.inj read
    exact (readFrameSlots?_length parsed).symm.trans admitted.2.1
  · simp at read

theorem FrameReadback.toEntry_readSlot_unbound (readback : FrameReadback)
    (index : Fin readback.slots.length)
    (unbound : readback.slots[index.val].value.skeleton = none) :
    readback.toEntry.readSlot? readback.view.writeClock index.val =
      some ⟨none, readback.slots[index.val].writeVersion, readback.view.writeClock,
        readback.view.boundary⟩ := by
  rw [readback.toEntry_readSlot index]
  simp [BindingValueView.payload, unbound]

theorem FrameReadback.toEntry_readSlot_outside (readback : FrameReadback) (index : Nat)
    (outside : readback.slots.length ≤ index) :
    readback.toEntry.readSlot? readback.view.writeClock index = none := by
  simp [FrameReadback.toEntry, EntryOf.readSlot?, Nat.not_lt.mpr outside]

/-- The existing lineage carrier supplies the activation observer; no second
definition of write history is introduced by native decoding. -/
def FrameReadback.lineage (readback : FrameReadback) :
    Mettapedia.Languages.MeTTa.MetavariableFrameLineage.Frame
      (Option BindingValueView) readback.toEntry.frame.length :=
  Mettapedia.Languages.MeTTa.MetavariableFrameLineage.Frame.ofEntry
    readback.view.writeClock readback.toEntry

def FrameReadback.slot (readback : FrameReadback) (index : Fin readback.slots.length) :
    Mettapedia.Languages.MeTTa.MetavariableFrame.Slot readback.toEntry.frame :=
  ⟨index.val, by
    change index.val < (readback.slots.map (fun slot => sourceIdName slot.sourceId)).length
    rw [List.length_map]
    exact index.isLt⟩

theorem FrameReadback.lineage_slot (readback : FrameReadback)
    (index : Fin readback.slots.length) :
    readback.lineage.slots (readback.slot index) =
      some (readback.slots[index.val].value.payload,
        readback.slots[index.val].writeVersion) := by
  unfold FrameReadback.lineage
  rw [← Mettapedia.Languages.MeTTa.MetavariableFrameLineage.Frame.ofEntry_readSlot]
  simp only [FrameReadback.slot]
  rw [readback.toEntry_readSlot index]
  rfl

theorem FrameReadback.lineage_output (readback : FrameReadback)
    (index : Fin readback.slots.length) :
    (readback.lineage.output (readback.slot index)).join =
      if readback.view.boundary.all (fun boundary =>
          decide (boundary < readback.slots[index.val].writeVersion))
        then readback.slots[index.val].value.payload else none := by
  unfold FrameReadback.lineage
  rw [Mettapedia.Languages.MeTTa.MetavariableFrameLineage.Frame.ofEntry_output]
  simp only [FrameReadback.slot]
  rw [readback.toEntry_readSlot index]
  rfl

def FrameStateView.Compatible (view : FrameStateView) (directory : FrameDirectoryView) : Prop :=
  view.bindings = directory.bindings ∧ some view.directory = directory.directory ∧
    view.schemaRevision = directory.schemaRevision ∧ view.writeClock = directory.writeClock

instance (view : FrameStateView) (directory : FrameDirectoryView) :
    Decidable (view.Compatible directory) := by
  unfold FrameStateView.Compatible
  infer_instance

def DirectoryAgrees (directory : FrameDirectoryView) (capacity : Nat)
    (frames : List FrameReadback) : Prop :=
  directory.Admissible ∧ frames.length = directory.frameCount ∧
    (frames.map (fun frame => frame.view.token.handle)).Nodup ∧
    ∀ index : Fin frames.length,
      frames[index.val].view.Compatible directory ∧ frames[index.val].view.token.handle < capacity

instance (directory : FrameDirectoryView) (capacity : Nat) (frames : List FrameReadback) :
    Decidable (DirectoryAgrees directory capacity frames) := by
  unfold DirectoryAgrees
  infer_instance

/-- Advertised cardinality, common borrowed headers and distinct handles are
checked together. This does not establish that the native iterator actually
supplied these records or that their storage stayed unchanged during reads. -/
structure DirectoryReadback where
  directory : FrameDirectoryView
  capacity : Nat
  frames : List FrameReadback
  admitted : DirectoryAgrees directory capacity frames

def readFrames? : List (TargetValue × List TargetValue) → Option (List FrameReadback)
  | [] => some []
  | (header, rows) :: rest => do
      let frame ← readFrame? header rows
      let frames ← readFrames? rest
      some (frame :: frames)

def readDirectory? (header : TargetValue) (capacity : Nat)
    (records : List (TargetValue × List TargetValue)) : Option DirectoryReadback := do
  let directory ← readFrameDirectory? header
  let frames ← readFrames? records
  if admitted : DirectoryAgrees directory capacity frames then
    some ⟨directory, capacity, frames, admitted⟩ else none

/-- The native owning vector is unordered. Its handles select common entries;
the enumeration position never becomes a lexical coordinate. -/
def DirectoryReadback.toImage (readback : DirectoryReadback) : Shared.ImageOf BindingValueView :=
  ⟨Array.ofFn (fun handle : Fin readback.capacity =>
    (readback.frames.find? (fun frame => frame.view.token.handle == handle.val)).map
      FrameReadback.toEntry), readback.directory.writeClock⟩

theorem DirectoryReadback.inventory_count (readback : DirectoryReadback) :
    readback.frames.length = readback.directory.frameCount := readback.admitted.2.1

theorem DirectoryReadback.frame_agrees (readback : DirectoryReadback)
    (frame : FrameReadback) (member : frame ∈ readback.frames) :
    frame.view.Compatible readback.directory ∧ frame.view.token.handle < readback.capacity := by
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have facts := readback.admitted.2.2.2 ⟨index, bound⟩
  simpa only [same] using facts

theorem DirectoryReadback.toImage_frameAt (readback : DirectoryReadback)
    (handle : Nat) (bound : handle < readback.capacity) :
    readback.toImage.frameAt handle =
      (readback.frames.find? (fun frame => frame.view.token.handle == handle)).map
        FrameReadback.toEntry := by
  change ((Array.ofFn (fun h : Fin readback.capacity =>
    (readback.frames.find? (fun frame => frame.view.token.handle == h.val)).map
      FrameReadback.toEntry))[handle]?).getD none = _
  simp [bound]

private theorem selectHandle_of_mem {frames : List FrameReadback} {frame : FrameReadback}
    (distinct : (frames.map (fun row => row.view.token.handle)).Nodup)
    (member : frame ∈ frames) :
    frames.find? (fun row => row.view.token.handle == frame.view.token.handle) = some frame := by
  induction frames with
  | nil => simp at member
  | cons first rest ih =>
    have nodup : first.view.token.handle ∉ rest.map (fun row => row.view.token.handle) ∧
        (rest.map (fun row => row.view.token.handle)).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using distinct
    rcases List.mem_cons.mp member with same | member
    · subst frame
      simp
    · have different : first.view.token.handle ≠ frame.view.token.handle := by
        intro same
        exact nodup.1 (List.mem_map.mpr ⟨frame, member, same.symm⟩)
      have miss : (first.view.token.handle == frame.view.token.handle) = false :=
        beq_eq_false_iff_ne.mpr different
      rw [List.find?_cons, miss]
      exact ih nodup.2 member

theorem DirectoryReadback.select_frame (readback : DirectoryReadback)
    (frame : FrameReadback) (member : frame ∈ readback.frames) :
    readback.frames.find? (fun row => row.view.token.handle == frame.view.token.handle) =
      some frame := selectHandle_of_mem readback.admitted.2.2.1 member

/-- The assembled image retains exactly the selected frame's indexed read and
the common directory clock. Selection still checks the actual native handle. -/
theorem DirectoryReadback.toImage_readSlot (readback : DirectoryReadback)
    (frame : FrameReadback) (member : frame ∈ readback.frames) (index : Nat) :
    readback.toImage.readSlot? (frame.view.token.ref index) =
      frame.toEntry.readSlot? frame.view.writeClock index := by
  have selected := readback.select_frame frame member
  have facts := readback.frame_agrees frame member
  have present := readback.toImage_frameAt frame.view.token.handle facts.2
  rw [selected, Option.map_some] at present
  change MetavariableFrameStore.frameAt
    ⟨readback.toImage.entries, 0, readback.directory.writeClock⟩
      frame.view.token.handle = some frame.toEntry at present
  change MetavariableFrameStore.readSlot?
    ⟨readback.toImage.entries, 0, readback.directory.writeClock⟩
      (frame.view.token.ref index) = _
  rw [MetavariableFrameStore.readSlot?_of_frameAt present rfl, facts.1.2.2.2]
  rfl

theorem DirectoryReadback.toImage_clock (readback : DirectoryReadback) :
    readback.toImage.writeClock = readback.directory.writeClock := rfl

/-! ### Contextual variable edges

The native variable helper either retains a materialized identifier or replaces
its high word by the stored contextual epoch. It does not combine two epochs.
The zero-base contextual case calls the native fresh-identity service, so it is
outside this pure inspection fragment. Directory selection is explicit: decoding
a lexical coordinate does not choose a branch image or acquire force rights.
-/

def variableRadix : Nat := 2 ^ 32

def variableBase (word : BitVec 64) : Nat := word.toNat % variableRadix

def variableEpoch (word : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (word.toNat / variableRadix)

/-- Exact native qualification on nonzero source bases. The materialized case
retains the whole identifier, including any existing frame suffix. -/
def BindingValueView.variableId? (value : BindingValueView) (source : BitVec 64) :
    Option (BitVec 64) :=
  if value.Admissible then
    if value.kind = 0 then some source
    else if variableBase source = 0 then none
    else some (BitVec.ofNat 64 (value.epoch.toNat * variableRadix + variableBase source))
  else none

theorem BindingValueView.variableId_materialized (value : BindingValueView)
    (valid : value.Admissible) (materialized : value.kind = 0) (source : BitVec 64) :
    value.variableId? source = some source := by
  simp only [BindingValueView.variableId?, valid, materialized, ite_true]

theorem BindingValueView.variableId_contextual (value : BindingValueView)
    (valid : value.Admissible) (contextual : value.kind ≠ 0)
    (source : BitVec 64) (nonzero : variableBase source ≠ 0) :
    value.variableId? source =
      some (BitVec.ofNat 64 (value.epoch.toNat * variableRadix + variableBase source)) := by
  simp only [BindingValueView.variableId?, valid, ite_true, contextual, ite_false, nonzero]

theorem qualifiedVariable_toNat (value : BindingValueView) (valid : value.Admissible)
    (source : BitVec 64) :
    (BitVec.ofNat 64 (value.epoch.toNat * variableRadix + variableBase source)).toNat =
      value.epoch.toNat * variableRadix + variableBase source := by
  rw [BitVec.toNat_ofNat]
  have base : variableBase source < 2 ^ 32 :=
    Nat.mod_lt _ (by decide : 0 < variableRadix)
  have width := valid.1
  have fits : value.epoch.toNat * variableRadix + variableBase source < 2 ^ 64 := by
    dsimp only [variableRadix] at *
    omega
  exact Nat.mod_eq_of_lt fits

theorem qualifiedVariable_base (value : BindingValueView) (valid : value.Admissible)
    (source : BitVec 64) :
    variableBase (BitVec.ofNat 64 (value.epoch.toNat * variableRadix + variableBase source)) =
      variableBase source := by
  rw [variableBase, qualifiedVariable_toNat value valid source,
    Nat.mul_add_mod_self_right]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < variableRadix))

theorem qualifiedVariable_epoch (value : BindingValueView) (valid : value.Admissible)
    (source : BitVec 64) :
    variableEpoch (BitVec.ofNat 64 (value.epoch.toNat * variableRadix + variableBase source)) =
      value.epoch := by
  have baseLess : variableBase source < variableRadix :=
    Nat.mod_lt _ (by decide : 0 < variableRadix)
  rw [variableEpoch, qualifiedVariable_toNat value valid source, Nat.add_comm,
    Nat.add_mul_div_right _ _ (by decide : 0 < variableRadix),
    Nat.div_eq_of_lt baseLess, Nat.zero_add]
  simp

/-- Read only the two observed fields of the actual Atom header: kind at
position 0 and VarId at position 2. The remaining graph is left untouched. -/
def readVariableId? (memory : TargetMemory) (value : BindingValueView) : Option (BitVec 64) := do
  let address ← value.skeleton
  match targetRead memory (sourceFieldAddress address 0) with
  | some (.word kind) =>
      if kind = 1 then
        match targetRead memory (sourceFieldAddress address 2) with
        | some (.word source) => value.variableId? source
        | _ => none
      else none
  | _ => none

theorem readVariableId_nonvariable (memory : TargetMemory) (value : BindingValueView)
    (address : Address) (pointer : value.skeleton = some address) (kind : BitVec 64)
    (loaded : targetRead memory (sourceFieldAddress address 0) = some (.word kind))
    (nonvariable : kind ≠ 1) : readVariableId? memory value = none := by
  change kind ≠ 1#64 at nonvariable
  simp [readVariableId?, pointer, loaded, nonvariable]

theorem readVariableId_variable (memory : TargetMemory) (value : BindingValueView)
    (address : Address) (pointer : value.skeleton = some address) (source : BitVec 64)
    (kind : targetRead memory (sourceFieldAddress address 0) = some (.word 1))
    (identifier : targetRead memory (sourceFieldAddress address 2) = some (.word source)) :
    readVariableId? memory value = value.variableId? source := by
  simp [readVariableId?, pointer, kind, identifier]

/-! ### Ordered expression-child readback

The active expression arm is the declared pointer/count pair. The count is a
native uint64, and the element sequence is read at every advertised index.
Each child keeps the resolved parent's context. A present null child differs
from a missing or mistyped pointer slot; graph admission separately requires
every reachable child to have an admitted node. This logical readback does not
acquire a physical array borrow or evaluate a child.
-/

def expressionView? (memory : TargetMemory) (value : BindingValueView) :
    Option (Option Address × BitVec 64) := do
  if value.Admissible then
    let address ← value.skeleton
    match targetRead memory (sourceFieldAddress address 0) with
    | some (.word 3) =>
        match targetRead memory (sourceFieldAddress address 8) with
        | some (.record "expr" [.reference elements, .word count]) => some (elements, count)
        | _ => none
    | _ => none
  else none

def expressionElement? (memory : TargetMemory) (elements : Option Address) (index : Nat) :
    Option (Option Address) := do
  let address ← elements
  match targetRead memory { address with element := address.element + index } with
  | some (.reference child) => some child
  | _ => none

theorem expressionElement?_iff (memory : TargetMemory) (elements : Option Address)
    (index : Nat) (child : Option Address) :
    expressionElement? memory elements index = some child ↔
      ∃ address, elements = some address ∧
        targetRead memory { address with element := address.element + index } =
          some (.reference child) := by
  unfold expressionElement?
  cases elements with
  | none => simp
  | some address =>
      cases observed : targetRead memory { address with element := address.element + index } with
      | none => simp [observed]
      | some entry => cases entry <;> simp [observed]

/-- The ordinary native cursor child operation changes only its term pointer.
The world is carried separately by the caller, and no new context is inferred. -/
def BindingValueView.child (parent : BindingValueView) (pointer : Option Address) :
    BindingValueView := { parent with skeleton := pointer }

def readExpressionChildren? (memory : TargetMemory) (parent : BindingValueView) :
    Option (List BindingValueView) :=
  (expressionView? memory parent).bind fun header =>
    (Fin.sequenceOption header.2.toNat
      (fun index => expressionElement? memory header.1 index.val)).map
        (fun pointers => List.ofFn fun index => parent.child (pointers index))

/-- The decoded list agrees at every physical element position with the
independent memory reads. In particular, neither order nor repeated pointers
is quotiented by the reader. -/
theorem readExpressionChildren?_iff (memory : TargetMemory) (parent : BindingValueView)
    (children : List BindingValueView) :
    readExpressionChildren? memory parent = some children ↔
      ∃ (elements : Option Address) (count : BitVec 64)
        (pointers : Fin count.toNat → Option Address),
        expressionView? memory parent = some (elements, count) ∧
        (∀ index, expressionElement? memory elements index.val = some (pointers index)) ∧
        children = List.ofFn (fun index => parent.child (pointers index)) := by
  unfold readExpressionChildren?
  constructor
  · intro decoded
    obtain ⟨⟨elements, count⟩, header, decoded⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨pointers, read, equal⟩ := Option.map_eq_some_iff.mp decoded
    exact ⟨elements, count, pointers, header,
      Fin.sequenceOption_sound count.toNat read, equal.symm⟩
  · rintro ⟨elements, count, pointers, header, reads, equal⟩
    obtain ⟨actual, read⟩ := Fin.sequenceOption_complete count.toNat
      (fun index => expressionElement? memory elements index.val)
      (fun index => ⟨pointers index, reads index⟩)
    have same : actual = pointers := by
      funext index
      exact Option.some.inj ((Fin.sequenceOption_sound count.toNat read index).symm.trans
        (reads index))
    subst actual
    simp [header, read, equal]

theorem readExpressionChildren?_length {memory : TargetMemory} {parent : BindingValueView}
    {children : List BindingValueView}
    (decoded : readExpressionChildren? memory parent = some children) :
    ∃ elements count, expressionView? memory parent = some (elements, count) ∧
      children.length = count.toNat := by
  obtain ⟨elements, count, pointers, header, _, rfl⟩ :=
    (readExpressionChildren?_iff _ _ _).mp decoded
  exact ⟨elements, count, header, List.length_ofFn⟩

theorem readExpressionChildren?_context {memory : TargetMemory} {parent : BindingValueView}
    {children : List BindingValueView}
    (decoded : readExpressionChildren? memory parent = some children) :
    ∀ child ∈ children, child.epoch = parent.epoch ∧ child.kind = parent.kind := by
  obtain ⟨_, _, pointers, _, _, rfl⟩ := (readExpressionChildren?_iff _ _ _).mp decoded
  intro child member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact ⟨rfl, rfl⟩

theorem readExpressionChildren?_position {memory : TargetMemory} {parent : BindingValueView}
    {children : List BindingValueView}
    (decoded : readExpressionChildren? memory parent = some children)
    (index : Fin children.length) :
    ∃ elements count, expressionView? memory parent = some (elements, count) ∧
      index.val < count.toNat ∧
      expressionElement? memory elements index.val = some children[index.val].skeleton := by
  obtain ⟨elements, count, pointers, header, reads, rfl⟩ :=
    (readExpressionChildren?_iff _ _ _).mp decoded
  have bounded : index.val < count.toNat := by simpa using index.isLt
  refine ⟨elements, count, header, bounded, ?_⟩
  simpa only [List.getElem_ofFn, BindingValueView.child] using reads ⟨index.val, bounded⟩


/-- Select a source identity in one generation-checked frame. Both contextual
operands and packed variable identifiers use this same inventory lookup. -/
def DirectoryReadback.sourceCoordinate? (directory : DirectoryReadback)
    (epoch source : BitVec 64) :
    Option Ref := do
  let token ← decode? epoch
  let entry ← directory.toImage.frameAt token.handle
  if entry.generation = token.generation then
    let slot ← Mettapedia.Languages.MeTTa.MetavariableFrame.indexOf entry.frame
      (sourceIdName source)
    some (token.ref slot)
  else none

/-- Interpret a packed framed identifier through the existing named inventory.
Ambient identifiers belong to the unframed domain, outside this operation. -/
def DirectoryReadback.variableCoordinate? (directory : DirectoryReadback) (identifier : BitVec 64) :
    Option Ref :=
  directory.sourceCoordinate? (variableEpoch identifier) (BitVec.ofNat 64 (variableBase identifier))

/-- Qualifying a contextual source selects the same frame, generation and
source slot as direct contextual lookup, including missing or stale cases.
The nonzero source condition excludes native fresh-identity allocation. This
is the readback coordinate law, not execution of either C lookup helper. -/
theorem DirectoryReadback.contextual_coordinate (directory : DirectoryReadback)
    (value : BindingValueView) (valid : value.Admissible) (contextual : value.kind ≠ 0)
    (source : BitVec 64) (nonzero : variableBase source ≠ 0) :
    (value.variableId? source).bind directory.variableCoordinate? =
      directory.sourceCoordinate? value.epoch (BitVec.ofNat 64 (variableBase source)) := by
  have qualified := value.variableId_contextual valid contextual source nonzero
  have transported := congrArg
    (fun result : Option (BitVec 64) => result.bind directory.variableCoordinate?) qualified
  have coordinates := congrArg₂ directory.sourceCoordinate?
    (qualifiedVariable_epoch value valid source)
    (congrArg (BitVec.ofNat 64) (qualifiedVariable_base value valid source))
  have applied := Option.bind_some
    (BitVec.ofNat 64 (value.epoch.toNat * variableRadix + variableBase source))
    directory.variableCoordinate?
  have expanded : directory.variableCoordinate?
      (BitVec.ofNat 64 (value.epoch.toNat * variableRadix + variableBase source)) =
      directory.sourceCoordinate?
        (variableEpoch (BitVec.ofNat 64 (value.epoch.toNat * variableRadix + variableBase source)))
        (BitVec.ofNat 64 (variableBase (BitVec.ofNat 64
          (value.epoch.toNat * variableRadix + variableBase source)))) := rfl
  exact transported.trans (applied.trans (expanded.trans coordinates))

def DirectoryReadback.readVariableSlot? (directory : DirectoryReadback)
    (memory : TargetMemory) (value : BindingValueView) : Option (SlotReadbackOf BindingValueView) := do
  let identifier ← readVariableId? memory value
  let coordinate ← directory.variableCoordinate? identifier
  directory.toImage.readSlot? coordinate

theorem DirectoryReadback.variableCoordinate_stale (directory : DirectoryReadback)
    (identifier : BitVec 64) (token : Token) (entry : EntryOf BindingValueView)
    (decoded : decode? (variableEpoch identifier) = some token)
    (present : directory.toImage.frameAt token.handle = some entry)
    (stale : entry.generation ≠ token.generation) :
    directory.variableCoordinate? identifier = none := by
  simp [DirectoryReadback.variableCoordinate?, DirectoryReadback.sourceCoordinate?, decoded, present, stale]

theorem DirectoryReadback.variableCoordinate_current (directory : DirectoryReadback)
    (identifier : BitVec 64) (token : Token) (entry : EntryOf BindingValueView) (slot : Nat)
    (decoded : decode? (variableEpoch identifier) = some token)
    (present : directory.toImage.frameAt token.handle = some entry)
    (current : entry.generation = token.generation)
    (position : Mettapedia.Languages.MeTTa.MetavariableFrame.indexOf entry.frame
      (sourceIdName (BitVec.ofNat 64 (variableBase identifier))) = some slot) :
    directory.variableCoordinate? identifier = some (token.ref slot) := by
  simp [DirectoryReadback.variableCoordinate?, DirectoryReadback.sourceCoordinate?, decoded, present, current, position]

theorem FrameSlotView.variable_epoch (view : FrameStateView) (index : Nat)
    (slot : FrameSlotView) (agrees : slot.Agrees view index) :
    variableEpoch slot.varId = encode view.token := by
  rw [variableEpoch, agrees.2.2.1, variableRadix, Nat.add_comm,
    Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 32),
    Nat.div_eq_of_lt agrees.1.2.1, Nat.zero_add]
  simp

theorem FrameSlotView.variable_source (view : FrameStateView) (index : Nat)
    (slot : FrameSlotView) (agrees : slot.Agrees view index) :
    BitVec.ofNat 64 (variableBase slot.varId) = slot.sourceId := by
  rw [variableBase, agrees.2.2.1, variableRadix, Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt agrees.1.2.1]
  simp

theorem FrameReadback.toEntry_index (readback : FrameReadback)
    (index : Fin readback.slots.length) :
    Mettapedia.Languages.MeTTa.MetavariableFrame.indexOf readback.toEntry.frame
      (sourceIdName readback.slots[index.val].sourceId) = some index.val := by
  simpa [FrameReadback.slot, FrameReadback.toEntry,
    Mettapedia.Languages.MeTTa.MetavariableFrame.nameOf, List.get_eq_getElem] using
    Mettapedia.Languages.MeTTa.MetavariableFrame.indexOf_get
      readback.toEntry_frame_nodup (readback.slot index)

/-- Native framed IDs select the supplied inventory position, rather than
using a source base or a printed name as the position. No lookup agreement
is assumed: it follows from the admitted complete inventory. -/
theorem DirectoryReadback.variableCoordinate_slot (directory : DirectoryReadback)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length) :
    directory.variableCoordinate? frame.slots[index.val].varId =
      some (frame.view.token.ref index.val) := by
  have agrees := frame.slot_agrees index
  have facts := directory.frame_agrees frame member
  have present := directory.toImage_frameAt frame.view.token.handle facts.2
  rw [directory.select_frame frame member, Option.map_some] at present
  apply directory.variableCoordinate_current _ _ _ _ ?_ present rfl ?_
  · rw [FrameSlotView.variable_epoch _ _ _ agrees]
    exact decode_encode frame.admitted.1.1
  · rw [FrameSlotView.variable_source _ _ _ agrees]
    exact frame.toEntry_index index

/-- An actual variable-header reading joins the common slot readback with its
value option, write version, directory clock and activation boundary intact. -/
theorem DirectoryReadback.readVariableSlot_current (directory : DirectoryReadback)
    (memory : TargetMemory) (value : BindingValueView) (frame : FrameReadback)
    (member : frame ∈ directory.frames) (index : Fin frame.slots.length)
    (identifier : readVariableId? memory value = some frame.slots[index.val].varId) :
    directory.readVariableSlot? memory value =
      some ⟨frame.slots[index.val].value.payload, frame.slots[index.val].writeVersion,
        frame.view.writeClock, frame.view.boundary⟩ := by
  unfold DirectoryReadback.readVariableSlot?
  rw [identifier]
  change (directory.variableCoordinate? frame.slots[index.val].varId).bind
    (fun coordinate => directory.toImage.readSlot? coordinate) = _
  rw [directory.variableCoordinate_slot frame member index]
  change directory.toImage.readSlot? (frame.view.token.ref index.val) = _
  rw [directory.toImage_readSlot frame member, frame.toEntry_readSlot index]

/-! ### Ordinary binding inventories

The chronological inventory has an immutable shared prefix and an owned
suffix. `Bindings.len` counts both; suffix index zero is logical index
`shared_len`. The reader below observes the current logical memory without
forcing values or dropping null rows. Frame-authoritative lookup is separate.
-/

namespace OrdinaryBindings

structure Row where
  identifier : BitVec 64
  value : BindingValueView
  deriving DecidableEq, Repr

structure Header where
  entries : Option Address
  count : Nat
  sharedEntries : Option Address
  sharedCount : Nat
  deriving DecidableEq, Repr

def Header.Admissible (header : Header) : Prop :=
  header.count < 2 ^ 32 ∧ header.sharedCount ≤ header.count

instance (header : Header) : Decidable header.Admissible := by
  unfold Header.Admissible
  infer_instance

/-- Field positions follow `Bindings` in `match.h`: entries, len,
shared_entries and shared_len. Allocation capacity is not a live row count. -/
def readHeader? (memory : TargetMemory) (bindings : Address) : Option Header :=
  match targetRead memory (sourceFieldAddress bindings 1),
      targetRead memory (sourceFieldAddress bindings 2),
      targetRead memory (sourceFieldAddress bindings 13),
      targetRead memory (sourceFieldAddress bindings 14) with
  | some (.reference entries), some (.word count),
      some (.reference shared), some (.word sharedCount) =>
      let header : Header := ⟨entries, count.toNat, shared, sharedCount.toNat⟩
      if header.Admissible then some header else none
  | _, _, _, _ => none

theorem readHeader?_sound {memory : TargetMemory} {bindings : Address} {header : Header}
    (read : readHeader? memory bindings = some header) : header.Admissible := by
  unfold readHeader? at read
  split at read
  · dsimp only at read
    split at read
    · next admitted => cases Option.some.inj read; exact admitted
    · simp at read
  · simp at read

theorem readHeader?_fields {memory : TargetMemory} {bindings : Address} {header : Header}
    (read : readHeader? memory bindings = some header) :
    targetRead memory (sourceFieldAddress bindings 1) = some (.reference header.entries) ∧
    targetRead memory (sourceFieldAddress bindings 2) =
      some (.word (BitVec.ofNat 64 header.count)) ∧
    targetRead memory (sourceFieldAddress bindings 13) =
      some (.reference header.sharedEntries) ∧
    targetRead memory (sourceFieldAddress bindings 14) =
      some (.word (BitVec.ofNat 64 header.sharedCount)) := by
  unfold readHeader? at read
  split at read
  · dsimp only at read
    split at read
    · cases Option.some.inj read
      simp_all
    · simp at read
  · simp at read

/-- The same element addressing as `bindings_entry_at`, checked at the live
bound. A null pointer is permitted for an empty segment but cannot supply a row. -/
def Header.rowAddress? (header : Header) (index : Nat) : Option Address :=
  if index < header.count then
    if index < header.sharedCount then
      header.sharedEntries.map fun address =>
        { address with element := address.element + index }
    else
      header.entries.map fun address =>
        { address with element := address.element + (index - header.sharedCount) }
  else none

theorem Header.rowAddress?_shared (header : Header) (index : Nat)
    (live : index < header.count) (shared : index < header.sharedCount) :
    header.rowAddress? index = header.sharedEntries.map (fun address =>
      { address with element := address.element + index }) := by
  simp [Header.rowAddress?, live, shared]

theorem Header.rowAddress?_owned (header : Header) (index : Nat)
    (live : index < header.count) (owned : header.sharedCount ≤ index) :
    header.rowAddress? index = header.entries.map (fun address =>
      { address with element := address.element + (index - header.sharedCount) }) := by
  simp [Header.rowAddress?, live, Nat.not_lt.mpr owned]

theorem Header.rowAddress?_outside (header : Header) (index : Nat)
    (outside : header.count ≤ index) : header.rowAddress? index = none := by
  simp [Header.rowAddress?, Nat.not_lt.mpr outside]

/-- `Binding.var_id` is field zero; its contextual `value` is field three.
The raw value is retained even when its skeleton is null. -/
def readRow? (memory : TargetMemory) (header : Header) (index : Nat) : Option Row := do
  let address ← header.rowAddress? index
  match targetRead memory (sourceFieldAddress address 0),
      targetRead memory (sourceFieldAddress address 3) with
  | some (.word identifier), some raw =>
      (readBindingValue? raw).map (fun value => ⟨identifier, value⟩)
  | _, _ => none

theorem readRow?_iff (memory : TargetMemory) (header : Header) (index : Nat) (row : Row) :
    readRow? memory header index = some row ↔
      ∃ address raw,
        header.rowAddress? index = some address ∧
        targetRead memory (sourceFieldAddress address 0) = some (.word row.identifier) ∧
        targetRead memory (sourceFieldAddress address 3) = some raw ∧
        readBindingValue? raw = some row.value := by
  constructor
  · intro read
    obtain ⟨address, atAddress, read⟩ := Option.bind_eq_some_iff.mp read
    split at read
    · next identifier raw identifierRead valueRead =>
        obtain ⟨value, decoded, equal⟩ := Option.map_eq_some_iff.mp read
        cases equal
        exact ⟨address, raw, atAddress, identifierRead, valueRead, decoded⟩
    · simp at read
  · rintro ⟨address, raw, atAddress, identifierRead, valueRead, decoded⟩
    simp [readRow?, atAddress, identifierRead, valueRead, decoded]

theorem readRow?_admissible {memory : TargetMemory} {header : Header} {index : Nat} {row : Row}
    (read : readRow? memory header index = some row) : row.value.Admissible := by
  obtain ⟨_, _, _, _, _, decoded⟩ := (readRow?_iff _ _ _ _).mp read
  exact readBindingValue?_sound decoded

def readback? (memory : TargetMemory) (bindings : Address) : Option (List Row) := do
  let header ← readHeader? memory bindings
  let rows ← Fin.sequenceOption header.count (fun index => readRow? memory header index.val)
  return List.ofFn rows

/-- Success is equivalent to reading every live physical row, in its original
position. This admits repeated identifiers and repeated or null payloads. -/
theorem readback?_iff (memory : TargetMemory) (bindings : Address) (rows : List Row) :
    readback? memory bindings = some rows ↔
      ∃ (header : Header) (positions : Fin header.count → Row),
        readHeader? memory bindings = some header ∧
        (∀ index, readRow? memory header index.val = some (positions index)) ∧
        rows = List.ofFn positions := by
  unfold readback?
  constructor
  · intro read
    obtain ⟨header, headerRead, read⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨positions, sequence, read⟩ := Option.bind_eq_some_iff.mp read
    exact ⟨header, positions, headerRead, Fin.sequenceOption_sound header.count sequence,
      (Option.some.inj read).symm⟩
  · rintro ⟨header, positions, headerRead, reads, equal⟩
    obtain ⟨actual, sequence⟩ := Fin.sequenceOption_complete header.count
      (fun index => readRow? memory header index.val)
      (fun index => ⟨positions index, reads index⟩)
    have same : actual = positions := by
      funext index
      exact Option.some.inj ((Fin.sequenceOption_sound header.count sequence index).symm.trans
        (reads index))
    subst actual
    simp [headerRead, sequence, equal]

theorem readback?_length {memory : TargetMemory} {bindings : Address} {rows : List Row}
    (read : readback? memory bindings = some rows) :
    ∃ header, readHeader? memory bindings = some header ∧ rows.length = header.count := by
  obtain ⟨header, positions, headerRead, _, rfl⟩ := (readback?_iff _ _ _).mp read
  exact ⟨header, headerRead, List.length_ofFn⟩

theorem readback?_position {memory : TargetMemory} {bindings : Address} {rows : List Row}
    (read : readback? memory bindings = some rows) (index : Fin rows.length) :
    ∃ header, readHeader? memory bindings = some header ∧ index.val < header.count ∧
      readRow? memory header index.val = some rows[index.val] := by
  obtain ⟨header, positions, headerRead, reads, rfl⟩ := (readback?_iff _ _ _).mp read
  have live : index.val < header.count := by simpa using index.isLt
  exact ⟨header, headerRead, live, by
    simpa only [List.getElem_ofFn] using reads ⟨index.val, live⟩⟩

theorem readback?_admissible {memory : TargetMemory} {bindings : Address} {rows : List Row}
    (read : readback? memory bindings = some rows) :
    ∀ row ∈ rows, row.value.Admissible := by
  obtain ⟨header, positions, _, reads, rfl⟩ := (readback?_iff _ _ _).mp read
  intro row member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact readRow?_admissible (reads index)

/-- Choose the newest matching row before interpreting boundness. Mapping
`payload` before this search would incorrectly resurrect older bindings. -/
def lookup? (rows : List Row) (identifier : BitVec 64) : Option BindingValueView :=
  (rows.findRev? (fun row => row.identifier == identifier)).map Row.value

theorem lookup?_eq_none_iff (rows : List Row) (identifier : BitVec 64) :
    lookup? rows identifier = none ↔ ∀ row ∈ rows, row.identifier ≠ identifier := by
  simp [lookup?, List.find?_eq_none]

theorem lookup?_last (before after : List Row) (row : Row) (identifier : BitVec 64)
    (sameId : row.identifier = identifier)
    (last : ∀ later ∈ after, later.identifier ≠ identifier) :
    lookup? (before ++ row :: after) identifier = some row.value := by
  have absent : after.reverse.find? (fun entry => entry.identifier == identifier) = none := by
    simpa using last
  simp [lookup?, List.reverse_cons, List.find?_append, absent, sameId]

/-- Characterize the selected occurrence, not merely membership of its value. -/
theorem lookup?_eq_some_iff (rows : List Row) (identifier : BitVec 64)
    (value : BindingValueView) :
    lookup? rows identifier = some value ↔
      ∃ before row after,
        rows = before ++ row :: after ∧ row.identifier = identifier ∧ row.value = value ∧
        ∀ later ∈ after, later.identifier ≠ identifier := by
  constructor
  · intro found
    obtain ⟨row, selected, valueEqual⟩ := Option.map_eq_some_iff.mp found
    have reverseFound : rows.reverse.find? (fun entry => entry.identifier == identifier) =
        some row := by simpa using selected
    obtain ⟨sameId, older, newer, reversed, last⟩ :=
      List.find?_eq_some_iff_append.mp reverseFound
    refine ⟨newer.reverse, row, older.reverse, ?_, by simpa using sameId, valueEqual, ?_⟩
    · have equal := congrArg List.reverse reversed
      simpa [List.reverse_cons, List.append_assoc] using equal
    · simpa using last
  · rintro ⟨before, row, after, rfl, sameId, rfl, last⟩
    exact lookup?_last before after row identifier sameId last

theorem lookup?_null_shadows (before after : List Row) (row : Row) (identifier : BitVec 64)
    (sameId : row.identifier = identifier)
    (last : ∀ later ∈ after, later.identifier ≠ identifier)
    (unbound : row.value.skeleton = none) :
    lookup? (before ++ row :: after) identifier = some row.value ∧
      (lookup? (before ++ row :: after) identifier).bind BindingValueView.payload = none := by
  rw [lookup?_last before after row identifier sameId last]
  simp [BindingValueView.payload, unbound]

end OrdinaryBindings


/-! ### Authored activation observations

An authored cursor carries an activation-view address, not a binding epoch.
The selected context must carry that same address. The view's authority word
selects a frame in the supplied image; its own write boundary determines which
known slots are visible. Unknown inventory entries are returned separately:
the native helper gives them a different fallback and boundary rule.

The record reader admits the allocated-frame domain of `NativeFrames`. Native
compatibility epochs without allocated generations are outside this adapter.
These observations do not execute the subsequent outer alias walk, acquire a
physical borrow, or assert that an Atom's cached variable flag is correct.
-/

namespace Activation

structure View where
  sourceIds : Option Address
  sourceVariables : Option Address
  authority : BitVec 64
  count : Nat
  firstSource : BitVec 64
  contiguous : Bool
  epoch : BitVec 64
  kind : BitVec 64
  firstEntry : Nat
  firstWrite : Nat
  deriving DecidableEq, Repr

def View.Admissible (view : View) : Prop :=
  view.authority.toNat < 2 ^ 32 ∧ view.count < 2 ^ 32 ∧
    view.epoch.toNat < 2 ^ 32 ∧ view.kind.toNat ≤ 2 ∧
    view.firstEntry < 2 ^ 32 ∧ view.firstWrite < 2 ^ 64

instance (view : View) : Decidable view.Admissible := by
  unfold View.Admissible
  infer_instance

/-- Declaration-order fields of `BindingsActivationView`, including the
separate authority identity and retained activation boundary. -/
def readView? : TargetValue → Option View
  | .record "BindingsActivationView"
      [.reference ids, .reference pointers, .record "BindingsFrameRef" [.word authority],
       .word count, .word first, .bool contiguous, .word epoch, .word kind,
       .word firstEntry, .word firstWrite] =>
      let view : View := ⟨ids, pointers, authority, count.toNat, first, contiguous,
        epoch, kind, firstEntry.toNat, firstWrite.toNat⟩
      if view.Admissible then some view else none
  | _ => none

structure Cursor where
  source : Option Address
  scope : Option Address
  deriving DecidableEq, Repr

structure Context where
  bindings : Option Address
  frame : Option Address
  deriving DecidableEq, Repr

def readCursor? : TargetValue → Option Cursor
  | .record "CettaGsltTermCursorV1" [.reference source, .reference scope] =>
      some ⟨source, scope⟩
  | _ => none

def readContext? : TargetValue → Option Context
  | .record "BindingsTermCursorContextV1" [.reference bindings, .reference frame] =>
      some ⟨bindings, frame⟩
  | _ => none

def readBindingCount? (memory : TargetMemory) (bindings : Address) : Option Nat :=
  match targetRead memory (sourceFieldAddress bindings 2) with
  | some (.word count) => if count.toNat < 2 ^ 32 then some count.toNat else none
  | _ => none

def readSourceId? (memory : TargetMemory) (base : Option Address) (index : Nat) :
    Option (BitVec 64) := do
  let address ← base
  match targetRead memory { address with element := address.element + index } with
  | some (.word identifier) => some identifier
  | _ => none

def readSourceIds? (memory : TargetMemory) (view : View) : Option (List (BitVec 64)) :=
  (Fin.sequenceOption view.count
    (fun index => readSourceId? memory view.sourceIds index.val)).map List.ofFn

theorem readSourceIds?_positions (memory : TargetMemory) (view : View)
    (sources : List (BitVec 64)) (read : readSourceIds? memory view = some sources) :
    sources.length = view.count ∧ ∀ index : Fin sources.length,
      readSourceId? memory view.sourceIds index.val = some sources[index.val] := by
  obtain ⟨values, sequence, equal⟩ := Option.map_eq_some_iff.mp read
  subst sources
  refine ⟨List.length_ofFn, ?_⟩
  intro index
  have bound : index.val < view.count := by simpa using index.isLt
  simpa using Fin.sequenceOption_sound view.count sequence ⟨index.val, bound⟩

def InventoryAgrees (view : View) (sources : List (BitVec 64)) : Prop :=
  view.Admissible ∧ sources.length = view.count ∧
    sources.Pairwise (fun first second => first.toNat < second.toNat) ∧
    (∀ source ∈ sources, 0 < source.toNat ∧ source.toNat < 2 ^ 32) ∧
    (view.contiguous = true → ∀ index : Fin sources.length,
      sources[index.val].toNat = view.firstSource.toNat + index.val)

instance (view : View) (sources : List (BitVec 64)) :
    Decidable (InventoryAgrees view sources) := by
  unfold InventoryAgrees
  infer_instance

structure Inventory where
  view : View
  sources : List (BitVec 64)
  admitted : InventoryAgrees view sources

def readInventory? (memory : TargetMemory) (view : View) : Option Inventory := do
  let sources ← readSourceIds? memory view
  if admitted : InventoryAgrees view sources then some ⟨view, sources, admitted⟩ else none

/-- Authority lookup uses the current supplied image and its generation. It
does not consult another image or recover an older namesake. -/
def View.authorityPresent (view : View) (directory : DirectoryReadback) : Bool :=
  ((decode? view.authority).bind fun token =>
    (directory.toImage.frameAt token.handle).map fun entry =>
      decide (entry.generation = token.generation)).getD false

def View.available (view : View) (directory : DirectoryReadback) (bindingCount : Nat) : Bool :=
  decide (view.epoch ≠ 0 ∧ (view.kind = 1 ∨ view.kind = 2) ∧
    view.firstEntry ≤ bindingCount ∧
    (view.count = 0 ∨ (view.sourceIds.isSome ∧ view.sourceVariables.isSome ∧
      view.authorityPresent directory)))

/-- The same activation metadata at another address does not satisfy the
cursor's scope check. The selected binding image is checked independently. -/
def readScope? (memory : TargetMemory) (directory : DirectoryReadback)
    (context : Context) (cursor : Cursor) : Option Inventory := do
  if cursor.source.isSome ∧ context.bindings = some directory.directory.bindings ∧
      context.frame = cursor.scope then
    let address ← cursor.scope
    let record ← targetRead memory address
    let view ← readView? record
    let count ← readBindingCount? memory directory.directory.bindings
    if view.available directory count then readInventory? memory view else none
  else none

theorem readScope?_different_scope (memory : TargetMemory) (directory : DirectoryReadback)
    (context : Context) (cursor : Cursor) (different : context.frame ≠ cursor.scope) :
    readScope? memory directory context cursor = none := by
  simp [readScope?, different]

theorem readScope?_different_image (memory : TargetMemory) (directory : DirectoryReadback)
    (context : Context) (cursor : Cursor)
    (different : context.bindings ≠ some directory.directory.bindings) :
    readScope? memory directory context cursor = none := by
  simp [readScope?, different]

theorem View.authorityPresent_current (view : View) (directory : DirectoryReadback)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (identity : view.authority = encode frame.view.token) :
    view.authorityPresent directory = true := by
  have facts := directory.frame_agrees frame member
  have selected := directory.toImage_frameAt frame.view.token.handle facts.2
  rw [directory.select_frame frame member, Option.map_some] at selected
  simp [View.authorityPresent, identity, decode_encode frame.admitted.1.1,
    selected, FrameReadback.toEntry]

inductive Lookup where
  | unknown
  | known (value : Option BindingValueView)
  deriving DecidableEq, Repr

/-- Inventory membership precedes the slot observation. `known none` is a
successful open-variable observation and must not use the unknown fallback.
The supplied reader is instantiated below by the actual current image and in
`CeTTaFrameWriteback` by the owned captured image. -/
def Inventory.lookup (inventory : Inventory) (memory : TargetMemory)
    (readSlot : BindingValueView → Option (SlotReadbackOf BindingValueView))
    (source : Address) : Option Lookup := do
  let identifier ← readVariableId? memory ⟨some source, 0, 0⟩
  if identifier ∈ inventory.sources then
    (readSlot ⟨some source, inventory.view.authority, 1⟩).map
      (fun row => .known (row.outputAfter inventory.view.firstWrite))
  else some .unknown

def readValue? (directory : DirectoryReadback) (memory : TargetMemory)
    (inventory : Inventory) (source : Address) : Option Lookup :=
  inventory.lookup memory (directory.readVariableSlot? memory) source

/-- Every admitted native slot has the same activation observation through
the assembled common image, including null payloads and pre-boundary writes.
The view boundary, rather than the frame's stored boundary, controls the read. -/
theorem readValue?_current (directory : DirectoryReadback) (memory : TargetMemory)
    (inventory : Inventory) (source : Address) (identifier : BitVec 64)
    (observed : readVariableId? memory ⟨some source, 0, 0⟩ = some identifier)
    (known : identifier ∈ inventory.sources)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length)
    (qualified : readVariableId? memory ⟨some source, inventory.view.authority, 1⟩ =
      some frame.slots[index.val].varId) :
    readValue? directory memory inventory source =
      some (.known (if inventory.view.firstWrite < frame.slots[index.val].writeVersion
        then frame.slots[index.val].value.payload else none)) := by
  unfold readValue? Inventory.lookup
  rw [observed]
  change (if identifier ∈ inventory.sources then _ else _) = _
  rw [if_pos known, directory.readVariableSlot_current memory _ frame member index qualified]
  rfl

theorem readValue?_unknown (directory : DirectoryReadback) (memory : TargetMemory)
    (inventory : Inventory) (source : Address) (identifier : BitVec 64)
    (observed : readVariableId? memory ⟨some source, 0, 0⟩ = some identifier)
    (unknown : identifier ∉ inventory.sources) :
    readValue? directory memory inventory source = some .unknown := by
  unfold readValue? Inventory.lookup
  rw [observed]
  change (if identifier ∈ inventory.sources then _ else _) = _
  rw [if_neg unknown]

/-- Qualification is derived from the native Atom fields and the selected
authority word. No agreement of a lookup function is assumed. -/
theorem readValue?_source_slot (directory : DirectoryReadback) (memory : TargetMemory)
    (inventory : Inventory) (source : Address) (frame : FrameReadback)
    (member : frame ∈ directory.frames) (index : Fin frame.slots.length)
    (identity : inventory.view.authority = encode frame.view.token)
    (known : frame.slots[index.val].sourceId ∈ inventory.sources)
    (kind : targetRead memory (sourceFieldAddress source 0) = some (.word 1))
    (sourceId : targetRead memory (sourceFieldAddress source 2) =
      some (.word frame.slots[index.val].sourceId)) :
    readValue? directory memory inventory source =
      some (.known (if inventory.view.firstWrite < frame.slots[index.val].writeVersion
        then frame.slots[index.val].value.payload else none)) := by
  have agrees := frame.slot_agrees index
  have base : variableBase frame.slots[index.val].sourceId =
      frame.slots[index.val].sourceId.toNat :=
    Nat.mod_eq_of_lt agrees.1.2.1
  have baseNonzero : variableBase frame.slots[index.val].sourceId ≠ 0 := by
    rw [base]
    exact Nat.ne_of_gt agrees.1.1
  have valid : (⟨some source, inventory.view.authority, 1⟩ : BindingValueView).Admissible := by
    exact ⟨by rw [identity]; exact encode_fits_uint32 frame.admitted.1.1,
      by change (1#64).toNat ≤ 2; decide⟩
  have qualified :
      BitVec.ofNat 64 (inventory.view.authority.toNat * variableRadix +
        variableBase frame.slots[index.val].sourceId) = frame.slots[index.val].varId := by
    apply BitVec.eq_of_toNat_eq
    rw [qualifiedVariable_toNat ⟨some source, inventory.view.authority, 1⟩ valid,
      identity, base]
    exact agrees.2.2.1.symm
  apply readValue?_current directory memory inventory source frame.slots[index.val].sourceId
    ?_ known frame member index ?_
  · rw [readVariableId_variable memory _ source rfl _ kind sourceId]
    exact BindingValueView.variableId_materialized _
      (by change (0#64).toNat < 2 ^ 32 ∧ (0#64).toNat ≤ 2; decide) rfl _
  · rw [readVariableId_variable memory _ source rfl _ kind sourceId,
      BindingValueView.variableId_contextual _ valid
        (by change (1#64) ≠ 0#64; decide) _ baseNonzero, qualified]

/-- The next native action after the authored lookup. `outer` still requires
the outer alias resolver; it is not a completed root-resolution verdict. -/
inductive Action where
  | fallback
  | stay (cursor : Cursor)
  | defer
  | outer (root : Address)
  deriving DecidableEq, Repr

def readHasVars? (memory : TargetMemory) (address : Address) : Option Bool :=
  match targetRead memory (sourceFieldAddress address 1) with
  | some (.word flags) =>
      if flags.toNat < 2 ^ 32 then some (flags.getLsbD 0) else none
  | _ => none

def nextAction? (memory : TargetMemory) (cursor : Cursor) : Lookup → Option Action
  | .unknown => some .fallback
  | .known none => some (.stay cursor)
  | .known (some value) => do
      let address ← value.skeleton
      if value.kind = 1 ∨ value.kind = 2 then
        let openTerm ← readHasVars? memory address
        if openTerm then some .defer else some (.outer address)
      else if value.kind = 0 then some (.outer address) else none

/-- The authored VARIABLE branch, ending before fallback or outer alias traversal.
Scoped non-variable roots bypass this branch in the native cursor adapter.
`none` denotes failed readback admission, not a uniform native DEFER result. -/
def readAuthoredRoot? (memory : TargetMemory) (directory : DirectoryReadback)
    (context : Context) (cursor : Cursor) : Option Action := do
  let inventory ← readScope? memory directory context cursor
  let source ← cursor.source
  let value ← readValue? directory memory inventory source
  nextAction? memory cursor value

/-- Read the selected native context and enter its authored VARIABLE branch.
The resulting action is an intermediate decision, not the complete root resolver. -/
def readContextRoot? (memory : TargetMemory) (directory : DirectoryReadback)
    (contextAddress : Address) (cursor : Cursor) : Option Action := do
  let record ← targetRead memory contextAddress
  let context ← readContext? record
  readAuthoredRoot? memory directory context cursor

theorem readAuthoredRoot?_known_open (memory : TargetMemory) (directory : DirectoryReadback)
    (context : Context) (cursor : Cursor) (inventory : Inventory) (source : Address)
    (scopeRead : readScope? memory directory context cursor = some inventory)
    (pointer : cursor.source = some source)
    (unbound : readValue? directory memory inventory source = some (.known none)) :
    readAuthoredRoot? memory directory context cursor = some (.stay cursor) := by
  simp [readAuthoredRoot?, scopeRead, pointer, unbound, nextAction?]

theorem nextAction?_open_contextual (memory : TargetMemory) (cursor : Cursor)
    (value : BindingValueView) (address : Address) (pointer : value.skeleton = some address)
    (contextual : value.kind = 1 ∨ value.kind = 2)
    (openTerm : readHasVars? memory address = some true) :
    nextAction? memory cursor (.known (some value)) = some .defer := by
  change value.kind = 1#64 ∨ value.kind = 2#64 at contextual
  simp [nextAction?, pointer, contextual, openTerm]

end Activation

/-! ## Root resolution as a retained adaptive query

The alias-move allowance is distinct from cursor fuel. A zero allowance still
permits the observations that distinguish an open variable or self-link from
a further alias. Every stop preserves the complete current value, including
its pointer and context. A non-variable head ends the walk without traversing
its children or invoking an evaluator.

This connection relates checked memory observations to the common query
machine. Execution of the encompassing C helper, including its fast lookup
index, physical borrow and metadata-derived allowance, is a separate join.
-/

namespace RootResolution

/-- The private variant namespace is not a frame epoch, even though its
upper word is nonzero. This is the native `binding_id_has_frame` split. -/
def hasFrame (identifier : BitVec 64) : Bool :=
  variableEpoch identifier != 0 && variableEpoch identifier != 0xFFFFA11A

theorem hasFrame_slot (frame : FrameReadback) (index : Fin frame.slots.length) :
    hasFrame frame.slots[index.val].varId = true := by
  have valid := frame.admitted.1.1
  have limits : 0 < (encode frame.view.token).toNat ∧
      (encode frame.view.token).toNat < 0xFFF00000 := by
    rw [encode_toNat valid]
    have bound := encoding_bounds valid
    omega
  have nonzero : encode frame.view.token ≠ 0#64 := by
    intro equal
    have numeric := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat] at numeric
    omega
  have notPrivate : encode frame.view.token ≠ 0xFFFFA11A#64 := by
    intro equal
    have numeric := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat] at numeric
    omega
  simp [hasFrame, FrameSlotView.variable_epoch _ _ _ (frame.slot_agrees index), nonzero, notPrivate]

/-- Root lookup uses the checked current frame inventory or the newest
ordinary row. Activation-boundary filtering belongs to the enclosing consumer,
not to this raw alias walk. A stale framed name never falls back to ordinary rows. -/
def lookup (directory : DirectoryReadback) (rows : List OrdinaryBindings.Row)
    (identifier : BitVec 64) : Option BindingValueView :=
  if hasFrame identifier then
    (directory.variableCoordinate? identifier).bind fun coordinate =>
      (directory.toImage.readSlot? coordinate).bind SlotReadbackOf.value
  else OrdinaryBindings.lookup? rows identifier

theorem lookup_ordinary (directory : DirectoryReadback) (rows : List OrdinaryBindings.Row)
    (identifier : BitVec 64) (ordinary : hasFrame identifier = false) :
    lookup directory rows identifier = OrdinaryBindings.lookup? rows identifier := by
  simp [lookup, ordinary]

theorem lookup_framed_missing (directory : DirectoryReadback) (rows : List OrdinaryBindings.Row)
    (identifier : BitVec 64) (framed : hasFrame identifier = true)
    (missing : directory.variableCoordinate? identifier = none) :
    lookup directory rows identifier = none := by
  simp [lookup, framed, missing]

/-- Every admitted source inventory position supplies its actual contextual
payload. No lookup correspondence is assumed. -/
theorem lookup_current_slot (directory : DirectoryReadback) (rows : List OrdinaryBindings.Row)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length) :
    lookup directory rows frame.slots[index.val].varId =
      frame.slots[index.val].value.payload := by
  simp only [lookup, hasFrame_slot frame index, ↓reduceIte, directory.variableCoordinate_slot frame member index,
    Option.bind_some, directory.toImage_readSlot frame member, frame.toEntry_readSlot index]

namespace Query

open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.GSLT.LanguageDef.NativeRecordAccess (targetReadWord)

inductive Key where
  | field (address : Address)
  | binding (identifier : BitVec 64)
  deriving DecidableEq, Repr

inductive Reply where
  | field (value : Option (BitVec 64))
  | binding (value : Option BindingValueView)
  deriving DecidableEq, Repr

/-- An admitted non-variable header is terminal even when its children contain
variables or pending computations. -/
inductive Head where
  | term
  | variable (identifier : BitVec 64)
  deriving DecidableEq, Repr

/-- Readback failure is not the native allowance refusal. -/
inductive Result where
  | unreadable
  | refused
  | resolved (value : BindingValueView)
  deriving DecidableEq, Repr

def store (memory : TargetMemory) (lookup : BitVec 64 → Option BindingValueView) : Key → Reply
  | .field address => .field (targetReadWord memory address)
  | .binding identifier => .binding (lookup identifier)

def head? (memory : TargetMemory) (value : BindingValueView) : Option Head :=
  match value.skeleton with
  | none => none
  | some address =>
      match targetReadWord memory (sourceFieldAddress address 0) with
      | none => none
      | some kind =>
          if kind = 1 then
            (targetReadWord memory (sourceFieldAddress address 2)).bind fun source =>
              (value.variableId? source).map Head.variable
          else some .term

def head (value : BindingValueView) : Program Key Reply (Option Head) :=
  match value.skeleton with
  | none => .pure none
  | some address => .read (.field (sourceFieldAddress address 0)) fun reply =>
      match reply with
      | .field (some kind) =>
          if kind = 1 then
            .read (.field (sourceFieldAddress address 2)) fun reply =>
              match reply with
              | .field (some source) => .pure ((value.variableId? source).map Head.variable)
              | _ => .pure none
          else .pure (some .term)
      | _ => .pure none

theorem run_head (memory : TargetMemory) (lookup : BitVec 64 → Option BindingValueView)
    (value : BindingValueView) :
    (run (store memory lookup) (head value)).answer = head? memory value := by
  cases pointer : value.skeleton with
  | none => simp [head, head?, pointer, run]
  | some address =>
      cases header : targetReadWord memory (sourceFieldAddress address 0) with
      | none => simp [head, head?, pointer, run, store, header]
      | some kind =>
          by_cases isVariable : kind = 1#64
          · cases identifier : targetReadWord memory (sourceFieldAddress address 2) <;>
              simp [head, head?, pointer, run, store, header, isVariable, identifier]
          · simp [head, head?, pointer, run, store, header, isVariable]

/-- A left result is a stop at the original current value. In particular,
the equal-ID test does not replace it with the lookup's pointer. -/
def step? (memory : TargetMemory) (lookup : BitVec 64 → Option BindingValueView)
    (value : BindingValueView) : Option (Sum BindingValueView BindingValueView) := do
  let first ← head? memory value
  match first with
  | .term => some (.inl value)
  | .variable identifier =>
      match lookup identifier with
      | none => some (.inl value)
      | some next =>
          if next.skeleton = none then some (.inl value)
          else do
            let following ← head? memory next
            if following = .variable identifier then some (.inl value)
            else some (.inr next)

def step (value : BindingValueView) :
    Program Key Reply (Option (Sum BindingValueView BindingValueView)) :=
  bind (head value) fun first =>
    match first with
    | none => .pure none
    | some .term => .pure (some (.inl value))
    | some (.variable identifier) => .read (.binding identifier) fun reply =>
        match reply with
        | .binding none => .pure (some (.inl value))
        | .binding (some next) =>
            if next.skeleton = none then .pure (some (.inl value))
            else map (fun following => following.map fun following =>
              if following = .variable identifier then .inl value else .inr next) (head next)
        | _ => .pure none

theorem run_step (memory : TargetMemory) (lookup : BitVec 64 → Option BindingValueView)
    (value : BindingValueView) :
    (run (store memory lookup) (step value)).answer = step? memory lookup value := by
  simp only [step, run_bind]
  rw [run_head]
  cases observed : head? memory value with
  | none => simp [step?, observed, run]
  | some tag =>
      cases tag with
      | term => simp [step?, observed, run]
      | «variable» identifier =>
          cases found : lookup identifier with
          | none => simp [step?, observed, run, store, found]
          | some next =>
              by_cases empty : next.skeleton = none
              · simp [step?, observed, run, store, found, empty]
              · simp only [run, store, found, empty, ite_false, run_map, run_head]
                cases following : head? memory next <;>
                  simp [step?, observed, found, empty, following, apply_ite]

/-- Independent bounded observation of the alias relation. Only a proper
alias edge consumes allowance; inspecting a terminal value consumes none. -/
def resolve (memory : TargetMemory) (lookup : BitVec 64 → Option BindingValueView) :
    Nat → BindingValueView → Result
  | allowance, value =>
      match step? memory lookup value with
      | none => .unreadable
      | some (.inl terminal) => .resolved terminal
      | some (.inr next) => match allowance with
          | 0 => .refused
          | allowance + 1 => resolve memory lookup allowance next

def walk : Nat → BindingValueView → Program Key Reply Result
  | allowance, value => bind (step value) fun observed =>
      match observed with
      | none => .pure .unreadable
      | some (.inl terminal) => .pure (.resolved terminal)
      | some (.inr next) => match allowance with
          | 0 => .pure .refused
          | allowance + 1 => walk allowance next
termination_by structural allowance => allowance

theorem resolve_term (memory : TargetMemory) (lookup : BitVec 64 → Option BindingValueView)
    (allowance : Nat) (value : BindingValueView) (terminal : head? memory value = some .term) :
    resolve memory lookup allowance value = .resolved value := by
  rw [resolve]
  simp [step?, terminal]

theorem resolve_open (memory : TargetMemory) (lookup : BitVec 64 → Option BindingValueView)
    (allowance : Nat) (value : BindingValueView) (identifier : BitVec 64)
    (headed : head? memory value = some (.variable identifier)) (unbound : lookup identifier = none) :
    resolve memory lookup allowance value = .resolved value := by
  rw [resolve]
  simp [step?, headed, unbound]

/-- Finding the same qualified variable stops at the current complete value;
an equal identifier is not permission to replace its pointer or context. -/
theorem resolve_self (memory : TargetMemory) (lookup : BitVec 64 → Option BindingValueView)
    (allowance : Nat) (value next : BindingValueView) (identifier : BitVec 64)
    (headed : head? memory value = some (.variable identifier))
    (found : lookup identifier = some next)
    (same : head? memory next = some (.variable identifier)) :
    resolve memory lookup allowance value = .resolved value := by
  rw [resolve]
  by_cases empty : next.skeleton = none <;> simp [step?, headed, found, same, empty]

/-- Once the walk succeeds, a larger alias allowance gives exactly the same
complete operand. A refusal alone does not establish that a cycle was found. -/
theorem resolve_add_allowance (memory : TargetMemory)
    (lookup : BitVec 64 → Option BindingValueView) (allowance extra : Nat)
    (value result : BindingValueView)
    (finished : resolve memory lookup allowance value = .resolved result) :
    resolve memory lookup (allowance + extra) value = .resolved result := by
  induction allowance generalizing value with
  | zero =>
      rw [resolve] at finished ⊢
      cases observed : step? memory lookup value with
      | none => simp [observed] at finished
      | some next =>
          cases next with
          | inl terminal => simpa [observed] using finished
          | inr next => simp [observed] at finished
  | succ allowance ih =>
      rw [resolve] at finished ⊢
      cases observed : step? memory lookup value with
      | none => simp [observed] at finished
      | some next =>
          cases next with
          | inl terminal => simpa [observed] using finished
          | inr next =>
              simpa [observed, Nat.succ_add] using ih next (by simpa [observed] using finished)

/-- The retained query and the independent bounded observation agree for
every allowance and complete contextual input, not only closed terms. -/
theorem run_walk (memory : TargetMemory) (lookup : BitVec 64 → Option BindingValueView)
    (allowance : Nat) (value : BindingValueView) :
    (run (store memory lookup) (walk allowance value)).answer =
      resolve memory lookup allowance value := by
  induction allowance generalizing value with
  | zero =>
      rw [walk, run_bind]
      dsimp only
      rw [run_step, resolve]
      cases step? memory lookup value with
      | none => rfl
      | some observed => cases observed <;> rfl
  | succ allowance ih =>
      rw [walk, run_bind]
      dsimp only
      rw [run_step, resolve]
      cases step? memory lookup value with
      | none => rfl
      | some observed => cases observed with
        | inl terminal => rfl
        | inr next => exact ih next

/-- Assemble the query provider from the actual ordinary-binding record
reader and the checked frame directory for the same bindings object. The
directory's iterator completeness and the lifetime of both borrowed inputs
remain the native caller's obligations. -/
def readStore? (memory : TargetMemory) (directory : DirectoryReadback) : Option (Key → Reply) :=
  (OrdinaryBindings.readback? memory directory.directory.bindings).map fun rows =>
    store memory (RootResolution.lookup directory rows)

theorem readStore?_constructed (memory : TargetMemory) (directory : DirectoryReadback)
    (rows : List OrdinaryBindings.Row)
    (read : OrdinaryBindings.readback? memory directory.directory.bindings = some rows) :
    readStore? memory directory = some (store memory (RootResolution.lookup directory rows)) := by
  simp [readStore?, read]

/-- The cursor retains the adaptive continuation, not a second resolver.
Its budget counts query reads; alias allowance is part of the input. -/
def advance (memory : TargetMemory) (directory : DirectoryReadback)
    (rows : List OrdinaryBindings.Row) (allowance fuel : Nat) (value : BindingValueView) :=
  let current := store memory (RootResolution.lookup directory rows)
  Mettapedia.Machines.Cursor.advance
    (Mettapedia.Machines.Cursor.ReadOnlyQuery.provider current)
    Mettapedia.Machines.Cursor.ReadOnlyQuery.client
    (Mettapedia.Machines.Cursor.ReadOnlyQuery.readCharge current) (base := .unit)
    fuel ⟨.unit, walk allowance value, []⟩

theorem advance_meaning (memory : TargetMemory) (directory : DirectoryReadback)
    (rows : List OrdinaryBindings.Row) (allowance fuel : Nat) (value : BindingValueView) :
    (Mettapedia.Machines.Cursor.ReadOnlyQuery.residualMeaning
      (store memory (RootResolution.lookup directory rows))
      (advance memory directory rows allowance fuel value).2).answer =
        resolve memory (RootResolution.lookup directory rows) allowance value := by
  unfold advance
  rw [Mettapedia.Machines.Cursor.ReadOnlyQuery.advance_meaning]
  exact run_walk _ _ _ _

theorem completed_correct (memory : TargetMemory) (directory : DirectoryReadback)
    (rows : List OrdinaryBindings.Row) (allowance fuel : Nat) (value : BindingValueView)
    (observation : Observation Key Reply Result)
    (finished : Mettapedia.Machines.Cursor.ReadOnlyQuery.completed?
      (store memory (RootResolution.lookup directory rows))
      (advance memory directory rows allowance fuel value).2 = some observation) :
    observation.answer = resolve memory (RootResolution.lookup directory rows) allowance value := by
  have correct := Mettapedia.Machines.Cursor.ReadOnlyQuery.completed_correct
    (store memory (RootResolution.lookup directory rows)) fuel (walk allowance value)
    observation finished
  rw [correct]
  exact run_walk _ _ _ _

/-- A cache key retains the whole contextual operand, including its pointer,
and the allowance. The common cache compares caller-supplied authority keys;
their lifetime and version meaning must be established by the native caller.
This fixed query family does not itself confer ownership or force rights. -/
def family {Authority : Type} (_authority : Authority) (input : Nat × BindingValueView) :
    Program Key Reply Result := walk input.1 input.2

theorem reuse_exact {Authority : Type} [DecidableEq Authority]
    (authority : Authority) (memory : TargetMemory) (directory : DirectoryReadback)
    (rows : List OrdinaryBindings.Row) (input : Nat × BindingValueView)
    (entry : Mettapedia.Machines.ReadCertifiedQueryReuse.Entry Authority
      (Nat × BindingValueView) Key Reply Result)
    (recorded : Mettapedia.Machines.ReadCertifiedQueryReuse.Recorded family entry) :
    (Mettapedia.Machines.ReadCertifiedQueryReuse.reuse family authority input
      (store memory (RootResolution.lookup directory rows)) entry).1 =
        resolve memory (RootResolution.lookup directory rows) input.1 input.2 := by
  rw [Mettapedia.Machines.ReadCertifiedQueryReuse.reuse_exact family authority input _ entry recorded]
  exact run_walk _ _ _ _

end Query

end RootResolution


end NativeFrames

open NativeFrames

/-- The native store changes the contextual value and its write stamp together. -/
def replaceSlot (row : FrameSlotView) (value : BindingValueView) (version : Nat) :
    FrameSlotView :=
  { row with value := value, writeVersion := version }

private theorem replaceSlot_agrees (before : FrameStateView) (row : FrameSlotView)
    (index : Nat) (agrees : row.Agrees before index)
    (value : BindingValueView) (valid : value.Admissible)
    (room : before.writeClock + 1 < 2 ^ 64) :
    (replaceSlot row value (before.writeClock + 1)).Agrees
      { before with writeClock := before.writeClock + 1 } index := by
  rcases agrees with ⟨⟨positive, source, spelling, _, _⟩, bound, qualified,
    declared, dense, grown⟩
  exact ⟨⟨positive, source, spelling, valid, room⟩, bound, qualified, declared, dense, grown⟩

private theorem unchangedSlot_agrees (before : FrameStateView) (row : FrameSlotView)
    (index : Nat) (agrees : row.Agrees before index) (clock : Nat) :
    row.Agrees { before with writeClock := clock } index := agrees

/-- Logical effect of the successful native writes, before decoding. -/
def write (before : FrameReadback) (slot : Fin before.slots.length)
    (value : BindingValueView) (valid : value.Admissible)
    (room : before.view.writeClock + 1 < 2 ^ 64) : FrameReadback where
  view := { before.view with writeClock := before.view.writeClock + 1 }
  slots := before.slots.set slot.val
    (replaceSlot before.slots[slot.val] value (before.view.writeClock + 1))
  admitted := by
    rcases before.admitted with ⟨header, count, ordered, entries⟩
    refine ⟨?_, by simpa using count, ?_, ?_⟩
    · rcases header with ⟨token, positive, schema, size, revision, _, boundary⟩
      exact ⟨token, positive, schema, size, revision, room, boundary⟩
    · rw [List.pairwise_iff_getElem] at ordered ⊢
      intro i j hi hj less
      have original := ordered i j (by simpa using hi) (by simpa using hj) less
      simp only [List.getElem_set]
      split <;> split <;> simp_all [replaceSlot]
    · intro index
      have bound : index.val < before.slots.length := by simpa using index.isLt
      by_cases selected : slot.val = index.val
      · simpa [List.getElem_set, selected] using
          replaceSlot_agrees before.view before.slots[index.val]
          index.val (entries ⟨index.val, bound⟩) value valid room
      · simpa [List.getElem_set, selected] using
          unchangedSlot_agrees before.view before.slots[index.val] index.val
            (entries ⟨index.val, bound⟩) (before.view.writeClock + 1)

theorem write_preserves_identity (before : FrameReadback) (slot : Fin before.slots.length)
    (value : BindingValueView) (valid : value.Admissible)
    (room : before.view.writeClock + 1 < 2 ^ 64) :
    (write before slot value valid room).toEntry.frame = before.toEntry.frame ∧
    (write before slot value valid room).toEntry.generation = before.toEntry.generation ∧
    (write before slot value valid room).toEntry.activationBoundary =
      before.toEntry.activationBoundary := by
  refine ⟨?_, rfl, rfl⟩
  simp [FrameReadback.toEntry, write, replaceSlot]
  have same := List.set_getElem_self
    (as := before.slots.map (fun row => sourceIdName row.sourceId))
    (i := slot.val) (by simp)
  change (before.slots.map (fun row => sourceIdName row.sourceId)).set slot.val
    ((before.slots.map (fun row => sourceIdName row.sourceId))[slot.val]) = _ at same
  simpa using same

theorem write_values (before : FrameReadback) (slot : Fin before.slots.length)
    (value : BindingValueView) (valid : value.Admissible)
    (room : before.view.writeClock + 1 < 2 ^ 64) :
    (write before slot value valid room).toEntry.values =
      before.toEntry.values.setIfInBounds slot.val value.payload := by
  simp [FrameReadback.toEntry, write, replaceSlot]

theorem write_versions (before : FrameReadback) (slot : Fin before.slots.length)
    (value : BindingValueView) (valid : value.Admissible)
    (room : before.view.writeClock + 1 < 2 ^ 64) :
    (write before slot value valid room).toEntry.writeVersions =
      before.toEntry.writeVersions.setIfInBounds slot.val (before.view.writeClock + 1) := by
  simp [FrameReadback.toEntry, write, replaceSlot]

/-- Install the independently updated native inventory in the same caller image. -/
def commit (store : StoreOf BindingValueView) (after : FrameReadback) :
    StoreOf BindingValueView :=
  { store with
    entries := store.entries.setIfInBounds after.view.token.handle (some after.toEntry)
    writeClock := after.view.writeClock }

/-- Decoding a successful view update agrees with the pre-existing store write.
The caller supplies the current frame and clock, rather than a sibling image. -/
theorem write_correspondence (store : StoreOf BindingValueView) (before : FrameReadback)
    (present : frameAt store before.view.token.handle = some before.toEntry)
    (clock : store.writeClock = before.view.writeClock)
    (slot : Fin before.slots.length) (value : BindingValueView)
    (valid : value.Admissible) (room : before.view.writeClock + 1 < 2 ^ 64) :
    MetavariableFrameStore.write? store (before.view.token.ref slot.val) value.payload =
      some (commit store (write before slot value valid room)) := by
  have bound : slot.val < before.toEntry.values.size := by
    simp [FrameReadback.toEntry]
  rw [MetavariableFrameStore.write?_valid present rfl bound]
  congr 1
  let updated : EntryOf BindingValueView :=
    { before.toEntry with
      values := before.toEntry.values.setIfInBounds slot.val value.payload
      size_eq := by simpa using before.toEntry.size_eq
      writeVersions := before.toEntry.writeVersions.setIfInBounds slot.val (store.writeClock + 1)
      versions_size_eq := by simpa using before.toEntry.versions_size_eq }
  have entry : (write before slot value valid room).toEntry = updated := by
    have identity := write_preserves_identity before slot value valid room
    have values := write_values before slot value valid room
    have versions := write_versions before slot value valid room
    change _ = before.toEntry.writeVersions.setIfInBounds slot.val (before.view.writeClock + 1) at versions
    cases old : before.toEntry
    cases new : (write before slot value valid room).toEntry
    simp only [old, new] at identity values versions
    rcases identity with ⟨frame, generation, boundary⟩
    simp_all [updated]
  change { store with
      entries := store.entries.setIfInBounds before.view.token.handle (some updated)
      writeClock := store.writeClock + 1 } = _
  unfold commit
  rw [entry, clock]
  rfl

theorem write_selected (store : StoreOf BindingValueView) (before : FrameReadback)
    (present : frameAt store before.view.token.handle = some before.toEntry)
    (clock : store.writeClock = before.view.writeClock)
    (slot : Fin before.slots.length) (value : BindingValueView)
    (valid : value.Admissible) (room : before.view.writeClock + 1 < 2 ^ 64) :
    lookup (commit store (write before slot value valid room)) (before.view.token.ref slot.val) =
      some value.payload :=
  lookup_write (write_correspondence store before present clock slot value valid room)

theorem write_other (store : StoreOf BindingValueView) (before : FrameReadback)
    (present : frameAt store before.view.token.handle = some before.toEntry)
    (clock : store.writeClock = before.view.writeClock)
    (slot : Fin before.slots.length) (value : BindingValueView)
    (valid : value.Admissible) (room : before.view.writeClock + 1 < 2 ^ 64)
    (other : Ref) (different : other ≠ before.view.token.ref slot.val) :
    lookup (commit store (write before slot value valid room)) other = lookup store other :=
  lookup_write_other (write_correspondence store before present clock slot value valid room) different

/-- A suspended destination names its binding world and source occurrence.
The directory address is deliberately absent: detachment can change it. -/
structure Destination where
  bindings : Address
  token : Shared.Token
  slot : Nat
  sourceId : BitVec 64
  deriving DecidableEq, Repr

def destination (before : FrameReadback) (slot : Fin before.slots.length) : Destination :=
  ⟨before.view.bindings, before.view.token, slot.val, before.slots[slot.val].sourceId⟩

/-- Checked receipt of a bound child value into an already writable current
frame. Reordered coordinates, another world and exhausted clocks are refused. -/
def receive? (before : FrameReadback) (wanted : Destination) (value : BindingValueView) :
    Option FrameReadback :=
  if before.view.bindings = wanted.bindings ∧ before.view.token = wanted.token then
    if bound : wanted.slot < before.slots.length then
      if before.slots[wanted.slot].sourceId = wanted.sourceId ∧ value.skeleton.isSome then
        if valid : value.Admissible then
          if room : before.view.writeClock + 1 < 2 ^ 64 then
            some (write before ⟨wanted.slot, bound⟩ value valid room)
          else none
        else none
      else none
    else none
  else none

theorem receive_current (before : FrameReadback) (slot : Fin before.slots.length)
    (value : BindingValueView) (valid : value.Admissible)
    (bound : value.skeleton.isSome = true)
    (room : before.view.writeClock + 1 < 2 ^ 64) :
    receive? before (destination before slot) value = some (write before slot value valid room) := by
  simp only [receive?, destination, and_self, ite_true, slot.isLt, dite_true,
    bound, valid, room]

/-- Both directions: the checked operation neither invents successful replies
nor refuses an admitted current destination with a bound contextual value. -/
theorem receive_success_iff (before after : FrameReadback) (wanted : Destination)
    (value : BindingValueView) :
    receive? before wanted value = some after ↔
      ∃ (slot : Fin before.slots.length) (valid : value.Admissible)
        (room : before.view.writeClock + 1 < 2 ^ 64),
        wanted = destination before slot ∧ value.skeleton.isSome = true ∧
        after = write before slot value valid room := by
  constructor
  · intro received
    unfold receive? at received
    split at received
    · next world =>
      split at received
      · next bound =>
        split at received
        · next source =>
          split at received
          · next valid =>
            split at received
            · next room =>
              refine ⟨⟨wanted.slot, bound⟩, valid, room, ?_, source.2,
                (Option.some.inj received).symm⟩
              cases wanted
              simp only [destination, Destination.mk.injEq]
              exact ⟨world.1.symm, world.2.symm, True.intro, source.1.symm⟩
            · simp at received
          · simp at received
        · simp at received
      · simp at received
    · simp at received
  · rintro ⟨slot, valid, room, rfl, bound, rfl⟩
    exact receive_current before slot value valid bound room

/-- A value write keeps the ordered native lexical identities. The payload
and its version change; source-name resolution remains the same operation. -/
theorem write_variable_ids (before : FrameReadback) (slot : Fin before.slots.length)
    (value : BindingValueView) (valid : value.Admissible)
    (room : before.view.writeClock + 1 < 2 ^ 64) :
    (write before slot value valid room).slots.map FrameSlotView.varId =
      before.slots.map FrameSlotView.varId := by
  have same := List.set_getElem_self
    (as := before.slots.map FrameSlotView.varId) (i := slot.val) (by simp)
  simpa [write,replaceSlot] using same

theorem receive_coordinates (before after : FrameReadback) (wanted : Destination)
    (value : BindingValueView) (received : receive? before wanted value = some after) :
    after.view.token = before.view.token ∧
      after.slots.map FrameSlotView.varId = before.slots.map FrameSlotView.varId := by
  obtain ⟨slot,valid,room,_,_,rfl⟩ :=
    (receive_success_iff before after wanted value).mp received
  exact ⟨rfl,write_variable_ids before slot value valid room⟩

/-- A successful child receipt realizes exactly the common store write at
the saved destination, including all unmodified frames of the caller image. -/
theorem receive_correspondence (store : StoreOf BindingValueView)
    (before after : FrameReadback)
    (present : frameAt store before.view.token.handle = some before.toEntry)
    (clock : store.writeClock = before.view.writeClock)
    (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) :
    MetavariableFrameStore.write? store (wanted.token.ref wanted.slot) (some value) =
      some (commit store after) := by
  obtain ⟨slot, valid, room, rfl, bound, rfl⟩ :=
    (receive_success_iff before after wanted value).mp received
  have payload : value.payload = some value := by simp [BindingValueView.payload, bound]
  simpa only [destination, payload] using
    write_correspondence store before present clock slot value valid room

/-- The shared-allocator image uses the same store operation. No owner count
is acquired, dropped or inferred by committing this logical write. -/
def commitImage (image : Shared.ImageOf BindingValueView) (after : FrameReadback) :
    Shared.ImageOf BindingValueView :=
  ⟨image.entries.setIfInBounds after.view.token.handle (some after.toEntry),
    after.view.writeClock⟩

theorem receive_image_correspondence (image : Shared.ImageOf BindingValueView)
    (before after : FrameReadback)
    (present : image.frameAt before.view.token.handle = some before.toEntry)
    (clock : image.writeClock = before.view.writeClock)
    (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) :
    image.write? (wanted.token.ref wanted.slot) (some value) =
      some (commitImage image after) := by
  have written := receive_correspondence ⟨image.entries, 0, image.writeClock⟩
    before after present clock wanted value received
  change (MetavariableFrameStore.write? ⟨image.entries, 0, image.writeClock⟩
    (wanted.token.ref wanted.slot) (some value)).map
      (fun store => (⟨store.entries, store.writeClock⟩ : Shared.ImageOf BindingValueView)) = _
  rw [written]
  rfl

/-- Compose with the checked whole-directory decoder, retaining its native
handles and the caller's current directory clock. -/
theorem receive_directory_correspondence (directory : DirectoryReadback)
    (before after : FrameReadback)
    (member : before ∈ directory.frames)
    (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) :
    directory.toImage.write? (wanted.token.ref wanted.slot) (some value) =
      some (commitImage directory.toImage after) := by
  have selected := directory.select_frame before member
  have facts := directory.frame_agrees before member
  have present := directory.toImage_frameAt before.view.token.handle facts.2
  rw [selected, Option.map_some] at present
  exact receive_image_correspondence directory.toImage before after present
    facts.1.2.2.2.symm wanted value received

/-! ## Receipts against the complete framed directory

Every frame header observes the directory's current clock. A successful receipt
updates one frame and refreshes every sibling's borrowed header; sibling values,
versions and activation boundaries are unchanged. This constructs the complete
next framed image, without acquiring payload or frame ownership.
-/

private theorem clock_bounded (frame : FrameReadback) : frame.view.writeClock < 2 ^ 64 := by
  exact frame.admitted.1.2.2.2.2.2.1

/-- Refresh a borrowed frame header to the clock of its current directory. -/
def refreshClock (frame : FrameReadback) (clock : Nat) (bounded : clock < 2 ^ 64) :
    FrameReadback where
  view := { frame.view with writeClock := clock }
  slots := frame.slots
  admitted := by
    rcases frame.admitted with ⟨header, count, ordered, entries⟩
    rcases header with ⟨token, positive, schema, size, revision, _, boundary⟩
    exact ⟨⟨token, positive, schema, size, revision, bounded, boundary⟩,
      count, ordered, fun index => unchangedSlot_agrees _ _ _ (entries index) clock⟩

@[simp] theorem refreshClock_toEntry (frame : FrameReadback) (clock : Nat)
    (bounded : clock < 2 ^ 64) : (refreshClock frame clock bounded).toEntry = frame.toEntry := rfl

private theorem receive_view (before after : FrameReadback) (wanted : Destination)
    (value : BindingValueView) (received : receive? before wanted value = some after) :
    after.view = { before.view with writeClock := before.view.writeClock + 1 } := by
  obtain ⟨slot, valid, room, _, _, rfl⟩ :=
    (receive_success_iff before after wanted value).mp received
  rfl

private def directoryFrame (before after frame : FrameReadback) : FrameReadback :=
  if frame.view.token.handle = before.view.token.handle then after
  else refreshClock frame after.view.writeClock (clock_bounded after)

private theorem directoryFrame_handle (before after : FrameReadback) (wanted : Destination)
    (value : BindingValueView) (received : receive? before wanted value = some after)
    (frame : FrameReadback) :
    (directoryFrame before after frame).view.token.handle = frame.view.token.handle := by
  have view := receive_view before after wanted value received
  simp only [directoryFrame]
  split
  · next same => simpa [view] using same.symm
  · rfl

/-- Commit one receipt and preserve the complete directory inventory, including
the shared clock seen by every sibling frame. -/
def commitDirectory (directory : DirectoryReadback) (before after : FrameReadback)
    (member : before ∈ directory.frames) (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) : DirectoryReadback where
  directory := { directory.directory with writeClock := after.view.writeClock }
  capacity := directory.capacity
  frames := directory.frames.map (directoryFrame before after)
  admitted := by
    have beforeFacts := directory.frame_agrees before member
    have view := receive_view before after wanted value received
    rcases directory.admitted with ⟨admitted, count, distinct, entries⟩
    refine ⟨?_, by simpa using count, ?_, ?_⟩
    · rcases admitted with ⟨size, revision, _, absent⟩
      refine ⟨size, revision, clock_bounded after, ?_⟩
      intro missing
      have impossible : directory.directory.directory ≠ none := by
        rw [← beforeFacts.1.2.1]
        simp
      exact False.elim (impossible missing)
    · simpa only [List.map_map, Function.comp_def,
        directoryFrame_handle before after wanted value received] using distinct
    · intro index
      have bound : index.val < directory.frames.length := by simpa using index.isLt
      have facts := entries ⟨index.val, bound⟩
      simp only [List.getElem_map, directoryFrame]
      split
      · refine ⟨?_, ?_⟩
        · simpa only [FrameStateView.Compatible, view] using
            (show before.view.bindings = directory.directory.bindings ∧
                some before.view.directory = directory.directory.directory ∧
                before.view.schemaRevision = directory.directory.schemaRevision ∧
                after.view.writeClock = after.view.writeClock from
              ⟨beforeFacts.1.1, beforeFacts.1.2.1, beforeFacts.1.2.2.1, rfl⟩)
        · simpa [view] using beforeFacts.2
      · exact ⟨⟨facts.1.1, facts.1.2.1, facts.1.2.2.1, rfl⟩, facts.2⟩

theorem commitDirectory_clock (directory : DirectoryReadback) (before after : FrameReadback)
    (member : before ∈ directory.frames) (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) :
    (commitDirectory directory before after member wanted value received).directory.writeClock =
      directory.directory.writeClock + 1 := by
  have facts := directory.frame_agrees before member
  simp only [commitDirectory, receive_view before after wanted value received]
  rw [facts.1.2.2.2]

private theorem commitDirectory_find (directory : DirectoryReadback) (before after : FrameReadback)
    (member : before ∈ directory.frames) (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) (handle : Nat) :
    (commitDirectory directory before after member wanted value received).frames.find?
        (fun frame => frame.view.token.handle == handle) =
      (directory.frames.find? (fun frame => frame.view.token.handle == handle)).map
        (directoryFrame before after) := by
  simp only [commitDirectory, List.find?_map]
  congr 2
  funext frame
  change ((directoryFrame before after frame).view.token.handle == handle) =
    (frame.view.token.handle == handle)
  rw [directoryFrame_handle before after wanted value received]

set_option backward.isDefEq.respectTransparency false in
/-- The constructed next directory decodes to precisely the independent common
store write, rather than only asserting a relation for a selected frame. -/
theorem commitDirectory_toImage (directory : DirectoryReadback) (before after : FrameReadback)
    (member : before ∈ directory.frames) (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) :
    (commitDirectory directory before after member wanted value received).toImage =
      commitImage directory.toImage after := by
  have view := receive_view before after wanted value received
  have selected := directory.select_frame before member
  have bound := (directory.frame_agrees before member).2
  unfold DirectoryReadback.toImage commitImage
  congr 1
  apply Array.ext_getElem?
  intro index
  by_cases indexBound : index < directory.capacity
  · simp only [Array.getElem?_setIfInBounds, Array.getElem?_ofFn]
    simp only [commitDirectory, Array.size_ofFn] at indexBound ⊢
    simp only [indexBound, dite_true]
    have foundEq := commitDirectory_find directory before after member wanted value received index
    change (directory.frames.map (directoryFrame before after)).find?
        (fun frame => frame.view.token.handle == index) = _ at foundEq
    rw [foundEq]
    by_cases same : before.view.token.handle = index
    · subst index
      simp [view, selected, directoryFrame, bound]
    · have different : after.view.token.handle ≠ index := by simpa [view] using same
      simp only [different, ite_false, Option.map_map, Function.comp_def]
      cases found : directory.frames.find? (fun frame => frame.view.token.handle == index) with
      | none => rfl
      | some frame =>
        have frameHandle : frame.view.token.handle = index := by
          have matched := List.find?_some (p := fun row : FrameReadback =>
            row.view.token.handle == index) found
          exact beq_iff_eq.mp matched
        have other : frame.view.token.handle ≠ before.view.token.handle := by
          rw [frameHandle]
          exact Ne.symm same
        simp [directoryFrame, other]
  · have notAfter : after.view.token.handle ≠ index := by
      rw [view]
      intro same
      exact indexBound (same ▸ bound)
    simp [commitDirectory, indexBound]

/-- Reacquire the saved destination from the complete current directory. The
shared clock and generation are read afresh for every receipt. -/
def receiveDirectory? (directory : DirectoryReadback) (wanted : Destination)
    (value : BindingValueView) : Option DirectoryReadback :=
  match selected : directory.frames.find? (fun frame =>
      frame.view.token.handle == wanted.token.handle) with
  | none => none
  | some before =>
    match received : receive? before wanted value with
    | none => none
    | some after => some (commitDirectory directory before after
        (List.mem_of_find?_eq_some selected) wanted value received)

/-- A successful whole-directory receipt realizes the same common write at
the saved source coordinate. -/
theorem receiveDirectory_correspondence (directory after : DirectoryReadback)
    (wanted : Destination) (value : BindingValueView)
    (received : receiveDirectory? directory wanted value = some after) :
    directory.toImage.write? (wanted.token.ref wanted.slot) (some value) =
      some after.toImage := by
  unfold receiveDirectory? at received
  split at received
  · simp at received
  · next before selected =>
    split at received
    · simp at received
    · next frame receipt =>
      cases Option.some.inj received
      rw [commitDirectory_toImage]
      exact receive_directory_correspondence directory before frame
        (List.mem_of_find?_eq_some selected) wanted value receipt

theorem receiveDirectory_clock (directory after : DirectoryReadback)
    (wanted : Destination) (value : BindingValueView)
    (received : receiveDirectory? directory wanted value = some after) :
    after.directory.writeClock = directory.directory.writeClock + 1 := by
  unfold receiveDirectory? at received
  split at received
  · simp at received
  · split at received
    · simp at received
    · cases Option.some.inj received
      exact commitDirectory_clock _ _ _ _ _ _ _

/-- The complete directory keeps its lexical coordinates through the
successful receipt, including the unchanged ordering of sibling frames. -/
theorem commitDirectory_coordinates (directory : DirectoryReadback) (before after : FrameReadback)
    (member : before ∈ directory.frames) (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) :
    (commitDirectory directory before after member wanted value received).frames.map
        (fun frame => (frame.view.token,frame.slots.map FrameSlotView.varId)) =
      directory.frames.map (fun frame => (frame.view.token,frame.slots.map FrameSlotView.varId)) := by
  change (directory.frames.map (directoryFrame before after)).map _ = _
  rw [List.map_map]
  apply List.map_congr_left
  intro frame frameMember
  by_cases same : frame.view.token.handle = before.view.token.handle
  · have selected := directory.select_frame frame frameMember
    rw [same] at selected
    have frameEq : frame = before :=
      Option.some.inj (selected.symm.trans (directory.select_frame before member))
    subst frame
    have coordinates := receive_coordinates before after wanted value received
    have sameCoordinates :
        (after.view.token,after.slots.map FrameSlotView.varId) =
          (before.view.token,before.slots.map FrameSlotView.varId) :=
      Prod.ext coordinates.1 coordinates.2
    simpa [directoryFrame] using sameCoordinates
  · simp [directoryFrame,same,refreshClock]

theorem receiveDirectory_coordinates (directory after : DirectoryReadback)
    (wanted : Destination) (value : BindingValueView)
    (received : receiveDirectory? directory wanted value = some after) :
    after.frames.map (fun frame => (frame.view.token,frame.slots.map FrameSlotView.varId)) =
      directory.frames.map (fun frame => (frame.view.token,frame.slots.map FrameSlotView.varId)) := by
  unfold receiveDirectory? at received
  split at received
  · simp at received
  · split at received
    · simp at received
    · cases Option.some.inj received
      exact commitDirectory_coordinates _ _ _ _ _ _ _

/-- Sibling inventories keep their payloads, write versions, presentation and
activation boundaries; only their common directory clock is refreshed. -/
theorem commitDirectory_sibling (directory : DirectoryReadback) (before after : FrameReadback)
    (member : before ∈ directory.frames) (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) (sibling : FrameReadback)
    (siblingMember : sibling ∈ directory.frames)
    (different : sibling.view.token.handle ≠ before.view.token.handle) :
    refreshClock sibling after.view.writeClock (clock_bounded after) ∈
      (commitDirectory directory before after member wanted value received).frames ∧
    (refreshClock sibling after.view.writeClock (clock_bounded after)).toEntry =
      sibling.toEntry := by
  refine ⟨?_, rfl⟩
  change _ ∈ directory.frames.map (directoryFrame before after)
  exact List.mem_map.mpr ⟨sibling, siblingMember, by simp [directoryFrame, different]⟩

theorem receiveDirectory_of_member (directory : DirectoryReadback) (before after : FrameReadback)
    (member : before ∈ directory.frames) (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) :
    receiveDirectory? directory wanted value =
      some (commitDirectory directory before after member wanted value received) := by
  have selected := directory.select_frame before member
  have handle : wanted.token.handle = before.view.token.handle := by
    obtain ⟨slot, _, _, same, _, _⟩ :=
      (receive_success_iff before after wanted value).mp received
    simp only [same, destination]
  have selectedWanted : directory.frames.find? (fun frame =>
      frame.view.token.handle == wanted.token.handle) = some before := by
    simpa only [handle] using selected
  unfold receiveDirectory?
  split
  · next missing => rw [selectedWanted] at missing; cases missing
  · next frame found =>
    have same := Option.some.inj (found.symm.trans selectedWanted)
    subst frame
    split
    · next missing => rw [received] at missing; cases missing
    · next written wrote =>
      have same := Option.some.inj (wrote.symm.trans received)
      subst written
      rfl

private theorem commitDirectory_metadata (directory : DirectoryReadback)
    (before after : FrameReadback) (member : before ∈ directory.frames)
    (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) (handle : Nat) :
    ((commitDirectory directory before after member wanted value received).toImage.frameAt handle).map
        (fun entry => (entry.generation, entry.frame)) =
      (directory.toImage.frameAt handle).map (fun entry => (entry.generation, entry.frame)) := by
  have view := receive_view before after wanted value received
  have sameHandle : after.view.token.handle = before.view.token.handle := by rw [view]
  have identity : after.toEntry.generation = before.toEntry.generation ∧
      after.toEntry.frame = before.toEntry.frame := by
    obtain ⟨slot, valid, room, _, _, rfl⟩ :=
      (receive_success_iff before after wanted value).mp received
    have preserved := write_preserves_identity before slot value valid room
    exact ⟨preserved.2.1, preserved.1⟩
  have facts := directory.frame_agrees before member
  have present := directory.toImage_frameAt before.view.token.handle facts.2
  rw [directory.select_frame before member, Option.map_some] at present
  rw [commitDirectory_toImage]
  change (((directory.toImage.entries.setIfInBounds after.view.token.handle
      (some after.toEntry))[handle]?).getD none).map _ = _
  by_cases selected : handle = before.view.token.handle
  · subst handle
    rw [sameHandle, Array.getElem?_setIfInBounds_self_of_lt
      (by simpa [DirectoryReadback.toImage] using facts.2)]
    change (some after.toEntry).map _ = _
    rw [present]
    simpa only [Option.map_some, Option.some.injEq, Prod.mk.injEq] using identity
  · have other : after.view.token.handle ≠ handle := by
      rw [sameHandle]
      exact Ne.symm selected
    rw [Array.getElem?_setIfInBounds_ne other]
    rfl

/-- Every packed framed identifier keeps its coordinate across a successful
receipt, including stale or missing identifiers that still select nothing. -/
theorem receiveDirectory_preserves_coordinates (directory after : DirectoryReadback)
    (wanted : Destination) (value : BindingValueView)
    (received : receiveDirectory? directory wanted value = some after) (identifier : BitVec 64) :
    after.variableCoordinate? identifier = directory.variableCoordinate? identifier := by
  have metadata : ∀ handle,
      (after.toImage.frameAt handle).map (fun entry => (entry.generation, entry.frame)) =
        (directory.toImage.frameAt handle).map (fun entry => (entry.generation, entry.frame)) := by
    intro handle
    unfold receiveDirectory? at received
    split at received
    · simp at received
    · next before selected =>
      split at received
      · simp at received
      · next frame receipt =>
        cases Option.some.inj received
        exact commitDirectory_metadata directory before frame
          (List.mem_of_find?_eq_some selected) wanted value receipt handle
  unfold DirectoryReadback.variableCoordinate? DirectoryReadback.sourceCoordinate?
  cases decoded : decode? (variableEpoch identifier) with
  | none => rfl
  | some token =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    have same := metadata token.handle
    cases old : directory.toImage.frameAt token.handle with
    | none =>
      cases new : after.toImage.frameAt token.handle with
      | none => rfl
      | some entry => simp [old, new] at same
    | some oldEntry =>
      cases new : after.toImage.frameAt token.handle with
      | none => simp [old, new] at same
      | some newEntry =>
        simp only [old, new, Option.map_some, Option.some.injEq, Prod.mk.injEq] at same
        simp only [Option.bind_some, same.1, same.2]

private theorem image_readSlot_write (before after : Shared.ImageOf BindingValueView)
    (ref : Ref) (value : BindingValueView)
    (written : before.write? ref (some value) = some after) :
    ∃ boundary, after.readSlot? ref =
        some ⟨some value, after.writeClock, after.writeClock, boundary⟩ ∧
      (before.frameAt ref.handle).map EntryOf.activationBoundary = some boundary := by
  change (MetavariableFrameStore.write? ⟨before.entries, 0, before.writeClock⟩ ref (some value)).map
    (fun store => (⟨store.entries, store.writeClock⟩ : Shared.ImageOf BindingValueView)) =
      some after at written
  obtain ⟨store, wrote, same⟩ := Option.map_eq_some_iff.mp written
  cases same
  obtain ⟨boundary, read, previous⟩ := readSlot?_write wrote
  refine ⟨boundary, ?_, previous⟩
  change MetavariableFrameStore.readSlot? ⟨store.entries, 0, store.writeClock⟩ ref = _
  simpa only [MetavariableFrameStore.readSlot?, frameAt] using read

/-- Join an actual variable-header interpretation to receipt and readback:
the saved source coordinate now reads the child value and its fresh version,
under the next shared directory clock and the original activation boundary. -/
theorem receiveDirectory_readVariableSlot_selected (directory after : DirectoryReadback)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length) (value : BindingValueView)
    (received : receiveDirectory? directory (destination frame index) value = some after)
    (memory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory) (operand : BindingValueView)
    (identifier : readVariableId? memory operand = some frame.slots[index.val].varId) :
    after.readVariableSlot? memory operand =
      some ⟨some value, directory.directory.writeClock + 1,
        directory.directory.writeClock + 1, frame.view.boundary⟩ := by
  have coordinate := directory.variableCoordinate_slot frame member index
  have coordinateAfter := receiveDirectory_preserves_coordinates directory after
    (destination frame index) value received frame.slots[index.val].varId
  rw [coordinate] at coordinateAfter
  have written := receiveDirectory_correspondence directory after
    (destination frame index) value received
  change directory.toImage.write? (frame.view.token.ref index.val) (some value) =
    some after.toImage at written
  obtain ⟨boundary, read, previous⟩ := image_readSlot_write _ _ _ _ written
  have facts := directory.frame_agrees frame member
  have present := directory.toImage_frameAt frame.view.token.handle facts.2
  rw [directory.select_frame frame member, Option.map_some] at present
  change (directory.toImage.frameAt frame.view.token.handle).map EntryOf.activationBoundary =
    some boundary at previous
  rw [present] at previous
  have boundarySame : boundary = frame.view.boundary := by
    exact (Option.some.inj previous).symm
  rw [boundarySame] at read
  have clock := receiveDirectory_clock directory after (destination frame index) value received
  change after.toImage.writeClock = directory.directory.writeClock + 1 at clock
  rw [clock] at read
  unfold DirectoryReadback.readVariableSlot?
  rw [identifier]
  change (after.variableCoordinate? frame.slots[index.val].varId).bind
    (fun ref => after.toImage.readSlot? ref) = _
  rw [coordinateAfter]
  exact read

/-! ## Captured directory observation

The directory supplies the complete saved inventory used to decode the packed
variable. The captured image supplies the slot values and metadata. Successful
whole capture proves that those inventories agree; retaining a frame token
does not prove that the borrowed Atom header or its payload storage is live,
and it grants no right to force a computation.
-/

/-- Read a borrowed contextual variable against an owned captured frame image.
The Atom-header reading remains explicit and does not acquire a storage owner. -/
def readCapturedVariableSlot? (directory : DirectoryReadback)
    (captured : Shared.ImageOf BindingValueView) (allocator : Shared.Allocator)
    (memory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory) (operand : BindingValueView) :
    Option (SlotReadbackOf BindingValueView) := do
  let identifier ← readVariableId? memory operand
  let coordinate ← directory.variableCoordinate? identifier
  captured.readSlotOwned? allocator coordinate

/-- The native packed-variable route commutes with complete image capture and
every allocator history in which the escaped holder keeps its retained counts.
Missing, stale and unbound slots retain their respective outcomes. -/
theorem captureAll_readVariableSlot (directory : DirectoryReadback)
    {allocator retained after : Shared.Allocator} {captured : Shared.ImageOf BindingValueView}
    (success : directory.toImage.captureAll? allocator = some (retained, captured))
    (held : ∀ token ∈ directory.toImage.inventory, Shared.HeldTrace token retained after)
    (memory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory) (operand : BindingValueView) :
    readCapturedVariableSlot? directory captured after memory operand =
      directory.readVariableSlot? memory operand := by
  unfold readCapturedVariableSlot? DirectoryReadback.readVariableSlot?
  cases read : readVariableId? memory operand with
  | none => rfl
  | some identifier =>
    change (directory.variableCoordinate? identifier).bind
      (fun ref => captured.readSlotOwned? after ref) =
      (directory.variableCoordinate? identifier).bind
        (fun ref => directory.toImage.readSlot? ref)
    cases coordinate : directory.variableCoordinate? identifier with
    | none => rfl
    | some ref =>
      exact Shared.ImageOf.escape_readSlot_captureAll success held ref

/-- Observe an authored variable through the retained owned image. The same
inventory and activation boundary apply before and after source release.
The borrowed memory remains fixed; this observer does not retain its storage
or reconstruct an activation view at a new context address. -/
def readCapturedActivationValue? (directory : DirectoryReadback)
    (captured : Shared.ImageOf BindingValueView) (allocator : Shared.Allocator)
    (memory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory)
    (inventory : Activation.Inventory) (source : Mettapedia.GSLT.LanguageDef.NativeOps.Address) :
    Option Activation.Lookup :=
  inventory.lookup memory (readCapturedVariableSlot? directory captured allocator memory) source

/-- Complete capture transports the activation observer itself, including
known-open versus unknown and the view's retained write boundary. This remains
valid after releasing the source holder while the captured counts stay held. -/
theorem captureAll_readActivationValue (directory : DirectoryReadback)
    {allocator retained after : Shared.Allocator} {captured : Shared.ImageOf BindingValueView}
    (success : directory.toImage.captureAll? allocator = some (retained, captured))
    (held : ∀ token ∈ directory.toImage.inventory, Shared.HeldTrace token retained after)
    (memory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory)
    (inventory : Activation.Inventory) (source : Mettapedia.GSLT.LanguageDef.NativeOps.Address) :
    readCapturedActivationValue? directory captured after memory inventory source =
      Activation.readValue? directory memory inventory source := by
  have readers : readCapturedVariableSlot? directory captured after memory =
      directory.readVariableSlot? memory := by
    funext operand
    exact captureAll_readVariableSlot directory success held memory operand
  unfold readCapturedActivationValue? Activation.readValue?
  rw [readers]

/-- The subsequent authored action is also unchanged: ownership transport
does not turn an open scoped value into permission to enter another context. -/
theorem captureAll_activationAction (directory : DirectoryReadback)
    {allocator retained after : Shared.Allocator} {captured : Shared.ImageOf BindingValueView}
    (success : directory.toImage.captureAll? allocator = some (retained, captured))
    (held : ∀ token ∈ directory.toImage.inventory, Shared.HeldTrace token retained after)
    (memory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory)
    (inventory : Activation.Inventory) (source : Mettapedia.GSLT.LanguageDef.NativeOps.Address)
    (cursor : Activation.Cursor) :
    (readCapturedActivationValue? directory captured after memory inventory source).bind
        (Activation.nextAction? memory cursor) =
      (Activation.readValue? directory memory inventory source).bind
        (Activation.nextAction? memory cursor) := by
  rw [captureAll_readActivationValue directory success held]

/-- Native Atom fields and the saved authority word determine the exact
captured slot observation after every permitted ownership history. -/
theorem captureAll_activationSourceSlot (directory : DirectoryReadback)
    {allocator retained after : Shared.Allocator} {captured : Shared.ImageOf BindingValueView}
    (success : directory.toImage.captureAll? allocator = some (retained, captured))
    (held : ∀ token ∈ directory.toImage.inventory, Shared.HeldTrace token retained after)
    (memory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory)
    (inventory : Activation.Inventory) (source : Mettapedia.GSLT.LanguageDef.NativeOps.Address)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length)
    (identity : inventory.view.authority = encode frame.view.token)
    (known : frame.slots[index.val].sourceId ∈ inventory.sources)
    (kind : Mettapedia.GSLT.LanguageDef.NativeOps.targetRead memory
      (Mettapedia.GSLT.LanguageDef.NativeOps.sourceFieldAddress source 0) = some (.word 1))
    (sourceId : Mettapedia.GSLT.LanguageDef.NativeOps.targetRead memory
      (Mettapedia.GSLT.LanguageDef.NativeOps.sourceFieldAddress source 2) =
        some (.word frame.slots[index.val].sourceId)) :
    readCapturedActivationValue? directory captured after memory inventory source =
      some (.known (if inventory.view.firstWrite < frame.slots[index.val].writeVersion
        then frame.slots[index.val].value.payload else none)) := by
  rw [captureAll_readActivationValue directory success held]
  exact Activation.readValue?_source_slot directory memory inventory source frame member index
    identity known kind sourceId

/-- An actual Atom-header reading selects the independently admitted native
slot before applying the whole-image escape law. Payload options, write stamps,
activation boundaries and the captured common clock survive source release. -/
theorem captureAll_readVariableSlot_current (directory : DirectoryReadback)
    {allocator retained after : Shared.Allocator} {captured : Shared.ImageOf BindingValueView}
    (success : directory.toImage.captureAll? allocator = some (retained, captured))
    (held : ∀ token ∈ directory.toImage.inventory, Shared.HeldTrace token retained after)
    (memory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory) (operand : BindingValueView)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length)
    (identifier : readVariableId? memory operand = some frame.slots[index.val].varId) :
    readCapturedVariableSlot? directory captured after memory operand =
      some ⟨frame.slots[index.val].value.payload, frame.slots[index.val].writeVersion,
        directory.directory.writeClock, frame.view.boundary⟩ := by
  rw [captureAll_readVariableSlot directory success held]
  have current := directory.readVariableSlot_current memory operand frame member index identifier
  rw [(directory.frame_agrees frame member).1.2.2.2] at current
  exact current

/-- The independently constructed receipt, native coordinate and ownership
escape laws compose: a captured successful return keeps its new slot stamp
after the original frame owners leave. -/
theorem receiveDirectory_captureAll_readVariableSlot_selected (directory written : DirectoryReadback)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length) (value : BindingValueView)
    (received : receiveDirectory? directory (destination frame index) value = some written)
    {allocator retained after : Shared.Allocator} {captured : Shared.ImageOf BindingValueView}
    (success : written.toImage.captureAll? allocator = some (retained, captured))
    (held : ∀ token ∈ written.toImage.inventory, Shared.HeldTrace token retained after)
    (memory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory) (operand : BindingValueView)
    (identifier : readVariableId? memory operand = some frame.slots[index.val].varId) :
    readCapturedVariableSlot? written captured after memory operand =
      some ⟨some value, directory.directory.writeClock + 1,
        directory.directory.writeClock + 1, frame.view.boundary⟩ := by
  rw [captureAll_readVariableSlot written success held]
  exact receiveDirectory_readVariableSlot_selected directory written frame member index
    value received memory operand identifier

/-- The last owner release revokes observation of the old incarnation even if
the saved directory and captured payload remain available as immutable data. -/
theorem capturedVariable_final_release (directory : DirectoryReadback)
    (captured : Shared.ImageOf BindingValueView) (memory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory)
    (operand : BindingValueView) (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length)
    (identifier : readVariableId? memory operand = some frame.slots[index.val].varId)
    {allocator released after : Shared.Allocator} {cell : Shared.Cell}
    (present : allocator.cells[frame.view.token.handle]? = some cell)
    (lastOwner : cell.owners = 1)
    (release : Shared.release? allocator frame.view.token = some released)
    (history : Shared.Trace released after) :
    readCapturedVariableSlot? directory captured after memory operand = none := by
  have dead := Shared.final_release_never_revives present lastOwner release history
  unfold readCapturedVariableSlot?
  rw [identifier]
  change (directory.variableCoordinate? frame.slots[index.val].varId).bind _ = _
  rw [directory.variableCoordinate_slot frame member index]
  simpa [Shared.ImageOf.readSlotOwned?, Shared.Token.ref] using
    (if_neg dead : (if Shared.Live after frame.view.token then
      captured.readSlot? (frame.view.token.ref index.val) else none) = none)

/-- A stale authority cannot license a saved current-coordinate read, whatever
later allocator actions occur. No rewriting of the borrowed operand repairs it. -/
theorem capturedVariable_stale_authority (directory : DirectoryReadback)
    (captured : Shared.ImageOf BindingValueView) (memory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory)
    (operand : BindingValueView) (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length)
    (identifier : readVariableId? memory operand = some frame.slots[index.val].varId)
    {allocator after : Shared.Allocator} {cell : Shared.Cell}
    (present : allocator.cells[frame.view.token.handle]? = some cell)
    (older : frame.view.token.generation < cell.generation)
    (history : Shared.Trace allocator after) :
    readCapturedVariableSlot? directory captured after memory operand = none := by
  have dead := Shared.stale_forever present older history
  unfold readCapturedVariableSlot?
  rw [identifier]
  change (directory.variableCoordinate? frame.slots[index.val].varId).bind _ = _
  rw [directory.variableCoordinate_slot frame member index]
  simpa [Shared.ImageOf.readSlotOwned?, Shared.Token.ref] using
    (if_neg dead : (if Shared.Live after frame.view.token then
      captured.readSlot? (frame.view.token.ref index.val) else none) = none)

/-- Reusing the established snapshot rollback restores all caller bindings
while retaining the consumed write-clock reading. This is whole-image rollback,
not the native conditional per-slot undo loop. -/
theorem receive_rollback (store : StoreOf BindingValueView)
    (before after : FrameReadback)
    (present : frameAt store before.view.token.handle = some before.toEntry)
    (clock : store.writeClock = before.view.writeClock)
    (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) :
    (∀ ref, lookup (rollback (commit store after) store) ref = lookup store ref) ∧
      (rollback (commit store after) store).writeClock = store.writeClock + 1 := by
  refine ⟨fun ref => lookup_rollback _ _ ref, ?_⟩
  rw [rollback_preserves_clock]
  exact write_advances_clock
    (receive_correspondence store before after present clock wanted value received)

/-- The machine-word increment agrees with the unbounded semantic clock under
the same overflow guard used by writeback. -/
theorem native_version_increment (clock : Nat) (room : clock + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 clock + 1).toNat = clock + 1 := by
  have bounded : clock < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  change (clock % 2 ^ 64 + 1) % 2 ^ 64 = clock + 1
  rw [Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt room]

theorem receive_wrong_world (before : FrameReadback) (wanted : Destination)
    (value : BindingValueView) (wrong : before.view.bindings ≠ wanted.bindings) :
    receive? before wanted value = none := by
  simp [receive?, wrong]

theorem receive_stale_generation (before : FrameReadback) (wanted : Destination)
    (value : BindingValueView) (wrong : before.view.token ≠ wanted.token) :
    receive? before wanted value = none := by
  simp [receive?, wrong]

theorem receive_wrong_source (before : FrameReadback) (wanted : Destination)
    (value : BindingValueView) (bound : wanted.slot < before.slots.length)
    (wrong : before.slots[wanted.slot].sourceId ≠ wanted.sourceId) :
    receive? before wanted value = none := by
  simp [receive?, bound, wrong]

theorem receive_clock_exhausted (before : FrameReadback) (wanted : Destination)
    (value : BindingValueView) (full : 2 ^ 64 ≤ before.view.writeClock + 1) :
    receive? before wanted value = none := by
  have blocked : ¬ before.view.writeClock + 1 < 2 ^ 64 := Nat.not_lt.mpr full
  simp only [receive?, blocked, dite_false, dite_eq_ite, ite_self]

theorem receive_unbound (before : FrameReadback) (wanted : Destination)
    (value : BindingValueView) (unbound : value.skeleton = none) :
    receive? before wanted value = none := by
  simp [receive?, unbound]

/-- Reacquiring the frame after moving its directory retains the destination.
This describes readback transport, not a proof that copying acquires ownership. -/
def relocateDirectory (before : FrameReadback) (directory : Address) : FrameReadback :=
  ⟨{ before.view with directory := directory }, before.slots, before.admitted⟩

theorem destination_relocated (before : FrameReadback) (directory : Address)
    (slot : Fin before.slots.length) :
    destination (relocateDirectory before directory) slot = destination before slot := rfl

theorem receive_relocated (before : FrameReadback) (directory : Address)
    (wanted : Destination) (value : BindingValueView) :
    receive? (relocateDirectory before directory) wanted value =
      (receive? before wanted value).map (fun after => relocateDirectory after directory) := by
  cases ran : receive? before wanted value with
  | some after =>
    obtain ⟨slot, valid, room, rfl, bound, rfl⟩ :=
      (receive_success_iff before after wanted value).mp ran
    rw [Option.map_some, ← destination_relocated before directory slot,
      receive_current (relocateDirectory before directory) slot value valid bound room]
    rfl
  | none =>
    rw [Option.map_none]
    cases moved : receive? (relocateDirectory before directory) wanted value with
    | none => rfl
    | some after =>
      obtain ⟨slot, valid, room, same, bound, _⟩ :=
        (receive_success_iff (relocateDirectory before directory) after wanted value).mp moved
      change wanted = destination before slot at same
      rw [same, receive_current before slot value valid bound room] at ran
      cases ran

/-- Transport only directory aliases in the complete borrowed inventory.
Supplying the new native header is a separate readback obligation. -/
def relocateDirectoryView (before : DirectoryReadback) (address : Address) :
    DirectoryReadback where
  directory := { before.directory with directory := some address }
  capacity := before.capacity
  frames := before.frames.map (fun frame => relocateDirectory frame address)
  admitted := by
    rcases before.admitted with ⟨admitted, count, distinct, entries⟩
    rcases admitted with ⟨size, revision, clock, _⟩
    refine ⟨⟨size, revision, clock, by simp⟩, by simpa using count, ?_, ?_⟩
    · simpa [relocateDirectory, List.map_map, Function.comp_def] using distinct
    · intro index
      have bound : index.val < before.frames.length := by simpa using index.isLt
      have facts := entries ⟨index.val, bound⟩
      simp only [List.getElem_map, relocateDirectory]
      exact ⟨⟨facts.1.1, rfl, facts.1.2.2.1, facts.1.2.2.2⟩, facts.2⟩

/-- A reacquired header may change its directory address, but not its binding
world, cardinality, schema revision or clock. This check acquires no owner. -/
def reheaderDirectory? (before : DirectoryReadback) (header : FrameDirectoryView) :
    Option DirectoryReadback :=
  match header.directory with
  | none => none
  | some address =>
      if header = { before.directory with directory := some address } then
        some (relocateDirectoryView before address)
      else none

theorem reheaderDirectory_current (before : DirectoryReadback) (address : Address) :
    reheaderDirectory? before { before.directory with directory := some address } =
      some (relocateDirectoryView before address) := by
  simp [reheaderDirectory?]

theorem relocateDirectoryView_toImage (before : DirectoryReadback) (address : Address) :
    (relocateDirectoryView before address).toImage = before.toImage := by
  unfold DirectoryReadback.toImage relocateDirectoryView
  congr 1
  congr 1
  funext handle
  simp only [List.find?_map, Option.map_map, Function.comp_def, relocateDirectory]
  rfl

/-- A saved source coordinate remains receivable after a checked directory
reheader. Its binding-world address, frame generation and source ID are retained. -/
theorem receiveDirectory_relocated_member (directory : DirectoryReadback) (address : Address)
    (before after : FrameReadback) (member : before ∈ directory.frames)
    (wanted : Destination) (value : BindingValueView)
    (received : receive? before wanted value = some after) :
    (receiveDirectory? (relocateDirectoryView directory address) wanted value).isSome = true := by
  have relocated : receive? (relocateDirectory before address) wanted value =
      some (relocateDirectory after address) := by
    rw [receive_relocated, received]
    rfl
  have relocatedMember : relocateDirectory before address ∈
      (relocateDirectoryView directory address).frames :=
    List.mem_map.mpr ⟨before, member, rfl⟩
  rw [receiveDirectory_of_member (relocateDirectoryView directory address)
    (relocateDirectory before address) (relocateDirectory after address)
    relocatedMember wanted value relocated]
  rfl

/-! ## Shared continuation protocol

The provider makes refusal an explicit reply and retains the current image.
Clients decide whether to retry, fall back or stop. No HE/PeTTa normalization,
search order, substitution rule or Prime force permission is imposed here.
-/

open Mettapedia.TypeTheory (IndexedPolynomial)
open Mettapedia.Machines.Cursor

abbrev protocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Destination × BindingValueView
  Position _ := Bool
  next _ _ := ()

/-- The local provider is restricted to one current frame with no intervening
directory writes. Use `directoryProvider` for a complete framed world. -/
def provider : Provider protocol where
  State _ _ := FrameReadback
  step before request :=
    match receive? before request.1 request.2 with
    | none => ⟨false, before⟩
    | some after => ⟨true, after⟩

/-- Failure is observable and preserves the image for the caller's fallback. -/
theorem provider_refused (before : FrameReadback) (wanted : Destination)
    (value : BindingValueView) (refused : receive? before wanted value = none) :
    provider.step (base := ()) (index := ()) before (wanted, value) = ⟨false, before⟩ := by
  simp [provider, refused]

theorem provider_accepted (before after : FrameReadback) (wanted : Destination)
    (value : BindingValueView) (received : receive? before wanted value = some after) :
    provider.step (base := ()) (index := ()) before (wanted, value) = ⟨true, after⟩ := by
  simp [provider, received]

/-- Shared continuation service over the complete framed binding world. Each
request reacquires its frame under the single current directory clock. -/
def directoryProvider : Provider protocol where
  State _ _ := DirectoryReadback
  step before request :=
    match receiveDirectory? before request.1 request.2 with
    | none => ⟨false, before⟩
    | some after => ⟨true, after⟩

theorem directoryProvider_refused (before : DirectoryReadback) (wanted : Destination)
    (value : BindingValueView) (refused : receiveDirectory? before wanted value = none) :
    directoryProvider.step (base := ()) (index := ()) before (wanted, value) =
      ⟨false, before⟩ := by
  simp [directoryProvider, refused]

theorem directoryProvider_accepted (before after : DirectoryReadback) (wanted : Destination)
    (value : BindingValueView) (received : receiveDirectory? before wanted value = some after) :
    directoryProvider.step (base := ()) (index := ()) before (wanted, value) =
      ⟨true, after⟩ := by
  simp [directoryProvider, received]

theorem directoryProvider_correspondence (before after : DirectoryReadback)
    (wanted : Destination) (value : BindingValueView)
    (accepted : directoryProvider.step (base := ()) (index := ()) before
      (wanted, value) = ⟨true, after⟩) :
    before.toImage.write? (wanted.token.ref wanted.slot) (some value) =
      some after.toImage := by
  cases received : receiveDirectory? before wanted value with
  | none => simp [directoryProvider, received] at accepted
  | some written =>
    have same : written = after := by simpa [directoryProvider, received] using accepted
    exact receiveDirectory_correspondence before after wanted value (same ▸ received)

/-- Abstract refusal retains the entire directory and consumes no write version.
This does not assert that a failed native helper preserves physical aliases. -/
theorem directoryProvider_refusal_clock (before after : DirectoryReadback)
    (wanted : Destination) (value : BindingValueView)
    (refused : directoryProvider.step (base := ()) (index := ()) before
      (wanted, value) = ⟨false, after⟩) :
    after = before ∧ after.directory.writeClock = before.directory.writeClock := by
  cases received : receiveDirectory? before wanted value with
  | none =>
    have same : before = after := by simpa [directoryProvider, received] using refused
    subst after
    exact ⟨rfl, rfl⟩
  | some written => simp [directoryProvider, received] at refused

theorem directory_resume_exact {Return : Unit → Unit → Type}
    (client : Client (P := protocol) (Return := Return)) (charge : Charge directoryProvider)
    (first second : Nat) (previous : Nat × Outcome directoryProvider client ()) :
    resume directoryProvider client charge second
        (resume directoryProvider client charge first previous) =
      resume directoryProvider client charge (first + second) previous :=
  (resume_add directoryProvider client charge first second previous).symm

/-- Receipt has the independent semantic effect even when embedded in an
arbitrary client's operation; the Boolean result is not collapsed into data. -/
theorem provider_store_correspondence (store : StoreOf BindingValueView)
    (before after : FrameReadback)
    (present : frameAt store before.view.token.handle = some before.toEntry)
    (clock : store.writeClock = before.view.writeClock)
    (wanted : Destination) (value : BindingValueView)
    (accepted : provider.step (base := ()) (index := ()) before (wanted, value) = ⟨true, after⟩) :
    MetavariableFrameStore.write? store (wanted.token.ref wanted.slot) (some value) =
      some (commit store after) := by
  cases received : receive? before wanted value with
  | none => simp [provider, received] at accepted
  | some written =>
    have same : written = after := by simpa [provider, received] using accepted
    exact receive_correspondence store before after present clock wanted value (same ▸ received)

/-- Any recursive client retains its exact control, frame image and cumulative
receipts across a scheduling pause. Charges here remain protocol observations. -/
theorem resume_exact {Return : Unit → Unit → Type}
    (client : Client (P := protocol) (Return := Return)) (charge : Charge provider)
    (first second : Nat) (previous : Nat × Outcome provider client ()) :
    resume provider client charge second (resume provider client charge first previous) =
      resume provider client charge (first + second) previous :=
  (resume_add provider client charge first second previous).symm


end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback

/-! ## Selected physical current-value copy

The admitted block appears after a frame and slot have been selected. Its
logical-cell execution retains all three BindingValue fields and the actual
array stride; it does not re-run directory lookup or claim a byte-ABI theorem.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.CurrentValueRead
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.LanguageDef.NativeOps (Address TargetValue)
open StatementBlock

def bindingValueType : CType := ⟨"BindingValue".toList, 0⟩
def frameType : CType := ⟨"BindingsFrameIndexEntry".toList, 0⟩
def framePointerType : CType := ⟨"BindingsFrameIndexEntry".toList, 1⟩
def valuePointerType : CType := ⟨"BindingValue".toList, 1⟩
def slotType : CType := ⟨"uint32_t".toList, 0⟩

def frameLayout : ReadExpressions.Layout := fun name =>
  if name = "values".toList then some ⟨4, .pointer⟩ else none

def profile : ObjectBindings.Profile where
  values := ReadExpressions.noCalls
  locations := fun _ => none
  outsideTypes := fun _ => none
  outsidePlaces := fun _ => none
  fieldTypes := fun type name =>
    if type = frameType ∧ name = "values".toList then some valuePointerType else none
  cellExtent := fun type => if type = bindingValueType then some 3 else none
  recordTypes := [bindingValueType]
  byteExtent := fun type => if type = bindingValueType then some 16 else none
  sizeWidth := .bits64
  recordFields := some (fun type => if type = frameType then frameLayout else fun _ => none)

def context (frame destination : Ptr) (slot : UInt32) : ObjectBindings.Context := fun name =>
  if name = "frame".toList then some (.scalar framePointerType (some (.ptr (some frame))))
  else if name = "value_out".toList then some (.scalar valuePointerType (some (.ptr (some destination))))
  else if name = "slot".toList then some (.scalar slotType (some (.u32 slot))) else none

def frameExpr : CExpr := .identifier "frame".toList
def slotExpr : CExpr := .identifier "slot".toList
def outputExpr : CExpr := .unary .dereference (.identifier "value_out".toList)
def valuesExpr : CExpr := .field frameExpr "values".toList true

def copyBody : List CStatement :=
  [.assign outputExpr (.index valuesExpr slotExpr), .return (some (.bool true))]

def copySource : String := "{ *value_out = frame->values[slot]; return true; }"
def copyTokens : List Token :=
  [.punctuation "{".toList, .punctuation "*".toList, .identifier "value_out".toList,
   .punctuation "=".toList, .identifier "frame".toList, .punctuation "->".toList,
   .identifier "values".toList, .punctuation "[".toList, .identifier "slot".toList,
   .punctuation "]".toList, .punctuation ";".toList, .identifier "return".toList,
   .identifier "true".toList, .punctuation ";".toList, .punctuation "}".toList]

theorem copy_lex : lex copySource.toList = .ok copyTokens := by
  apply lex_of_completed
  decide +kernel

theorem copy_parsed : blockText? [] copySource.toList = some copyBody :=
  block_text_of_parts [] _ copyTokens _ copy_lex (by rfl)

def program (frame destination : Ptr) (slot : UInt32) :
    CProg CVal (ReadBlock.Result ObjectBindings.Context) :=
  StatementBlock.executeScopedWith
    (ObjectBindings.services profile (fun _ _ _ => CProg.undefined)
      (fun _ _ _ => CProg.undefined))
    frameLayout 0 3 (context frame destination slot) copyBody

def operations (frame destination : Ptr) (slot : UInt32) :
    CProg CVal (ReadBlock.Result ObjectBindings.Context) := do
  let storage ← CProg.loadPtr (frame + 4)
  match storage with
  | none => CProg.undefined
  | some storage => do
      CProg.copyCells (storage + slot.toNat * 3) destination 3
      pure (.finished (.returned (context frame destination slot) (some (.bool true))))

theorem output_place (frame destination : Ptr) (slot : UInt32) :
    ObjectBindings.place profile frameLayout (context frame destination slot) outputExpr =
      pure destination := rfl

def selectedPlace (frame : Ptr) (slot : UInt32) : CProg CVal Ptr := do
  let storage ← CProg.loadPtr (frame + 4)
  match storage with
  | none => CProg.undefined
  | some storage => pure (storage + slot.toNat * 3)

theorem values_read (frame destination : Ptr) (slot : UInt32) :
    ObjectBindings.read profile frameLayout (context frame destination slot) valuesExpr =
      (CProg.loadPtr (frame + 4) >>= fun storage => pure (.ptr storage)) := rfl

theorem slot_read (frame destination : Ptr) (slot : UInt32) :
    ObjectBindings.read profile frameLayout (context frame destination slot) slotExpr =
      pure (.u32 slot) := rfl

theorem selected_place (frame destination : Ptr) (slot : UInt32) :
    ObjectBindings.place profile frameLayout (context frame destination slot)
      (.index valuesExpr slotExpr) = selectedPlace frame slot := by
  rw [ObjectBindings.place,
    ReadExpressions.described_index_place_keeps_operands _ _ _ _ _ _ 3 (by rfl)]
  change (ObjectBindings.read profile frameLayout (context frame destination slot) valuesExpr >>=
    fun storage => ObjectBindings.read profile frameLayout (context frame destination slot) slotExpr >>=
    fun position => ReadExpressions.indexedPlace 3 storage position) = _
  rw [values_read, slot_read]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  unfold selectedPlace
  simp only [Prog.bind_eq]
  congr 1
  funext storage
  cases storage <;> rfl

theorem returns_true (frame destination : Ptr) (slot : UInt32) :
    StatementBlock.executeScopedWith
      (ObjectBindings.services profile (fun _ _ _ => CProg.undefined)
        (fun _ _ _ => CProg.undefined))
      frameLayout 0 2 (context frame destination slot) [.return (some (.bool true))] =
      pure (.finished (.returned (context frame destination slot) (some (.bool true)))) := rfl

theorem copy_uses_current_memory (frame destination : Ptr) (slot : UInt32) :
    program frame destination slot = operations frame destination slot := by
  unfold program copyBody
  rw [StatementBlock.scoped_assignment_keeps_continuation]
  change (ObjectBindings.assignment profile frameLayout (context frame destination slot)
    (.assign outputExpr (.index valuesExpr slotExpr)) >>= fun updated =>
      StatementBlock.executeScopedWith
        (ObjectBindings.services profile (fun _ _ _ => CProg.undefined)
          (fun _ _ _ => CProg.undefined)) frameLayout 0 2 updated
        [.return (some (.bool true))]) = _
  rw [ObjectBindings.record_assignment_retains_snapshot _ _ _ _ _ bindingValueType 3
    (by rfl) (by rfl) (by rfl)]
  rw [output_place, selected_place]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc, returns_true]
  unfold selectedPlace operations
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext storage
  cases storage with
  | none => exact ReadExpressions.undefined_bind _
  | some storage => simp only [Prog.pure_eq, Prog.ret_bind]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem current_value_copy_owned (frame storage destination : Ptr) (slot : UInt32)
    (value : List CVal) (old : List (Option CVal)) (valueWidth : value.length = 3)
    (oldWidth : old.length = 3) (rest : Heap L → Prop) :
    CTriple (PointsTo (frame + 4) (.ptr (some storage)) ∗
      Cells (storage + slot.toNat * 3) (value.map some) ∗ Cells destination old ∗ rest)
      (program frame destination slot)
      (fun result heap =>
        result = .finished (.returned (context frame destination slot) (some (.bool true))) ∧
        (PointsTo (frame + 4) (.ptr (some storage)) ∗
          Cells (storage + slot.toNat * 3) (value.map some) ∗
          Cells destination (value.map some) ∗ rest) heap) := by
  rw [copy_uses_current_memory]
  cmem_start heap held
  unfold operations
  simp only [CProg.loadPtr, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  have copying := copy_cells (L := L) (storage + slot.toNat * 3) destination old value
    (oldWidth.trans valueWidth.symm)
  simp only [valueWidth] at copying
  cmem_call copying
  rintro _ heap copied
  cmem_exact

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.CurrentValueRead

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.CurrentValueRead
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.LanguageDef.NativeOps (Address TargetValue)

def physicalAddress (pointer : Ptr) : Address := ⟨pointer.block, pointer.offset, []⟩
def valueCells (skeleton : Option Ptr) (epoch kind : UInt32) : List CVal :=
  [.ptr skeleton, .u32 epoch, .u32 kind]

def cellView (skeleton : Option Ptr) (epoch kind : UInt32) : BindingValueView :=
  ⟨skeleton.map physicalAddress, BitVec.ofNat 64 epoch.toNat, BitVec.ofNat 64 kind.toNat⟩

def readCells? : List CVal → Option BindingValueView
  | [.ptr skeleton, .u32 epoch, .u32 kind] => readBindingValue? (cellView skeleton epoch kind).toTarget
  | _ => none

theorem cellView_admissible (skeleton : Option Ptr) (epoch kind : UInt32)
    (kindBound : kind.toNat ≤ 2) : (cellView skeleton epoch kind).Admissible := by
  have epochBound := epoch.toNat_lt
  have typeBound := kind.toNat_lt
  simp only [cellView, BindingValueView.Admissible, BitVec.toNat_ofNat]
  omega

theorem read_value_cells (skeleton : Option Ptr) (epoch kind : UInt32)
    (kindBound : kind.toNat ≤ 2) :
    readCells? (valueCells skeleton epoch kind) = some (cellView skeleton epoch kind) := by
  simp only [readCells?, valueCells, readBindingValue?_toTarget,
    cellView_admissible skeleton epoch kind kindBound, ↓reduceIte]

/-- This is the selected physical copy joined to the established current-slot
observation. Frame/table lookup and layout ownership are distinct premises;
ordinary history rows cannot override the selected frame value. -/
theorem slot_readback (directory : DirectoryReadback) (rows : List OrdinaryBindings.Row)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length) (skeleton : Option Ptr) (epoch kind : UInt32)
    (kindBound : kind.toNat ≤ 2)
    (represented : frame.slots[index.val].value = cellView skeleton epoch kind) :
    (readCells? (valueCells skeleton epoch kind)).bind BindingValueView.payload =
      RootResolution.lookup directory rows frame.slots[index.val].varId := by
  rw [read_value_cells skeleton epoch kind kindBound,
    RootResolution.lookup_current_slot directory rows frame member index, represented]
  rfl

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

/-- Executing the selected parsed native block copies the complete contextual
value observed by the checked current frame. The postcondition keeps the
physical record and its semantic readback together; historical rows cannot
supply an alternate current value. -/
theorem current_value_copy_readback_owned {L : Type} [Zero L] [Add L] [SepAlgebra L]
    [CellPermission L (Option CVal)]
    (directory : DirectoryReadback) (rows : List OrdinaryBindings.Row)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length) (physicalFrame storage destination : Ptr)
    (slot epoch kind : UInt32) (sameSlot : slot.toNat = index.val) (skeleton : Option Ptr)
    (kindBound : kind.toNat ≤ 2)
    (represented : frame.slots[index.val].value = cellView skeleton epoch kind)
    (old : List (Option CVal)) (oldWidth : old.length = 3) (rest : Heap L → Prop) :
    CTriple (PointsTo (physicalFrame + 4) (.ptr (some storage)) ∗
      Cells (storage + index.val * 3) ((valueCells skeleton epoch kind).map some) ∗
      Cells destination old ∗ rest)
      (program physicalFrame destination slot)
      (fun result heap =>
        result = .finished (.returned (context physicalFrame destination slot) (some (.bool true))) ∧
        (readCells? (valueCells skeleton epoch kind)).bind BindingValueView.payload =
          RootResolution.lookup directory rows frame.slots[index.val].varId ∧
        (PointsTo (physicalFrame + 4) (.ptr (some storage)) ∗
          Cells (storage + index.val * 3) ((valueCells skeleton epoch kind).map some) ∗
          Cells destination ((valueCells skeleton epoch kind).map some) ∗ rest) heap) := by
  intro heap held
  have held' := held
  rw [← sameSlot] at held'
  obtain ⟨safe, post⟩ := current_value_copy_owned (L := L) physicalFrame storage destination slot
    (valueCells skeleton epoch kind) old rfl oldWidth rest heap held'
  refine ⟨safe, ?_⟩
  intro result final runs
  obtain ⟨returned, cells⟩ := post result final runs
  exact ⟨returned, slot_readback directory rows frame member index skeleton epoch kind
    kindBound represented, by simpa only [sameSlot] using cells⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.CurrentValueRead

/-! ## Physical contiguous source-slot selection

This selected block is the actual contiguous branch of the native slot
selector. Its enclosing null/invalid-ID guard and schema-mode selection are
separate entry obligations. The schema and slot-count reads are physical;
repeated source reads are retained in their original order. The final unsigned
cast uses the shared C11 conversion, and source identifiers are never narrowed
before interval admission. The sorted suffix is handled below; directory probing remains
separate components.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open StatementBlock

def uint32 : CType := ⟨"uint32_t".toList, 0⟩
def uint64 : CType := ⟨"uint64_t".toList, 0⟩
def framePointer : CType := ⟨"BindingsFrameIndexEntry".toList, 1⟩
def outputPointer : CType := ⟨"uint32_t".toList, 1⟩

def layout : ReadExpressions.Layout := fun name =>
  if name = "schema".toList then some ⟨2, .pointer⟩
  else if name = "source_first_id".toList then some ⟨3, .word64⟩
  else if name = "slot_len".toList then some ⟨8, .word⟩ else none

def profile : ObjectBindings.Profile where
  values := ReadExpressions.noCalls
  locations := fun _ => none
  outsideTypes := fun _ => none
  outsidePlaces := fun _ => none
  fieldTypes := fun _ _ => none
  cellExtent := fun _ => none
  byteExtent := fun _ => none
  sizeWidth := .bits64

def context (frame output : Ptr) (source : UInt64) : ObjectBindings.Context := fun name =>
  if name = "frame".toList then some (.scalar framePointer (some (.ptr (some frame))))
  else if name = "slot_out".toList then some (.scalar outputPointer (some (.ptr (some output))))
  else if name = "source_id".toList then some (.scalar uint64 (some (.u64 source))) else none

def id (name : String) : CExpr := .identifier name.toList

def firstId : CExpr := .field (.field (id "frame") "schema".toList true)
  "source_first_id".toList true

def slotLength : CExpr := .field (id "frame") "slot_len".toList true

def offsetTail : List CStatement :=
  [.branch (.binary .ge (id "offset") slotLength) [.return (some (.bool false))] [],
   .assign (.unary .dereference (id "slot_out")) (.cast uint32 (id "offset")),
   .return (some (.bool true))]

def body : List CStatement :=
  .branch (.binary .lt (id "source_id") firstId) [.return (some (.bool false))] [] ::
  .declare uint64 "offset".toList (.binary .sub (id "source_id") firstId) :: offsetTail

def source : String := "{\n        if (source_id < frame->schema->source_first_id)\n            return false;\n        uint64_t offset = source_id - frame->schema->source_first_id;\n        if (offset >= frame->slot_len)\n            return false;\n        *slot_out = (uint32_t)offset;\n        return true;\n    }"

def tokens : List Token :=
  [.punctuation "{".toList,
   .identifier "if".toList,
   .punctuation "(".toList,
   .identifier "source_id".toList,
   .punctuation "<".toList,
   .identifier "frame".toList,
   .punctuation "->".toList,
   .identifier "schema".toList,
   .punctuation "->".toList,
   .identifier "source_first_id".toList,
   .punctuation ")".toList,
   .identifier "return".toList,
   .identifier "false".toList,
   .punctuation ";".toList,
   .identifier "uint64_t".toList,
   .identifier "offset".toList,
   .punctuation "=".toList,
   .identifier "source_id".toList,
   .punctuation "-".toList,
   .identifier "frame".toList,
   .punctuation "->".toList,
   .identifier "schema".toList,
   .punctuation "->".toList,
   .identifier "source_first_id".toList,
   .punctuation ";".toList,
   .identifier "if".toList,
   .punctuation "(".toList,
   .identifier "offset".toList,
   .punctuation ">=".toList,
   .identifier "frame".toList,
   .punctuation "->".toList,
   .identifier "slot_len".toList,
   .punctuation ")".toList,
   .identifier "return".toList,
   .identifier "false".toList,
   .punctuation ";".toList,
   .punctuation "*".toList,
   .identifier "slot_out".toList,
   .punctuation "=".toList,
   .punctuation "(".toList,
   .identifier "uint32_t".toList,
   .punctuation ")".toList,
   .identifier "offset".toList,
   .punctuation ";".toList,
   .identifier "return".toList,
   .identifier "true".toList,
   .punctuation ";".toList,
   .punctuation "}".toList]

theorem source_lex : lex source.toList = .ok tokens := by
  apply lex_of_completed
  decide +kernel

theorem source_parsed : blockText? ["uint64_t".toList, "uint32_t".toList] source.toList =
    some body := block_text_of_parts _ _ tokens _ source_lex (by rfl)

def services : ScopedServices ObjectBindings.Context :=
  ObjectBindings.services profile (fun _ _ _ => CProg.undefined)
    (fun _ _ _ => CProg.undefined)

def program (frame output : Ptr) (source : UInt64) :
    CProg CVal (ReadBlock.Result ObjectBindings.Context) :=
  executeScopedWith services layout 0 10 (context frame output source) body

def readFirst (frame : Ptr) : CProg CVal UInt64 := do
  let schema ← CProg.loadPtr (frame + 2)
  match schema with
  | none => CProg.undefined
  | some schema => CProg.loadU64 (schema + 3)

def operations (frame output : Ptr) (source : UInt64) :
    CProg CVal (ReadBlock.Result ObjectBindings.Context) := do
  let first ← readFirst frame
  if source < first then
    pure (.finished (.returned (context frame output source) (some (.bool false))))
  else do
    let firstAgain ← readFirst frame
    let offset := source - firstAgain
    let length ← CProg.loadU32 (frame + 8)
    if UInt64.ofNat length.toNat ≤ offset then
      pure (.finished (.returned (context frame output source) (some (.bool false))))
    else do
      let converted ← ReadExpressions.unsignedCast uint32 (.u64 offset)
      CProg.store output converted
      pure (.finished (.returned (context frame output source) (some (.bool true))))


private theorem scalar_read (current : ObjectBindings.Context) (name : String)
    (type : CType) (value : CVal)
    (present : current name.toList = some (.scalar type (some value))) :
    ObjectBindings.read profile layout current (id name) = pure value := by
  simp only [ObjectBindings.read, id, ReadExpressions.expressionWithNames.eq_def,
    ReadExpressions.localOrLocated, ObjectBindings.values, present]

private theorem first_read (current : ObjectBindings.Context) (frame : Ptr)
    (present : current "frame".toList =
      some (.scalar framePointer (some (.ptr (some frame))))) :
    ObjectBindings.read profile layout current firstId =
      (readFirst frame >>= fun value => pure (.u64 value)) := by
  simp only [ObjectBindings.read, firstId, id, ReadExpressions.expressionWithNames.eq_def,
    ReadExpressions.localOrLocated, ObjectBindings.values, present,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  change (ReadExpressions.field layout (.ptr (some frame)) "schema".toList >>= fun owner =>
    ReadExpressions.field layout owner "source_first_id".toList) = _
  rw [ReadExpressions.pointer_field_uses_actual_offset layout frame "schema".toList 2 (by rfl)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  simp only [readFirst, Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext pointer
  cases pointer with
  | none => exact (ReadExpressions.undefined_bind _).symm
  | some pointer => rfl

private theorem length_read (current : ObjectBindings.Context) (frame : Ptr)
    (present : current "frame".toList =
      some (.scalar framePointer (some (.ptr (some frame))))) :
    ObjectBindings.read profile layout current slotLength =
      (CProg.loadU32 (frame + 8) >>= fun value => pure (.u32 value)) := by
  simp only [ObjectBindings.read, slotLength, id,
    ReadExpressions.expressionWithNames.eq_def, ReadExpressions.localOrLocated,
    ObjectBindings.values, present, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

private theorem first_comparison (current : ObjectBindings.Context) (frame : Ptr)
    (source : UInt64)
    (framePresent : current "frame".toList =
      some (.scalar framePointer (some (.ptr (some frame)))))
    (sourcePresent : current "source_id".toList = some (.scalar uint64 (some (.u64 source)))) :
    ObjectBindings.read profile layout current (.binary .lt (id "source_id") firstId) =
      (readFirst frame >>= fun first => pure (.bool (decide (source < first)))) := by
  change (ObjectBindings.read profile layout current (id "source_id") >>= fun source =>
    ObjectBindings.read profile layout current firstId >>= fun first =>
      ReadExpressions.binary .lt source first) = _
  rw [scalar_read current "source_id" uint64 (.u64 source) sourcePresent,
    first_read current frame framePresent]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl

private theorem difference_read (current : ObjectBindings.Context) (frame : Ptr)
    (source : UInt64)
    (framePresent : current "frame".toList =
      some (.scalar framePointer (some (.ptr (some frame)))))
    (sourcePresent : current "source_id".toList = some (.scalar uint64 (some (.u64 source)))) :
    ObjectBindings.read profile layout current (.binary .sub (id "source_id") firstId) =
      (readFirst frame >>= fun first => pure (.u64 (source - first))) := by
  change (ObjectBindings.read profile layout current (id "source_id") >>= fun source =>
    ObjectBindings.read profile layout current firstId >>= fun first =>
      ReadExpressions.binary .sub source first) = _
  rw [scalar_read current "source_id" uint64 (.u64 source) sourcePresent,
    first_read current frame framePresent]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl

private theorem length_comparison (current : ObjectBindings.Context) (frame : Ptr)
    (offset : UInt64)
    (framePresent : current "frame".toList =
      some (.scalar framePointer (some (.ptr (some frame)))))
    (offsetPresent : current "offset".toList = some (.scalar uint64 (some (.u64 offset)))) :
    ObjectBindings.read profile layout current (.binary .ge (id "offset") slotLength) =
      (CProg.loadU32 (frame + 8) >>= fun length =>
        pure (.bool (decide (UInt64.ofNat length.toNat ≤ offset)))) := by
  change (ObjectBindings.read profile layout current (id "offset") >>= fun offset =>
    ObjectBindings.read profile layout current slotLength >>= fun length =>
      ReadExpressions.binary .ge offset length) = _
  rw [scalar_read current "offset" uint64 (.u64 offset) offsetPresent,
    length_read current frame framePresent]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl


private theorem store_offset (current : ObjectBindings.Context) (output : Ptr)
    (offset : UInt64)
    (outputPresent : current "slot_out".toList =
      some (.scalar outputPointer (some (.ptr (some output)))))
    (offsetPresent : current "offset".toList = some (.scalar uint64 (some (.u64 offset)))) :
    ObjectBindings.assignment profile layout current
      (.assign (.unary .dereference (id "slot_out")) (.cast uint32 (id "offset"))) =
      (CProg.store output (.u32 (UInt32.ofNat offset.toNat)) >>= fun _ => pure current) := by
  have outputType : ScalarBytes.typeOf? (ObjectBindings.types current profile.outsideTypes)
      (.unary .dereference (id "slot_out")) profile.fieldTypes = some uint32 := by
    simp only [ScalarBytes.typeOf?, id, ObjectBindings.types]
    rw [outputPresent]
    rfl
  have outputPlace : ObjectBindings.place profile layout current
      (.unary .dereference (id "slot_out")) = pure output := by
    simp only [ObjectBindings.place, ReadExpressions.placeWithNames.eq_def, id,
      ReadExpressions.expressionWithNames.eq_def, ReadExpressions.localOrLocated,
      ObjectBindings.values, outputPresent, ReadExpressions.pointer,
      ReadExpressions.resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  have offsetRead : ObjectBindings.read profile layout current (.cast uint32 (id "offset")) =
      pure (.u32 (UInt32.ofNat offset.toNat)) := by
    change (ObjectBindings.read profile layout current (id "offset") >>=
      ReadExpressions.unsignedCast uint32) = _
    rw [scalar_read current "offset" uint64 (.u64 offset) offsetPresent]
    simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
    exact ReadExpressions.unsignedCast32_of_u64 offset
  simp only [ObjectBindings.assignment, outputType, ReadExpressions.resolved,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  change (ObjectBindings.read profile layout current (.cast uint32 (id "offset")) >>=
    fun value => ObjectBindings.writeValue profile layout current
      (.unary .dereference (id "slot_out")) value) = _
  rw [offsetRead]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, ObjectBindings.writeValue,
    outputType, ReadExpressions.resolved]
  change (ObjectBindings.place profile layout current (.unary .dereference (id "slot_out")) >>=
    fun address => CProg.store address (.u32 (UInt32.ofNat offset.toNat)) >>= fun _ => pure current) = _
  rw [outputPlace]
  rfl

private theorem offset_tail_execution (current : ObjectBindings.Context)
    (frame output : Ptr) (offset : UInt64)
    (framePresent : current "frame".toList =
      some (.scalar framePointer (some (.ptr (some frame)))))
    (outputPresent : current "slot_out".toList =
      some (.scalar outputPointer (some (.ptr (some output)))))
    (offsetPresent : current "offset".toList = some (.scalar uint64 (some (.u64 offset)))) :
    executeScopedWith services layout 0 8 current offsetTail =
      (CProg.loadU32 (frame + 8) >>= fun length =>
        if UInt64.ofNat length.toNat ≤ offset then
          pure (.finished (.returned current (some (.bool false))))
        else CProg.store output (.u32 (UInt32.ofNat offset.toNat)) >>= fun _ =>
          pure (.finished (.returned current (some (.bool true))))) := by
  unfold offsetTail
  rw [executeScopedWith.eq_def]
  change (ObjectBindings.read profile layout current
    (.binary .ge (id "offset") slotLength) >>= fun actual =>
      ReadExpressions.truth actual >>= fun selected =>
        executeScopedWith services layout 0 7 current
          (if selected then [.return (some (.bool false))] else []) >>= fun result =>
            ReadBlock.resume (fun updated => executeScopedWith services layout 0 7 updated
              [.assign (.unary .dereference (id "slot_out")) (.cast uint32 (id "offset")),
               .return (some (.bool true))]) result) = _
  rw [length_comparison current frame offset framePresent offsetPresent]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext length
  by_cases outside : UInt64.ofNat length.toNat ≤ offset
  · simp only [outside, decide_true, ReadExpressions.truth, Prog.pure_eq, Prog.ret_bind,
      ↓reduceIte]
    rfl
  · simp only [outside, decide_false, ReadExpressions.truth, Prog.pure_eq, Prog.ret_bind,
      ↓reduceIte]
    change (ObjectBindings.assignment profile layout current
      (.assign (.unary .dereference (id "slot_out")) (.cast uint32 (id "offset"))) >>=
      fun updated => executeScopedWith services layout 0 6 updated
        [.return (some (.bool true))]) = _
    rw [store_offset current output offset outputPresent offsetPresent]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    rfl

private theorem declared_tail_execution (current : ObjectBindings.Context)
    (frame output : Ptr) (source : UInt64)
    (framePresent : current "frame".toList =
      some (.scalar framePointer (some (.ptr (some frame)))))
    (outputPresent : current "slot_out".toList =
      some (.scalar outputPointer (some (.ptr (some output)))))
    (sourcePresent : current "source_id".toList = some (.scalar uint64 (some (.u64 source)))) :
    executeScopedWith services layout 0 9 current
      (.declare uint64 "offset".toList (.binary .sub (id "source_id") firstId) :: offsetTail) =
      (readFirst frame >>= fun first =>
        CProg.loadU32 (frame + 8) >>= fun length =>
          if UInt64.ofNat length.toNat ≤ source - first then
            pure (.finished (.returned current (some (.bool false))))
          else CProg.store output (.u32 (UInt32.ofNat (source - first).toNat)) >>= fun _ =>
            pure (.finished (.returned current (some (.bool true))))) := by
  rw [scoped_initialized_declaration_keeps_continuation]
  change ObjectBindings.declaration profile (fun _ _ _ => CProg.undefined) layout current
    uint64 "offset".toList (some (.binary .sub (id "source_id") firstId))
    (fun updated => executeScopedWith services layout 0 8 updated offsetTail) = _
  unfold ObjectBindings.declaration
  simp only [show profile.recordExtent uint64 = none from rfl]
  rw [difference_read current frame source framePresent sourcePresent]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext first
  change (executeScopedWith services layout 0 8
    (Function.update current "offset".toList (some (.scalar uint64 (some (.u64 (source - first))))))
    offsetTail >>= fun result => pure (ObjectBindings.restore "offset".toList
      (current "offset".toList) result)) = _
  rw [offset_tail_execution _ frame output (source - first)
    (by exact framePresent) (by exact outputPresent) (by simp only [Function.update_self])]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext length
  by_cases outside : UInt64.ofNat length.toNat ≤ source - first
  · simp only [if_pos outside, Prog.pure_eq, Prog.ret_bind,
      ObjectBindings.returned_local_restores_previous_binding]
  · simp only [if_neg outside, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
      ObjectBindings.returned_local_restores_previous_binding]

/-- Execution follows the parsed branch, including the second physical schema
read, both range checks, unsigned conversion and the single output store. -/
theorem program_uses_current_memory (frame output : Ptr) (source : UInt64) :
    program frame output source = operations frame output source := by
  unfold program body
  rw [executeScopedWith.eq_def]
  change (ObjectBindings.read profile layout (context frame output source)
    (.binary .lt (id "source_id") firstId) >>= fun actual =>
      ReadExpressions.truth actual >>= fun selected =>
        executeScopedWith services layout 0 9 (context frame output source)
          (if selected then [.return (some (.bool false))] else []) >>= fun result =>
            ReadBlock.resume (fun updated => executeScopedWith services layout 0 9 updated
              (.declare uint64 "offset".toList (.binary .sub (id "source_id") firstId) ::
                offsetTail)) result) = _
  rw [first_comparison (context frame output source) frame source (by rfl) (by rfl)]
  unfold operations
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext first
  by_cases below : source < first
  · simp only [below, decide_true, ReadExpressions.truth, Prog.pure_eq, Prog.ret_bind,
      ↓reduceIte]
    rfl
  · simp only [below, decide_false, ReadExpressions.truth, Prog.pure_eq, Prog.ret_bind,
      ↓reduceIte]
    change executeScopedWith services layout 0 9 (context frame output source)
      (.declare uint64 "offset".toList (.binary .sub (id "source_id") firstId) :: offsetTail) = _
    rw [declared_tail_execution _ frame output source (by rfl) (by rfl) (by rfl)]
    simp only [uint32, ReadExpressions.unsignedCast32_of_u64,
      Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

/-- Mathematical interval selection for the contiguous inventory. In
particular a source below its first identifier does not wrap to a slot. -/
def contiguousIndex? (first length source : Nat) : Option Nat :=
  if first ≤ source ∧ source < first + length then some (source - first) else none

theorem contiguous_index_of_member (first length source index : Nat)
    (bound : index < length) (identity : source = first + index) :
    contiguousIndex? first length source = some index := by
  subst source
  have inside : first ≤ first + index ∧ first + index < first + length := by omega
  simp only [contiguousIndex?, if_pos inside]
  congr 1
  omega

theorem contiguous_index_reflects_interval (first length source index : Nat)
    (selected : contiguousIndex? first length source = some index) :
    index < length ∧ source = first + index := by
  unfold contiguousIndex? at selected
  split at selected
  · cases selected
    omega
  · cases selected

theorem contiguous_index_rejects_below (first length source : Nat) (below : source < first) :
    contiguousIndex? first length source = none := by
  simp only [contiguousIndex?]
  have outside : ¬(first ≤ source ∧ source < first + length) := by omega
  rw [if_neg outside]

theorem contiguous_index_rejects_upper (first length source : Nat)
    (above : first + length ≤ source) :
    contiguousIndex? first length source = none := by
  simp only [contiguousIndex?]
  have outside : ¬(first ≤ source ∧ source < first + length) := by omega
  rw [if_neg outside]

/-- The retained inventory names every source identifier, rather than
postulating what the C selector returns. -/
def Contiguous (frame : FrameReadback) (first : Nat) : Prop :=
  ∀ index : Fin frame.slots.length, frame.slots[index.val].sourceId.toNat = first + index.val

theorem contiguous_inventory_selects (frame : FrameReadback) (first : Nat)
    (contiguous : Contiguous frame first) (index : Fin frame.slots.length) :
    contiguousIndex? first frame.view.slotCount frame.slots[index.val].sourceId.toNat =
      some index.val := by
  apply contiguous_index_of_member
  · simpa only [frame.inventory_count] using index.isLt
  · exact contiguous index


universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- The logical offsets describe actual fields and owned output storage.
They do not supply a selector result or a foreign callback. -/
def held (frame schema output : Ptr) (first : UInt64) (length : UInt32)
    (old : CVal) (rest : Heap L → Prop) : Heap L → Prop :=
  PointsTo (frame + 2) (.ptr (some schema)) ∗
    PointsTo (schema + 3) (.u64 first) ∗ PointsTo (frame + 8) (.u32 length) ∗
    PointsTo output old ∗ rest

theorem select_member_owned (frame schema output : Ptr) (first source : UInt64)
    (length : UInt32) (index : Nat) (old : CVal) (rest : Heap L → Prop)
    (identity : source.toNat = first.toNat + index) (bound : index < length.toNat) :
    CTriple (held frame schema output first length old rest)
      (program frame output source)
      (fun result heap => result =
        .finished (.returned (context frame output source) (some (.bool true))) ∧
        held frame schema output first length (.u32 (UInt32.ofNat index)) rest heap) := by
  have lower : first ≤ source := by change first.toNat ≤ source.toNat; omega
  have notBelow : ¬ source < first := by change ¬ source.toNat < first.toNat; omega
  have difference : (source - first).toNat = index := by
    rw [UInt64.toNat_sub_of_le _ _ lower, identity]
    omega
  have wideLength : (UInt64.ofNat length.toNat).toNat = length.toNat := by
    apply UInt64.toNat_ofNat_of_lt
    change length.toNat < 2 ^ 64
    have limit := length.toNat_lt
    omega
  have notBeyond : ¬ UInt64.ofNat length.toNat ≤ source - first := by
    change ¬ (UInt64.ofNat length.toNat).toNat ≤ (source - first).toNat
    rw [wideLength, difference]
    omega
  rw [program_uses_current_memory]
  unfold held
  cmem_start heap owned
  unfold operations readFirst
  simp only [CProg.loadPtr, CProg.loadU64, CProg.loadU32, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen [notBelow, notBeyond, uint32, ReadExpressions.unsignedCast32_of_u64, difference]
  cmem_exact

theorem select_below_owned (frame schema output : Ptr) (first source : UInt64)
    (length : UInt32) (old : CVal) (rest : Heap L → Prop) (below : source < first) :
    CTriple (held frame schema output first length old rest)
      (program frame output source)
      (fun result heap => result =
        .finished (.returned (context frame output source) (some (.bool false))) ∧
        held frame schema output first length old rest heap) := by
  rw [program_uses_current_memory]
  unfold held
  cmem_start heap owned
  unfold operations readFirst
  simp only [CProg.loadPtr, CProg.loadU64, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen [below]
  cmem_exact

theorem select_above_owned (frame schema output : Ptr) (first source : UInt64)
    (length : UInt32) (old : CVal) (rest : Heap L → Prop)
    (lower : first ≤ source) (above : first.toNat + length.toNat ≤ source.toNat) :
    CTriple (held frame schema output first length old rest)
      (program frame output source)
      (fun result heap => result =
        .finished (.returned (context frame output source) (some (.bool false))) ∧
        held frame schema output first length old rest heap) := by
  have notBelow : ¬ source < first := by change ¬ source.toNat < first.toNat; exact Nat.not_lt.mpr lower
  have difference := UInt64.toNat_sub_of_le source first lower
  have wideLength : (UInt64.ofNat length.toNat).toNat = length.toNat := by
    apply UInt64.toNat_ofNat_of_lt
    change length.toNat < 2 ^ 64
    have limit := length.toNat_lt
    omega
  have beyond : UInt64.ofNat length.toNat ≤ source - first := by
    change (UInt64.ofNat length.toNat).toNat ≤ (source - first).toNat
    rw [wideLength, difference]
    change first.toNat ≤ source.toNat at lower
    omega
  rw [program_uses_current_memory]
  unfold held
  cmem_start heap owned
  unfold operations readFirst
  simp only [CProg.loadPtr, CProg.loadU64, CProg.loadU32, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen [notBelow, beyond]
  cmem_exact


/-- Every admitted physical input either stores the unique interval index or
returns false with the old output intact. The result class is not supplied as
a premise, and both rejecting ranges remain observable. -/
theorem contiguous_selector_owned (frame schema output : Ptr) (first source : UInt64)
    (length : UInt32) (old : CVal) (rest : Heap L → Prop) :
    let selected := contiguousIndex? first.toNat length.toNat source.toNat
    CTriple (held frame schema output first length old rest)
      (program frame output source)
      (fun result heap => result =
        .finished (.returned (context frame output source) (some (.bool selected.isSome))) ∧
        held frame schema output first length
          ((selected.map (fun index => CVal.u32 (UInt32.ofNat index))).getD old) rest heap) := by
  dsimp only
  by_cases below : source.toNat < first.toNat
  · rw [contiguous_index_rejects_below _ _ _ below]
    exact select_below_owned frame schema output first source length old rest below
  · by_cases above : first.toNat + length.toNat ≤ source.toNat
    · rw [contiguous_index_rejects_upper _ _ _ above]
      exact select_above_owned frame schema output first source length old rest
        (by change first.toNat ≤ source.toNat; omega) above
    · have identity : source.toNat = first.toNat + (source.toNat - first.toNat) := by omega
      have bound : source.toNat - first.toNat < length.toNat := by omega
      rw [contiguous_index_of_member _ _ _ _ bound identity]
      exact select_member_owned frame schema output first source length _ old rest identity bound

/-- The physical selector stores exactly the coordinate of the corresponding
complete frame inventory. The directory theorem retains the frame generation;
this local block does not claim to execute the directory table lookup. -/
theorem current_coordinate_selected_owned (directory : DirectoryReadback)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length) (physicalFrame schema output : Ptr)
    (first source : UInt64) (length : UInt32) (old : CVal) (rest : Heap L → Prop)
    (contiguous : Contiguous frame first.toNat)
    (count : length.toNat = frame.view.slotCount)
    (sourceIdentity : source.toNat = frame.slots[index.val].sourceId.toNat) :
    CTriple (held physicalFrame schema output first length old rest)
      (program physicalFrame output source)
      (fun result heap =>
        result = .finished (.returned (context physicalFrame output source) (some (.bool true))) ∧
        directory.variableCoordinate? frame.slots[index.val].varId =
          some (frame.view.token.ref index.val) ∧
        held physicalFrame schema output first length
          (.u32 (UInt32.ofNat index.val)) rest heap) := by
  have identity : source.toNat = first.toNat + index.val :=
    sourceIdentity.trans (contiguous index)
  have bound : index.val < length.toNat := by
    rw [count, ← frame.inventory_count]
    exact index.isLt
  intro heap owned
  obtain ⟨safe, post⟩ := select_member_owned physicalFrame schema output first source length
    index.val old rest identity bound heap owned
  refine ⟨safe, ?_⟩
  intro result final ran
  obtain ⟨returned, cells⟩ := post result final ran
  exact ⟨returned, directory.variableCoordinate_slot frame member index, cells⟩


end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector

/-! ## Sorted schema-slot selection from actual C statements

The schema array is embedded, not a stored pointer. The finite interval proof
is connected to the actual parsed loop, declarations and short-circuit guard;
no loop result or probe service is assumed. The physical inventory contract
states initialized ownership, its length and strict source-ID order. It does
not establish the surrounding mode guard, directory lookup or byte ABI.
-/

section SortedSlotWindow
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector

/-- The exact unsigned arithmetic used by the native lower-bound loop. -/
def midpoint (low high : UInt32) : UInt32 := low + (high - low) / 2

theorem midpoint_readout (low high : UInt32) (ordered : low ≤ high) :
    (midpoint low high).toNat = low.toNat + (high.toNat - low.toNat) / 2 := by
  unfold midpoint
  rw [UInt32.toNat_add, UInt32.toNat_div, UInt32.toNat_sub_of_le _ _ ordered]
  change (low.toNat + (high.toNat - low.toNat) / 2) % 2 ^ 32 = _
  apply Nat.mod_eq_of_lt
  have bound := high.toNat_lt
  change low.toNat ≤ high.toNat at ordered
  omega

theorem midpoint_inside (low high : UInt32) (running : low < high) :
    low.toNat ≤ (midpoint low high).toNat ∧ (midpoint low high).toNat < high.toNat := by
  have ordered : low ≤ high := by
    change low.toNat ≤ high.toNat
    change low.toNat < high.toNat at running
    omega
  rw [midpoint_readout _ _ ordered]
  change low.toNat < high.toNat at running
  omega

theorem midpoint_successor_no_wrap (low high : UInt32) (running : low < high) :
    (midpoint low high + 1).toNat = (midpoint low high).toNat + 1 := by
  rw [UInt32.toNat_add]
  change ((midpoint low high).toNat + 1) % 2 ^ 32 = _
  apply Nat.mod_eq_of_lt
  have inside := (midpoint_inside low high running).2
  have bound := high.toNat_lt
  omega

theorem both_windows_decrease (low high : UInt32) (running : low < high) :
    (midpoint low high).toNat - low.toNat < high.toNat - low.toNat ∧
    high.toNat - (midpoint low high + 1).toNat < high.toNat - low.toNat := by
  rw [midpoint_successor_no_wrap _ _ running]
  have inside := midpoint_inside low high running
  change low.toNat < high.toNat at running
  omega

/-- A lower-bound window describes what has been ruled out on each side.
No actual array read or result is postulated by this invariant. -/
structure SearchWindow (values : Nat → Nat) (length key low high : Nat) : Prop where
  ordered : low ≤ high
  within : high ≤ length
  before : ∀ index, index < low → values index < key
  after : ∀ index, high ≤ index → index < length → key ≤ values index

def Increasing (values : Nat → Nat) (length : Nat) : Prop :=
  ∀ first second, first < second → second < length → values first < values second

theorem initial_window (values : Nat → Nat) (length key : Nat) :
    SearchWindow values length key 0 length := by
  constructor
  · omega
  · rfl
  · intro index less; omega
  · intro index lower upper; omega

theorem window_move_low {values : Nat → Nat} {length key low high middle : Nat}
    (sorted : Increasing values length) (window : SearchWindow values length key low high)
    (inside : low ≤ middle ∧ middle < high) (below : values middle < key) :
    SearchWindow values length key (middle + 1) high := by
  constructor
  · omega
  · exact window.within
  · intro index lower
    by_cases previous : index < low
    · exact window.before index previous
    · by_cases same : index = middle
      · simpa only [same] using below
      · exact Nat.lt_trans (sorted index middle (by omega) (by have := window.within; omega)) below
  · exact window.after

theorem window_move_high {values : Nat → Nat} {length key low high middle : Nat}
    (sorted : Increasing values length) (window : SearchWindow values length key low high)
    (inside : low ≤ middle ∧ middle < high) (above : key ≤ values middle) :
    SearchWindow values length key low middle := by
  constructor
  · exact inside.1
  · have := window.within; omega
  · exact window.before
  · intro index lower upper
    by_cases same : index = middle
    · simpa only [same] using above
    · exact Nat.le_trans above (Nat.le_of_lt (sorted middle index (by omega) upper))

/-- Only a closed window supplies the final source comparison. Rejection
excludes every actual inventory position, not merely the last probe. -/
theorem closed_window_find {values : Nat → Nat} {length key position : Nat}
    (sorted : Increasing values length) (window : SearchWindow values length key position position) :
    (position < length ∧ values position = key) ↔ ∃ index, index < length ∧ values index = key := by
  constructor
  · intro found; exact ⟨position, found⟩
  · rintro ⟨index, inRange, found⟩
    by_cases below : index < position
    · have less := window.before index below; omega
    · have low : position ≤ index := by omega
      have atRange : position < length := by omega
      have upper := window.after position (by rfl) atRange
      by_cases same : position = index
      · simpa only [same] using And.intro inRange found
      · have less := sorted position index (by omega) inRange
        omega

theorem closed_window_unique {values : Nat → Nat} {length key position index : Nat}
    (sorted : Increasing values length) (window : SearchWindow values length key position position)
    (inRange : index < length) (found : values index = key) : index = position := by
  by_cases below : index < position
  · have less := window.before index below; omega
  · have low : position ≤ index := by omega
    have atRange : position < length := by omega
    have upper := window.after position (by rfl) atRange
    by_cases same : position = index
    · exact same.symm
    · have less := sorted position index (by omega) inRange
      omega

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector
end SortedSlotWindow

section PettaSortedSource
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedSource
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def id (name : String) : CExpr := .identifier name.toList
def schema : CExpr := .field (id "frame") "schema".toList true
def field (name : String) : CExpr := .field schema name.toList true
def sourceAt (position : CExpr) : CExpr := .index (field "source_ids") position
def uint32 : CType := ⟨"uint32_t".toList, 0⟩
def uint64 : CType := ⟨"uint64_t".toList, 0⟩
def returnFalse : List CStatement := [.return (some (.bool false))]

def iteration : List CStatement :=
  [.declare uint32 "middle".toList
    (.binary .add (id "low") (.binary .div (.binary .sub (id "high") (id "low")) (.unsignedInteger 2))),
   .branch (.binary .lt (sourceAt (id "middle")) (id "source_id"))
     [.assign (id "low") (.binary .add (id "middle") (.unsignedInteger 1))]
     [.assign (id "high") (id "middle")]]

def body : List CStatement :=
  [.declare uint32 "low".toList (.unsignedInteger 0),
   .declare uint32 "high".toList (field "len"),
   .whileLoop (.binary .lt (id "low") (id "high")) iteration,
   .branch (.binary .or (.binary .ge (id "low") (field "len"))
     (.binary .ne (sourceAt (id "low")) (id "source_id"))) returnFalse [],
   .assign (.unary .dereference (id "slot_out")) (id "low"),
   .return (some (.bool true))]

/-- This raw first branch is retained only to admit the entire actual C
function body. The separate contiguous owner proves its physical behavior. -/
def contiguousBody : List CStatement :=
  [.branch (.binary .lt (id "source_id") (field "source_first_id")) returnFalse [],
   .declare uint64 "offset".toList (.binary .sub (id "source_id") (field "source_first_id")),
   .branch (.binary .ge (id "offset") (.field (id "frame") "slot_len".toList true)) returnFalse [],
   .assign (.unary .dereference (id "slot_out")) (.cast uint32 (id "offset")),
   .return (some (.bool true))]

def completeBody : List CStatement :=
  .branch (.binary .or (.binary .or (.unary .not (id "frame")) (.unary .not (id "slot_out")))
    (.binary .eq (id "source_id") (id "VAR_ID_NONE"))) returnFalse [] ::
  .branch (field "source_ids_contiguous") contiguousBody [] :: body

private def sourcePiece0 : String × List Token :=
  ("{\n", [.punctuation ['{']])

private theorem sourcePiece0_lex : sourcePiece0.1.toList.foldl step initial = completed sourcePiece0.2 := by
  decide +kernel

private def sourcePiece1 : String × List Token :=
  ("    if (!frame || !slot_out || source_id == VAR_ID_NONE)\n", [.identifier ['i', 'f'], .punctuation ['('], .punctuation ['!'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['|', '|'], .punctuation ['!'], .identifier ['s', 'l', 'o', 't', '_', 'o', 'u', 't'], .punctuation ['|', '|'], .identifier ['s', 'o', 'u', 'r', 'c', 'e', '_', 'i', 'd'], .punctuation ['=', '='], .identifier ['V', 'A', 'R', '_', 'I', 'D', '_', 'N', 'O', 'N', 'E'], .punctuation [')']])

private theorem sourcePiece1_lex : sourcePiece1.1.toList.foldl step initial = completed sourcePiece1.2 := by
  decide +kernel

private def sourcePiece2 : String × List Token :=
  ("        return false;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['f', 'a', 'l', 's', 'e'], .punctuation [';']])

private theorem sourcePiece2_lex : sourcePiece2.1.toList.foldl step initial = completed sourcePiece2.2 := by
  decide +kernel

private def sourcePiece3 : String × List Token :=
  ("    if (frame->schema->source_ids_contiguous) {\n", [.identifier ['i', 'f'], .punctuation ['('], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['s', 'c', 'h', 'e', 'm', 'a'], .punctuation ['-', '>'], .identifier ['s', 'o', 'u', 'r', 'c', 'e', '_', 'i', 'd', 's', '_', 'c', 'o', 'n', 't', 'i', 'g', 'u', 'o', 'u', 's'], .punctuation [')'], .punctuation ['{']])

private theorem sourcePiece3_lex : sourcePiece3.1.toList.foldl step initial = completed sourcePiece3.2 := by
  decide +kernel

private def sourcePiece4 : String × List Token :=
  ("        if (source_id < frame->schema->source_first_id)\n", [.identifier ['i', 'f'], .punctuation ['('], .identifier ['s', 'o', 'u', 'r', 'c', 'e', '_', 'i', 'd'], .punctuation ['<'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['s', 'c', 'h', 'e', 'm', 'a'], .punctuation ['-', '>'], .identifier ['s', 'o', 'u', 'r', 'c', 'e', '_', 'f', 'i', 'r', 's', 't', '_', 'i', 'd'], .punctuation [')']])

private theorem sourcePiece4_lex : sourcePiece4.1.toList.foldl step initial = completed sourcePiece4.2 := by
  decide +kernel

private def sourcePiece5 : String × List Token :=
  ("            return false;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['f', 'a', 'l', 's', 'e'], .punctuation [';']])

private theorem sourcePiece5_lex : sourcePiece5.1.toList.foldl step initial = completed sourcePiece5.2 := by
  decide +kernel

private def sourcePiece6 : String × List Token :=
  ("        uint64_t offset = source_id - frame->schema->source_first_id;\n", [.identifier ['u', 'i', 'n', 't', '6', '4', '_', 't'], .identifier ['o', 'f', 'f', 's', 'e', 't'], .punctuation ['='], .identifier ['s', 'o', 'u', 'r', 'c', 'e', '_', 'i', 'd'], .punctuation ['-'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['s', 'c', 'h', 'e', 'm', 'a'], .punctuation ['-', '>'], .identifier ['s', 'o', 'u', 'r', 'c', 'e', '_', 'f', 'i', 'r', 's', 't', '_', 'i', 'd'], .punctuation [';']])

private theorem sourcePiece6_lex : sourcePiece6.1.toList.foldl step initial = completed sourcePiece6.2 := by
  decide +kernel

private def sourcePiece7 : String × List Token :=
  ("        if (offset >= frame->slot_len)\n", [.identifier ['i', 'f'], .punctuation ['('], .identifier ['o', 'f', 'f', 's', 'e', 't'], .punctuation ['>', '='], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['s', 'l', 'o', 't', '_', 'l', 'e', 'n'], .punctuation [')']])

private theorem sourcePiece7_lex : sourcePiece7.1.toList.foldl step initial = completed sourcePiece7.2 := by
  decide +kernel

private def sourcePiece8 : String × List Token :=
  ("            return false;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['f', 'a', 'l', 's', 'e'], .punctuation [';']])

private theorem sourcePiece8_lex : sourcePiece8.1.toList.foldl step initial = completed sourcePiece8.2 := by
  decide +kernel

private def sourcePiece9 : String × List Token :=
  ("        *slot_out = (uint32_t)offset;\n", [.punctuation ['*'], .identifier ['s', 'l', 'o', 't', '_', 'o', 'u', 't'], .punctuation ['='], .punctuation ['('], .identifier ['u', 'i', 'n', 't', '3', '2', '_', 't'], .punctuation [')'], .identifier ['o', 'f', 'f', 's', 'e', 't'], .punctuation [';']])

private theorem sourcePiece9_lex : sourcePiece9.1.toList.foldl step initial = completed sourcePiece9.2 := by
  decide +kernel

private def sourcePiece10 : String × List Token :=
  ("        return true;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['t', 'r', 'u', 'e'], .punctuation [';']])

private theorem sourcePiece10_lex : sourcePiece10.1.toList.foldl step initial = completed sourcePiece10.2 := by
  decide +kernel

private def sourcePiece11 : String × List Token :=
  ("    }\n", [.punctuation ['}']])

private theorem sourcePiece11_lex : sourcePiece11.1.toList.foldl step initial = completed sourcePiece11.2 := by
  decide +kernel

private def sourcePiece12 : String × List Token :=
  ("    uint32_t low = 0u;\n", [.identifier ['u', 'i', 'n', 't', '3', '2', '_', 't'], .identifier ['l', 'o', 'w'], .punctuation ['='], .number ['0', 'u'], .punctuation [';']])

private theorem sourcePiece12_lex : sourcePiece12.1.toList.foldl step initial = completed sourcePiece12.2 := by
  decide +kernel

private def sourcePiece13 : String × List Token :=
  ("    uint32_t high = frame->schema->len;\n", [.identifier ['u', 'i', 'n', 't', '3', '2', '_', 't'], .identifier ['h', 'i', 'g', 'h'], .punctuation ['='], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['s', 'c', 'h', 'e', 'm', 'a'], .punctuation ['-', '>'], .identifier ['l', 'e', 'n'], .punctuation [';']])

private theorem sourcePiece13_lex : sourcePiece13.1.toList.foldl step initial = completed sourcePiece13.2 := by
  decide +kernel

private def sourcePiece14 : String × List Token :=
  ("    while (low < high) {\n", [.identifier ['w', 'h', 'i', 'l', 'e'], .punctuation ['('], .identifier ['l', 'o', 'w'], .punctuation ['<'], .identifier ['h', 'i', 'g', 'h'], .punctuation [')'], .punctuation ['{']])

private theorem sourcePiece14_lex : sourcePiece14.1.toList.foldl step initial = completed sourcePiece14.2 := by
  decide +kernel

private def sourcePiece15 : String × List Token :=
  ("        uint32_t middle = low + (high - low) / 2u;\n", [.identifier ['u', 'i', 'n', 't', '3', '2', '_', 't'], .identifier ['m', 'i', 'd', 'd', 'l', 'e'], .punctuation ['='], .identifier ['l', 'o', 'w'], .punctuation ['+'], .punctuation ['('], .identifier ['h', 'i', 'g', 'h'], .punctuation ['-'], .identifier ['l', 'o', 'w'], .punctuation [')'], .punctuation ['/'], .number ['2', 'u'], .punctuation [';']])

private theorem sourcePiece15_lex : sourcePiece15.1.toList.foldl step initial = completed sourcePiece15.2 := by
  decide +kernel

private def sourcePiece16 : String × List Token :=
  ("        if (frame->schema->source_ids[middle] < source_id)\n", [.identifier ['i', 'f'], .punctuation ['('], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['s', 'c', 'h', 'e', 'm', 'a'], .punctuation ['-', '>'], .identifier ['s', 'o', 'u', 'r', 'c', 'e', '_', 'i', 'd', 's'], .punctuation ['['], .identifier ['m', 'i', 'd', 'd', 'l', 'e'], .punctuation [']'], .punctuation ['<'], .identifier ['s', 'o', 'u', 'r', 'c', 'e', '_', 'i', 'd'], .punctuation [')']])

private theorem sourcePiece16_lex : sourcePiece16.1.toList.foldl step initial = completed sourcePiece16.2 := by
  decide +kernel

private def sourcePiece17 : String × List Token :=
  ("            low = middle + 1u;\n", [.identifier ['l', 'o', 'w'], .punctuation ['='], .identifier ['m', 'i', 'd', 'd', 'l', 'e'], .punctuation ['+'], .number ['1', 'u'], .punctuation [';']])

private theorem sourcePiece17_lex : sourcePiece17.1.toList.foldl step initial = completed sourcePiece17.2 := by
  decide +kernel

private def sourcePiece18 : String × List Token :=
  ("        else\n", [.identifier ['e', 'l', 's', 'e']])

private theorem sourcePiece18_lex : sourcePiece18.1.toList.foldl step initial = completed sourcePiece18.2 := by
  decide +kernel

private def sourcePiece19 : String × List Token :=
  ("            high = middle;\n", [.identifier ['h', 'i', 'g', 'h'], .punctuation ['='], .identifier ['m', 'i', 'd', 'd', 'l', 'e'], .punctuation [';']])

private theorem sourcePiece19_lex : sourcePiece19.1.toList.foldl step initial = completed sourcePiece19.2 := by
  decide +kernel

private def sourcePiece20 : String × List Token :=
  ("    }\n", [.punctuation ['}']])

private theorem sourcePiece20_lex : sourcePiece20.1.toList.foldl step initial = completed sourcePiece20.2 := by
  decide +kernel

private def sourcePiece21 : String × List Token :=
  ("    if (low >= frame->schema->len || frame->schema->source_ids[low] != source_id)\n", [.identifier ['i', 'f'], .punctuation ['('], .identifier ['l', 'o', 'w'], .punctuation ['>', '='], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['s', 'c', 'h', 'e', 'm', 'a'], .punctuation ['-', '>'], .identifier ['l', 'e', 'n'], .punctuation ['|', '|'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['s', 'c', 'h', 'e', 'm', 'a'], .punctuation ['-', '>'], .identifier ['s', 'o', 'u', 'r', 'c', 'e', '_', 'i', 'd', 's'], .punctuation ['['], .identifier ['l', 'o', 'w'], .punctuation [']'], .punctuation ['!', '='], .identifier ['s', 'o', 'u', 'r', 'c', 'e', '_', 'i', 'd'], .punctuation [')']])

private theorem sourcePiece21_lex : sourcePiece21.1.toList.foldl step initial = completed sourcePiece21.2 := by
  decide +kernel

private def sourcePiece22 : String × List Token :=
  ("        return false;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['f', 'a', 'l', 's', 'e'], .punctuation [';']])

private theorem sourcePiece22_lex : sourcePiece22.1.toList.foldl step initial = completed sourcePiece22.2 := by
  decide +kernel

private def sourcePiece23 : String × List Token :=
  ("    *slot_out = low;\n", [.punctuation ['*'], .identifier ['s', 'l', 'o', 't', '_', 'o', 'u', 't'], .punctuation ['='], .identifier ['l', 'o', 'w'], .punctuation [';']])

private theorem sourcePiece23_lex : sourcePiece23.1.toList.foldl step initial = completed sourcePiece23.2 := by
  decide +kernel

private def sourcePiece24 : String × List Token :=
  ("    return true;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['t', 'r', 'u', 'e'], .punctuation [';']])

private theorem sourcePiece24_lex : sourcePiece24.1.toList.foldl step initial = completed sourcePiece24.2 := by
  decide +kernel

private def sourcePiece25 : String × List Token :=
  ("}", [.punctuation ['}']])

private theorem sourcePiece25_lex : sourcePiece25.1.toList.foldl step initial = completed sourcePiece25.2 := by
  decide +kernel

private def sourcePieces : List (String × List Token) :=
  [sourcePiece0, sourcePiece1, sourcePiece2, sourcePiece3, sourcePiece4, sourcePiece5, sourcePiece6, sourcePiece7, sourcePiece8, sourcePiece9, sourcePiece10, sourcePiece11, sourcePiece12, sourcePiece13, sourcePiece14, sourcePiece15, sourcePiece16, sourcePiece17, sourcePiece18, sourcePiece19, sourcePiece20, sourcePiece21, sourcePiece22, sourcePiece23, sourcePiece24, sourcePiece25]

def source : String := String.join (sourcePieces.map Prod.fst)
def tokens : List Token := sourcePieces.flatMap Prod.snd

theorem source_lex : lex source.toList = .ok tokens := by
  apply lex_completed_string_pieces
  simp only [sourcePieces, List.forall_cons]
  exact ⟨sourcePiece0_lex, sourcePiece1_lex, sourcePiece2_lex, sourcePiece3_lex, sourcePiece4_lex, sourcePiece5_lex, sourcePiece6_lex, sourcePiece7_lex, sourcePiece8_lex, sourcePiece9_lex, sourcePiece10_lex, sourcePiece11_lex, sourcePiece12_lex, sourcePiece13_lex, sourcePiece14_lex, sourcePiece15_lex, sourcePiece16_lex, sourcePiece17_lex, sourcePiece18_lex, sourcePiece19_lex, sourcePiece20_lex, sourcePiece21_lex, sourcePiece22_lex, sourcePiece23_lex, sourcePiece24_lex, sourcePiece25_lex, trivial⟩

theorem source_parsed : blockText? ["uint32_t".toList, "uint64_t".toList] source.toList =
    some completeBody := block_text_of_parts _ _ tokens _ source_lex (by rfl)

/-- Both initial guards remain explicit. Only after their own source rules
choose the fallback does this suffix become the active control. -/
theorem sorted_suffix_is_actual_source : completeBody.drop 2 = body := rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedSource
end PettaSortedSource

section PettaSortedProbe
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedProbe
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def layout : Layout := fun name =>
  if name = "schema".toList then some ⟨2, .pointer⟩
  else if name = "len".toList then some ⟨1, .word⟩
  else if name = "source_ids".toList then some ⟨7, .embedded⟩ else none

/-- The selected C operand's declared flexible array has unsigned 64-bit
elements. The metadata admits address decay, never a pointer stored inside
the first element. Its native byte layout remains a separate obligation. -/
def objects : ObjectReads where
  arrayField := fun owner through name => match owner with
    | .field (.identifier frame) schema true =>
        frame == "frame".toList && schema == "schema".toList && through &&
          name == "source_ids".toList
    | _ => false
  indexKind := some (fun array => match array with
    | .field (.field (.identifier frame) schema true) member true =>
        if frame == "frame".toList && schema == "schema".toList && member == "source_ids".toList
          then some .word64 else none
    | _ => none)

theorem schema_is_read_from_frame (names : NameReads) (frame : Ptr)
    (frameLocal : names "frame".toList = pure (.ptr (some frame))) :
    expressionWithNames names noCalls layout SortedSource.schema objects =
      (CProg.loadPtr (frame + 2) >>= fun value => pure (.ptr value)) := by
  change (names "frame".toList >>= fun value =>
    ReadExpressions.field layout value "schema".toList) = _
  rw [frameLocal]
  rfl

theorem flexible_array_is_member_address (names : NameReads) (frame : Ptr)
    (frameLocal : names "frame".toList = pure (.ptr (some frame))) :
    expressionWithNames names noCalls layout (SortedSource.field "source_ids") objects =
      (CProg.loadPtr (frame + 2) >>= fun selected => match selected with
        | none => CProg.undefined
        | some schema => pure (.ptr (some (schema + 7)))) := by
  unfold SortedSource.field
  rw [array_member_retains_owner_expression _ _ _ _ _ _ (by decide),
    schema_is_read_from_frame names frame frameLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext selected
  cases selected with
  | none => exact array_field_null_owner_is_undefined _ _ _ (by rfl)
  | some schema => exact array_field_address_uses_member_place _ _ _ _ (by rfl)

/-- Exact source-probe execution: one actual frame read followed by the
current initialized array cell, with the original unsigned index retained.
Null schema refusal is not a successful comparison result. -/
theorem actual_index_probe (names : NameReads) (frame : Ptr) (name : Name) (index : UInt32)
    (frameLocal : names "frame".toList = pure (.ptr (some frame)))
    (indexLocal : names name = pure (.u32 index)) :
    expressionWithNames names noCalls layout
      (SortedSource.sourceAt (.identifier name)) objects =
      (CProg.loadPtr (frame + 2) >>= fun selected => match selected with
        | none => CProg.undefined
        | some schema => CProg.loadU64 ((schema + 7) + index.toNat) >>=
            fun value => pure (.u64 value)) := by
  unfold SortedSource.sourceAt
  rw [described_index_keeps_operands _ _ _ _ _ _ _ .word64 rfl (by rfl),
    flexible_array_is_member_address names frame frameLocal]
  change ((CProg.loadPtr (frame + 2) >>= fun selected => match selected with
    | none => CProg.undefined
    | some schema => pure (.ptr (some (schema + 7)))) >>= fun array =>
      names name >>= fun actual => indexedScalar .word64 array actual) = _
  rw [indexLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext selected
  cases selected with
  | none => exact undefined_bind _
  | some schema => rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedProbe
end PettaSortedProbe

section PettaSortedPhysical
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedPhysical
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

abbrev Window := UInt32 × UInt32

/-- Each probe rereads the frame's schema reference. The flexible array is
embedded at its declared member address; there is no pointer load at that
address. -/
def readAt (frame : Ptr) (index : UInt32) : CProg CVal UInt64 := do
  let schema ← CProg.loadPtr (frame + 2)
  match schema with
  | none => CProg.undefined
  | some schema => CProg.loadU64 ((schema + 7) + index.toNat)

def test (window : Window) : CProg CVal Bool := pure (decide (window.1 < window.2))

def iteration (frame : Ptr) (key : UInt64) (window : Window) :
    CProg CVal (ReadBlock.Result Window) := do
  let middle := midpoint window.1 window.2
  let actual ← readAt frame middle
  if actual < key then pure (.finished (.next (middle + 1, window.2)))
  else pure (.finished (.next (window.1, middle)))

def search (frame : Ptr) (key : UInt64) (fuel : Nat) (window : Window) :
    CProg CVal (ReadBlock.Result Window) :=
  ReadBlock.whileWith test (iteration frame key) fuel window

def readLength (frame : Ptr) : CProg CVal UInt32 := do
  let schema ← CProg.loadPtr (frame + 2)
  match schema with
  | none => CProg.undefined
  | some schema => CProg.loadU32 (schema + 1)

/-- The final source guard rereads the length before deciding whether an
array access is permitted. A failed lookup leaves the output untouched. -/
def finish (frame output : Ptr) (key : UInt64) (position : UInt32) : CProg CVal Bool := do
  let length ← readLength frame
  if length ≤ position then pure false
  else do
    let actual ← readAt frame position
    if actual ≠ key then pure false
    else do
      CProg.store output (.u32 position)
      pure true

def valueAt (sources : List UInt64) (index : Nat) : Nat :=
  (sources[index]?.getD 0).toNat

theorem valueAt_of_inRange (sources : List UInt64) (index : Nat)
    (inRange : index < sources.length) : valueAt sources index = sources[index].toNat := by
  simp only [valueAt, List.getElem?_eq_getElem inRange, Option.getD_some]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def held (frame schema : Ptr) (length : UInt32) (sources : List UInt64)
    (rest : Heap L → Prop) : Heap L → Prop :=
  PointsTo (frame + 2) (.ptr (some schema)) ∗
    PointsTo (schema + 1) (.u32 length) ∗
      Cells (schema + 7) ((sources.map CVal.u64).map some) ∗ rest

/-- The static inventory supplies initialized cells, not probe results. -/
theorem read_at_owned (frame schema : Ptr) (length index : UInt32)
    (sources : List UInt64) (rest : Heap L → Prop)
    (inRange : index.toNat < sources.length) :
    CTriple (held frame schema length sources rest) (readAt frame index)
      (fun value heap => value = sources[index.toNat] ∧
        held frame schema length sources rest heap) := by
  have pointerRead : Ensures (held frame schema length sources rest)
      (Reads (frame + 2) (.ptr (some schema))) :=
    Ensures.left (reads_persistent _ _) (ensures_reads_pointsTo _ _)
  have elementRead : Ensures (held frame schema length sources rest)
      (Reads ((schema + 7) + index.toNat) (.u64 sources[index.toNat])) := by
    unfold held
    apply Ensures.right (reads_persistent _ _)
    apply Ensures.right (reads_persistent _ _)
    apply Ensures.left (reads_persistent _ _)
    have owned := ensures_reads_cells (L := L) (schema + 7) (sources.map CVal.u64)
      index.toNat (by simpa only [List.length_map] using inRange)
    simpa only [List.getElem_map] using owned
  unfold readAt
  refine triple_bind _ (loadPtr_rule (fun heap owned => pointerRead.apply owned)) ?_
  intro pointer
  apply triple_pure
  rintro rfl
  exact loadU64_rule (fun heap owned => elementRead.apply owned)

theorem read_length_owned (frame schema : Ptr) (length : UInt32)
    (sources : List UInt64) (rest : Heap L → Prop) :
    CTriple (held frame schema length sources rest) (readLength frame)
      (fun value heap => value = length ∧ held frame schema length sources rest heap) := by
  have pointerRead : Ensures (held frame schema length sources rest)
      (Reads (frame + 2) (.ptr (some schema))) :=
    Ensures.left (reads_persistent _ _) (ensures_reads_pointsTo _ _)
  have lengthRead : Ensures (held frame schema length sources rest)
      (Reads (schema + 1) (.u32 length)) :=
    Ensures.right (reads_persistent _ _)
      (Ensures.left (reads_persistent _ _) (ensures_reads_pointsTo _ _))
  unfold readLength
  refine triple_bind _ (loadPtr_rule (fun heap owned => pointerRead.apply owned)) ?_
  intro pointer
  apply triple_pure
  rintro rfl
  exact loadU32_rule (fun heap owned => lengthRead.apply owned)

def invariant (frame schema : Ptr) (length : UInt32) (sources : List UInt64)
    (key : UInt64) (rest : Heap L → Prop) (window : Window) (heap : Heap L) : Prop :=
  SearchWindow (valueAt sources) length.toNat key.toNat window.1.toNat window.2.toNat ∧
    held frame schema length sources rest heap

/-- One physical iteration preserves the independent lower-bound window and
strictly lowers its width. Neither the next interval nor its selected value
is a primitive-service assumption. -/
theorem iteration_narrows (frame schema : Ptr) (length : UInt32) (sources : List UInt64)
    (key : UInt64) (rest : Heap L → Prop)
    (count : sources.length = length.toNat)
    (sorted : Increasing (valueAt sources) length.toNat) (window : Window) :
    CTriple
      (fun heap => invariant frame schema length sources key rest window heap ∧
        0 < window.2.toNat - window.1.toNat)
      (iteration frame key window)
      (fun result heap => ∃ updated,
        result = .finished (.next updated) ∧
          invariant frame schema length sources key rest updated heap ∧
            updated.2.toNat - updated.1.toNat < window.2.toNat - window.1.toNat) := by
  intro heap guarded
  obtain ⟨⟨windowInvariant, owned⟩, positive⟩ := guarded
  have running : window.1 < window.2 := by
    change window.1.toNat < window.2.toNat
    omega
  have middleInside := midpoint_inside window.1 window.2 running
  have middleRange : (midpoint window.1 window.2).toNat < sources.length := by
    have upper := windowInvariant.within
    omega
  change (iteration frame key window).wp act
    (fun result heap => ∃ updated, result = .finished (.next updated) ∧
      invariant frame schema length sources key rest updated heap ∧
      updated.2.toNat - updated.1.toNat < window.2.toNat - window.1.toNat) heap
  unfold iteration
  rw [wp_bind']
  refine wp_consequence act
    (read_at_owned frame schema length (midpoint window.1 window.2) sources rest middleRange)
    owned ?_
  rintro actual reached ⟨rfl, retained⟩
  by_cases below : sources[(midpoint window.1 window.2).toNat] < key
  · rw [if_pos below, wp_pure]
    refine ⟨(midpoint window.1 window.2 + 1, window.2), rfl, ?_,
      (both_windows_decrease window.1 window.2 running).2⟩
    refine ⟨?_, retained⟩
    dsimp only
    rw [midpoint_successor_no_wrap _ _ running]
    apply window_move_low sorted windowInvariant middleInside
    rw [valueAt_of_inRange sources _ middleRange]
    exact below
  · rw [if_neg below, wp_pure]
    refine ⟨(window.1, midpoint window.1 window.2), rfl, ?_,
      (both_windows_decrease window.1 window.2 running).1⟩
    refine ⟨window_move_high sorted windowInvariant middleInside ?_, retained⟩
    rw [valueAt_of_inRange sources _ middleRange]
    change ¬ sources[(midpoint window.1 window.2).toNat].toNat < key.toNat at below
    omega

/-- Sufficient allowance is derived from the current interval width. The
native binary-search arithmetic cannot wrap, and every successful probe lies
inside the owned initialized source inventory. -/
theorem search_closes_window (frame schema : Ptr) (length : UInt32) (sources : List UInt64)
    (key : UInt64) (rest : Heap L → Prop)
    (count : sources.length = length.toNat)
    (sorted : Increasing (valueAt sources) length.toNat)
    (fuel : Nat) (window : Window)
    (enough : window.2.toNat - window.1.toNat ≤ fuel) :
    CTriple (invariant frame schema length sources key rest window)
      (search frame key fuel window)
      (fun result heap => ∃ updated,
        result = .finished (.next updated) ∧
          updated.1 = updated.2 ∧
          invariant frame schema length sources key rest updated heap) := by
  unfold search
  apply ReadBlock.while_normal_body_rank test (iteration frame key)
    (fun reached => reached.2.toNat - reached.1.toNat)
    (invariant frame schema length sources key rest)
    (fun reached heap => reached.1 = reached.2 ∧
      invariant frame schema length sources key rest reached heap)
    ?_ (iteration_narrows frame schema length sources key rest count sorted) fuel window enough
  intro reached heap owns
  change (test reached).wp act
    (fun selected heap => invariant frame schema length sources key rest reached heap ∧
      (selected = true → 0 < reached.2.toNat - reached.1.toNat) ∧
      (selected = false → reached.1 = reached.2 ∧
        invariant frame schema length sources key rest reached heap)) heap
  simp only [test, wp_pure]
  refine ⟨owns, ?_, ?_⟩
  · intro running
    have smaller : reached.1 < reached.2 := of_decide_eq_true running
    change reached.1.toNat < reached.2.toNat at smaller
    omega
  · intro stopped
    have notRunning : ¬ reached.1 < reached.2 := of_decide_eq_false stopped
    change ¬ reached.1.toNat < reached.2.toNat at notRunning
    have ordered := owns.1.ordered
    refine ⟨UInt32.toNat_inj.mp (by omega), owns⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedPhysical
end PettaSortedPhysical

section PettaSortedControls
set_option autoImplicit false
set_option maxRecDepth 12000

end PettaSortedControls

section PettaSortedFinish
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedPhysical
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

private theorem output_store_owned (frame schema output : Ptr) (length : UInt32)
    (sources : List UInt64) (old value : CVal) (rest : Heap L → Prop) :
    CTriple (held frame schema length sources (PointsTo output old ∗ rest))
      (CProg.store output value)
      (fun _ => held frame schema length sources (PointsTo output value ∗ rest)) := by
  unfold held
  cmem_start heap owned
  cmem_vcgen
  cmem_exact

/-- The actual final guard rereads the schema length and short-circuits an
out-of-range index. It reads the candidate cell only in range, and writes the
output only when that cell equals the requested identifier. -/
theorem finish_owned (frame schema output : Ptr) (length position : UInt32)
    (sources : List UInt64) (key : UInt64) (old : CVal) (rest : Heap L → Prop)
    (count : sources.length = length.toNat) :
    CTriple (held frame schema length sources (PointsTo output old ∗ rest))
      (finish frame output key position)
      (fun answer heap =>
        (answer = true ↔ position.toNat < length.toNat ∧
          valueAt sources position.toNat = key.toNat) ∧
        held frame schema length sources
          (PointsTo output (if answer then .u32 position else old) ∗ rest) heap) := by
  unfold finish
  refine triple_bind _ (read_length_owned frame schema length sources _) ?_
  intro actual
  apply triple_pure
  intro same
  subst actual
  by_cases outside : length ≤ position
  · rw [if_pos outside]
    intro heap owned
    change (pure false : CProg CVal Bool).wp act _ heap
    rw [wp_pure]
    refine ⟨?_, owned⟩
    change length.toNat ≤ position.toNat at outside
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro smaller
    omega
  · rw [if_neg outside]
    have inside : position.toNat < sources.length := by
      change ¬length.toNat ≤ position.toNat at outside
      omega
    refine triple_bind _ (read_at_owned frame schema length position sources _ inside) ?_
    intro actual
    apply triple_pure
    intro sameValue
    subst actual
    by_cases different : sources[position.toNat] ≠ key
    · rw [if_pos different]
      intro heap owned
      change (pure false : CProg CVal Bool).wp act _ heap
      rw [wp_pure]
      refine ⟨?_, owned⟩
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro smaller equal
      rw [valueAt_of_inRange sources _ inside] at equal
      exact different (UInt64.toNat_inj.mp equal)
    · rw [if_neg different]
      have same : sources[position.toNat] = key := not_not.mp different
      refine triple_bind _ (output_store_owned frame schema output length sources old
        (.u32 position) rest) ?_
      intro ignored
      cases ignored
      intro heap owned
      change (pure true : CProg CVal Bool).wp act _ heap
      rw [wp_pure]
      refine ⟨?_, owned⟩
      simp only [iff_true_left]
      refine ⟨by omega, ?_⟩
      rw [valueAt_of_inRange sources _ inside, same]

/-- On a closed lower-bound window, completed refusal excludes every source
identifier. Success returns its unique physical coordinate. -/
theorem finish_closed_window_owned (frame schema output : Ptr) (length position : UInt32)
    (sources : List UInt64) (key : UInt64) (old : CVal) (rest : Heap L → Prop)
    (count : sources.length = length.toNat)
    (sorted : Increasing (valueAt sources) length.toNat)
    (window : SearchWindow (valueAt sources) length.toNat key.toNat
      position.toNat position.toNat) :
    CTriple (held frame schema length sources (PointsTo output old ∗ rest))
      (finish frame output key position)
      (fun answer heap =>
        (answer = true ↔ ∃ index, index < sources.length ∧
          valueAt sources index = key.toNat) ∧
        (∀ index, index < sources.length → valueAt sources index = key.toNat →
          index = position.toNat) ∧
        held frame schema length sources
          (PointsTo output (if answer then .u32 position else old) ∗ rest) heap) := by
  intro heap owned
  obtain ⟨safe, post⟩ := finish_owned frame schema output length position sources key old rest
    count heap owned
  refine ⟨safe, ?_⟩
  intro answer reached ran
  obtain ⟨observed, retained⟩ := post answer reached ran
  refine ⟨?_, ?_, retained⟩
  · rw [observed, count]
    exact closed_window_find sorted window
  · intro index inside found
    exact closed_window_unique sorted window (by simpa only [count] using inside) found

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedPhysical
end PettaSortedFinish

section PettaSortedStatements
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

abbrev Context := ObjectBindings.Context

def profile : ObjectBindings.Profile where
  values := noCalls
  locations := fun _ => none
  outsideTypes := fun _ => none
  outsidePlaces := fun _ => none
  fieldTypes := fun _ _ => none
  cellExtent := fun _ => none
  byteExtent := fun _ => none
  sizeWidth := .bits64

def names (context : Context) : NameReads :=
  localOrLocated (ObjectBindings.values context) (ObjectBindings.declared context) profile.locations

def read (layout : Layout) (context : Context) (operand : CExpr) : CProg CVal CVal :=
  expressionWithNames (names context) noCalls layout operand SortedProbe.objects

def services : ScopedServices Context :=
  { ObjectBindings.services profile (fun _ _ _ => CProg.undefined)
      (fun _ _ _ => CProg.undefined) with read := read, physicalWhile := true }

def scalar (type : CType) (value : CVal) : Option ObjectBindings.Binding :=
  some (.scalar type (some value))

def windowContext (outer : Context) (window : SortedPhysical.Window) : Context :=
  Function.update (Function.update outer "low".toList (scalar SortedSource.uint32 (.u32 window.1)))
    "high".toList (scalar SortedSource.uint32 (.u32 window.2))

def middleContext (outer : Context) (window : SortedPhysical.Window) : Context :=
  Function.update (windowContext outer window) "middle".toList
    (scalar SortedSource.uint32 (.u32 (midpoint window.1 window.2)))

theorem names_of_scalar (context : Context) (name : Name) (type : CType) (value : CVal)
    (known : context name = scalar type value) : names context name = pure value := by
  simp only [names, localOrLocated, ObjectBindings.values,
    known, scalar]

theorem read_of_scalar (context : Context) (name : Name) (type : CType) (value : CVal)
    (known : context name = scalar type value) :
    read SortedProbe.layout context (.identifier name) = pure value :=
  names_of_scalar context name type value known

theorem actual_loop_guard (outer : Context) (window : SortedPhysical.Window) :
    (services.read SortedProbe.layout (windowContext outer window)
      (.binary .lt (SortedSource.id "low") (SortedSource.id "high")) >>= truth) =
        SortedPhysical.test window := by
  change ((read SortedProbe.layout (windowContext outer window) (SortedSource.id "low") >>= fun low =>
    read SortedProbe.layout (windowContext outer window) (SortedSource.id "high") >>= fun high =>
      binary .lt low high) >>= truth) = _
  unfold SortedSource.id
  rw [read_of_scalar _ _ SortedSource.uint32 (.u32 window.1) (by simp [windowContext]),
    read_of_scalar _ _ SortedSource.uint32 (.u32 window.2) (by simp [windowContext])]
  rfl

theorem actual_midpoint_initializer (outer : Context) (window : SortedPhysical.Window) :
    ObjectBindings.read profile SortedProbe.layout (windowContext outer window)
      (.binary .add (SortedSource.id "low")
        (.binary .div (.binary .sub (SortedSource.id "high") (SortedSource.id "low"))
          (.unsignedInteger 2))) = pure (.u32 (midpoint window.1 window.2)) := by
  rfl

theorem actual_midpoint_probe (outer : Context) (window : SortedPhysical.Window)
    (frame : Ptr) (frameType : CType)
    (frameLocal : outer "frame".toList = scalar frameType (.ptr (some frame))) :
    read SortedProbe.layout (middleContext outer window)
      (SortedSource.sourceAt (SortedSource.id "middle")) =
      (SortedPhysical.readAt frame (midpoint window.1 window.2) >>= fun value => pure (.u64 value)) := by
  unfold read SortedSource.id
  rw [SortedProbe.actual_index_probe _ frame "middle".toList (midpoint window.1 window.2)
    (names_of_scalar _ _ frameType _ (by simpa [middleContext, windowContext] using frameLocal))
    (names_of_scalar _ _ SortedSource.uint32 _ (by simp [middleContext]))]
  unfold SortedPhysical.readAt
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext selected
  cases selected
  · exact (undefined_bind _).symm
  · rfl

theorem scalar_assignment_retains_other_locals (context : Context) (name : Name)
    (previous : CVal) (value : UInt32) (operand : CExpr)
    (known : context name = scalar SortedSource.uint32 previous)
    (rhs : ObjectBindings.read profile SortedProbe.layout context operand = pure (.u32 value)) :
    services.assignment SortedProbe.layout context (.assign (.identifier name) operand) =
      pure (Function.update context name (scalar SortedSource.uint32 (.u32 value))) := by
  change ObjectBindings.assignment profile SortedProbe.layout context
    (.assign (.identifier name) operand) = _
  unfold ObjectBindings.assignment
  dsimp only
  have typed : ScalarBytes.typeOf? (ObjectBindings.types context profile.outsideTypes)
      (.identifier name) profile.fieldTypes = some SortedSource.uint32 := by
    simp only [ScalarBytes.typeOf?, ObjectBindings.types, known, scalar]
  rw [typed]
  change (ObjectBindings.read profile SortedProbe.layout context operand >>= fun actual =>
    ObjectBindings.writeValue profile SortedProbe.layout context (.identifier name) actual) = _
  rw [rhs]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rw [ObjectBindings.local_scalar_write_refines_existing_inventory profile SortedProbe.layout
    context name SortedSource.uint32 (some previous) (.u32 value) known]
  rfl

theorem restore_middle_after_low (outer : Context) (window : SortedPhysical.Window)
    (value : UInt32) :
    Function.update
      (Function.update (middleContext outer window) "low".toList
        (scalar SortedSource.uint32 (.u32 value))) "middle".toList
      (windowContext outer window "middle".toList) = windowContext outer (value, window.2) := by
  funext name
  simp only [middleContext, windowContext, Function.update_apply]
  split_ifs <;> simp_all

theorem restore_middle_after_high (outer : Context) (window : SortedPhysical.Window)
    (value : UInt32) :
    Function.update
      (Function.update (middleContext outer window) "high".toList
        (scalar SortedSource.uint32 (.u32 value))) "middle".toList
      (windowContext outer window "middle".toList) = windowContext outer (window.1, value) := by
  funext name
  simp only [middleContext, windowContext, Function.update_apply]
  split_ifs <;> simp_all

theorem actual_midpoint_comparison (outer : Context) (window : SortedPhysical.Window)
    (frame : Ptr) (key : UInt64) (frameType : CType)
    (frameLocal : outer "frame".toList = scalar frameType (.ptr (some frame)))
    (keyLocal : outer "source_id".toList = scalar SortedSource.uint64 (.u64 key)) :
    (services.read SortedProbe.layout (middleContext outer window)
      (.binary .lt (SortedSource.sourceAt (SortedSource.id "middle"))
        (SortedSource.id "source_id")) >>= truth) =
      (SortedPhysical.readAt frame (midpoint window.1 window.2) >>= fun actual =>
        pure (decide (actual < key))) := by
  change ((read SortedProbe.layout (middleContext outer window)
    (SortedSource.sourceAt (SortedSource.id "middle")) >>= fun actual =>
    read SortedProbe.layout (middleContext outer window) (SortedSource.id "source_id") >>=
      fun requested => binary .lt actual requested) >>= truth) = _
  rw [actual_midpoint_probe outer window frame frameType frameLocal]
  unfold SortedSource.id
  rw [read_of_scalar _ _ SortedSource.uint64 (.u64 key)
    (by simpa [middleContext, windowContext] using keyLocal)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

theorem actual_selected_assignment (outer : Context) (window : SortedPhysical.Window)
    (allowance : Nat) (selected : Bool) :
    executeScopedWith services SortedProbe.layout allowance 6 (middleContext outer window)
      (if selected then [.assign (SortedSource.id "low")
        (.binary .add (SortedSource.id "middle") (.unsignedInteger 1))]
       else [.assign (SortedSource.id "high") (SortedSource.id "middle")]) =
      pure (.finished (.next (if selected then
        Function.update (middleContext outer window) "low".toList
          (scalar SortedSource.uint32 (.u32 (midpoint window.1 window.2 + 1)))
        else Function.update (middleContext outer window) "high".toList
          (scalar SortedSource.uint32 (.u32 (midpoint window.1 window.2)))))) := by
  cases selected with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show 6 = 5 + 1 from rfl, scoped_assignment_keeps_continuation]
      unfold SortedSource.id
      rw [scalar_assignment_retains_other_locals _ _ (.u32 window.2) _ _
        (by simp [middleContext, windowContext]) (by rfl)]
      rfl
  | true =>
      simp only [↓reduceIte]
      rw [show 6 = 5 + 1 from rfl, scoped_assignment_keeps_continuation]
      unfold SortedSource.id
      rw [scalar_assignment_retains_other_locals _ _ (.u32 window.1) _ _
        (by simp [middleContext, windowContext]) (by rfl)]
      rfl

theorem actual_branch_control (allowance fuel : Nat) (context : Context)
    (condition : CExpr) (yes no rest : List CStatement) :
    executeScopedWith services SortedProbe.layout allowance (fuel + 1) context
      (.branch condition yes no :: rest) =
      ((services.read SortedProbe.layout context condition >>= truth) >>= fun selected =>
        executeScopedWith services SortedProbe.layout allowance fuel context
          (if selected then yes else no) >>= ReadBlock.resume
            (fun updated => executeScopedWith services SortedProbe.layout allowance fuel updated rest)) := by
  rw [executeScopedWith.eq_def]
  simp only [Prog.bind_eq, Prog.bind_assoc]

theorem actual_iteration_restores_middle (outer : Context) (window : SortedPhysical.Window)
    (frame : Ptr) (key : UInt64) (frameType : CType) (allowance : Nat)
    (frameLocal : outer "frame".toList = scalar frameType (.ptr (some frame)))
    (keyLocal : outer "source_id".toList = scalar SortedSource.uint64 (.u64 key)) :
    executeScopedWith services SortedProbe.layout allowance 8
      (windowContext outer window) SortedSource.iteration =
      (SortedPhysical.iteration frame key window >>= fun result =>
        pure (result.mapContext (windowContext outer))) := by
  unfold SortedSource.iteration
  rw [show 8 = 7 + 1 from rfl, scoped_initialized_declaration_keeps_continuation]
  have declarationProvider : services.declaration =
      ObjectBindings.declaration profile (fun _ _ _ => CProg.undefined) := rfl
  rw [declarationProvider]
  rw [ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow _ _ _ _ _ _ _ (by rfl)]
  rw [actual_midpoint_initializer]
  change ((executeScopedWith services SortedProbe.layout allowance 7
    (middleContext outer window)
      [.branch (.binary .lt (SortedSource.sourceAt (SortedSource.id "middle"))
        (SortedSource.id "source_id"))
        [.assign (SortedSource.id "low") (.binary .add (SortedSource.id "middle") (.unsignedInteger 1))]
        [.assign (SortedSource.id "high") (SortedSource.id "middle")]]) >>= fun result =>
          pure (ObjectBindings.restore "middle".toList
            (windowContext outer window "middle".toList) result)) = _
  rw [show 7 = 6 + 1 from rfl, actual_branch_control]
  change (((services.read SortedProbe.layout (middleContext outer window)
    (.binary .lt (SortedSource.sourceAt (SortedSource.id "middle"))
      (SortedSource.id "source_id")) >>= truth) >>= fun selected =>
    executeScopedWith services SortedProbe.layout allowance 6 (middleContext outer window)
      (if selected then [.assign (SortedSource.id "low")
        (.binary .add (SortedSource.id "middle") (.unsignedInteger 1))]
       else [.assign (SortedSource.id "high") (SortedSource.id "middle")]) >>=
      fun result => ReadBlock.resume (fun updated => pure (.finished (.next updated))) result) >>=
        fun result => pure (ObjectBindings.restore "middle".toList
          (windowContext outer window "middle".toList) result)) = _
  rw [actual_midpoint_comparison outer window frame key frameType frameLocal keyLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    actual_selected_assignment, SortedPhysical.iteration]
  congr 1
  funext actual
  by_cases smaller : actual < key
  · simp only [smaller, decide_true, ↓reduceIte, ReadBlock.resume, Prog.ret_bind,
      ObjectBindings.restore, ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext,
      restore_middle_after_low]
  · simp only [smaller, decide_false, Bool.false_eq_true, ↓reduceIte, ReadBlock.resume, Prog.ret_bind,
      ObjectBindings.restore, ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext,
      restore_middle_after_high]

/-- The parsed loop's body restores its private midpoint binding at every
iteration while retaining both search bounds and every older local. -/
theorem actual_loop_uses_owned_search (outer : Context) (window : SortedPhysical.Window)
    (frame : Ptr) (key : UInt64) (frameType : CType) (allowance : Nat)
    (frameLocal : outer "frame".toList = scalar frameType (.ptr (some frame)))
    (keyLocal : outer "source_id".toList = scalar SortedSource.uint64 (.u64 key)) :
    ReadBlock.whileWith
      (fun current => services.read SortedProbe.layout current
        (.binary .lt (SortedSource.id "low") (SortedSource.id "high")) >>= truth)
      (fun current => executeScopedWith services SortedProbe.layout allowance 8 current
        SortedSource.iteration) allowance (windowContext outer window) =
      (SortedPhysical.search frame key allowance window >>= fun result =>
        pure (result.mapContext (windowContext outer))) :=
  ReadBlock.while_context_extension (windowContext outer) SortedPhysical.test
    (SortedPhysical.iteration frame key) _ _ (actual_loop_guard outer)
    (fun reached => actual_iteration_restores_middle outer reached frame key frameType allowance
      frameLocal keyLocal) allowance window

theorem actual_length_read (context : Context) (frame : Ptr) (frameType : CType)
    (frameLocal : context "frame".toList = scalar frameType (.ptr (some frame))) :
    read SortedProbe.layout context (SortedSource.field "len") =
      (SortedPhysical.readLength frame >>= fun value => pure (.u32 value)) := by
  change (expressionWithNames (names context) noCalls SortedProbe.layout SortedSource.schema
    SortedProbe.objects >>= fun owner => field SortedProbe.layout owner "len".toList) = _
  rw [SortedProbe.schema_is_read_from_frame _ frame
    (names_of_scalar context _ frameType _ frameLocal)]
  unfold SortedPhysical.readLength
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext selected
  cases selected with
  | none => exact (undefined_bind _).symm
  | some address => rfl

theorem actual_length_initializer (context : Context) (frame : Ptr) (frameType : CType)
    (frameLocal : context "frame".toList = scalar frameType (.ptr (some frame))) :
    ObjectBindings.read profile SortedProbe.layout context (SortedSource.field "len") =
      (SortedPhysical.readLength frame >>= fun value => pure (.u32 value)) := by
  change read SortedProbe.layout context (SortedSource.field "len") = _
  exact actual_length_read context frame frameType frameLocal

theorem actual_selected_probe (outer : Context) (window : SortedPhysical.Window)
    (frame : Ptr) (frameType : CType)
    (frameLocal : outer "frame".toList = scalar frameType (.ptr (some frame))) :
    read SortedProbe.layout (windowContext outer window)
      (SortedSource.sourceAt (SortedSource.id "low")) =
      (SortedPhysical.readAt frame window.1 >>= fun value => pure (.u64 value)) := by
  unfold read SortedSource.id
  rw [SortedProbe.actual_index_probe _ frame "low".toList window.1
    (names_of_scalar _ _ frameType _ (by simpa [windowContext] using frameLocal))
    (names_of_scalar _ _ SortedSource.uint32 _ (by simp [windowContext]))]
  unfold SortedPhysical.readAt
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext selected
  cases selected
  · exact (undefined_bind _).symm
  · rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements
end PettaSortedStatements

section PettaSortedTail
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def finalGuard : CExpr :=
  .binary .or (.binary .ge (SortedSource.id "low") (SortedSource.field "len"))
    (.binary .ne (SortedSource.sourceAt (SortedSource.id "low")) (SortedSource.id "source_id"))

theorem actual_final_guard (outer : Context) (window : SortedPhysical.Window)
    (frame : Ptr) (key : UInt64) (frameType : CType)
    (frameLocal : outer "frame".toList = scalar frameType (.ptr (some frame)))
    (keyLocal : outer "source_id".toList = scalar SortedSource.uint64 (.u64 key)) :
    (services.read SortedProbe.layout (windowContext outer window) finalGuard >>= truth) =
      (SortedPhysical.readLength frame >>= fun length =>
        if length ≤ window.1 then pure true
        else SortedPhysical.readAt frame window.1 >>= fun actual => pure (decide (actual ≠ key))) := by
  have left : read SortedProbe.layout (windowContext outer window)
      (.binary .ge (SortedSource.id "low") (SortedSource.field "len")) =
      (SortedPhysical.readLength frame >>= fun length => pure (.bool (decide (length ≤ window.1)))) := by
    change (read SortedProbe.layout (windowContext outer window) (SortedSource.id "low") >>= fun low =>
      read SortedProbe.layout (windowContext outer window) (SortedSource.field "len") >>= fun length =>
        binary .ge low length) = _
    unfold SortedSource.id
    rw [read_of_scalar (windowContext outer window) "low".toList SortedSource.uint32 (.u32 window.1) (by simp [windowContext]),
      actual_length_read _ frame frameType (by exact frameLocal)]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    rfl
  have right : read SortedProbe.layout (windowContext outer window)
      (.binary .ne (SortedSource.sourceAt (SortedSource.id "low")) (SortedSource.id "source_id")) =
      (SortedPhysical.readAt frame window.1 >>= fun actual => pure (.bool (decide (actual ≠ key)))) := by
    change (read SortedProbe.layout (windowContext outer window)
      (SortedSource.sourceAt (SortedSource.id "low")) >>= fun actual =>
      read SortedProbe.layout (windowContext outer window) (SortedSource.id "source_id") >>=
        fun requested => binary .ne actual requested) = _
    rw [actual_selected_probe outer window frame frameType frameLocal]
    unfold SortedSource.id
    rw [read_of_scalar (windowContext outer window) "source_id".toList SortedSource.uint64 (.u64 key) (by exact keyLocal)]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    congr 1
    funext actual
    change (pure (CVal.bool (!(actual == key))) : CProg CVal CVal) = pure (.bool (decide (actual ≠ key)))
    by_cases same : actual = key <;> simp [same]
  change ((read SortedProbe.layout (windowContext outer window)
    (.binary .ge (SortedSource.id "low") (SortedSource.field "len")) >>= fun first =>
      truth first >>= fun selected => if selected then pure (.bool true)
      else read SortedProbe.layout (windowContext outer window)
        (.binary .ne (SortedSource.sourceAt (SortedSource.id "low")) (SortedSource.id "source_id")) >>=
          fun second => truth second >>= fun chosen => pure (.bool chosen)) >>= truth) = _
  rw [left, right]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext length
  by_cases outside : length ≤ window.1
  · simp only [outside, decide_true, ↓reduceIte, Prog.ret_bind]
    rfl
  · simp only [outside, decide_false, Bool.false_eq_true, ↓reduceIte, Prog.bind_assoc, Prog.ret_bind]
    rfl

/-- The actual scalar destination declaration licenses the source dereference
store. It neither invents a pointer nor changes another local binding. -/
theorem actual_output_assignment (context : Context) (position : UInt32) (output : Ptr)
    (lowLocal : context "low".toList = scalar SortedSource.uint32 (.u32 position))
    (outputLocal : context "slot_out".toList =
      scalar ⟨"uint32_t".toList, 1⟩ (.ptr (some output))) :
    services.assignment SortedProbe.layout context
      (.assign (.unary .dereference (SortedSource.id "slot_out")) (SortedSource.id "low")) =
      (CProg.store output (.u32 position) >>= fun _ => pure context) := by
  change ObjectBindings.assignment profile SortedProbe.layout context
    (.assign (.unary .dereference (SortedSource.id "slot_out")) (SortedSource.id "low")) = _
  have type : ScalarBytes.typeOf? (ObjectBindings.types context profile.outsideTypes)
      (.unary .dereference (SortedSource.id "slot_out")) profile.fieldTypes =
        some SortedSource.uint32 := by
    simp only [ScalarBytes.typeOf?, SortedSource.id, ObjectBindings.types, outputLocal, scalar]
    rfl
  unfold SortedSource.id at type
  unfold ObjectBindings.assignment SortedSource.id
  dsimp only
  rw [type]
  change (ObjectBindings.read profile SortedProbe.layout context (SortedSource.id "low") >>= fun value =>
    ObjectBindings.writeValue profile SortedProbe.layout context
      (.unary .dereference (SortedSource.id "slot_out")) value) = _
  unfold SortedSource.id
  rw [ObjectBindings.initialized_local_keeps_its_value profile SortedProbe.layout context
    "low".toList SortedSource.uint32 (.u32 position) lowLocal]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  unfold ObjectBindings.writeValue
  dsimp only
  rw [type]
  change (ObjectBindings.place profile SortedProbe.layout context
    (.unary .dereference (SortedSource.id "slot_out")) >>= fun pointer =>
      CProg.store pointer (.u32 position) >>= fun _ => pure context) = _
  have place : ObjectBindings.place profile SortedProbe.layout context
      (.unary .dereference (SortedSource.id "slot_out")) = pure output := by
    change (ObjectBindings.read profile SortedProbe.layout context (SortedSource.id "slot_out") >>=
      fun value => pointer value >>= fun address => resolved address) = _
    unfold SortedSource.id
    rw [ObjectBindings.initialized_local_keeps_its_value profile SortedProbe.layout context
      "slot_out".toList ⟨"uint32_t".toList, 1⟩ (.ptr (some output)) outputLocal]
    rfl
  rw [place]
  rfl

/-- The final three parsed statements preserve the actual short-circuit
read sequence and publish the Boolean only after the licensed output store. -/
theorem actual_final_statements (outer : Context) (window : SortedPhysical.Window)
    (frame output : Ptr) (key : UInt64) (frameType : CType) (allowance : Nat)
    (frameLocal : outer "frame".toList = scalar frameType (.ptr (some frame)))
    (keyLocal : outer "source_id".toList = scalar SortedSource.uint64 (.u64 key))
    (outputLocal : outer "slot_out".toList =
      scalar ⟨"uint32_t".toList, 1⟩ (.ptr (some output))) :
    executeScopedWith services SortedProbe.layout allowance 8 (windowContext outer window)
      (SortedSource.body.drop 3) =
      (SortedPhysical.finish frame output key window.1 >>= fun answer =>
        pure (.finished (.returned (windowContext outer window) (some (.bool answer))))) := by
  have storeTail : executeScopedWith services SortedProbe.layout allowance 7
      (windowContext outer window)
      [.assign (.unary .dereference (SortedSource.id "slot_out")) (SortedSource.id "low"),
       .return (some (.bool true))] =
      (CProg.store output (.u32 window.1) >>= fun _ =>
        pure (.finished (.returned (windowContext outer window) (some (.bool true))))) := by
    rw [show 7 = 6 + 1 from rfl, scoped_assignment_keeps_continuation]
    rw [actual_output_assignment (windowContext outer window) window.1 output
      (by rfl) (by exact outputLocal)]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    rfl
  change executeScopedWith services SortedProbe.layout allowance 8 (windowContext outer window)
    (.branch finalGuard SortedSource.returnFalse [] ::
      [.assign (.unary .dereference (SortedSource.id "slot_out")) (SortedSource.id "low"),
       .return (some (.bool true))]) = _
  rw [show 8 = 7 + 1 from rfl, actual_branch_control,
    actual_final_guard outer window frame key frameType frameLocal keyLocal]
  have selectedFlow (rejected : Bool) :
      (executeScopedWith services SortedProbe.layout allowance 7 (windowContext outer window)
        (if rejected then SortedSource.returnFalse else []) >>= ReadBlock.resume
          (fun updated => executeScopedWith services SortedProbe.layout allowance 7 updated
            [.assign (.unary .dereference (SortedSource.id "slot_out")) (SortedSource.id "low"),
             .return (some (.bool true))])) =
      (if rejected then pure (.finished (.returned (windowContext outer window) (some (.bool false))))
       else CProg.store output (.u32 window.1) >>= fun _ =>
         pure (.finished (.returned (windowContext outer window) (some (.bool true))))) := by
    cases rejected with
    | false =>
        change executeScopedWith services SortedProbe.layout allowance 7 (windowContext outer window)
          [.assign (.unary .dereference (SortedSource.id "slot_out")) (SortedSource.id "low"),
           .return (some (.bool true))] = _
        exact storeTail
    | true => rfl
  unfold SortedPhysical.finish
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext length
  by_cases outside : length ≤ window.1
  · simp only [outside, ↓reduceIte, Prog.pure_eq, Prog.ret_bind]
    exact selectedFlow true
  · simp only [outside, ↓reduceIte, Prog.bind_assoc]
    congr 1
    funext actual
    simp only [Prog.pure_eq, Prog.ret_bind]
    have selected := selectedFlow (decide (actual ≠ key))
    simp only [Prog.bind_eq, Prog.pure_eq] at selected
    rw [selected]
    by_cases different : actual ≠ key
    · rw [if_pos (decide_eq_true different), if_pos different]
      rfl
    · simp only [different, decide_false, Bool.false_eq_true, ↓reduceIte,
        Prog.bind_assoc, Prog.ret_bind]

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements
end PettaSortedTail

section PettaSortedWhole
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def restoreBounds (outer : Context) (result : ReadBlock.Result Context) : ReadBlock.Result Context :=
  ObjectBindings.restore "low".toList (outer "low".toList)
    (ObjectBindings.restore "high".toList (outer "high".toList) result)

theorem restored_window_context (outer : Context) (window : SortedPhysical.Window) :
    Function.update (Function.update (windowContext outer window) "high".toList
      (outer "high".toList)) "low".toList (outer "low".toList) = outer := by
  funext name
  simp only [windowContext, Function.update_apply]
  split_ifs <;> simp_all

theorem restore_bounds_result (outer : Context) (result : ReadBlock.Result SortedPhysical.Window) :
    restoreBounds outer (result.mapContext (windowContext outer)) =
      result.mapContext (fun _ => outer) := by
  cases result with
  | exhausted => rfl
  | finished flow =>
      cases flow <;> simp only [restoreBounds, ObjectBindings.restore,
        ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext, restored_window_context]

theorem actual_while_suffix (outer : Context) (window : SortedPhysical.Window)
    (frame output : Ptr) (key : UInt64) (frameType : CType) (allowance : Nat)
    (frameLocal : outer "frame".toList = scalar frameType (.ptr (some frame)))
    (keyLocal : outer "source_id".toList = scalar SortedSource.uint64 (.u64 key))
    (outputLocal : outer "slot_out".toList =
      scalar ⟨"uint32_t".toList, 1⟩ (.ptr (some output))) :
    executeScopedWith services SortedProbe.layout allowance 9 (windowContext outer window)
      (SortedSource.body.drop 2) =
      (SortedPhysical.search frame key allowance window >>= fun result => match result with
        | .finished (.next updated) => SortedPhysical.finish frame output key updated.1 >>= fun answer =>
            pure (.finished (.returned (windowContext outer updated) (some (.bool answer))))
        | other => pure (other.mapContext (windowContext outer))) := by
  change executeScopedWith services SortedProbe.layout allowance 9 (windowContext outer window)
    (.whileLoop (.binary .lt (SortedSource.id "low") (SortedSource.id "high"))
      SortedSource.iteration :: SortedSource.body.drop 3) = _
  rw [show 9 = 8 + 1 from rfl, scoped_while_keeps_guard_body_and_continuation _ _ _ _ _ _ _ _ rfl,
    actual_loop_uses_owned_search outer window frame key frameType allowance frameLocal keyLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext result
  cases result with
  | exhausted => rfl
  | finished flow =>
      cases flow with
      | next updated =>
          exact actual_final_statements outer updated frame output key frameType allowance
            frameLocal keyLocal outputLocal
      | broken updated => rfl
      | returned updated value => rfl

private theorem scalar_word_declaration (context : Context) (name : Name) (operand : CExpr)
    (valueRead : CProg CVal UInt32)
    (readValue : ObjectBindings.read profile SortedProbe.layout context operand =
      (valueRead >>= fun value => pure (.u32 value)))
    (continuation : Context → CProg CVal (ReadBlock.Result Context)) :
    services.declaration SortedProbe.layout context SortedSource.uint32 name (some operand) continuation =
      (valueRead >>= fun value =>
        continuation (Function.update context name (scalar SortedSource.uint32 (.u32 value))) >>=
          fun result => pure (ObjectBindings.restore name (context name) result)) := by
  have declarationProvider : services.declaration =
      ObjectBindings.declaration profile (fun _ _ _ => CProg.undefined) := rfl
  rw [declarationProvider,
    ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow _ _ _ _ _ _ _ (by rfl), readValue]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

def program (allowance : Nat) (outer : Context) : CProg CVal (ReadBlock.Result Context) :=
  executeScopedWith services SortedProbe.layout allowance 11 outer SortedSource.body

/-- These are the source block's physical operations, including the initial
length read, every probe, the final length reread and the selected output store.
Non-normal loop results remain non-normal under the same scope restoration. -/
def operations (allowance : Nat) (outer : Context) (frame output : Ptr) (key : UInt64) :
    CProg CVal (ReadBlock.Result Context) := do
  let length ← SortedPhysical.readLength frame
  let result ← SortedPhysical.search frame key allowance (0, length)
  match result with
  | .finished (.next updated) =>
      let answer ← SortedPhysical.finish frame output key updated.1
      pure (.finished (.returned outer (some (.bool answer))))
  | other => pure (other.mapContext (fun _ => outer))

/-- Exact parsed-control correspondence. Both loop locals are restored only
after the actual body and final guard return; the physical operation tree,
including any suspended read or unfinished loop, is retained. -/
theorem program_uses_memory_operations (outer : Context) (frame output : Ptr)
    (key : UInt64) (frameType : CType) (allowance : Nat)
    (frameLocal : outer "frame".toList = scalar frameType (.ptr (some frame)))
    (keyLocal : outer "source_id".toList = scalar SortedSource.uint64 (.u64 key))
    (outputLocal : outer "slot_out".toList =
      scalar ⟨"uint32_t".toList, 1⟩ (.ptr (some output))) :
    program allowance outer = operations allowance outer frame output key := by
  unfold program
  change executeScopedWith services SortedProbe.layout allowance 11 outer
    (.declare SortedSource.uint32 "low".toList (.unsignedInteger 0) ::
      .declare SortedSource.uint32 "high".toList (SortedSource.field "len") ::
        SortedSource.body.drop 2) = _
  rw [show 11 = 10 + 1 from rfl, scoped_initialized_declaration_keeps_continuation,
    scalar_word_declaration outer "low".toList (.unsignedInteger 0) (pure 0) (by rfl)]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rw [show 10 = 9 + 1 from rfl, scoped_initialized_declaration_keeps_continuation,
    scalar_word_declaration _ "high".toList (SortedSource.field "len")
      (SortedPhysical.readLength frame) (actual_length_initializer _ frame frameType (by exact frameLocal))]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  change (SortedPhysical.readLength frame >>= fun length =>
    executeScopedWith services SortedProbe.layout allowance 9 (windowContext outer (0, length))
      (SortedSource.body.drop 2) >>= fun result => pure (restoreBounds outer result)) = _
  unfold operations
  congr 1
  funext length
  rw [actual_while_suffix outer (0, length) frame output key frameType allowance
    frameLocal keyLocal outputLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext result
  cases result with
  | exhausted => rfl
  | finished flow =>
      cases flow with
      | broken updated =>
          simp only [Prog.pure_eq, Prog.ret_bind, restore_bounds_result]
      | returned updated value =>
          simp only [Prog.pure_eq, Prog.ret_bind, restore_bounds_result]
      | next updated =>
          simp only [Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
          congr 1
          funext answer
          change (pure (restoreBounds outer
            ((ReadBlock.Result.finished (.returned updated (some (.bool answer)))).mapContext
              (windowContext outer))) : CProg CVal (ReadBlock.Result Context)) = _
          rw [restore_bounds_result]
          rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements
end PettaSortedWhole

section PettaSortedOwned
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Complete correctness for the actual parsed sorted suffix. The admitted
inventory supplies owned cells, a count and strict order. It does not supply
probe outcomes or a whole-loop simulation. Successful completion returns the
unique slot; completed refusal excludes all slots and preserves the old output.
The statement budget is sufficient for this fixed block; loop allowance is
derived from the actual initial interval. -/
theorem parsed_sorted_suffix_owned (outer : Context) (frame schema output : Ptr)
    (length : UInt32) (sources : List UInt64) (key : UInt64) (frameType : CType)
    (old : CVal) (rest : Heap L → Prop) (allowance : Nat)
    (frameLocal : outer "frame".toList = scalar frameType (.ptr (some frame)))
    (keyLocal : outer "source_id".toList = scalar SortedSource.uint64 (.u64 key))
    (outputLocal : outer "slot_out".toList =
      scalar ⟨"uint32_t".toList, 1⟩ (.ptr (some output)))
    (count : sources.length = length.toNat)
    (sorted : Increasing (SortedPhysical.valueAt sources) length.toNat)
    (enough : length.toNat ≤ allowance) :
    CTriple (SortedPhysical.held frame schema length sources (PointsTo output old ∗ rest))
      (program allowance outer)
      (fun result heap => ∃ position : UInt32, ∃ answer : Bool,
        result = .finished (.returned outer (some (.bool answer))) ∧
        (answer = true ↔ ∃ index, index < sources.length ∧
          SortedPhysical.valueAt sources index = key.toNat) ∧
        (∀ index, index < sources.length → SortedPhysical.valueAt sources index = key.toNat →
          index = position.toNat) ∧
        SortedPhysical.held frame schema length sources
          (PointsTo output (if answer then .u32 position else old) ∗ rest) heap) := by
  rw [program_uses_memory_operations outer frame output key frameType allowance
    frameLocal keyLocal outputLocal]
  intro heap owned
  change (operations allowance outer frame output key).wp act _ heap
  unfold operations
  rw [wp_bind']
  refine wp_consequence act
    (SortedPhysical.read_length_owned frame schema length sources _) owned ?_
  intro actualLength reached observed
  obtain ⟨same, owned⟩ := observed
  subst actualLength
  rw [wp_bind']
  have initial : SortedPhysical.invariant frame schema length sources key
      (PointsTo output old ∗ rest) (0, length) reached :=
    ⟨initial_window _ _ _, owned⟩
  refine wp_consequence act
    (SortedPhysical.search_closes_window frame schema length sources key
      (PointsTo output old ∗ rest) count sorted allowance (0, length) (by simpa using enough))
    initial ?_
  rintro result after ⟨updated, rfl, closed, searchInvariant, held⟩
  change (SortedPhysical.finish frame output key updated.1 >>= fun answer =>
    pure (ReadBlock.Result.finished (.returned outer (some (.bool answer))))).wp act _ after
  rw [wp_bind']
  have finalWindow : SearchWindow (SortedPhysical.valueAt sources) length.toNat key.toNat
      updated.1.toNat updated.1.toNat := by
    simpa only [← closed] using searchInvariant
  refine wp_consequence act
    (SortedPhysical.finish_closed_window_owned frame schema output length updated.1 sources key
      old rest count sorted finalWindow) held ?_
  rintro answer finalHeap ⟨classification, unique, preserved⟩
  rw [wp_pure]
  exact ⟨updated.1, answer, rfl, classification, unique, preserved⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements
end PettaSortedOwned

section PettaSortedWholeControls
set_option autoImplicit false

end PettaSortedWholeControls

section PettaSortedCoordinate
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

/-- The physical sorted schema contains its declared prefix. A grown frame can
have additional slots; their count is not substituted for `schema->len`. -/
def schemaSources (frame : FrameReadback) : List UInt64 :=
  (frame.slots.take frame.view.schemaSlotCount).map
    (fun slot => UInt64.ofBitVec slot.sourceId)

theorem schemaSources_length (frame : FrameReadback) :
    (schemaSources frame).length = frame.view.schemaSlotCount := by
  have within : frame.view.schemaSlotCount ≤ frame.slots.length := by
    rw [frame.inventory_count]
    exact frame.admitted.1.2.2.1
  simp only [schemaSources, List.length_map, List.length_take, Nat.min_eq_left within]

theorem schemaSources_readout (frame : FrameReadback) (index : Nat)
    (declared : index < frame.view.schemaSlotCount) :
    SortedPhysical.valueAt (schemaSources frame) index =
      (frame.slots[index]'(by have := frame.admitted.1.2.2.1; have := frame.inventory_count; omega)).sourceId.toNat := by
  have inRange : index < (schemaSources frame).length := by
    rw [schemaSources_length]
    exact declared
  rw [SortedPhysical.valueAt_of_inRange _ _ inRange]
  simp only [schemaSources, List.getElem_map, List.getElem_take, UInt64.toNat_ofBitVec]

theorem schemaSources_increasing (frame : FrameReadback) :
    Increasing (SortedPhysical.valueAt (schemaSources frame)) frame.view.schemaSlotCount := by
  intro first second less within
  rw [schemaSources_readout frame first (by omega), schemaSources_readout frame second within]
  have ordered := (List.pairwise_iff_getElem.mp frame.admitted.2.2.1)
  exact ordered first second (by have := frame.admitted.1.2.2.1; have := frame.inventory_count; omega)
    (by have := frame.admitted.1.2.2.1; have := frame.inventory_count; omega) less

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- The actual parsed sorted suffix writes the coordinate of a declared slot
in the existing frame inventory. The directory readback retains its generation.
Physical directory probing, schema lifetime and the entry guard are separate
component obligations; no directory lookup execution is assumed here. -/
theorem current_coordinate_sorted_owned (directory : DirectoryReadback)
    (frame : FrameReadback) (member : frame ∈ directory.frames)
    (index : Fin frame.slots.length) (declared : index.val < frame.view.schemaSlotCount)
    (outer : Context) (physicalFrame schema output : Ptr)
    (length : UInt32) (key : UInt64) (frameType : CType)
    (old : CVal) (rest : Heap L → Prop) (allowance : Nat)
    (frameLocal : outer "frame".toList = scalar frameType (.ptr (some physicalFrame)))
    (keyLocal : outer "source_id".toList = scalar SortedSource.uint64 (.u64 key))
    (outputLocal : outer "slot_out".toList =
      scalar ⟨"uint32_t".toList, 1⟩ (.ptr (some output)))
    (count : length.toNat = frame.view.schemaSlotCount)
    (sourceIdentity : key.toNat = frame.slots[index.val].sourceId.toNat)
    (enough : length.toNat ≤ allowance) :
    CTriple
      (SortedPhysical.held physicalFrame schema length (schemaSources frame)
        (PointsTo output old ∗ rest))
      (program allowance outer)
      (fun result heap =>
        result = .finished (.returned outer (some (.bool true))) ∧
        directory.variableCoordinate? frame.slots[index.val].varId =
          some (frame.view.token.ref index.val) ∧
        SortedPhysical.held physicalFrame schema length (schemaSources frame)
          (PointsTo output (.u32 (UInt32.ofNat index.val)) ∗ rest) heap) := by
  have physicalCount : (schemaSources frame).length = length.toNat :=
    (schemaSources_length frame).trans count.symm
  have sorted : Increasing (SortedPhysical.valueAt (schemaSources frame)) length.toNat := by
    rw [count]
    exact schemaSources_increasing frame
  have inRange : index.val < (schemaSources frame).length := by
    rw [schemaSources_length]
    exact declared
  have found : SortedPhysical.valueAt (schemaSources frame) index.val = key.toNat :=
    (schemaSources_readout frame index.val declared).trans sourceIdentity.symm
  intro heap owned
  obtain ⟨safe, post⟩ := parsed_sorted_suffix_owned outer physicalFrame schema output length
    (schemaSources frame) key frameType old rest allowance frameLocal keyLocal outputLocal
    physicalCount sorted enough heap owned
  refine ⟨safe, ?_⟩
  intro result final ran
  obtain ⟨position, answer, returned, classification, unique, cells⟩ := post result final ran
  have accepted : answer = true := classification.mpr ⟨index.val, inRange, found⟩
  subst answer
  have same : index.val = position.toNat := unique index.val inRange found
  have positionSame : position = UInt32.ofNat index.val := by
    rw [same]
    simp
  exact ⟨returned, directory.variableCoordinate_slot frame member index,
    by simpa only [positionSame, Bool.true_eq, ↓reduceIte] using cells⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements
end PettaSortedCoordinate

section PhysicalAtomStorage

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps (Address TargetValue TargetMemory)
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open StatementBlock

def atomType : CType := ⟨"Atom".toList, 0⟩
def atomPointerType : CType := ⟨"Atom".toList, 1⟩
def childrenType : CType := ⟨"Atom".toList, 2⟩
def expressionArmType : CType := ⟨"AtomExpressionArm".toList, 0⟩
def wordType : CType := ⟨"uint32_t".toList, 0⟩
def wideType : CType := ⟨"uint64_t".toList, 0⟩

/-- This is the declaration-order scalar-cell view of the selected fields.
The expression arm starts at the last union; its pointer/count remain separate. -/
def atomLayout : ReadExpressions.Layout := fun name =>
  if name = "kind".toList then some ⟨0, .word⟩
  else if name = "var_id".toList then some ⟨2, .word64⟩
  else if name = "symbol_number".toList then some ⟨3, .word⟩
  else if name = "arena_id".toList then some ⟨4, .word⟩
  else if name = "spelling".toList ∨ name = "name_key".toList then some ⟨5, .pointer⟩
  else if name = "expr".toList then some ⟨8, .embedded⟩
  else none

def expressionLayout : ReadExpressions.Layout := fun name =>
  if name = "elems".toList then some ⟨0, .pointer⟩
  else if name = "len".toList then some ⟨1, .word64⟩ else none

def profile : ObjectBindings.Profile where
  values := ReadExpressions.noCalls
  locations := fun _ => none
  outsideTypes := fun _ => none
  outsidePlaces := fun _ => none
  fieldTypes := fun type name =>
    if type = atomType then
      if name = "kind".toList ∨ name = "symbol_number".toList ∨
          name = "arena_id".toList then some wordType
      else if name = "var_id".toList then some wideType
      else if name = "spelling".toList then some ⟨"CettaSymbolSpelling".toList, 1⟩
      else if name = "name_key".toList then some atomPointerType
      else if name = "expr".toList then some expressionArmType else none
    else if type = expressionArmType then
      if name = "elems".toList then some childrenType
      else if name = "len".toList then some wideType else none
    else none
  cellExtent := fun type => if type = atomPointerType then some 1 else none
  byteExtent := fun _ => none
  sizeWidth := .bits64
  recordFields := some fun type =>
    if type = atomType then atomLayout
    else if type = expressionArmType then expressionLayout else fun _ => none

def context (atom : Ptr) (index : UInt64) : ObjectBindings.Context := fun name =>
  if name = "atom".toList then some (.scalar atomPointerType (some (.ptr (some atom))))
  else if name = "i".toList then some (.scalar wideType (some (.u64 index)))
  else none

def atomOperand : CExpr := .identifier "atom".toList
def kindOperand : CExpr := .field atomOperand "kind".toList true
def variableOperand : CExpr := .field atomOperand "var_id".toList true
def symbolOperand : CExpr := .field atomOperand "symbol_number".toList true
def arenaOperand : CExpr := .field atomOperand "arena_id".toList true
def spellingOperand : CExpr := .field atomOperand "spelling".toList true
def forwardOperand : CExpr := .field atomOperand "name_key".toList true
def expressionOperand : CExpr := .field atomOperand "expr".toList true
def elementsOperand : CExpr := .field expressionOperand "elems".toList false
def lengthOperand : CExpr := .field expressionOperand "len".toList false
def childOperand : CExpr := .index elementsOperand (.identifier "i".toList)

theorem selected_operands_parse :
    expressionText? [] "atom->kind".toList = some kindOperand ∧
    expressionText? [] "atom->var_id".toList = some variableOperand ∧
    expressionText? [] "atom->symbol_number".toList = some symbolOperand ∧
    expressionText? [] "atom->expr.elems".toList = some elementsOperand ∧
    expressionText? [] "atom->expr.len".toList = some lengthOperand ∧
    expressionText? [] "atom->expr.elems[i]".toList = some childOperand := by
  cbv

def readOperand (atom : Ptr) (index : UInt64) (operand : CExpr) : CProg CVal CVal :=
  ReadExpressions.expressionWithNames
    (ReadExpressions.localOrLocated (ObjectBindings.values (context atom index))
      (ObjectBindings.declared (context atom index)) profile.locations)
    profile.values atomLayout operand
    { ObjectBindings.objects profile (context atom index) with
      indexKind := some fun array => do
        let type ← ScalarBytes.typeOf?
          (ObjectBindings.types (context atom index) profile.outsideTypes)
          array profile.fieldTypes
        if type = childrenType then some .pointer else none }

theorem kind_uses_actual_cell (atom : Ptr) (index : UInt64) :
    readOperand atom index kindOperand =
      (CProg.loadU32 atom >>= fun kind => pure (.u32 kind)) := rfl

theorem variable_uses_all_identity_bits (atom : Ptr) (index : UInt64) :
    readOperand atom index variableOperand =
      (CProg.loadU64 (atom + 2) >>= fun identifier => pure (.u64 identifier)) := rfl

theorem symbol_uses_actual_number (atom : Ptr) (index : UInt64) :
    readOperand atom index symbolOperand =
      (CProg.loadU32 (atom + 3) >>= fun identifier => pure (.u32 identifier)) := rfl

theorem spelling_uses_actual_pointer (atom : Ptr) (index : UInt64) :
    readOperand atom index spellingOperand =
      (CProg.loadPtr (atom + 5) >>= fun spelling => pure (.ptr spelling)) := rfl

theorem arena_uses_actual_cell (atom : Ptr) (index : UInt64) :
    readOperand atom index arenaOperand =
      (CProg.loadU32 (atom + 4) >>= fun arena => pure (.u32 arena)) := rfl

theorem forwarding_uses_alias_pointer (atom : Ptr) (index : UInt64) :
    readOperand atom index forwardOperand =
      (CProg.loadPtr (atom + 5) >>= fun next => pure (.ptr next)) := rfl

theorem forwarding_operands_parse :
    expressionText? [] "atom->arena_id".toList = some arenaOperand ∧
    expressionText? [] "atom->name_key".toList = some forwardOperand ∧
    expressionText? [] "atom->spelling".toList = some spellingOperand := by
  cbv

theorem expression_elements_uses_active_arm (atom : Ptr) (index : UInt64) :
    readOperand atom index elementsOperand =
      (CProg.loadPtr (atom + 8) >>= fun elements => pure (.ptr elements)) := rfl

theorem expression_length_uses_all_length_bits (atom : Ptr) (index : UInt64) :
    readOperand atom index lengthOperand =
      (CProg.loadU64 (atom + 9) >>= fun count => pure (.u64 count)) := rfl

def childOperation (atom : Ptr) (index : UInt64) : CProg CVal CVal := do
  let elements ← CProg.loadPtr (atom + 8)
  match elements with
  | none => CProg.undefined
  | some elements => do
      let child ← CProg.loadPtr (elements + index.toNat)
      pure (.ptr child)

theorem expression_child_uses_current_pointer_array (atom : Ptr) (index : UInt64) :
    readOperand atom index childOperand = childOperation atom index := by
  change (readOperand atom index elementsOperand >>= fun elements =>
    pure (CVal.u64 index) >>= fun position =>
      ReadExpressions.indexedScalar .pointer elements position) = _
  rw [expression_elements_uses_active_arm]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  unfold childOperation
  simp only [Prog.bind_eq]
  congr 1
  funext elements
  cases elements with
  | none => rfl
  | some elements => rfl

/-- Logical Address fields are paths inside decoded records. A physical pointer
names only a block and scalar-cell offset; a path is never silently flattened. -/
def physicalPointer? (address : Address) : Option Ptr :=
  if address.fields = [] then some ⟨address.storage, address.element⟩ else none

@[simp] theorem physicalPointer_physicalAddress (pointer : Ptr) :
    physicalPointer? (CurrentValueRead.physicalAddress pointer) = some pointer := rfl

theorem physicalPointer_reflects {address : Address} {pointer : Ptr}
    (read : physicalPointer? address = some pointer) :
    CurrentValueRead.physicalAddress pointer = address := by
  unfold physicalPointer? at read
  split at read
  · next plain =>
    cases Option.some.inj read
    cases address
    simp_all [CurrentValueRead.physicalAddress]
  · simp at read

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

def cell? (heap : Heap L) (pointer : Ptr) : Option CVal :=
  (read ((heap pointer.block).2 pointer.offset)).join

def word? (heap : Heap L) (pointer : Ptr) : Option UInt32 := do
  match ← cell? heap pointer with
  | .u32 value => some value
  | _ => none

/-- Read the declared unsigned-byte storage cell, retaining all eight bits. -/
def byte? (heap : Heap L) (pointer : Ptr) : Option UInt8 := do
  match ← cell? heap pointer with
  | .u8 value => some value
  | _ => none

def wide? (heap : Heap L) (pointer : Ptr) : Option UInt64 := do
  match ← cell? heap pointer with
  | .u64 value => some value
  | _ => none

def pointer? (heap : Heap L) (pointer : Ptr) : Option (Option Ptr) := do
  match ← cell? heap pointer with
  | .ptr value => some value
  | _ => none

/-- Only fields actually needed for the structural observer are projected.
Unit entries mark unobserved coordinates, not fabricated scalar contents. -/
def symbolRecord (identifier : UInt32) (spelling : Option Ptr) : TargetValue :=
  .record "Atom" [.word 0, .unit, .unit, .word (BitVec.ofNat 64 identifier.toNat),
    .unit, .reference (spelling.map CurrentValueRead.physicalAddress)]

def variableRecord (identifier : UInt64) : TargetValue :=
  .record "Atom" [.word 1, .unit, .word identifier.toBitVec]

def expressionRecord (elements : Option Ptr) (count : UInt64) : TargetValue :=
  .record "Atom" [.word 3, .unit, .unit, .unit, .unit, .unit, .unit, .unit,
    .record "expr" [.reference (elements.map CurrentValueRead.physicalAddress), .word count.toBitVec]]

def structuralRecord? (heap : Heap L) (atom : Ptr) : Option TargetValue := do
  let kind ← word? heap atom
  if kind = 0 then do
    let identifier ← word? heap (atom + 3)
    let spelling ← pointer? heap (atom + 5)
    pure (symbolRecord identifier spelling)
  else if kind = 1 then do
    let identifier ← wide? heap (atom + 2)
    pure (variableRecord identifier)
  else if kind = 3 then do
    let elements ← pointer? heap (atom + 8)
    let count ← wide? heap (atom + 9)
    pure (expressionRecord elements count)
  else none

/-- The byte buffer is an embedded member, not a pointer stored in its
first byte. The logical-cell layout and unsigned-byte representation remain
explicit native ABI obligations. The hash is not read by these helpers. -/
def spellingRecord (spelling : Ptr) (length : UInt32) : TargetValue :=
  .record "CettaSymbolSpelling" [.unit, .word (BitVec.ofNat 64 length.toNat),
    .reference (some (CurrentValueRead.physicalAddress (spelling + 2)))]

def spellingRecord? (heap : Heap L) (spelling : Ptr) : Option TargetValue :=
  (word? heap (spelling + 1)).map (spellingRecord spelling)

/-- This is a structural memory observer, not a new evaluator or recursive atom
decoder. Inactive union arms, grounded resources and unregistered objects are
not inferred from their bytes. -/
inductive ObjectKind where
  | atom
  | pointerCell
  | spelling
  | byteCell
  deriving DecidableEq, Repr

abbrev Inventory := Ptr → Option ObjectKind

def memory (inventory : Inventory) (heap : Heap L) : TargetMemory where
  cells := fun block offset =>
    let pointer : Ptr := ⟨block, offset⟩
    match inventory pointer with
    | some .atom => structuralRecord? heap pointer
    | some .pointerCell =>
        (pointer? heap pointer).map (fun value =>
          .reference (value.map CurrentValueRead.physicalAddress))
    | some .spelling => spellingRecord? heap pointer
    | some .byteCell => (byte? heap pointer).map (fun value => .byte value.toBitVec)
    | none => none
  owned := fun _ => none

/-- The logical reader never manufactures ownership from its borrowed view. -/
theorem borrowed_memory_has_no_ownership (inventory : Inventory) (heap : Heap L)
    (block : Nat) : (memory inventory heap).owned block = none := rfl

theorem atom_record_from_inventory (inventory : Inventory) (heap : Heap L) (atom : Ptr)
    (registered : inventory atom = some .atom) :
    Mettapedia.GSLT.LanguageDef.NativeOps.targetRead (memory inventory heap)
      (CurrentValueRead.physicalAddress atom) = structuralRecord? heap atom := by
  simp [Mettapedia.GSLT.LanguageDef.NativeOps.targetRead, memory,
    CurrentValueRead.physicalAddress, registered,
    Mettapedia.GSLT.LanguageDef.NativeOps.targetReadPath]

theorem cell_of_owned (pointer : Ptr) (value : CVal) (rest : Heap L → Prop)
    (heap : Heap L) (held : (PointsTo pointer value ∗ rest) heap) :
    cell? heap pointer = some value := by
  simp only [cell?, read_of_pointsTo held, Option.join_some]

theorem variable_record_owned (atom : Ptr) (identifier : UInt64) (rest : Heap L → Prop)
    (heap : Heap L)
    (held : (PointsTo atom (.u32 1) ∗ PointsTo (atom + 2) (.u64 identifier) ∗ rest) heap) :
    structuralRecord? heap atom = some (variableRecord identifier) := by
  have tag := cell_of_owned atom (.u32 1) _ heap held
  have identity : cell? heap (atom + 2) = some (.u64 identifier) :=
    cell_of_owned _ _ (PointsTo atom (.u32 1) ∗ rest) heap (by cmem_exact)
  simp [structuralRecord?, word?, wide?, tag, identity]

theorem symbol_record_owned (atom : Ptr) (identifier : UInt32) (spelling : Option Ptr)
    (rest : Heap L → Prop) (heap : Heap L)
    (held : (PointsTo atom (.u32 0) ∗ PointsTo (atom + 3) (.u32 identifier) ∗
      PointsTo (atom + 5) (.ptr spelling) ∗ rest) heap) :
    structuralRecord? heap atom = some (symbolRecord identifier spelling) := by
  have tag := cell_of_owned atom (.u32 0) _ heap held
  have number : cell? heap (atom + 3) = some (.u32 identifier) :=
    cell_of_owned _ _ (PointsTo atom (.u32 0) ∗ PointsTo (atom + 5) (.ptr spelling) ∗ rest)
      heap (by cmem_exact)
  have spellingRead : cell? heap (atom + 5) = some (.ptr spelling) :=
    cell_of_owned _ _ (PointsTo atom (.u32 0) ∗ PointsTo (atom + 3) (.u32 identifier) ∗ rest)
      heap (by cmem_exact)
  simp [structuralRecord?, word?, pointer?, tag, number, spellingRead]

theorem expression_record_owned (atom : Ptr) (elements : Option Ptr) (count : UInt64)
    (rest : Heap L → Prop) (heap : Heap L)
    (held : (PointsTo atom (.u32 3) ∗ PointsTo (atom + 8) (.ptr elements) ∗
      PointsTo (atom + 9) (.u64 count) ∗ rest) heap) :
    structuralRecord? heap atom = some (expressionRecord elements count) := by
  have tag := cell_of_owned atom (.u32 3) _ heap held
  have elementsRead : cell? heap (atom + 8) = some (.ptr elements) :=
    cell_of_owned _ _ (PointsTo atom (.u32 3) ∗ PointsTo (atom + 9) (.u64 count) ∗ rest)
      heap (by cmem_exact)
  have countRead : cell? heap (atom + 9) = some (.u64 count) :=
    cell_of_owned _ _ (PointsTo atom (.u32 3) ∗ PointsTo (atom + 8) (.ptr elements) ∗ rest)
      heap (by cmem_exact)
  simp [structuralRecord?, word?, pointer?, wide?, tag, elementsRead, countRead]

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

end PhysicalAtomStorage

section PhysicalAtomPrograms

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps (Address TargetValue TargetMemory targetRead targetReadPath sourceFieldAddress)

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

def structuralProgram (atom : Ptr) : CProg CVal (Option TargetValue) := do
  match ← readOperand atom 0 kindOperand with
  | .u32 kind =>
    if kind = 0 then do
      match ← readOperand atom 0 symbolOperand,
          ← readOperand atom 0 spellingOperand with
      | .u32 identifier, .ptr spelling => pure (some (symbolRecord identifier spelling))
      | _, _ => CProg.undefined
    else if kind = 1 then do
      match ← readOperand atom 0 variableOperand with
      | .u64 identifier => pure (some (variableRecord identifier))
      | _ => CProg.undefined
    else if kind = 3 then do
      match ← readOperand atom 0 elementsOperand,
          ← readOperand atom 0 lengthOperand with
      | .ptr elements, .u64 count => pure (some (expressionRecord elements count))
      | _, _ => CProg.undefined
    else pure none
  | _ => CProg.undefined

def structuralOperations (atom : Ptr) : CProg CVal (Option TargetValue) := do
  let kind ← CProg.loadU32 atom
  if kind = 0 then do
    let identifier ← CProg.loadU32 (atom + 3)
    let spelling ← CProg.loadPtr (atom + 5)
    pure (some (symbolRecord identifier spelling))
  else if kind = 1 then do
    let identifier ← CProg.loadU64 (atom + 2)
    pure (some (variableRecord identifier))
  else if kind = 3 then do
    let elements ← CProg.loadPtr (atom + 8)
    let count ← CProg.loadU64 (atom + 9)
    pure (some (expressionRecord elements count))
  else pure none

theorem structural_program_uses_selected_fields (atom : Ptr) :
    structuralProgram atom = structuralOperations atom := by
  unfold structuralProgram structuralOperations
  rw [kind_uses_actual_cell]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext kind
  split
  · rw [symbol_uses_actual_number, spelling_uses_actual_pointer]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  · split
    · rw [variable_uses_all_identity_bits]
      simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    · split
      · rw [expression_elements_uses_active_arm, expression_length_uses_all_length_bits]
        simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
      · rfl

theorem structural_program_readOnly (atom : Ptr) :
    ReadExpressions.ReadOnly (L := L) (structuralProgram atom) := by
  rw [structural_program_uses_selected_fields]
  unfold structuralOperations
  apply ReadExpressions.bind_readOnly _ _ (ReadExpressions.load_word_readOnly atom)
  intro kind
  split
  · apply ReadExpressions.bind_readOnly _ _ (ReadExpressions.load_word_readOnly (atom + 3))
    intro identifier
    apply ReadExpressions.bind_readOnly _ _ (ReadExpressions.load_pointer_readOnly (atom + 5))
    intro spelling
    exact ReadExpressions.pure_readOnly _
  · split
    · apply ReadExpressions.bind_readOnly _ _ (ReadExpressions.load_word64_readOnly (atom + 2))
      intro identifier
      exact ReadExpressions.pure_readOnly _
    · split
      · apply ReadExpressions.bind_readOnly _ _ (ReadExpressions.load_pointer_readOnly (atom + 8))
        intro elements
        apply ReadExpressions.bind_readOnly _ _ (ReadExpressions.load_word64_readOnly (atom + 9))
        intro count
        exact ReadExpressions.pure_readOnly _
      · exact ReadExpressions.pure_readOnly _

theorem variable_program_owned (atom : Ptr) (identifier : UInt64) (rest : Heap L → Prop) :
    CTriple (PointsTo atom (.u32 1) ∗ PointsTo (atom + 2) (.u64 identifier) ∗ rest)
      (structuralProgram atom)
      (fun actual heap => actual = some (variableRecord identifier) ∧
        (PointsTo atom (.u32 1) ∗ PointsTo (atom + 2) (.u64 identifier) ∗ rest) heap) := by
  rw [structural_program_uses_selected_fields]
  cmem_start heap held
  unfold structuralOperations
  simp only [CProg.loadU32, CProg.loadU64, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen [CProg.loadU64, (by decide : (1 : UInt32) ≠ 0)]
  cmem_exact

theorem symbol_program_owned (atom : Ptr) (identifier : UInt32) (spelling : Option Ptr)
    (rest : Heap L → Prop) :
    CTriple (PointsTo atom (.u32 0) ∗ PointsTo (atom + 3) (.u32 identifier) ∗
      PointsTo (atom + 5) (.ptr spelling) ∗ rest)
      (structuralProgram atom)
      (fun actual heap => actual = some (symbolRecord identifier spelling) ∧
        (PointsTo atom (.u32 0) ∗ PointsTo (atom + 3) (.u32 identifier) ∗
          PointsTo (atom + 5) (.ptr spelling) ∗ rest) heap) := by
  rw [structural_program_uses_selected_fields]
  cmem_start heap held
  unfold structuralOperations
  simp only [CProg.loadU32, CProg.loadPtr, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen [CProg.loadU64]
  cmem_exact

theorem expression_program_owned (atom : Ptr) (elements : Option Ptr) (count : UInt64)
    (rest : Heap L → Prop) :
    CTriple (PointsTo atom (.u32 3) ∗ PointsTo (atom + 8) (.ptr elements) ∗
      PointsTo (atom + 9) (.u64 count) ∗ rest)
      (structuralProgram atom)
      (fun actual heap => actual = some (expressionRecord elements count) ∧
        (PointsTo atom (.u32 3) ∗ PointsTo (atom + 8) (.ptr elements) ∗
          PointsTo (atom + 9) (.u64 count) ∗ rest) heap) := by
  rw [structural_program_uses_selected_fields]
  cmem_start heap held
  unfold structuralOperations
  simp only [CProg.loadU32, CProg.loadU64, CProg.loadPtr, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen [CProg.loadU64, (by decide : (3 : UInt32) ≠ 0),
    (by decide : (3 : UInt32) ≠ 1)]
  cmem_exact

theorem field_from_registered_record (inventory : Inventory) (heap : Heap L)
    (atom : Ptr) (record : TargetValue) (index : Nat)
    (registered : inventory atom = some .atom)
    (read : structuralRecord? heap atom = some record) :
    targetRead (memory inventory heap)
      (sourceFieldAddress (CurrentValueRead.physicalAddress atom) index) =
      targetReadPath [index] record := by
  simp [targetRead, memory, sourceFieldAddress, CurrentValueRead.physicalAddress,
    registered, read]

theorem pointer_from_registered_cell (inventory : Inventory) (heap : Heap L)
    (address : Ptr) (value : Option Ptr) (rest : Heap L → Prop)
    (registered : inventory address = some .pointerCell)
    (owned : (PointsTo address (.ptr value) ∗ rest) heap) :
    targetRead (memory inventory heap) (CurrentValueRead.physicalAddress address) =
      some (.reference (value.map CurrentValueRead.physicalAddress)) := by
  have observed := cell_of_owned address (.ptr value) rest heap owned
  simp [targetRead, memory, CurrentValueRead.physicalAddress, registered,
    pointer?, observed, targetReadPath]

theorem pointer_from_registered_read (inventory : Inventory) (heap : Heap L)
    (address : Ptr) (value : Option Ptr)
    (registered : inventory address = some .pointerCell)
    (observed : cell? heap address = some (.ptr value)) :
    targetRead (memory inventory heap) (CurrentValueRead.physicalAddress address) =
      some (.reference (value.map CurrentValueRead.physicalAddress)) := by
  simp [targetRead, memory, CurrentValueRead.physicalAddress, registered,
    pointer?, observed, targetReadPath]


end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

end PhysicalAtomPrograms

section PhysicalAtomLiveness

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps (TargetMemory targetRead targetReadPath sourceFieldAddress)

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- This check reads the current block header. Inventory membership alone
neither revives a dead allocation nor extends its lifetime across a reset. -/
def liveAt? (heap : Heap L) (pointer : Ptr) : Bool :=
  match (heap pointer.block).1 with
  | .own header => header.live && decide (pointer.offset < header.size)
  | _ => false

/-- Direct active-arm observations are admitted only before forwarding. The
forwarding sentinel is a uint32 value in arena_id, not an Atom tag. -/
def unforwarded? (heap : Heap L) (atom : Ptr) : Bool :=
  (word? heap (atom + 4)).any (fun arena => arena != (4294967295 : UInt32))

/-- Filter the existing registration inventory by actual lifetime and
forwarding storage. This is an observer guard, not a second recursive reader.
Following a forwarded atom remains the native symbol helper's obligation. -/
def liveInventory (inventory : Inventory) (heap : Heap L) : Inventory := fun pointer =>
  if liveAt? heap pointer then
    match inventory pointer with
    | some .atom => if unforwarded? heap pointer then some .atom else none
    | other => other
  else none

def liveMemory (inventory : Inventory) (heap : Heap L) : TargetMemory :=
  memory (liveInventory inventory heap) heap

theorem liveInventory_atom_iff (inventory : Inventory) (heap : Heap L) (atom : Ptr) :
    liveInventory inventory heap atom = some .atom ↔
      liveAt? heap atom = true ∧ inventory atom = some .atom ∧ unforwarded? heap atom = true := by
  unfold liveInventory
  cases live : liveAt? heap atom <;> simp only [Bool.false_eq_true,
    ↓reduceIte, false_and, true_and]
  · simp
  · cases registered : inventory atom with
    | none => simp
    | some kind => cases kind <;> cases unforwarded? heap atom <;> simp

theorem liveInventory_pointer_iff (inventory : Inventory) (heap : Heap L) (pointer : Ptr) :
    liveInventory inventory heap pointer = some .pointerCell ↔
      liveAt? heap pointer = true ∧ inventory pointer = some .pointerCell := by
  unfold liveInventory
  cases live : liveAt? heap pointer <;> simp only [Bool.false_eq_true,
    ↓reduceIte, false_and, true_and]
  · simp
  · cases registered : inventory pointer with
    | none => simp
    | some kind => cases kind <;> simp

theorem unforwarded_of_actual_arena (heap : Heap L) (atom : Ptr) (arena : UInt32)
    (read : word? heap (atom + 4) = some arena) (ordinary : arena ≠ 4294967295) :
    unforwarded? heap atom = true := by
  simp [unforwarded?, read, ordinary]

theorem forwarded_is_not_admitted (inventory : Inventory) (heap : Heap L) (atom : Ptr)
    (registered : inventory atom = some .atom)
    (forwarded : word? heap (atom + 4) = some 4294967295) :
    liveInventory inventory heap atom = none := by
  simp [liveInventory, registered, unforwarded?, forwarded]

theorem dead_or_absent_is_not_admitted (inventory : Inventory) (heap : Heap L) (pointer : Ptr)
    (dead : liveAt? heap pointer = false) : liveInventory inventory heap pointer = none := by
  simp [liveInventory, dead]


end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

end PhysicalAtomLiveness


/-! ## Native symbol forwarding

The parsed helper follows actual arena and forwarding-arm cells. The finite
path describes owned storage, not an assumed helper result. -/

section NativeSymbolForward

set_option maxHeartbeats 600000
set_option maxRecDepth 12000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolForward

open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

abbrev Context := ObjectBindings.Context

abbrev atomType := PhysicalAtoms.atomType
abbrev atomPointerType := PhysicalAtoms.atomPointerType
abbrev wordType := PhysicalAtoms.wordType
abbrev layout := PhysicalAtoms.atomLayout

/-- Pointer locals and pointer-array strides use the same admitted profile.
The record inventory keeps scalar assignment distinct from by-value copying. -/
def profile : ObjectBindings.Profile := PhysicalAtoms.profile

def scalar (value : CVal) : Option ObjectBindings.Binding :=
  some (.scalar atomPointerType (some value))

def context (outer : Context) (atom : Option Ptr) : Context :=
  Function.update outer "atom".toList (scalar (.ptr atom))

def names (current : Context) : NameReads := fun name =>
  if name = "ATOM_ARENA_ID_FORWARDED".toList then pure (.u32 4294967295)
  else localOrLocated (ObjectBindings.values current) (ObjectBindings.declared current)
    profile.locations name

def read (fallback : Layout) (current : Context) (operand : CExpr) : CProg CVal CVal :=
  expressionWithNames (names current) noCalls fallback operand
    (ObjectBindings.objects profile current)

def services : ScopedServices Context :=
  { ObjectBindings.services profile (fun _ _ _ => CProg.undefined)
      (fun _ _ _ => CProg.undefined) with read := read, physicalWhile := true }

def atomOperand : CExpr := .identifier "atom".toList
def arenaOperand : CExpr := .field atomOperand "arena_id".toList true
def nextOperand : CExpr := .field atomOperand "name_key".toList true
def condition : CExpr := .binary .and atomOperand
  (.binary .eq arenaOperand (.identifier "ATOM_ARENA_ID_FORWARDED".toList))
def iteration : List CStatement := [.assign atomOperand nextOperand]
def body : List CStatement := [.whileLoop condition iteration, .return (some atomOperand)]

private def piece0 : String × List Token := ("{\n    ", [.punctuation ['{']])
private def piece1 : String × List Token := ("while ", [.identifier "while".toList])
private def piece2 : String × List Token := ("(atom ", [.punctuation ['('], .identifier "atom".toList])
private def piece3 : String × List Token := ("&& ", [.punctuation ['&', '&']])
private def piece4 : String × List Token := ("atom->arena_id ",
  [.identifier "atom".toList, .punctuation ['-', '>'], .identifier "arena_id".toList])
private def piece5 : String × List Token := ("== ", [.punctuation ['=', '=']])
private def piece6 : String × List Token := ("ATOM_ARENA_ID_FORWARDED)\n        ",
  [.identifier "ATOM_ARENA_ID_FORWARDED".toList, .punctuation [')']])
private def piece7 : String × List Token := ("atom = ", [.identifier "atom".toList, .punctuation ['=']])
private def piece8 : String × List Token := ("atom->name_key;\n    ",
  [.identifier "atom".toList, .punctuation ['-', '>'], .identifier "name_key".toList,
   .punctuation [';']])
private def piece9 : String × List Token := ("return ", [.identifier "return".toList])
private def piece10 : String × List Token := ("atom;\n}",
  [.identifier "atom".toList, .punctuation [';'], .punctuation ['}']])

private theorem piece0_lex : piece0.1.toList.foldl step initial = completed piece0.2 := by decide +kernel
private theorem piece1_lex : piece1.1.toList.foldl step initial = completed piece1.2 := by decide +kernel
private theorem piece2_lex : piece2.1.toList.foldl step initial = completed piece2.2 := by decide +kernel
private theorem piece3_lex : piece3.1.toList.foldl step initial = completed piece3.2 := by decide +kernel
private theorem piece4_lex : piece4.1.toList.foldl step initial = completed piece4.2 := by decide +kernel
private theorem piece5_lex : piece5.1.toList.foldl step initial = completed piece5.2 := by decide +kernel
private theorem piece6_lex : piece6.1.toList.foldl step initial = completed piece6.2 := by decide +kernel
private theorem piece7_lex : piece7.1.toList.foldl step initial = completed piece7.2 := by decide +kernel
private theorem piece8_lex : piece8.1.toList.foldl step initial = completed piece8.2 := by decide +kernel
private theorem piece9_lex : piece9.1.toList.foldl step initial = completed piece9.2 := by decide +kernel
private theorem piece10_lex : piece10.1.toList.foldl step initial = completed piece10.2 := by decide +kernel

private def pieces : List (String × List Token) :=
  [piece0, piece1, piece2, piece3, piece4, piece5, piece6, piece7, piece8, piece9, piece10]
def source : String := String.join (pieces.map Prod.fst)
def tokens : List Token := pieces.flatMap Prod.snd

theorem actual_body_lexed : lex source.toList = .ok tokens := by
  apply lex_completed_string_pieces
  simp only [pieces, List.forall_cons]
  exact ⟨piece0_lex, piece1_lex, piece2_lex, piece3_lex, piece4_lex, piece5_lex,
    piece6_lex, piece7_lex, piece8_lex, piece9_lex, piece10_lex, trivial⟩

theorem actual_body_parsed : blockText? [] source.toList = some body := by
  exact block_text_of_parts [] _ tokens _ actual_body_lexed (by rfl)

theorem current_atom_read (outer : Context) (atom : Option Ptr) :
    read layout (context outer atom) atomOperand = pure (.ptr atom) := by
  rfl

def readArena (atom : Option Ptr) : CProg CVal UInt32 := match atom with
  | none => CProg.undefined
  | some pointer => CProg.loadU32 (pointer + 4)

def test (atom : Option Ptr) : CProg CVal Bool := do
  let isNull ← CProg.ptrEq atom none
  if !isNull then do
    let arena ← readArena atom
    pure (arena == 4294967295)
  else pure false

def next (atom : Option Ptr) : CProg CVal (Option Ptr) := match atom with
  | none => CProg.undefined
  | some pointer => CProg.loadPtr (pointer + 5)

theorem arena_operand_uses_current_pointer (outer : Context) (atom : Ptr) :
    read layout (context outer (some atom)) arenaOperand =
      (CProg.loadU32 (atom + 4) >>= fun arena => pure (.u32 arena)) := by
  rfl

theorem next_operand_uses_current_pointer (outer : Context) (atom : Ptr) :
    ObjectBindings.read profile layout (context outer (some atom)) nextOperand =
      (CProg.loadPtr (atom + 5) >>= fun selected => pure (.ptr selected)) := by
  rfl

theorem next_operand_nullable (outer : Context) (atom : Option Ptr) :
    ObjectBindings.read profile layout (context outer atom) nextOperand =
      (next atom >>= fun selected => pure (.ptr selected)) := by
  cases atom with
  | none => exact (undefined_bind _).symm
  | some pointer => exact next_operand_uses_current_pointer outer pointer

theorem arena_operand_nullable (outer : Context) (atom : Option Ptr) :
    read layout (context outer atom) arenaOperand =
      (readArena atom >>= fun arena => pure (.u32 arena)) := by
  cases atom with
  | none => exact (undefined_bind _).symm
  | some pointer => exact arena_operand_uses_current_pointer outer pointer

theorem actual_guard (outer : Context) (atom : Option Ptr) :
    (services.read layout (context outer atom) condition >>= truth) = test atom := by
  have comparison : read layout (context outer atom)
      (.binary .eq arenaOperand (.identifier "ATOM_ARENA_ID_FORWARDED".toList)) =
      (readArena atom >>= fun arena => pure (.bool (arena == 4294967295))) := by
    change (read layout (context outer atom) arenaOperand >>= fun arena =>
      pure (CVal.u32 4294967295) >>= fun constant => binary .eq arena constant) = _
    rw [arena_operand_nullable]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    congr 1
  change ((read layout (context outer atom) atomOperand >>= fun first =>
    truth first >>= fun selected => if selected then do
      let compared ← read layout (context outer atom)
        (.binary .eq arenaOperand (.identifier "ATOM_ARENA_ID_FORWARDED".toList))
      let second ← truth compared
      pure (CVal.bool second)
    else pure (CVal.bool false)) >>= truth) = test atom
  rw [current_atom_read, comparison]
  simp only [truth, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  unfold test
  simp only [Prog.bind_eq]
  congr 1
  funext isNull
  cases isNull with
  | true => rfl
  | false =>
      simp only [Bool.not_false, ↓reduceIte, Prog.bind_assoc]
      congr 1

theorem assignment_keeps_other_locals (outer : Context) (atom : Option Ptr) :
    services.assignment layout (context outer atom) (.assign atomOperand nextOperand) =
      (next atom >>= fun selected => pure (context outer selected)) := by
  change ObjectBindings.assignment profile layout (context outer atom)
    (.assign atomOperand nextOperand) = _
  unfold ObjectBindings.assignment
  dsimp only
  have typed : ScalarBytes.typeOf?
      (ObjectBindings.types (context outer atom) profile.outsideTypes)
      atomOperand profile.fieldTypes = some atomPointerType := by
    rfl
  rw [typed]
  change (ObjectBindings.read profile layout (context outer atom) nextOperand >>= fun value =>
    ObjectBindings.writeValue profile layout (context outer atom) atomOperand value) = _
  rw [next_operand_nullable]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext selected
  change ObjectBindings.writeValue profile layout (context outer atom)
    (.identifier "atom".toList) (.ptr selected) = _
  rw [ObjectBindings.local_scalar_write_refines_existing_inventory profile layout
    (context outer atom) "atom".toList atomPointerType
    (some (.ptr atom)) (.ptr selected) (by simp [context, scalar])]
  change (pure (Function.update (context outer atom) "atom".toList
    (scalar (.ptr selected))) : CProg CVal Context) = pure (context outer selected)
  have updated : Function.update (context outer atom) "atom".toList
      (scalar (.ptr selected)) = context outer selected := by
    exact Function.update_idem _ _ _
  rw [updated]

def step (atom : Option Ptr) : CProg CVal (ReadBlock.Result (Option Ptr)) := do
  let selected ← next atom
  pure (.finished (.next selected))

def traversal (allowance : Nat) (atom : Option Ptr) : CProg CVal (ReadBlock.Result (Option Ptr)) :=
  ReadBlock.whileWith test step allowance atom

theorem actual_iteration (outer : Context) (atom : Option Ptr) (allowance : Nat) :
    executeScopedWith services layout allowance 1 (context outer atom) iteration =
      (step atom >>= fun result => pure (result.mapContext (context outer))) := by
  change (services.assignment layout (context outer atom)
    (.assign atomOperand nextOperand) >>= fun updated =>
      pure (ReadBlock.Result.finished (ReadBlock.Flow.next updated))) = _
  rw [assignment_keeps_other_locals]
  simp only [step, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext]

theorem actual_loop (outer : Context) (atom : Option Ptr) (allowance : Nat) :
    ReadBlock.whileWith
      (fun current => services.read layout current condition >>= truth)
      (fun current => executeScopedWith services layout allowance 1 current iteration)
      allowance (context outer atom) =
      (traversal allowance atom >>= fun result => pure (result.mapContext (context outer))) :=
  ReadBlock.while_context_extension (context outer) test step _ _
    (actual_guard outer) (fun atom => actual_iteration outer atom allowance) allowance atom

def program (outer : Context) (allowance : Nat) (atom : Option Ptr) :
    CProg CVal (ReadBlock.Result Context) :=
  executeScopedWith services layout allowance 2 (context outer atom) body

def operations (outer : Context) (allowance : Nat) (atom : Option Ptr) :
    CProg CVal (ReadBlock.Result Context) := do
  let result ← traversal allowance atom
  match result with
  | .finished (.next final) =>
      pure (.finished (.returned (context outer final) (some (.ptr final))))
  | other => pure (other.mapContext (context outer))

/-- The source body retains its physical guard and pointer reads, even when
paused or out of loop allowance. No forwarded pointer is interpreted as an
ordinary symbol's active union arm. -/
theorem actual_body_uses_memory_operations (outer : Context) (allowance : Nat)
    (atom : Option Ptr) : program outer allowance atom = operations outer allowance atom := by
  unfold program body
  rw [scoped_while_keeps_guard_body_and_continuation _ _ _ _ _ _ _ _ rfl,
    actual_loop]
  unfold operations
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext result
  cases result with
  | exhausted => rfl
  | finished flow =>
      cases flow with
      | next final =>
          change (read layout (context outer final) atomOperand >>= fun value =>
            pure (ReadBlock.Result.finished
              (ReadBlock.Flow.returned (context outer final) (some value)))) = _
          rw [current_atom_read]
          rfl
      | broken final => rfl
      | returned final value => rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolForward


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolForward

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- A finite physical forwarding path. Each edge cites the actual live
pointer, arena tag and active forwarding arm in one unchanged heap. The
terminal node is null or has a non-forwarded arena tag. -/
inductive ForwardPath (heap : Heap L) : Option Ptr → Option Ptr → Nat → Prop where
  | null : ForwardPath heap none none 0
  | stop (pointer : Ptr) (arena : UInt32) (valid : Valid heap pointer)
      (tag : Reads (pointer + 4) (.u32 arena) heap)
      (ordinary : arena ≠ 4294967295) :
      ForwardPath heap (some pointer) (some pointer) 0
  | edge (pointer : Ptr) (next terminal : Option Ptr) (length : Nat)
      (valid : Valid heap pointer)
      (tag : Reads (pointer + 4) (.u32 4294967295) heap)
      (forward : Reads (pointer + 5) (.ptr next) heap)
      (suffix : ForwardPath heap next terminal length) :
      ForwardPath heap (some pointer) terminal (length + 1)

private theorem load_word_wp (heap : Heap L) (pointer : Ptr) (value : UInt32)
    (held : Reads pointer (.u32 value) heap) (post : UInt32 → Heap L → Prop)
    (after : post value heap) : (CProg.loadU32 pointer).wp act post heap := by
  refine wp_consequence act
    (loadU32_rule (P := fun reached => reached = heap) (n := value) ?_) rfl ?_
  · intro reached equal
    subst reached
    exact held
  · rintro _ _ ⟨rfl, rfl⟩
    exact after

private theorem load_pointer_wp (heap : Heap L) (pointer : Ptr) (value : Option Ptr)
    (held : Reads pointer (.ptr value) heap) (post : Option Ptr → Heap L → Prop)
    (after : post value heap) : (CProg.loadPtr pointer).wp act post heap := by
  refine wp_consequence act
    (loadPtr_rule (P := fun reached => reached = heap) (q := value) ?_) rfl ?_
  · intro reached equal
    subst reached
    exact held
  · rintro _ _ ⟨rfl, rfl⟩
    exact after

theorem test_null_wp (heap : Heap L) (post : Bool → Heap L → Prop)
    (after : post false heap) : (test none).wp act post heap := by
  unfold test
  rw [wp_bind']
  apply wp_ptrEq (p := none) (q := none) (σ := heap) trivial trivial
  simpa only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, wp_pure]
    using after

theorem test_some_wp (heap : Heap L) (pointer : Ptr) (arena : UInt32)
    (valid : Valid heap pointer) (tag : Reads (pointer + 4) (.u32 arena) heap)
    (post : Bool → Heap L → Prop) (after : post (arena == 4294967295) heap) :
    (test (some pointer)).wp act post heap := by
  unfold test
  rw [wp_bind']
  apply wp_ptrEq (p := some pointer) (q := none) (σ := heap) valid trivial
  simp only [reduceCtorEq, decide_false, Bool.not_false, ↓reduceIte]
  change (CProg.loadU32 (pointer + 4) >>= fun tag => pure (tag == 4294967295)).wp
    act post heap
  rw [wp_bind']
  exact load_word_wp heap (pointer + 4) arena tag _ (by simpa only [wp_pure] using after)

/-- Sufficient iteration allowance completes exactly the independently given
physical path. Every guard and pointer read remains in the operation tree;
the entire heap is preserved, including unobserved cells and ownership. -/
theorem traversal_path_wp (heap : Heap L) {start terminal : Option Ptr} {length : Nat}
    (path : ForwardPath heap start terminal length) (allowance : Nat)
    (enough : length ≤ allowance)
    (post : ReadBlock.Result (Option Ptr) → Heap L → Prop)
    (after : post (.finished (.next terminal)) heap) :
    (traversal allowance start).wp act post heap := by
  induction path generalizing allowance with
  | null =>
      change (ReadBlock.whileWith test step allowance none).wp act post heap
      rw [ReadBlock.whileWith.eq_def, wp_bind']
      apply test_null_wp heap
      simpa only [Bool.false_eq_true, ↓reduceIte, wp_pure] using after
  | stop pointer arena valid tag ordinary =>
      change (ReadBlock.whileWith test step allowance (some pointer)).wp act post heap
      rw [ReadBlock.whileWith.eq_def, wp_bind']
      apply test_some_wp heap pointer arena valid tag
      have differs : (arena == 4294967295) = false := beq_eq_false_iff_ne.mpr ordinary
      simpa only [differs, Bool.false_eq_true, ↓reduceIte, wp_pure] using after
  | edge pointer next terminal length valid tag forward suffix ih =>
      cases allowance with
      | zero => omega
      | succ allowance =>
          change (ReadBlock.whileWith test step (allowance + 1) (some pointer)).wp act post heap
          rw [ReadBlock.whileWith.eq_def, wp_bind']
          apply test_some_wp heap pointer 4294967295 valid tag
          simp only [beq_self_eq_true, ↓reduceIte, wp_bind']
          change (CProg.loadPtr (pointer + 5) >>= fun selected =>
            pure (ReadBlock.Result.finished (ReadBlock.Flow.next selected))).wp act _ heap
          rw [wp_bind']
          apply load_pointer_wp heap (pointer + 5) next forward
          simpa only [wp_pure, traversal] using ih allowance (by omega) after

theorem traversal_path_owned (start terminal : Option Ptr) (length allowance : Nat)
    (enough : length ≤ allowance) :
    CTriple (fun heap : Heap L => ForwardPath heap start terminal length)
      (traversal allowance start)
      (fun result heap => result = .finished (.next terminal) ∧
        ForwardPath heap start terminal length) := by
  intro heap path
  exact traversal_path_wp heap path allowance enough _ ⟨rfl, path⟩

theorem actual_body_path_owned (outer : Context) (start terminal : Option Ptr)
    (length allowance : Nat) (enough : length ≤ allowance) :
    CTriple (fun heap : Heap L => ForwardPath heap start terminal length)
      (program outer allowance start)
      (fun result heap => result = .finished (.returned (context outer terminal)
          (some (.ptr terminal))) ∧ ForwardPath heap start terminal length) := by
  rw [actual_body_uses_memory_operations]
  intro heap path
  change (operations outer allowance start).wp act
    (fun result reached => result = .finished (.returned (context outer terminal)
      (some (.ptr terminal))) ∧ ForwardPath reached start terminal length) heap
  unfold operations
  rw [wp_bind']
  apply traversal_path_wp heap path allowance enough
  simpa only [wp_pure, eq_self_iff_true, true_and] using path

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolForward


end NativeSymbolForward


section ManagedNativeSpellingStorage
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps
open CellPermission

variable {L : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem spelling_record_from_inventory (inventory : Inventory) (heap : Heap L) (spelling : Ptr)
    (registered : inventory spelling = some .spelling) :
    targetRead (memory inventory heap) (CurrentValueRead.physicalAddress spelling) =
      spellingRecord? heap spelling := by
  simp [targetRead, memory, CurrentValueRead.physicalAddress, registered, targetReadPath]

theorem spelling_record_owned (spelling : Ptr) (length : UInt32) (rest : Heap L → Prop)
    (heap : Heap L) (held : (PointsTo (spelling + 1) (.u32 length) ∗ rest) heap) :
    spellingRecord? heap spelling = some (spellingRecord spelling length) := by
  have read := cell_of_owned (spelling + 1) (.u32 length) rest heap held
  simp [spellingRecord?, word?, read]

theorem byte_at_from_inventory (inventory : Inventory) (heap : Heap L) (pointer : Ptr)
    (value : UInt8) (registered : inventory pointer = some .byteCell)
    (read : byte? heap pointer = some value) :
    ByteViews.targetAt (memory inventory heap) (CurrentValueRead.physicalAddress pointer) =
      some value := by
  simp [ByteViews.targetAt, targetRead, memory, CurrentValueRead.physicalAddress,
    registered, read, targetReadPath]

theorem byte_at_from_owned (inventory : Inventory) (heap : Heap L) (pointer : Ptr)
    (value : UInt8) (registered : inventory pointer = some .byteCell)
    (rest : Heap L → Prop) (held : (PointsTo pointer (.u8 value) ∗ rest) heap) :
    ByteViews.targetAt (memory inventory heap) (CurrentValueRead.physicalAddress pointer) =
      some value := by
  apply byte_at_from_inventory inventory heap pointer value registered
  simp [byte?, cell_of_owned pointer (.u8 value) rest heap held]

theorem advance_physical_address (pointer : Ptr) :
    ByteViews.advance (CurrentValueRead.physicalAddress pointer) =
      CurrentValueRead.physicalAddress (pointer + 1) := rfl

/-- The existing byte view reads every initialized byte in order. The
registration and owned storage are explicit; no value or UTF-8 oracle is used. -/
theorem byte_block_from_owned (inventory : Inventory) (heap : Heap L) (pointer : Ptr)
    (bytes : List UInt8) (rest : Heap L → Prop)
    (registered : ∀ index, index < bytes.length → inventory (pointer + index) = some .byteCell)
    (held : (Cells pointer (bytes.map (fun byte => some (CVal.u8 byte))) ∗ rest) heap) :
    ByteViews.targetBlock (memory inventory heap) (CurrentValueRead.physicalAddress pointer)
      bytes.length = some bytes := by
  induction bytes generalizing pointer rest with
  | nil => rfl
  | cons byte bytes ih =>
      have head : ByteViews.targetAt (memory inventory heap)
          (CurrentValueRead.physicalAddress pointer) = some byte := by
        refine byte_at_from_owned inventory heap pointer byte ?_
          (Cells (pointer + 1) (bytes.map (fun value => some (CVal.u8 value))) ∗ rest) ?_
        · simpa only [ptr_add_zero] using registered 0 (by simp)
        · have split := held
          rw [List.map_cons, cells_cons, sepConj_assoc] at split
          exact split
      have tailRegistered : ∀ index, index < bytes.length →
          inventory ((pointer + 1) + index) = some .byteCell := by
        intro index within
        simpa only [Ptr.add_add, Nat.add_comm 1 index] using registered (index + 1) (by simpa using within)
      have tailHeld : (Cells (pointer + 1) (bytes.map (fun value => some (CVal.u8 value))) ∗
          (PointsTo pointer (.u8 byte) ∗ rest)) heap := by
        have split : (PointsTo pointer (.u8 byte) ∗
            Cells (pointer + 1) (bytes.map (fun value => some (CVal.u8 value))) ∗ rest) heap := by
          have split := held
          rw [List.map_cons, cells_cons, sepConj_assoc] at split
          exact split
        cmem_exact
      simp only [List.length_cons, ByteViews.targetBlock, head, advance_physical_address,
        ih (pointer + 1) (PointsTo pointer (.u8 byte) ∗ rest) tailRegistered tailHeld]

/-- Materialize the already selected explicit-length byte range through the
shared memory primitives. This is the observer's read, not a second C evaluator. -/
def byteContents (pointer : Ptr) (length : Nat) : CProg CVal (List UInt8) := do
  let values ← CProg.loadCells pointer length
  values.mapM ReadExpressions.byte

theorem byte_values_preserve_all_bits (bytes : List UInt8) :
    (bytes.map CVal.u8).mapM ReadExpressions.byte =
      (pure bytes : CProg CVal (List UInt8)) := by
  induction bytes with
  | nil => rfl
  | cons first bytes ih =>
      simp only [List.map_cons, List.mapM_cons, ReadExpressions.byte, ih,
        Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]

theorem byte_contents_owned (pointer : Ptr) (bytes : List UInt8) :
    CTriple (L := L) (Cells pointer (bytes.map (fun byte => some (CVal.u8 byte))))
      (byteContents pointer bytes.length)
      (fun actual heap => actual = bytes ∧
        Cells pointer (bytes.map (fun byte => some (CVal.u8 byte))) heap) := by
  unfold byteContents
  have cells := load_cells (L := L) pointer (bytes.map CVal.u8)
  simp only [List.length_map, List.map_map] at cells
  refine triple_bind _ cells fun values => ?_
  apply triple_pure
  intro same
  subst values
  rw [byte_values_preserve_all_bits]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ bytes _)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.PhysicalAtoms

end ManagedNativeSpellingStorage


section ManagedNativeSymbolHelpers
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolSpelling

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions

/-- Logical-cell descriptors for the selected native fields. A byte buffer
is an embedded array; it is not a pointer stored in its first byte. -/
def layout : Layout := fun name =>
  if name = "kind".toList then some ⟨0, .word⟩
  else if name = "symbol_number".toList then some ⟨3, .word⟩
  else if name = "spelling".toList then some ⟨5, .pointer⟩
  else if name = "len".toList then some ⟨1, .word⟩
  else if name = "bytes".toList then some ⟨2, .embedded⟩ else none

def names (atom : Option Ptr) : NameReads := fun name =>
  if name = "atom".toList then pure (.ptr atom)
  else if name = "ATOM_SYMBOL".toList ∨ name = "SYMBOL_ID_NONE".toList then pure (.u32 0)
  else CProg.undefined

def atomOperand : CExpr := .identifier "atom".toList
def kindOperand : CExpr := .field atomOperand "kind".toList true
def numberOperand : CExpr := .field atomOperand "symbol_number".toList true
def spellingOperand : CExpr := .field atomOperand "spelling".toList true
def bytesOperand : CExpr := .field spellingOperand "bytes".toList true
def lengthOperand : CExpr := .field spellingOperand "len".toList true

def kindGuard : CExpr := .binary .eq kindOperand (.identifier "ATOM_SYMBOL".toList)
def numberGuard : CExpr := .binary .eq numberOperand (.identifier "SYMBOL_ID_NONE".toList)
def spellingGuard : CExpr := .binary .ne spellingOperand .null

def condition : CExpr := .binary .and
  (.binary .and (.binary .and atomOperand kindGuard) numberGuard) spellingGuard

/-- Array decay is admitted only for the actual bytes member in this
selected source expression; inactive payload arms are never guessed. -/
def objects : ObjectReads where
  arrayField := fun _ through name => through && name == "bytes".toList

def read (atom : Option Ptr) (operand : CExpr) : CProg CVal CVal :=
  expressionWithNames (names atom) noCalls layout operand objects

def readWord (atom : Option Ptr) (offset : Nat) : CProg CVal UInt32 := match atom with
  | none => CProg.undefined
  | some atom => CProg.loadU32 (atom + offset)

def readSpelling (atom : Option Ptr) : CProg CVal (Option Ptr) := match atom with
  | none => CProg.undefined
  | some atom => CProg.loadPtr (atom + 5)

def test (atom : Option Ptr) : CProg CVal Bool := do
  let isNull ← CProg.ptrEq atom none
  if !isNull then do
    let kind ← readWord atom 0
    if kind == 0 then do
      let number ← readWord atom 3
      if number == 0 then do
        let spelling ← readSpelling atom
        let isNull ← CProg.ptrEq spelling none
        pure (!isNull)
      else pure false
    else pure false
  else pure false

/-- The two returned members are still read from the selected spelling
pointer; no logical string or byte payload is passed to these operations. -/
def bytes (atom : Option Ptr) : CProg CVal (Option Ptr) := do
  let spelling ← readSpelling atom
  match spelling with
  | none => CProg.undefined
  | some spelling => pure (some (spelling + 2))

def length (atom : Option Ptr) : CProg CVal UInt32 := do
  let spelling ← readSpelling atom
  match spelling with
  | none => CProg.undefined
  | some spelling => CProg.loadU32 (spelling + 1)

theorem current_atom_is_parameter (atom : Option Ptr) :
    read atom atomOperand = pure (.ptr atom) := rfl

theorem kind_uses_current_field (atom : Option Ptr) :
    read atom kindOperand = (readWord atom 0 >>= fun value => pure (.u32 value)) := by
  cases atom with
  | none => exact (undefined_bind _).symm
  | some atom => rfl

theorem number_uses_current_field (atom : Option Ptr) :
    read atom numberOperand = (readWord atom 3 >>= fun value => pure (.u32 value)) := by
  cases atom with
  | none => exact (undefined_bind _).symm
  | some atom => rfl

theorem spelling_uses_current_field (atom : Option Ptr) :
    read atom spellingOperand = (readSpelling atom >>= fun value => pure (.ptr value)) := by
  cases atom with
  | none => exact (undefined_bind _).symm
  | some atom => rfl

private theorem read_kind_guard (atom : Option Ptr) :
    read atom kindGuard = (readWord atom 0 >>= fun value => pure (.bool (value == 0))) := by
  change (read atom kindOperand >>= fun value => pure (CVal.u32 0) >>=
    fun constant => binary .eq value constant) = _
  rw [kind_uses_current_field]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1

private theorem read_number_guard (atom : Option Ptr) :
    read atom numberGuard = (readWord atom 3 >>= fun value => pure (.bool (value == 0))) := by
  change (read atom numberOperand >>= fun value => pure (CVal.u32 0) >>=
    fun constant => binary .eq value constant) = _
  rw [number_uses_current_field]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1

private theorem read_spelling_guard (atom : Option Ptr) :
    read atom spellingGuard = (readSpelling atom >>= fun spelling =>
      CProg.ptrEq spelling none >>= fun isNull => pure (.bool (!isNull))) := by
  change (read atom spellingOperand >>= fun value => pure (CVal.ptr none) >>=
    fun constant => binary .ne value constant) = _
  rw [spelling_uses_current_field]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

private theorem and_read (atom : Option Ptr) (left right : CExpr) :
    (read atom (.binary .and left right) >>= truth) =
      (do let value ← read atom left
          let selected ← truth value
          if selected then read atom right >>= truth else pure false) := by
  change ((do let value ← read atom left
              let selected ← truth value
              if selected then do
                let next ← read atom right
                let selectedNext ← truth next
                pure (CVal.bool selectedNext)
              else pure (CVal.bool false)) >>= truth) = _
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext value
  congr 1
  funext selected
  cases selected <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext next
  change (truth next).bind Prog.ret = truth next
  exact Prog.bind_ret _

theorem actual_guard_uses_current_fields (atom : Option Ptr) :
    (read atom condition >>= truth) = test atom := by
  have join (left right : CExpr) :
      Prog.bind (read atom (.binary .and left right)) truth =
        Prog.bind (read atom left) (fun value => Prog.bind (truth value)
          (fun selected => if selected then Prog.bind (read atom right) truth else pure false)) := by
    simpa only [Prog.bind_eq] using and_read atom left right
  unfold condition
  simp only [Prog.bind_eq]
  rw [join, ← Prog.bind_assoc, join, ← Prog.bind_assoc, join,
    current_atom_is_parameter, read_kind_guard, read_number_guard, read_spelling_guard]
  simp only [test, truth, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext isNull
  cases isNull with
  | true => rfl
  | false =>
      simp only [Bool.not_false, ↓reduceIte, Prog.ret_bind, Prog.bind_assoc]
      congr 1
      funext kind
      by_cases zero : (kind == 0) = true <;>
        simp [zero, Prog.bind_assoc, Prog.ret_bind]

/-- The native array member yields its address; the first byte is not
loaded as a pointer and its contents cannot select an allocation. -/
theorem actual_bytes_operand (atom : Option Ptr) :
    read atom bytesOperand = (bytes atom >>= fun value => pure (.ptr value)) := by
  change (read atom spellingOperand >>= fun selected =>
    objects.fieldRead layout spellingOperand true selected "bytes".toList) = _
  rw [spelling_uses_current_field]
  unfold bytes
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext spelling
  cases spelling with
  | none =>
      simp [ObjectReads.fieldRead, arrayFieldAddress, ObjectReads.fieldLayout,
        objects, layout, fieldAddress, resolved, pointer, Prog.bind_eq, Prog.pure_eq,
        Prog.ret_bind]
      change (CProg.undefined >>= fun address => pure (CVal.ptr (some address))) =
        (CProg.undefined >>= fun value => pure (CVal.ptr value))
      rw [undefined_bind, undefined_bind]
  | some spelling => rfl

theorem actual_length_operand (atom : Option Ptr) :
    read atom lengthOperand = (length atom >>= fun value => pure (.u32 value)) := by
  change (read atom spellingOperand >>= fun selected =>
    objects.fieldRead layout spellingOperand true selected "len".toList) = _
  rw [spelling_uses_current_field]
  unfold length
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext spelling
  cases spelling with
  | none => exact (undefined_bind _).symm
  | some spelling => rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolSpelling

end ManagedNativeSymbolHelpers


section ManagedNativeSymbolSource
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolSpelling

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

private def guardPiece0 : String × List Token := ("return atom && atom->", [.identifier "return".toList, .identifier "atom".toList, .punctuation "&&".toList, .identifier "atom".toList, .punctuation "->".toList])
private theorem guardPiece0_lex : guardPiece0.1.toList.foldl step initial = completed guardPiece0.2 := by decide +kernel

private def guardPiece1 : String × List Token := ("kind == ATOM_SYMBOL ", [.identifier "kind".toList, .punctuation "==".toList, .identifier "ATOM_SYMBOL".toList])
private theorem guardPiece1_lex : guardPiece1.1.toList.foldl step initial = completed guardPiece1.2 := by decide +kernel

private def guardPiece2 : String × List Token := ("&&\n           atom->", [.punctuation "&&".toList, .identifier "atom".toList, .punctuation "->".toList])
private theorem guardPiece2_lex : guardPiece2.1.toList.foldl step initial = completed guardPiece2.2 := by decide +kernel

private def guardPiece3 : String × List Token := ("symbol_number == SYMBOL_ID_NONE ", [.identifier "symbol_number".toList, .punctuation "==".toList, .identifier "SYMBOL_ID_NONE".toList])
private theorem guardPiece3_lex : guardPiece3.1.toList.foldl step initial = completed guardPiece3.2 := by decide +kernel

private def guardPiece4 : String × List Token := ("&& atom->spelling ", [.punctuation "&&".toList, .identifier "atom".toList, .punctuation "->".toList, .identifier "spelling".toList])
private theorem guardPiece4_lex : guardPiece4.1.toList.foldl step initial = completed guardPiece4.2 := by decide +kernel

private def guardPiece5 : String × List Token := ("!= NULL;", [.punctuation "!=".toList, .identifier "NULL".toList, .punctuation ";".toList])
private theorem guardPiece5_lex : guardPiece5.1.toList.foldl step initial = completed guardPiece5.2 := by decide +kernel

private def guardPieces : List (String × List Token) := [guardPiece0, guardPiece1, guardPiece2, guardPiece3, guardPiece4, guardPiece5]
def guardSource : String := String.join (guardPieces.map Prod.fst)
def guardTokens : List Token := guardPieces.flatMap Prod.snd

theorem guard_source_lexed : lex guardSource.toList = .ok guardTokens := by
  apply lex_completed_string_pieces
  simp only [guardPieces, List.forall_cons]
  exact ⟨guardPiece0_lex, guardPiece1_lex, guardPiece2_lex, guardPiece3_lex, guardPiece4_lex, guardPiece5_lex, trivial⟩

theorem guard_source_parsed : statement? 80 [] guardTokens = some (.return (some condition), []) := by rfl

def bytesSource : String := "atom->spelling->bytes"
def bytesTokens : List Token := [.identifier "atom".toList, .punctuation "->".toList, .identifier "spelling".toList, .punctuation "->".toList, .identifier "bytes".toList]
theorem bytes_source_lexed : lex bytesSource.toList = .ok bytesTokens := by decide +kernel
theorem bytes_source_parsed : expressionText? [] bytesSource.toList = some bytesOperand := by
  unfold expressionText?
  rw [bytes_source_lexed]
  rfl

def lengthSource : String := "atom->spelling->len"
def lengthTokens : List Token := [.identifier "atom".toList, .punctuation "->".toList, .identifier "spelling".toList, .punctuation "->".toList, .identifier "len".toList]
theorem length_source_lexed : lex lengthSource.toList = .ok lengthTokens := by decide +kernel
theorem length_source_parsed : expressionText? [] lengthSource.toList = some lengthOperand := by
  unfold expressionText?
  rw [length_source_lexed]
  rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolSpelling

end ManagedNativeSymbolSource


section ManagedNativeSymbolOwned
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolSpelling

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open CellPermission
open ReadExpressions


universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem test_spelled_wp (heap : Heap L) (atom spelling : Ptr)
    (live : Valid heap atom) (spellingLive : Valid heap spelling)
    (kind : Reads atom (.u32 0) heap)
    (number : Reads (atom + 3) (.u32 0) heap)
    (stored : Reads (atom + 5) (.ptr (some spelling)) heap)
    (post : Bool → Heap L → Prop) (after : post true heap) :
    (test (some atom)).wp act post heap := by
  unfold test
  rw [wp_bind']
  apply wp_ptrEq (p := some atom) (q := none) (σ := heap) live trivial
  simp only [reduceCtorEq, decide_false, Bool.not_false, ↓reduceIte]
  change (CProg.loadU32 (atom + 0) >>= fun value =>
    if (value == 0) then do
      let number ← readWord (some atom) 3
      if number == 0 then do
        let value ← readSpelling (some atom)
        let isNull ← CProg.ptrEq value none
        pure (!isNull)
      else pure false
    else pure false).wp act post heap
  rw [wp_bind']
  apply SymbolForward.load_word_wp heap (atom + 0) 0 (by simpa only [ptr_add_zero] using kind)
  simp only [beq_self_eq_true, ↓reduceIte]
  change (CProg.loadU32 (atom + 3) >>= fun value =>
    if (value == 0) then do
      let value ← readSpelling (some atom)
      let isNull ← CProg.ptrEq value none
      pure (!isNull)
    else pure false).wp act post heap
  rw [wp_bind']
  apply SymbolForward.load_word_wp heap (atom + 3) 0 number
  simp only [beq_self_eq_true, ↓reduceIte]
  change (CProg.loadPtr (atom + 5) >>= fun value => CProg.ptrEq value none >>=
    fun isNull => pure (!isNull)).wp act post heap
  rw [wp_bind']
  apply SymbolForward.load_pointer_wp heap (atom + 5) (some spelling) stored
  rw [wp_bind']
  apply wp_ptrEq (p := some spelling) (q := none) (σ := heap) spellingLive trivial
  simpa only [reduceCtorEq, decide_false, Bool.not_false, wp_pure] using after

theorem bytes_spelled_wp (heap : Heap L) (atom spelling : Ptr)
    (stored : Reads (atom + 5) (.ptr (some spelling)) heap)
    (post : Option Ptr → Heap L → Prop) (after : post (some (spelling + 2)) heap) :
    (bytes (some atom)).wp act post heap := by
  unfold bytes readSpelling
  rw [wp_bind']
  apply SymbolForward.load_pointer_wp heap (atom + 5) (some spelling) stored
  simpa only [wp_pure] using after

theorem length_spelled_wp (heap : Heap L) (atom spelling : Ptr) (count : UInt32)
    (stored : Reads (atom + 5) (.ptr (some spelling)) heap)
    (header : Reads (spelling + 1) (.u32 count) heap)
    (post : UInt32 → Heap L → Prop) (after : post count heap) :
    (length (some atom)).wp act post heap := by
  unfold length readSpelling
  rw [wp_bind']
  apply SymbolForward.load_pointer_wp heap (atom + 5) (some spelling) stored
  exact SymbolForward.load_word_wp heap (spelling + 1) count header post after

/-- Selected managed-symbol field observation. It executes the native guard
before either returned member; the numbered-table alternative is separate. -/
def managedHeader (atom : Option Ptr) : CProg CVal (Option (Option Ptr × UInt32)) := do
  let managed ← test atom
  if managed then do
    let buffer ← bytes atom
    let count ← length atom
    pure (some (buffer, count))
  else pure none

theorem managedHeader_wp (heap : Heap L) (atom spelling : Ptr) (count : UInt32)
    (live : Valid heap atom) (spellingLive : Valid heap spelling)
    (kind : Reads atom (.u32 0) heap) (number : Reads (atom + 3) (.u32 0) heap)
    (stored : Reads (atom + 5) (.ptr (some spelling)) heap)
    (header : Reads (spelling + 1) (.u32 count) heap)
    (post : Option (Option Ptr × UInt32) → Heap L → Prop)
    (after : post (some (some (spelling + 2), count)) heap) :
    (managedHeader (some atom)).wp act post heap := by
  unfold managedHeader
  rw [wp_bind']
  apply test_spelled_wp heap atom spelling live spellingLive kind number stored
  simp only [↓reduceIte]
  rw [wp_bind']
  apply bytes_spelled_wp heap atom spelling stored
  rw [wp_bind']
  apply length_spelled_wp heap atom spelling count stored header
  simpa only [wp_pure] using after

/-- Finishing a real forwarding path leaves a terminal which needs no
further forwarding iteration; the helper's second guard still executes. -/
theorem terminal_path {heap : Heap L} {start terminal : Option Ptr} {count : Nat}
    (path : SymbolForward.ForwardPath heap start terminal count) :
    SymbolForward.ForwardPath heap terminal terminal 0 := by
  induction path with
  | null => exact .null
  | stop pointer arena live tag ordinary => exact .stop pointer arena live tag ordinary
  | edge _ _ _ _ _ _ _ _ ih => exact ih

/-- The caller's forwarding and the called predicate's forwarding are separate
operation traces. Exhaustion remains explicit; it is not semantic refusal. -/
def managedAfterForward (allowance : Nat) (start : Option Ptr) :
    CProg CVal (ReadBlock.Result (Option Ptr × Option (Option Ptr × UInt32))) := do
  let first ← SymbolForward.traversal allowance start
  match first with
  | .exhausted => pure .exhausted
  | .finished (.next current) =>
      let second ← SymbolForward.traversal 0 current
      match second with
      | .exhausted => pure .exhausted
      | .finished (.next selected) =>
          let result ← managedHeader selected
          pure (.finished (.next (selected, result)))
      | other => pure (other.mapContext (fun pointer => (pointer, none)))
  | other => pure (other.mapContext (fun pointer => (pointer, none)))

theorem managedAfterForward_wp (heap : Heap L) (start : Option Ptr)
    (atom spelling : Ptr) (count : UInt32) (hops allowance : Nat)
    (path : SymbolForward.ForwardPath heap start (some atom) hops) (enough : hops ≤ allowance)
    (live : Valid heap atom) (spellingLive : Valid heap spelling)
    (kind : Reads atom (.u32 0) heap) (number : Reads (atom + 3) (.u32 0) heap)
    (stored : Reads (atom + 5) (.ptr (some spelling)) heap)
    (header : Reads (spelling + 1) (.u32 count) heap)
    (post : ReadBlock.Result (Option Ptr × Option (Option Ptr × UInt32)) → Heap L → Prop)
    (after : post (.finished (.next (some atom, some (some (spelling + 2), count)))) heap) :
    (managedAfterForward allowance start).wp act post heap := by
  unfold managedAfterForward
  rw [wp_bind']
  apply SymbolForward.traversal_path_wp heap path allowance enough
  rw [wp_bind']
  apply SymbolForward.traversal_path_wp heap (terminal_path path) 0 (Nat.le_refl 0)
  rw [wp_bind']
  apply managedHeader_wp heap atom spelling count live spellingLive kind number stored header
  simpa only [wp_pure] using after

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolSpelling

end ManagedNativeSymbolOwned


section ManagedNativeSymbolExecutionControls
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

end ManagedNativeSymbolExecutionControls


/-! ## Actual frame-directory lookup

The typed-cell source reader retains the authored unsigned hash, empty `for`
loop, physical table/entry loads and lexical declarations. The independent
inventory supplies table geometry, no-vacancy paths, owning-row coverage and
a finite stopping bound. The identity decoder is instantiated by its proved
bit-level meaning; the full C parts/output helper and by-value reference call
remain separate source/ABI joins.
-/
section NativeDirectoryLookupPackage
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe
open Mettapedia.Machines.IncrementalConformance

/-- Native 32-bit multiplicative hashing. The multiplication deliberately
wraps before the shift, exactly as the unsigned C expression does. -/
def home (handle shift : UInt32) : UInt32 := (handle * 0x9E3779B1) >>> shift

def advance (slot mask : UInt32) : UInt32 := (slot + 1) &&& mask

theorem home_within_capacity (handle shift : UInt32) (valid : shift.toNat < 32) :
    (home handle shift).toNat < 2 ^ (32 - shift.toNat) := by
  have bounded := BitVec.toNat_ushiftRight_lt (handle * 0x9E3779B1).toBitVec
    shift.toNat (by omega)
  rw [home, UInt32.toNat_shiftRight, Nat.mod_eq_of_lt valid]
  exact bounded

theorem advance_is_cyclic (slot mask : UInt32) (bits : Nat) (width : bits ≤ 32)
    (shape : mask.toNat = 2 ^ bits - 1) :
    (advance slot mask).toNat = (slot.toNat + 1) % 2 ^ bits := by
  simp only [advance, UInt32.toNat_and, UInt32.toNat_add, shape,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 width)

/-- Distance in the physical probe direction, before the first complete turn. -/
def distance (capacity start target : Nat) : Nat :=
  if start ≤ target then target - start else capacity - start + target

theorem distance_lt {capacity start target : Nat}
    (startWithin : start < capacity) (targetWithin : target < capacity) :
    distance capacity start target < capacity := by
  unfold distance
  split <;> omega

theorem distance_reaches {capacity start target : Nat}
    (startWithin : start < capacity) (targetWithin : target < capacity) :
    (start + distance capacity start target) % capacity = target := by
  unfold distance
  split
  · have sum : start + (target - start) = target := by omega
    rw [sum, Nat.mod_eq_of_lt targetWithin]
  · have sum : start + (capacity - start + target) = capacity + target := by omega
    rw [sum, Nat.add_mod_left, Nat.mod_eq_of_lt targetWithin]

variable {Key Value : Type*} [DecidableEq Key]

/-- One traversal of the existing physical table, starting at the computed
home. This supplies InternProbe's existing finite sequence; it is not a new
lookup algorithm. -/
def sequence {capacity : Nat} (table : Fin capacity → Option (Key × Value))
    (start : Fin capacity) : InternProbe.Cells Key Value :=
  List.ofFn fun offset : Fin capacity =>
    table ⟨(start.val + offset.val) % capacity, Nat.mod_lt _ (by have := start.isLt; omega)⟩

/-- The checkpoint validator's no-hole condition is about occupied storage
between an entry's hash home and its physical table slot. -/
def PathsOccupied {capacity : Nat} (table : Fin capacity → Option (Key × Value))
    (start : Key → Fin capacity) : Prop :=
  ∀ target key value, table target = some (key, value) →
    ∀ offset, offset < distance capacity (start key).val target.val →
      table ⟨((start key).val + offset) % capacity, Nat.mod_lt _ (by have := target.isLt; omega)⟩ ≠ none

/-- Existing frame identities make a handle determine one entry. This says
nothing about the success of a particular probe. -/
def KeysCoherent {capacity : Nat} (table : Fin capacity → Option (Key × Value)) : Prop :=
  ∀ first second key left right,
    table first = some (key, left) → table second = some (key, right) → left = right

theorem sequence_finds_entry {capacity : Nat}
    (table : Fin capacity → Option (Key × Value)) (start : Key → Fin capacity)
    (paths : PathsOccupied table start) (keys : KeysCoherent table)
    (target : Fin capacity) (key : Key) (value : Value)
    (present : table target = some (key, value)) :
    (InternProbe.probe key (sequence table (start key))).1 = some value := by
  let offset := distance capacity (start key).val target.val
  have within : offset < capacity := distance_lt (start key).isLt target.isLt
  have atTarget : (sequence table (start key))[offset]'(by simpa [sequence] using within) =
      some (key, value) := by
    simp only [sequence, List.getElem_ofFn]
    have index : (⟨((start key).val + offset) % capacity,
        Nat.mod_lt _ (by have := target.isLt; omega)⟩ : Fin capacity) = target := by
      apply Fin.ext
      exact distance_reaches (start key).isLt target.isLt
    simpa only [index] using present
  apply InternProbe.finds_reachable_member key value (sequence table (start key))
    ⟨offset, by simpa [sequence] using within⟩ atTarget
  · intro earlier before
    simp only [sequence, List.getElem_ofFn]
    exact paths target key value present earlier.val before
  · intro candidate member
    obtain ⟨offset, found⟩ := List.mem_ofFn.mp member
    exact keys _ target key candidate value found present

omit [DecidableEq Key] in
theorem sequence_mem_iff {capacity : Nat}
    (table : Fin capacity → Option (Key × Value)) (start : Fin capacity)
    (cell : Option (Key × Value)) :
    cell ∈ sequence table start ↔ ∃ slot, table slot = cell := by
  constructor
  · intro member
    obtain ⟨offset, same⟩ := List.mem_ofFn.mp member
    exact ⟨_, same⟩
  · rintro ⟨slot, same⟩
    let offset := distance capacity start.val slot.val
    have within : offset < capacity := distance_lt start.isLt slot.isLt
    apply List.mem_ofFn.mpr
    refine ⟨⟨offset, within⟩, ?_⟩
    have index : (⟨(start.val + offset) % capacity,
        Nat.mod_lt _ (by have := slot.isLt; omega)⟩ : Fin capacity) = slot := by
      apply Fin.ext
      exact distance_reaches start.isLt slot.isLt
    simpa only [index] using same

/-- Bidirectional lookup against a concrete table inventory: success is
neither assumed nor defined to be source membership. -/
theorem sequence_found_iff {capacity : Nat}
    (table : Fin capacity → Option (Key × Value)) (start : Key → Fin capacity)
    (paths : PathsOccupied table start) (keys : KeysCoherent table)
    (key : Key) (value : Value) :
    (InternProbe.probe key (sequence table (start key))).1 = some value ↔
      ∃ slot, table slot = some (key, value) := by
  constructor
  · intro found
    exact (sequence_mem_iff table (start key) _).mp
      (InternProbe.found_mem key _ value found)
  · rintro ⟨slot, present⟩
    exact sequence_finds_entry table start paths keys slot key value present

/-- The native half-load invariant supplies a vacant slot in every complete
cyclic traversal, independently of the particular requested handle. -/
theorem sequence_stops_of_half_load {capacity : Nat}
    (table : Fin capacity → Option (Key × Value)) (start : Fin capacity)
    (loaded : (List.ofFn table).countP Option.isSome ≤ capacity / 2)
    (key : Key) :
    (InternProbe.probe key (sequence table start)).1 ≠ none ∨
      (InternProbe.probe key (sequence table start)).2 ≠ none := by
  have positive : 0 < capacity := by have := start.isLt; omega
  have room : (List.ofFn table).countP Option.isSome < (List.ofFn table).length := by
    simp only [List.length_ofFn]
    have half : capacity / 2 < capacity := Nat.div_lt_self positive (by decide)
    omega
  have vacant := InternProbe.vacancy_of_count_lt (List.ofFn table) room
  obtain ⟨slot, empty⟩ := List.mem_ofFn.mp vacant
  apply InternProbe.stops_if_vacancy
  exact (sequence_mem_iff table start none).mpr ⟨slot, empty⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe
open Mettapedia.Machines.IncrementalConformance

variable {Key : Type*} [DecidableEq Key]

/-- Table entries name rows of the separately retained owning vector. The
key comes from that row, not from a second copy in the pointer table. -/
def keyed {capacity : Nat} (keys : List Key)
    (table : Fin capacity → Option (Fin keys.length)) :
    Fin capacity → Option (Key × Fin keys.length) :=
  fun slot => (table slot).map fun row => (keys[row.val], row)

/-- The structural checkpoint checks each occupied pointer's membership,
pairwise uniqueness, and the occupied count. It does not invoke lookup. -/
def RowsComplete {capacity : Nat} {keys : List Key}
    (table : Fin capacity → Option (Fin keys.length)) : Prop :=
  ((List.ofFn table).filterMap id).Nodup ∧
    ((List.ofFn table).filterMap id).length = keys.length

omit [DecidableEq Key] in
theorem rows_complete_cover {capacity : Nat} {keys : List Key}
    (table : Fin capacity → Option (Fin keys.length)) (complete : RowsComplete table)
    (row : Fin keys.length) : ∃ slot, table slot = some row := by
  let rows := (List.ofFn table).filterMap id
  have distinct : rows.Nodup := complete.1
  have cardinal : rows.toFinset.card = Fintype.card (Fin keys.length) := by
    rw [List.toFinset_card_of_nodup distinct, Fintype.card_fin]
    exact complete.2
  have allRows : rows.toFinset = Finset.univ := Finset.eq_univ_of_card _ cardinal
  have member : row ∈ rows := List.mem_toFinset.mp (by rw [allRows]; simp)
  obtain ⟨cell, present, same⟩ := List.mem_filterMap.mp member
  have isRow : cell = some row := same
  subst cell
  exact List.mem_ofFn.mp present

omit [DecidableEq Key] in
theorem keyed_coherent {capacity : Nat} (keys : List Key)
    (distinct : keys.Nodup) (table : Fin capacity → Option (Fin keys.length)) :
    KeysCoherent (keyed keys table) := by
  intro first second key left right atFirst atSecond
  obtain ⟨firstRow, _, firstPair⟩ := Option.map_eq_some_iff.mp atFirst
  obtain ⟨secondRow, _, secondPair⟩ := Option.map_eq_some_iff.mp atSecond
  have firstFields := Prod.mk.inj firstPair
  have secondFields := Prod.mk.inj secondPair
  rw [← firstFields.2, ← secondFields.2]
  apply Fin.ext
  exact distinct.getElem_inj_iff.mp (firstFields.1.trans secondFields.1.symm)

/-- A successful finite probe corresponds exactly to the requested owning
row. Completeness of table membership is derived from the validator's count
and uniqueness checks, not supplied as lookup adequacy. -/
theorem probe_owning_row_iff {capacity : Nat} (keys : List Key)
    (distinct : keys.Nodup) (table : Fin capacity → Option (Fin keys.length))
    (complete : RowsComplete table) (start : Key → Fin capacity)
    (paths : PathsOccupied (keyed keys table) start)
    (key : Key) (row : Fin keys.length) :
    (InternProbe.probe key (sequence (keyed keys table) (start key))).1 = some row ↔
      keys[row.val] = key := by
  rw [sequence_found_iff _ start paths (keyed_coherent keys distinct table)]
  constructor
  · rintro ⟨slot, present⟩
    obtain ⟨actual, _, same⟩ := Option.map_eq_some_iff.mp present
    have fields := Prod.mk.inj same
    simpa only [fields.2] using fields.1
  · intro same
    obtain ⟨slot, present⟩ := rows_complete_cover table complete row
    exact ⟨slot, by simp only [keyed, present, Option.map_some, same]⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe
open Mettapedia.Machines.IncrementalConformance

/-- Physical directory rows keep the entire admitted epoch. The hash key is
only the handle; generation is checked after selection. -/
def frameKeys (directory : DirectoryReadback) : List Nat :=
  directory.frames.map fun frame => frame.view.token.handle

def frameAtRow (directory : DirectoryReadback) (row : Fin (frameKeys directory).length) :
    FrameReadback :=
  directory.frames[row.val]'(by simpa only [frameKeys, List.length_map] using row.isLt)

def frameEpoch (frame : FrameReadback) : UInt32 := UInt32.ofNat (encode frame.view.token).toNat

theorem frameEpoch_toNat (frame : FrameReadback) :
    (frameEpoch frame).toNat = (encode frame.view.token).toNat := by
  rw [frameEpoch, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (encode_fits_uint32 frame.admitted.1.1)]

theorem frameEpoch_ne_zero (frame : FrameReadback) : frameEpoch frame ≠ 0 := by
  intro same
  have positive := (encoding_bounds frame.admitted.1.1).1
  have number := congrArg UInt32.toNat same
  rw [frameEpoch_toNat, encode_toNat frame.admitted.1.1] at number
  change encoding frame.view.token = 0 at number
  omega

theorem frameEpoch_handle (frame : FrameReadback) :
    unpackHandle (frameEpoch frame).toNat = frame.view.token.handle := by
  rw [frameEpoch_toNat, encode_toNat frame.admitted.1.1]
  exact (unpack_encoding frame.admitted.1.1).1

theorem frameAtRow_key (directory : DirectoryReadback)
    (row : Fin (frameKeys directory).length) :
    (frameKeys directory)[row.val] = (frameAtRow directory row).view.token.handle := by
  simp only [frameKeys, List.getElem_map, frameAtRow]

theorem frameAtRow_mem (directory : DirectoryReadback)
    (row : Fin (frameKeys directory).length) : frameAtRow directory row ∈ directory.frames :=
  List.getElem_mem _

/-- The selected row still passes the source helper's full-epoch comparison.
This combines the existing finite probe and the independent directory
inventory; physical load and C-control correspondence are separate laws. -/
def findRef {capacity : Nat} (directory : DirectoryReadback)
    (table : Fin capacity → Option (Fin (frameKeys directory).length))
    (start : Nat → Fin capacity) (reference : UInt32) :
    Option (Fin (frameKeys directory).length) :=
  if reference = 0 then none else
    (InternProbe.probe (unpackHandle reference.toNat)
      (sequence (keyed (frameKeys directory) table) (start (unpackHandle reference.toNat)))).1.bind
      fun row => if frameEpoch (frameAtRow directory row) = reference then some row else none

/-- The complete generation, not merely its handle, determines a returned
owning row. Table coverage follows from count and uniqueness. -/
theorem findRef_eq_some_iff {capacity : Nat} (directory : DirectoryReadback)
    (table : Fin capacity → Option (Fin (frameKeys directory).length))
    (complete : RowsComplete table) (start : Nat → Fin capacity)
    (paths : PathsOccupied (keyed (frameKeys directory) table) start)
    (reference : UInt32) (row : Fin (frameKeys directory).length) :
    findRef directory table start reference = some row ↔
      frameEpoch (frameAtRow directory row) = reference := by
  have probeLaw := probe_owning_row_iff (frameKeys directory)
    directory.admitted.2.2.1 table complete start paths (unpackHandle reference.toNat) row
  constructor
  · intro found
    unfold findRef at found
    split at found
    · contradiction
    · obtain ⟨selected, _, accepted⟩ := Option.bind_eq_some_iff.mp found
      split at accepted
      · have same : selected = row := Option.some.inj accepted
        subst selected
        assumption
      · contradiction
  · intro same
    have nonzero : reference ≠ 0 := by rw [← same]; exact frameEpoch_ne_zero _
    have key : (frameKeys directory)[row.val] = unpackHandle reference.toNat := by
      rw [frameAtRow_key, ← same, frameEpoch_handle]
    simp only [findRef, nonzero, ↓reduceIte, probeLaw.mpr key, Option.bind_some, same]

theorem findRef_stale_epoch {capacity : Nat} (directory : DirectoryReadback)
    (table : Fin capacity → Option (Fin (frameKeys directory).length))
    (complete : RowsComplete table) (start : Nat → Fin capacity)
    (paths : PathsOccupied (keyed (frameKeys directory) table) start)
    (reference : UInt32) (row : Fin (frameKeys directory).length)
    (sameHandle : unpackHandle reference.toNat = (frameAtRow directory row).view.token.handle)
    (differentEpoch : frameEpoch (frameAtRow directory row) ≠ reference) :
    findRef directory table start reference = none := by
  have key : (frameKeys directory)[row.val] = unpackHandle reference.toNat := by
    rw [frameAtRow_key, sameHandle]
  have probe := (probe_owning_row_iff (frameKeys directory)
    directory.admitted.2.2.1 table complete start paths _ row).mpr key
  unfold findRef
  split
  · rfl
  · rw [probe, Option.bind_some, if_neg differentEpoch]

/-- Once the entire requested epoch passes, the actual returned row reads
that requested coordinate in the shared retained image. Row position never
becomes a key, and a stale generation cannot enter this observation. -/
theorem findRef_shared_read {capacity : Nat} (directory : DirectoryReadback)
    (table : Fin capacity → Option (Fin (frameKeys directory).length))
    (complete : RowsComplete table) (start : Nat → Fin capacity)
    (paths : PathsOccupied (keyed (frameKeys directory) table) start)
    (requested : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Token)
    (valid : Representable requested) (row : Fin (frameKeys directory).length)
    (found : findRef directory table start (UInt32.ofNat (encode requested).toNat) = some row)
    (slot : Nat) :
    directory.toImage.readSlot? (requested.ref slot) =
      (frameAtRow directory row).toEntry.readSlot? (frameAtRow directory row).view.writeClock slot := by
  have epoch := (findRef_eq_some_iff directory table complete start paths _ row).mp found
  have natural := congrArg UInt32.toNat epoch
  rw [frameEpoch_toNat, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (encode_fits_uint32 valid)] at natural
  have encoded : encode (frameAtRow directory row).view.token = encode requested :=
    BitVec.eq_of_toNat_eq natural
  have token := encode_injective (frameAtRow directory row).admitted.1.1 valid encoded
  rw [← token]
  exact directory.toImage_readSlot (frameAtRow directory row) (frameAtRow_mem directory row) slot

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Physical
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.IncrementalConformance
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open CellPermission

/-- The loop's actual read path reloads the directory's pointer table, then
loads its selected pointer and checks the stored epoch. Null testing remains
a C pointer operation with its lifetime obligation. -/
def iteration (directory : Ptr) (key : Nat) (mask slot : UInt32) :
    CProg CVal (ReadBlock.Result UInt32) := do
  let table ← CProg.loadPtr (directory + 9)
  match table with
  | none => CProg.undefined
  | some table =>
    let entry ← CProg.loadPtr (table + slot.toNat)
    let null ← CProg.ptrEq entry none
    if null then pure (.finished (.returned slot (some (.ptr none))))
    else match entry with
      | none => CProg.undefined
      | some entry =>
        let epoch ← CProg.loadU32 entry
        if unpackHandle epoch.toNat = key then
          pure (.finished (.returned slot (some (.ptr (some entry)))))
        else pure (.finished (.next (advance slot mask)))

def search (directory : Ptr) (key : Nat) (mask : UInt32) (fuel : Nat) (slot : UInt32) :
    CProg CVal (ReadBlock.Result UInt32) :=
  ReadBlock.whileWith (fun _ => pure true) (iteration directory key mask) fuel slot

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- An initialized physical table cell and, when present, its epoch field.
These are read and lifetime facts about actual cells; they do not assert
anything about the outcome of lookup. -/
def CellRead (directory : Ptr) (slot : UInt32) (cell : Option (Nat × Ptr))
    (heap : Heap L) : Prop :=
  ∃ table, Reads (directory + 9) (.ptr (some table)) heap ∧
    Reads (table + slot.toNat) (.ptr (cell.map Prod.snd)) heap ∧
    match cell with
    | none => True
    | some (key, address) =>
        ValidAt address heap ∧ ∃ epoch, Reads address (.u32 epoch) heap ∧
          unpackHandle epoch.toNat = key

/-- One finite turn of initialized cells in physical advance order. Repeated
addresses or malformed epochs are not normalized by this read relation. -/
def SequenceRead (directory : Ptr) (mask : UInt32) :
    UInt32 → InternProbe.Cells Nat Ptr → Heap L → Prop
  | _, [], _ => True
  | slot, cell :: tail, heap =>
      CellRead directory slot cell heap ∧
        SequenceRead directory mask (advance slot mask) tail heap

theorem sequenceRead_iff (directory : Ptr) (mask slot : UInt32)
    (cells : InternProbe.Cells Nat Ptr) (heap : Heap L) :
    SequenceRead directory mask slot cells heap ↔
      ∀ offset : Fin cells.length,
        CellRead directory ((fun current => advance current mask)^[offset.val] slot)
          cells[offset.val] heap := by
  induction cells generalizing slot with
  | nil => simp [SequenceRead]
  | cons cell tail ih =>
    rw [SequenceRead, ih]
    constructor
    · rintro ⟨first, rest⟩ offset
      rcases offset with ⟨offset, bound⟩
      cases offset with
      | zero => exact first
      | succ offset =>
        simpa only [List.getElem_cons_succ, Function.iterate_succ_apply] using
          rest ⟨offset, by simpa using bound⟩
    · intro all
      refine ⟨all ⟨0, by simp⟩, ?_⟩
      intro offset
      simpa only [List.getElem_cons_succ, Function.iterate_succ_apply] using
        all ⟨offset.val + 1, by simp⟩

theorem advance_iterate_toNat (slot mask : UInt32) (bits : Nat) (width : bits ≤ 32)
    (shape : mask.toNat = 2 ^ bits - 1) (inside : slot.toNat < 2 ^ bits) (offset : Nat) :
    ((fun current => advance current mask)^[offset] slot).toNat =
      (slot.toNat + offset) % 2 ^ bits := by
  induction offset with
  | zero => simp [Nat.mod_eq_of_lt inside]
  | succ offset ih =>
    rw [Function.iterate_succ_apply', advance_is_cyclic _ mask bits width shape, ih]
    rw [Nat.mod_add_mod, Nat.add_assoc]

/-- The physical read inventory is supplied in table coordinates. The cyclic
probe order is then derived from the actual unsigned increment and mask. -/
theorem sequenceRead_of_inventory (directory : Ptr) (mask slot : UInt32)
    (bits : Nat) (width : bits ≤ 32) (shape : mask.toNat = 2 ^ bits - 1)
    (inside : slot.toNat < 2 ^ bits)
    (table : Fin (2 ^ bits) → Option (Nat × Ptr)) (heap : Heap L)
    (reads : ∀ position, CellRead directory (UInt32.ofNat position.val) (table position) heap) :
    SequenceRead directory mask slot (sequence table ⟨slot.toNat, inside⟩) heap := by
  rw [sequenceRead_iff]
  intro offset
  let position : Fin (2 ^ bits) :=
    ⟨(slot.toNat + offset.val) % 2 ^ bits, Nat.mod_lt _ (Nat.two_pow_pos bits)⟩
  have coordinate : UInt32.ofNat position.val =
      (fun current => advance current mask)^[offset.val] slot := by
    have index := advance_iterate_toNat slot mask bits width shape inside offset.val
    rw [show position.val =
      ((fun current => advance current mask)^[offset.val] slot).toNat from index.symm]
    exact UInt32.ofNat_toNat
  simpa only [sequence, List.getElem_ofFn, coordinate] using reads position

private theorem loadPtr_at {address : Ptr} {value : Option Ptr} {heap : Heap L}
    {post : Option Ptr → Heap L → Prop} (reads : Reads address (.ptr value) heap)
    (holds : post value heap) : (CProg.loadPtr address).wp act post heap := by
  refine wp_consequence act
    (loadPtr_rule (P := fun reached => reached = heap) (q := value) ?_) rfl ?_
  · rintro reached rfl
    exact reads
  · rintro actual reached ⟨rfl, rfl⟩
    exact holds

private theorem loadU32_at {address : Ptr} {value : UInt32} {heap : Heap L}
    {post : UInt32 → Heap L → Prop} (reads : Reads address (.u32 value) heap)
    (holds : post value heap) : (CProg.loadU32 address).wp act post heap := by
  refine wp_consequence act
    (loadU32_rule (P := fun reached => reached = heap) (n := value) ?_) rfl ?_
  · rintro reached rfl
    exact reads
  · rintro actual reached ⟨rfl, rfl⟩
    exact holds

/-- A complete physical probe implements the existing independent finite
probe. Sufficient iteration allowance is proved from its supplied inventory;
scheduler pauses still retain the operation tree and do not consume another
copy of an already executed read. -/
theorem search_returns_probe (directory : Ptr) (key : Nat) (mask : UInt32)
    (cells : InternProbe.Cells Nat Ptr) (pre : Heap L → Prop)
    (stops : (InternProbe.probe key cells).1 ≠ none ∨
      (InternProbe.probe key cells).2 ≠ none)
    (fuel : Nat) (slot : UInt32) (enough : cells.length ≤ fuel)
    (inventory : ∀ heap, pre heap → SequenceRead directory mask slot cells heap) :
    CTriple pre (search directory key mask fuel slot)
      (fun result heap => pre heap ∧ ∃ finalSlot,
        result = .finished (.returned finalSlot
          (some (.ptr (InternProbe.probe key cells).1)))) := by
  induction cells generalizing fuel slot with
  | nil => simp [InternProbe.probe] at stops
  | cons cell tail ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      intro heap held
      obtain ⟨readCell, _⟩ := inventory heap held
      obtain ⟨table, readTable, readPointer, readEpoch⟩ := readCell
      change (search directory key mask (fuel + 1) slot).wp act _ heap
      rw [search, ReadBlock.whileWith.eq_def]
      simp only [Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, ↓reduceIte]
      rw [wp_bind]
      rw [iteration, wp_bind']
      apply loadPtr_at readTable
      rw [wp_bind']
      apply loadPtr_at readPointer
      rw [wp_bind']
      cases cell with
      | none =>
        simp only [Option.map_none]
        apply wp_ptrEq (by trivial) (by trivial)
        simp only [decide_true, ↓reduceIte, wp_pure, wp_ret]
        exact ⟨held, slot, rfl⟩
      | some pair =>
        rcases pair with ⟨stored, address⟩
        simp only [Option.map_some]
        obtain ⟨valid, epoch, readValue, keyValue⟩ := readEpoch
        apply wp_ptrEq (p := some address) (q := none)
          (show ValidOpt heap (some address) from valid) (by trivial)
        simp only [Option.some_ne_none, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [wp_bind']
        apply loadU32_at readValue
        rw [keyValue]
        by_cases same : stored = key
        · simp only [same, ↓reduceIte, wp_pure, wp_ret]
          exact ⟨held, slot, by simp [InternProbe.probe]⟩
        · simp only [same, ↓reduceIte, wp_pure]
          have tailStops : (InternProbe.probe key tail).1 ≠ none ∨
              (InternProbe.probe key tail).2 ≠ none := by
            simpa [InternProbe.probe, Ne.symm same] using stops
          have next := ih tailStops fuel (advance slot mask)
            (by simp only [List.length_cons] at enough; omega)
            (fun reached owns => (inventory reached owns).2) heap held
          simpa only [Prog.wp, search, Prog.pure_eq, InternProbe.probe,
            if_neg (Ne.symm same)] using next

/-- A half-full native directory always supplies a stopping cell in one
physical turn. The loop's result is the independent inventory probe, with
the same full heap retained throughout all its loads. -/
theorem search_returns_inventory (directory : Ptr) (key : Nat) (mask slot : UInt32)
    (bits : Nat) (width : bits ≤ 32) (shape : mask.toNat = 2 ^ bits - 1)
    (inside : slot.toNat < 2 ^ bits)
    (table : Fin (2 ^ bits) → Option (Nat × Ptr))
    (loaded : (List.ofFn table).countP Option.isSome ≤ 2 ^ bits / 2)
    (fuel : Nat) (enough : 2 ^ bits ≤ fuel) (pre : Heap L → Prop)
    (reads : ∀ heap, pre heap → ∀ position,
      CellRead directory (UInt32.ofNat position.val) (table position) heap) :
    CTriple pre (search directory key mask fuel slot)
      (fun result heap => pre heap ∧ ∃ finalSlot,
        result = .finished (.returned finalSlot
          (some (.ptr (InternProbe.probe key (sequence table ⟨slot.toNat, inside⟩)).1)))) := by
  exact search_returns_probe directory key mask _ pre
    (sequence_stops_of_half_load table ⟨slot.toNat, inside⟩ loaded key) fuel slot
    (by simpa only [sequence, List.length_ofFn] using enough)
    (fun heap held => sequenceRead_of_inventory directory mask slot bits width shape
      inside table heap (reads heap held))

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Physical


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Source
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def id (name : String) : CExpr := .identifier name.toList
def field (owner name : String) : CExpr := .field (id owner) name.toList true
def uint32 : CType := ⟨"uint32_t".toList, 0⟩
def entryType : CType := ⟨"BindingsFrameIndexEntry".toList, 1⟩
def types : TypeNames := ["uint32_t".toList, "BindingsFrameIndexEntry".toList]
def nullReturn : List CStatement := [.return (some .null)]

def homeBody : List CStatement :=
  [.return (some (.binary .shiftRight
    (.binary .mul (id "handle") (.unsignedInteger 2654435761))
    (field "index" "handle_table_shift")))]

def iteration : List CStatement :=
  [.declare entryType "entry".toList (.index (field "index" "handle_table") (id "slot")),
   .branch (.unary .not (id "entry")) nullReturn [],
   .branch (.binary .eq (.call "cetta_frame_handle".toList [field "entry" "epoch"])
     (id "handle")) [.return (some (id "entry"))] [],
   .assign (id "slot") (.binary .bitAnd
     (.binary .add (id "slot") (.unsignedInteger 1)) (id "mask"))]

def lookupBody : List CStatement :=
  [.branch (.unary .not (field "index" "handle_table")) nullReturn [],
   .declare uint32 "mask".toList (field "index" "handle_table_mask"),
   .declare uint32 "slot".toList
     (.call "bindings_frame_table_home".toList [id "index", id "handle"]),
   .whileLoop (.bool true) iteration]

def identity : CExpr := .field (id "ref") "identity".toList false

def findRefBody : List CStatement :=
  [.branch (.binary .or (.unary .not (id "index"))
     (.unary .not (.call "bindings_frame_ref_is_valid".toList [id "ref"]))) nullReturn [],
   .declare entryType "entry".toList (.call "bindings_frame_table_lookup".toList
     [id "index", .call "cetta_frame_handle".toList [identity]]),
   .return (some (.conditional (.binary .and (id "entry")
     (.binary .eq (field "entry" "epoch") identity)) (id "entry") .null))]

private def homePiece0 : String × List Token :=
  ("{\n", [.punctuation ['{']])

private theorem homePiece0_lex : homePiece0.1.toList.foldl step initial =
    completed homePiece0.2 := by decide +kernel

private def homePiece1 : String × List Token :=
  ("    return (handle * UINT32_C(0x9E3779B1)) >> index->handle_table_shift;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .punctuation ['('], .identifier ['h', 'a', 'n', 'd', 'l', 'e'], .punctuation ['*'], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '9', 'E', '3', '7', '7', '9', 'B', '1'], .punctuation [')'], .punctuation [')'], .punctuation ['>', '>'], .identifier ['i', 'n', 'd', 'e', 'x'], .punctuation ['-', '>'], .identifier ['h', 'a', 'n', 'd', 'l', 'e', '_', 't', 'a', 'b', 'l', 'e', '_', 's', 'h', 'i', 'f', 't'], .punctuation [';']])

private theorem homePiece1_lex : homePiece1.1.toList.foldl step initial =
    completed homePiece1.2 := by decide +kernel

private def homePiece2 : String × List Token :=
  ("}", [.punctuation ['}']])

private theorem homePiece2_lex : homePiece2.1.toList.foldl step initial =
    completed homePiece2.2 := by decide +kernel

private def homePieces : List (String × List Token) :=
  [homePiece0, homePiece1, homePiece2]

def homeSource : String := String.join (homePieces.map Prod.fst)
def homeTokens : List Token := homePieces.flatMap Prod.snd

theorem home_lex : lex homeSource.toList = .ok homeTokens := by
  apply lex_completed_string_pieces
  simp only [homePieces, List.forall_cons]
  exact ⟨homePiece0_lex, homePiece1_lex, homePiece2_lex, trivial⟩

theorem home_parsed : blockText? types homeSource.toList = some homeBody :=
  block_text_of_parts _ _ homeTokens _ home_lex (by rfl)

private def lookupPiece0 : String × List Token :=
  ("{\n", [.punctuation ['{']])

private theorem lookupPiece0_lex : lookupPiece0.1.toList.foldl step initial =
    completed lookupPiece0.2 := by decide +kernel

private def lookupPiece1 : String × List Token :=
  ("    if (!index->handle_table)\n", [.identifier ['i', 'f'], .punctuation ['('], .punctuation ['!'], .identifier ['i', 'n', 'd', 'e', 'x'], .punctuation ['-', '>'], .identifier ['h', 'a', 'n', 'd', 'l', 'e', '_', 't', 'a', 'b', 'l', 'e'], .punctuation [')']])

private theorem lookupPiece1_lex : lookupPiece1.1.toList.foldl step initial =
    completed lookupPiece1.2 := by decide +kernel

private def lookupPiece2 : String × List Token :=
  ("        return NULL;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['N', 'U', 'L', 'L'], .punctuation [';']])

private theorem lookupPiece2_lex : lookupPiece2.1.toList.foldl step initial =
    completed lookupPiece2.2 := by decide +kernel

private def lookupPiece3 : String × List Token :=
  ("    uint32_t mask = index->handle_table_mask;\n", [.identifier ['u', 'i', 'n', 't', '3', '2', '_', 't'], .identifier ['m', 'a', 's', 'k'], .punctuation ['='], .identifier ['i', 'n', 'd', 'e', 'x'], .punctuation ['-', '>'], .identifier ['h', 'a', 'n', 'd', 'l', 'e', '_', 't', 'a', 'b', 'l', 'e', '_', 'm', 'a', 's', 'k'], .punctuation [';']])

private theorem lookupPiece3_lex : lookupPiece3.1.toList.foldl step initial =
    completed lookupPiece3.2 := by decide +kernel

private def lookupPiece4 : String × List Token :=
  ("    uint32_t slot = bindings_frame_table_home(index, handle);\n", [.identifier ['u', 'i', 'n', 't', '3', '2', '_', 't'], .identifier ['s', 'l', 'o', 't'], .punctuation ['='], .identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's', '_', 'f', 'r', 'a', 'm', 'e', '_', 't', 'a', 'b', 'l', 'e', '_', 'h', 'o', 'm', 'e'], .punctuation ['('], .identifier ['i', 'n', 'd', 'e', 'x'], .punctuation [','], .identifier ['h', 'a', 'n', 'd', 'l', 'e'], .punctuation [')'], .punctuation [';']])

private theorem lookupPiece4_lex : lookupPiece4.1.toList.foldl step initial =
    completed lookupPiece4.2 := by decide +kernel

private def lookupPiece5 : String × List Token :=
  ("    for (;;) {\n", [.identifier ['f', 'o', 'r'], .punctuation ['('], .punctuation [';'], .punctuation [';'], .punctuation [')'], .punctuation ['{']])

private theorem lookupPiece5_lex : lookupPiece5.1.toList.foldl step initial =
    completed lookupPiece5.2 := by decide +kernel

private def lookupPiece6 : String × List Token :=
  ("        BindingsFrameIndexEntry *entry = index->handle_table[slot];\n", [.identifier ['B', 'i', 'n', 'd', 'i', 'n', 'g', 's', 'F', 'r', 'a', 'm', 'e', 'I', 'n', 'd', 'e', 'x', 'E', 'n', 't', 'r', 'y'], .punctuation ['*'], .identifier ['e', 'n', 't', 'r', 'y'], .punctuation ['='], .identifier ['i', 'n', 'd', 'e', 'x'], .punctuation ['-', '>'], .identifier ['h', 'a', 'n', 'd', 'l', 'e', '_', 't', 'a', 'b', 'l', 'e'], .punctuation ['['], .identifier ['s', 'l', 'o', 't'], .punctuation [']'], .punctuation [';']])

private theorem lookupPiece6_lex : lookupPiece6.1.toList.foldl step initial =
    completed lookupPiece6.2 := by decide +kernel

private def lookupPiece7 : String × List Token :=
  ("        if (!entry)\n", [.identifier ['i', 'f'], .punctuation ['('], .punctuation ['!'], .identifier ['e', 'n', 't', 'r', 'y'], .punctuation [')']])

private theorem lookupPiece7_lex : lookupPiece7.1.toList.foldl step initial =
    completed lookupPiece7.2 := by decide +kernel

private def lookupPiece8 : String × List Token :=
  ("            return NULL;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['N', 'U', 'L', 'L'], .punctuation [';']])

private theorem lookupPiece8_lex : lookupPiece8.1.toList.foldl step initial =
    completed lookupPiece8.2 := by decide +kernel

private def lookupPiece9 : String × List Token :=
  ("        if (cetta_frame_handle(entry->epoch) == handle)\n", [.identifier ['i', 'f'], .punctuation ['('], .identifier ['c', 'e', 't', 't', 'a', '_', 'f', 'r', 'a', 'm', 'e', '_', 'h', 'a', 'n', 'd', 'l', 'e'], .punctuation ['('], .identifier ['e', 'n', 't', 'r', 'y'], .punctuation ['-', '>'], .identifier ['e', 'p', 'o', 'c', 'h'], .punctuation [')'], .punctuation ['=', '='], .identifier ['h', 'a', 'n', 'd', 'l', 'e'], .punctuation [')']])

private theorem lookupPiece9_lex : lookupPiece9.1.toList.foldl step initial =
    completed lookupPiece9.2 := by decide +kernel

private def lookupPiece10 : String × List Token :=
  ("            return entry;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['e', 'n', 't', 'r', 'y'], .punctuation [';']])

private theorem lookupPiece10_lex : lookupPiece10.1.toList.foldl step initial =
    completed lookupPiece10.2 := by decide +kernel

private def lookupPiece11 : String × List Token :=
  ("        slot = (slot + 1u) & mask;\n", [.identifier ['s', 'l', 'o', 't'], .punctuation ['='], .punctuation ['('], .identifier ['s', 'l', 'o', 't'], .punctuation ['+'], .number ['1', 'u'], .punctuation [')'], .punctuation ['&'], .identifier ['m', 'a', 's', 'k'], .punctuation [';']])

private theorem lookupPiece11_lex : lookupPiece11.1.toList.foldl step initial =
    completed lookupPiece11.2 := by decide +kernel

private def lookupPiece12 : String × List Token :=
  ("    }\n", [.punctuation ['}']])

private theorem lookupPiece12_lex : lookupPiece12.1.toList.foldl step initial =
    completed lookupPiece12.2 := by decide +kernel

private def lookupPiece13 : String × List Token :=
  ("}", [.punctuation ['}']])

private theorem lookupPiece13_lex : lookupPiece13.1.toList.foldl step initial =
    completed lookupPiece13.2 := by decide +kernel

private def lookupPieces : List (String × List Token) :=
  [lookupPiece0, lookupPiece1, lookupPiece2, lookupPiece3, lookupPiece4, lookupPiece5, lookupPiece6, lookupPiece7, lookupPiece8, lookupPiece9, lookupPiece10, lookupPiece11, lookupPiece12, lookupPiece13]

def lookupSource : String := String.join (lookupPieces.map Prod.fst)
def lookupTokens : List Token := lookupPieces.flatMap Prod.snd

theorem lookup_lex : lex lookupSource.toList = .ok lookupTokens := by
  apply lex_completed_string_pieces
  simp only [lookupPieces, List.forall_cons]
  exact ⟨lookupPiece0_lex, lookupPiece1_lex, lookupPiece2_lex, lookupPiece3_lex, lookupPiece4_lex, lookupPiece5_lex, lookupPiece6_lex, lookupPiece7_lex, lookupPiece8_lex, lookupPiece9_lex, lookupPiece10_lex, lookupPiece11_lex, lookupPiece12_lex, lookupPiece13_lex, trivial⟩

theorem lookup_parsed : blockText? types lookupSource.toList = some lookupBody :=
  block_text_of_parts _ _ lookupTokens _ lookup_lex (by rfl)

private def findRefPiece0 : String × List Token :=
  ("{\n", [.punctuation ['{']])

private theorem findRefPiece0_lex : findRefPiece0.1.toList.foldl step initial =
    completed findRefPiece0.2 := by decide +kernel

private def findRefPiece1 : String × List Token :=
  ("    if (!index || !bindings_frame_ref_is_valid(ref))\n", [.identifier ['i', 'f'], .punctuation ['('], .punctuation ['!'], .identifier ['i', 'n', 'd', 'e', 'x'], .punctuation ['|', '|'], .punctuation ['!'], .identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's', '_', 'f', 'r', 'a', 'm', 'e', '_', 'r', 'e', 'f', '_', 'i', 's', '_', 'v', 'a', 'l', 'i', 'd'], .punctuation ['('], .identifier ['r', 'e', 'f'], .punctuation [')'], .punctuation [')']])

private theorem findRefPiece1_lex : findRefPiece1.1.toList.foldl step initial =
    completed findRefPiece1.2 := by decide +kernel

private def findRefPiece2 : String × List Token :=
  ("        return NULL;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['N', 'U', 'L', 'L'], .punctuation [';']])

private theorem findRefPiece2_lex : findRefPiece2.1.toList.foldl step initial =
    completed findRefPiece2.2 := by decide +kernel

private def findRefPiece3 : String × List Token :=
  ("    BindingsFrameIndexEntry *entry = bindings_frame_table_lookup(\n", [.identifier ['B', 'i', 'n', 'd', 'i', 'n', 'g', 's', 'F', 'r', 'a', 'm', 'e', 'I', 'n', 'd', 'e', 'x', 'E', 'n', 't', 'r', 'y'], .punctuation ['*'], .identifier ['e', 'n', 't', 'r', 'y'], .punctuation ['='], .identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's', '_', 'f', 'r', 'a', 'm', 'e', '_', 't', 'a', 'b', 'l', 'e', '_', 'l', 'o', 'o', 'k', 'u', 'p'], .punctuation ['(']])

private theorem findRefPiece3_lex : findRefPiece3.1.toList.foldl step initial =
    completed findRefPiece3.2 := by decide +kernel

private def findRefPiece4 : String × List Token :=
  ("        index, cetta_frame_handle(ref.identity));\n", [.identifier ['i', 'n', 'd', 'e', 'x'], .punctuation [','], .identifier ['c', 'e', 't', 't', 'a', '_', 'f', 'r', 'a', 'm', 'e', '_', 'h', 'a', 'n', 'd', 'l', 'e'], .punctuation ['('], .identifier ['r', 'e', 'f'], .punctuation ['.'], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation [')'], .punctuation [')'], .punctuation [';']])

private theorem findRefPiece4_lex : findRefPiece4.1.toList.foldl step initial =
    completed findRefPiece4.2 := by decide +kernel

private def findRefPiece5 : String × List Token :=
  ("    return entry && entry->epoch == ref.identity ? entry : NULL;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['e', 'n', 't', 'r', 'y'], .punctuation ['&', '&'], .identifier ['e', 'n', 't', 'r', 'y'], .punctuation ['-', '>'], .identifier ['e', 'p', 'o', 'c', 'h'], .punctuation ['=', '='], .identifier ['r', 'e', 'f'], .punctuation ['.'], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['?'], .identifier ['e', 'n', 't', 'r', 'y'], .punctuation [':'], .identifier ['N', 'U', 'L', 'L'], .punctuation [';']])

private theorem findRefPiece5_lex : findRefPiece5.1.toList.foldl step initial =
    completed findRefPiece5.2 := by decide +kernel

private def findRefPiece6 : String × List Token :=
  ("}", [.punctuation ['}']])

private theorem findRefPiece6_lex : findRefPiece6.1.toList.foldl step initial =
    completed findRefPiece6.2 := by decide +kernel

private def findRefPieces : List (String × List Token) :=
  [findRefPiece0, findRefPiece1, findRefPiece2, findRefPiece3, findRefPiece4, findRefPiece5, findRefPiece6]

def findRefSource : String := String.join (findRefPieces.map Prod.fst)
def findRefTokens : List Token := findRefPieces.flatMap Prod.snd

theorem findRef_lex : lex findRefSource.toList = .ok findRefTokens := by
  apply lex_completed_string_pieces
  simp only [findRefPieces, List.forall_cons]
  exact ⟨findRefPiece0_lex, findRefPiece1_lex, findRefPiece2_lex, findRefPiece3_lex, findRefPiece4_lex, findRefPiece5_lex, findRefPiece6_lex, trivial⟩

theorem findRef_parsed : blockText? types findRefSource.toList = some findRefBody :=
  block_text_of_parts _ _ findRefTokens _ findRef_lex (by rfl)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Source

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.SourceRead
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

abbrev Context := ObjectBindings.Context

def layout : Layout := fun name =>
  if name = "handle_table".toList then some ⟨9, .pointer⟩
  else if name = "handle_table_mask".toList then some ⟨10, .word⟩
  else if name = "handle_table_shift".toList then some ⟨11, .word⟩
  else if name = "epoch".toList then some ⟨0, .word⟩ else none

/-- The hash helper's unsigned operation tree retains the shift-field load.
Its relation to the actual parsed helper body is proved below. -/
def homeProgram (directory : Ptr) (handle : UInt32) : CProg CVal CVal := do
  let shift ← CProg.loadU32 (directory + 11)
  binary .shiftRight (.u32 (handle * 0x9E3779B1)) (.u32 shift)

/-- Calls retain an explicit identity-decoder component. This module proves
the directory control and hash helper; the decoder's C body/ABI is a separate
component and is not licensed by the name of this call. -/
def calls (decode : UInt32 → CProg CVal UInt32) : Calls := fun name values =>
  if name = "bindings_frame_table_home".toList then
    match values with
    | [.ptr (some directory), .u32 handle] => homeProgram directory handle
    | _ => CProg.undefined
  else if name = "cetta_frame_handle".toList then
    match values with
    | [.u32 epoch] => decode epoch >>= fun handle => pure (.u32 handle)
    | _ => CProg.undefined
  else CProg.undefined

def profile (decode : UInt32 → CProg CVal UInt32) : ObjectBindings.Profile where
  values := calls decode
  locations := fun _ => none
  outsideTypes := fun _ => none
  outsidePlaces := fun _ => none
  fieldTypes := fun _ _ => none
  cellExtent := fun _ => none
  byteExtent := fun _ => none
  sizeWidth := .bits64

def services (decode : UInt32 → CProg CVal UInt32) : ScopedServices Context :=
  { ObjectBindings.services (profile decode) (fun _ _ _ => CProg.undefined)
      (fun _ _ _ => CProg.undefined) with physicalWhile := true }

def scalar (type : CType) (value : CVal) : Option ObjectBindings.Binding :=
  some (.scalar type (some value))

def names (context : Context) : NameReads :=
  localOrLocated (ObjectBindings.values context) (ObjectBindings.declared context) (fun _ => none)

def read (decode : UInt32 → CProg CVal UInt32) (context : Context) (operand : CExpr) :
    CProg CVal CVal := ObjectBindings.read (profile decode) layout context operand

theorem read_scalar (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (name : Name) (type : CType) (value : CVal)
    (known : context name = scalar type value) :
    read decode context (.identifier name) = pure value := by
  simp only [read, ObjectBindings.read, expressionWithNames, localOrLocated,
    ObjectBindings.values, known, scalar]

theorem read_named (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (name : String) (type : CType) (value : CVal)
    (known : context name.toList = scalar type value) :
    read decode context (Source.id name) = pure value :=
  read_scalar decode context name.toList type value known

theorem read_table (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (directory : Ptr) (directoryType : CType)
    (known : context "index".toList = scalar directoryType (.ptr (some directory))) :
    read decode context (Source.field "index" "handle_table") =
      (CProg.loadPtr (directory + 9) >>= fun value => pure (.ptr value)) := by
  change (read decode context (Source.id "index") >>= fun owner =>
    ReadExpressions.field layout owner "handle_table".toList) = _
  rw [read_named decode context _ directoryType _ known]
  rfl

theorem read_slot_pointer (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (directory : Ptr) (directoryType : CType) (slot : UInt32)
    (directoryLocal : context "index".toList = scalar directoryType (.ptr (some directory)))
    (slotLocal : context "slot".toList = scalar Source.uint32 (.u32 slot)) :
    read decode context (.index (Source.field "index" "handle_table") (Source.id "slot")) =
      (CProg.loadPtr (directory + 9) >>= fun table => match table with
        | none => CProg.undefined
        | some table => CProg.loadPtr (table + slot.toNat) >>= fun value => pure (.ptr value)) := by
  change (read decode context (Source.field "index" "handle_table") >>= fun table =>
    read decode context (Source.id "slot") >>= fun offset => indexed table offset) = _
  rw [read_table decode context directory directoryType directoryLocal,
    read_named decode context _ Source.uint32 _ slotLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext table
  cases table <;> rfl

theorem read_shift (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (directory : Ptr) (directoryType : CType)
    (known : context "index".toList = scalar directoryType (.ptr (some directory))) :
    read decode context (Source.field "index" "handle_table_shift") =
      (CProg.loadU32 (directory + 11) >>= fun value => pure (.u32 value)) := by
  change (read decode context (Source.id "index") >>= fun owner =>
    ReadExpressions.field layout owner "handle_table_shift".toList) = _
  rw [read_named decode context _ directoryType _ known]
  rfl

/-- The supplied hash expression performs its actual modular product before
loading the shift and invoking the guarded C unsigned shift operation. -/
theorem actual_hash_expression (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (directory : Ptr) (directoryType : CType) (handle : UInt32)
    (directoryLocal : context "index".toList = scalar directoryType (.ptr (some directory)))
    (handleLocal : context "handle".toList = scalar Source.uint32 (.u32 handle)) :
    read decode context (.binary .shiftRight
      (.binary .mul (Source.id "handle") (.unsignedInteger 2654435761))
      (Source.field "index" "handle_table_shift")) = homeProgram directory handle := by
  change ((read decode context (Source.id "handle") >>= fun value =>
    (pure (.u32 2654435761) : CProg CVal CVal) >>= fun multiplier =>
      binary .mul value multiplier) >>= fun product =>
    read decode context (Source.field "index" "handle_table_shift") >>= fun shift =>
      binary .shiftRight product shift) = _
  rw [read_named decode context _ Source.uint32 _ handleLocal,
    read_shift decode context directory directoryType directoryLocal]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl

theorem actual_home_body (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (directory : Ptr) (directoryType : CType) (handle : UInt32) (allowance fuel : Nat)
    (directoryLocal : context "index".toList = scalar directoryType (.ptr (some directory)))
    (handleLocal : context "handle".toList = scalar Source.uint32 (.u32 handle)) :
    executeScopedWith (services decode) layout allowance (fuel + 1) context Source.homeBody =
      (homeProgram directory handle >>= fun result =>
        pure (.finished (.returned context (some result)))) := by
  unfold Source.homeBody
  rw [executeScopedWith.eq_def]
  change (read decode context _ >>= fun result =>
    pure (ReadBlock.Result.finished (.returned context (some result)))) = _
  rw [actual_hash_expression decode context directory directoryType handle directoryLocal handleLocal]

theorem homeProgram_at_shift (handle shift : UInt32)
    (valid : shift.toNat < 32) :
    binary .shiftRight (.u32 (handle * 0x9E3779B1)) (.u32 shift) =
      pure (.u32 (home handle shift)) := by
  change resolved ((if shift.toNat < 32 then
    some (ScalarRead.Value.unsigned ((handle * 0x9E3779B1) >>> shift))
      else none).bind cell?) = _
  rw [if_pos valid]
  rfl

theorem unpackHandle_fits_uint32 (word : Nat) : unpackHandle word < 2 ^ 32 := by
  unfold unpackHandle
  split_ifs
  · have bound := Nat.mod_lt word (Nat.two_pow_pos 20)
    omega
  · have bound := Nat.mod_lt word (Nat.two_pow_pos 24)
    dsimp [classOneFirst]
    omega
  · have bound := Nat.mod_lt word (Nat.two_pow_pos 26)
    dsimp [classTwoFirst]
    omega
  · have bound := Nat.mod_lt word (Nat.two_pow_pos 26)
    dsimp [classThreeFirst]
    omega
  · have bound := Nat.mod_lt word (Nat.two_pow_pos 28)
    dsimp [handleLimit]
    omega

/-- Mathematical codec instance for the directory component. Its bit-level
meaning is already proved by `packedHandle_eq_native_bits`; composition with
the full C codec helper remains a separately named implementation boundary. -/
def decodedHandle (epoch : UInt32) : CProg CVal UInt32 :=
  pure (UInt32.ofNat (unpackHandle epoch.toNat))

theorem decodedHandle_comparison (epoch handle : UInt32) :
    (UInt32.ofNat (unpackHandle epoch.toNat) == handle) =
      decide (unpackHandle epoch.toNat = handle.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro same
    have number := congrArg UInt32.toNat same
    simpa only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (unpackHandle_fits_uint32 _)] using number
  · intro same
    apply UInt32.toNat.inj
    simpa only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (unpackHandle_fits_uint32 _)] using same

def loopContext (outer : Context) (mask slot : UInt32) : Context :=
  Function.update (Function.update outer "mask".toList (scalar Source.uint32 (.u32 mask)))
    "slot".toList (scalar Source.uint32 (.u32 slot))

def entryContext (outer : Context) (mask slot : UInt32) (entry : Option Ptr) : Context :=
  Function.update (loopContext outer mask slot) "entry".toList
    (scalar Source.entryType (.ptr entry))

theorem read_entry_null (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (entry : Option Ptr)
    (known : context "entry".toList = scalar Source.entryType (.ptr entry)) :
    (read decode context (.unary .not (Source.id "entry")) >>= truth) =
      CProg.ptrEq entry none := by
  change ((read decode context (Source.id "entry") >>= fun value =>
    truth value >>= fun yes => pure (.bool (!yes))) >>= truth) = _
  rw [read_named decode context _ Source.entryType _ known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, truth, Prog.bind_assoc,
    Bool.not_not]
  exact Prog.bind_ret _

theorem read_call_single (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (name : Name) (argument : CExpr) :
    read decode context (.call name [argument]) =
      (read decode context argument >>= fun value => calls decode name [value]) := by
  unfold read ObjectBindings.read
  rw [expressionWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl

theorem read_entry_handle (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (entry : Ptr)
    (known : context "entry".toList = scalar Source.entryType (.ptr (some entry))) :
    read decode context (.call "cetta_frame_handle".toList [Source.field "entry" "epoch"]) =
      (CProg.loadU32 entry >>= fun epoch => decode epoch >>= fun handle => pure (.u32 handle)) := by
  have epochRead : read decode context (Source.field "entry" "epoch") =
      (CProg.loadU32 entry >>= fun epoch => pure (.u32 epoch)) := by
    change (read decode context (Source.id "entry") >>= fun value =>
      field layout value "epoch".toList) = _
    rw [read_named decode context _ Source.entryType _ known]
    rfl
  rw [read_call_single, epochRead]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

theorem restore_entry_after_slot (outer : Context) (mask slot next : UInt32)
    (entry : Option Ptr) :
    Function.update (Function.update (entryContext outer mask slot entry) "slot".toList
      (scalar Source.uint32 (.u32 next))) "entry".toList
      (loopContext outer mask slot "entry".toList) = loopContext outer mask next := by
  funext name
  simp only [entryContext, loopContext, Function.update_apply]
  split_ifs <;> simp_all

theorem restore_entry (outer : Context) (mask slot : UInt32) (entry : Option Ptr) :
    Function.update (entryContext outer mask slot entry) "entry".toList
      (loopContext outer mask slot "entry".toList) = loopContext outer mask slot := by
  funext name
  simp only [entryContext, Function.update_apply]
  split_ifs <;> simp_all

theorem restore_loop_declarations (outer : Context) (mask : UInt32)
    (result : ReadBlock.Result UInt32) :
    ObjectBindings.restore "mask".toList (outer "mask".toList)
      (ObjectBindings.restore "slot".toList
        ((Function.update outer "mask".toList (scalar Source.uint32 (.u32 mask))) "slot".toList)
        (result.mapContext (loopContext outer mask))) =
      result.mapContext (fun _ => outer) := by
  have restored (slot : UInt32) :
      Function.update
        (Function.update (loopContext outer mask slot) "slot".toList
          ((Function.update outer "mask".toList (scalar Source.uint32 (.u32 mask))) "slot".toList))
        "mask".toList (outer "mask".toList) = outer := by
    funext name
    simp only [loopContext, Function.update_apply]
    split_ifs <;> simp_all
  cases result with
  | exhausted => rfl
  | finished flow =>
    cases flow <;> simp only [ObjectBindings.restore, ReadBlock.Result.mapContext,
      ReadBlock.Flow.mapContext, restored]

theorem read_call_pair (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (name : Name) (left right : CExpr) :
    read decode context (.call name [left, right]) =
      (read decode context left >>= fun first =>
        read decode context right >>= fun second => calls decode name [first, second]) := by
  unfold read ObjectBindings.read
  rw [expressionWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl

/-- The existing physical iteration with an effectful implementation of its
actual called identity helper. The helper is sequenced after the stored epoch
load and before the comparison; it is not identified with a pure codec. -/
def iteration (decode : UInt32 → CProg CVal UInt32) (directory : Ptr)
    (key mask slot : UInt32) : CProg CVal (ReadBlock.Result UInt32) := do
  let table ← CProg.loadPtr (directory + 9)
  match table with
  | none => CProg.undefined
  | some table =>
    let entry ← CProg.loadPtr (table + slot.toNat)
    let null ← CProg.ptrEq entry none
    if null then pure (.finished (.returned slot (some (.ptr none))))
    else match entry with
      | none => CProg.undefined
      | some entry =>
        let epoch ← CProg.loadU32 entry
        let handle ← decode epoch
        if handle = key then pure (.finished (.returned slot (some (.ptr (some entry)))))
        else pure (.finished (.next (advance slot mask)))

def search (decode : UInt32 → CProg CVal UInt32) (directory : Ptr)
    (key mask : UInt32) (fuel : Nat) (slot : UInt32) : CProg CVal (ReadBlock.Result UInt32) :=
  ReadBlock.whileWith (fun _ => pure true) (iteration decode directory key mask) fuel slot

theorem read_entry_comparison (decode : UInt32 → CProg CVal UInt32)
    (outer : Context) (mask slot handle : UInt32) (entry : Ptr)
    (handleLocal : outer "handle".toList = scalar Source.uint32 (.u32 handle)) :
    (read decode (entryContext outer mask slot (some entry))
      (.binary .eq (.call "cetta_frame_handle".toList [Source.field "entry" "epoch"])
        (Source.id "handle")) >>= truth) =
      (CProg.loadU32 entry >>= fun epoch => decode epoch >>= fun actual =>
        pure (decide (actual = handle))) := by
  change ((read decode (entryContext outer mask slot (some entry))
    (.call "cetta_frame_handle".toList [Source.field "entry" "epoch"]) >>= fun actual =>
      read decode (entryContext outer mask slot (some entry)) (Source.id "handle") >>=
        fun requested => binary .eq actual requested) >>= truth) = _
  rw [read_entry_handle _ _ entry (by simp [entryContext]),
    read_named _ _ _ Source.uint32 _ (by simpa [entryContext, loopContext] using handleLocal)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    binary, equal, ReadExpressions.scalar, ScalarRead.equal?, resolved, truth,
    Bool.beq_eq_decide_eq]


theorem read_entry_comparison_null (decode : UInt32 → CProg CVal UInt32) (context : Context)
    (known : context "entry".toList = scalar Source.entryType (.ptr none)) :
    (read decode context
      (.binary .eq (.call "cetta_frame_handle".toList [Source.field "entry" "epoch"])
        (Source.id "handle")) >>= truth) = CProg.undefined := by
  have epochRead : read decode context (Source.field "entry" "epoch") =
      CProg.undefined := by
    change (read decode context (Source.id "entry") >>= fun owner =>
      field layout owner "epoch".toList) = _
    rw [read_named _ _ "entry" Source.entryType (.ptr none) known]
    rfl
  change ((read decode context
    (.call "cetta_frame_handle".toList [Source.field "entry" "epoch"]) >>= fun actual =>
      read decode context (Source.id "handle") >>= fun wanted => binary .eq actual wanted)
        >>= truth) = _
  rw [read_call_single, epochRead]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  exact undefined_bind _

theorem slot_assignment (decode : UInt32 → CProg CVal UInt32) (outer : Context) (mask slot : UInt32) (entry : Option Ptr) :
    (services decode).assignment layout (entryContext outer mask slot entry)
      (.assign (Source.id "slot")
        (.binary .bitAnd (.binary .add (Source.id "slot") (.unsignedInteger 1))
          (Source.id "mask"))) =
      pure (Function.update (entryContext outer mask slot entry) "slot".toList
        (scalar Source.uint32 (.u32 (advance slot mask)))) := by
  dsimp only [services, ObjectBindings.services]
  change ObjectBindings.assignment (profile decode) layout
    (entryContext outer mask slot entry) _ = _
  unfold ObjectBindings.assignment
  dsimp only
  have typed : ScalarBytes.typeOf?
      (ObjectBindings.types (entryContext outer mask slot entry) (profile decode).outsideTypes)
      (Source.id "slot") (profile decode).fieldTypes = some Source.uint32 := by
    simp [ScalarBytes.typeOf?, Source.id, ObjectBindings.types, entryContext, loopContext, SourceRead.scalar]
  rw [typed]
  change (read decode (entryContext outer mask slot entry) _ >>= fun actual =>
    ObjectBindings.writeValue (profile decode) layout (entryContext outer mask slot entry)
      (Source.id "slot") actual) = _
  have rhs : read decode (entryContext outer mask slot entry)
      (.binary .bitAnd (.binary .add (Source.id "slot") (.unsignedInteger 1))
        (Source.id "mask")) = pure (.u32 (advance slot mask)) := by
    change ((read decode (entryContext outer mask slot entry) (Source.id "slot") >>=
      fun current => binary .add current (.u32 1)) >>= fun added =>
      read decode (entryContext outer mask slot entry) (Source.id "mask") >>=
        fun mask => binary .bitAnd added mask) = _
    rw [read_named _ _ "slot" Source.uint32 (.u32 slot) (by simp [entryContext, loopContext]),
      read_named _ _ "mask" Source.uint32 (.u32 mask) (by simp [entryContext, loopContext])]
    rfl
  rw [rhs]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  unfold Source.id
  rw [ObjectBindings.local_scalar_write_refines_existing_inventory _ _ _ _ Source.uint32
    (some (.u32 slot)) (.u32 (advance slot mask)) (by simp [entryContext, loopContext, SourceRead.scalar])]
  rfl

private theorem branch_control (decode : UInt32 → CProg CVal UInt32)
    (allowance fuel : Nat) (context : Context) (condition : CExpr)
    (yes no rest : List CStatement) :
    executeScopedWith (services decode) layout allowance (fuel + 1) context
      (.branch condition yes no :: rest) =
      ((read decode context condition >>= truth) >>= fun selected =>
        executeScopedWith (services decode) layout allowance fuel context
          (if selected then yes else no) >>= ReadBlock.resume
            (fun reached => executeScopedWith (services decode) layout allowance fuel reached rest)) := by
  rw [executeScopedWith.eq_def]
  simp only [services, Prog.bind_eq, Prog.bind_assoc]
  rfl

/-- Each iteration restores its private entry pointer before continuing or
returning. The retained slot and all older locals pass through the real
declaration, null test, epoch read and assignment. -/
theorem actual_iteration (decode : UInt32 → CProg CVal UInt32) (outer : Context) (directory : Ptr) (directoryType : CType)
    (mask slot handle : UInt32) (allowance : Nat)
    (directoryLocal : outer "index".toList = scalar directoryType (.ptr (some directory)))
    (handleLocal : outer "handle".toList = scalar Source.uint32 (.u32 handle)) :
    executeScopedWith (services decode) layout allowance 8
      (loopContext outer mask slot) Source.iteration =
      (iteration decode directory handle mask slot >>= fun result =>
        pure (result.mapContext (loopContext outer mask))) := by
  unfold Source.iteration
  rw [show 8 = 7 + 1 from rfl, scoped_initialized_declaration_keeps_continuation]
  dsimp only [services, ObjectBindings.services]
  change ObjectBindings.declaration (profile decode) (fun _ _ _ => CProg.undefined)
    layout (loopContext outer mask slot) Source.entryType "entry".toList
    (some (.index (Source.field "index" "handle_table") (Source.id "slot"))) _ = _
  rw [ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow _ _ _ _ _ _ _ (by rfl)]
  change (read decode (loopContext outer mask slot)
    (.index (Source.field "index" "handle_table") (Source.id "slot")) >>= _) = _
  rw [read_slot_pointer decode _ directory directoryType slot
    (by simpa [loopContext] using directoryLocal) (by simp [loopContext])]
  unfold iteration
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext table
  cases table with
  | none =>
    trans CProg.undefined
    · exact undefined_bind _
    · exact (undefined_bind _).symm
  | some table =>
    simp only [Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    congr 1
    funext entry
    change (executeScopedWith (services decode) layout allowance 7
      (entryContext outer mask slot entry)
      [.branch (.unary .not (Source.id "entry")) Source.nullReturn [],
       .branch (.binary .eq (.call "cetta_frame_handle".toList [Source.field "entry" "epoch"])
         (Source.id "handle")) [.return (some (Source.id "entry"))] [],
       .assign (Source.id "slot") (.binary .bitAnd
         (.binary .add (Source.id "slot") (.unsignedInteger 1)) (Source.id "mask"))] >>=
       fun result => pure (ObjectBindings.restore "entry".toList
         (loopContext outer mask slot "entry".toList) result)) = _
    rw [show 7 = 6 + 1 from rfl, branch_control,
      read_entry_null _ _ entry (by simp [entryContext])]
    simp only [Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext isNull
    cases isNull with
    | true =>
      simp only [↓reduceIte]
      change (pure (ObjectBindings.restore "entry".toList
        (loopContext outer mask slot "entry".toList)
        (.finished (.returned (entryContext outer mask slot entry) (some (.ptr none))))) :
          CProg CVal (ReadBlock.Result Context)) = _
      simp only [ObjectBindings.restore, ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext,
        restore_entry]
      rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      change (executeScopedWith (services decode) layout allowance 6
        (entryContext outer mask slot entry)
        [.branch (.binary .eq (.call "cetta_frame_handle".toList [Source.field "entry" "epoch"])
          (Source.id "handle")) [.return (some (Source.id "entry"))] [],
         .assign (Source.id "slot") (.binary .bitAnd
           (.binary .add (Source.id "slot") (.unsignedInteger 1)) (Source.id "mask"))] >>=
         fun result => pure (ObjectBindings.restore "entry".toList
           (loopContext outer mask slot "entry".toList) result)) = _
      rw [show 6 = 5 + 1 from rfl, branch_control]
      cases entry with
      | none =>
        rw [read_entry_comparison_null decode _ (by simp [entryContext])]
        simp only [Prog.bind_eq, Prog.bind_assoc]
        trans CProg.undefined
        · exact undefined_bind _
        · exact (undefined_bind _).symm
      | some entry =>
        rw [read_entry_comparison decode outer mask slot handle entry handleLocal]
        simp only [Prog.bind_eq, Prog.bind_assoc]
        congr 1
        funext epoch
        congr 1
        funext actual
        by_cases same : actual = handle
        · simp only [same, decide_true, ↓reduceIte, Prog.pure_eq, Prog.ret_bind]
          change (read decode (entryContext outer mask slot (some entry))
            (Source.id "entry") >>= fun value => pure (ObjectBindings.restore "entry".toList
              (loopContext outer mask slot "entry".toList)
                (.finished (.returned (entryContext outer mask slot (some entry)) (some value))))) = _
          rw [read_named _ _ "entry" Source.entryType (.ptr (some entry)) (by simp [entryContext])]
          simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, ObjectBindings.restore,
            ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext, restore_entry]
        · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte,
            Prog.pure_eq, Prog.ret_bind]
          change (executeScopedWith (services decode) layout allowance 5
            (entryContext outer mask slot (some entry))
            [.assign (Source.id "slot") (.binary .bitAnd
              (.binary .add (Source.id "slot") (.unsignedInteger 1)) (Source.id "mask"))] >>=
            fun result => pure (ObjectBindings.restore "entry".toList
              (loopContext outer mask slot "entry".toList) result)) = _
          rw [show 5 = 4 + 1 from rfl, scoped_assignment_keeps_continuation, slot_assignment decode]
          change (pure (ObjectBindings.restore "entry".toList
            (loopContext outer mask slot "entry".toList)
            (.finished (.next (Function.update (entryContext outer mask slot (some entry))
              "slot".toList (scalar Source.uint32 (.u32 (advance slot mask))))))) :
              CProg CVal (ReadBlock.Result Context)) = _
          simp only [ObjectBindings.restore, ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext,
            restore_entry_after_slot]
          rfl

theorem actual_loop_uses_search (decode : UInt32 → CProg CVal UInt32) (outer : Context) (directory : Ptr) (directoryType : CType)
    (mask slot handle : UInt32) (allowance : Nat)
    (directoryLocal : outer "index".toList = scalar directoryType (.ptr (some directory)))
    (handleLocal : outer "handle".toList = scalar Source.uint32 (.u32 handle)) :
    ReadBlock.whileWith
      (fun context => read decode context (.bool true) >>= truth)
      (fun context => executeScopedWith (services decode) layout allowance 8 context Source.iteration)
      allowance (loopContext outer mask slot) =
      (search decode directory handle mask allowance slot >>= fun result =>
        pure (result.mapContext (loopContext outer mask))) :=
  ReadBlock.while_context_extension (loopContext outer mask) (fun _ => pure true)
    (iteration decode directory handle mask) _ _ (fun _ => rfl)
    (fun reached => actual_iteration decode outer directory directoryType mask reached handle allowance
      directoryLocal handleLocal) allowance slot

private theorem resume_empty (result : ReadBlock.Result Context)
    (decode : UInt32 → CProg CVal UInt32) (allowance fuel : Nat) :
    ReadBlock.resume
      (fun reached => executeScopedWith (services decode) layout allowance fuel reached []) result =
      pure result := by
  cases result with
  | exhausted => rfl
  | finished flow => cases flow <;> simp only [ReadBlock.resume, executeScopedWith.eq_def]

/-- The parsed loop uses the physical iteration allowance and its actual body;
there is no supplied loop-result oracle. -/
theorem actual_while_statement (decode : UInt32 → CProg CVal UInt32) (outer : Context) (directory : Ptr) (directoryType : CType)
    (mask slot handle : UInt32) (allowance : Nat)
    (directoryLocal : outer "index".toList = scalar directoryType (.ptr (some directory)))
    (handleLocal : outer "handle".toList = scalar Source.uint32 (.u32 handle)) :
    executeScopedWith (services decode) layout allowance 9
      (loopContext outer mask slot) [.whileLoop (.bool true) Source.iteration] =
      (search decode directory handle mask allowance slot >>= fun result =>
        pure (result.mapContext (loopContext outer mask))) := by
  rw [show 9 = 8 + 1 from rfl,
    scoped_while_keeps_guard_body_and_continuation _ _ _ _ _ _ _ _ (by rfl)]
  change (ReadBlock.whileWith
    (fun context => read decode context (.bool true) >>= truth)
    (fun context => executeScopedWith (services decode) layout allowance 8 context Source.iteration)
    allowance (loopContext outer mask slot) >>= _) = _
  rw [actual_loop_uses_search decode outer directory directoryType mask slot handle allowance
    directoryLocal handleLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext result
  exact resume_empty _ decode allowance 8

/-- The whole lookup control retains the initial table test, the mask load,
the actual hash-helper operation, typed slot conversion and physical search.
Only the local lexical context is discarded by this function observer. -/
def lookupProgram (decode : UInt32 → CProg CVal UInt32) (directory : Ptr) (handle : UInt32) (allowance : Nat) :
    CProg CVal (ReadBlock.Result Unit) := do
  let table ← CProg.loadPtr (directory + 9)
  let null ← CProg.ptrEq table none
  if null then pure (.finished (.returned () (some (.ptr none))))
  else
    let mask ← CProg.loadU32 (directory + 10)
    let initial ← homeProgram directory handle
    let slot ← word initial
    let result ← search decode directory handle mask allowance slot
    pure (result.mapContext (fun _ => ()))

theorem read_home_call (decode : UInt32 → CProg CVal UInt32) (context : Context) (directory : Ptr) (directoryType : CType)
    (handle : UInt32)
    (directoryLocal : context "index".toList = scalar directoryType (.ptr (some directory)))
    (handleLocal : context "handle".toList = scalar Source.uint32 (.u32 handle)) :
    read decode context (.call "bindings_frame_table_home".toList
      [Source.id "index", Source.id "handle"]) = homeProgram directory handle := by
  rw [read_call_pair, read_named _ _ _ directoryType _ directoryLocal,
    read_named _ _ _ Source.uint32 _ handleLocal]
  rfl

theorem read_mask (decode : UInt32 → CProg CVal UInt32) (context : Context) (directory : Ptr) (directoryType : CType)
    (known : context "index".toList = scalar directoryType (.ptr (some directory))) :
    read decode context (Source.field "index" "handle_table_mask") =
      (CProg.loadU32 (directory + 10) >>= fun value => pure (.u32 value)) := by
  change (read decode context (Source.id "index") >>= fun owner =>
    ReadExpressions.field layout owner "handle_table_mask".toList) = _
  rw [read_named _ _ _ directoryType _ known]
  rfl

theorem read_table_null (decode : UInt32 → CProg CVal UInt32) (context : Context) (directory : Ptr) (directoryType : CType)
    (known : context "index".toList = scalar directoryType (.ptr (some directory))) :
    (read decode context (.unary .not (Source.field "index" "handle_table")) >>= truth) =
      (CProg.loadPtr (directory + 9) >>= fun table => CProg.ptrEq table none) := by
  change ((read decode context (Source.field "index" "handle_table") >>= fun value =>
    truth value >>= fun yes => pure (.bool (!yes))) >>= truth) = _
  rw [read_table _ _ directory directoryType known]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth,
    Bool.not_not, Prog.bind_ret]

/-- Actual mask/slot declarations restore both shadowed bindings on every
completed flow, while exhaustion remains exhaustion. -/
theorem actual_local_declarations (decode : UInt32 → CProg CVal UInt32) (outer : Context) (directory : Ptr) (directoryType : CType)
    (handle : UInt32) (allowance : Nat)
    (directoryLocal : outer "index".toList = scalar directoryType (.ptr (some directory)))
    (handleLocal : outer "handle".toList = scalar Source.uint32 (.u32 handle)) :
    executeScopedWith (services decode) layout allowance 11 outer Source.lookupBody.tail =
      (CProg.loadU32 (directory + 10) >>= fun mask =>
        homeProgram directory handle >>= fun initial => word initial >>= fun slot =>
          search decode directory handle mask allowance slot >>= fun result =>
            pure (result.mapContext (fun _ => outer))) := by
  unfold Source.lookupBody
  simp only [List.tail_cons]
  rw [show 11 = 10 + 1 from rfl, scoped_initialized_declaration_keeps_continuation]
  dsimp only [services, ObjectBindings.services]
  rw [ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow _ _ _ _ _ _ _ (by rfl)]
  change (read decode outer (Source.field "index" "handle_table_mask") >>= _) = _
  rw [read_mask decode outer directory directoryType directoryLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext mask
  change (executeScopedWith (services decode) layout allowance 10
    (Function.update outer "mask".toList (scalar Source.uint32 (.u32 mask)))
    [.declare Source.uint32 "slot".toList
      (.call "bindings_frame_table_home".toList [Source.id "index", Source.id "handle"]),
     .whileLoop (.bool true) Source.iteration] >>= fun result =>
       pure (ObjectBindings.restore "mask".toList (outer "mask".toList) result)) = _
  rw [show 10 = 9 + 1 from rfl, scoped_initialized_declaration_keeps_continuation]
  dsimp only [services, ObjectBindings.services]
  rw [ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow _ _ _ _ _ _ _ (by rfl)]
  change ((read decode
    (Function.update outer "mask".toList (scalar Source.uint32 (.u32 mask)))
      (.call "bindings_frame_table_home".toList [Source.id "index", Source.id "handle"]) >>= _) >>= _) = _
  rw [read_home_call decode _ directory directoryType handle
    (by simpa using directoryLocal) (by simpa using handleLocal)]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext initial
  have initialWord : ObjectBindings.scalarInitialValue (profile decode) Source.uint32 initial =
      (word initial >>= fun slot => pure (.u32 slot)) := by rfl
  rw [initialWord]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  change (word initial >>= fun slot =>
    executeScopedWith (services decode) layout allowance 9
      (loopContext outer mask slot) [.whileLoop (.bool true) Source.iteration] >>= fun result =>
        pure (ObjectBindings.restore "mask".toList (outer "mask".toList)
          (ObjectBindings.restore "slot".toList
            ((Function.update outer "mask".toList (scalar Source.uint32 (.u32 mask))) "slot".toList)
              result))) = _
  congr 1
  funext slot
  rw [actual_while_statement decode outer directory directoryType mask slot handle allowance
    directoryLocal handleLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    restore_loop_declarations]

/-- The entire parsed source body is the physical lookup operation tree,
including its initial null test and scoped hash/slot declarations. -/
theorem actual_lookup_body (decode : UInt32 → CProg CVal UInt32) (outer : Context) (directory : Ptr) (directoryType : CType)
    (handle : UInt32) (allowance : Nat)
    (directoryLocal : outer "index".toList = scalar directoryType (.ptr (some directory)))
    (handleLocal : outer "handle".toList = scalar Source.uint32 (.u32 handle)) :
    executeScopedWith (services decode) layout allowance 12 outer Source.lookupBody =
      (lookupProgram decode directory handle allowance >>= fun result =>
        pure (result.mapContext (fun _ => outer))) := by
  change executeScopedWith _ _ _ _ _
    (.branch (.unary .not (Source.field "index" "handle_table")) Source.nullReturn [] ::
      Source.lookupBody.tail) = _
  rw [show 12 = 11 + 1 from rfl, branch_control,
    read_table_null decode outer directory directoryType directoryLocal]
  unfold lookupProgram
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext table
  congr 1
  funext isNull
  cases isNull with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Prog.bind_assoc]
    change executeScopedWith (services decode) layout allowance 11 outer
      Source.lookupBody.tail = _
    rw [actual_local_declarations decode outer directory directoryType handle allowance
      directoryLocal handleLocal]
    simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
    congr 1
    funext mask
    congr 1
    funext initial
    congr 1
    funext slot
    congr 1
    funext result
    rw [ReadBlock.result_context_map_composition]
    rfl

private theorem codec_equal (epoch handle : UInt32) :
    UInt32.ofNat (unpackHandle epoch.toNat) = handle ↔
      unpackHandle epoch.toNat = handle.toNat := by
  constructor
  · intro same
    have equal := congrArg UInt32.toNat same
    simpa only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (unpackHandle_fits_uint32 _)] using equal
  · intro same
    apply UInt32.toNat.inj
    simpa only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (unpackHandle_fits_uint32 _)] using same

/-- The earlier mathematical codec is the pure instance of the same helper
parameter. Only that explicit instance has the shorter operation trace. -/
theorem iteration_decodedHandle (directory : Ptr) (handle mask slot : UInt32) :
    iteration decodedHandle directory handle mask slot =
      Physical.iteration directory handle.toNat mask slot := by
  simp only [iteration, Physical.iteration, decodedHandle, Prog.bind_eq,
    Prog.pure_eq, Prog.ret_bind, codec_equal]

theorem search_decodedHandle (directory : Ptr) (handle mask : UInt32)
    (fuel : Nat) (slot : UInt32) :
    search decodedHandle directory handle mask fuel slot =
      Physical.search directory handle.toNat mask fuel slot := by
  have same : iteration decodedHandle directory handle mask =
      Physical.iteration directory handle.toNat mask := by
    funext slot
    exact iteration_decodedHandle directory handle mask slot
  rw [search, Physical.search, same]

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.SourceRead

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.SourceRead
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open CellPermission
open Mettapedia.Machines.IncrementalConformance

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

private theorem loadPtr_at {address : Ptr} {value : Option Ptr} {heap : Heap L}
    {post : Option Ptr → Heap L → Prop} (reads : Reads address (.ptr value) heap)
    (holds : post value heap) : (CProg.loadPtr address).wp act post heap := by
  refine wp_consequence act
    (loadPtr_rule (P := fun reached => reached = heap) (q := value) ?_) rfl ?_
  · rintro reached rfl
    exact reads
  · rintro actual reached ⟨rfl, rfl⟩
    exact holds

private theorem loadU32_at {address : Ptr} {value : UInt32} {heap : Heap L}
    {post : UInt32 → Heap L → Prop} (reads : Reads address (.u32 value) heap)
    (holds : post value heap) : (CProg.loadU32 address).wp act post heap := by
  refine wp_consequence act
    (loadU32_rule (P := fun reached => reached = heap) (n := value) ?_) rfl ?_
  · rintro reached rfl
    exact reads
  · rintro actual reached ⟨rfl, rfl⟩
    exact holds

/-- Typed directory fields, a live table pointer and the actual physical
cell inventory. This is storage evidence rather than a lookup-result premise. -/
def LookupReads (directory : Ptr) (mask shift : UInt32)
    (table : Fin (2 ^ (32 - shift.toNat)) → Option (Nat × Ptr))
    (heap : Heap L) : Prop :=
  ∃ tableAddress,
    Reads (directory + 9) (.ptr (some tableAddress)) heap ∧
    ValidAt tableAddress heap ∧
    Reads (directory + 10) (.u32 mask) heap ∧
    Reads (directory + 11) (.u32 shift) heap ∧
    ∀ position, Physical.CellRead directory (UInt32.ofNat position.val) (table position) heap

/-- The whole lookup terminates with the independent finite-probe result
under the native directory's power-of-two, half-load and physical inventory
conditions. Its initial hash reads are included and the same heap is retained. -/
theorem lookup_returns_inventory (directory : Ptr) (handle mask shift : UInt32)
    (validShift : shift.toNat < 32)
    (maskShape : mask.toNat = 2 ^ (32 - shift.toNat) - 1)
    (table : Fin (2 ^ (32 - shift.toNat)) → Option (Nat × Ptr))
    (loaded : (List.ofFn table).countP Option.isSome ≤ 2 ^ (32 - shift.toNat) / 2)
    (allowance : Nat) (enough : 2 ^ (32 - shift.toNat) ≤ allowance)
    (pre : Heap L → Prop)
    (inventory : ∀ heap, pre heap → LookupReads directory mask shift table heap) :
    CTriple pre (lookupProgram decodedHandle directory handle allowance)
      (fun result heap => pre heap ∧
        result = .finished (.returned () (some (.ptr
          (InternProbe.probe handle.toNat
            (sequence table ⟨(home handle shift).toNat,
              home_within_capacity handle shift validShift⟩)).1)))) := by
  intro heap held
  obtain ⟨tableAddress, readTable, liveTable, readMask, readShift, _⟩ := inventory heap held
  change (lookupProgram decodedHandle directory handle allowance).wp act _ heap
  rw [lookupProgram, wp_bind']
  apply loadPtr_at readTable
  rw [wp_bind']
  apply wp_ptrEq (p := some tableAddress) (q := none)
    (show ValidOpt heap (some tableAddress) from liveTable) (by trivial)
  simp only [Option.some_ne_none, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply loadU32_at readMask
  rw [homeProgram, wp_bind', wp_bind']
  apply loadU32_at readShift
  rw [homeProgram_at_shift handle shift validShift]
  simp only [Prog.pure_eq, Prog.bind_eq, wp_ret, Prog.ret_bind, word]
  rw [search_decodedHandle, wp_bind]
  apply wp_mono act (Q := fun result reached => pre reached ∧ ∃ finalSlot,
    result = .finished (.returned finalSlot
      (some (.ptr (InternProbe.probe handle.toNat
        (sequence table ⟨(home handle shift).toNat,
          home_within_capacity handle shift validShift⟩)).1))))
  · rintro result reached ⟨retained, finalSlot, rfl⟩
    simpa [wp_pure, wp_ret, ReadBlock.Result.mapContext,
      ReadBlock.Flow.mapContext] using retained
  · exact Physical.search_returns_inventory directory handle.toNat mask (home handle shift)
      (32 - shift.toNat) (Nat.sub_le _ _) maskShape
      (home_within_capacity handle shift validShift) table loaded allowance enough pre
      (fun reached owns => (inventory reached owns).choose_spec.2.2.2.2) heap held

/-- The actual parsed source body inherits the finite inventory theorem. The
caller context is restored after successful return; no loop-service adequacy
hypothesis is supplied. -/
theorem parsed_lookup_returns_inventory (outer : Context) (directory : Ptr)
    (directoryType : Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.CType)
    (handle mask shift : UInt32) (validShift : shift.toNat < 32)
    (maskShape : mask.toNat = 2 ^ (32 - shift.toNat) - 1)
    (table : Fin (2 ^ (32 - shift.toNat)) → Option (Nat × Ptr))
    (loaded : (List.ofFn table).countP Option.isSome ≤ 2 ^ (32 - shift.toNat) / 2)
    (allowance : Nat) (enough : 2 ^ (32 - shift.toNat) ≤ allowance)
    (directoryLocal : outer "index".toList = scalar directoryType (.ptr (some directory)))
    (handleLocal : outer "handle".toList = scalar Source.uint32 (.u32 handle))
    (pre : Heap L → Prop)
    (inventory : ∀ heap, pre heap → LookupReads directory mask shift table heap) :
    CTriple pre
      (StatementBlock.executeScopedWith (services decodedHandle) layout allowance 12 outer Source.lookupBody)
      (fun result heap => pre heap ∧
        result = .finished (.returned outer (some (.ptr
          (InternProbe.probe handle.toNat
            (sequence table ⟨(home handle shift).toNat,
              home_within_capacity handle shift validShift⟩)).1)))) := by
  rw [actual_lookup_body decodedHandle outer directory directoryType handle allowance directoryLocal handleLocal]
  intro heap held
  change (lookupProgram decodedHandle directory handle allowance >>= fun result =>
    pure (result.mapContext (fun _ => outer))).wp act _ heap
  rw [wp_bind']
  refine wp_mono act ?_
    (lookup_returns_inventory directory handle mask shift validShift maskShape table loaded
      allowance enough pre inventory heap held)
  rintro result reached ⟨retained, rfl⟩
  simpa [wp_pure, wp_ret, ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext] using retained

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.SourceRead


end NativeDirectoryLookupPackage


section NativeIdentityHelperPackage

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentitySource
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def id (name : String) : CExpr := .identifier name.toList
def out (name : String) : CExpr := .field (id "out") name.toList true
def uint (value : Nat) : CExpr := .unsignedInteger value
def shift (bits : Nat) : CExpr := .binary .shiftRight (id "identity") (.decimal bits)
def mask (bits : Nat) : CExpr := .binary .bitAnd (id "identity") (uint bits)
def assign (name : String) (value : CExpr) : CStatement := .assign (out name) value
def partsType : CType := ⟨"CettaFrameIdentityParts".toList, 0⟩
def types : TypeNames := ["CettaFrameIdentity".toList, "CettaFrameIdentityParts".toList,
  "uint32_t".toList, "bool".toList, "void".toList]

def class0 : List CStatement :=
  [assign "handle" (.binary .bitAnd (id "identity") (id "CETTA_FRAME_HANDLE_MASK")),
   assign "generation" (shift 20),
   assign "generation_max" (id "CETTA_FRAME_GENERATION_MAX")]

def class1 : List CStatement :=
  [assign "handle" (.binary .add (id "CETTA_FRAME_CLASS1_FIRST") (mask 16777215)),
   assign "generation" (.binary .bitAnd (shift 24) (uint 63)),
   assign "generation_max" (uint 62)]

def class2 : List CStatement :=
  [assign "handle" (.binary .add (id "CETTA_FRAME_CLASS2_FIRST") (mask 67108863)),
   assign "generation" (.binary .bitAnd (shift 26) (uint 7)),
   assign "generation_max" (uint 6)]

def class3 : List CStatement :=
  [assign "handle" (.binary .add (id "CETTA_FRAME_CLASS3_FIRST") (mask 67108863)),
   assign "generation" (.binary .bitAnd (shift 26) (uint 3)),
   assign "generation_max" (uint 2)]

def outside : List CStatement :=
  [assign "handle" (.binary .add (id "CETTA_FRAME_HANDLE_LIMIT") (mask 268435455)),
   assign "generation" (uint 0), assign "generation_max" (uint 0),
   .return (some (.bool false))]

def partsBody : List CStatement :=
  [.branch (.binary .eq (shift 31) (uint 0)) class0
     [.branch (.binary .eq (shift 30) (uint 2)) class1
       [.branch (.binary .eq (shift 29) (uint 6)) class2
         [.branch (.binary .eq (shift 28) (uint 14)) class3 outside]]],
   .return (some (.binary .and
     (.binary .and
       (.binary .and (.binary .ne (out "handle") (uint 0))
         (.binary .lt (out "handle") (id "CETTA_FRAME_HANDLE_LIMIT")))
       (.binary .ne (out "generation") (uint 0)))
     (.binary .le (out "generation") (out "generation_max"))))]

def wrapperBody (field : String) : List CStatement :=
  [.declareUninitialized partsType "parts".toList,
   .effect (.cast ⟨"void".toList, 0⟩ (.call "cetta_frame_identity_parts".toList
     [id "identity", .unary .address (id "parts")])),
   .return (some (.field (id "parts") field.toList false))]

def handleBody : List CStatement := wrapperBody "handle"
def generationBody : List CStatement := wrapperBody "generation"

private def partsPiece0 : String × List Token :=
  ("{\n", [.punctuation ['{']])

private theorem partsPiece0_lex : partsPiece0.1.toList.foldl step initial =
    completed partsPiece0.2 := by decide +kernel

private def partsPiece1 : String × List Token :=
  ("    if ((identity >> 31) == 0u) {\n", [.identifier ['i', 'f'], .punctuation ['('], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['>', '>'], .number ['3', '1'], .punctuation [')'], .punctuation ['=', '='], .number ['0', 'u'], .punctuation [')'], .punctuation ['{']])

private theorem partsPiece1_lex : partsPiece1.1.toList.foldl step initial =
    completed partsPiece1.2 := by decide +kernel

private def partsPiece2 : String × List Token :=
  ("        out->handle = identity & CETTA_FRAME_HANDLE_MASK;\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['h', 'a', 'n', 'd', 'l', 'e'], .punctuation ['='], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['&'], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'F', 'R', 'A', 'M', 'E', '_', 'H', 'A', 'N', 'D', 'L', 'E', '_', 'M', 'A', 'S', 'K'], .punctuation [';']])

private theorem partsPiece2_lex : partsPiece2.1.toList.foldl step initial =
    completed partsPiece2.2 := by decide +kernel

private def partsPiece3 : String × List Token :=
  ("        out->generation = identity >> 20;\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n'], .punctuation ['='], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['>', '>'], .number ['2', '0'], .punctuation [';']])

private theorem partsPiece3_lex : partsPiece3.1.toList.foldl step initial =
    completed partsPiece3.2 := by decide +kernel

private def partsPiece4 : String × List Token :=
  ("        out->generation_max = CETTA_FRAME_GENERATION_MAX;\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n', '_', 'm', 'a', 'x'], .punctuation ['='], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'F', 'R', 'A', 'M', 'E', '_', 'G', 'E', 'N', 'E', 'R', 'A', 'T', 'I', 'O', 'N', '_', 'M', 'A', 'X'], .punctuation [';']])

private theorem partsPiece4_lex : partsPiece4.1.toList.foldl step initial =
    completed partsPiece4.2 := by decide +kernel

private def partsPiece5 : String × List Token :=
  ("    } else if ((identity >> 30) == 2u) {\n", [.punctuation ['}'], .identifier ['e', 'l', 's', 'e'], .identifier ['i', 'f'], .punctuation ['('], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['>', '>'], .number ['3', '0'], .punctuation [')'], .punctuation ['=', '='], .number ['2', 'u'], .punctuation [')'], .punctuation ['{']])

private theorem partsPiece5_lex : partsPiece5.1.toList.foldl step initial =
    completed partsPiece5.2 := by decide +kernel

private def partsPiece6 : String × List Token :=
  ("        out->handle = CETTA_FRAME_CLASS1_FIRST + (identity & UINT32_C(0x00ffffff));\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['h', 'a', 'n', 'd', 'l', 'e'], .punctuation ['='], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'L', 'A', 'S', 'S', '1', '_', 'F', 'I', 'R', 'S', 'T'], .punctuation ['+'], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['&'], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '0', '0', 'f', 'f', 'f', 'f', 'f', 'f'], .punctuation [')'], .punctuation [')'], .punctuation [';']])

private theorem partsPiece6_lex : partsPiece6.1.toList.foldl step initial =
    completed partsPiece6.2 := by decide +kernel

private def partsPiece7 : String × List Token :=
  ("        out->generation = (identity >> 24) & UINT32_C(0x3f);\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n'], .punctuation ['='], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['>', '>'], .number ['2', '4'], .punctuation [')'], .punctuation ['&'], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '3', 'f'], .punctuation [')'], .punctuation [';']])

private theorem partsPiece7_lex : partsPiece7.1.toList.foldl step initial =
    completed partsPiece7.2 := by decide +kernel

private def partsPiece8 : String × List Token :=
  ("        out->generation_max = UINT32_C(0x3e);\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n', '_', 'm', 'a', 'x'], .punctuation ['='], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '3', 'e'], .punctuation [')'], .punctuation [';']])

private theorem partsPiece8_lex : partsPiece8.1.toList.foldl step initial =
    completed partsPiece8.2 := by decide +kernel

private def partsPiece9 : String × List Token :=
  ("    } else if ((identity >> 29) == 6u) {\n", [.punctuation ['}'], .identifier ['e', 'l', 's', 'e'], .identifier ['i', 'f'], .punctuation ['('], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['>', '>'], .number ['2', '9'], .punctuation [')'], .punctuation ['=', '='], .number ['6', 'u'], .punctuation [')'], .punctuation ['{']])

private theorem partsPiece9_lex : partsPiece9.1.toList.foldl step initial =
    completed partsPiece9.2 := by decide +kernel

private def partsPiece10 : String × List Token :=
  ("        out->handle = CETTA_FRAME_CLASS2_FIRST + (identity & UINT32_C(0x03ffffff));\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['h', 'a', 'n', 'd', 'l', 'e'], .punctuation ['='], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'L', 'A', 'S', 'S', '2', '_', 'F', 'I', 'R', 'S', 'T'], .punctuation ['+'], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['&'], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '0', '3', 'f', 'f', 'f', 'f', 'f', 'f'], .punctuation [')'], .punctuation [')'], .punctuation [';']])

private theorem partsPiece10_lex : partsPiece10.1.toList.foldl step initial =
    completed partsPiece10.2 := by decide +kernel

private def partsPiece11 : String × List Token :=
  ("        out->generation = (identity >> 26) & UINT32_C(0x7);\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n'], .punctuation ['='], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['>', '>'], .number ['2', '6'], .punctuation [')'], .punctuation ['&'], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '7'], .punctuation [')'], .punctuation [';']])

private theorem partsPiece11_lex : partsPiece11.1.toList.foldl step initial =
    completed partsPiece11.2 := by decide +kernel

private def partsPiece12 : String × List Token :=
  ("        out->generation_max = UINT32_C(0x6);\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n', '_', 'm', 'a', 'x'], .punctuation ['='], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '6'], .punctuation [')'], .punctuation [';']])

private theorem partsPiece12_lex : partsPiece12.1.toList.foldl step initial =
    completed partsPiece12.2 := by decide +kernel

private def partsPiece13 : String × List Token :=
  ("    } else if ((identity >> 28) == 14u) {\n", [.punctuation ['}'], .identifier ['e', 'l', 's', 'e'], .identifier ['i', 'f'], .punctuation ['('], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['>', '>'], .number ['2', '8'], .punctuation [')'], .punctuation ['=', '='], .number ['1', '4', 'u'], .punctuation [')'], .punctuation ['{']])

private theorem partsPiece13_lex : partsPiece13.1.toList.foldl step initial =
    completed partsPiece13.2 := by decide +kernel

private def partsPiece14 : String × List Token :=
  ("        out->handle = CETTA_FRAME_CLASS3_FIRST + (identity & UINT32_C(0x03ffffff));\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['h', 'a', 'n', 'd', 'l', 'e'], .punctuation ['='], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'L', 'A', 'S', 'S', '3', '_', 'F', 'I', 'R', 'S', 'T'], .punctuation ['+'], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['&'], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '0', '3', 'f', 'f', 'f', 'f', 'f', 'f'], .punctuation [')'], .punctuation [')'], .punctuation [';']])

private theorem partsPiece14_lex : partsPiece14.1.toList.foldl step initial =
    completed partsPiece14.2 := by decide +kernel

private def partsPiece15 : String × List Token :=
  ("        out->generation = (identity >> 26) & UINT32_C(0x3);\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n'], .punctuation ['='], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['>', '>'], .number ['2', '6'], .punctuation [')'], .punctuation ['&'], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '3'], .punctuation [')'], .punctuation [';']])

private theorem partsPiece15_lex : partsPiece15.1.toList.foldl step initial =
    completed partsPiece15.2 := by decide +kernel

private def partsPiece16 : String × List Token :=
  ("        out->generation_max = UINT32_C(0x2);\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n', '_', 'm', 'a', 'x'], .punctuation ['='], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '2'], .punctuation [')'], .punctuation [';']])

private theorem partsPiece16_lex : partsPiece16.1.toList.foldl step initial =
    completed partsPiece16.2 := by decide +kernel

private def partsPiece17 : String × List Token :=
  ("    } else {\n", [.punctuation ['}'], .identifier ['e', 'l', 's', 'e'], .punctuation ['{']])

private theorem partsPiece17_lex : partsPiece17.1.toList.foldl step initial =
    completed partsPiece17.2 := by decide +kernel

private def partsPiece18 : String × List Token :=
  ("        out->handle = CETTA_FRAME_HANDLE_LIMIT + (identity & UINT32_C(0x0fffffff));\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['h', 'a', 'n', 'd', 'l', 'e'], .punctuation ['='], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'F', 'R', 'A', 'M', 'E', '_', 'H', 'A', 'N', 'D', 'L', 'E', '_', 'L', 'I', 'M', 'I', 'T'], .punctuation ['+'], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation ['&'], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '0', 'f', 'f', 'f', 'f', 'f', 'f', 'f'], .punctuation [')'], .punctuation [')'], .punctuation [';']])

private theorem partsPiece18_lex : partsPiece18.1.toList.foldl step initial =
    completed partsPiece18.2 := by decide +kernel

private def partsPiece19 : String × List Token :=
  ("        out->generation = 0u;\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n'], .punctuation ['='], .number ['0', 'u'], .punctuation [';']])

private theorem partsPiece19_lex : partsPiece19.1.toList.foldl step initial =
    completed partsPiece19.2 := by decide +kernel

private def partsPiece20 : String × List Token :=
  ("        out->generation_max = 0u;\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n', '_', 'm', 'a', 'x'], .punctuation ['='], .number ['0', 'u'], .punctuation [';']])

private theorem partsPiece20_lex : partsPiece20.1.toList.foldl step initial =
    completed partsPiece20.2 := by decide +kernel

private def partsPiece21 : String × List Token :=
  ("        return false;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['f', 'a', 'l', 's', 'e'], .punctuation [';']])

private theorem partsPiece21_lex : partsPiece21.1.toList.foldl step initial =
    completed partsPiece21.2 := by decide +kernel

private def partsPiece22 : String × List Token :=
  ("    }\n", [.punctuation ['}']])

private theorem partsPiece22_lex : partsPiece22.1.toList.foldl step initial =
    completed partsPiece22.2 := by decide +kernel

private def partsPiece23 : String × List Token :=
  ("    return out->handle != 0u && out->handle < CETTA_FRAME_HANDLE_LIMIT &&\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['h', 'a', 'n', 'd', 'l', 'e'], .punctuation ['!', '='], .number ['0', 'u'], .punctuation ['&', '&'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['h', 'a', 'n', 'd', 'l', 'e'], .punctuation ['<'], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'F', 'R', 'A', 'M', 'E', '_', 'H', 'A', 'N', 'D', 'L', 'E', '_', 'L', 'I', 'M', 'I', 'T'], .punctuation ['&', '&']])

private theorem partsPiece23_lex : partsPiece23.1.toList.foldl step initial =
    completed partsPiece23.2 := by decide +kernel

private def partsPiece24 : String × List Token :=
  ("           out->generation != 0u && out->generation <= out->generation_max;\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n'], .punctuation ['!', '='], .number ['0', 'u'], .punctuation ['&', '&'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n'], .punctuation ['<', '='], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n', '_', 'm', 'a', 'x'], .punctuation [';']])

private theorem partsPiece24_lex : partsPiece24.1.toList.foldl step initial =
    completed partsPiece24.2 := by decide +kernel

private def partsPiece25 : String × List Token :=
  ("}", [.punctuation ['}']])

private theorem partsPiece25_lex : partsPiece25.1.toList.foldl step initial =
    completed partsPiece25.2 := by decide +kernel

private def partsPieces : List (String × List Token) :=
  [partsPiece0, partsPiece1, partsPiece2, partsPiece3, partsPiece4, partsPiece5, partsPiece6, partsPiece7, partsPiece8, partsPiece9, partsPiece10, partsPiece11, partsPiece12, partsPiece13, partsPiece14, partsPiece15, partsPiece16, partsPiece17, partsPiece18, partsPiece19, partsPiece20, partsPiece21, partsPiece22, partsPiece23, partsPiece24, partsPiece25]

def partsSource : String := String.join (partsPieces.map Prod.fst)
def partsTokens : List Token := partsPieces.flatMap Prod.snd

theorem parts_lex : lex partsSource.toList = .ok partsTokens := by
  apply lex_completed_string_pieces
  simp only [partsPieces, List.forall_cons]
  exact ⟨partsPiece0_lex, partsPiece1_lex, partsPiece2_lex, partsPiece3_lex, partsPiece4_lex, partsPiece5_lex, partsPiece6_lex, partsPiece7_lex, partsPiece8_lex, partsPiece9_lex, partsPiece10_lex, partsPiece11_lex, partsPiece12_lex, partsPiece13_lex, partsPiece14_lex, partsPiece15_lex, partsPiece16_lex, partsPiece17_lex, partsPiece18_lex, partsPiece19_lex, partsPiece20_lex, partsPiece21_lex, partsPiece22_lex, partsPiece23_lex, partsPiece24_lex, partsPiece25_lex, trivial⟩

theorem parts_parsed : blockText? types partsSource.toList = some partsBody :=
  block_text_of_parts _ _ partsTokens _ parts_lex (by rfl)

private def handlePiece0 : String × List Token :=
  ("{\n", [.punctuation ['{']])

private theorem handlePiece0_lex : handlePiece0.1.toList.foldl step initial =
    completed handlePiece0.2 := by decide +kernel

private def handlePiece1 : String × List Token :=
  ("    CettaFrameIdentityParts parts;\n", [.identifier ['C', 'e', 't', 't', 'a', 'F', 'r', 'a', 'm', 'e', 'I', 'd', 'e', 'n', 't', 'i', 't', 'y', 'P', 'a', 'r', 't', 's'], .identifier ['p', 'a', 'r', 't', 's'], .punctuation [';']])

private theorem handlePiece1_lex : handlePiece1.1.toList.foldl step initial =
    completed handlePiece1.2 := by decide +kernel

private def handlePiece2 : String × List Token :=
  ("    (void)cetta_frame_identity_parts(identity, &parts);\n", [.punctuation ['('], .identifier ['v', 'o', 'i', 'd'], .punctuation [')'], .identifier ['c', 'e', 't', 't', 'a', '_', 'f', 'r', 'a', 'm', 'e', '_', 'i', 'd', 'e', 'n', 't', 'i', 't', 'y', '_', 'p', 'a', 'r', 't', 's'], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation [','], .punctuation ['&'], .identifier ['p', 'a', 'r', 't', 's'], .punctuation [')'], .punctuation [';']])

private theorem handlePiece2_lex : handlePiece2.1.toList.foldl step initial =
    completed handlePiece2.2 := by decide +kernel

private def handlePiece3 : String × List Token :=
  ("    return parts.handle;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['p', 'a', 'r', 't', 's'], .punctuation ['.'], .identifier ['h', 'a', 'n', 'd', 'l', 'e'], .punctuation [';']])

private theorem handlePiece3_lex : handlePiece3.1.toList.foldl step initial =
    completed handlePiece3.2 := by decide +kernel

private def handlePiece4 : String × List Token :=
  ("}", [.punctuation ['}']])

private theorem handlePiece4_lex : handlePiece4.1.toList.foldl step initial =
    completed handlePiece4.2 := by decide +kernel

private def handlePieces : List (String × List Token) :=
  [handlePiece0, handlePiece1, handlePiece2, handlePiece3, handlePiece4]

def handleSource : String := String.join (handlePieces.map Prod.fst)
def handleTokens : List Token := handlePieces.flatMap Prod.snd

theorem handle_lex : lex handleSource.toList = .ok handleTokens := by
  apply lex_completed_string_pieces
  simp only [handlePieces, List.forall_cons]
  exact ⟨handlePiece0_lex, handlePiece1_lex, handlePiece2_lex, handlePiece3_lex, handlePiece4_lex, trivial⟩

theorem handle_parsed : blockText? types handleSource.toList = some handleBody :=
  block_text_of_parts _ _ handleTokens _ handle_lex (by rfl)

private def generationPiece0 : String × List Token :=
  ("{\n", [.punctuation ['{']])

private theorem generationPiece0_lex : generationPiece0.1.toList.foldl step initial =
    completed generationPiece0.2 := by decide +kernel

private def generationPiece1 : String × List Token :=
  ("    CettaFrameIdentityParts parts;\n", [.identifier ['C', 'e', 't', 't', 'a', 'F', 'r', 'a', 'm', 'e', 'I', 'd', 'e', 'n', 't', 'i', 't', 'y', 'P', 'a', 'r', 't', 's'], .identifier ['p', 'a', 'r', 't', 's'], .punctuation [';']])

private theorem generationPiece1_lex : generationPiece1.1.toList.foldl step initial =
    completed generationPiece1.2 := by decide +kernel

private def generationPiece2 : String × List Token :=
  ("    (void)cetta_frame_identity_parts(identity, &parts);\n", [.punctuation ['('], .identifier ['v', 'o', 'i', 'd'], .punctuation [')'], .identifier ['c', 'e', 't', 't', 'a', '_', 'f', 'r', 'a', 'm', 'e', '_', 'i', 'd', 'e', 'n', 't', 'i', 't', 'y', '_', 'p', 'a', 'r', 't', 's'], .punctuation ['('], .identifier ['i', 'd', 'e', 'n', 't', 'i', 't', 'y'], .punctuation [','], .punctuation ['&'], .identifier ['p', 'a', 'r', 't', 's'], .punctuation [')'], .punctuation [';']])

private theorem generationPiece2_lex : generationPiece2.1.toList.foldl step initial =
    completed generationPiece2.2 := by decide +kernel

private def generationPiece3 : String × List Token :=
  ("    return parts.generation;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['p', 'a', 'r', 't', 's'], .punctuation ['.'], .identifier ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n'], .punctuation [';']])

private theorem generationPiece3_lex : generationPiece3.1.toList.foldl step initial =
    completed generationPiece3.2 := by decide +kernel

private def generationPiece4 : String × List Token :=
  ("}", [.punctuation ['}']])

private theorem generationPiece4_lex : generationPiece4.1.toList.foldl step initial =
    completed generationPiece4.2 := by decide +kernel

private def generationPieces : List (String × List Token) :=
  [generationPiece0, generationPiece1, generationPiece2, generationPiece3, generationPiece4]

def generationSource : String := String.join (generationPieces.map Prod.fst)
def generationTokens : List Token := generationPieces.flatMap Prod.snd

theorem generation_lex : lex generationSource.toList = .ok generationTokens := by
  apply lex_completed_string_pieces
  simp only [generationPieces, List.forall_cons]
  exact ⟨generationPiece0_lex, generationPiece1_lex, generationPiece2_lex, generationPiece3_lex, generationPiece4_lex, trivial⟩

theorem generation_parsed : blockText? types generationSource.toList = some generationBody :=
  block_text_of_parts _ _ generationTokens _ generation_lex (by rfl)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentitySource

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentitySource
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def macroText : List (Name × String) :=
  [("CETTA_FRAME_HANDLE_MASK".toList, "UINT32_C(0x000fffff)"),
   ("CETTA_FRAME_GENERATION_MAX".toList, "UINT32_C(0x000007fe)"),
   ("CETTA_FRAME_CLASS1_FIRST".toList, "(UINT32_C(1) << 20)"),
   ("CETTA_FRAME_CLASS2_FIRST".toList, "(CETTA_FRAME_CLASS1_FIRST + (UINT32_C(1) << 24))"),
   ("CETTA_FRAME_CLASS3_FIRST".toList, "(CETTA_FRAME_CLASS2_FIRST + (UINT32_C(1) << 26))"),
   ("CETTA_FRAME_HANDLE_LIMIT".toList, "(CETTA_FRAME_CLASS3_FIRST + (UINT32_C(1) << 26))")]

def macroTerms : List (Name × CExpr) :=
  [("CETTA_FRAME_HANDLE_MASK".toList, uint 1048575),
   ("CETTA_FRAME_GENERATION_MAX".toList, uint 2046),
   ("CETTA_FRAME_CLASS1_FIRST".toList, .binary .shiftLeft (uint 1) (.decimal 20)),
   ("CETTA_FRAME_CLASS2_FIRST".toList, .binary .add (id "CETTA_FRAME_CLASS1_FIRST")
     (.binary .shiftLeft (uint 1) (.decimal 24))),
   ("CETTA_FRAME_CLASS3_FIRST".toList, .binary .add (id "CETTA_FRAME_CLASS2_FIRST")
     (.binary .shiftLeft (uint 1) (.decimal 26))),
   ("CETTA_FRAME_HANDLE_LIMIT".toList, .binary .add (id "CETTA_FRAME_CLASS3_FIRST")
     (.binary .shiftLeft (uint 1) (.decimal 26)))]

private theorem macroEntry0_parsed :
    expressionText? types "UINT32_C(0x000fffff)".toList = some (uint 1048575) := by
  have tokenized : lex "UINT32_C(0x000fffff)".toList = .ok
      [.identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '0', '0', '0', 'f', 'f', 'f', 'f', 'f'], .punctuation [')']] := by rfl
  rw [expressionText?, tokenized]
  rfl


private theorem macroEntry1_parsed :
    expressionText? types "UINT32_C(0x000007fe)".toList = some (uint 2046) := by
  have tokenized : lex "UINT32_C(0x000007fe)".toList = .ok
      [.identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['0', 'x', '0', '0', '0', '0', '0', '7', 'f', 'e'], .punctuation [')']] := by rfl
  rw [expressionText?, tokenized]
  rfl

private theorem macroEntry2_parsed :
    expressionText? types "(UINT32_C(1) << 20)".toList = some (.binary .shiftLeft (uint 1) (.decimal 20)) := by
  have tokenized : lex "(UINT32_C(1) << 20)".toList = .ok
      [.punctuation ['('], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['1'], .punctuation [')'], .punctuation ['<', '<'], .number ['2', '0'], .punctuation [')']] := by rfl
  rw [expressionText?, tokenized]
  rfl

private theorem macroEntry3_parsed :
    expressionText? types "(CETTA_FRAME_CLASS1_FIRST + (UINT32_C(1) << 24))".toList = some (.binary .add (id "CETTA_FRAME_CLASS1_FIRST") (.binary .shiftLeft (uint 1) (.decimal 24))) := by
  have tokenized : lex "(CETTA_FRAME_CLASS1_FIRST + (UINT32_C(1) << 24))".toList = .ok
      [.punctuation ['('], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'L', 'A', 'S', 'S', '1', '_', 'F', 'I', 'R', 'S', 'T'], .punctuation ['+'], .punctuation ['('], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['1'], .punctuation [')'], .punctuation ['<', '<'], .number ['2', '4'], .punctuation [')'], .punctuation [')']] := by rfl
  rw [expressionText?, tokenized]
  rfl

private theorem macroEntry4_parsed :
    expressionText? types "(CETTA_FRAME_CLASS2_FIRST + (UINT32_C(1) << 26))".toList = some (.binary .add (id "CETTA_FRAME_CLASS2_FIRST") (.binary .shiftLeft (uint 1) (.decimal 26))) := by
  have tokenized : lex "(CETTA_FRAME_CLASS2_FIRST + (UINT32_C(1) << 26))".toList = .ok
      [.punctuation ['('], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'L', 'A', 'S', 'S', '2', '_', 'F', 'I', 'R', 'S', 'T'], .punctuation ['+'], .punctuation ['('], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['1'], .punctuation [')'], .punctuation ['<', '<'], .number ['2', '6'], .punctuation [')'], .punctuation [')']] := by rfl
  rw [expressionText?, tokenized]
  rfl

private theorem macroEntry5_parsed :
    expressionText? types "(CETTA_FRAME_CLASS3_FIRST + (UINT32_C(1) << 26))".toList = some (.binary .add (id "CETTA_FRAME_CLASS3_FIRST") (.binary .shiftLeft (uint 1) (.decimal 26))) := by
  have tokenized : lex "(CETTA_FRAME_CLASS3_FIRST + (UINT32_C(1) << 26))".toList = .ok
      [.punctuation ['('], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'L', 'A', 'S', 'S', '3', '_', 'F', 'I', 'R', 'S', 'T'], .punctuation ['+'], .punctuation ['('], .identifier ['U', 'I', 'N', 'T', '3', '2', '_', 'C'], .punctuation ['('], .number ['1'], .punctuation [')'], .punctuation ['<', '<'], .number ['2', '6'], .punctuation [')'], .punctuation [')']] := by rfl
  rw [expressionText?, tokenized]
  rfl

theorem macro_terms_parsed :
    macroText.map (fun entry => (entry.1, expressionText? types entry.2.toList)) =
      macroTerms.map (fun entry => (entry.1, some entry.2)) := by
  simp only [macroText, macroTerms, List.map_cons, List.map_nil,
    macroEntry0_parsed, macroEntry1_parsed, macroEntry2_parsed, macroEntry3_parsed, macroEntry4_parsed, macroEntry5_parsed]

/-- Definitions are evaluated in their actual declaration order. Later names
cannot supply a guessed value to an earlier macro. -/
def macroStep (state : Option (ScalarRead.Environment Nat)) (entry : Name × CExpr) :
    Option (ScalarRead.Environment Nat) := do
  let environment ← state
  let value ← ScalarRead.expression environment (fun _ _ => none) entry.2
  pure (Function.update environment entry.1 (some value))

def macroEnvironment? : Option (ScalarRead.Environment Nat) :=
  macroTerms.foldl macroStep (some (fun _ => none))

def expectedMacroEnvironment : ScalarRead.Environment Nat :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update (fun _ => none)
              "CETTA_FRAME_HANDLE_MASK".toList (some (.unsigned 1048575)))
            "CETTA_FRAME_GENERATION_MAX".toList (some (.unsigned 2046)))
          "CETTA_FRAME_CLASS1_FIRST".toList (some (.unsigned 1048576)))
        "CETTA_FRAME_CLASS2_FIRST".toList (some (.unsigned 17825792)))
      "CETTA_FRAME_CLASS3_FIRST".toList (some (.unsigned 84934656)))
    "CETTA_FRAME_HANDLE_LIMIT".toList (some (.unsigned 152043520))

theorem macro_environment_computes :
    macroEnvironment? = some expectedMacroEnvironment := by rfl

theorem missing_macro_dependency_refused :
    macroStep (some (fun _ => none))
      ("CETTA_FRAME_CLASS2_FIRST".toList, .binary .add (id "CETTA_FRAME_CLASS1_FIRST")
        (.binary .shiftLeft (uint 1) (.decimal 24))) = none := rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentitySource

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityParts

/-- The three unsigned words written by the source's selected class branch.
The malformed high-prefix case still writes a handle and two zero words. -/
def words (identity : UInt32) : UInt32 × UInt32 × UInt32 :=
  if identity >>> 31 = 0 then
    (identity &&& 1048575, identity >>> 20, 2046)
  else if identity >>> 30 = 2 then
    (1048576 + (identity &&& 16777215), (identity >>> 24) &&& 63, 62)
  else if identity >>> 29 = 6 then
    (17825792 + (identity &&& 67108863), (identity >>> 26) &&& 7, 6)
  else if identity >>> 28 = 14 then
    (84934656 + (identity &&& 67108863), (identity >>> 26) &&& 3, 2)
  else (152043520 + (identity &&& 268435455), 0, 0)

private theorem shift_nat (value count : UInt32) (small : count.toNat < 32) :
    (value >>> count).toNat = value.toNat >>> count.toNat := by
  rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt small]

private theorem shift_equals (value count output : UInt32)
    (small : count.toNat < 32) :
    value >>> count = output ↔ value.toNat >>> count.toNat = output.toNat := by
  rw [← UInt32.toNat_inj, shift_nat value count small]

theorem words_handle_matches_codec (identity : UInt32) :
    (words identity).1.toNat = unpackHandle identity.toNat := by
  have bounded := identity.toNat_lt
  have masked24 : identity.toNat &&& 16777215 < 16777216 := by
    change identity.toNat &&& (2 ^ 24 - 1) < 2 ^ 24
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have masked26 : identity.toNat &&& 67108863 < 67108864 := by
    change identity.toNat &&& (2 ^ 26 - 1) < 2 ^ 26
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have masked28 : identity.toNat &&& 268435455 < 268435456 := by
    change identity.toNat &&& (2 ^ 28 - 1) < 2 ^ 28
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have add24 : 1048576 + (identity.toNat &&& 16777215) < 2 ^ 32 := by omega
  have add26a : 17825792 + (identity.toNat &&& 67108863) < 2 ^ 32 := by omega
  have add26b : 84934656 + (identity.toNat &&& 67108863) < 2 ^ 32 := by omega
  have add28 : 152043520 + (identity.toNat &&& 268435455) < 2 ^ 32 := by omega
  have native := packedHandle_eq_native_bits (BitVec.ofNat 64 identity.toNat) (by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : identity.toNat < 2 ^ 64)]
      using bounded)
  simp only [packedHandle, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : identity.toNat < 2 ^ 64)] at native
  rw [native]
  simp only [words, shift_equals identity 31 0 (by decide),
    shift_equals identity 30 2 (by decide),
    shift_equals identity 29 6 (by decide),
    shift_equals identity 28 14 (by decide), UInt32.reduceToNat]
  split_ifs <;> simp only [UInt32.toNat_add, UInt32.toNat_and, UInt32.reduceToNat,
    Nat.mod_eq_of_lt add24, Nat.mod_eq_of_lt add26a,
    Nat.mod_eq_of_lt add26b, Nat.mod_eq_of_lt add28,
    classOneFirst, classTwoFirst, classThreeFirst, handleLimit] <;> rfl

theorem words_generation_matches_codec (identity : UInt32) :
    (words identity).2.1.toNat = unpackGeneration identity.toNat := by
  have bounded := identity.toNat_lt
  have native := packedGeneration_eq_native_bits (BitVec.ofNat 64 identity.toNat) (by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : identity.toNat < 2 ^ 64)]
      using bounded)
  simp only [packedGeneration, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : identity.toNat < 2 ^ 64)] at native
  rw [native]
  simp only [words, shift_equals identity 31 0 (by decide),
    shift_equals identity 30 2 (by decide),
    shift_equals identity 29 6 (by decide),
    shift_equals identity 28 14 (by decide), UInt32.reduceToNat]
  split_ifs <;> simp only [UInt32.toNat_and, shift_nat identity 20 (by decide),
    shift_nat identity 24 (by decide), shift_nat identity 26 (by decide),
    UInt32.reduceToNat] <;> rfl


private theorem mask_bound (value : UInt32) (bits : Nat) :
    value.toNat &&& (2 ^ bits - 1) < 2 ^ bits := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos bits)

theorem words_maximum_matches_codec (identity : UInt32)
    (inside : (words identity).1.toNat < handleLimit) :
    (words identity).2.2.toNat = generationMax (words identity).1.toNat := by
  have b20 := mask_bound identity 20
  have b24 := mask_bound identity 24
  have b26 := mask_bound identity 26
  have b28 := mask_bound identity 28
  norm_num only [Nat.reducePow, Nat.reduceSub] at b20 b24 b26 b28
  have add24 : 1048576 + (identity.toNat &&& 16777215) < 2 ^ 32 := by omega
  have add26a : 17825792 + (identity.toNat &&& 67108863) < 2 ^ 32 := by omega
  have add26b : 84934656 + (identity.toNat &&& 67108863) < 2 ^ 32 := by omega
  have add28 : 152043520 + (identity.toNat &&& 268435455) < 2 ^ 32 := by omega
  unfold words at inside ⊢
  split_ifs at inside ⊢ <;>
    simp only [UInt32.toNat_add, UInt32.toNat_and, UInt32.reduceToNat,
      generationMax, classOneFirst, classTwoFirst,
      classThreeFirst, handleLimit, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul] at inside ⊢
  all_goals split_ifs <;> omega

/-- A malformed high prefix still receives a deterministic handle, but that
handle lies outside the allocator's entire handle range. -/
theorem outside_prefix_handle (identity : UInt32)
    (first : identity >>> 31 ≠ 0) (second : identity >>> 30 ≠ 2)
    (third : identity >>> 29 ≠ 6) (fourth : identity >>> 28 ≠ 14) :
    handleLimit ≤ (words identity).1.toNat := by
  have bound := mask_bound identity 28
  norm_num only [Nat.reducePow, Nat.reduceSub] at bound
  have added : 152043520 + (identity.toNat &&& 268435455) < 2 ^ 32 := by omega
  simp only [words, if_neg first, if_neg second, if_neg third, if_neg fourth,
    UInt32.toNat_add, UInt32.toNat_and, UInt32.reduceToNat,
    handleLimit, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul]
  omega

/-- The validity flag has the existing codec's meaning. Decoding a malformed
spelling and treating its handle as live ownership remain distinct operations. -/
theorem valid_words_iff_representable (identity : UInt32) :
    ((words identity).1 ≠ 0 ∧ (words identity).1 < 152043520 ∧
      (words identity).2.1 ≠ 0 ∧ (words identity).2.1 ≤ (words identity).2.2) ↔
    Representable ⟨unpackHandle identity.toNat, unpackGeneration identity.toNat⟩ := by
  rw [← words_handle_matches_codec, ← words_generation_matches_codec]
  unfold Representable
  constructor
  · rintro ⟨nonzero, inside, positive, bounded⟩
    have ih : (words identity).1.toNat < handleLimit := by
      simpa only [UInt32.lt_iff_toNat_lt, UInt32.reduceToNat, handleLimit,
        Nat.reducePow, Nat.reduceAdd, Nat.reduceMul] using inside
    rw [← words_maximum_matches_codec identity ih]
    exact ⟨by simpa only [← UInt32.pos_iff_ne_zero, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] using nonzero, ih,
      by simpa only [← UInt32.pos_iff_ne_zero, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] using positive,
      by simpa only [UInt32.le_iff_toNat_le] using bounded⟩
  · rintro ⟨nonzero, inside, positive, bounded⟩
    rw [← words_maximum_matches_codec identity inside] at bounded
    exact ⟨by simpa only [← UInt32.pos_iff_ne_zero, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] using nonzero,
      by simpa only [UInt32.lt_iff_toNat_lt, UInt32.reduceToNat, handleLimit,
        Nat.reducePow, Nat.reduceAdd, Nat.reduceMul] using inside,
      by simpa only [← UInt32.pos_iff_ne_zero, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] using positive,
      by simpa only [UInt32.le_iff_toNat_le] using bounded⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityParts

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityRead
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic


def layout : Layout := fun name =>
  if name = "handle".toList then some ⟨0, .word⟩
  else if name = "generation".toList then some ⟨1, .word⟩
  else if name = "generation_max".toList then some ⟨2, .word⟩ else none

/-- Macro values are computed by the previously checked source-order fold.
The function parameters remain scalar values; `out` is a pointer, not a record. -/
def environment (identity : UInt32) (output : Ptr) : Environment := fun name =>
  if name = "identity".toList then some (.u32 identity)
  else if name = "out".toList then some (.ptr (some output))
  else IdentitySource.macroEnvironment?.bind fun macros =>
    (macros name).bind fun value => match value with
      | .unsigned word => some (.u32 word)
      | _ => none

def read (identity : UInt32) (output : Ptr) (operand : CExpr) : CProg CVal CVal :=
  expression layout (environment identity output) operand

theorem read_named (identity : UInt32) (output : Ptr) (name : Name) (value : CVal)
    (known : environment identity output name = some value) :
    read identity output (.identifier name) = pure value := by
  simp only [read, expression, expressionWith, expressionWithNames, known, resolved]

theorem read_identity (identity : UInt32) (output : Ptr) :
    read identity output (IdentitySource.id "identity") = pure (.u32 identity) := by
  apply read_named
  simp only [environment, ↓reduceIte]

theorem read_output (identity : UInt32) (output : Ptr) :
    read identity output (IdentitySource.id "out") = pure (.ptr (some output)) := by
  apply read_named
  rfl

theorem read_unsigned (identity : UInt32) (output : Ptr) (value : Nat)
    (bounded : value < 2 ^ 32) :
    read identity output (IdentitySource.uint value) = pure (.u32 (UInt32.ofNat value)) := by
  simp only [read, IdentitySource.uint, expression, expressionWith, expressionWithNames,
    if_pos bounded, resolved]

theorem read_decimal (identity : UInt32) (output : Ptr) (value : Nat)
    (bounded : value < 2 ^ 31) :
    read identity output (.decimal value) = pure (.i32 (Int32.ofNat value)) := by
  simp only [read, expression, expressionWith, expressionWithNames, ScalarRead.signedDecimal?,
    if_pos bounded, Option.bind_some, cell?, resolved]

theorem read_binary (identity : UInt32) (output : Ptr) (operator : BinaryOperator)
    (left right : CExpr) (notAnd : operator ≠ .and) (notOr : operator ≠ .or) :
    read identity output (.binary operator left right) =
      (read identity output left >>= fun a => read identity output right >>= fun b =>
        binary operator a b) := by
  cases operator <;> first | contradiction | rfl

theorem read_shift (identity : UInt32) (output : Ptr) (count : Nat) (small : count < 32) :
    read identity output (IdentitySource.shift count) = pure (.u32 (identity >>> UInt32.ofNat count)) := by
  rw [IdentitySource.shift, read_binary _ _ _ _ _ (by decide) (by decide),
    read_identity, read_decimal _ _ _ (by omega)]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  have countValue : (Int32.ofNat count).toInt = (count : Int) :=
    Int32.toInt_ofNat_of_lt (by omega)
  have within : 0 ≤ (Int32.ofNat count).toInt ∧ (Int32.ofNat count).toInt < 32 := by
    rw [countValue]
    omega
  have law := (ScalarRead.unsigned32_signed_right_c11 (Ptr := Ptr)
    identity (Int32.ofNat count) within .arithmetic).1
  simp only [countValue, Int.toNat_natCast] at law
  change resolved ((ScalarRead.numericBinary .shiftRight (.unsigned identity)
    (.signed (Int32.ofNat count))).bind cell?) = _
  rw [law]
  rfl

theorem read_mask (identity : UInt32) (output : Ptr) (value : Nat)
    (bounded : value < 2 ^ 32) :
    read identity output (IdentitySource.mask value) = pure (.u32 (identity &&& UInt32.ofNat value)) := by
  rw [IdentitySource.mask, read_binary _ _ _ _ _ (by decide) (by decide),
    read_identity, read_unsigned _ _ _ bounded]
  rfl

theorem field_store (identity : UInt32) (output : Ptr) (name : String)
    (offset : Nat) (descriptor : layout name.toList = some ⟨offset, .word⟩)
    (operand : CExpr) (value : UInt32)
    (readValue : read identity output operand = pure (.u32 value)) :
    fieldAssignment expression layout (environment identity output) (IdentitySource.assign name operand) =
      (CProg.store (output + offset) (.u32 value) >>= fun _ =>
        pure (environment identity output)) := by
  rw [IdentitySource.assign, IdentitySource.out, field_assignment_retains_actual_operands]
  change (read identity output (IdentitySource.id "out") >>= fun owner =>
    read identity output operand >>= fun actual =>
      storeField layout owner name.toList actual >>= fun _ =>
        pure (environment identity output)) = _
  rw [read_output, readValue]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, storeField, descriptor,
    resolved, valueKind, ↓reduceIte, fieldAddress, pointer]

theorem read_field (identity : UInt32) (output : Ptr) (name : String)
    (offset : Nat) (descriptor : layout name.toList = some ⟨offset, .word⟩) :
    read identity output (IdentitySource.out name) =
      (CProg.loadU32 (output + offset) >>= fun value => pure (.u32 value)) := by
  change (read identity output (IdentitySource.id "out") >>= fun owner =>
    ReadExpressions.field layout owner name.toList) = _
  rw [read_output]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, ReadExpressions.field,
    pointer, descriptor]


private theorem macro_lookup (identity : UInt32) (output : Ptr) (name : Name)
    (different : name ≠ "identity".toList) (notOutput : name ≠ "out".toList)
    (value : UInt32) (known : IdentitySource.expectedMacroEnvironment name = some (.unsigned value)) :
    read identity output (.identifier name) = pure (.u32 value) := by
  apply read_named
  simp only [environment, if_neg different, if_neg notOutput,
    IdentitySource.macro_environment_computes, Option.bind_some, known]

theorem read_handle_mask (identity : UInt32) (output : Ptr) :
    read identity output (IdentitySource.id "CETTA_FRAME_HANDLE_MASK") = pure (.u32 1048575) := by
  exact macro_lookup _ _ _ (by decide) (by decide) _ (by rfl)

theorem read_generation_max (identity : UInt32) (output : Ptr) :
    read identity output (IdentitySource.id "CETTA_FRAME_GENERATION_MAX") = pure (.u32 2046) := by
  exact macro_lookup _ _ _ (by decide) (by decide) _ (by rfl)

theorem read_class_one (identity : UInt32) (output : Ptr) :
    read identity output (IdentitySource.id "CETTA_FRAME_CLASS1_FIRST") = pure (.u32 1048576) := by
  exact macro_lookup _ _ _ (by decide) (by decide) _ (by rfl)

theorem read_class_two (identity : UInt32) (output : Ptr) :
    read identity output (IdentitySource.id "CETTA_FRAME_CLASS2_FIRST") = pure (.u32 17825792) := by
  exact macro_lookup _ _ _ (by decide) (by decide) _ (by rfl)

theorem read_class_three (identity : UInt32) (output : Ptr) :
    read identity output (IdentitySource.id "CETTA_FRAME_CLASS3_FIRST") = pure (.u32 84934656) := by
  exact macro_lookup _ _ _ (by decide) (by decide) _ (by rfl)

theorem read_handle_limit (identity : UInt32) (output : Ptr) :
    read identity output (IdentitySource.id "CETTA_FRAME_HANDLE_LIMIT") = pure (.u32 152043520) := by
  exact macro_lookup _ _ _ (by decide) (by decide) _ (by rfl)

/-- These are the actual physical reads of the final short-circuit return.
The second handle and generation occurrences are retained as separate reads. -/
def validityProgram (output : Ptr) : CProg CVal Bool := do
  let handle ← CProg.loadU32 output
  if handle != 0 then
    let handleAgain ← CProg.loadU32 output
    if handleAgain < 152043520 then
      let generation ← CProg.loadU32 (output + 1)
      if generation != 0 then
        let generationAgain ← CProg.loadU32 (output + 1)
        let maximum ← CProg.loadU32 (output + 2)
        pure (decide (generationAgain ≤ maximum))
      else pure false
    else pure false
  else pure false

def finalCondition : CExpr := .binary .and
  (.binary .and
    (.binary .and (.binary .ne (IdentitySource.out "handle") (IdentitySource.uint 0))
      (.binary .lt (IdentitySource.out "handle") (IdentitySource.id "CETTA_FRAME_HANDLE_LIMIT")))
    (.binary .ne (IdentitySource.out "generation") (IdentitySource.uint 0)))
  (.binary .le (IdentitySource.out "generation") (IdentitySource.out "generation_max"))

theorem read_and (identity : UInt32) (output : Ptr) (left right : CExpr) :
    read identity output (.binary .and left right) =
      (read identity output left >>= fun value => truth value >>= fun flag =>
        if flag then read identity output right >>= fun value => truth value >>= fun flag =>
          pure (.bool flag) else pure (.bool false)) := rfl

theorem read_final_condition (identity : UInt32) (output : Ptr) :
    read identity output finalCondition =
      (validityProgram output >>= fun valid => pure (.bool valid)) := by
  unfold finalCondition
  rw [read_and, read_and, read_and]
  rw [read_binary _ _ .ne _ _ (by decide) (by decide),
    read_binary _ _ .lt _ _ (by decide) (by decide),
    read_binary _ _ .ne _ _ (by decide) (by decide),
    read_binary _ _ .le _ _ (by decide) (by decide)]
  rw [read_field _ _ "handle" 0 rfl, read_field _ _ "generation" 1 rfl,
    read_field _ _ "generation_max" 2 rfl, read_unsigned _ _ 0 (by decide), read_handle_limit]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    binary, equal, scalar, ScalarRead.equal?, resolved, truth, word,
    ScalarRead.numericBinary, ScalarRead.unsignedBinary, cell?, Option.bind_some]
  unfold validityProgram
  simp only [bne_eq, show UInt32.ofNat 0 = 0 from rfl,
    Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]
  congr 1
  funext handle
  split
  · simp only [Prog.bind_assoc, Prog.ret_bind]
    congr 1
    funext handleAgain
    simp only [decide_eq_true_eq]
    split
    · simp only [Prog.bind_assoc, Prog.ret_bind]
      congr 1
      funext generation
      split <;> simp only [Prog.bind_assoc, Prog.ret_bind]
    · simp only [Prog.ret_bind, Bool.false_eq_true, ↓reduceIte]
  · rfl


/-- Three scalar stores in the source's fixed order. Nothing here asserts that
an intermediate two-word record is a completed decoding. -/
def storeWords (output : Ptr) (handle generation maximum : UInt32) : CProg CVal Unit := do
  CProg.store output (.u32 handle)
  CProg.store (output + 1) (.u32 generation)
  CProg.store (output + 2) (.u32 maximum)

theorem actual_three_store_block (identity : UInt32) (output : Ptr) (fuel : Nat)
    (handleExpr generationExpr maximumExpr : CExpr) (handle generation maximum : UInt32)
    (readHandle : read identity output handleExpr = pure (.u32 handle))
    (readGeneration : read identity output generationExpr = pure (.u32 generation))
    (readMaximum : read identity output maximumExpr = pure (.u32 maximum)) :
    executeWith {} (fieldAssignment expression) layout 0 (fuel + 3) (environment identity output)
      [IdentitySource.assign "handle" handleExpr, IdentitySource.assign "generation" generationExpr,
        IdentitySource.assign "generation_max" maximumExpr] =
      (storeWords output handle generation maximum >>= fun _ =>
        pure (.finished (.next (environment identity output)))) := by
  let entries : List ((CExpr × CExpr) × CProg CVal Unit) :=
    [((IdentitySource.out "handle", handleExpr), CProg.store output (.u32 handle)),
     ((IdentitySource.out "generation", generationExpr), CProg.store (output + 1) (.u32 generation)),
     ((IdentitySource.out "generation_max", maximumExpr), CProg.store (output + 2) (.u32 maximum))]
  have realizes : ∀ entry ∈ entries,
      (Services.scoped {} (fieldAssignment expression)).assignment layout (environment identity output)
        (.assign entry.1.1 entry.1.2) =
        (entry.2 >>= fun _ => pure (environment identity output)) := by
    intro entry member
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact field_store identity output "handle" 0 rfl _ _ readHandle
    · exact field_store identity output "generation" 1 rfl _ _ readGeneration
    · exact field_store identity output "generation_max" 2 rfl _ _ readMaximum
  have law := scoped_assignment_prefix_keeps_operations
    (Services.scoped {} (fieldAssignment expression)) layout 0 fuel
    (environment identity output) entries [] realizes
  change executeWith {} (fieldAssignment expression) layout 0 (fuel + 3) (environment identity output)
    [IdentitySource.assign "handle" handleExpr, IdentitySource.assign "generation" generationExpr,
      IdentitySource.assign "generation_max" maximumExpr] = _ at law
  rw [law]
  simp only [entries, List.foldr_cons, List.foldr_nil, executeScopedWith.eq_def,
    storeWords, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]

theorem read_shift_mask (identity : UInt32) (output : Ptr) (count mask : Nat)
    (small : count < 32) (bounded : mask < 2 ^ 32) :
    read identity output (.binary .bitAnd (IdentitySource.shift count) (IdentitySource.uint mask)) =
      pure (.u32 ((identity >>> UInt32.ofNat count) &&& UInt32.ofNat mask)) := by
  rw [read_binary _ _ _ _ _ (by decide) (by decide), read_shift _ _ _ small,
    read_unsigned _ _ _ bounded]
  rfl

theorem read_add_mask (identity : UInt32) (output : Ptr) (first : CExpr) (value : UInt32)
    (mask : Nat) (bounded : mask < 2 ^ 32)
    (firstRead : read identity output first = pure (.u32 value)) :
    read identity output (.binary .add first (IdentitySource.mask mask)) =
      pure (.u32 (value + (identity &&& UInt32.ofNat mask))) := by
  rw [read_binary _ _ _ _ _ (by decide) (by decide), firstRead, read_mask _ _ _ bounded]
  rfl

theorem actual_class_zero (identity : UInt32) (output : Ptr) (fuel : Nat) :
    executeWith {} (fieldAssignment expression) layout 0 (fuel + 3) (environment identity output)
      IdentitySource.class0 =
      (storeWords output (identity &&& 1048575) (identity >>> 20) 2046 >>= fun _ =>
        pure (.finished (.next (environment identity output)))) := by
  apply actual_three_store_block
  · rw [read_binary _ _ _ _ _ (by decide) (by decide), read_identity, read_handle_mask]
    rfl
  · exact read_shift _ _ 20 (by decide)
  · exact read_generation_max _ _

theorem actual_class_one (identity : UInt32) (output : Ptr) (fuel : Nat) :
    executeWith {} (fieldAssignment expression) layout 0 (fuel + 3) (environment identity output)
      IdentitySource.class1 =
      (storeWords output (1048576 + (identity &&& 16777215)) ((identity >>> 24) &&& 63) 62 >>= fun _ =>
        pure (.finished (.next (environment identity output)))) := by
  apply actual_three_store_block
  · exact read_add_mask _ _ _ _ _ (by decide) (read_class_one _ _)
  · exact read_shift_mask _ _ 24 63 (by decide) (by decide)
  · exact read_unsigned _ _ 62 (by decide)

theorem actual_class_two (identity : UInt32) (output : Ptr) (fuel : Nat) :
    executeWith {} (fieldAssignment expression) layout 0 (fuel + 3) (environment identity output)
      IdentitySource.class2 =
      (storeWords output (17825792 + (identity &&& 67108863)) ((identity >>> 26) &&& 7) 6 >>= fun _ =>
        pure (.finished (.next (environment identity output)))) := by
  apply actual_three_store_block
  · exact read_add_mask _ _ _ _ _ (by decide) (read_class_two _ _)
  · exact read_shift_mask _ _ 26 7 (by decide) (by decide)
  · exact read_unsigned _ _ 6 (by decide)

theorem actual_class_three (identity : UInt32) (output : Ptr) (fuel : Nat) :
    executeWith {} (fieldAssignment expression) layout 0 (fuel + 3) (environment identity output)
      IdentitySource.class3 =
      (storeWords output (84934656 + (identity &&& 67108863)) ((identity >>> 26) &&& 3) 2 >>= fun _ =>
        pure (.finished (.next (environment identity output)))) := by
  apply actual_three_store_block
  · exact read_add_mask _ _ _ _ _ (by decide) (read_class_three _ _)
  · exact read_shift_mask _ _ 26 3 (by decide) (by decide)
  · exact read_unsigned _ _ 2 (by decide)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityRead

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityRead
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

/-- The C helper always stores a three-word decoding. Its return only reports
whether that spelling belongs to an issuable class and generation. -/
def partsProgram (identity : UInt32) (output : Ptr) : CProg CVal Bool := do
  let words := IdentityParts.words identity
  storeWords output words.1 words.2.1 words.2.2
  if identity >>> 31 = 0 ∨ identity >>> 30 = 2 ∨ identity >>> 29 = 6 ∨ identity >>> 28 = 14 then
    validityProgram output
  else pure false

theorem read_class_guard (identity : UInt32) (output : Ptr) (count expected : Nat)
    (small : count < 32) (bounded : expected < 2 ^ 32) :
    read identity output (.binary .eq (IdentitySource.shift count) (IdentitySource.uint expected)) =
      pure (.bool (decide (identity >>> UInt32.ofNat count = UInt32.ofNat expected))) := by
  rw [read_binary _ _ _ _ _ (by decide) (by decide), read_shift _ _ _ small,
    read_unsigned _ _ _ bounded]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, binary, equal,
    scalar, ScalarRead.equal?, resolved]
  congr 2

theorem actual_outside (identity : UInt32) (output : Ptr) (fuel : Nat) :
    executeWith {} (fieldAssignment expression) layout 0 (fuel + 4) (environment identity output)
      IdentitySource.outside =
      (storeWords output (152043520 + (identity &&& 268435455)) 0 0 >>= fun _ =>
        pure (.finished (.returned (environment identity output) (some (.bool false))))) := by
  have first := field_store identity output "handle" 0 rfl _ _
    (read_add_mask _ _ _ _ 268435455 (by decide) (read_handle_limit _ _))
  have second := field_store identity output "generation" 1 rfl _ _
    (read_unsigned _ _ 0 (by decide))
  have third := field_store identity output "generation_max" 2 rfl _ _
    (read_unsigned _ _ 0 (by decide))
  dsimp only [IdentitySource.assign] at first second third
  unfold IdentitySource.outside storeWords
  rw [executeWith_equation]
  dsimp only [IdentitySource.assign]
  rw [first]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  congr 1

theorem actual_final_return (identity : UInt32) (output : Ptr) (fuel : Nat) :
    executeWith {} (fieldAssignment expression) layout 0 (fuel + 1) (environment identity output)
      [.return (some finalCondition)] =
      (validityProgram output >>= fun flag =>
        pure (.finished (.returned (environment identity output) (some (.bool flag))))) := by
  rw [executeWith_equation]
  change (read identity output finalCondition >>= fun value =>
    pure (ReadBlock.Result.finished (.returned (environment identity output) (some value)))) = _
  rw [read_final_condition]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem branch_with_read_guard (identity : UInt32) (output : Ptr) (fuel : Nat)
    (count expected : Nat) (small : count < 32) (bounded : expected < 2 ^ 32)
    (yes no rest : List CStatement) :
    executeWith {} (fieldAssignment expression) layout 0 (fuel + 1) (environment identity output)
      (.branch (.binary .eq (IdentitySource.shift count) (IdentitySource.uint expected)) yes no :: rest) =
      (executeWith {} (fieldAssignment expression) layout 0 fuel (environment identity output)
        (if identity >>> UInt32.ofNat count = UInt32.ofNat expected then yes else no) >>=
          ReadBlock.resume (fun updated => executeWith {} (fieldAssignment expression) layout 0 fuel updated rest)) := by
  rw [executeWith_equation]
  change (read identity output _ >>= fun value => truth value >>= fun flag =>
    executeWith {} (fieldAssignment expression) layout 0 fuel (environment identity output)
      (if flag then yes else no) >>= _) = _
  rw [read_class_guard _ _ _ _ small bounded]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, truth, decide_eq_true_eq]

private theorem empty_execute (fuel : Nat) (context : Environment) :
    executeWith {} (fieldAssignment expression) layout 0 fuel context [] =
      pure (.finished (.next context)) := by rw [executeWith_equation]

/-- Source control with sufficient structural allowance reaches exactly the
three physical stores and the selected return reads. Statement allowance is
not a scheduler grant; the common retained operation runner can pause anywhere
inside the resulting operation tree. -/
theorem actual_parts_body (identity : UInt32) (output : Ptr) (fuel : Nat) :
    executeWith {} (fieldAssignment expression) layout 0 (fuel + 8) (environment identity output)
      IdentitySource.partsBody =
      (partsProgram identity output >>= fun flag =>
        pure (.finished (.returned (environment identity output) (some (.bool flag))))) := by
  have final := actual_final_return identity output (fuel + 6)
  unfold finalCondition at final
  unfold IdentitySource.partsBody
  rw [branch_with_read_guard _ _ (fuel + 7) 31 0 (by decide) (by decide)]
  simp only [show UInt32.ofNat 31 = (31 : UInt32) from rfl,
    show UInt32.ofNat 0 = (0 : UInt32) from rfl]
  by_cases first : identity >>> 31 = 0
  · rw [if_pos first, actual_class_zero _ _ (fuel + 4)]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
    rw [final]
    simp only [partsProgram, IdentityParts.words, first, true_or, ↓reduceIte,
      Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]
  · rw [if_neg first]
    rw [branch_with_read_guard _ _ (fuel + 6) 30 2 (by decide) (by decide)]
    simp only [show UInt32.ofNat 30 = (30 : UInt32) from rfl,
      show UInt32.ofNat 2 = (2 : UInt32) from rfl]
    by_cases second : identity >>> 30 = 2
    · rw [if_pos second, actual_class_one _ _ (fuel + 3)]
      simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume,
        empty_execute]
      rw [final]
      simp only [partsProgram, IdentityParts.words, first, second, false_or, true_or, ↓reduceIte,
        Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]
    · rw [if_neg second]
      rw [branch_with_read_guard _ _ (fuel + 5) 29 6 (by decide) (by decide)]
      simp only [show UInt32.ofNat 29 = (29 : UInt32) from rfl,
        show UInt32.ofNat 6 = (6 : UInt32) from rfl]
      by_cases third : identity >>> 29 = 6
      · rw [if_pos third, actual_class_two _ _ (fuel + 2)]
        simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume,
          empty_execute]
        rw [final]
        simp only [partsProgram, IdentityParts.words, first, second, third, false_or, true_or, ↓reduceIte,
          Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]
      · rw [if_neg third]
        rw [branch_with_read_guard _ _ (fuel + 4) 28 14 (by decide) (by decide)]
        simp only [show UInt32.ofNat 28 = (28 : UInt32) from rfl,
          show UInt32.ofNat 14 = (14 : UInt32) from rfl]
        by_cases fourth : identity >>> 28 = 14
        · rw [if_pos fourth, actual_class_three _ _ (fuel + 1)]
          simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume,
            empty_execute]
          rw [final]
          simp only [partsProgram, IdentityParts.words, first, second, third, fourth, false_or, ↓reduceIte,
            Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]
        · rw [if_neg fourth, actual_outside _ _ fuel]
          simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
          simp only [partsProgram, IdentityParts.words, first, second, third, fourth, or_false, ↓reduceIte]
          rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityRead

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityRead
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def PartsCells (output : Ptr) (handle generation maximum : UInt32) : Heap L → Prop :=
  Cells output [some (.u32 handle), some (.u32 generation), some (.u32 maximum)]

private theorem unit_bind_return (program : CProg CVal Unit) :
    program.bind (fun _ => Prog.ret ()) = program := by
  have identity : (fun _ : Unit => (Prog.ret () : CProg CVal Unit)) = Prog.ret := by
    funext value
    cases value
    rfl
  rw [identity, Prog.bind_ret]

theorem store_words_initializes (output : Ptr) (old : List (Option CVal))
    (length : old.length = 3) (handle generation maximum : UInt32) :
    CTriple (L := L) (Cells output old) (storeWords output handle generation maximum)
      (fun _ => PartsCells output handle generation maximum) := by
  have initialized := initialize_cells (L := L) output old
    [.u32 handle, .u32 generation, .u32 maximum] length
  simpa only [CProg.initializeCells, Ptr.add_add, Nat.reduceAdd, PartsCells, List.map_cons,
    List.map_nil, storeWords, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, unit_bind_return] using initialized

private theorem load_handle (output : Ptr) (handle generation maximum : UInt32) :
    CTriple (L := L) (PartsCells output handle generation maximum) (CProg.loadU32 output)
      (fun actual heap => actual = handle ∧ PartsCells output handle generation maximum heap) := by
  apply loadU32_rule
  intro heap held
  exact read_cells (p := output) (cs := [some (.u32 handle), some (.u32 generation), some (.u32 maximum)]) (F := emp) (i := 0) (by simp only [List.length_cons, List.length_nil]; omega) rfl
    (by simpa only [sepConj_emp, PartsCells] using held)

private theorem load_generation (output : Ptr) (handle generation maximum : UInt32) :
    CTriple (L := L) (PartsCells output handle generation maximum) (CProg.loadU32 (output + 1))
      (fun actual heap => actual = generation ∧ PartsCells output handle generation maximum heap) := by
  apply loadU32_rule
  intro heap held
  exact read_cells (p := output) (cs := [some (.u32 handle), some (.u32 generation), some (.u32 maximum)]) (F := emp) (i := 1) (by simp only [List.length_cons, List.length_nil]; omega) rfl
    (by simpa only [sepConj_emp, PartsCells] using held)

private theorem load_maximum (output : Ptr) (handle generation maximum : UInt32) :
    CTriple (L := L) (PartsCells output handle generation maximum) (CProg.loadU32 (output + 2))
      (fun actual heap => actual = maximum ∧ PartsCells output handle generation maximum heap) := by
  apply loadU32_rule
  intro heap held
  exact read_cells (p := output) (cs := [some (.u32 handle), some (.u32 generation), some (.u32 maximum)]) (F := emp) (i := 2) (by simp only [List.length_cons, List.length_nil]; omega) rfl
    (by simpa only [sepConj_emp, PartsCells] using held)

def wordsValid (handle generation maximum : UInt32) : Bool :=
  decide (handle ≠ 0 ∧ handle < 152043520 ∧ generation ≠ 0 ∧ generation ≤ maximum)

theorem validity_reads_stored_words (output : Ptr) (handle generation maximum : UInt32) :
    CTriple (L := L) (PartsCells output handle generation maximum) (validityProgram output)
      (fun valid heap => valid = wordsValid handle generation maximum ∧
        PartsCells output handle generation maximum heap) := by
  unfold validityProgram
  refine triple_bind _ (load_handle (L := L) output handle generation maximum) fun actual => ?_
  apply triple_pure
  intro same
  subst actual
  by_cases first : handle = 0
  · rw [if_neg (by simpa only [bne_iff_ne] using (not_not.mpr first))]
    exact triple_pre _ (fun heap held => ⟨by simp [wordsValid, first], held⟩)
      (triple_ret _ false _)
  · rw [if_pos (bne_iff_ne.mpr first)]
    refine triple_bind _ (load_handle (L := L) output handle generation maximum) fun actual => ?_
    apply triple_pure
    intro same
    subst actual
    by_cases second : handle < 152043520
    · rw [if_pos second]
      refine triple_bind _ (load_generation (L := L) output handle generation maximum) fun actual => ?_
      apply triple_pure
      intro same
      subst actual
      by_cases third : generation = 0
      · rw [if_neg (by simpa only [bne_iff_ne] using (not_not.mpr third))]
        exact triple_pre _ (fun heap held => ⟨by simp [wordsValid, third], held⟩)
          (triple_ret _ false _)
      · rw [if_pos (bne_iff_ne.mpr third)]
        refine triple_bind _ (load_generation (L := L) output handle generation maximum) fun actual => ?_
        apply triple_pure
        intro same
        subst actual
        refine triple_bind _ (load_maximum (L := L) output handle generation maximum) fun actual => ?_
        apply triple_pure
        intro same
        subst actual
        exact triple_pre _ (fun heap held => ⟨by simp [wordsValid, first, second, third], held⟩)
          (triple_ret _ (decide (generation ≤ maximum)) _)
    · rw [if_neg second]
      exact triple_pre _ (fun heap held => ⟨by simp [wordsValid, second], held⟩)
        (triple_ret _ false _)

/-- The selected source branch both materializes the existing codec and
returns its validity test. Raw checkpoints retain the three physical cells. -/
theorem parts_program_spec (identity : UInt32) (output : Ptr) (old : List (Option CVal))
    (length : old.length = 3) :
    CTriple (L := L) (Cells output old) (partsProgram identity output)
      (fun valid heap =>
        valid = decide (Representable ⟨unpackHandle identity.toNat, unpackGeneration identity.toNat⟩) ∧
        PartsCells output (IdentityParts.words identity).1 (IdentityParts.words identity).2.1
          (IdentityParts.words identity).2.2 heap) := by
  unfold partsProgram
  refine triple_bind _ (store_words_initializes output old length _ _ _) fun _ => ?_
  split
  · refine triple_post _ (validity_reads_stored_words output _ _ _) ?_
    intro valid heap holds
    refine ⟨?_, holds.2⟩
    rw [holds.1, wordsValid]
    congr 1
    exact propext (IdentityParts.valid_words_iff_representable identity)
  · rename_i outside
    have handleOutside := IdentityParts.outside_prefix_handle identity
      (fun h => outside (Or.inl h)) (fun h => outside (Or.inr (Or.inl h)))
      (fun h => outside (Or.inr (Or.inr (Or.inl h))))
      (fun h => outside (Or.inr (Or.inr (Or.inr h))))
    have invalid : ¬ Representable ⟨unpackHandle identity.toNat, unpackGeneration identity.toNat⟩ := by
      intro valid
      have inside := valid.2.1
      rw [← IdentityParts.words_handle_matches_codec] at inside
      change (IdentityParts.words identity).1.toNat < handleLimit at inside
      omega
    exact triple_pre _ (fun heap held => ⟨by simp [invalid], held⟩) (triple_ret _ false _)


/-- The handle wrapper keeps the completed parts computation, then reads its
stored handle even when the helper's validity result is false. -/
def handleProgram (identity : UInt32) (output : Ptr) : CProg CVal UInt32 := do
  let _ ← partsProgram identity output
  CProg.loadU32 output

def generationProgram (identity : UInt32) (output : Ptr) : CProg CVal UInt32 := do
  let _ ← partsProgram identity output
  CProg.loadU32 (output + 1)

theorem handle_program_spec (identity : UInt32) (output : Ptr) (old : List (Option CVal))
    (length : old.length = 3) :
    CTriple (L := L) (Cells output old) (handleProgram identity output)
      (fun handle heap => handle.toNat = unpackHandle identity.toNat ∧
        PartsCells output (IdentityParts.words identity).1 (IdentityParts.words identity).2.1
          (IdentityParts.words identity).2.2 heap) := by
  unfold handleProgram
  refine triple_bind _ (parts_program_spec identity output old length) fun valid => ?_
  apply triple_pure
  intro validity
  refine triple_post _ (load_handle (L := L) output _ _ _) ?_
  intro handle heap held
  refine ⟨?_, held.2⟩
  rw [held.1]
  exact IdentityParts.words_handle_matches_codec identity

theorem generation_program_spec (identity : UInt32) (output : Ptr) (old : List (Option CVal))
    (length : old.length = 3) :
    CTriple (L := L) (Cells output old) (generationProgram identity output)
      (fun generation heap => generation.toNat = unpackGeneration identity.toNat ∧
        PartsCells output (IdentityParts.words identity).1 (IdentityParts.words identity).2.1
          (IdentityParts.words identity).2.2 heap) := by
  unfold generationProgram
  refine triple_bind _ (parts_program_spec identity output old length) fun valid => ?_
  apply triple_pure
  intro validity
  refine triple_post _ (load_generation (L := L) output _ _ _) ?_
  intro generation heap held
  refine ⟨?_, held.2⟩
  rw [held.1]
  exact IdentityParts.words_generation_matches_codec identity

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityRead

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityRead
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ProductiveBlocks
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Three owned cells construct a completed retained execution; no completed
run or codec agreement is assumed as a component premise. -/
theorem retained_parts_completion (identity : UInt32) (output : Ptr)
    (storage : Storage CVal) (old : List (Option CVal)) (length : old.length = 3)
    (owned : Cells output old (heap storage)) :
    ∃ choices fuel final,
      (machine.run fuel (State.mk (partsProgram identity output) storage choices)).2 =
        .finished (.returned final) ∧
      final.answer = decide (Representable ⟨unpackHandle identity.toNat, unpackGeneration identity.toNat⟩) ∧
      PartsCells output (IdentityParts.words identity).1 (IdentityParts.words identity).2.1
        (IdentityParts.words identity).2.2 (heap final.storage) := by
  have spec := parts_program_spec (L := Excl (Option CVal)) identity output old length
  have safe := (spec (heap storage) owned).1
  obtain ⟨answer, after, ran⟩ := exists_runs (partsProgram identity output) (heap storage) safe
  have post := (spec (heap storage) owned).2 answer after ran
  obtain ⟨choices, fuel, final, answerCorrect, heapCorrect, completed⟩ :=
    source_execution_realized (partsProgram identity output) storage answer after safe ran
  refine ⟨choices, fuel, final, completed, answerCorrect.trans post.1, ?_⟩
  rw [heapCorrect]
  exact post.2

/-- An actual completed primitive run has the same codec result and stored
words. The saved native record remains separate from that semantic readout. -/
theorem retained_parts_reflection (identity : UInt32) (output : Ptr)
    (storage : Storage CVal) (old : List (Option CVal)) (length : old.length = 3)
    (owned : Cells output old (heap storage)) (choices : List AllocationChoice)
    (fuel : Nat) (final : Finished CVal Bool)
    (completed : (machine.run fuel (State.mk (partsProgram identity output) storage choices)).2 =
      .finished (.returned final)) :
    final.answer = decide (Representable ⟨unpackHandle identity.toNat, unpackGeneration identity.toNat⟩) ∧
      PartsCells output (IdentityParts.words identity).1 (IdentityParts.words identity).2.1
        (IdentityParts.words identity).2.2 (heap final.storage) := by
  exact ((parts_program_spec (L := Excl (Option CVal)) identity output old length)
    (heap storage) owned).2 _ _ (returned_sound _ _ _ completed)

/-- Larger scheduler grants cannot replay a completed helper's stores. -/
theorem retained_parts_completed_stable (identity : UInt32) (output : Ptr)
    (storage : Storage CVal) (choices : List AllocationChoice) (fuel extra : Nat)
    (final : Finished CVal Bool)
    (completed : (machine.run fuel (State.mk (partsProgram identity output) storage choices)).2 =
      .finished (.returned final)) :
    machine.run (fuel + extra) (State.mk (partsProgram identity output) storage choices) =
      machine.run fuel (State.mk (partsProgram identity output) storage choices) := by
  apply Machine.run_stable
  intro residual
  rw [completed]
  exact fun impossible => nomatch impossible

/-- The common retained executor composes a paused prefix with only its
saved suffix, including every already performed partial field store. -/
theorem retained_parts_resume (identity : UInt32) (output : Ptr)
    (storage : Storage CVal) (choices : List AllocationChoice) (first extra : Nat)
    (saved : State CVal Bool) (events : List (Receipt CVal))
    (paused : machine.run first (State.mk (partsProgram identity output) storage choices) =
      (events, .exhausted saved)) :
    machine.run (first + extra) (State.mk (partsProgram identity output) storage choices) =
      (events ++ (machine.run extra saved).1, (machine.run extra saved).2) :=
  resume_after_prefix first extra _ saved events paused

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityRead

set_option autoImplicit false


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityWrapper
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ObjectBindings

/-- Execute the parsed parts helper and return its actual C result. Wrong
argument shapes and incomplete control do not invent a decoded value. -/
def partsCall (allowance : Nat) : Calls := fun name values =>
  if name = "cetta_frame_identity_parts".toList then
    match values with
    | [.u32 identity, .ptr (some address)] => do
        let result ← executeWith {} (fieldAssignment expression) IdentityRead.layout 0
          (allowance + 8) (IdentityRead.environment identity address) IdentitySource.partsBody
        match result with
        | .finished (.returned _ (some value)) => pure value
        | _ => CProg.undefined
    | _ => CProg.undefined
  else CProg.undefined

theorem parts_call_is_actual_body (allowance : Nat) (identity : UInt32) (address : Ptr) :
    partsCall allowance "cetta_frame_identity_parts".toList [.u32 identity, .ptr (some address)] =
      (IdentityRead.partsProgram identity address >>= fun flag => pure (.bool flag)) := by
  simp only [partsCall, ↓reduceIte]
  rw [IdentityRead.actual_parts_body]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

def profile (allowance : Nat) : Profile where
  values := partsCall allowance
  locations := fun _ => none
  outsideTypes := fun _ => none
  outsidePlaces := fun _ => none
  fieldTypes := fun _ _ => some ⟨"uint32_t".toList, 0⟩
  cellExtent := fun type => if type = IdentitySource.partsType then some 3 else none
  byteExtent := fun _ => none
  sizeWidth := .bits64
  recordTypes := [IdentitySource.partsType]
  recordFields := some (fun type => if type = IdentitySource.partsType then IdentityRead.layout else fun _ => none)

def operand : CExpr := .call "cetta_frame_identity_parts".toList
  [IdentitySource.id "identity", .unary .address (IdentitySource.id "parts")]

def effects (allowance : Nat) : Layout → Context → CExpr → CProg CVal Unit :=
  EffectStatements.withObjects (profile allowance) (fun _ _ => CProg.undefined)

def service (allowance : Nat) (region : AutomaticRegion Context) : ScopedServices Context :=
  ObjectBindings.services (profile allowance) region (effects allowance)

theorem read_actual_arguments (allowance : Nat) (context : Context) (identity : UInt32)
    (address : Ptr)
    (identityBound : context "identity".toList = some (.scalar ⟨"CettaFrameIdentity".toList, 0⟩ (some (.u32 identity))))
    (partsBound : context "parts".toList = some (.object IdentitySource.partsType address)) :
    ObjectBindings.read (profile allowance) IdentityRead.layout context operand =
      (IdentityRead.partsProgram identity address >>= fun flag => pure (.bool flag)) := by
  have arg1 := initialized_local_keeps_its_value (profile allowance) IdentityRead.layout context
    "identity".toList ⟨"CettaFrameIdentity".toList, 0⟩ (.u32 identity) identityBound
  have arg2 := local_object_address_does_not_read_value (profile allowance) IdentityRead.layout context
    "parts".toList IdentitySource.partsType address partsBound
  unfold operand
  change (argumentsWithNames
    (localOrLocated (values context) (declared context) (profile allowance).locations)
      (profile allowance).values IdentityRead.layout
      [IdentitySource.id "identity", .unary .address (IdentitySource.id "parts")]
      (objects (profile allowance) context) >>= partsCall allowance "cetta_frame_identity_parts".toList) = _
  unfold IdentitySource.id at *
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (ObjectBindings.read (profile allowance) IdentityRead.layout context (.identifier "identity".toList) >>= fun first =>
    ObjectBindings.read (profile allowance) IdentityRead.layout context (.unary .address (.identifier "parts".toList)) >>= fun second =>
      partsCall allowance "cetta_frame_identity_parts".toList [first, second]) = _
  rw [arg1, arg2]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  exact parts_call_is_actual_body allowance identity address

theorem discarded_actual_call (allowance : Nat) (context : Context) (identity : UInt32)
    (address : Ptr)
    (identityBound : context "identity".toList = some (.scalar ⟨"CettaFrameIdentity".toList, 0⟩ (some (.u32 identity))))
    (partsBound : context "parts".toList = some (.object IdentitySource.partsType address)) :
    effects allowance IdentityRead.layout context (.cast ⟨"void".toList, 0⟩ operand) =
      (IdentityRead.partsProgram identity address >>= fun _ => pure ()) := by
  rw [effects, EffectStatements.explicit_void_cast_keeps_operand,
    read_actual_arguments allowance context identity address identityBound partsBound]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem read_return_field (allowance : Nat) (context : Context) (address : Ptr)
    (name : String) (offset : Nat)
    (partsBound : context "parts".toList = some (.object IdentitySource.partsType address))
    (field : IdentityRead.layout name.toList = some ⟨offset, .word⟩) :
    ObjectBindings.read (profile allowance) IdentityRead.layout context
      (.field (IdentitySource.id "parts") name.toList false) =
      (CProg.loadU32 (address + offset) >>= fun word => pure (.u32 word)) := by
  unfold IdentitySource.id
  rw [local_object_field_keeps_place_and_inventory (profile allowance) IdentityRead.layout context
    (fun type => if type = IdentitySource.partsType then IdentityRead.layout else fun _ => none)
    "parts".toList name.toList IdentitySource.partsType address rfl partsBound]
  simp only [if_true, ReadExpressions.field, field, pointer,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

/-- The body keeps the actual automatic region and its complete local context.
The Boolean helper return is discarded only after its writes and reached
validation loads; the wrapper then reads the stored selected field. -/
theorem actual_wrapper_body (allowance fuel : Nat) (region : AutomaticRegion Context)
    (context : Context) (identity : UInt32) (name : String) (offset : Nat)
    (identityBound : context "identity".toList = some (.scalar ⟨"CettaFrameIdentity".toList, 0⟩ (some (.u32 identity))))
    (field : IdentityRead.layout name.toList = some ⟨offset, .word⟩) :
    executeScopedWith (service allowance region) IdentityRead.layout 0 (fuel + 3) context
      (IdentitySource.wrapperBody name) =
      ((region "parts".toList 3 fun address =>
        IdentityRead.partsProgram identity address >>= fun _ =>
          CProg.loadU32 (address + offset) >>= fun word =>
            pure (.finished (.returned
              (Function.update context "parts".toList (some (.object IdentitySource.partsType address)))
              (some (.u32 word))))) >>= fun result => pure (restore "parts".toList (context "parts".toList) result)) := by
  unfold IdentitySource.wrapperBody
  rw [executeScopedWith.eq_def]
  dsimp only [service, ObjectBindings.services]
  have extent : (profile allowance).recordExtent IdentitySource.partsType = some 3 := by
    simp only [Profile.recordExtent, profile, List.mem_singleton, ↓reduceIte]
  simp only [declaration, extent]
  congr 1
  congr 1
  funext address
  let updated := Function.update context "parts".toList (some (.object IdentitySource.partsType address))
  have pb : updated "parts".toList = some (.object IdentitySource.partsType address) := by simp only [updated, Function.update_self]
  have ib : updated "identity".toList = some (.scalar ⟨"CettaFrameIdentity".toList, 0⟩ (some (.u32 identity))) := by
    simpa only [updated, Function.update_of_ne (by decide : "identity".toList ≠ "parts".toList)] using identityBound
  rw [scoped_effect_keeps_continuation]
  change (effects allowance IdentityRead.layout updated (.cast ⟨"void".toList, 0⟩ operand) >>= fun _ => _) = _
  rw [discarded_actual_call _ _ _ _ ib pb]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext ignored
  rw [executeScopedWith.eq_def]
  change (ObjectBindings.read (profile allowance) IdentityRead.layout updated
    (.field (IdentitySource.id "parts") name.toList false) >>= fun value => pure (ReadBlock.Result.finished (.returned updated (some value)))) = _
  rw [read_return_field _ _ _ _ _ pb field]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl


/-- A bracketed automatic region retains entry and exit around the real
callee and final field read. The previous lexical binding is restored after
the region returns; it is not exposed as the local record's scalar value. -/
theorem actual_wrapper_bracket (allowance fuel : Nat)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit)
    (context : Context) (identity : UInt32) (name : String) (offset : Nat)
    (identityBound : context "identity".toList = some (.scalar ⟨"CettaFrameIdentity".toList, 0⟩ (some (.u32 identity))))
    (field : IdentityRead.layout name.toList = some ⟨offset, .word⟩) :
    executeScopedWith (service allowance (AutomaticRegion.bracket enter leave))
      IdentityRead.layout 0 (fuel + 3) context (IdentitySource.wrapperBody name) =
      (enter "parts".toList 3 >>= fun address =>
        IdentityRead.partsProgram identity address >>= fun _ =>
          CProg.loadU32 (address + offset) >>= fun word =>
            leave "parts".toList address 3 >>= fun _ =>
              pure (.finished (.returned context (some (.u32 word))))) := by
  rw [actual_wrapper_body _ _ _ _ _ _ _ identityBound field]
  simp only [AutomaticRegion.bracket, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq,
    Prog.ret_bind, returned_local_restores_previous_binding]

theorem actual_handle_body (allowance fuel : Nat)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit)
    (context : Context) (identity : UInt32)
    (identityBound : context "identity".toList = some (.scalar ⟨"CettaFrameIdentity".toList, 0⟩ (some (.u32 identity)))) :
    executeScopedWith (service allowance (AutomaticRegion.bracket enter leave))
      IdentityRead.layout 0 (fuel + 3) context IdentitySource.handleBody =
      (enter "parts".toList 3 >>= fun address =>
        IdentityRead.handleProgram identity address >>= fun word =>
          leave "parts".toList address 3 >>= fun _ =>
            pure (.finished (.returned context (some (.u32 word))))) := by
  rw [IdentitySource.handleBody, actual_wrapper_bracket _ _ _ _ _ _ "handle" 0 identityBound rfl]
  simp only [IdentityRead.handleProgram, Prog.bind_eq, Prog.bind_assoc]
  rfl

theorem actual_generation_body (allowance fuel : Nat)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit)
    (context : Context) (identity : UInt32)
    (identityBound : context "identity".toList = some (.scalar ⟨"CettaFrameIdentity".toList, 0⟩ (some (.u32 identity)))) :
    executeScopedWith (service allowance (AutomaticRegion.bracket enter leave))
      IdentityRead.layout 0 (fuel + 3) context IdentitySource.generationBody =
      (enter "parts".toList 3 >>= fun address =>
        IdentityRead.generationProgram identity address >>= fun word =>
          leave "parts".toList address 3 >>= fun _ =>
            pure (.finished (.returned context (some (.u32 word))))) := by
  rw [IdentitySource.generationBody, actual_wrapper_bracket _ _ _ _ _ _ "generation" 1 identityBound rfl]
  simp only [IdentityRead.generationProgram, Prog.bind_eq, Prog.bind_assoc]

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityWrapper

set_option autoImplicit false


end NativeIdentityHelperPackage


/-! ## Published numbered-symbol reads

The managed current-ID guard, chunk selection and row-reference helpers retain
the actual selected C source. Physical count, pointer and byte reads construct
the numbered-symbol data; the source spelling bridge is downstream in the
existing payload reader. Logical layout, acquire/publication and borrowed
lifetimes remain explicit. The managed ID-zero lookup algorithm and registration
are separate components.
-/
section NumberedSymbolReadout
set_option maxHeartbeats 1200000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ReadExpressions CellPermission

/-- The two coordinates used by the actual chunked SymbolEntry table. -/
def chunkIndex (identifier : UInt32) : Nat := (identifier >>> 14).toNat
def rowIndex (identifier : UInt32) : Nat := (identifier &&& 16383).toNat

/-- Declared fields occupy five logical scalar cells. Native byte layout is
an independent representation obligation, not inferred from this stride. -/
def entryStride : Nat := 5

def entryPointer (chunk : Ptr) (identifier : UInt32) : Ptr :=
  chunk + (rowIndex identifier * entryStride)

theorem chunk_index_exact (identifier : UInt32) :
    chunkIndex identifier = identifier.toNat / 16384 := by
  simp [chunkIndex, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem row_index_exact (identifier : UInt32) :
    rowIndex identifier = identifier.toNat % 16384 := by
  simp only [rowIndex, UInt32.toNat_and]
  change identifier.toNat &&& (2 ^ 14 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ 14

theorem chunk_row_reconstruct (identifier : UInt32) :
    chunkIndex identifier * 16384 + rowIndex identifier = identifier.toNat := by
  rw [chunk_index_exact, row_index_exact]
  omega

theorem chunk_within_directory (identifier : UInt32) : chunkIndex identifier < 262144 := by
  rw [chunk_index_exact]
  have bound := identifier.toNat_lt
  omega

theorem row_within_chunk (identifier : UInt32) : rowIndex identifier < 16384 := by
  rw [row_index_exact]
  exact Nat.mod_lt _ (by decide)

/-- Actual entry-chunk source order: the guard reads entry_chunks, then the
return expression reads it again. Snapshot stability licenses equal values,
without deleting either read from the operation tree. -/
def entryChunk (table : Option Ptr) (identifier : UInt32) : CProg CVal (Option Ptr) := do
  let nullTable ← CProg.ptrEq table none
  if nullTable then pure none else
    match table with
    | none => CProg.undefined
    | some table => do
      let guardedChunks ← CProg.loadPtr (table + 4)
      let nullChunks ← CProg.ptrEq guardedChunks none
      if nullChunks then pure none else do
        let chunks ← CProg.loadPtr (table + 4)
        match chunks with
        | none => CProg.undefined
        | some chunks => CProg.loadPtr (chunks + chunkIndex identifier)

/-- The actual entry-ref helper calls the chunk helper, checks its returned
pointer, then forms the selected row address. -/
def entryRef (table : Option Ptr) (identifier : UInt32) : CProg CVal (Option Ptr) := do
  let chunk ← entryChunk table identifier
  let nullChunk ← CProg.ptrEq chunk none
  if nullChunk then pure none else
    match chunk with
    | none => CProg.undefined
    | some chunk => pure (some (entryPointer chunk identifier))

/-- Sequential view after the native acquire of entry_len. The ABI and
acquire/publication contract must establish this typed cell snapshot. The
read does not freeze or insert any table entry. -/
def publishedEntry (table : Option Ptr) (identifier : UInt32) : CProg CVal (Option Ptr) := do
  let nullTable ← CProg.ptrEq table none
  if nullTable || identifier == 0 then pure none else
    match table with
    | none => CProg.undefined
    | some table => do
      let count ← CProg.loadU32 (table + 5)
      if identifier ≥ count then pure none else entryRef (some table) identifier

/-- Actual stored members are nullable; the caller keeps the literal-empty
fallback distinct from a stored buffer. No length is fabricated from strlen. -/
def storedSpelling (table : Option Ptr) (identifier : UInt32) :
    CProg CVal (Option (Option Ptr × UInt32)) := do
  let selected ← publishedEntry table identifier
  match selected with
  | none => pure none
  | some entry => do
    let bytes ← CProg.loadPtr entry
    let length ← CProg.loadU32 (entry + 1)
    pure (some (bytes, length))

variable {L : Type} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- A published row describes the actual table and chunk cells. It contains
neither a helper execution nor its final spelling or source Atom. -/
structure PublishedRow (heap : Heap L) (table : Ptr) (identifier : UInt32) where
  count : UInt32
  chunks : Ptr
  chunk : Ptr
  nonzero : identifier ≠ 0
  within : identifier < count
  tableLive : Valid heap table
  chunksLive : Valid heap chunks
  chunkLive : Valid heap chunk
  countCell : Reads (table + 5) (.u32 count) heap
  chunksCell : Reads (table + 4) (.ptr (some chunks)) heap
  chunkCell : Reads (chunks + chunkIndex identifier) (.ptr (some chunk)) heap

theorem entry_chunk_wp (heap : Heap L) (table : Ptr) (identifier : UInt32)
    (row : PublishedRow heap table identifier) (post : Option Ptr → Heap L → Prop)
    (after : post (some row.chunk) heap) :
    (entryChunk (some table) identifier).wp act post heap := by
  unfold entryChunk
  rw [wp_bind']
  apply wp_ptrEq (p := some table) (q := none) (σ := heap) row.tableLive trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply SymbolForward.load_pointer_wp heap (table + 4) (some row.chunks) row.chunksCell
  rw [wp_bind']
  apply wp_ptrEq (p := some row.chunks) (q := none) (σ := heap) row.chunksLive trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply SymbolForward.load_pointer_wp heap (table + 4) (some row.chunks) row.chunksCell
  exact SymbolForward.load_pointer_wp heap (row.chunks + chunkIndex identifier)
    (some row.chunk) row.chunkCell post after

theorem entry_ref_wp (heap : Heap L) (table : Ptr) (identifier : UInt32)
    (row : PublishedRow heap table identifier)
    (post : Option Ptr → Heap L → Prop)
    (after : post (some (entryPointer row.chunk identifier)) heap) :
    (entryRef (some table) identifier).wp act post heap := by
  unfold entryRef
  rw [wp_bind']
  apply entry_chunk_wp heap table identifier row
  rw [wp_bind']
  apply wp_ptrEq (p := some row.chunk) (q := none) (σ := heap) row.chunkLive trivial
  simpa only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, wp_pure] using after

theorem published_entry_wp (heap : Heap L) (table : Ptr) (identifier : UInt32)
    (row : PublishedRow heap table identifier)
    (post : Option Ptr → Heap L → Prop)
    (after : post (some (entryPointer row.chunk identifier)) heap) :
    (publishedEntry (some table) identifier).wp act post heap := by
  unfold publishedEntry
  rw [wp_bind']
  apply wp_ptrEq (p := some table) (q := none) (σ := heap) row.tableLive trivial
  simp only [reduceCtorEq, decide_false, Bool.false_or, beq_eq_false_iff_ne.mpr row.nonzero,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply SymbolForward.load_word_wp heap (table + 5) row.count row.countCell
  rw [if_neg (UInt32.not_le.mpr row.within)]
  exact entry_ref_wp heap table identifier row post after

theorem stored_spelling_wp (heap : Heap L) (table : Ptr) (identifier : UInt32)
    (row : PublishedRow heap table identifier) (buffer : Option Ptr) (length : UInt32)
    (bytesCell : Reads (entryPointer row.chunk identifier) (.ptr buffer) heap)
    (lengthCell : Reads (entryPointer row.chunk identifier + 1) (.u32 length) heap)
    (post : Option (Option Ptr × UInt32) → Heap L → Prop)
    (after : post (some (buffer, length)) heap) :
    (storedSpelling (some table) identifier).wp act post heap := by
  unfold storedSpelling
  rw [wp_bind']
  apply published_entry_wp heap table identifier row
  rw [wp_bind']
  apply SymbolForward.load_pointer_wp heap (entryPointer row.chunk identifier) buffer bytesCell
  rw [wp_bind']
  apply SymbolForward.load_word_wp heap (entryPointer row.chunk identifier + 1) length lengthCell
  simpa only [wp_pure] using after

/-- This checked projection uses the same acquired physical snapshot. Missing
cells and unpublished/zero IDs fail before selecting a spelling. -/
def publishedEntry? (heap : Heap L) (table : Ptr) (identifier : UInt32) : Option Ptr := do
  if identifier = 0 then none else
    let count ← PhysicalAtoms.word? heap (table + 5)
    if identifier ≥ count then none else
      let chunks ← PhysicalAtoms.pointer? heap (table + 4)
      let chunks ← chunks
      let chunk ← PhysicalAtoms.pointer? heap (chunks + chunkIndex identifier)
      let chunk ← chunk
      pure (entryPointer chunk identifier)

def spelling? (heap : Heap L) (table : Ptr) (identifier : UInt32) : Option (Ptr × UInt32) := do
  let entry ← publishedEntry? heap table identifier
  let buffer ← PhysicalAtoms.pointer? heap entry
  let buffer ← buffer
  let length ← PhysicalAtoms.word? heap (entry + 1)
  pure (buffer, length)

private theorem cell_of_reads (heap : Heap L) (pointer : Ptr) (value : CVal)
    (held : Reads pointer value heap) : PhysicalAtoms.cell? heap pointer = some value := by
  unfold Reads at held
  simp only [PhysicalAtoms.cell?, held, Option.join_some]

private theorem word_of_reads (heap : Heap L) (pointer : Ptr) (value : UInt32)
    (held : Reads pointer (.u32 value) heap) : PhysicalAtoms.word? heap pointer = some value := by
  simp [PhysicalAtoms.word?, cell_of_reads heap pointer (.u32 value) held]

private theorem pointer_of_reads (heap : Heap L) (pointer : Ptr) (value : Option Ptr)
    (held : Reads pointer (.ptr value) heap) : PhysicalAtoms.pointer? heap pointer = some value := by
  simp [PhysicalAtoms.pointer?, cell_of_reads heap pointer (.ptr value) held]

theorem published_entry_projection (heap : Heap L) (table : Ptr) (identifier : UInt32)
    (row : PublishedRow heap table identifier) :
    publishedEntry? heap table identifier = some (entryPointer row.chunk identifier) := by
  simp [publishedEntry?, row.nonzero,
    word_of_reads heap (table + 5) row.count row.countCell,
    UInt32.not_le.mpr row.within,
    pointer_of_reads heap (table + 4) (some row.chunks) row.chunksCell,
    pointer_of_reads heap (row.chunks + chunkIndex identifier) (some row.chunk) row.chunkCell]

theorem spelling_projection (heap : Heap L) (table : Ptr) (identifier : UInt32)
    (row : PublishedRow heap table identifier) (buffer : Ptr) (length : UInt32)
    (bytesCell : Reads (entryPointer row.chunk identifier) (.ptr (some buffer)) heap)
    (lengthCell : Reads (entryPointer row.chunk identifier + 1) (.u32 length) heap) :
    spelling? heap table identifier = some (buffer, length) := by
  simp [spelling?, published_entry_projection heap table identifier row,
    pointer_of_reads heap _ (some buffer) bytesCell, word_of_reads heap _ length lengthCell]

/-- The existing byte observer supplies table payloads. This definition reads
actual physical fields and byte cells; no spelling callback is supplied. -/
def physicalBytes? (inventory : PhysicalAtoms.Inventory) (heap : Heap L)
    (table : Ptr) (identifier : UInt32) : Option ByteArray := do
  let (buffer, length) ← spelling? heap table identifier
  let bytes ← Mettapedia.GSLT.LanguageDef.NativeOps.ByteViews.targetBlock
    (PhysicalAtoms.memory inventory heap) (CurrentValueRead.physicalAddress buffer) length.toNat
  pure ⟨bytes.toArray⟩

theorem physical_bytes_from_owned (inventory : PhysicalAtoms.Inventory) (heap : Heap L)
    (table : Ptr) (identifier : UInt32) (row : PublishedRow heap table identifier)
    (buffer : Ptr) (length : UInt32) (bytes : List UInt8) (rest : Heap L → Prop)
    (bytesCell : Reads (entryPointer row.chunk identifier) (.ptr (some buffer)) heap)
    (lengthCell : Reads (entryPointer row.chunk identifier + 1) (.u32 length) heap)
    (count : bytes.length = length.toNat)
    (registered : ∀ index, index < bytes.length → inventory (buffer + index) = some .byteCell)
    (owned : (Cells buffer (bytes.map (fun byte => some (CVal.u8 byte))) ∗ rest) heap) :
    physicalBytes? inventory heap table identifier = some ⟨bytes.toArray⟩ := by
  unfold physicalBytes?
  rw [spelling_projection heap table identifier row buffer length bytesCell lengthCell]
  change (Mettapedia.GSLT.LanguageDef.NativeOps.ByteViews.targetBlock
    (PhysicalAtoms.memory inventory heap) (CurrentValueRead.physicalAddress buffer)
    length.toNat).bind (fun actual => some (⟨actual.toArray⟩ : ByteArray)) =
      some (⟨bytes.toArray⟩ : ByteArray)
  rw [← count, PhysicalAtoms.byte_block_from_owned inventory heap buffer bytes rest registered owned]
  rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Source
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions

/-- Declaration-order logical fields. Concurrent publication, byte ABI and
borrowed table lifetime are separate from this scalar-cell source projection. -/
def layout : Layout := fun name =>
  if name = "entry_chunks".toList then some ⟨4, .pointer⟩
  else if name = "entry_len".toList then some ⟨5, .word⟩
  else if name = "bytes".toList then some ⟨0, .pointer⟩
  else if name = "len".toList then some ⟨1, .word⟩
  else if name = "hash".toList then some ⟨2, .word64⟩
  else none

def names (table chunk entry : Option Ptr) (identifier : UInt32) : NameReads := fun name =>
  if name = "st".toList then pure (.ptr table)
  else if name = "chunk".toList then pure (.ptr chunk)
  else if name = "entry".toList then pure (.ptr entry)
  else if name = "id".toList then pure (.u32 identifier)
  else if name = "SYMBOL_ENTRY_CHUNK_BITS".toList then pure (.u32 14)
  else if name = "SYMBOL_ENTRY_CHUNK_MASK".toList then pure (.u32 16383)
  else CProg.undefined

def objects : ObjectReads where
  place := some fun _ => none
  indexStride := fun array => match array with
    | .identifier name => if name = "chunk".toList then some entryStride else none
    | _ => none
  indexKind := some fun array => match array with
    | .field (.identifier name) member true =>
      if name = "st".toList ∧ member = "entry_chunks".toList then some .pointer else none
    | _ => none

def read (table chunk entry : Option Ptr) (identifier : UInt32) (operand : CExpr) : CProg CVal CVal :=
  expressionWithNames (names table chunk entry identifier) noCalls layout operand objects

def chunksOperand : CExpr := .field (.identifier "st".toList) "entry_chunks".toList true
def chunkOperand : CExpr := .index chunksOperand
  (.binary .shiftRight (.identifier "id".toList) (.identifier "SYMBOL_ENTRY_CHUNK_BITS".toList))
def entryOperand : CExpr := .unary .address (.index (.identifier "chunk".toList)
  (.binary .bitAnd (.identifier "id".toList) (.identifier "SYMBOL_ENTRY_CHUNK_MASK".toList)))
def countAddress : CExpr := .unary .address
  (.field (.identifier "st".toList) "entry_len".toList true)
def bytesOperand : CExpr := .field (.identifier "entry".toList) "bytes".toList true
def lengthOperand : CExpr := .field (.identifier "entry".toList) "len".toList true

theorem chunks_use_actual_pointer (table : Ptr) (chunk entry : Option Ptr) (identifier : UInt32) :
    read (some table) chunk entry identifier chunksOperand =
      (CProg.loadPtr (table + 4) >>= fun pointer => pure (.ptr pointer)) := rfl

theorem chunk_uses_actual_index (table : Ptr) (chunk entry : Option Ptr) (identifier : UInt32) :
    read (some table) chunk entry identifier chunkOperand =
      (do let chunks ← CProg.loadPtr (table + 4)
          match chunks with
          | none => CProg.undefined
          | some chunks => do
            let found ← CProg.loadPtr (chunks + chunkIndex identifier)
            pure (.ptr found)) := by
  change ((read (some table) chunk entry identifier chunksOperand >>= fun address =>
    pure (CVal.u32 identifier) >>= fun actual =>
    pure (CVal.u32 14) >>= fun bits => binary .shiftRight actual bits >>= fun position =>
    indexedScalar .pointer address position)) = _
  rw [chunks_use_actual_pointer]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext chunks
  cases chunks with
  | none => rfl
  | some chunks => rfl

theorem entry_address_uses_actual_row (table entry : Option Ptr) (chunk : Ptr) (identifier : UInt32) :
    read table (some chunk) entry identifier entryOperand =
      pure (.ptr (some (entryPointer chunk identifier))) := by
  rfl

theorem count_address_is_actual_field (table : Ptr) (chunk entry : Option Ptr) (identifier : UInt32) :
    read (some table) chunk entry identifier countAddress = pure (.ptr (some (table + 5))) := rfl

theorem bytes_use_actual_member (table chunk : Option Ptr) (entry : Ptr) (identifier : UInt32) :
    read table chunk (some entry) identifier bytesOperand =
      (CProg.loadPtr entry >>= fun actual => pure (.ptr actual)) := by
  change (CProg.loadPtr (entry + 0) >>= fun actual => pure (CVal.ptr actual)) = _
  rw [ptr_add_zero]

theorem length_uses_actual_member (table chunk : Option Ptr) (entry : Ptr) (identifier : UInt32) :
    read table chunk (some entry) identifier lengthOperand =
      (CProg.loadU32 (entry + 1) >>= fun actual => pure (.u32 actual)) := rfl

def chunkTokens : List Token := [.identifier "st".toList, .punctuation "->".toList,
  .identifier "entry_chunks".toList, .punctuation "[".toList, .identifier "id".toList,
  .punctuation ">>".toList, .identifier "SYMBOL_ENTRY_CHUNK_BITS".toList, .punctuation "]".toList]
def entryTokens : List Token := [.punctuation "&".toList, .identifier "chunk".toList,
  .punctuation "[".toList, .identifier "id".toList, .punctuation "&".toList,
  .identifier "SYMBOL_ENTRY_CHUNK_MASK".toList, .punctuation "]".toList]

theorem actual_chunk_operand_parses :
    expressionText? [] "st->entry_chunks[id >> SYMBOL_ENTRY_CHUNK_BITS]".toList = some chunkOperand := by
  have lexed : lex "st->entry_chunks[id >> SYMBOL_ENTRY_CHUNK_BITS]".toList = .ok chunkTokens := by
    decide +kernel
  unfold expressionText?
  rw [lexed]
  rfl

theorem actual_entry_operand_parses :
    expressionText? [] "&chunk[id & SYMBOL_ENTRY_CHUNK_MASK]".toList = some entryOperand := by
  have lexed : lex "&chunk[id & SYMBOL_ENTRY_CHUNK_MASK]".toList = .ok entryTokens := by
    decide +kernel
  unfold expressionText?
  rw [lexed]
  rfl

theorem actual_member_operands_parse :
    expressionText? [] "&st->entry_len".toList = some countAddress ∧
    expressionText? [] "entry->bytes".toList = some bytesOperand ∧
    expressionText? [] "entry->len".toList = some lengthOperand := by
  exact ⟨rfl, rfl, rfl⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Source

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open CellPermission

variable {L : Type} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

theorem accepted_bytes_are_published (inventory : PhysicalAtoms.Inventory)
    (heap : Heap L) (table : Ptr) (identifier count : UInt32) (bytes : ByteArray)
    (published : Reads (table + 5) (.u32 count) heap)
    (accepted : physicalBytes? inventory heap table identifier = some bytes) :
    identifier ≠ 0 ∧ identifier < count := by
  by_cases zero : identifier = 0
  · simp [physicalBytes?, spelling?, publishedEntry?, zero] at accepted
  · refine ⟨zero, ?_⟩
    by_contra outside
    have above : count ≤ identifier := UInt32.not_lt.mp outside
    simp [physicalBytes?, spelling?, publishedEntry?, zero,
      word_of_reads heap (table + 5) count published, above] at accepted

/-- Independent declared contents of one published table entry. Its payload
is tied below to actual memory, rather than to any evaluator result. -/
structure EntryImage where
  identifier : UInt32
  buffer : Ptr
  length : UInt32
  bytes : List UInt8

/-- The table's published, borrowed snapshot. Coverage is by numeric ID and
physical row contents; uniqueness is the table's storage invariant. Establishing
this snapshot across the native acquire and lifetime boundary is a separate
component contract. No helper-return equation is an input field. -/
structure PublishedTable (inventory : PhysicalAtoms.Inventory) (heap : Heap L) where
  table : Ptr
  count : UInt32
  countCell : Reads (table + 5) (.u32 count) heap
  entries : List EntryImage
  unique : entries.Pairwise (fun first second => first.bytes ≠ second.bytes)
  covered : ∀ identifier, identifier ≠ 0 → identifier < count →
    ∃ entry ∈ entries, entry.identifier = identifier
  rows : ∀ entry ∈ entries, PublishedRow heap table entry.identifier
  buffers : ∀ entry (member : entry ∈ entries),
    Reads (entryPointer (rows entry member).chunk entry.identifier) (.ptr (some entry.buffer)) heap
  lengths : ∀ entry (member : entry ∈ entries),
    Reads (entryPointer (rows entry member).chunk entry.identifier + 1) (.u32 entry.length) heap
  byteCount : ∀ entry ∈ entries, entry.bytes.length = entry.length.toNat
  registered : ∀ entry ∈ entries, ∀ index, index < entry.bytes.length →
    inventory (entry.buffer + index) = some .byteCell
  bytesHeld : ∀ entry ∈ entries, ∃ rest : Heap L → Prop,
    (Cells entry.buffer (entry.bytes.map (fun byte => some (CVal.u8 byte))) ∗ rest) heap

theorem PublishedTable.entry_bytes {inventory : PhysicalAtoms.Inventory} {heap : Heap L}
    (snapshot : PublishedTable inventory heap) (entry : EntryImage) (member : entry ∈ snapshot.entries) :
    physicalBytes? inventory heap snapshot.table entry.identifier = some ⟨entry.bytes.toArray⟩ := by
  obtain ⟨rest, held⟩ := snapshot.bytesHeld entry member
  exact physical_bytes_from_owned inventory heap snapshot.table entry.identifier
    (snapshot.rows entry member) entry.buffer entry.length entry.bytes rest
    (snapshot.buffers entry member) (snapshot.lengths entry member)
    (snapshot.byteCount entry member) (snapshot.registered entry member) held

theorem PublishedTable.accepted_entry {inventory : PhysicalAtoms.Inventory} {heap : Heap L}
    (snapshot : PublishedTable inventory heap) (identifier : UInt32) (bytes : ByteArray)
    (accepted : physicalBytes? inventory heap snapshot.table identifier = some bytes) :
    ∃ entry ∈ snapshot.entries, entry.identifier = identifier ∧ bytes = ⟨entry.bytes.toArray⟩ := by
  obtain ⟨nonzero, within⟩ := accepted_bytes_are_published inventory heap snapshot.table
    identifier snapshot.count bytes snapshot.countCell accepted
  obtain ⟨entry, member, same⟩ := snapshot.covered identifier nonzero within
  refine ⟨entry, member, same, ?_⟩
  have actual := snapshot.entry_bytes entry member
  rw [same, accepted] at actual
  exact Option.some.inj actual

private theorem entry_eq_of_same_bytes (entries : List EntryImage)
    (unique : entries.Pairwise (fun first second => first.bytes ≠ second.bytes))
    (first second : EntryImage) (firstIn : first ∈ entries) (secondIn : second ∈ entries)
    (same : first.bytes = second.bytes) : first = second := by
  induction entries with
  | nil => simp at firstIn
  | cons head tail ih =>
      obtain ⟨headDifferent, tailUnique⟩ := List.pairwise_cons.mp unique
      rcases List.mem_cons.mp firstIn with firstHead | firstTail
      · subst first
        rcases List.mem_cons.mp secondIn with secondHead | secondTail
        · exact secondHead.symm
        · exact False.elim (headDifferent second secondTail same)
      · rcases List.mem_cons.mp secondIn with secondHead | secondTail
        · subst second
          exact False.elim (headDifferent first firstTail same.symm)
        · exact ih tailUnique firstTail secondTail

theorem PublishedTable.readout_unique {inventory : PhysicalAtoms.Inventory} {heap : Heap L}
    (snapshot : PublishedTable inventory heap) (first second : UInt32) (bytes : ByteArray)
    (firstRead : physicalBytes? inventory heap snapshot.table first = some bytes)
    (secondRead : physicalBytes? inventory heap snapshot.table second = some bytes) : first = second := by
  obtain ⟨firstEntry, firstIn, firstId, firstBytes⟩ := snapshot.accepted_entry first bytes firstRead
  obtain ⟨secondEntry, secondIn, secondId, secondBytes⟩ := snapshot.accepted_entry second bytes secondRead
  have same : firstEntry.bytes = secondEntry.bytes := by
    have encoded := firstBytes.symm.trans secondBytes
    have readout := congrArg (fun value : ByteArray => value.data.toList) encoded
    simpa only [List.toList_toArray] using readout
  have entriesSame := entry_eq_of_same_bytes snapshot.entries snapshot.unique
    firstEntry secondEntry firstIn secondIn same
  exact firstId.symm.trans (entriesSame ▸ secondId)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Current
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions StatementBlock

abbrev Lookup := Option Ptr → CProg CVal UInt32

def names (environment : Environment) : NameReads := fun name =>
  if name = "ATOM_SYMBOL".toList ∨ name = "SYMBOL_ID_NONE".toList then pure (.u32 0)
  else resolved (environment name)

def calls (lookup : Lookup) : Calls := fun name values =>
  if name = "atom_symbol_lookup_spelling_id".toList then
    match values with
    | [.ptr atom] => lookup atom >>= fun identifier => pure (.u32 identifier)
    | _ => CProg.undefined
  else CProg.undefined

def read (lookup : Lookup) (environment : Environment) (operand : CExpr) : CProg CVal CVal :=
  expressionWithNames (names environment) (calls lookup) SymbolSpelling.layout operand

def atomOperand : CExpr := .identifier "atom".toList
def kindGuard : CExpr := SymbolSpelling.kindGuard
def numberGuard : CExpr := SymbolSpelling.numberGuard
def spellingOperand : CExpr := SymbolSpelling.spellingOperand
def managedCondition : CExpr := .binary .and (.binary .and kindGuard numberGuard) spellingOperand

def body : List CStatement :=
  [.branch (.unary .not atomOperand) [.return (some (.identifier "SYMBOL_ID_NONE".toList))] [],
   .branch managedCondition [.return (some (.call "atom_symbol_lookup_spelling_id".toList [atomOperand]))] [],
   .return (some SymbolSpelling.numberOperand)]

/-- The body selected by CETTA_MANAGED_SYMBOLS. Preprocessor selection and
parameter/call ABI are explicit; this is the existing parsed block runner. -/
def program (lookup : Lookup) (environment : Environment) : CProg CVal ReadBlock.Result :=
  executeWith { read := fun _ => read lookup }
    (fun _ _ _ => CProg.undefined) SymbolSpelling.layout 0 6 environment body

/-- The source guard reads only the current header. It deliberately performs
no unconditional forwarding traversal. -/
def managedTest (atom : Option Ptr) : CProg CVal Bool := do
  let kind ← SymbolSpelling.readWord atom 0
  if kind == 0 then do
    let number ← SymbolSpelling.readWord atom 3
    if number == 0 then do
      let spelling ← SymbolSpelling.readSpelling atom
      let null ← CProg.ptrEq spelling none
      pure (!null)
    else pure false
  else pure false

def operations (lookup : Lookup) (atom : Option Ptr) : CProg CVal UInt32 := do
  let null ← CProg.ptrEq atom none
  if null then pure 0 else do
    let managed ← managedTest atom
    if managed then lookup atom else SymbolSpelling.readWord atom 3

theorem atom_parameter (lookup : Lookup) (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read lookup environment atomOperand = pure (.ptr atom) := by
  change resolved (environment "atom".toList) = _
  rw [known]
  rfl

theorem number_field (lookup : Lookup) (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read lookup environment SymbolSpelling.numberOperand =
      (SymbolSpelling.readWord atom 3 >>= fun number => pure (.u32 number)) := by
  change (read lookup environment atomOperand >>= fun value =>
    field SymbolSpelling.layout value "symbol_number".toList) = _
  rw [atom_parameter lookup environment atom known]
  cases atom with
  | none => exact (undefined_bind _).symm
  | some atom => rfl

theorem kind_field (lookup : Lookup) (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read lookup environment SymbolSpelling.kindOperand =
      (SymbolSpelling.readWord atom 0 >>= fun kind => pure (.u32 kind)) := by
  change (read lookup environment atomOperand >>= fun value =>
    field SymbolSpelling.layout value "kind".toList) = _
  rw [atom_parameter lookup environment atom known]
  cases atom with
  | none => exact (undefined_bind _).symm
  | some atom => rfl

theorem spelling_field (lookup : Lookup) (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read lookup environment spellingOperand =
      (SymbolSpelling.readSpelling atom >>= fun value => pure (.ptr value)) := by
  change (read lookup environment atomOperand >>= fun value =>
    field SymbolSpelling.layout value "spelling".toList) = _
  rw [atom_parameter lookup environment atom known]
  cases atom with
  | none => exact (undefined_bind _).symm
  | some atom => rfl

theorem and_read (lookup : Lookup) (environment : Environment) (left right : CExpr) :
    (read lookup environment (.binary .and left right) >>= truth) =
      (do let first ← read lookup environment left
          let selected ← truth first
          if selected then read lookup environment right >>= truth else pure false) := by
  change ((do let first ← read lookup environment left
              let selected ← truth first
              if selected then do
                let second ← read lookup environment right
                let selectedSecond ← truth second
                pure (CVal.bool selectedSecond)
              else pure (CVal.bool false)) >>= truth) = _
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext first
  congr 1
  funext selected
  cases selected <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext second
  change (truth second).bind Prog.ret = truth second
  exact Prog.bind_ret _

theorem actual_managed_guard (lookup : Lookup) (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    (read lookup environment managedCondition >>= truth) = managedTest atom := by
  have first : read lookup environment kindGuard =
      (SymbolSpelling.readWord atom 0 >>= fun kind => pure (.bool (kind == 0))) := by
    change (read lookup environment SymbolSpelling.kindOperand >>= fun kind =>
      pure (CVal.u32 0) >>= fun zero => binary .eq kind zero) = _
    rw [kind_field lookup environment atom known]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    rfl
  have second : read lookup environment numberGuard =
      (SymbolSpelling.readWord atom 3 >>= fun number => pure (.bool (number == 0))) := by
    change (read lookup environment SymbolSpelling.numberOperand >>= fun number =>
      pure (CVal.u32 0) >>= fun zero => binary .eq number zero) = _
    rw [number_field lookup environment atom known]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    rfl
  unfold managedCondition
  rw [and_read]
  have inner : (read lookup environment (.binary .and kindGuard numberGuard) >>= truth) =
      (SymbolSpelling.readWord atom 0 >>= fun kind =>
        if kind == 0 then SymbolSpelling.readWord atom 3 >>= fun number => pure (number == 0)
        else pure false) := by
    rw [and_read, first, second]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  simp only [Prog.bind_eq] at inner ⊢
  rw [← Prog.bind_assoc, inner, spelling_field lookup environment atom known]
  simp only [managedTest, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext kind
  by_cases yes : (kind == 0) = true <;> simp [yes, Prog.bind_assoc, Prog.ret_bind]


theorem initial_null_test (lookup : Lookup) (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    (read lookup environment (.unary .not atomOperand) >>= truth) = CProg.ptrEq atom none := by
  change ((read lookup environment atomOperand >>= fun value => do
    let selected ← truth value
    pure (CVal.bool (!selected))) >>= truth) = _
  rw [atom_parameter lookup environment atom known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, truth, Prog.bind_assoc]
  change (CProg.ptrEq atom none >>= fun yes => pure (!(!yes))) = _
  simp only [Bool.not_not, Prog.bind_eq, Prog.pure_eq, Prog.bind_ret]

theorem lookup_call (lookup : Lookup) (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read lookup environment (.call "atom_symbol_lookup_spelling_id".toList [atomOperand]) =
      (lookup atom >>= fun identifier => pure (.u32 identifier)) := by
  change ((read lookup environment atomOperand >>= fun value => pure [value]) >>=
    calls lookup "atom_symbol_lookup_spelling_id".toList) = _
  rw [atom_parameter lookup environment atom known]
  rfl

private theorem return_block (lookup : Lookup) (environment : Environment)
    (fuel : Nat) (operand : CExpr) :
    executeWith { read := fun _ => read lookup } (fun _ _ _ => CProg.undefined)
      SymbolSpelling.layout 0 (fuel + 1) environment [.return (some operand)] =
      (read lookup environment operand >>= fun value =>
        pure (.finished (.returned environment (some value)))) := rfl

private theorem empty_block (lookup : Lookup) (environment : Environment) (fuel : Nat) :
    executeWith { read := fun _ => read lookup } (fun _ _ _ => CProg.undefined)
      SymbolSpelling.layout 0 fuel environment [] =
      pure (.finished (.next environment)) := by
  rw [executeWith_equation]

/-- The selected C body is interpreted by the maintained block semantics.
The callback occurs only at the managed-ID-zero branch and receives the
original pointer; the numbered branch performs its own final header load. -/
theorem actual_body_uses_operations (lookup : Lookup) (environment : Environment)
    (atom : Option Ptr) (known : environment "atom".toList = some (.ptr atom)) :
    program lookup environment =
      (operations lookup atom >>= fun value =>
        pure (.finished (.returned environment (some (.u32 value))))) := by
  unfold program body
  rw [executeWith_equation]
  simp only [Prog.bind_eq]
  rw [← Prog.bind_assoc]
  change ((read lookup environment (.unary .not atomOperand) >>= truth) >>=
    fun null => (executeWith { read := fun _ => read lookup }
      (fun _ _ _ => CProg.undefined) SymbolSpelling.layout 0 5 environment
      (if null then [.return (some (.identifier "SYMBOL_ID_NONE".toList))] else [])) >>=
      ReadBlock.resume (fun current => executeWith { read := fun _ => read lookup }
        (fun _ _ _ => CProg.undefined) SymbolSpelling.layout 0 5 current
        [.branch managedCondition [.return (some (.call "atom_symbol_lookup_spelling_id".toList
          [atomOperand]))] [], .return (some SymbolSpelling.numberOperand)])) = _
  rw [initial_null_test lookup environment atom known]
  simp only [operations, Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext null
  cases null with
  | true =>
      simp only [↓reduceIte]
      rw [return_block]
      have zero : read lookup environment (.identifier "SYMBOL_ID_NONE".toList) = pure (.u32 0) := rfl
      rw [zero]
      rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [empty_block]
      simp only [Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
      rw [executeWith_equation]
      simp only [Prog.bind_eq]
      rw [← Prog.bind_assoc]
      change ((read lookup environment managedCondition >>= truth) >>=
        fun managed => executeWith { read := fun _ => read lookup }
          (fun _ _ _ => CProg.undefined) SymbolSpelling.layout 0 4 environment
          (if managed then [.return (some (.call "atom_symbol_lookup_spelling_id".toList
            [atomOperand]))] else []) >>=
            ReadBlock.resume (fun current => executeWith { read := fun _ => read lookup }
              (fun _ _ _ => CProg.undefined) SymbolSpelling.layout 0 4 current
              [.return (some SymbolSpelling.numberOperand)])) = _
      rw [actual_managed_guard lookup environment atom known]
      simp only [Prog.bind_eq, Prog.bind_assoc]
      congr 1
      funext managed
      cases managed with
      | true =>
          simp only [↓reduceIte]
          rw [return_block, lookup_call lookup environment atom known]
          simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [empty_block]
          simp only [Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
          rw [return_block, number_field lookup environment atom known]
          simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]


universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem numbered_guard_wp (heap : Heap L) (atom : Ptr) (identifier : UInt32)
    (kind : Reads atom (.u32 0) heap) (number : Reads (atom + 3) (.u32 identifier) heap)
    (nonzero : identifier ≠ 0) (post : Bool → Heap L → Prop) (after : post false heap) :
    (managedTest (some atom)).wp act post heap := by
  unfold managedTest SymbolSpelling.readWord
  rw [wp_bind']
  apply SymbolForward.load_word_wp heap (atom + 0) 0 (by simpa only [ptr_add_zero] using kind)
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply SymbolForward.load_word_wp heap (atom + 3) identifier number
  simpa only [beq_eq_false_iff_ne.mpr nonzero, Bool.false_eq_true, ↓reduceIte, wp_pure] using after

/-- For a numbered symbol the source does not call the lookup callback or
unforward. Both actual number loads remain in the program. -/
theorem numbered_current_id_wp (lookup : Lookup) (heap : Heap L) (atom : Ptr)
    (identifier : UInt32) (live : Valid heap atom)
    (kind : Reads atom (.u32 0) heap) (number : Reads (atom + 3) (.u32 identifier) heap)
    (nonzero : identifier ≠ 0) (post : UInt32 → Heap L → Prop) (after : post identifier heap) :
    (operations lookup (some atom)).wp act post heap := by
  unfold operations
  rw [wp_bind']
  apply wp_ptrEq (p := some atom) (q := none) (σ := heap) live trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply numbered_guard_wp heap atom identifier kind number nonzero
  simp only [Bool.false_eq_true, ↓reduceIte, SymbolSpelling.readWord]
  exact SymbolForward.load_word_wp heap (atom + 3) identifier number post after

/-- The source runner itself returns the observed numbered ID and the
unchanged local environment. Its spelling-lookup service is unreachable. -/
theorem actual_numbered_body_wp (lookup : Lookup) (environment : Environment)
    (heap : Heap L) (atom : Ptr) (identifier : UInt32)
    (parameter : environment "atom".toList = some (.ptr (some atom)))
    (live : Valid heap atom) (kind : Reads atom (.u32 0) heap)
    (number : Reads (atom + 3) (.u32 identifier) heap) (nonzero : identifier ≠ 0)
    (post : ReadBlock.Result → Heap L → Prop)
    (after : post (.finished (.returned environment (some (.u32 identifier)))) heap) :
    (program lookup environment).wp act post heap := by
  rw [actual_body_uses_operations lookup environment (some atom) parameter, wp_bind']
  apply numbered_current_id_wp lookup heap atom identifier live kind number nonzero
  simpa only [wp_pure] using after

theorem null_current_id_wp (lookup : Lookup) (heap : Heap L)
    (post : UInt32 → Heap L → Prop) (after : post 0 heap) :
    (operations lookup none).wp act post heap := by
  unfold operations
  rw [wp_bind']
  apply wp_ptrEq (p := none) (q := none) (σ := heap) trivial trivial
  simpa only [decide_true, ↓reduceIte, wp_pure] using after

/-- Managed spelling dispatch is kept as a separate component boundary.
Its service receives the original pointer and may traverse forwarding; this
lemma does not identify that service with registration or infer its result. -/
theorem managed_current_id_wp (lookup : Lookup) (heap : Heap L) (atom spelling : Ptr)
    (live : Valid heap atom) (spellingLive : Valid heap spelling)
    (kind : Reads atom (.u32 0) heap) (number : Reads (atom + 3) (.u32 0) heap)
    (stored : Reads (atom + 5) (.ptr (some spelling)) heap)
    (post : UInt32 → Heap L → Prop) (call : (lookup (some atom)).wp act post heap) :
    (operations lookup (some atom)).wp act post heap := by
  unfold operations
  rw [wp_bind']
  apply wp_ptrEq (p := some atom) (q := none) (σ := heap) live trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
  unfold managedTest SymbolSpelling.readWord SymbolSpelling.readSpelling
  rw [wp_bind']
  rw [wp_bind']
  apply SymbolForward.load_word_wp heap (atom + 0) 0 (by simpa only [ptr_add_zero] using kind)
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply SymbolForward.load_word_wp heap (atom + 3) 0 number
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply SymbolForward.load_pointer_wp heap (atom + 5) (some spelling) stored
  rw [wp_bind']
  apply wp_ptrEq (p := some spelling) (q := none) (σ := heap) spellingLive trivial
  simpa only [reduceCtorEq, decide_false, Bool.not_false, wp_pure, ↓reduceIte] using call

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Current

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Current
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

private def sourcePiece0 : String × List Token := ("{\n    if (!atom) return SYMBOL_ID_NONE;\n    if (atom->", [.punctuation "{".toList, .identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "atom".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "SYMBOL_ID_NONE".toList, .punctuation ";".toList, .identifier "if".toList, .punctuation "(".toList, .identifier "atom".toList, .punctuation "->".toList])
private theorem sourcePiece0_lex : sourcePiece0.1.toList.foldl step initial = completed sourcePiece0.2 := by decide +kernel

private def sourcePiece1 : String × List Token := ("kind == ATOM_SYMBOL && atom->symbol_number == ", [.identifier "kind".toList, .punctuation "==".toList, .identifier "ATOM_SYMBOL".toList, .punctuation "&&".toList, .identifier "atom".toList, .punctuation "->".toList, .identifier "symbol_number".toList, .punctuation "==".toList])
private theorem sourcePiece1_lex : sourcePiece1.1.toList.foldl step initial = completed sourcePiece1.2 := by decide +kernel

private def sourcePiece2 : String × List Token := ("SYMBOL_ID_NONE &&\n        atom->spelling)\n        ", [.identifier "SYMBOL_ID_NONE".toList, .punctuation "&&".toList, .identifier "atom".toList, .punctuation "->".toList, .identifier "spelling".toList, .punctuation ")".toList])
private theorem sourcePiece2_lex : sourcePiece2.1.toList.foldl step initial = completed sourcePiece2.2 := by decide +kernel

private def sourcePiece3 : String × List Token := ("return atom_symbol_lookup_spelling_id(atom);\n    ", [.identifier "return".toList, .identifier "atom_symbol_lookup_spelling_id".toList, .punctuation "(".toList, .identifier "atom".toList, .punctuation ")".toList, .punctuation ";".toList])
private theorem sourcePiece3_lex : sourcePiece3.1.toList.foldl step initial = completed sourcePiece3.2 := by decide +kernel

private def sourcePiece4 : String × List Token := ("return atom->symbol_number;\n}", [.identifier "return".toList, .identifier "atom".toList, .punctuation "->".toList, .identifier "symbol_number".toList, .punctuation ";".toList, .punctuation "}".toList])
private theorem sourcePiece4_lex : sourcePiece4.1.toList.foldl step initial = completed sourcePiece4.2 := by decide +kernel

private def sourcePieces : List (String × List Token) := [sourcePiece0, sourcePiece1, sourcePiece2, sourcePiece3, sourcePiece4]
def source : String := String.join (sourcePieces.map Prod.fst)
def sourceTokens : List Token := sourcePieces.flatMap Prod.snd

/-- The managed-symbol preprocessor branch, with the raw source and selection
checked separately. The kernel checks all tokens and the actual parsed body. -/
theorem source_lexed : lex source.toList = .ok sourceTokens := by
  apply lex_completed_string_pieces
  simp only [sourcePieces, List.forall_cons]
  exact ⟨sourcePiece0_lex, sourcePiece1_lex, sourcePiece2_lex, sourcePiece3_lex, sourcePiece4_lex, trivial⟩

theorem source_parsed : blockText? [] source.toList = some body := by
  exact block_text_of_parts [] _ sourceTokens _ source_lexed (by rfl)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Current

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ReadExpressions CellPermission

/-- The final symbol_bytes conditional tests the row and the stored buffer.
A successful branch reads the buffer again; no load is erased. The empty
literal has an independently supplied static-storage identity. -/
def returnedBytes (empty : Ptr) (entry : Option Ptr) : CProg CVal (Option Ptr) := do
  let nullEntry ← CProg.ptrEq entry none
  if nullEntry then pure (some empty) else
    match entry with
    | none => CProg.undefined
    | some entry => do
      let buffer ← CProg.loadPtr entry
      let nullBuffer ← CProg.ptrEq buffer none
      if nullBuffer then pure (some empty) else CProg.loadPtr entry

def returnedLength (entry : Option Ptr) : CProg CVal UInt32 := do
  let nullEntry ← CProg.ptrEq entry none
  if nullEntry then pure 0 else
    match entry with
    | none => CProg.undefined
    | some entry => CProg.loadU32 (entry + 1)

/-- Source-level sentinel and acquired-count guards precede actual chunk and
member selection. The proof boundary assumes CETTA_SYMBOL_READ_COVERAGE is
inactive, or its separate gate has already returned successfully. -/
def bytesOperation (empty : Ptr) (table : Option Ptr) (identifier : UInt32) :
    CProg CVal (Option Ptr) := do
  let entry ← publishedEntry table identifier
  returnedBytes empty entry

def lengthOperation (table : Option Ptr) (identifier : UInt32) : CProg CVal UInt32 := do
  let entry ← publishedEntry table identifier
  returnedLength entry

namespace Source

def entryName : CExpr := .identifier "entry".toList

def bytesCondition : CExpr := .binary .and entryName bytesOperand

def returnLengthOperand : CExpr := .conditional entryName lengthOperand (.decimal 0)

/-- The selected conditional uses the maintained expression reader. Its empty
string leaf is an explicit static-storage service, since this parser profile
does not itself allocate or decode C string literals. -/
def bytesReturn (empty : Ptr) (table chunk entry : Option Ptr) (identifier : UInt32) :
    CProg CVal CVal := do
  let selectedValue ← read table chunk entry identifier bytesCondition
  let selected ← truth selectedValue
  if selected then read table chunk entry identifier bytesOperand
  else pure (.ptr (some empty))

private theorem bytes_condition (table chunk entry : Option Ptr) (identifier : UInt32) :
    (read table chunk entry identifier bytesCondition >>= truth) =
      (do let hasEntry ← truth (CVal.ptr entry)
          if hasEntry then read table chunk entry identifier bytesOperand >>= truth
          else pure false) := by
  change ((truth (CVal.ptr entry) >>= fun yes =>
    if yes then do
      let buffer ← read table chunk entry identifier bytesOperand
      let selected ← truth buffer
      pure (CVal.bool selected)
    else pure (CVal.bool false)) >>= truth) = _
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext yes
  cases yes with
  | false => rfl
  | true =>
      simp only [↓reduceIte, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
      congr 1
      funext buffer
      exact Prog.bind_ret _

theorem actual_bytes_return_uses_selected_reads (empty : Ptr)
    (table chunk entry : Option Ptr) (identifier : UInt32) :
    bytesReturn empty table chunk entry identifier =
      (returnedBytes empty entry >>= fun buffer => pure (.ptr buffer)) := by
  unfold bytesReturn
  simp only [Prog.bind_eq]
  rw [← Prog.bind_assoc]
  have condition := bytes_condition table chunk entry identifier
  simp only [Prog.bind_eq] at condition
  rw [condition]
  change (truth (CVal.ptr entry) >>= fun hasEntry =>
    (if hasEntry then read table chunk entry identifier bytesOperand >>= truth else pure false) >>=
    fun selected => if selected then read table chunk entry identifier bytesOperand
      else pure (CVal.ptr (some empty))) = _
  simp only [truth, returnedBytes, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext nullEntry
  cases nullEntry with
  | true => rfl
  | false =>
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      cases entry with
      | none =>
          have missing : read table chunk none identifier bytesOperand = CProg.undefined := rfl
          rw [missing]
          simp only [CProg.undefined, Prog.call_bind]
          congr 1
          funext impossible
          cases impossible
      | some entry =>
          rw [bytes_use_actual_member table chunk entry identifier]
          simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
          congr 1
          funext buffer
          congr 1
          funext nullBuffer
          cases nullBuffer <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true,
            ↓reduceIte, Prog.ret_bind]

private theorem word_return_cast (value : UInt32) :
    unsignedCast ⟨"uint32_t".toList, 0⟩ (.u32 value) = pure (.u32 value) := by
  rw [unsignedCast32_exact _ _ rfl]
  change (pure (CVal.u32 (UInt32.ofNat (value.toNat % 2 ^ 32))) : CProg CVal CVal) = _
  rw [UInt32.ofNat_mod_size, UInt32.ofNat_toNat]

/-- The function's declared uint32 return conversion is retained. In
particular, the C literal zero is not mislabeled as an unsigned operand. -/
theorem actual_length_return_uses_selected_reads
    (table chunk entry : Option Ptr) (identifier : UInt32) :
    (read table chunk entry identifier returnLengthOperand >>=
      unsignedCast ⟨"uint32_t".toList, 0⟩) =
      (returnedLength entry >>= fun length => pure (.u32 length)) := by
  change ((truth (CVal.ptr entry) >>= fun selected =>
    if selected then read table chunk entry identifier lengthOperand else pure (CVal.i32 0)) >>=
      unsignedCast ⟨"uint32_t".toList, 0⟩) = _
  simp only [truth, returnedLength, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext nullEntry
  cases nullEntry with
  | true => rfl
  | false =>
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      cases entry with
      | none =>
          have missing : read table chunk none identifier lengthOperand = CProg.undefined := rfl
          rw [missing]
          simp only [CProg.undefined, Prog.call_bind]
          congr 1
          funext impossible
          cases impossible
      | some entry =>
          rw [length_uses_actual_member table chunk entry identifier]
          simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, word_return_cast]

end Source

variable {L : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem returned_bytes_wp (heap : Heap L) (empty entry buffer : Ptr)
    (entryLive : Valid heap entry) (bufferLive : Valid heap buffer)
    (stored : Reads entry (.ptr (some buffer)) heap)
    (post : Option Ptr → Heap L → Prop) (after : post (some buffer) heap) :
    (returnedBytes empty (some entry)).wp act post heap := by
  unfold returnedBytes
  rw [wp_bind']
  apply wp_ptrEq (p := some entry) (q := none) (σ := heap) entryLive trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply SymbolForward.load_pointer_wp heap entry (some buffer) stored
  rw [wp_bind']
  apply wp_ptrEq (p := some buffer) (q := none) (σ := heap) bufferLive trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
  exact SymbolForward.load_pointer_wp heap entry (some buffer) stored post after

theorem returned_length_wp (heap : Heap L) (entry : Ptr) (length : UInt32)
    (entryLive : Valid heap entry) (stored : Reads (entry + 1) (.u32 length) heap)
    (post : UInt32 → Heap L → Prop) (after : post length heap) :
    (returnedLength (some entry)).wp act post heap := by
  unfold returnedLength
  rw [wp_bind']
  apply wp_ptrEq (p := some entry) (q := none) (σ := heap) entryLive trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
  exact SymbolForward.load_word_wp heap (entry + 1) length stored post after

theorem bytes_operation_wp (heap : Heap L) (empty table : Ptr) (identifier : UInt32)
    (row : PublishedRow heap table identifier) (buffer : Ptr)
    (entryLive : Valid heap (entryPointer row.chunk identifier))
    (bufferLive : Valid heap buffer)
    (stored : Reads (entryPointer row.chunk identifier) (.ptr (some buffer)) heap)
    (post : Option Ptr → Heap L → Prop) (after : post (some buffer) heap) :
    (bytesOperation empty (some table) identifier).wp act post heap := by
  unfold bytesOperation
  rw [wp_bind']
  apply published_entry_wp heap table identifier row
  exact returned_bytes_wp heap empty (entryPointer row.chunk identifier) buffer
    entryLive bufferLive stored post after

theorem length_operation_wp (heap : Heap L) (table : Ptr) (identifier : UInt32)
    (row : PublishedRow heap table identifier) (length : UInt32)
    (entryLive : Valid heap (entryPointer row.chunk identifier))
    (stored : Reads (entryPointer row.chunk identifier + 1) (.u32 length) heap)
    (post : UInt32 → Heap L → Prop) (after : post length heap) :
    (lengthOperation (some table) identifier).wp act post heap := by
  unfold lengthOperation
  rw [wp_bind']
  apply published_entry_wp heap table identifier row
  exact returned_length_wp heap (entryPointer row.chunk identifier) length entryLive stored post after

/-- Calling both actual helpers preserves both publication reads and their
separate row lookups. The entire framed heap is unchanged. -/
theorem spelling_pair_wp (heap : Heap L) (empty table : Ptr) (identifier : UInt32)
    (row : PublishedRow heap table identifier) (buffer : Ptr) (length : UInt32)
    (entryLive : Valid heap (entryPointer row.chunk identifier)) (bufferLive : Valid heap buffer)
    (bufferCell : Reads (entryPointer row.chunk identifier) (.ptr (some buffer)) heap)
    (lengthCell : Reads (entryPointer row.chunk identifier + 1) (.u32 length) heap)
    (post : Option Ptr × UInt32 → Heap L → Prop) (after : post (some buffer, length) heap) :
    (do let buffer ← bytesOperation empty (some table) identifier
        let length ← lengthOperation (some table) identifier
        pure (buffer, length)).wp act post heap := by
  rw [wp_bind']
  apply bytes_operation_wp heap empty table identifier row buffer entryLive bufferLive bufferCell
  rw [wp_bind']
  apply length_operation_wp heap table identifier row length entryLive lengthCell
  simpa only [wp_pure] using after


end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Source
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ReadExpressions StatementBlock

def tableName : CExpr := .identifier "st".toList
def chunkCondition : CExpr := .binary .or (.unary .not tableName) (.unary .not chunksOperand)
def chunkBody : List CStatement :=
  [.branch chunkCondition [.return (some .null)] [], .return (some chunkOperand)]

def chunkProgram (table : Option Ptr) (identifier : UInt32) (outer : Environment) :
    CProg CVal ReadBlock.Result :=
  executeWith { read := fun _ _ => read table none none identifier }
    (fun _ _ _ => CProg.undefined) layout 0 4 outer chunkBody

private theorem table_test (table : Option Ptr) (identifier : UInt32) :
    (read table none none identifier (.unary .not tableName) >>= truth) =
      CProg.ptrEq table none := by
  change ((truth (CVal.ptr table) >>= fun yes => pure (CVal.bool (!yes))) >>= truth) = _
  simp only [truth, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  simp only [Bool.not_not, Prog.bind_ret]

private theorem chunks_test (table : Ptr) (identifier : UInt32) :
    (read (some table) none none identifier (.unary .not chunksOperand) >>= truth) =
      (CProg.loadPtr (table + 4) >>= fun chunks => CProg.ptrEq chunks none) := by
  change ((read (some table) none none identifier chunksOperand >>= fun pointer =>
    truth pointer >>= fun yes => pure (CVal.bool (!yes))) >>= truth) = _
  rw [chunks_use_actual_pointer]
  simp only [truth, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext chunks
  simp only [Bool.not_not, Prog.bind_ret]

private theorem or_test (table : Option Ptr) (identifier : UInt32) (left right : CExpr) :
    (read table none none identifier (.binary .or left right) >>= truth) =
      ((read table none none identifier left >>= truth) >>= fun yes =>
        if yes then pure true else read table none none identifier right >>= truth) := by
  change ((read table none none identifier left >>= fun value => truth value >>= fun yes =>
    if yes then pure (CVal.bool true) else do
      let value ← read table none none identifier right
      let yes ← truth value
      pure (CVal.bool yes)) >>= truth) = _
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext value
  congr 1
  funext yes
  cases yes with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Prog.bind_assoc, Prog.pure_eq,
        Prog.ret_bind, truth]
      congr 1
      funext value
      exact Prog.bind_ret _

theorem actual_chunk_condition (table : Ptr) (identifier : UInt32) :
    (read (some table) none none identifier chunkCondition >>= truth) =
      (CProg.ptrEq (some table) none >>= fun nullTable =>
        if nullTable then pure true else
          CProg.loadPtr (table + 4) >>= fun chunks => CProg.ptrEq chunks none) := by
  rw [chunkCondition, or_test, table_test, chunks_test]

private theorem chunk_return_block (table : Option Ptr) (identifier : UInt32)
    (outer : Environment) (fuel : Nat) (operand : CExpr) :
    executeWith { read := fun _ _ => read table none none identifier }
      (fun _ _ _ => CProg.undefined) layout 0 (fuel + 1) outer [.return (some operand)] =
      (read table none none identifier operand >>= fun value =>
        pure (.finished (.returned outer (some value)))) := rfl

/-- The actual helper's guard and return expression are composed through the
existing block interpreter. Both entry_chunks reads remain in the result. -/
theorem actual_chunk_body_uses_memory_operations (table : Ptr) (identifier : UInt32)
    (outer : Environment) :
    chunkProgram (some table) identifier outer =
      (entryChunk (some table) identifier >>= fun pointer =>
        pure (.finished (.returned outer (some (.ptr pointer))))) := by
  unfold chunkProgram chunkBody
  rw [executeWith_equation]
  simp only [Prog.bind_eq]
  rw [← Prog.bind_assoc]
  have guard := actual_chunk_condition table identifier
  simp only [Prog.bind_eq] at guard
  rw [guard]
  simp only [Prog.bind_assoc, entryChunk, Prog.bind_eq]
  congr 1
  funext nullTable
  cases nullTable with
  | true =>
      simp only [↓reduceIte, Prog.pure_eq, Prog.ret_bind]
      rw [chunk_return_block]
      rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Prog.bind_assoc]
      congr 1
      funext chunks
      congr 1
      funext nullChunks
      cases nullChunks with
      | true =>
          simp only [↓reduceIte]
          rw [chunk_return_block]
          rfl
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [executeWith_equation]
          simp only [Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
          rw [chunk_return_block, chunk_uses_actual_index]
          simp only [Prog.bind_eq, Prog.bind_assoc]
          congr 1
          funext selectedChunks
          cases selectedChunks with
          | none =>
              simp only [CProg.undefined, Prog.call_bind]
              congr 1
              funext impossible
              cases impossible
          | some selectedChunks =>
              simp only [Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Source

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Source
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

private def chunkSourcePiece0 : String × List Token := ("{\n", [.punctuation "{".toList])
private theorem chunkSourcePiece0_lex : chunkSourcePiece0.1.toList.foldl step initial = completed chunkSourcePiece0.2 := by decide +kernel
private def chunkSourcePiece1 : String × List Token := ("    if (!st || !st->entry_chunks) return NULL;\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "st".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "st".toList, .punctuation "->".toList, .identifier "entry_chunks".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "NULL".toList, .punctuation ";".toList])
private theorem chunkSourcePiece1_lex : chunkSourcePiece1.1.toList.foldl step initial = completed chunkSourcePiece1.2 := by decide +kernel
private def chunkSourcePiece2 : String × List Token := ("    return st->entry_chunks[id >> SYMBOL_ENTRY_CHUNK_BITS];\n", [.identifier "return".toList, .identifier "st".toList, .punctuation "->".toList, .identifier "entry_chunks".toList, .punctuation "[".toList, .identifier "id".toList, .punctuation ">>".toList, .identifier "SYMBOL_ENTRY_CHUNK_BITS".toList, .punctuation "]".toList, .punctuation ";".toList])
private theorem chunkSourcePiece2_lex : chunkSourcePiece2.1.toList.foldl step initial = completed chunkSourcePiece2.2 := by decide +kernel
private def chunkSourcePiece3 : String × List Token := ("}", [.punctuation "}".toList])
private theorem chunkSourcePiece3_lex : chunkSourcePiece3.1.toList.foldl step initial = completed chunkSourcePiece3.2 := by decide +kernel
private def chunkSourcePieces : List (String × List Token) := [chunkSourcePiece0, chunkSourcePiece1, chunkSourcePiece2, chunkSourcePiece3]
def chunkSource : String := String.join (chunkSourcePieces.map Prod.fst)
def chunkSourceTokens : List Token := chunkSourcePieces.flatMap Prod.snd
theorem chunkSource_lexed : lex chunkSource.toList = .ok chunkSourceTokens := by
  apply lex_completed_string_pieces
  simp only [chunkSourcePieces, List.forall_cons]
  exact ⟨chunkSourcePiece0_lex, chunkSourcePiece1_lex, chunkSourcePiece2_lex, chunkSourcePiece3_lex, trivial⟩
private def refSourcePiece0 : String × List Token := ("{\n", [.punctuation "{".toList])
private theorem refSourcePiece0_lex : refSourcePiece0.1.toList.foldl step initial = completed refSourcePiece0.2 := by decide +kernel
private def refSourcePiece1 : String × List Token := ("    const SymbolEntry *chunk = symbol_table_entry_chunk(st, id);\n", [.identifier "const".toList, .identifier "SymbolEntry".toList, .punctuation "*".toList, .identifier "chunk".toList, .punctuation "=".toList, .identifier "symbol_table_entry_chunk".toList, .punctuation "(".toList, .identifier "st".toList, .punctuation ",".toList, .identifier "id".toList, .punctuation ")".toList, .punctuation ";".toList])
private theorem refSourcePiece1_lex : refSourcePiece1.1.toList.foldl step initial = completed refSourcePiece1.2 := by decide +kernel
private def refSourcePiece2 : String × List Token := ("    if (!chunk) return NULL;\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "chunk".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "NULL".toList, .punctuation ";".toList])
private theorem refSourcePiece2_lex : refSourcePiece2.1.toList.foldl step initial = completed refSourcePiece2.2 := by decide +kernel
private def refSourcePiece3 : String × List Token := ("    return &chunk[id & SYMBOL_ENTRY_CHUNK_MASK];\n", [.identifier "return".toList, .punctuation "&".toList, .identifier "chunk".toList, .punctuation "[".toList, .identifier "id".toList, .punctuation "&".toList, .identifier "SYMBOL_ENTRY_CHUNK_MASK".toList, .punctuation "]".toList, .punctuation ";".toList])
private theorem refSourcePiece3_lex : refSourcePiece3.1.toList.foldl step initial = completed refSourcePiece3.2 := by decide +kernel
private def refSourcePiece4 : String × List Token := ("}", [.punctuation "}".toList])
private theorem refSourcePiece4_lex : refSourcePiece4.1.toList.foldl step initial = completed refSourcePiece4.2 := by decide +kernel
private def refSourcePieces : List (String × List Token) := [refSourcePiece0, refSourcePiece1, refSourcePiece2, refSourcePiece3, refSourcePiece4]
def refSource : String := String.join (refSourcePieces.map Prod.fst)
def refSourceTokens : List Token := refSourcePieces.flatMap Prod.snd
theorem refSource_lexed : lex refSource.toList = .ok refSourceTokens := by
  apply lex_completed_string_pieces
  simp only [refSourcePieces, List.forall_cons]
  exact ⟨refSourcePiece0_lex, refSourcePiece1_lex, refSourcePiece2_lex, refSourcePiece3_lex, refSourcePiece4_lex, trivial⟩
theorem actual_chunk_body_parsed : blockText? [] chunkSource.toList = some chunkBody := by
  exact block_text_of_parts [] _ chunkSourceTokens _ chunkSource_lexed (by rfl)

def refBody : List CStatement :=
  [.declarePointeeConst ⟨"SymbolEntry".toList, 1⟩ "chunk".toList
    (.call "symbol_table_entry_chunk".toList [tableName, .identifier "id".toList]),
   .branch (.unary .not (.identifier "chunk".toList)) [.return (some .null)] [],
   .return (some entryOperand)]

theorem actual_ref_body_parsed : blockText? ["SymbolEntry".toList] refSource.toList = some refBody := by
  exact block_text_of_parts ["SymbolEntry".toList] _ refSourceTokens _ refSource_lexed (by rfl)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Source

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Source
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ReadExpressions StatementBlock

def refNames (table : Option Ptr) (identifier : UInt32) (environment : Environment) : NameReads :=
  fun name => if name = "chunk".toList then resolved (environment name)
    else names table none none identifier name

def refCalls : Calls := fun name values =>
  if name = "symbol_table_entry_chunk".toList then
    match values with
    | [.ptr table, .u32 identifier] => entryChunk table identifier >>= fun chunk => pure (.ptr chunk)
    | _ => CProg.undefined
  else CProg.undefined

def refRead (table : Option Ptr) (identifier : UInt32) (environment : Environment)
    (operand : CExpr) : CProg CVal CVal :=
  expressionWithNames (refNames table identifier environment) refCalls layout operand objects

def refProgram (table : Option Ptr) (identifier : UInt32) (outer : Environment) :
    CProg CVal ReadBlock.Result :=
  executeWith { pointeeConst := true, initialValue := objectInitialValue, read := fun _ => refRead table identifier }
    (fun _ _ _ => CProg.undefined) layout 0 5 outer refBody

private theorem actual_chunk_call (table : Option Ptr) (identifier : UInt32)
    (outer : Environment) :
    refRead table identifier outer (.call "symbol_table_entry_chunk".toList
      [tableName, .identifier "id".toList]) =
      (entryChunk table identifier >>= fun chunk => pure (.ptr chunk)) := rfl

private theorem ref_chunk_read (table : Option Ptr) (identifier : UInt32)
    (outer : Environment) (chunk : Option Ptr) :
    refRead table identifier (Function.update outer "chunk".toList (some (.ptr chunk)))
      (.identifier "chunk".toList) = pure (.ptr chunk) := by
  change resolved ((Function.update outer "chunk".toList (some (.ptr chunk))) "chunk".toList) = _
  rw [Function.update_self]
  rfl

private theorem ref_chunk_guard (table : Option Ptr) (identifier : UInt32)
    (outer : Environment) (chunk : Option Ptr) :
    (refRead table identifier (Function.update outer "chunk".toList (some (.ptr chunk)))
      (.unary .not (.identifier "chunk".toList)) >>= truth) = CProg.ptrEq chunk none := by
  change ((refRead table identifier (Function.update outer "chunk".toList (some (.ptr chunk)))
      (.identifier "chunk".toList) >>= fun pointer => do
    let yes ← truth pointer
    pure (CVal.bool (!yes))) >>= truth) = _
  rw [ref_chunk_read]
  simp only [truth, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    Bool.not_not, Prog.bind_ret]

private theorem ref_row_address (table : Option Ptr) (identifier : UInt32)
    (outer : Environment) (chunk : Option Ptr) :
    refRead table identifier (Function.update outer "chunk".toList (some (.ptr chunk))) entryOperand =
      match chunk with
      | none => CProg.undefined
      | some chunk => pure (.ptr (some (entryPointer chunk identifier))) := by
  change (pure entryStride >>= fun stride =>
    (refRead table identifier (Function.update outer "chunk".toList (some (.ptr chunk)))
      (.identifier "chunk".toList)) >>= fun address =>
    pure (CVal.u32 (identifier &&& 16383)) >>= fun index => indexedPlace stride address index >>=
      fun pointer => pure (CVal.ptr (some pointer))) = _
  rw [ref_chunk_read]
  cases chunk with
  | none => exact undefined_bind _
  | some chunk => rfl

private theorem ref_null (table : Option Ptr) (identifier : UInt32) (outer : Environment) :
    refRead table identifier outer .null = pure (.ptr none) := rfl

private theorem ref_initial_pointer (chunk : Option Ptr) :
    objectInitialValue ⟨"SymbolEntry".toList, 1⟩ (.ptr chunk) = pure (.ptr chunk) :=
  nullable_object_declaration_retains_value _ chunk (by decide)

/-- The actual const-pointer local is scoped by the maintained declaration
semantics. The helper composes the parsed chunk call, physical pointer guard,
row address, and exact restoration of the caller's local environment. -/
theorem actual_ref_body_uses_memory_operations (table : Option Ptr) (identifier : UInt32)
    (outer : Environment) :
    refProgram table identifier outer =
      (entryRef table identifier >>= fun pointer =>
        pure (.finished (.returned outer (some (.ptr pointer))))) := by
  unfold refProgram refBody
  rw [executeWith_equation]
  dsimp only
  rw [actual_chunk_call]
  simp only [and_self, ↓reduceIte, ref_initial_pointer, Prog.bind_eq, Prog.bind_assoc,
    Prog.pure_eq, Prog.ret_bind]
  unfold entryRef
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext chunk
  change ((executeWith { pointeeConst := true, initialValue := objectInitialValue, read := fun _ => refRead table identifier }
      (fun _ _ _ => CProg.undefined) layout 0 4
      (Function.update outer "chunk".toList (some (.ptr chunk)))
      [.branch (.unary .not (.identifier "chunk".toList)) [.return (some .null)] [],
       .return (some entryOperand)]) >>= fun result =>
      pure (ReadBlock.restore "chunk".toList (outer "chunk".toList) result)) = _
  rw [executeWith_equation]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  rw [← Prog.bind_assoc]
  have guard := ref_chunk_guard table identifier outer chunk
  simp only [Prog.bind_eq] at guard
  rw [guard]
  congr 1
  funext nullChunk
  cases nullChunk with
  | true =>
      simp only [↓reduceIte, executeWith_equation, ref_null, Prog.bind_eq,
        Prog.pure_eq, Prog.ret_bind, ReadBlock.resume,
        ReadBlock.returned_declaration_restores_scope]
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, executeWith_equation, Prog.bind_eq,
        Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
      rw [ref_row_address]
      cases chunk with
      | none =>
          simp only [CProg.undefined, Prog.call_bind]
          congr 1
          funext impossible
          cases impossible
      | some chunk =>
          simp only [Prog.pure_eq, Prog.ret_bind,
            ReadBlock.returned_declaration_restores_scope]

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Source


end NumberedSymbolReadout


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.RefArgument

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings
open ReadBlock (Result Flow)

def refType : CType := ⟨"BindingsFrameRef".toList, 0⟩
def identityType : CType := ⟨"CettaFrameIdentity".toList, 0⟩
def boolType : CType := ⟨"bool".toList, 0⟩
def refName : Name := "ref".toList
def identityName : Name := "identity".toList

def body : List CStatement :=
  [.return (some (.binary .ne (.field (.identifier refName) identityName false)
    (.unsignedInteger 0)))]

def source : String := "static inline bool bindings_frame_ref_is_valid(BindingsFrameRef ref) {\n    return ref.identity != 0u;\n}"
def typeNames : TypeNames := ["bool".toList, "BindingsFrameRef".toList]
def parameterSyntax : CParameter := ⟨refType, refName⟩
def function : CFunction :=
  ⟨boolType, "bindings_frame_ref_is_valid".toList, [parameterSyntax], body⟩

def tokens : List Token :=
  [.identifier "static".toList, .identifier "inline".toList,
   .identifier "bool".toList, .identifier "bindings_frame_ref_is_valid".toList,
   .punctuation ['('], .identifier "BindingsFrameRef".toList, .identifier "ref".toList,
   .punctuation [')'], .punctuation ['{'], .identifier "return".toList,
   .identifier "ref".toList, .punctuation ['.'], .identifier "identity".toList,
   .punctuation ['!', '='], .number ['0', 'u'], .punctuation [';'], .punctuation ['}']]

theorem lexed : lex source.toList = .ok tokens := by decide +kernel

theorem parsed : ordinaryFunctionText? typeNames source.toList = some function := by
  exact function_text_using_of_parts (parameter? typeNames) typeNames source.toList
    tokens function lexed (by rfl)

/-- One logical UInt32 cell represents the current declared identity field.
Native padding, byte offsets and calling convention are separate obligations. -/
def profile : Profile where
  values := noCalls
  locations := fun _ => none
  outsideTypes := fun _ => none
  outsidePlaces := fun _ => none
  fieldTypes := fun owner name =>
    if owner = refType ∧ name = identityName then some identityType else none
  cellExtent := fun type => if type = refType then some 1 else none
  byteExtent := fun _ => none
  sizeWidth := .bits64
  recordFields := some (fun type name =>
    if type = refType ∧ name = identityName then some ⟨0, .word⟩ else none)
  recordTypes := [refType]

def layout : Layout := fun _ => none

def bodyProgram (region : AutomaticRegion Context) (context : Context) :
    CProg CVal (Result Context) :=
  executeScopedWith (ObjectBindings.services profile region (fun _ _ _ => CProg.undefined))
    layout 0 1 context body

/-- The actual function body reads its copied parameter object, rather than
calling a supplied Boolean oracle or reading the original caller's object. -/
theorem bodyProgram_reads_parameter (region : AutomaticRegion Context) (context : Context)
    (address : Ptr) (bound : context refName = some (.object refType address)) :
    bodyProgram region context =
      (CProg.loadU32 address >>= fun identity =>
        pure (.finished (.returned context (some (.bool (!(identity == 0))))))) := by
  simp only [bodyProgram, body, executeScopedWith, ObjectBindings.services,
    ObjectBindings.read, expressionWithNames.eq_def, ObjectBindings.objects,
    placeWithNames.eq_def, ObjectBindings.places, bound, resolved,
    ObjectReads.fieldRead, Bool.false_eq_true, ObjectReads.fieldLayout,
    Option.map_some, ObjectBindings.fieldLayouts, ScalarBytes.typeOf?, ObjectBindings.types,
    bind, Option.bind, profile, field, pointer, and_self, ↓reduceIte,
    ptr_add_zero, binary, equal, scalar, ScalarRead.equal?,
    Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl

/-- The parsed signature supplies the complete record parameter declaration. -/
def invoke (region : AutomaticRegion Context) (context : Context)
    (arguments : List CallArgument) : CProg CVal (Result Context) :=
  match ordinaryFunctionText? typeNames source.toList with
  | none => CProg.undefined
  | some parsedFunction =>
      parameters profile region context parsedFunction.parameters arguments
        (fun localContext => executeScopedWith
          (ObjectBindings.services profile region (fun _ _ _ => CProg.undefined))
          layout 0 1 localContext parsedFunction.body)

theorem invoke_from_actual_signature (region : AutomaticRegion Context) (context : Context)
    (arguments : List CallArgument) :
    invoke region context arguments =
      parameters profile region context [parameterSyntax] arguments (bodyProgram region) := by
  rw [invoke, parsed]
  rfl

theorem actual_record_parameter_entry_field (region : AutomaticRegion Context) (context : Context)
    (value : CVal) :
    invoke region context [.record refType [value]] =
      (region refName 1 (fun address =>
        CProg.store address (value) >>= fun _ =>
        CProg.loadU32 address >>= fun observed =>
        pure (.finished (.returned
          (Function.update context refName (some (.object refType address)))
          (some (.bool (!(observed == 0))))))) >>= fun result =>
          pure (ObjectBindings.restore refName (context refName) result)) := by
  rw [invoke_from_actual_signature]
  change parameter profile region context refType refName (.record refType [value])
    (bodyProgram region) = _
  have extent : profile.recordExtent refType = some 1 := by
    simp only [Profile.recordExtent, profile, List.mem_cons, List.not_mem_nil, or_false,
      if_true]
  rw [parameter_record_keeps_complete_copy profile region context refType refName
    [value] 1 extent rfl]
  congr 1
  congr 1
  funext address
  simp only [CProg.initializeCells, Prog.bind_eq, Prog.pure_eq]
  rw [bodyProgram_reads_parameter region _ address (Function.update_self ..)]
  simp only [Prog.bind_assoc, Prog.ret_bind]
  rfl

theorem actual_record_parameter_entry (region : AutomaticRegion Context) (context : Context)
    (identity : UInt32) :
    invoke region context [.record refType [.u32 identity]] =
      (region refName 1 (fun address =>
        CProg.store address (.u32 identity) >>= fun _ =>
        CProg.loadU32 address >>= fun observed =>
        pure (.finished (.returned
          (Function.update context refName (some (.object refType address)))
          (some (.bool (!(observed == 0))))))) >>= fun result =>
          pure (ObjectBindings.restore refName (context refName) result)) :=
  actual_record_parameter_entry_field region context (.u32 identity)

/-- The source body has completed its return before automatic-region exit;
exit and lexical restoration preserve that actual scalar reply. -/
theorem actual_record_parameter_bracket_field (context : Context) (value : CVal)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) :
    invoke (AutomaticRegion.bracket enter leave) context [.record refType [value]] =
      (enter refName 1 >>= fun address =>
        CProg.store address (value) >>= fun _ =>
        CProg.loadU32 address >>= fun observed =>
        leave refName address 1 >>= fun _ =>
        pure (.finished (.returned context (some (.bool (!(observed == 0))))))) := by
  rw [actual_record_parameter_entry_field]
  simp only [AutomaticRegion.bracket, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc,
    Prog.ret_bind, returned_local_restores_previous_binding]

theorem actual_record_parameter_bracket (context : Context) (identity : UInt32)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) :
    invoke (AutomaticRegion.bracket enter leave) context [.record refType [.u32 identity]] =
      (enter refName 1 >>= fun address =>
        CProg.store address (.u32 identity) >>= fun _ =>
        CProg.loadU32 address >>= fun observed =>
        leave refName address 1 >>= fun _ =>
        pure (.finished (.returned context (some (.bool (!(observed == 0))))))) :=
  actual_record_parameter_bracket_field context (.u32 identity) enter leave

/-- A call service exposes only a scalar actually returned by the parsed
body. Exhaustion or an absent return cannot manufacture a Boolean value. -/
def returnedScalar (result : Result Context) : CProg CVal CVal :=
  match result with
  | .finished (.returned _ (some value)) => pure value
  | _ => CProg.undefined

def service (region : AutomaticRegion Context) (context : Context) : ArgumentCall CVal where
  mode := .whole
  invoke arguments := invoke region context arguments >>= returnedScalar

theorem actual_service_bracket (context : Context) (identity : UInt32)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) :
    (service (AutomaticRegion.bracket enter leave) context).invoke
        [.record refType [.u32 identity]] =
      (enter refName 1 >>= fun address =>
        CProg.store address (.u32 identity) >>= fun _ =>
        CProg.loadU32 address >>= fun observed =>
        leave refName address 1 >>= fun _ => pure (.bool (!(observed == 0)))) := by
  dsimp only [service, ArgumentMode.Value]
  rw [actual_record_parameter_bracket]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, returnedScalar]

theorem incomplete_execution_cannot_return_boolean :
    returnedScalar .exhausted = CProg.undefined := rfl

theorem absent_return_cannot_return_boolean (context : Context) :
    returnedScalar (.finished (.next context)) = CProg.undefined := rfl

section Ownership
open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem copied_parameter_body_owned (region : AutomaticRegion Context) (context : Context)
    (address : Ptr) (identity : UInt32)
    (bound : context refName = some (.object refType address)) :
    CTriple (L := L) (PointsTo address (.u32 identity)) (bodyProgram region context)
      (fun result heap => result = .finished (.returned context
        (some (.bool (!(identity == 0))))) ∧ PointsTo address (.u32 identity) heap) := by
  rw [bodyProgram_reads_parameter region context address bound]
  refine triple_bind _ (loadU32_rule (n := identity) fun _ held =>
    read_of_pointsTo (F := emp) (by simpa only [sepConj_emp] using held)) fun actual => ?_
  apply triple_pure
  intro same
  subst actual
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
    (triple_ret act (Result.finished (Flow.returned context (some (.bool (!(identity == 0))))))
      (fun result heap => result = .finished (.returned context
        (some (.bool (!(identity == 0))))) ∧ PointsTo (L := L) address (CVal.u32 identity) heap))

/-- Parameter admission and exit are storage contracts. The Boolean is
proved from the actual store, typed load and parsed comparison between them. -/
theorem actual_service_owned (context : Context) (identity : UInt32)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit)
    (pre post : Heap L → Prop) (remainder : Ptr → Heap L → Prop)
    (entry : CTriple pre (enter refName 1) (fun address => PointsToAny address ∗ remainder address))
    (exit : ∀ address, CTriple (PointsTo address (.u32 identity) ∗ remainder address)
      (leave refName address 1) (fun _ => post)) :
    CTriple pre ((service (AutomaticRegion.bracket enter leave) context).invoke
      [.record refType [.u32 identity]])
      (fun result heap => result = .bool (!(identity == 0)) ∧ post heap) := by
  rw [actual_service_bracket]
  refine triple_bind _ entry fun address => ?_
  refine triple_bind _ (triple_frame act act_local (store_spec address (.u32 identity))
    (remainder address)) fun _ => ?_
  refine triple_bind _ (loadU32_rule (n := identity) fun _ held => read_of_pointsTo held)
    fun observed => ?_
  apply triple_pure
  intro same
  subst observed
  refine triple_bind _ (exit address) fun _ => ?_
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
    (triple_ret act (CVal.bool (!(identity == 0)))
      (fun result heap => result = .bool (!(identity == 0)) ∧ post heap))

end Ownership
end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.RefArgument


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.RefArgument
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings

def helperName : Name := "bindings_frame_ref_is_valid".toList
def emptyContext : Context := fun _ => none
def caller (sourceAddress : Ptr) : Context :=
  Function.update emptyContext refName (some (.object refType sourceAddress))

def callerProfile (region : AutomaticRegion Context) : Profile :=
  { profile with argumentCalls := fun name =>
      if name = helperName then some (service region emptyContext) else none }

def call (region : AutomaticRegion Context) (sourceAddress : Ptr) : CProg CVal CVal :=
  ObjectBindings.read (callerProfile region) layout (caller sourceAddress)
    (.call helperName [.identifier refName])

/-- Static record admission comes from the existing type and record-extent
inventory, and the whole argument fold reads the caller object once. -/
theorem argument_capture (region : AutomaticRegion Context) (sourceAddress : Ptr) :
    argumentsWithNames
      (localOrLocated (ObjectBindings.values (caller sourceAddress))
        (declared (caller sourceAddress)) (callerProfile region).locations)
      (callerProfile region).values layout [.identifier refName]
      (ObjectBindings.objects (callerProfile region) (caller sourceAddress)) .whole =
      (CProg.load sourceAddress >>= fun value => pure [.record refType [value]]) := by
  rfl

/-- The callee's parameter writes occur after the entire source snapshot.
The nested call executes the parsed helper; it is not a supplied result. -/
theorem call_captures_before_invocation (region : AutomaticRegion Context)
    (sourceAddress : Ptr) :
    call region sourceAddress =
      (CProg.load sourceAddress >>= fun value =>
        invoke region emptyContext [.record refType [value]] >>= returnedScalar) := by
  rfl

theorem call_retains_operations (sourceAddress : Ptr)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) :
    call (AutomaticRegion.bracket enter leave) sourceAddress =
      (CProg.load sourceAddress >>= fun fieldValue =>
        enter refName 1 >>= fun address =>
        CProg.store address fieldValue >>= fun _ =>
        CProg.loadU32 address >>= fun identity =>
        leave refName address 1 >>= fun _ => pure (.bool (!(identity == 0)))) := by
  refine (call_captures_before_invocation (AutomaticRegion.bracket enter leave)
    sourceAddress).trans ?_
  apply congrArg (fun continuation : CVal → CProg CVal CVal =>
    CProg.load sourceAddress >>= continuation)
  funext fieldValue
  refine (congrArg (fun program : CProg CVal (ReadBlock.Result Context) =>
    program >>= returnedScalar)
    (actual_record_parameter_bracket_field emptyContext fieldValue enter leave)).trans ?_
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, returnedScalar]


end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.RefArgument


set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings
open ReadBlock (Result Flow)
open DirectoryProbe

def indexType : CType := ⟨"BindingsFrameIndex".toList, 1⟩
def indexName : Name := "index".toList
def helperName : Name := "bindings_frame_ref_is_valid".toList
def types : TypeNames := ["BindingsFrameIndexEntry".toList,
  "BindingsFrameIndex".toList, "BindingsFrameRef".toList]

def function : CFunction :=
  ⟨Source.entryType, "bindings_frame_index_find_ref".toList,
    [⟨indexType, indexName⟩, ⟨RefArgument.refType, RefArgument.refName⟩], Source.findRefBody⟩

private def headerPiece0 : String × List Token :=
  ("static inline BindingsFrameIndexEntry ",
   [.identifier "static".toList, .identifier "inline".toList,
    .identifier "BindingsFrameIndexEntry".toList])
private def headerPiece1 : String × List Token :=
  ("*bindings_frame_index_find_ref(\n",
   [.punctuation ['*'], .identifier "bindings_frame_index_find_ref".toList,
    .punctuation ['(']])
private def headerPiece2 : String × List Token :=
  ("        BindingsFrameIndex *index, ",
   [.identifier "BindingsFrameIndex".toList, .punctuation ['*'],
    .identifier "index".toList, .punctuation [',']])
private def headerPiece3 : String × List Token :=
  ("BindingsFrameRef ref) ",
   [.identifier "BindingsFrameRef".toList, .identifier "ref".toList,
    .punctuation [')']])

private theorem header0_lex : headerPiece0.1.toList.foldl step initial =
    completed headerPiece0.2 := by decide +kernel
private theorem header1_lex : headerPiece1.1.toList.foldl step initial =
    completed headerPiece1.2 := by decide +kernel
private theorem header2_lex : headerPiece2.1.toList.foldl step initial =
    completed headerPiece2.2 := by decide +kernel
private theorem header3_lex : headerPiece3.1.toList.foldl step initial =
    completed headerPiece3.2 := by decide +kernel

private def pieces : List (String × List Token) :=
  headerPiece0 :: headerPiece1 :: headerPiece2 :: headerPiece3 :: Source.findRefPieces
def source : String := String.join (pieces.map Prod.fst)
def tokens : List Token := pieces.flatMap Prod.snd

theorem lexed : lex source.toList = .ok tokens := by
  apply lex_completed_string_pieces
  simp only [pieces, Source.findRefPieces, List.forall_cons]
  exact ⟨header0_lex, header1_lex, header2_lex, header3_lex,
    Source.findRefPiece0_lex, Source.findRefPiece1_lex,
    Source.findRefPiece2_lex, Source.findRefPiece3_lex, Source.findRefPiece4_lex,
    Source.findRefPiece5_lex, Source.findRefPiece6_lex, trivial⟩

theorem parsed : ordinaryFunctionText? types source.toList = some function :=
  function_text_using_of_parts (parameter? types) types source.toList
    tokens function lexed (by rfl)

/-- The helper catalogue retains actual lower programs for the continuation.
Only the validity call is supplied here, by its parsed by-value implementation. -/
def profile (calleeRegion : AutomaticRegion Context) (following : Calls) : Profile :=
  { RefArgument.profile with
      recordFields := some (fun type name =>
        if type = RefArgument.refType then
          if name = RefArgument.identityName then some ⟨0, .word⟩ else none
        else if type = ⟨"BindingsFrameIndexEntry".toList, 0⟩ then
          if name = "epoch".toList then some ⟨0, .word⟩ else none
        else none)
      values := following
      argumentCalls := fun name => if name = helperName then
        some (RefArgument.service calleeRegion (fun _ => none)) else none }

def services (calleeRegion : AutomaticRegion Context) (following : Calls) :
    ScopedServices Context :=
  ObjectBindings.services (profile calleeRegion following) calleeRegion
    (fun _ _ _ => CProg.undefined)

def bodyProgram (calleeRegion : AutomaticRegion Context) (following : Calls) (layout : Layout)
    (fuel : Nat) (context : Context) : CProg CVal (Result Context) :=
  executeScopedWith (services calleeRegion following) layout 0 fuel
    context Source.findRefBody

/-- The outer function's parameter region and its nested helper's region
are separate supplied activations. Their actual storage providers establish
freshness and lifetime; this wrapper does not allocate an invented record. -/
def invoke (parameterRegion calleeRegion : AutomaticRegion Context) (following : Calls) (layout : Layout)
    (fuel : Nat) (context : Context) (arguments : List CallArgument) :
    CProg CVal (Result Context) :=
  match ordinaryFunctionText? types source.toList with
  | none => CProg.undefined
  | some parsedFunction =>
      parameters (profile calleeRegion following) parameterRegion context
        parsedFunction.parameters arguments (fun localContext =>
          executeScopedWith (services calleeRegion following) layout 0 fuel
            localContext parsedFunction.body)

theorem invoke_from_actual_signature (parameterRegion calleeRegion : AutomaticRegion Context)
    (following : Calls) (layout : Layout) (fuel : Nat) (context : Context) (arguments : List CallArgument) :
    invoke parameterRegion calleeRegion following layout fuel context arguments =
      parameters (profile calleeRegion following) parameterRegion context
        [⟨indexType, indexName⟩, ⟨RefArgument.refType, RefArgument.refName⟩]
        arguments (bodyProgram calleeRegion following layout fuel) := by
  rw [invoke, parsed]
  rfl

private theorem scalar_parameter (p : Profile) (region : AutomaticRegion Context)
    (context : Context) (type : CType) (name : Name) (value converted : CVal)
    (notRecord : p.recordExtent type = none)
    (conversion : scalarInitialValue p type value = pure converted)
    (body : Context → CProg CVal (Result Context)) :
    parameter p region context type name (.scalar value) body =
      (body (Function.update context name (some (.scalar type (some converted)))) >>= fun result =>
        pure (ObjectBindings.restore name (context name) result)) := by
  simp only [parameter, notRecord, conversion, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

/-- The exact copied Ref and scalar pointer reach the actual full source
body. Both lexical bindings are restored only after that body returns. -/
theorem actual_two_parameter_entry (parameterRegion calleeRegion : AutomaticRegion Context)
    (following : Calls) (layout : Layout) (fuel : Nat) (context : Context) (index : Option Ptr)
    (identity : UInt32) :
    invoke parameterRegion calleeRegion following layout fuel context
      [.scalar (.ptr index), .record RefArgument.refType [.u32 identity]] =
      (parameterRegion RefArgument.refName 1 (fun address =>
        CProg.store address (.u32 identity) >>= fun _ =>
        bodyProgram calleeRegion following layout fuel
          (Function.update
            (Function.update context indexName (some (.scalar indexType (some (.ptr index)))))
            RefArgument.refName (some (.object RefArgument.refType address)))) >>= fun result =>
        pure (ObjectBindings.restore indexName (context indexName)
          (ObjectBindings.restore RefArgument.refName (context RefArgument.refName) result))) := by
  rw [invoke_from_actual_signature]
  change parameter (profile calleeRegion following) parameterRegion context indexType
    indexName (.scalar (.ptr index)) (fun withIndex =>
      parameter (profile calleeRegion following) parameterRegion withIndex
        RefArgument.refType RefArgument.refName (.record RefArgument.refType [.u32 identity])
        (bodyProgram calleeRegion following layout fuel)) = _
  have notRecord : (profile calleeRegion following).recordExtent indexType = none := by rfl
  have conversion : scalarInitialValue (profile calleeRegion following) indexType (.ptr index) =
      pure (.ptr index) := by rfl
  rw [scalar_parameter _ _ _ _ _ _ _ notRecord conversion]
  have extent : (profile calleeRegion following).recordExtent RefArgument.refType = some 1 := by rfl
  rw [parameter_record_keeps_complete_copy _ _ _ _ _ [.u32 identity] 1 extent rfl]
  have different : RefArgument.refName ≠ indexName := by decide
  simp only [CProg.initializeCells, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc,
    Prog.ret_bind, Function.update_of_ne different]

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings
open ReadBlock (Result Flow)
open DirectoryProbe

private theorem read_scalar (region : AutomaticRegion Context) (following : Calls)
    (layout : Layout) (context : Context) (name : Name) (type : CType) (value : CVal)
    (bound : context name = some (.scalar type (some value))) :
    ObjectBindings.read (profile region following) layout context (.identifier name) =
      pure value := by
  simp only [ObjectBindings.read, expressionWithNames, localOrLocated,
    ObjectBindings.values, bound]

private def captureNames (region : AutomaticRegion Context) (following : Calls)
    (context : Context) := localOrLocated (ObjectBindings.values context) (declared context)
      (profile region following).locations

private theorem capture_admitted (region : AutomaticRegion Context) (following : Calls)
    (context : Context) (sourceAddress : Ptr)
    (bound : context RefArgument.refName = some (.object RefArgument.refType sourceAddress)) :
    (ObjectBindings.objects (profile region following) context).record
        (.identifier RefArgument.refName) = some (RefArgument.refType, 1) := by
  simp only [ObjectBindings.objects, ScalarBytes.typeOf?, ObjectBindings.types,
    bound, profile, RefArgument.profile, Profile.recordExtent, List.mem_cons,
    List.not_mem_nil, or_false]
  rfl


private theorem capture_place (region : AutomaticRegion Context) (following : Calls)
    (layout : Layout) (context : Context) (sourceAddress : Ptr)
    (bound : context RefArgument.refName = some (.object RefArgument.refType sourceAddress)) :
    placeWithNames (captureNames region following context) (profile region following).values layout
      (.identifier RefArgument.refName) (ObjectBindings.objects (profile region following) context) =
        pure sourceAddress := by
  simp only [placeWithNames.eq_def, ObjectBindings.objects, ObjectBindings.places, bound,
    Option.bind_some, resolved]


private theorem capture_arguments (region : AutomaticRegion Context) (following : Calls)
    (layout : Layout) (context : Context) (sourceAddress : Ptr)
    (bound : context RefArgument.refName = some (.object RefArgument.refType sourceAddress)) :
    argumentsWithNames (captureNames region following context) (profile region following).values layout
      [.identifier RefArgument.refName] (ObjectBindings.objects (profile region following) context) .whole =
      (CProg.load sourceAddress >>= fun value =>
        pure [CallArgument.record RefArgument.refType [value]]) := by
  rw [arguments_whole_record_cons _ _ _ _ _ _ _ _
    (capture_admitted region following context sourceAddress bound),
    capture_place region following layout context sourceAddress bound]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, CProg.loadCells,
    argumentsWithNames.eq_def, Prog.bind_assoc]


/-- Capture precedes the nested parameter copy and parsed helper invocation. -/
theorem validity_call_snapshots_parameter (region : AutomaticRegion Context)
    (following : Calls) (layout : Layout) (context : Context) (sourceAddress : Ptr)
    (bound : context RefArgument.refName = some (.object RefArgument.refType sourceAddress)) :
    ObjectBindings.read (profile region following) layout context
      (.call helperName [.identifier RefArgument.refName]) =
      (CProg.load sourceAddress >>= fun value =>
        RefArgument.invoke region (fun _ => none)
          [.record RefArgument.refType [value]] >>= RefArgument.returnedScalar) := by
  have initial := explicit_call_waits_for_all_arguments
    (captureNames region following context) (profile region following).values layout helperName
    [.identifier RefArgument.refName] (ObjectBindings.objects (profile region following) context)
    (RefArgument.service region (fun _ => none)) (by rfl)
  have captured := congrArg
    (fun arguments : CProg CVal (List CallArgument) =>
      Prog.bind arguments (RefArgument.service region (fun _ => none)).invoke)
    (capture_arguments region following layout context sourceAddress bound)
  have reassociate := Prog.bind_assoc (CProg.load sourceAddress)
    (fun value => (pure [CallArgument.record RefArgument.refType [value]] : CProg CVal _))
    (RefArgument.service region (fun _ => none)).invoke
  have finish :
      (CProg.load sourceAddress >>= fun value =>
        (pure [CallArgument.record RefArgument.refType [value]] : CProg CVal _) >>=
          (RefArgument.service region (fun _ => none)).invoke) =
      (CProg.load sourceAddress >>= fun value =>
        (RefArgument.service region (fun _ => none)).invoke
          [CallArgument.record RefArgument.refType [value]]) := by
    apply congrArg (fun next : CVal → CProg CVal CVal => Prog.bind (CProg.load sourceAddress) next)
    funext value
    exact Prog.ret_bind _ _
  exact initial.trans (captured.trans (reassociate.trans finish))


end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings
open ReadBlock (Result Flow)
open DirectoryProbe


theorem validity_call_keeps_operations (following : Calls) (layout : Layout)
    (context : Context) (sourceAddress : Ptr)
    (bound : context RefArgument.refName = some (.object RefArgument.refType sourceAddress))
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) :
    ObjectBindings.read (profile (AutomaticRegion.bracket enter leave) following) layout context
      (.call helperName [.identifier RefArgument.refName]) =
      (CProg.load sourceAddress >>= fun captured =>
        enter RefArgument.refName 1 >>= fun address =>
        CProg.store address captured >>= fun _ =>
        CProg.loadU32 address >>= fun observed =>
        leave RefArgument.refName address 1 >>= fun _ =>
        pure (CVal.bool (!(observed == 0)))) := by
  refine (validity_call_snapshots_parameter _ _ _ _ _ bound).trans ?_
  apply congrArg (fun continuation : CVal → CProg CVal CVal =>
    CProg.load sourceAddress >>= continuation)
  funext value
  refine (congrArg (fun program : CProg CVal (Result Context) =>
    program >>= RefArgument.returnedScalar)
    (RefArgument.actual_record_parameter_bracket_field (fun _ => none) value enter leave)).trans ?_
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    RefArgument.returnedScalar]

def entryGuard : CExpr := .binary .or (.unary .not (Source.id "index"))
  (.unary .not (.call helperName [Source.id "ref"]))

theorem source_starts_with_guard :
    Source.findRefBody.head? = some (.branch entryGuard Source.nullReturn []) := rfl

/-- The actual first source condition short-circuits a null index before
reading the already-entered Ref parameter or invoking its nested helper.
The outer function's argument snapshots have occurred before this point. -/
theorem guard_keeps_actual_nested_call (following : Calls) (layout : Layout)
    (context : Context) (index : Option Ptr) (sourceAddress : Ptr)
    (indexBound : context indexName = some (.scalar indexType (some (.ptr index))))
    (refBound : context RefArgument.refName = some (.object RefArgument.refType sourceAddress))
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) :
    ObjectBindings.read (profile (AutomaticRegion.bracket enter leave) following) layout context
      entryGuard =
      (CProg.ptrEq index none >>= fun isNull =>
        if isNull then pure (CVal.bool true) else
          CProg.load sourceAddress >>= fun captured =>
          enter RefArgument.refName 1 >>= fun address =>
          CProg.store address captured >>= fun _ =>
          CProg.loadU32 address >>= fun observed =>
          leave RefArgument.refName address 1 >>= fun _ =>
          pure (CVal.bool (observed == 0))) := by
  change ((ObjectBindings.read (profile (AutomaticRegion.bracket enter leave) following) layout context (.identifier indexName) >>= fun first =>
    truth first >>= fun selected => pure (CVal.bool (!selected))) >>= fun first =>
    truth first >>= fun selected => if selected then pure (CVal.bool true) else
      ((ObjectBindings.read (profile (AutomaticRegion.bracket enter leave) following) layout context (.call helperName [.identifier RefArgument.refName])
        >>= fun second => truth second >>= fun selectedSecond => pure (CVal.bool (!selectedSecond)))
        >>= fun second => truth second >>= fun selectedSecond => pure (CVal.bool selectedSecond))) = _
  rw [read_scalar _ _ _ _ _ _ _ indexBound]
  simp only [truth, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, Bool.not_not]
  apply congrArg (fun continuation : Bool → CProg CVal CVal => CProg.ptrEq index none >>= continuation)
  funext isNull
  cases isNull
  · simp only [Bool.false_eq_true, if_false]
    rw [validity_call_keeps_operations following layout context sourceAddress refBound enter leave]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, Bool.not_not]
  · rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityWrapper
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.SeparationAlgebra
open ObjectBindings
open ReadBlock (Result Flow)


def identityType : CType := ⟨"CettaFrameIdentity".toList, 0⟩
def identityName : Name := "identity".toList

def callProfile (allowance : Nat) : Profile :=
  { profile allowance with scalarAliases := fun type =>
      if type = identityType then some ⟨"uint32_t".toList, 0⟩ else none }

private def header0 : String × List Token :=
  ("static inline uint32_t cetta_frame_handle(",
   [.identifier "static".toList, .identifier "inline".toList,
    .identifier "uint32_t".toList, .identifier "cetta_frame_handle".toList,
    .punctuation ['(']])
private def header1 : String × List Token :=
  ("CettaFrameIdentity identity) ",
   [.identifier "CettaFrameIdentity".toList, .identifier "identity".toList,
    .punctuation [')']])
private theorem header0_lex : header0.1.toList.foldl step initial =
    completed header0.2 := by decide +kernel
private theorem header1_lex : header1.1.toList.foldl step initial =
    completed header1.2 := by decide +kernel
private def pieces : List (String × List Token) := header0 :: header1 :: IdentitySource.handlePieces

def functionSource : String := String.join (pieces.map Prod.fst)
def functionTokens : List Token := pieces.flatMap Prod.snd
def handleFunction : CFunction := ⟨⟨"uint32_t".toList, 0⟩,
  "cetta_frame_handle".toList, [⟨identityType, identityName⟩], IdentitySource.handleBody⟩

theorem function_lexed : lex functionSource.toList = .ok functionTokens := by
  apply lex_completed_string_pieces
  simp only [pieces, IdentitySource.handlePieces, List.forall_cons]
  exact ⟨header0_lex, header1_lex, IdentitySource.handlePiece0_lex, IdentitySource.handlePiece1_lex,
    IdentitySource.handlePiece2_lex, IdentitySource.handlePiece3_lex, IdentitySource.handlePiece4_lex, trivial⟩

theorem function_parsed : ordinaryFunctionText? IdentitySource.types functionSource.toList =
    some handleFunction :=
  function_text_using_of_parts (parameter? IdentitySource.types) IdentitySource.types
    functionSource.toList functionTokens handleFunction function_lexed (by rfl)

/-- Actual source signature, scalar typedef conversion, parameter shadowing,
parsed body and restoration. The native ABI and region provider remain visible. -/
def invokeHandle (allowance : Nat) (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (context : Context)
    (arguments : List CallArgument) : CProg CVal (Result Context) :=
  match ordinaryFunctionText? IdentitySource.types functionSource.toList with
  | none => CProg.undefined
  | some fn => parameters (callProfile allowance) (AutomaticRegion.bracket enter leave)
      context fn.parameters arguments fun localContext =>
        executeScopedWith (service allowance (AutomaticRegion.bracket enter leave))
          IdentityRead.layout 0 3 localContext fn.body

/-- The caller observes the function's returned UInt32 only after the full
body and its automatic-region exit have returned. -/
def handleCall (allowance : Nat) (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (context : Context)
    (identity : UInt32) : CProg CVal UInt32 := do
  let result ← invokeHandle allowance enter leave context [.scalar (.u32 identity)]
  match result with
  | .finished (.returned _ (some (.u32 value))) => pure value
  | _ => CProg.undefined

theorem invoke_handle_keeps_source_operations (allowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr) (leave : Name → Ptr → Nat → CProg CVal Unit)
    (context : Context) (identity : UInt32) :
    invokeHandle allowance enter leave context [.scalar (.u32 identity)] =
      (enter "parts".toList 3 >>= fun address =>
        IdentityRead.handleProgram identity address >>= fun word =>
          leave "parts".toList address 3 >>= fun _ =>
            pure (.finished (.returned context (some (.u32 word))))) := by
  rw [invokeHandle, function_parsed]
  change parameter (callProfile allowance) (AutomaticRegion.bracket enter leave)
    context identityType identityName (.scalar (.u32 identity))
    (fun localContext => executeScopedWith (service allowance (AutomaticRegion.bracket enter leave))
      IdentityRead.layout 0 3 localContext IdentitySource.handleBody) = _
  have extent : (callProfile allowance).recordExtent identityType = none := by rfl
  have convert : scalarInitialValue (callProfile allowance) identityType (.u32 identity) =
      pure (.u32 identity) := by rfl
  simp only [parameter, extent, convert, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  let localContext : Context := Function.update context identityName
    (some (.scalar identityType (some (.u32 identity))))
  have bound : localContext "identity".toList =
      some (.scalar ⟨"CettaFrameIdentity".toList, 0⟩ (some (.u32 identity))) :=
    Function.update_self _ _ _
  have body := actual_handle_body allowance 0 enter leave localContext identity bound
  change (executeScopedWith (service allowance (AutomaticRegion.bracket enter leave))
      IdentityRead.layout 0 3 localContext IdentitySource.handleBody >>= fun result =>
        pure (ObjectBindings.restore identityName (context identityName) result)) = _
  refine (congrArg (fun program : CProg CVal (Result Context) =>
    program >>= fun result =>
      pure (ObjectBindings.restore identityName (context identityName) result)) body).trans ?_
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    localContext, returned_local_restores_previous_binding]

theorem handle_call_keeps_source_operations (allowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr) (leave : Name → Ptr → Nat → CProg CVal Unit)
    (context : Context) (identity : UInt32) :
    handleCall allowance enter leave context identity =
      (enter "parts".toList 3 >>= fun address =>
        IdentityRead.handleProgram identity address >>= fun word =>
          leave "parts".toList address 3 >>= fun _ => pure word) := by
  rw [handleCall, invoke_handle_keeps_source_operations]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Only entry and exit are component contracts. The result is earned by the
three stores and actual post-store loads of the parsed helper in between. -/
theorem actual_handle_owned (allowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr) (leave : Name → Ptr → Nat → CProg CVal Unit)
    (context : Context) (identity : UInt32) (pre post : Heap L → Prop)
    (remainder : Ptr → Heap L → Prop)
    (entry : CTriple pre (enter "parts".toList 3) (fun address heap =>
      ∃ old : List (Option CVal), old.length = 3 ∧ (Cells address old ∗ remainder address) heap))
    (exit : ∀ address handle generation maximum,
      CTriple (IdentityRead.PartsCells address handle generation maximum ∗ remainder address)
        (leave "parts".toList address 3) (fun _ => post)) :
    CTriple pre (handleCall allowance enter leave context identity)
      (fun handle heap => handle.toNat = unpackHandle identity.toNat ∧ post heap) := by
  rw [handle_call_keeps_source_operations]
  refine triple_bind _ entry fun address => ?_
  apply triple_exists
  intro old
  apply triple_pure
  intro length
  have body := frame (IdentityRead.handle_program_spec (L := L) identity address old length)
    (remainder address)
  simp only [sepConj_pure_left] at body
  refine triple_bind _ body fun handle => ?_
  apply triple_pure
  intro decoded
  refine triple_bind _ (exit address _ _ _) fun _ => ?_
  exact triple_pre _ (fun _ held => ⟨decoded, held⟩)
    (triple_ret act handle (fun actual heap => actual.toNat = unpackHandle identity.toNat ∧ post heap))

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityWrapper


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityWrapper
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- A concrete borrowed scratch activation inhabits the primitive region
contracts: three separately owned cells are reused, and every other owned cell
is framed. This is not a claim about a native automatic-storage allocator.
The actual helper still performs its stores and validation loads. -/
theorem borrowed_scratch_handle_spec (allowance : Nat) (context : Context)
    (output : Ptr) (identity : UInt32) (frame : Heap L → Prop) :
    CTriple (fun heap => ∃ old : List (Option CVal), old.length = 3 ∧
        (Cells output old ∗ frame) heap)
      (handleCall allowance (fun _ _ => pure output) (fun _ _ _ => pure ()) context identity)
      (fun handle heap => handle.toNat = unpackHandle identity.toNat ∧
        ∃ old : List (Option CVal), old.length = 3 ∧ (Cells output old ∗ frame) heap) := by
  apply actual_handle_owned allowance _ _ context identity _ _
    (fun address heap => address = output ∧ frame heap)
  · apply triple_pre _ (spec := triple_ret act output _)
    rintro heap ⟨old, length, held⟩
    refine ⟨old, length, ?_⟩
    simpa only [sepConj_pure_right, and_true, true_and] using held
  · intro address handle generation maximum
    apply triple_pre _ (spec := triple_ret act () _)
    intro heap held
    rw [sepConj_pure_right] at held
    rcases held with ⟨rfl, owned⟩
    exact ⟨[some (.u32 handle), some (.u32 generation), some (.u32 maximum)], rfl, owned⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityWrapper


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Effectful
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open SourceRead
open Mettapedia.Machines.IncrementalConformance

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

private theorem loadPtr_at {address : Ptr} {value : Option Ptr} {heap : Heap L}
    {post : Option Ptr → Heap L → Prop} (reads : Reads address (.ptr value) heap)
    (holds : post value heap) : (CProg.loadPtr address).wp act post heap := by
  refine wp_consequence act
    (loadPtr_rule (P := fun reached => reached = heap) (q := value) ?_) rfl ?_
  · rintro reached rfl
    exact reads
  · rintro actual reached ⟨rfl, rfl⟩
    exact holds

private theorem loadU32_at {address : Ptr} {value : UInt32} {heap : Heap L}
    {post : UInt32 → Heap L → Prop} (reads : Reads address (.u32 value) heap)
    (holds : post value heap) : (CProg.loadU32 address).wp act post heap := by
  refine wp_consequence act
    (loadU32_rule (P := fun reached => reached = heap) (n := value) ?_) rfl ?_
  · rintro reached rfl
    exact reads
  · rintro actual reached ⟨rfl, rfl⟩
    exact holds

/-- Finite physical iteration with the actual parsed helper. Only automatic
entry/exit ownership is supplied. Every key comparison follows the three
stores and reached typed loads; the directory invariant holds in that reached
heap, rather than being inferred from a pure decoded-value equation. -/
theorem search_returns_probe (allowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (context : Context)
    (directory : Ptr) (key mask : UInt32)
    (cells : InternProbe.Cells Nat Ptr) (pre : Heap L → Prop)
    (remainder : Ptr → Heap L → Prop)
    (entry : CTriple pre (enter "parts".toList 3) (fun address heap =>
      ∃ old : List (Option CVal), old.length = 3 ∧ (Cells address old ∗ remainder address) heap))
    (exit : ∀ address handle generation maximum,
      CTriple (IdentityRead.PartsCells address handle generation maximum ∗ remainder address)
        (leave "parts".toList address 3) (fun _ => pre))
    (stops : (InternProbe.probe key.toNat cells).1 ≠ none ∨
      (InternProbe.probe key.toNat cells).2 ≠ none)
    (fuel : Nat) (slot : UInt32) (enough : cells.length ≤ fuel)
    (inventory : ∀ heap, pre heap → Physical.SequenceRead directory mask slot cells heap) :
    CTriple pre (search (IdentityWrapper.handleCall allowance enter leave context)
      directory key mask fuel slot)
      (fun result heap => pre heap ∧ ∃ finalSlot,
        result = .finished (.returned finalSlot
          (some (.ptr (InternProbe.probe key.toNat cells).1)))) := by
  induction cells generalizing fuel slot with
  | nil => simp [InternProbe.probe] at stops
  | cons cell tail ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      intro heap held
      obtain ⟨readCell, _⟩ := inventory heap held
      obtain ⟨table, readTable, readPointer, readEpoch⟩ := readCell
      change (search _ directory key mask (fuel + 1) slot).wp act _ heap
      rw [search, ReadBlock.whileWith.eq_def]
      simp only [Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, ↓reduceIte]
      rw [wp_bind]
      rw [iteration, wp_bind']
      apply loadPtr_at readTable
      rw [wp_bind']
      apply loadPtr_at readPointer
      rw [wp_bind']
      cases cell with
      | none =>
        simp only [Option.map_none]
        apply wp_ptrEq (by trivial) (by trivial)
        simp only [decide_true, ↓reduceIte, wp_pure, wp_ret]
        exact ⟨held, slot, rfl⟩
      | some pair =>
        rcases pair with ⟨stored, address⟩
        simp only [Option.map_some]
        obtain ⟨valid, epoch, readValue, keyValue⟩ := readEpoch
        apply wp_ptrEq (p := some address) (q := none)
          (show ValidOpt heap (some address) from valid) (by trivial)
        simp only [Option.some_ne_none, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [wp_bind']
        apply loadU32_at readValue
        rw [wp_bind']
        refine wp_mono act ?_
          (IdentityWrapper.actual_handle_owned allowance enter leave context epoch pre pre
            remainder entry exit heap held)
        rintro actual reached ⟨decoded, retained⟩
        have actualKey : actual.toNat = stored := decoded.trans keyValue
        by_cases same : stored = key.toNat
        · have equal : actual = key := UInt32.toNat.inj (actualKey.trans same)
          simp only [equal, ↓reduceIte, wp_pure, wp_ret]
          exact ⟨retained, slot, by simp [InternProbe.probe, same]⟩
        · have different : actual ≠ key := fun equality => same (equality ▸ actualKey.symm)
          simp only [different, ↓reduceIte, wp_pure]
          have tailStops : (InternProbe.probe key.toNat tail).1 ≠ none ∨
              (InternProbe.probe key.toNat tail).2 ≠ none := by
            simpa [InternProbe.probe, Ne.symm same] using stops
          have next := ih tailStops fuel (advance slot mask)
            (by simp only [List.length_cons] at enough; omega)
            (fun target owns => (inventory target owns).2) reached retained
          simpa only [Prog.wp, search, Prog.pure_eq, InternProbe.probe,
            if_neg (Ne.symm same)] using next

/-- Half load supplies a stopping cell independently of the lookup result.
No repeated helper call is erased from the returned operation tree. -/
theorem search_returns_inventory (allowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (context : Context)
    (directory : Ptr) (key mask slot : UInt32)
    (bits : Nat) (width : bits ≤ 32) (shape : mask.toNat = 2 ^ bits - 1)
    (inside : slot.toNat < 2 ^ bits)
    (table : Fin (2 ^ bits) → Option (Nat × Ptr))
    (loaded : (List.ofFn table).countP Option.isSome ≤ 2 ^ bits / 2)
    (fuel : Nat) (enough : 2 ^ bits ≤ fuel) (pre : Heap L → Prop)
    (remainder : Ptr → Heap L → Prop)
    (entry : CTriple pre (enter "parts".toList 3) (fun address heap =>
      ∃ old : List (Option CVal), old.length = 3 ∧ (Cells address old ∗ remainder address) heap))
    (exit : ∀ address handle generation maximum,
      CTriple (IdentityRead.PartsCells address handle generation maximum ∗ remainder address)
        (leave "parts".toList address 3) (fun _ => pre))
    (reads : ∀ heap, pre heap → ∀ position,
      Physical.CellRead directory (UInt32.ofNat position.val) (table position) heap) :
    CTriple pre (search (IdentityWrapper.handleCall allowance enter leave context)
      directory key mask fuel slot)
      (fun result heap => pre heap ∧ ∃ finalSlot,
        result = .finished (.returned finalSlot
          (some (.ptr (InternProbe.probe key.toNat (sequence table ⟨slot.toNat, inside⟩)).1)))) := by
  exact search_returns_probe allowance enter leave context directory key mask _ pre remainder
    entry exit (sequence_stops_of_half_load table ⟨slot.toNat, inside⟩ loaded key.toNat)
    fuel slot (by simpa only [sequence, List.length_ofFn] using enough)
    (fun heap held => Physical.sequenceRead_of_inventory directory mask slot bits width shape
      inside table heap (reads heap held))

/-- The actual whole lookup keeps the hash reads and the complete helper
calls, while its public result is determined by the independent inventory. -/
theorem lookup_returns_inventory (helperAllowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (context : Context)
    (directory : Ptr) (handle mask shift : UInt32)
    (validShift : shift.toNat < 32)
    (maskShape : mask.toNat = 2 ^ (32 - shift.toNat) - 1)
    (table : Fin (2 ^ (32 - shift.toNat)) → Option (Nat × Ptr))
    (loaded : (List.ofFn table).countP Option.isSome ≤ 2 ^ (32 - shift.toNat) / 2)
    (allowance : Nat) (enough : 2 ^ (32 - shift.toNat) ≤ allowance)
    (pre : Heap L → Prop) (remainder : Ptr → Heap L → Prop)
    (entry : CTriple pre (enter "parts".toList 3) (fun address heap =>
      ∃ old : List (Option CVal), old.length = 3 ∧ (Cells address old ∗ remainder address) heap))
    (exit : ∀ address h g m,
      CTriple (IdentityRead.PartsCells address h g m ∗ remainder address)
        (leave "parts".toList address 3) (fun _ => pre))
    (inventory : ∀ heap, pre heap → LookupReads directory mask shift table heap) :
    CTriple pre (lookupProgram (IdentityWrapper.handleCall helperAllowance enter leave context)
      directory handle allowance)
      (fun result heap => pre heap ∧
        result = .finished (.returned () (some (.ptr
          (InternProbe.probe handle.toNat
            (sequence table ⟨(home handle shift).toNat,
              home_within_capacity handle shift validShift⟩)).1)))) := by
  intro heap held
  obtain ⟨tableAddress, readTable, liveTable, readMask, readShift, _⟩ := inventory heap held
  change (lookupProgram _ directory handle allowance).wp act _ heap
  rw [lookupProgram, wp_bind']
  apply loadPtr_at readTable
  rw [wp_bind']
  apply wp_ptrEq (p := some tableAddress) (q := none)
    (show ValidOpt heap (some tableAddress) from liveTable) (by trivial)
  simp only [Option.some_ne_none, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply loadU32_at readMask
  rw [homeProgram, wp_bind', wp_bind']
  apply loadU32_at readShift
  rw [homeProgram_at_shift handle shift validShift]
  simp only [Prog.pure_eq, Prog.bind_eq, wp_ret, Prog.ret_bind, word]
  rw [wp_bind]
  apply wp_mono act (Q := fun result reached => pre reached ∧ ∃ finalSlot,
    result = .finished (.returned finalSlot
      (some (.ptr (InternProbe.probe handle.toNat
        (sequence table ⟨(home handle shift).toNat,
          home_within_capacity handle shift validShift⟩)).1))))
  · rintro result reached ⟨retained, finalSlot, rfl⟩
    simpa [wp_pure, wp_ret, ReadBlock.Result.mapContext,
      ReadBlock.Flow.mapContext] using retained
  · exact search_returns_inventory helperAllowance enter leave context directory handle mask
      (home handle shift) (32 - shift.toNat) (Nat.sub_le _ _) maskShape
      (home_within_capacity handle shift validShift) table loaded allowance enough pre remainder
      entry exit (fun reached owns => (inventory reached owns).choose_spec.2.2.2.2) heap held

/-- Source-body correctness with real helper execution. This result does not
identify operation traces with those of a pure identity decoder. -/
theorem parsed_lookup_returns_inventory (helperAllowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (callee : Context)
    (outer : Context) (directory : Ptr) (directoryType : CType)
    (handle mask shift : UInt32) (validShift : shift.toNat < 32)
    (maskShape : mask.toNat = 2 ^ (32 - shift.toNat) - 1)
    (table : Fin (2 ^ (32 - shift.toNat)) → Option (Nat × Ptr))
    (loaded : (List.ofFn table).countP Option.isSome ≤ 2 ^ (32 - shift.toNat) / 2)
    (allowance : Nat) (enough : 2 ^ (32 - shift.toNat) ≤ allowance)
    (directoryLocal : outer "index".toList = SourceRead.scalar directoryType (.ptr (some directory)))
    (handleLocal : outer "handle".toList = SourceRead.scalar Source.uint32 (.u32 handle))
    (pre : Heap L → Prop) (remainder : Ptr → Heap L → Prop)
    (entry : CTriple pre (enter "parts".toList 3) (fun address heap =>
      ∃ old : List (Option CVal), old.length = 3 ∧ (Cells address old ∗ remainder address) heap))
    (exit : ∀ address h g m,
      CTriple (IdentityRead.PartsCells address h g m ∗ remainder address)
        (leave "parts".toList address 3) (fun _ => pre))
    (inventory : ∀ heap, pre heap → LookupReads directory mask shift table heap) :
    CTriple pre
      (executeScopedWith (services (IdentityWrapper.handleCall helperAllowance enter leave callee))
        layout allowance 12 outer Source.lookupBody)
      (fun result heap => pre heap ∧
        result = .finished (.returned outer (some (.ptr
          (InternProbe.probe handle.toNat
            (sequence table ⟨(home handle shift).toNat,
              home_within_capacity handle shift validShift⟩)).1)))) := by
  rw [actual_lookup_body _ outer directory directoryType handle allowance directoryLocal handleLocal]
  intro heap held
  change (lookupProgram _ directory handle allowance >>= fun result =>
    pure (result.mapContext (fun _ => outer))).wp act _ heap
  rw [wp_bind']
  refine wp_mono act ?_
    (lookup_returns_inventory helperAllowance enter leave callee directory handle mask shift
      validShift maskShape table loaded allowance enough pre remainder entry exit inventory heap held)
  rintro result reached ⟨retained, rfl⟩
  simpa [wp_pure, wp_ret, ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext] using retained

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Effectful


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Effectful
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.Machines.CMemory.ProductiveBlocks
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open SourceRead
open Mettapedia.Machines.IncrementalConformance

/-- The independent inventory and primitive ownership contracts construct
an actual completed retained run. No successful child history is assumed. -/
theorem retained_lookup_completion (helperAllowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (callee : Context)
    (outer : Context) (directory : Ptr) (directoryType : CType)
    (handle mask shift : UInt32) (validShift : shift.toNat < 32)
    (maskShape : mask.toNat = 2 ^ (32 - shift.toNat) - 1)
    (table : Fin (2 ^ (32 - shift.toNat)) → Option (Nat × Ptr))
    (loaded : (List.ofFn table).countP Option.isSome ≤ 2 ^ (32 - shift.toNat) / 2)
    (allowance : Nat) (enough : 2 ^ (32 - shift.toNat) ≤ allowance)
    (directoryLocal : outer "index".toList = SourceRead.scalar directoryType (.ptr (some directory)))
    (handleLocal : outer "handle".toList = SourceRead.scalar Source.uint32 (.u32 handle))
    (pre : Heap (Excl (Option CVal)) → Prop)
    (remainder : Ptr → Heap (Excl (Option CVal)) → Prop)
    (entry : CTriple pre (enter "parts".toList 3) (fun address heap =>
      ∃ old : List (Option CVal), old.length = 3 ∧ (Cells address old ∗ remainder address) heap))
    (exit : ∀ address h g m,
      CTriple (IdentityRead.PartsCells address h g m ∗ remainder address)
        (leave "parts".toList address 3) (fun _ => pre))
    (inventory : ∀ heap, pre heap → LookupReads directory mask shift table heap)
    (storage : Storage CVal) (owned : pre (heap storage)) :
    ∃ choices fuel final,
      (machine.run fuel (State.mk (executeScopedWith (services (IdentityWrapper.handleCall helperAllowance enter leave callee))
        layout allowance 12 outer Source.lookupBody) storage choices)).2 =
        .finished (.returned final) ∧
      final.answer = ReadBlock.Result.finished (.returned outer (some (.ptr
          (InternProbe.probe handle.toNat
            (sequence table ⟨(home handle shift).toNat,
              home_within_capacity handle shift validShift⟩)).1))) ∧ pre (heap final.storage) := by
  let program := (executeScopedWith (services (IdentityWrapper.handleCall helperAllowance enter leave callee))
        layout allowance 12 outer Source.lookupBody)
  have spec := parsed_lookup_returns_inventory helperAllowance enter leave callee outer
    directory directoryType handle mask shift validShift maskShape table loaded allowance
    enough directoryLocal handleLocal pre remainder entry exit inventory
  have safe := (spec (heap storage) owned).1
  obtain ⟨answer, after, ran⟩ := exists_runs program (heap storage) safe
  have post := (spec (heap storage) owned).2 answer after ran
  obtain ⟨choices, fuel, final, answerCorrect, heapCorrect, completed⟩ :=
    source_execution_realized program storage answer after safe ran
  refine ⟨choices, fuel, final, completed, answerCorrect.trans post.2, ?_⟩
  rw [heapCorrect]
  exact post.1

/-- Every completed retained execution reflects the independent inventory;
its raw storage and causal history remain present in the retained result. -/
theorem retained_lookup_reflection (helperAllowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (callee : Context)
    (outer : Context) (directory : Ptr) (directoryType : CType)
    (handle mask shift : UInt32) (validShift : shift.toNat < 32)
    (maskShape : mask.toNat = 2 ^ (32 - shift.toNat) - 1)
    (table : Fin (2 ^ (32 - shift.toNat)) → Option (Nat × Ptr))
    (loaded : (List.ofFn table).countP Option.isSome ≤ 2 ^ (32 - shift.toNat) / 2)
    (allowance : Nat) (enough : 2 ^ (32 - shift.toNat) ≤ allowance)
    (directoryLocal : outer "index".toList = SourceRead.scalar directoryType (.ptr (some directory)))
    (handleLocal : outer "handle".toList = SourceRead.scalar Source.uint32 (.u32 handle))
    (pre : Heap (Excl (Option CVal)) → Prop)
    (remainder : Ptr → Heap (Excl (Option CVal)) → Prop)
    (entry : CTriple pre (enter "parts".toList 3) (fun address heap =>
      ∃ old : List (Option CVal), old.length = 3 ∧ (Cells address old ∗ remainder address) heap))
    (exit : ∀ address h g m,
      CTriple (IdentityRead.PartsCells address h g m ∗ remainder address)
        (leave "parts".toList address 3) (fun _ => pre))
    (inventory : ∀ heap, pre heap → LookupReads directory mask shift table heap)
    (storage : Storage CVal) (owned : pre (heap storage))
    (choices : List AllocationChoice) (fuel : Nat)
    (final : Finished CVal (ReadBlock.Result Context))
    (completed : (machine.run fuel (State.mk (executeScopedWith (services (IdentityWrapper.handleCall helperAllowance enter leave callee))
        layout allowance 12 outer Source.lookupBody) storage choices)).2 =
      .finished (.returned final)) :
    pre (heap final.storage) ∧ final.answer = ReadBlock.Result.finished (.returned outer (some (.ptr
          (InternProbe.probe handle.toNat
            (sequence table ⟨(home handle shift).toNat,
              home_within_capacity handle shift validShift⟩)).1))) := by
  exact ((parsed_lookup_returns_inventory helperAllowance enter leave callee outer
    directory directoryType handle mask shift validShift maskShape table loaded allowance
    enough directoryLocal handleLocal pre remainder entry exit inventory)
      (heap storage) owned).2 _ _ (returned_sound _ _ _ completed)

/-- Pause retains the actual decoder's current stores, remaining loads,
parent loop and older lexical bindings. Only the saved suffix is resumed. -/
theorem retained_lookup_resume (decode : UInt32 → CProg CVal UInt32)
    (outer : Context) (allowance : Nat) (storage : Storage CVal)
    (choices : List AllocationChoice) (first extra : Nat)
    (saved : State CVal (ReadBlock.Result Context)) (events : List (Receipt CVal))
    (paused : machine.run first
      (State.mk (executeScopedWith (services decode) layout allowance 12 outer Source.lookupBody)
        storage choices) = (events, .exhausted saved)) :
    machine.run (first + extra)
      (State.mk (executeScopedWith (services decode) layout allowance 12 outer Source.lookupBody)
        storage choices) =
      (events ++ (machine.run extra saved).1, (machine.run extra saved).2) :=
  resume_after_prefix first extra _ saved events paused

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Effectful


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Effectful.LookupCall
open DirectoryProbe.SourceRead (lookupProgram actual_lookup_body)
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ObjectBindings

def indexType : CType := ⟨"BindingsFrameIndex".toList, 1⟩
def indexName : Name := "index".toList
def handleName : Name := "handle".toList
def types : TypeNames := ["BindingsFrameIndex".toList,
  "BindingsFrameIndexEntry".toList, "uint32_t".toList]

private def header0 : String × List Token :=
  ("static inline BindingsFrameIndexEntry *bindings_frame_table_lookup(\n",
   [.identifier "static".toList, .identifier "inline".toList,
    .identifier "BindingsFrameIndexEntry".toList, .punctuation ['*'],
    .identifier "bindings_frame_table_lookup".toList, .punctuation ['(']])
private def header1 : String × List Token :=
  ("        const BindingsFrameIndex *index, uint32_t handle) ",
   [.identifier "const".toList, .identifier "BindingsFrameIndex".toList,
    .punctuation ['*'], .identifier "index".toList, .punctuation [','],
    .identifier "uint32_t".toList, .identifier "handle".toList, .punctuation [')']])
private theorem header0_lex : header0.1.toList.foldl step initial =
    completed header0.2 := by decide +kernel
private theorem header1_lex : header1.1.toList.foldl step initial =
    completed header1.2 := by decide +kernel
private def pieces : List (String × List Token) := header0 :: header1 :: Source.lookupPieces

def source : String := String.join (pieces.map Prod.fst)
def tokens : List Token := pieces.flatMap Prod.snd
/-- Source qualification is retained in the syntax. Parameter value loading
uses the existing unqualified runtime type component; const typing and the
native byte ABI remain separate from this physical operation interpreter. -/
def function : CQualifiedFunction :=
  ⟨Source.entryType, "bindings_frame_table_lookup".toList,
    [⟨⟨indexType, indexName⟩, true⟩, ⟨⟨Source.uint32, handleName⟩, false⟩], Source.lookupBody⟩

theorem lexed : lex source.toList = .ok tokens := by
  apply lex_completed_string_pieces
  simp only [pieces, Source.lookupPieces, List.forall_cons]
  exact ⟨header0_lex, header1_lex, Source.lookupPiece0_lex, Source.lookupPiece1_lex, Source.lookupPiece2_lex, Source.lookupPiece3_lex, Source.lookupPiece4_lex, Source.lookupPiece5_lex, Source.lookupPiece6_lex, Source.lookupPiece7_lex, Source.lookupPiece8_lex, Source.lookupPiece9_lex, Source.lookupPiece10_lex, Source.lookupPiece11_lex, Source.lookupPiece12_lex, Source.lookupPiece13_lex, trivial⟩

theorem parsed : qualifiedFunctionText? types source.toList = some function :=
  function_text_using_of_parts (qualifiedParameter? types) types source.toList
    tokens function lexed (by rfl)


def invoke (decode : UInt32 → CProg CVal UInt32) (allowance : Nat)
    (region : AutomaticRegion Context) (context : Context) (arguments : List CallArgument) :
    CProg CVal (ReadBlock.Result Context) :=
  match qualifiedFunctionText? types source.toList with
  | none => CProg.undefined
  | some fn => parameters (SourceRead.profile decode) region context fn.unqualified.parameters
      arguments fun localContext => executeScopedWith (SourceRead.services decode)
        SourceRead.layout allowance 12 localContext fn.body

private theorem scalar_parameter (p : Profile) (region : AutomaticRegion Context)
    (context : Context) (type : CType) (name : Name) (value converted : CVal)
    (notRecord : p.recordExtent type = none)
    (conversion : scalarInitialValue p type value = pure converted)
    (body : Context → CProg CVal (ReadBlock.Result Context)) :
    parameter p region context type name (.scalar value) body =
      (body (Function.update context name (some (.scalar type (some converted)))) >>= fun result =>
        pure (ObjectBindings.restore name (context name) result)) := by
  simp only [parameter, notRecord, conversion, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]


/-- Actual source parameters reach the parsed body and both shadowed scalar
locals are restored after it. No selected directory result is supplied. -/
theorem invoke_keeps_source_operations (decode : UInt32 → CProg CVal UInt32)
    (allowance : Nat) (region : AutomaticRegion Context) (context : Context)
    (directory : Ptr) (handle : UInt32) :
    invoke decode allowance region context [.scalar (.ptr (some directory)), .scalar (.u32 handle)] =
      (lookupProgram decode directory handle allowance >>= fun result =>
        pure (result.mapContext (fun _ => context))) := by
  rw [invoke, parsed]
  change parameter (SourceRead.profile decode) region context indexType indexName
    (.scalar (.ptr (some directory))) (fun withIndex =>
      parameter (SourceRead.profile decode) region withIndex Source.uint32 handleName
        (.scalar (.u32 handle)) (fun withHandle =>
          executeScopedWith (SourceRead.services decode) SourceRead.layout allowance 12
            withHandle Source.lookupBody)) = _
  rw [scalar_parameter _ _ _ _ _ _ _ (by rfl) (by rfl)]
  rw [scalar_parameter _ _ _ _ _ _ _ (by rfl) (by rfl)]
  let withIndex := Function.update context indexName
    (some (.scalar indexType (some (.ptr (some directory)))))
  let withHandle := Function.update withIndex handleName
    (some (.scalar Source.uint32 (some (.u32 handle))))
  have indexBound : withHandle "index".toList =
      SourceRead.scalar indexType (.ptr (some directory)) := by
    simp only [withHandle, withIndex, indexName, handleName,
      Function.update_of_ne (by decide : "index".toList ≠ "handle".toList),
      Function.update_self, SourceRead.scalar]
  have handleBound : withHandle "handle".toList =
      SourceRead.scalar Source.uint32 (.u32 handle) := Function.update_self _ _ _
  have body := actual_lookup_body decode withHandle directory indexType handle allowance
    indexBound handleBound
  change ((executeScopedWith (SourceRead.services decode) SourceRead.layout allowance 12
      withHandle Source.lookupBody >>= fun result =>
        pure (ObjectBindings.restore handleName (withIndex handleName) result)) >>= fun result =>
          pure (ObjectBindings.restore indexName (context indexName) result)) = _
  rw [body]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  apply congrArg (fun next : ReadBlock.Result Unit → CProg CVal (ReadBlock.Result Context) =>
    lookupProgram decode directory handle allowance >>= next)
  funext result
  cases result with
  | exhausted => rfl
  | finished flow =>
    cases flow <;> simp only [ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext,
      ObjectBindings.restore, withHandle, withIndex, Function.update_idem,
      Function.update_eq_self]

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Effectful.LookupCall


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings
open ReadBlock (Result Flow)
open DirectoryProbe

abbrev read (region : AutomaticRegion Context) (following : Calls) (context : Context) :=
  ObjectBindings.read (profile region following) SourceRead.layout context

theorem read_identity (region : AutomaticRegion Context) (following : Calls)
    (context : Context) (sourceAddress : Ptr)
    (bound : context RefArgument.refName = some (.object RefArgument.refType sourceAddress)) :
    read region following context Source.identity =
      (CProg.loadU32 sourceAddress >>= fun identity => pure (.u32 identity)) := by
  have located := capture_place region following SourceRead.layout context sourceAddress bound
  have descriptor :
      (ObjectBindings.objects (profile region following) context).fieldLayout SourceRead.layout
          (Source.id "ref") false "identity".toList = some ⟨0, .word⟩ := by
    simp only [ObjectBindings.objects, ObjectReads.fieldLayout, Option.map_some,
      ObjectBindings.fieldLayouts, ScalarBytes.typeOf?, ObjectBindings.types,
      Source.id, show "ref".toList = RefArgument.refName from rfl, bound,
      Bool.false_eq_true, ↓reduceIte, profile]
    rfl
  change (placeWithNames (captureNames region following context)
      (profile region following).values SourceRead.layout (.identifier RefArgument.refName)
      (ObjectBindings.objects (profile region following) context) >>= fun address =>
      field ((ObjectBindings.objects (profile region following) context).fieldLayout SourceRead.layout
        (Source.id "ref") false) (.ptr (some address)) "identity".toList) = _
  rw [located]
  simp only [Prog.pure_eq, field, pointer, descriptor]
  rfl

private theorem read_named (region : AutomaticRegion Context) (following : Calls)
    (context : Context) (name : Name) (type : CType) (value : CVal)
    (bound : context name = some (.scalar type (some value))) :
    read region following context (.identifier name) = pure value :=
  read_scalar region following SourceRead.layout context name type value bound

theorem scalar_call_one (region : AutomaticRegion Context) (following : Calls)
    (context : Context) (name : Name) (argument : CExpr) (different : name ≠ helperName) :
    read region following context (.call name [argument]) =
      (read region following context argument >>= fun value => following name [value]) := by
  unfold read ObjectBindings.read
  rw [absent_argument_call_preserves_scalar_path _ _ _ _ _ _ (by
    simp only [ObjectBindings.objects, profile, different, if_false])]
  rw [arguments_scalar_cons, argumentsWithNames.eq_def]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl

theorem scalar_call_two (region : AutomaticRegion Context) (following : Calls)
    (context : Context) (name : Name) (left right : CExpr) (different : name ≠ helperName) :
    read region following context (.call name [left, right]) =
      (read region following context left >>= fun first =>
        read region following context right >>= fun second => following name [first, second]) := by
  unfold read ObjectBindings.read
  rw [absent_argument_call_preserves_scalar_path _ _ _ _ _ _ (by
    simp only [ObjectBindings.objects, profile, different, if_false])]
  rw [arguments_scalar_cons, arguments_scalar_cons, argumentsWithNames.eq_def]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl

theorem read_lookup_initializer (region : AutomaticRegion Context) (following : Calls)
    (context : Context) (index : Option Ptr) (sourceAddress : Ptr)
    (indexBound : context indexName = some (.scalar indexType (some (.ptr index))))
    (refBound : context RefArgument.refName = some (.object RefArgument.refType sourceAddress)) :
    read region following context
      (.call "bindings_frame_table_lookup".toList
        [Source.id "index", .call "cetta_frame_handle".toList [Source.identity]]) =
      (CProg.loadU32 sourceAddress >>= fun identity =>
        following "cetta_frame_handle".toList [.u32 identity] >>= fun handle =>
          following "bindings_frame_table_lookup".toList [.ptr index, handle]) := by
  have indexRead : read region following context (Source.id "index") = pure (.ptr index) :=
    read_named region following context indexName indexType (.ptr index) indexBound
  rw [scalar_call_two _ _ _ _ _ _ (by decide), indexRead,
    scalar_call_one _ _ _ _ _ (by decide), read_identity _ _ _ _ refBound]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

/-- Actual final short-circuit check reloads the complete epoch and original
Ref field. A helper with effects cannot replace these loads by a saved pure
codec value. -/
def finalRead (entry : Option Ptr) (sourceAddress : Ptr) : CProg CVal CVal := do
  let isNull ← CProg.ptrEq entry none
  if isNull then pure (.ptr none) else
    match entry with
    | none => CProg.undefined
    | some address =>
      let observed ← CProg.loadU32 address
      let requested ← CProg.loadU32 sourceAddress
      pure (.ptr (if observed == requested then some address else none))

def epochReadProgram : Option Ptr → CProg CVal CVal
  | none => CProg.undefined
  | some address => CProg.loadU32 address >>= fun value => pure (.u32 value)

theorem final_expression_keeps_epoch_reads (region : AutomaticRegion Context) (following : Calls)
    (context : Context) (entry : Option Ptr) (sourceAddress : Ptr)
    (entryBound : context "entry".toList = some (.scalar Source.entryType (some (.ptr entry))))
    (refBound : context RefArgument.refName = some (.object RefArgument.refType sourceAddress)) :
    read region following context
      (.conditional (.binary .and (Source.id "entry")
        (.binary .eq (Source.field "entry" "epoch") Source.identity)) (Source.id "entry") .null) =
      finalRead entry sourceAddress := by
  have entryRead : read region following context (Source.id "entry") = pure (.ptr entry) :=
    read_named _ _ _ _ _ _ entryBound
  have epochRead : read region following context (Source.field "entry" "epoch") =
      epochReadProgram entry := by
    have descriptor :
        (ObjectBindings.objects (profile region following) context).fieldLayout SourceRead.layout
          (Source.id "entry") true "epoch".toList = some ⟨0, .word⟩ := by
      simp only [ObjectBindings.objects, ObjectReads.fieldLayout, Option.map_some,
        ObjectBindings.fieldLayouts, ScalarBytes.typeOf?, ObjectBindings.types,
        Source.id, entryBound, ↓reduceIte, profile]
      rfl
    change (read region following context (Source.id "entry") >>= fun value =>
      field ((ObjectBindings.objects (profile region following) context).fieldLayout SourceRead.layout
        (Source.id "entry") true) value "epoch".toList) = _
    rw [entryRead]
    cases entry <;>
      simp only [epochReadProgram, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, field, pointer, descriptor, ptr_add_zero]
  change ((read region following context (Source.id "entry") >>= fun first =>
    truth first >>= fun left => if left then
      read region following context (.binary .eq (Source.field "entry" "epoch") Source.identity)
        >>= fun second => truth second >>= fun right => pure (.bool right)
    else pure (.bool false)) >>= fun condition => truth condition >>= fun selected =>
      if selected then read region following context (Source.id "entry") else pure (.ptr none)) = _
  rw [entryRead]
  simp only [truth, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  unfold finalRead
  apply congrArg (fun next : Bool → CProg CVal CVal => CProg.ptrEq entry none >>= next)
  funext isNull
  cases isNull with
  | true => rfl
  | false =>
    simp only [Bool.not_false, if_true]
    have equalityRead : read region following context
        (.binary .eq (Source.field "entry" "epoch") Source.identity) =
        (read region following context (Source.field "entry" "epoch") >>= fun left =>
          read region following context Source.identity >>= fun right => binary .eq left right) := by
      rfl
    rw [equalityRead, epochRead, read_identity _ _ _ _ refBound]
    cases entry with
    | none =>
      simp only [epochReadProgram, Bool.false_eq_true, if_false,
        ← Prog.bind_eq, ReadExpressions.undefined_bind]
    | some address =>
      simp only [epochReadProgram, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
        binary, equal, ReadExpressions.scalar, ScalarRead.equal?, resolved]
      apply congrArg (fun next : UInt32 → CProg CVal CVal => CProg.loadU32 address >>= next)
      funext observed
      apply congrArg (fun next : UInt32 → CProg CVal CVal => CProg.loadU32 sourceAddress >>= next)
      funext requested
      split <;> rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings
open ReadBlock (Result Flow)
open DirectoryProbe

def lookupInitializer : CExpr := .call "bindings_frame_table_lookup".toList
  [Source.id "index", .call "cetta_frame_handle".toList [Source.identity]]
def finalExpression : CExpr := .conditional (.binary .and (Source.id "entry")
  (.binary .eq (Source.field "entry" "epoch") Source.identity)) (Source.id "entry") .null

def afterGuard (following : Calls) (index : Option Ptr) (sourceAddress : Ptr) : CProg CVal CVal := do
  let identity ← CProg.loadU32 sourceAddress
  let handle ← following "cetta_frame_handle".toList [.u32 identity]
  let value ← following "bindings_frame_table_lookup".toList [.ptr index, handle]
  let entry ← pointer value
  finalRead entry sourceAddress

/-- The scalar entry declaration retains the actual helper replies, pointer
conversion and final full-epoch read, then restores its shadowed local. -/
theorem tail_keeps_actual_calls (region : AutomaticRegion Context) (following : Calls)
    (context : Context) (index : Option Ptr) (sourceAddress : Ptr)
    (indexBound : context indexName = some (.scalar indexType (some (.ptr index))))
    (refBound : context RefArgument.refName = some (.object RefArgument.refType sourceAddress))
    (fuel : Nat) :
    executeScopedWith (services region following) SourceRead.layout 0 (fuel + 2) context
      [.declare Source.entryType "entry".toList lookupInitializer,
       .return (some finalExpression)] =
      (afterGuard following index sourceAddress >>= fun value =>
        pure (.finished (.returned context (some value)))) := by
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl,
    scoped_initialized_declaration_keeps_continuation]
  simp only [services, ObjectBindings.services]
  rw [ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow _ _ _ _ _ _ _ (by rfl)]
  have initialRead : ObjectBindings.read (profile region following) SourceRead.layout context
      lookupInitializer =
      (CProg.loadU32 sourceAddress >>= fun identity =>
        following "cetta_frame_handle".toList [.u32 identity] >>= fun handle =>
        following "bindings_frame_table_lookup".toList [.ptr index, handle]) :=
    read_lookup_initializer region following context index sourceAddress indexBound refBound
  rw [initialRead]
  unfold afterGuard
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]
  apply congrArg (fun next : UInt32 → CProg CVal (Result Context) =>
    CProg.loadU32 sourceAddress >>= next)
  funext identity
  apply congrArg (fun next : CVal → CProg CVal (Result Context) =>
    following "cetta_frame_handle".toList [.u32 identity] >>= next)
  funext handle
  apply congrArg (fun next : CVal → CProg CVal (Result Context) =>
    following "bindings_frame_table_lookup".toList [.ptr index, handle] >>= next)
  funext value
  have conversion : scalarInitialValue (profile region following) Source.entryType value =
      (pointer value >>= fun entry => pure (.ptr entry)) := by rfl
  rw [conversion]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  apply congrArg (fun next : Option Ptr → CProg CVal (Result Context) => pointer value >>= next)
  funext entry
  rw [executeScopedWith]
  change ((read region following
    (Function.update context "entry".toList (some (.scalar Source.entryType (some (.ptr entry)))))
      finalExpression >>= fun actual =>
        pure (Result.finished (Flow.returned
          (Function.update context "entry".toList (some (.scalar Source.entryType (some (.ptr entry)))))
          (some actual)))) >>= fun result => pure (ObjectBindings.restore "entry".toList
            (context "entry".toList) result)) = _
  have finalReads : read region following
      (Function.update context "entry".toList (some (.scalar Source.entryType (some (.ptr entry)))))
      finalExpression = finalRead entry sourceAddress :=
    final_expression_keeps_epoch_reads region following
      (Function.update context "entry".toList (some (.scalar Source.entryType (some (.ptr entry)))))
      entry sourceAddress (Function.update_self _ _ _)
      (by simpa only [Function.update_of_ne (by decide : RefArgument.refName ≠ "entry".toList)] using refBound)
  rw [finalReads]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    returned_local_restores_previous_binding]

private theorem null_return (region : AutomaticRegion Context) (following : Calls)
    (context : Context) (fuel : Nat) :
    executeScopedWith (services region following) SourceRead.layout 0 (fuel + 1)
      context Source.nullReturn = pure (.finished (.returned context (some (.ptr none)))) := by
  rfl

/-- The nested Ref helper's operations remain before the lookup. Null index
short-circuits them; a zero Ref returns without decoding or table access. -/
def bodyOperations (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (following : Calls)
    (index : Option Ptr) (sourceAddress : Ptr) : CProg CVal CVal := do
  let isNull ← CProg.ptrEq index none
  if isNull then pure (.ptr none) else
    let captured ← CProg.load sourceAddress
    let address ← enter RefArgument.refName 1
    CProg.store address captured
    let observed ← CProg.loadU32 address
    leave RefArgument.refName address 1
    if observed == 0 then pure (.ptr none) else afterGuard following index sourceAddress

theorem actual_body_keeps_operations (following : Calls) (context : Context)
    (index : Option Ptr) (sourceAddress : Ptr)
    (indexBound : context indexName = some (.scalar indexType (some (.ptr index))))
    (refBound : context RefArgument.refName = some (.object RefArgument.refType sourceAddress))
    (enter : Name → Nat → CProg CVal Ptr) (leave : Name → Ptr → Nat → CProg CVal Unit)
    (fuel : Nat) :
    bodyProgram (AutomaticRegion.bracket enter leave) following SourceRead.layout (fuel + 3) context =
      (bodyOperations enter leave following index sourceAddress >>= fun value =>
        pure (.finished (.returned context (some value)))) := by
  change executeScopedWith _ _ 0 ((fuel + 2) + 1) context
    (.branch entryGuard Source.nullReturn [] ::
      [.declare Source.entryType "entry".toList lookupInitializer,
       .return (some finalExpression)]) = _
  rw [executeScopedWith]
  change (ObjectBindings.read (profile (AutomaticRegion.bracket enter leave) following)
      SourceRead.layout context entryGuard >>= fun actual =>
      truth actual >>= fun selected => executeScopedWith _ _ _ (fuel + 2) context
        (if selected then Source.nullReturn else []) >>= ReadBlock.resume _) = _
  rw [guard_keeps_actual_nested_call following SourceRead.layout context index sourceAddress
    indexBound refBound enter leave]
  unfold bodyOperations
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]
  apply congrArg (fun next : Bool → CProg CVal (Result Context) => CProg.ptrEq index none >>= next)
  funext isNull
  cases isNull with
  | true =>
    simp only [↓reduceIte, truth, Prog.pure_eq, Prog.ret_bind, null_return,
      ReadBlock.resume]
  | false =>
    simp only [Bool.false_eq_true, if_false]
    apply congrArg (fun next : CVal → CProg CVal (Result Context) => CProg.load sourceAddress >>= next)
    funext captured
    simp only [Op.Ret, Prog.ret_bind, Prog.bind_assoc]
    apply congrArg (fun next : Ptr → CProg CVal (Result Context) => enter RefArgument.refName 1 >>= next)
    funext address
    apply congrArg (fun next : Unit → CProg CVal (Result Context) => CProg.store address captured >>= next)
    funext ignored
    apply congrArg (fun next : UInt32 → CProg CVal (Result Context) => CProg.loadU32 address >>= next)
    funext observed
    apply congrArg (fun next : Unit → CProg CVal (Result Context) => leave RefArgument.refName address 1 >>= next)
    funext ignored
    cases (observed == 0) with
    | true =>
      simp only [↓reduceIte, truth, Prog.pure_eq, Prog.ret_bind, null_return,
        ReadBlock.resume]
    | false =>
      simp only [Bool.false_eq_true, if_false, truth, Prog.ret_bind,
        executeScopedWith, Prog.pure_eq, ReadBlock.resume]
      exact tail_keeps_actual_calls (AutomaticRegion.bracket enter leave) following context
        index sourceAddress indexBound refBound fuel

/-- The complete parsed function retains the copied outer Ref parameter,
all nested calls and final epoch reads, then performs outer cleanup before
restoring the shadowed Ref and index bindings. -/
theorem invoke_keeps_actual_body (following : Calls) (context : Context)
    (index : Option Ptr) (identity : UInt32)
    (parameterEnter enter : Name → Nat → CProg CVal Ptr)
    (parameterLeave leave : Name → Ptr → Nat → CProg CVal Unit) (fuel : Nat) :
    invoke (AutomaticRegion.bracket parameterEnter parameterLeave)
      (AutomaticRegion.bracket enter leave) following SourceRead.layout (fuel + 3) context
      [.scalar (.ptr index), .record RefArgument.refType [.u32 identity]] =
      (parameterEnter RefArgument.refName 1 >>= fun sourceAddress =>
        CProg.store sourceAddress (.u32 identity) >>= fun _ =>
        bodyOperations enter leave following index sourceAddress >>= fun value =>
        parameterLeave RefArgument.refName sourceAddress 1 >>= fun _ =>
        pure (.finished (.returned context (some value)))) := by
  rw [actual_two_parameter_entry]
  simp only [AutomaticRegion.bracket, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  apply congrArg (fun next : Ptr → CProg CVal (Result Context) =>
    parameterEnter RefArgument.refName 1 >>= next)
  funext sourceAddress
  apply congrArg (fun next : Unit → CProg CVal (Result Context) =>
    CProg.store sourceAddress (.u32 identity) >>= next)
  funext ignored
  let withIndex := Function.update context indexName (some (.scalar indexType (some (.ptr index))))
  let withRef := Function.update withIndex RefArgument.refName
    (some (.object RefArgument.refType sourceAddress))
  have indexBound : withRef indexName = some (.scalar indexType (some (.ptr index))) := by
    simp only [withRef, withIndex,
      Function.update_of_ne (by decide : indexName ≠ RefArgument.refName), Function.update_self]
  have refBound : withRef RefArgument.refName = some (.object RefArgument.refType sourceAddress) :=
    Function.update_self _ _ _
  have body := actual_body_keeps_operations following withRef index sourceAddress
    indexBound refBound enter leave fuel
  change (bodyProgram (AutomaticRegion.bracket enter leave) following SourceRead.layout
      (fuel + 3) withRef >>= fun result =>
      parameterLeave RefArgument.refName sourceAddress 1 >>= fun _ =>
      pure (ObjectBindings.restore indexName (context indexName)
        (ObjectBindings.restore RefArgument.refName (context RefArgument.refName) result))) = _
  rw [body]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  apply congrArg (fun next : CVal → CProg CVal (Result Context) =>
    bodyOperations enter leave following index sourceAddress >>= next)
  funext value
  apply congrArg (fun next : Unit → CProg CVal (Result Context) =>
    parameterLeave RefArgument.refName sourceAddress 1 >>= next)
  funext ignored
  have oldRef : withIndex RefArgument.refName = context RefArgument.refName := by
    exact Function.update_of_ne (by decide : RefArgument.refName ≠ indexName) _ _
  rw [← oldRef]
  change (pure (ObjectBindings.restore indexName (context indexName)
    (ObjectBindings.restore RefArgument.refName (withIndex RefArgument.refName)
      (.finished (.returned
        (Function.update withIndex RefArgument.refName
          (some (.object RefArgument.refType sourceAddress))) (some value))))) :
      CProg CVal (Result Context)) = _
  rw [returned_local_restores_previous_binding]
  exact congrArg (fun result : Result Context => (pure result : CProg CVal (Result Context)))
    (returned_local_restores_previous_binding context indexName
      (.scalar indexType (some (.ptr index))) (some value))

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Effectful
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.IncrementalConformance

/-- Mapping a retained row to its physical address preserves the probe's
occurrence order and vacancy. No native lookup result is assumed. -/
theorem probe_map_values {Key Value Target : Type*} [DecidableEq Key]
    (mapValue : Value → Target) (key : Key) (cells : InternProbe.Cells Key Value) :
    InternProbe.probe key (cells.map (Option.map fun pair => (pair.1, mapValue pair.2))) =
      ((InternProbe.probe key cells).1.map mapValue, (InternProbe.probe key cells).2) := by
  induction cells with
  | nil => rfl
  | cons cell tail ih =>
    cases cell with
    | none => rfl
    | some pair =>
      rcases pair with ⟨stored, value⟩
      by_cases same : key = stored
      · simp only [List.map_cons, Option.map_some, InternProbe.probe, same, ↓reduceIte]
      · simp only [List.map_cons, Option.map_some, InternProbe.probe, same, ↓reduceIte, ih]

theorem sequence_map_values {capacity : Nat} {Key Value Target : Type*}
    (mapValue : Value → Target) (table : Fin capacity → Option (Key × Value))
    (start : Fin capacity) :
    sequence (fun slot => (table slot).map fun pair => (pair.1, mapValue pair.2)) start =
      (sequence table start).map (Option.map fun pair => (pair.1, mapValue pair.2)) := by
  simp only [sequence, List.map_ofFn, Function.comp_def]

def physicalRows {capacity : Nat} (directory : DirectoryReadback)
    (rows : Fin capacity → Option (Fin (frameKeys directory).length))
    (address : Fin (frameKeys directory).length → Ptr) : Fin capacity → Option (Nat × Ptr) :=
  fun slot => (keyed (frameKeys directory) rows slot).map fun pair => (pair.1, address pair.2)

theorem physicalRows_probe {capacity : Nat} (directory : DirectoryReadback)
    (rows : Fin capacity → Option (Fin (frameKeys directory).length))
    (address : Fin (frameKeys directory).length → Ptr) (start : Fin capacity) (key : Nat) :
    (InternProbe.probe key (sequence (physicalRows directory rows address) start)).1 =
      ((InternProbe.probe key (sequence (keyed (frameKeys directory) rows) start)).1.map address) := by
  unfold physicalRows
  rw [sequence_map_values, probe_map_values]

theorem physicalRows_half_load {capacity : Nat} (directory : DirectoryReadback)
    (rows : Fin capacity → Option (Fin (frameKeys directory).length))
    (address : Fin (frameKeys directory).length → Ptr) :
    (List.ofFn (physicalRows directory rows address)).countP Option.isSome =
      (List.ofFn rows).countP Option.isSome := by
  have same : (List.ofFn (physicalRows directory rows address)).map Option.isSome =
      (List.ofFn rows).map Option.isSome := by
    simp only [List.map_ofFn]
    congr 1
    funext slot
    cases selected : rows slot <;> simp only [Function.comp_def, physicalRows, keyed, selected,
      Option.map_none, Option.map_some, Option.isSome_none, Option.isSome_some]
  have counted := congrArg (List.countP id) same
  simpa only [List.countP_map, Function.comp_def, id_eq] using counted

/-- The public reference observer remains the existing full-epoch directory
observer. Mapping rows to addresses happens only after that comparison. -/
theorem findRef_physical_result {capacity : Nat} (directory : DirectoryReadback)
    (rows : Fin capacity → Option (Fin (frameKeys directory).length))
    (address : Fin (frameKeys directory).length → Ptr) (start : Nat → Fin capacity)
    (reference : UInt32) :
    (findRef directory rows start reference).map address =
      if reference = 0 then none else
        (InternProbe.probe (unpackHandle reference.toNat)
          (sequence (keyed (frameKeys directory) rows) (start (unpackHandle reference.toNat)))).1.bind
          (fun row => if frameEpoch (frameAtRow directory row) = reference
            then some (address row) else none) := by
  unfold findRef
  split
  · rfl
  · simp only [Option.map_bind]
    congr 1
    funext row
    dsimp only [Function.comp_def]
    split <;> rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Effectful


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings
open ReadBlock (Result Flow)
open DirectoryProbe

/-- The catalogue executes the parsed identity and directory functions.
Its source admission covers their declared scalar arguments; no decoded key,
selected pointer or completed lookup outcome is supplied by a callback. -/
def actualCalls (helperAllowance lookupAllowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr) (leave : Name → Ptr → Nat → CProg CVal Unit)
    (callee : Context) (lookupRegion : AutomaticRegion Context) : Calls := fun name arguments =>
  if name = "cetta_frame_handle".toList then
    match arguments with
    | [.u32 identity] => IdentityWrapper.handleCall helperAllowance enter leave callee identity
        >>= fun handle => pure (.u32 handle)
    | _ => CProg.undefined
  else if name = "bindings_frame_table_lookup".toList then
    match arguments with
    | [.ptr directory, .u32 handle] =>
        Effectful.LookupCall.invoke
          (IdentityWrapper.handleCall helperAllowance enter leave callee)
          lookupAllowance lookupRegion callee [.scalar (.ptr directory), .scalar (.u32 handle)]
            >>= RefArgument.returnedScalar
    | _ => CProg.undefined
  else CProg.undefined

theorem actual_calls_handle (helperAllowance lookupAllowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr) (leave : Name → Ptr → Nat → CProg CVal Unit)
    (callee : Context) (lookupRegion : AutomaticRegion Context) (identity : UInt32) :
    actualCalls helperAllowance lookupAllowance enter leave callee lookupRegion
        "cetta_frame_handle".toList [.u32 identity] =
      (IdentityWrapper.handleCall helperAllowance enter leave callee identity >>=
        fun handle => pure (.u32 handle)) := by
  simp only [actualCalls, ↓reduceIte]

theorem actual_calls_lookup (helperAllowance lookupAllowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr) (leave : Name → Ptr → Nat → CProg CVal Unit)
    (callee : Context) (lookupRegion : AutomaticRegion Context) (directory : Ptr) (handle : UInt32) :
    actualCalls helperAllowance lookupAllowance enter leave callee lookupRegion
        "bindings_frame_table_lookup".toList [.ptr (some directory), .u32 handle] =
      (SourceRead.lookupProgram (IdentityWrapper.handleCall helperAllowance enter leave callee)
        directory handle lookupAllowance >>= fun result =>
          RefArgument.returnedScalar (result.mapContext (fun _ => callee))) := by
  rw [actualCalls]
  simp only [show "bindings_frame_table_lookup".toList ≠ "cetta_frame_handle".toList by decide,
    if_false, if_true]
  rw [Effectful.LookupCall.invoke_keeps_source_operations]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

/-- The actual source continuation first decodes its own copied Ref through
an effectful helper, then invokes the full parsed lookup, then reloads the
selected epoch and copied Ref. -/
theorem after_guard_actual_helpers (helperAllowance lookupAllowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr) (leave : Name → Ptr → Nat → CProg CVal Unit)
    (callee : Context) (lookupRegion : AutomaticRegion Context)
    (directory sourceAddress : Ptr) :
    afterGuard (actualCalls helperAllowance lookupAllowance enter leave callee lookupRegion)
        (some directory) sourceAddress =
      (CProg.loadU32 sourceAddress >>= fun identity =>
        IdentityWrapper.handleCall helperAllowance enter leave callee identity >>= fun handle =>
        SourceRead.lookupProgram (IdentityWrapper.handleCall helperAllowance enter leave callee)
          directory handle lookupAllowance >>= fun result =>
        RefArgument.returnedScalar (result.mapContext (fun _ => callee)) >>= fun value =>
        pointer value >>= fun entry => finalRead entry sourceAddress) := by
  unfold afterGuard
  apply congrArg (fun next : UInt32 → CProg CVal CVal => CProg.loadU32 sourceAddress >>= next)
  funext identity
  rw [actual_calls_handle]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  apply congrArg (fun next : UInt32 → CProg CVal CVal =>
    IdentityWrapper.handleCall helperAllowance enter leave callee identity >>= next)
  funext handle
  rw [actual_calls_lookup]
  simp only [Prog.bind_eq, Prog.bind_assoc]

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.IncrementalConformance
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings
open ReadBlock (Result Flow)
open DirectoryProbe

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- The final full-epoch test is established from the reached physical
inventory. It reads both cells, preserves the heap, and can reject a selected
handle whose generation is stale. -/
theorem final_read_owned_row (directory : DirectoryReadback)
    (address : Fin (frameKeys directory).length → Ptr)
    (selected : Option (Fin (frameKeys directory).length))
    (sourceAddress : Ptr) (identity : UInt32) (pre : Heap L → Prop)
    (referenceRead : ∀ heap, pre heap → Reads sourceAddress (.u32 identity) heap)
    (rowsRead : ∀ heap, pre heap → ∀ row,
      ValidAt (address row) heap ∧ Reads (address row) (.u32 (frameEpoch (frameAtRow directory row))) heap) :
    CTriple pre (finalRead (selected.map address) sourceAddress)
      (fun value heap => pre heap ∧ value = .ptr
        (selected.bind fun row => if frameEpoch (frameAtRow directory row) = identity
          then some (address row) else none)) := by
  intro heap held
  change (finalRead (selected.map address) sourceAddress).wp act _ heap
  cases selected with
  | none =>
    simp only [Option.map_none]
    rw [finalRead.eq_def, wp_bind']
    apply wp_ptrEq (by trivial) (by trivial)
    simp only [decide_true, ↓reduceIte, wp_pure, Option.bind_none]
    exact ⟨held, trivial⟩
  | some row =>
    simp only [Option.map_some]
    rw [finalRead.eq_def, wp_bind']
    apply wp_ptrEq (p := some (address row)) (q := none)
      (show ValidOpt heap (some (address row)) from (rowsRead heap held row).1) (by trivial)
    simp only [Option.some_ne_none, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [wp_bind']
    apply Effectful.loadU32_at (rowsRead heap held row).2
    rw [wp_bind']
    apply Effectful.loadU32_at (referenceRead heap held)
    simp only [wp_pure, Option.bind_some, beq_iff_eq]
    exact ⟨held, trivial⟩

/-- Nested by-value validation uses a real parameter copy. Only automatic
entry/exit ownership is supplied; the zero result comes from its typed load. -/
theorem validation_zero_owned (identity : UInt32)
    (enter : Name → Nat → CProg CVal Ptr) (leave : Name → Ptr → Nat → CProg CVal Unit)
    (pre post : Heap L → Prop) (remainder : Ptr → Heap L → Prop)
    (entry : CTriple pre (enter RefArgument.refName 1)
      (fun address => PointsToAny address ∗ remainder address))
    (exit : ∀ address, CTriple (PointsTo address (.u32 identity) ∗ remainder address)
      (leave RefArgument.refName address 1) (fun _ => post)) :
    CTriple pre
      (enter RefArgument.refName 1 >>= fun address =>
        CProg.store address (.u32 identity) >>= fun _ =>
        CProg.loadU32 address >>= fun observed =>
        leave RefArgument.refName address 1 >>= fun _ => pure (observed == 0))
      (fun zero heap => zero = (identity == 0) ∧ post heap) := by
  have actual := RefArgument.actual_service_owned (fun _ => none) identity enter leave pre post
    remainder entry exit
  have after : CTriple pre
      ((RefArgument.service (AutomaticRegion.bracket enter leave) (fun _ => none)).invoke
        [.record RefArgument.refType [.u32 identity]] >>= fun value =>
          truth value >>= fun valid => pure (!valid))
      (fun zero heap => zero = (identity == 0) ∧ post heap) := by
    refine triple_bind _ actual fun value => ?_
    apply triple_pure
    intro same
    subst value
    simp only [truth, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Bool.not_not]
    exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
      (triple_ret act (identity == 0)
        (fun zero heap => zero = (identity == 0) ∧ post heap))
  rw [RefArgument.actual_service_bracket] at after
  simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    truth, Bool.not_not] using after

/-- The physical lookup returns addresses of the independent retained rows;
the final comparison is therefore exactly the existing full-epoch observer. -/
theorem after_guard_returns_directory (helperAllowance lookupAllowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr) (leave : Name → Ptr → Nat → CProg CVal Unit)
    (callee : Context) (lookupRegion : AutomaticRegion Context)
    (directory : DirectoryReadback) (directoryAddress sourceAddress : Ptr)
    (identity key mask shift : UInt32) (keyValue : key.toNat = unpackHandle identity.toNat)
    (nonzero : identity ≠ 0) (validShift : shift.toNat < 32)
    (maskShape : mask.toNat = 2 ^ (32 - shift.toNat) - 1)
    (rows : Fin (2 ^ (32 - shift.toNat)) → Option (Fin (frameKeys directory).length))
    (address : Fin (frameKeys directory).length → Ptr)
    (loaded : (List.ofFn rows).countP Option.isSome ≤ 2 ^ (32 - shift.toNat) / 2)
    (enough : 2 ^ (32 - shift.toNat) ≤ lookupAllowance)
    (pre : Heap L → Prop) (remainder : Ptr → Heap L → Prop)
    (entry : CTriple pre (enter "parts".toList 3) (fun address heap =>
      ∃ old : List (Option CVal), old.length = 3 ∧ (Cells address old ∗ remainder address) heap))
    (exit : ∀ address h g m,
      CTriple (IdentityRead.PartsCells address h g m ∗ remainder address)
        (leave "parts".toList address 3) (fun _ => pre))
    (referenceRead : ∀ heap, pre heap → Reads sourceAddress (.u32 identity) heap)
    (rowsRead : ∀ heap, pre heap → ∀ row,
      ValidAt (address row) heap ∧ Reads (address row) (.u32 (frameEpoch (frameAtRow directory row))) heap)
    (inventory : ∀ heap, pre heap → SourceRead.LookupReads directoryAddress mask shift
      (Effectful.physicalRows directory rows address) heap) :
    CTriple pre (afterGuard (actualCalls helperAllowance lookupAllowance enter leave callee lookupRegion)
      (some directoryAddress) sourceAddress)
      (fun value heap => pre heap ∧ value = .ptr
        ((findRef directory rows (fun query => ⟨(home (UInt32.ofNat query) shift).toNat,
          home_within_capacity _ _ validShift⟩) identity).map address)) := by
  intro heap held
  change (afterGuard (actualCalls helperAllowance lookupAllowance enter leave callee lookupRegion)
    (some directoryAddress) sourceAddress).wp act _ heap
  rw [after_guard_actual_helpers, wp_bind']
  apply Effectful.loadU32_at (referenceRead heap held)
  rw [wp_bind']
  refine wp_mono act ?_
    (IdentityWrapper.actual_handle_owned helperAllowance enter leave callee identity pre pre
      remainder entry exit heap held)
  rintro actual reached ⟨decoded, retained⟩
  have sameKey : actual = key := UInt32.toNat.inj (decoded.trans keyValue.symm)
  subst actual
  rw [wp_bind']
  refine wp_mono act ?_
    (Effectful.lookup_returns_inventory helperAllowance enter leave callee directoryAddress
      key mask shift validShift maskShape (Effectful.physicalRows directory rows address)
      (by simpa only [Effectful.physicalRows_half_load] using loaded)
      lookupAllowance enough pre remainder entry exit inventory reached retained)
  rintro result final ⟨kept, rfl⟩
  simp only [ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext,
    RefArgument.returnedScalar, pointer, Prog.pure_eq]
  rw [Effectful.physicalRows_probe]
  have checked := final_read_owned_row directory address
    (InternProbe.probe key.toNat
      (sequence (keyed (frameKeys directory) rows) ⟨(home key shift).toNat,
        home_within_capacity _ _ validShift⟩)).1 sourceAddress identity pre referenceRead rowsRead final kept
  refine wp_mono act ?_ checked
  rintro value after ⟨saved, same⟩
  refine ⟨saved, same.trans ?_⟩
  congr 1
  rw [Effectful.findRef_physical_result, if_neg nonzero]
  simp only [← keyValue, UInt32.ofNat_toNat]

/-- The complete body observer is earned from actual validation, decoding,
lookup and final epoch loads. Primitive region contracts preserve the reached
inventory; no source-body result is assumed. -/
theorem body_operations_returns_directory (helperAllowance lookupAllowance : Nat)
    (enter : Name → Nat → CProg CVal Ptr) (leave : Name → Ptr → Nat → CProg CVal Unit)
    (callee : Context) (lookupRegion : AutomaticRegion Context)
    (directory : DirectoryReadback) (directoryAddress sourceAddress : Ptr)
    (identity key mask shift : UInt32) (keyValue : key.toNat = unpackHandle identity.toNat)
    (validShift : shift.toNat < 32)
    (maskShape : mask.toNat = 2 ^ (32 - shift.toNat) - 1)
    (rows : Fin (2 ^ (32 - shift.toNat)) → Option (Fin (frameKeys directory).length))
    (address : Fin (frameKeys directory).length → Ptr)
    (loaded : (List.ofFn rows).countP Option.isSome ≤ 2 ^ (32 - shift.toNat) / 2)
    (enough : 2 ^ (32 - shift.toNat) ≤ lookupAllowance)
    (pre : Heap L → Prop) (remainder : Ptr → Heap L → Prop)
    (entry : CTriple pre (enter "parts".toList 3) (fun address heap =>
      ∃ old : List (Option CVal), old.length = 3 ∧ (Cells address old ∗ remainder address) heap))
    (exit : ∀ address h g m,
      CTriple (IdentityRead.PartsCells address h g m ∗ remainder address)
        (leave "parts".toList address 3) (fun _ => pre))
    (refRemainder : Ptr → Heap L → Prop)
    (refEntry : CTriple pre (enter RefArgument.refName 1)
      (fun address => PointsToAny address ∗ refRemainder address))
    (refExit : ∀ address, CTriple (PointsTo address (.u32 identity) ∗ refRemainder address)
      (leave RefArgument.refName address 1) (fun _ => pre))
    (validDirectory : ∀ heap, pre heap → ValidAt directoryAddress heap)
    (referenceRead : ∀ heap, pre heap → Reads sourceAddress (.u32 identity) heap)
    (rowsRead : ∀ heap, pre heap → ∀ row,
      ValidAt (address row) heap ∧ Reads (address row) (.u32 (frameEpoch (frameAtRow directory row))) heap)
    (inventory : ∀ heap, pre heap → SourceRead.LookupReads directoryAddress mask shift
      (Effectful.physicalRows directory rows address) heap) :
    CTriple pre (bodyOperations enter leave
      (actualCalls helperAllowance lookupAllowance enter leave callee lookupRegion)
      (some directoryAddress) sourceAddress)
      (fun value heap => pre heap ∧ value = .ptr
        ((findRef directory rows (fun query => ⟨(home (UInt32.ofNat query) shift).toNat,
          home_within_capacity _ _ validShift⟩) identity).map address)) := by
  intro heap held
  change (bodyOperations enter leave
    (actualCalls helperAllowance lookupAllowance enter leave callee lookupRegion)
    (some directoryAddress) sourceAddress).wp act _ heap
  rw [bodyOperations, wp_bind']
  apply wp_ptrEq (p := some directoryAddress) (q := none)
    (show ValidOpt heap (some directoryAddress) from validDirectory heap held) (by trivial)
  simp only [Option.some_ne_none, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply wp_load held ⟨referenceRead⟩
  have validated := validation_zero_owned identity enter leave pre pre refRemainder refEntry refExit
  have continued : CTriple pre
      ((enter RefArgument.refName 1 >>= fun temporary =>
        CProg.store temporary (.u32 identity) >>= fun _ =>
        CProg.loadU32 temporary >>= fun observed =>
        leave RefArgument.refName temporary 1 >>= fun _ => pure (observed == 0)) >>= fun zero =>
          if zero then pure (.ptr none) else
            afterGuard (actualCalls helperAllowance lookupAllowance enter leave callee lookupRegion)
              (some directoryAddress) sourceAddress)
      (fun value heap => pre heap ∧ value = .ptr
        ((findRef directory rows (fun query => ⟨(home (UInt32.ofNat query) shift).toNat,
          home_within_capacity _ _ validShift⟩) identity).map address)) := by
    refine triple_bind _ validated fun zero => ?_
    apply triple_pure
    intro same
    subst zero
    by_cases isZero : identity = 0
    · simp only [isZero, beq_self_eq_true, ↓reduceIte, findRef, Option.map_none]
      exact triple_pre _ (fun _ owned => ⟨owned, rfl⟩)
        (triple_ret act (CVal.ptr none) (fun value heap => pre heap ∧ value = CVal.ptr none))
    · simp only [show (identity == 0) = false from beq_eq_false_iff_ne.mpr isZero,
        Bool.false_eq_true, if_false]
      exact after_guard_returns_directory helperAllowance lookupAllowance enter leave callee
        lookupRegion directory directoryAddress sourceAddress identity key mask shift keyValue
        isZero validShift maskShape rows address loaded enough pre remainder entry exit
        referenceRead rowsRead inventory
  simpa only [Prog.wp, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind] using continued heap held

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.IncrementalConformance
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings
open ReadBlock (Result Flow)
open DirectoryProbe

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Complete source-function correctness, including its copied by-value Ref
and lexical cleanup. Assumptions describe primitive automatic-region ownership,
physical cells and the independent table inventory. The call and its result
are constructed by the parsed functions rather than supplied as assumptions. -/
theorem actual_find_ref_owned (helperAllowance lookupAllowance controlAllowance : Nat)
    (enter parameterEnter : Name → Nat → CProg CVal Ptr)
    (leave parameterLeave : Name → Ptr → Nat → CProg CVal Unit)
    (callee caller : Context) (lookupRegion : AutomaticRegion Context)
    (directory : DirectoryReadback) (directoryAddress : Ptr)
    (identity mask shift : UInt32) (validShift : shift.toNat < 32)
    (maskShape : mask.toNat = 2 ^ (32 - shift.toNat) - 1)
    (rows : Fin (2 ^ (32 - shift.toNat)) → Option (Fin (frameKeys directory).length))
    (address : Fin (frameKeys directory).length → Ptr)
    (loaded : (List.ofFn rows).countP Option.isSome ≤ 2 ^ (32 - shift.toNat) / 2)
    (enough : 2 ^ (32 - shift.toNat) ≤ lookupAllowance)
    (pre post : Heap L → Prop) (saved : Ptr → Heap L → Prop)
    (helperRemainder refRemainder : Ptr → Ptr → Heap L → Prop)
    (parameterEntry : CTriple pre (parameterEnter RefArgument.refName 1)
      (fun source => PointsToAny source ∗ saved source))
    (parameterExit : ∀ source,
      CTriple (PointsTo source (.u32 identity) ∗ saved source)
        (parameterLeave RefArgument.refName source 1) (fun _ => post))
    (entry : ∀ source,
      CTriple (PointsTo source (.u32 identity) ∗ saved source) (enter "parts".toList 3)
        (fun temporary heap => ∃ old : List (Option CVal), old.length = 3 ∧
          (Cells temporary old ∗ helperRemainder source temporary) heap))
    (exit : ∀ source temporary h g m,
      CTriple (IdentityRead.PartsCells temporary h g m ∗ helperRemainder source temporary)
        (leave "parts".toList temporary 3)
        (fun _ => PointsTo source (.u32 identity) ∗ saved source))
    (refEntry : ∀ source,
      CTriple (PointsTo source (.u32 identity) ∗ saved source) (enter RefArgument.refName 1)
        (fun temporary => PointsToAny temporary ∗ refRemainder source temporary))
    (refExit : ∀ source temporary,
      CTriple (PointsTo temporary (.u32 identity) ∗ refRemainder source temporary)
        (leave RefArgument.refName temporary 1)
        (fun _ => PointsTo source (.u32 identity) ∗ saved source))
    (validDirectory : ∀ source heap, (PointsTo source (.u32 identity) ∗ saved source) heap →
      ValidAt directoryAddress heap)
    (rowsRead : ∀ source heap, (PointsTo source (.u32 identity) ∗ saved source) heap → ∀ row,
      ValidAt (address row) heap ∧ Reads (address row) (.u32 (frameEpoch (frameAtRow directory row))) heap)
    (inventory : ∀ source heap, (PointsTo source (.u32 identity) ∗ saved source) heap →
      SourceRead.LookupReads directoryAddress mask shift (Effectful.physicalRows directory rows address) heap) :
    CTriple pre
      (invoke (AutomaticRegion.bracket parameterEnter parameterLeave)
        (AutomaticRegion.bracket enter leave)
        (actualCalls helperAllowance lookupAllowance enter leave callee lookupRegion)
        SourceRead.layout (controlAllowance + 3) caller
        [.scalar (.ptr (some directoryAddress)), .record RefArgument.refType [.u32 identity]])
      (fun result heap => post heap ∧ result = .finished (.returned caller (some (.ptr
        ((findRef directory rows (fun query => ⟨(home (UInt32.ofNat query) shift).toNat,
          home_within_capacity _ _ validShift⟩) identity).map address))))) := by
  rw [invoke_keeps_actual_body]
  refine triple_bind _ parameterEntry fun source => ?_
  refine triple_bind _ (triple_frame act act_local (store_spec source (.u32 identity))
    (saved source)) fun _ => ?_
  have keyValue : (UInt32.ofNat (unpackHandle identity.toNat)).toNat = unpackHandle identity.toNat := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (SourceRead.unpackHandle_fits_uint32 _)]
  have body := body_operations_returns_directory helperAllowance lookupAllowance enter leave callee
    lookupRegion directory directoryAddress source identity (UInt32.ofNat (unpackHandle identity.toNat))
    mask shift keyValue validShift maskShape rows address loaded enough
    (PointsTo source (.u32 identity) ∗ saved source) (helperRemainder source)
    (entry source) (exit source) (refRemainder source) (refEntry source) (refExit source)
    (validDirectory source) (fun _ held => read_of_pointsTo held) (rowsRead source) (inventory source)
  refine triple_bind _ body fun value => ?_
  refine triple_pre _ (P := fun heap =>
    value = .ptr ((findRef directory rows
      (fun query => ⟨(home (UInt32.ofNat query) shift).toNat,
        home_within_capacity _ _ validShift⟩) identity).map address) ∧
      (PointsTo source (.u32 identity) ∗ saved source) heap)
    (fun _ held => ⟨held.2, held.1⟩) ?_
  apply triple_pure
  intro same
  subst value
  refine triple_bind _ (parameterExit source) fun _ => ?_
  exact triple_pre _ (fun _ held => ⟨held, rfl⟩)
    (triple_ret act (Result.finished (Flow.returned caller (some (CVal.ptr
      ((findRef directory rows (fun query => ⟨(home (UInt32.ofNat query) shift).toNat,
        home_within_capacity _ _ validShift⟩) identity).map address))))) _)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.IncrementalConformance
open Mettapedia.Machines.CMemory.ProductiveBlocks
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings
open DirectoryProbe

private theorem realized_observation {Answer : Type} (program : CProg CVal Answer)
    (expected : Answer) (pre post : Heap (Excl (Option CVal)) → Prop)
    (contract : CTriple pre program (fun answer heap => post heap ∧ answer = expected))
    (storage : Storage CVal) (owned : pre (heap storage)) :
    (∃ choices fuel final,
      (machine.run fuel (State.mk program storage choices)).2 = .finished (.returned final) ∧
      final.answer = expected ∧ post (heap final.storage) ∧
      ∀ extra, machine.run (fuel + extra) (State.mk program storage choices) =
        machine.run fuel (State.mk program storage choices)) ∧
    (∀ choices fuel final,
      (machine.run fuel (State.mk program storage choices)).2 = .finished (.returned final) →
      final.answer = expected ∧ post (heap final.storage)) := by
  have safe := (contract (heap storage) owned).1
  constructor
  · obtain ⟨answer, after, ran⟩ := exists_runs program (heap storage) safe
    have observed := (contract (heap storage) owned).2 answer after ran
    obtain ⟨choices, fuel, final, answerCorrect, heapCorrect, completed⟩ :=
      source_execution_realized program storage answer after safe ran
    refine ⟨choices, fuel, final, completed, answerCorrect.trans observed.2, ?_, ?_⟩
    · rw [heapCorrect]
      exact observed.1
    · intro extra
      apply machine.run_stable
      intro residual
      rw [completed]
      intro impossible
      cases impossible
  · intro choices fuel final completed
    have observed := (contract (heap storage) owned).2 final.answer (heap final.storage)
      (returned_sound _ _ _ completed)
    exact ⟨observed.2, observed.1⟩

/-- The admitted actual source function has a constructed finite retained
completion. Every completed retained run reflects the independent directory
observer, and extending the completed scheduler budget preserves every receipt
and the full result. Source loop allowance and scheduler suspension are separate. -/
theorem actual_find_ref_retained (helperAllowance lookupAllowance controlAllowance : Nat)
    (enter parameterEnter : Name → Nat → CProg CVal Ptr)
    (leave parameterLeave : Name → Ptr → Nat → CProg CVal Unit)
    (callee caller : Context) (lookupRegion : AutomaticRegion Context)
    (directory : DirectoryReadback) (directoryAddress : Ptr)
    (identity mask shift : UInt32) (validShift : shift.toNat < 32)
    (maskShape : mask.toNat = 2 ^ (32 - shift.toNat) - 1)
    (rows : Fin (2 ^ (32 - shift.toNat)) → Option (Fin (frameKeys directory).length))
    (address : Fin (frameKeys directory).length → Ptr)
    (loaded : (List.ofFn rows).countP Option.isSome ≤ 2 ^ (32 - shift.toNat) / 2)
    (enough : 2 ^ (32 - shift.toNat) ≤ lookupAllowance)
    (pre post : Heap (Excl (Option CVal)) → Prop) (saved : Ptr → Heap (Excl (Option CVal)) → Prop)
    (helperRemainder refRemainder : Ptr → Ptr → Heap (Excl (Option CVal)) → Prop)
    (parameterEntry : CTriple pre (parameterEnter RefArgument.refName 1)
      (fun source => PointsToAny source ∗ saved source))
    (parameterExit : ∀ source,
      CTriple (PointsTo source (.u32 identity) ∗ saved source)
        (parameterLeave RefArgument.refName source 1) (fun _ => post))
    (entry : ∀ source,
      CTriple (PointsTo source (.u32 identity) ∗ saved source) (enter "parts".toList 3)
        (fun temporary heap => ∃ old : List (Option CVal), old.length = 3 ∧
          (Cells temporary old ∗ helperRemainder source temporary) heap))
    (exit : ∀ source temporary h g m,
      CTriple (IdentityRead.PartsCells temporary h g m ∗ helperRemainder source temporary)
        (leave "parts".toList temporary 3)
        (fun _ => PointsTo source (.u32 identity) ∗ saved source))
    (refEntry : ∀ source,
      CTriple (PointsTo source (.u32 identity) ∗ saved source) (enter RefArgument.refName 1)
        (fun temporary => PointsToAny temporary ∗ refRemainder source temporary))
    (refExit : ∀ source temporary,
      CTriple (PointsTo temporary (.u32 identity) ∗ refRemainder source temporary)
        (leave RefArgument.refName temporary 1)
        (fun _ => PointsTo source (.u32 identity) ∗ saved source))
    (validDirectory : ∀ source heap, (PointsTo source (.u32 identity) ∗ saved source) heap →
      ValidAt directoryAddress heap)
    (rowsRead : ∀ source heap, (PointsTo source (.u32 identity) ∗ saved source) heap → ∀ row,
      ValidAt (address row) heap ∧ Reads (address row) (.u32 (frameEpoch (frameAtRow directory row))) heap)
    (inventory : ∀ source heap, (PointsTo source (.u32 identity) ∗ saved source) heap →
      SourceRead.LookupReads directoryAddress mask shift (Effectful.physicalRows directory rows address) heap) (storage : Storage CVal) (owned : pre (heap storage)) :
    let program := invoke (AutomaticRegion.bracket parameterEnter parameterLeave)
        (AutomaticRegion.bracket enter leave)
        (actualCalls helperAllowance lookupAllowance enter leave callee lookupRegion)
        SourceRead.layout (controlAllowance + 3) caller
        [.scalar (.ptr (some directoryAddress)), .record RefArgument.refType [.u32 identity]]
    let expected := ReadBlock.Result.finished (.returned caller (some (.ptr
        ((findRef directory rows (fun query => ⟨(home (UInt32.ofNat query) shift).toNat,
          home_within_capacity _ _ validShift⟩) identity).map address))))
    (∃ choices fuel final,
      (machine.run fuel (State.mk program storage choices)).2 = .finished (.returned final) ∧
      final.answer = expected ∧ post (heap final.storage) ∧
      ∀ extra, machine.run (fuel + extra) (State.mk program storage choices) =
        machine.run fuel (State.mk program storage choices)) ∧
    (∀ choices fuel final,
      (machine.run fuel (State.mk program storage choices)).2 = .finished (.returned final) →
      final.answer = expected ∧ post (heap final.storage)) := by
  exact realized_observation _ _ pre post
    (actual_find_ref_owned helperAllowance lookupAllowance controlAllowance
      enter parameterEnter leave parameterLeave callee caller lookupRegion directory directoryAddress
      identity mask shift validShift maskShape rows address loaded enough pre post saved
      helperRemainder refRemainder parameterEntry parameterExit entry exit refEntry refExit
      validDirectory rowsRead inventory) storage owned

/-- Suspending any prefix retains the actual copied parameter and nested
helper's pending operations. Resumption appends only the saved suffix and
cannot repeat the already recorded loads, stores or cleanup events. -/
theorem actual_find_ref_resume (parameterRegion calleeRegion : AutomaticRegion Context)
    (following : Calls) (allowance : Nat) (caller : Context) (arguments : List CallArgument)
    (storage : Storage CVal) (choices : List AllocationChoice) (first extra : Nat)
    (saved : State CVal (ReadBlock.Result Context)) (events : List (Receipt CVal))
    (paused : machine.run first
      (State.mk (invoke parameterRegion calleeRegion following SourceRead.layout allowance caller arguments)
        storage choices) = (events, .exhausted saved)) :
    machine.run (first + extra)
      (State.mk (invoke parameterRegion calleeRegion following SourceRead.layout allowance caller arguments)
        storage choices) =
      (events ++ (machine.run extra saved).1, (machine.run extra saved).2) :=
  resume_after_prefix first extra _ saved events paused

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000


/-! ## Physical symbol span lookup

The actual C entry-match and complete lookup bodies are read through the
maintained source recognizer and executed by the existing cell-memory reader.
Table layout, acquired publication/borrow lifetime and the exact libc span
contract remain explicit. No lookup-result oracle, new hash/probe algorithm,
or whole native compiler/allocator/concurrency correspondence is introduced.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.EntryMatch
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.SeparationAlgebra
open ReadExpressions StatementBlock

/-- The C library component is invoked at the actual two span addresses and
length. Its byte-comparison and borrowed-storage contract is stated separately. -/
abbrev Compare := Option Ptr → Option Ptr → UInt32 → CProg CVal Int32

def calls (compare : Compare) : Calls := fun name arguments =>
  if name = "memcmp".toList then
    match arguments with
    | [.ptr left, .ptr right, .u32 length] =>
        compare left right length >>= fun result => pure (.i32 result)
    | _ => CProg.undefined
  else CProg.undefined

def read (compare : Compare) (environment : Environment) (operand : CExpr) : CProg CVal CVal :=
  expressionWithNames (fun name => resolved (environment name)) (calls compare) Source.layout operand

def entryOperand : CExpr := .identifier "entry".toList
def bufferOperand : CExpr := .identifier "bytes".toList
def lengthOperand : CExpr := .identifier "len".toList
def hashOperand : CExpr := .identifier "hash".toList
def storedBytes : CExpr := .field entryOperand "bytes".toList true
def lengthEqual : CExpr := .binary .eq (.field entryOperand "len".toList true) lengthOperand
def hashEqual : CExpr := .binary .eq (.field entryOperand "hash".toList true) hashOperand
def comparison : CExpr := .call "memcmp".toList [storedBytes, bufferOperand, lengthOperand]
def comparisonZero : CExpr := .binary .eq comparison (.decimal 0)
def condition : CExpr := .binary .and
  (.binary .and (.binary .and (.binary .and entryOperand storedBytes) lengthEqual) hashEqual)
  comparisonZero

def body : List CStatement := [.return (some condition)]
def program (compare : Compare) (environment : Environment) : CProg CVal ReadBlock.Result :=
  executeWith { read := fun _ => read compare } (fun _ _ _ => CProg.undefined)
    Source.layout 0 1 environment body

def bytesAt : Option Ptr → CProg CVal (Option Ptr)
  | none => CProg.undefined
  | some entry => CProg.loadPtr entry

def lengthAt : Option Ptr → CProg CVal UInt32
  | none => CProg.undefined
  | some entry => CProg.loadU32 (entry + 1)

def hashAt : Option Ptr → CProg CVal UInt64
  | none => CProg.undefined
  | some entry => CProg.loadU64 (entry + 2)

/-- This performs the source's loads in order, including the second bytes
field load at the actual call. It does not replace pointer truth by a host test. -/
def operations (compare : Compare) (entry bytes : Option Ptr) (length : UInt32)
    (hash : UInt64) : CProg CVal Bool := do
  let entryNull ← CProg.ptrEq entry none
  if entryNull then pure false else do
    let firstBytes ← bytesAt entry
    let bytesNull ← CProg.ptrEq firstBytes none
    if bytesNull then pure false else do
      let storedLength ← lengthAt entry
      if storedLength == length then do
        let storedHash ← hashAt entry
        if storedHash == hash then do
          let actualBytes ← bytesAt entry
          let result ← compare actualBytes bytes length
          pure (result == 0)
        else pure false
      else pure false

structure Parameters (environment : Environment) (entry bytes : Option Ptr)
    (length : UInt32) (hash : UInt64) : Prop where
  entry : environment "entry".toList = some (.ptr entry)
  bytes : environment "bytes".toList = some (.ptr bytes)
  length : environment "len".toList = some (.u32 length)
  hash : environment "hash".toList = some (.u64 hash)

theorem entry_parameter (compare : Compare) (environment : Environment)
    (entry bytes : Option Ptr) (length : UInt32) (hash : UInt64)
    (parameters : Parameters environment entry bytes length hash) :
    read compare environment entryOperand = pure (.ptr entry) := by
  change resolved (environment "entry".toList) = _
  rw [parameters.entry]
  rfl

theorem bytes_field (compare : Compare) (environment : Environment)
    (entry bytes : Option Ptr) (length : UInt32) (hash : UInt64)
    (parameters : Parameters environment entry bytes length hash) :
    read compare environment storedBytes =
      (bytesAt entry >>= fun value => pure (.ptr value)) := by
  change (read compare environment entryOperand >>= fun value =>
    field Source.layout value "bytes".toList) = _
  rw [entry_parameter compare environment entry bytes length hash parameters]
  cases entry with
  | none => exact (undefined_bind _).symm
  | some entry =>
      change (CProg.loadPtr (entry + 0) >>= fun value => pure (CVal.ptr value)) = _
      rw [ptr_add_zero]
      rfl

theorem length_test (compare : Compare) (environment : Environment)
    (entry bytes : Option Ptr) (length : UInt32) (hash : UInt64)
    (parameters : Parameters environment entry bytes length hash) :
    read compare environment lengthEqual =
      (lengthAt entry >>= fun value => pure (.bool (value == length))) := by
  have argument : read compare environment lengthOperand = pure (.u32 length) := by
    change resolved (environment "len".toList) = _
    rw [parameters.length]
    rfl
  change (read compare environment (.field entryOperand "len".toList true) >>= fun value =>
    read compare environment lengthOperand >>= fun actual => binary .eq value actual) = _
  rw [argument]
  have member : read compare environment (.field entryOperand "len".toList true) =
      (lengthAt entry >>= fun value => pure (.u32 value)) := by
    change (read compare environment entryOperand >>= fun value =>
      field Source.layout value "len".toList) = _
    rw [entry_parameter compare environment entry bytes length hash parameters]
    cases entry with
    | none => exact (undefined_bind _).symm
    | some entry => rfl
  rw [member]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

theorem hash_test (compare : Compare) (environment : Environment)
    (entry bytes : Option Ptr) (length : UInt32) (hash : UInt64)
    (parameters : Parameters environment entry bytes length hash) :
    read compare environment hashEqual =
      (hashAt entry >>= fun value => pure (.bool (value == hash))) := by
  have argument : read compare environment hashOperand = pure (.u64 hash) := by
    change resolved (environment "hash".toList) = _
    rw [parameters.hash]
    rfl
  change (read compare environment (.field entryOperand "hash".toList true) >>= fun value =>
    read compare environment hashOperand >>= fun actual => binary .eq value actual) = _
  rw [argument]
  have member : read compare environment (.field entryOperand "hash".toList true) =
      (hashAt entry >>= fun value => pure (.u64 value)) := by
    change (read compare environment entryOperand >>= fun value =>
      field Source.layout value "hash".toList) = _
    rw [entry_parameter compare environment entry bytes length hash parameters]
    cases entry with
    | none => exact (undefined_bind _).symm
    | some entry => rfl
  rw [member]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

theorem comparison_call (compare : Compare) (environment : Environment)
    (entry bytes : Option Ptr) (length : UInt32) (hash : UInt64)
    (parameters : Parameters environment entry bytes length hash) :
    read compare environment comparison =
      (bytesAt entry >>= fun actual => compare actual bytes length >>= fun result => pure (.i32 result)) := by
  have buffer : read compare environment bufferOperand = pure (.ptr bytes) := by
    change resolved (environment "bytes".toList) = _
    rw [parameters.bytes]
    rfl
  have size : read compare environment lengthOperand = pure (.u32 length) := by
    change resolved (environment "len".toList) = _
    rw [parameters.length]
    rfl
  have arguments : argumentsWithNames (fun name => resolved (environment name))
      (calls compare) Source.layout [storedBytes, bufferOperand, lengthOperand] =
      (read compare environment storedBytes >>= fun first =>
        read compare environment bufferOperand >>= fun second =>
        read compare environment lengthOperand >>= fun third => pure [first, second, third]) := by
    simp only [argumentsWithNames.eq_def,
      Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, read]
  change (argumentsWithNames (fun name => resolved (environment name)) (calls compare)
    Source.layout [storedBytes, bufferOperand, lengthOperand] >>= calls compare "memcmp".toList) = _
  rw [arguments]
  rw [bytes_field compare environment entry bytes length hash parameters, buffer, size]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

theorem comparison_test (compare : Compare) (environment : Environment)
    (entry bytes : Option Ptr) (length : UInt32) (hash : UInt64)
    (parameters : Parameters environment entry bytes length hash) :
    read compare environment comparisonZero =
      (bytesAt entry >>= fun actual => compare actual bytes length >>= fun result =>
        pure (.bool (result == 0))) := by
  change (read compare environment comparison >>= fun result =>
    pure (.i32 0) >>= fun zero => binary .eq result zero) = _
  rw [comparison_call compare environment entry bytes length hash parameters]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

/-- The source interpreter's short-circuiting is kept at the operand level,
so no unselected operand or external comparison can acquire a receipt. -/
theorem and_read (compare : Compare) (environment : Environment) (left right : CExpr) :
    (read compare environment (.binary .and left right) >>= truth) =
      (do let first ← read compare environment left
          let selected ← truth first
          if selected then read compare environment right >>= truth else pure false) := by
  change ((do let first ← read compare environment left
              let selected ← truth first
              if selected then do
                let second ← read compare environment right
                let selectedSecond ← truth second
                pure (CVal.bool selectedSecond)
              else pure (CVal.bool false)) >>= truth) = _
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext first
  congr 1
  funext selected
  cases selected <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext second
  change (truth second).bind Prog.ret = truth second
  exact Prog.bind_ret _


/-- A logical-and expression produces a Boolean C value after the same
left-to-right guarded reads used by its truth observation. -/
theorem and_value (compare : Compare) (environment : Environment) (left right : CExpr) :
    read compare environment (.binary .and left right) =
      ((read compare environment (.binary .and left right) >>= truth) >>=
        fun result => pure (.bool result)) := by
  rw [and_read]
  change (do let first ← read compare environment left
             let selected ← truth first
             if selected then do
               let second ← read compare environment right
               let selectedSecond ← truth second
               pure (CVal.bool selectedSecond)
             else pure (CVal.bool false)) = _
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext first
  congr 1
  funext selected
  cases selected <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

/-- The source expression and concrete memory operations have the same
ordered reads, pointer checks and sole selected external call. -/
theorem actual_condition_uses_operations (compare : Compare) (environment : Environment)
    (entry bytes : Option Ptr) (length : UInt32) (hash : UInt64)
    (parameters : Parameters environment entry bytes length hash) :
    (read compare environment condition >>= truth) = operations compare entry bytes length hash := by
  have prefix0 : (read compare environment (.binary .and entryOperand storedBytes) >>= truth) =
      (do let entryNull ← CProg.ptrEq entry none
          if entryNull then pure false else do
            let firstBytes ← bytesAt entry
            let bytesNull ← CProg.ptrEq firstBytes none
            pure (!bytesNull)) := by
    rw [and_read, entry_parameter compare environment entry bytes length hash parameters,
      bytes_field compare environment entry bytes length hash parameters]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
    congr 1
    funext entryNull
    cases entryNull <;> rfl
  simp only [Prog.bind_eq] at prefix0
  have prefix1 : (read compare environment
      (.binary .and (.binary .and entryOperand storedBytes) lengthEqual) >>= truth) =
      (do let entryNull ← CProg.ptrEq entry none
          if entryNull then pure false else do
            let firstBytes ← bytesAt entry
            let bytesNull ← CProg.ptrEq firstBytes none
            if bytesNull then pure false else do
              let storedLength ← lengthAt entry
              pure (storedLength == length)) := by
    rw [and_read]
    simp only [Prog.bind_eq]
    rw [← Prog.bind_assoc, prefix0,
      length_test compare environment entry bytes length hash parameters]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
    congr 1
    funext entryNull
    cases entryNull <;> simp only [Bool.false_eq_true, ↓reduceIte, Prog.bind_assoc, Prog.ret_bind]
    congr 1
    funext firstBytes
    congr 1
    funext bytesNull
    cases bytesNull <;> rfl
  simp only [Prog.bind_eq] at prefix1
  have prefix2 : (read compare environment
      (.binary .and (.binary .and (.binary .and entryOperand storedBytes) lengthEqual) hashEqual)
        >>= truth) =
      (do let entryNull ← CProg.ptrEq entry none
          if entryNull then pure false else do
            let firstBytes ← bytesAt entry
            let bytesNull ← CProg.ptrEq firstBytes none
            if bytesNull then pure false else do
              let storedLength ← lengthAt entry
              if storedLength == length then do
                let storedHash ← hashAt entry
                pure (storedHash == hash)
              else pure false) := by
    rw [and_read]
    simp only [Prog.bind_eq]
    rw [← Prog.bind_assoc, prefix1, hash_test compare environment entry bytes length hash parameters]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
    congr 1
    funext entryNull
    cases entryNull <;> simp only [Bool.false_eq_true, ↓reduceIte, Prog.bind_assoc, Prog.ret_bind]
    congr 1
    funext firstBytes
    congr 1
    funext bytesNull
    cases bytesNull <;> simp only [Bool.false_eq_true, ↓reduceIte, Prog.bind_assoc, Prog.ret_bind]
  simp only [Prog.bind_eq] at prefix2
  unfold condition
  rw [and_read]
  simp only [Prog.bind_eq]
  rw [← Prog.bind_assoc, prefix2, comparison_test compare environment entry bytes length hash parameters]
  simp only [operations, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext entryNull
  cases entryNull <;> simp only [Bool.false_eq_true, ↓reduceIte, Prog.bind_assoc, Prog.ret_bind]
  congr 1
  funext firstBytes
  congr 1
  funext bytesNull
  cases bytesNull <;> simp only [Bool.false_eq_true, ↓reduceIte, Prog.bind_assoc, Prog.ret_bind]
  congr 1
  funext storedLength
  by_cases sameLength : (storedLength == length) = true
  · simp only [sameLength, ↓reduceIte, Prog.bind_assoc, Prog.ret_bind]
  · simp only [Bool.eq_false_iff.mpr sameLength, Bool.false_eq_true, ↓reduceIte, Prog.ret_bind]

theorem actual_body_uses_operations (compare : Compare) (environment : Environment)
    (entry bytes : Option Ptr) (length : UInt32) (hash : UInt64)
    (parameters : Parameters environment entry bytes length hash) :
    program compare environment =
      (operations compare entry bytes length hash >>= fun result =>
        pure (.finished (.returned environment (some (.bool result))))) := by
  change (read compare environment condition >>= fun result =>
    pure (ReadBlock.Result.finished (.returned environment (some result)))) = _
  rw [show read compare environment condition =
    ((read compare environment condition >>= truth) >>= fun result => pure (.bool result)) from
      and_value compare environment _ _]
  rw [actual_condition_uses_operations compare environment entry bytes length hash parameters]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]


universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

private theorem load_pointer_wp (heap : Heap L) (pointer : Ptr) (value : Option Ptr)
    (held : Reads pointer (.ptr value) heap) (post : Option Ptr → Heap L → Prop)
    (after : post value heap) : (CProg.loadPtr pointer).wp act post heap := by
  refine wp_consequence act
    (loadPtr_rule (P := fun reached => reached = heap) (q := value) ?_) rfl ?_
  · intro reached equal
    subst reached
    exact held
  · rintro _ _ ⟨rfl, rfl⟩
    exact after

private theorem load_word_wp (heap : Heap L) (pointer : Ptr) (value : UInt32)
    (held : Reads pointer (.u32 value) heap) (post : UInt32 → Heap L → Prop)
    (after : post value heap) : (CProg.loadU32 pointer).wp act post heap := by
  refine wp_consequence act
    (loadU32_rule (P := fun reached => reached = heap) (n := value) ?_) rfl ?_
  · intro reached equal
    subst reached
    exact held
  · rintro _ _ ⟨rfl, rfl⟩
    exact after

private theorem load_wide_wp (heap : Heap L) (pointer : Ptr) (value : UInt64)
    (held : Reads pointer (.u64 value) heap) (post : UInt64 → Heap L → Prop)
    (after : post value heap) : (CProg.loadU64 pointer).wp act post heap := by
  refine wp_consequence act
    (loadU64_rule (P := fun reached => reached = heap) (n := value) ?_) rfl ?_
  · intro reached equal
    subst reached
    exact held
  · rintro _ _ ⟨rfl, rfl⟩
    exact after

/-- A borrowed byte span is a physical typed-cell resource. It preserves
arbitrary bytes; no UTF-8 or terminating-NUL interpretation is introduced. -/
def Span (heap : Heap L) (pointer : Ptr) (bytes : List UInt8) : Prop :=
  ∃ rest : Heap L → Prop, (Cells pointer (bytes.map (fun byte => some (CVal.u8 byte))) ∗ rest) heap

/-- Named libc component contract. It constrains only the invoked comparison
of the two supplied borrowed spans, its zero result and heap preservation.
It supplies no symbol-table lookup answer or receipt for an internal libc step. -/
structure MemcmpContract (compare : Compare) : Prop where
  compares : ∀ (heap : Heap L) (left right : Ptr) (length : UInt32)
    (leftBytes rightBytes : List UInt8),
    leftBytes.length = length.toNat → rightBytes.length = length.toNat →
    Valid heap left → Valid heap right →
    Span heap left leftBytes → Span heap right rightBytes →
    (compare (some left) (some right) length).wp act
      (fun result reached => reached = heap ∧ (result = 0 ↔ leftBytes = rightBytes)) heap

theorem null_entry_wp (compare : Compare) (heap : Heap L) (bytes : Option Ptr)
    (length : UInt32) (hash : UInt64) (post : Bool → Heap L → Prop)
    (after : post false heap) :
    (operations compare none bytes length hash).wp act post heap := by
  unfold operations
  rw [wp_bind']
  apply wp_ptrEq (p := none) (q := none) (σ := heap) trivial trivial
  simpa only [decide_true, ↓reduceIte, wp_pure] using after

theorem null_bytes_wp (compare : Compare) (heap : Heap L) (entry : Ptr) (bytes : Option Ptr)
    (length : UInt32) (hash : UInt64) (live : Valid heap entry)
    (stored : Reads entry (.ptr none) heap) (post : Bool → Heap L → Prop)
    (after : post false heap) :
    (operations compare (some entry) bytes length hash).wp act post heap := by
  unfold operations
  rw [wp_bind']
  apply wp_ptrEq (p := some entry) (q := none) (σ := heap) live trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, bytesAt]
  rw [wp_bind']
  apply load_pointer_wp heap entry none stored
  rw [wp_bind']
  apply wp_ptrEq (p := none) (q := none) (σ := heap) trivial trivial
  simpa only [decide_true, ↓reduceIte, wp_pure] using after

theorem mismatched_length_wp (compare : Compare) (heap : Heap L) (entry buffer : Ptr)
    (bytes : Option Ptr) (length storedLength : UInt32) (hash : UInt64)
    (live : Valid heap entry) (bufferLive : Valid heap buffer)
    (stored : Reads entry (.ptr (some buffer)) heap)
    (lengthCell : Reads (entry + 1) (.u32 storedLength) heap)
    (different : storedLength ≠ length) (post : Bool → Heap L → Prop)
    (after : post false heap) :
    (operations compare (some entry) bytes length hash).wp act post heap := by
  unfold operations
  rw [wp_bind']
  apply wp_ptrEq (p := some entry) (q := none) (σ := heap) live trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, bytesAt]
  rw [wp_bind']
  apply load_pointer_wp heap entry (some buffer) stored
  rw [wp_bind']
  apply wp_ptrEq (p := some buffer) (q := none) (σ := heap) bufferLive trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, lengthAt]
  rw [wp_bind']
  apply load_word_wp heap (entry + 1) storedLength lengthCell
  simpa only [beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte, wp_pure] using after

theorem mismatched_hash_wp (compare : Compare) (heap : Heap L) (entry buffer : Ptr)
    (bytes : Option Ptr) (length : UInt32) (hash storedHash : UInt64)
    (live : Valid heap entry) (bufferLive : Valid heap buffer)
    (stored : Reads entry (.ptr (some buffer)) heap)
    (lengthCell : Reads (entry + 1) (.u32 length) heap)
    (hashCell : Reads (entry + 2) (.u64 storedHash) heap)
    (different : storedHash ≠ hash) (post : Bool → Heap L → Prop)
    (after : post false heap) :
    (operations compare (some entry) bytes length hash).wp act post heap := by
  unfold operations
  rw [wp_bind']
  apply wp_ptrEq (p := some entry) (q := none) (σ := heap) live trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, bytesAt]
  rw [wp_bind']
  apply load_pointer_wp heap entry (some buffer) stored
  rw [wp_bind']
  apply wp_ptrEq (p := some buffer) (q := none) (σ := heap) bufferLive trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, lengthAt]
  rw [wp_bind']
  apply load_word_wp heap (entry + 1) length lengthCell
  simp only [beq_self_eq_true, ↓reduceIte, hashAt]
  rw [wp_bind']
  apply load_wide_wp heap (entry + 2) storedHash hashCell
  simpa only [beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte, wp_pure] using after

/-- Under the named libc contract, the source-selected comparison decides
exactly the two stored byte spans. Equal lengths or hashes alone are insufficient. -/
theorem matching_header_compares_bytes_wp (compare : Compare) (library : MemcmpContract (L := L) compare)
    (heap : Heap L) (entry buffer bytes : Ptr) (length : UInt32) (hash : UInt64)
    (storedBytes queryBytes : List UInt8)
    (live : Valid heap entry) (bufferLive : Valid heap buffer) (queryLive : Valid heap bytes)
    (stored : Reads entry (.ptr (some buffer)) heap)
    (lengthCell : Reads (entry + 1) (.u32 length) heap)
    (hashCell : Reads (entry + 2) (.u64 hash) heap)
    (storedCount : storedBytes.length = length.toNat) (queryCount : queryBytes.length = length.toNat)
    (storedSpan : Span heap buffer storedBytes) (querySpan : Span heap bytes queryBytes)
    (post : Bool → Heap L → Prop) (after : post (decide (storedBytes = queryBytes)) heap) :
    (operations compare (some entry) (some bytes) length hash).wp act post heap := by
  unfold operations
  rw [wp_bind']
  apply wp_ptrEq (p := some entry) (q := none) (σ := heap) live trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, bytesAt]
  rw [wp_bind']
  apply load_pointer_wp heap entry (some buffer) stored
  rw [wp_bind']
  apply wp_ptrEq (p := some buffer) (q := none) (σ := heap) bufferLive trivial
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, lengthAt]
  rw [wp_bind']
  apply load_word_wp heap (entry + 1) length lengthCell
  simp only [beq_self_eq_true, ↓reduceIte, hashAt]
  rw [wp_bind']
  apply load_wide_wp heap (entry + 2) hash hashCell
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply load_pointer_wp heap entry (some buffer) stored
  rw [wp_bind']
  refine wp_mono act ?_ (library.compares heap buffer bytes length storedBytes queryBytes
    storedCount queryCount bufferLive queryLive storedSpan querySpan)
  rintro result reached ⟨rfl, zero⟩
  have same : (result == 0) = decide (storedBytes = queryBytes) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq, decide_eq_true_eq] using zero
  simpa only [wp_pure, same] using after

theorem actual_body_compares_owned_bytes_wp (compare : Compare)
    (library : MemcmpContract (L := L) compare) (environment : Environment)
    (heap : Heap L) (entry buffer bytes : Ptr) (length : UInt32) (hash : UInt64)
    (storedBytes queryBytes : List UInt8)
    (parameters : Parameters environment (some entry) (some bytes) length hash)
    (live : Valid heap entry) (bufferLive : Valid heap buffer) (queryLive : Valid heap bytes)
    (stored : Reads entry (.ptr (some buffer)) heap)
    (lengthCell : Reads (entry + 1) (.u32 length) heap)
    (hashCell : Reads (entry + 2) (.u64 hash) heap)
    (storedCount : storedBytes.length = length.toNat) (queryCount : queryBytes.length = length.toNat)
    (storedSpan : Span heap buffer storedBytes) (querySpan : Span heap bytes queryBytes)
    (post : ReadBlock.Result → Heap L → Prop)
    (after : post (.finished (.returned environment (some (.bool (decide (storedBytes = queryBytes)))))) heap) :
    (program compare environment).wp act post heap := by
  rw [actual_body_uses_operations compare environment (some entry) (some bytes) length hash parameters,
    wp_bind']
  apply matching_header_compares_bytes_wp compare library heap entry buffer bytes length hash
    storedBytes queryBytes live bufferLive queryLive stored lengthCell hashCell storedCount queryCount storedSpan querySpan
  simpa only [wp_pure] using after


/-- The full entry predicate observes the declared hash together with exact
bytes. The same hash and length cannot turn a byte collision into equality. -/
theorem entry_compares_owned_key_wp (compare : Compare)
    (library : MemcmpContract (L := L) compare)
    (heap : Heap L) (entry buffer bytes : Ptr) (length storedLength : UInt32)
    (hash storedHash : UInt64) (storedBytes queryBytes : List UInt8)
    (live : Valid heap entry) (bufferLive : Valid heap buffer) (queryLive : Valid heap bytes)
    (stored : Reads entry (.ptr (some buffer)) heap)
    (lengthCell : Reads (entry + 1) (.u32 storedLength) heap)
    (hashCell : Reads (entry + 2) (.u64 storedHash) heap)
    (storedCount : storedBytes.length = storedLength.toNat)
    (queryCount : queryBytes.length = length.toNat)
    (storedSpan : Span heap buffer storedBytes) (querySpan : Span heap bytes queryBytes)
    (post : Bool → Heap L → Prop)
    (after : post (decide ((storedHash, storedBytes) = (hash, queryBytes))) heap) :
    (operations compare (some entry) (some bytes) length hash).wp act post heap := by
  by_cases sameLength : storedLength = length
  · subst storedLength
    by_cases sameHash : storedHash = hash
    · subst storedHash
      apply matching_header_compares_bytes_wp compare library heap entry buffer bytes length hash
        storedBytes queryBytes live bufferLive queryLive stored lengthCell hashCell storedCount queryCount
        storedSpan querySpan
      simpa only [Prod.mk.injEq, true_and] using after
    · apply mismatched_hash_wp compare heap entry buffer (some bytes) length hash storedHash
        live bufferLive stored lengthCell hashCell sameHash
      simpa only [Prod.mk.injEq, sameHash, false_and, decide_false] using after
  · have differentBytes : storedBytes ≠ queryBytes := by
      intro same
      have counts := congrArg List.length same
      rw [storedCount, queryCount] at counts
      exact sameLength (UInt32.toNat.inj counts)
    apply mismatched_length_wp compare heap entry buffer (some bytes) length storedLength hash
      live bufferLive stored lengthCell sameLength
    simpa only [Prod.mk.injEq, differentBytes, and_false, decide_false] using after

private def sourcePiece0 : String × List Token := ("{\n", [.punctuation "{".toList])
private theorem sourcePiece0_lex : sourcePiece0.1.toList.foldl step initial = completed sourcePiece0.2 := by decide +kernel

private def sourcePiece1 : String × List Token := ("    return entry && entry->bytes && entry->len == len && entry->hash == hash &&\n", [.identifier "return".toList, .identifier "entry".toList, .punctuation "&&".toList, .identifier "entry".toList, .punctuation "->".toList, .identifier "bytes".toList, .punctuation "&&".toList, .identifier "entry".toList, .punctuation "->".toList, .identifier "len".toList, .punctuation "==".toList, .identifier "len".toList, .punctuation "&&".toList, .identifier "entry".toList, .punctuation "->".toList, .identifier "hash".toList, .punctuation "==".toList, .identifier "hash".toList, .punctuation "&&".toList])
private theorem sourcePiece1_lex : sourcePiece1.1.toList.foldl step initial = completed sourcePiece1.2 := by decide +kernel

private def sourcePiece2 : String × List Token := ("           memcmp(entry->bytes, bytes, len) == 0;\n", [.identifier "memcmp".toList, .punctuation "(".toList, .identifier "entry".toList, .punctuation "->".toList, .identifier "bytes".toList, .punctuation ",".toList, .identifier "bytes".toList, .punctuation ",".toList, .identifier "len".toList, .punctuation ")".toList, .punctuation "==".toList, .number "0".toList, .punctuation ";".toList])
private theorem sourcePiece2_lex : sourcePiece2.1.toList.foldl step initial = completed sourcePiece2.2 := by decide +kernel

private def sourcePiece3 : String × List Token := ("}", [.punctuation "}".toList])
private theorem sourcePiece3_lex : sourcePiece3.1.toList.foldl step initial = completed sourcePiece3.2 := by decide +kernel

private def sourcePieces : List (String × List Token) := [sourcePiece0, sourcePiece1, sourcePiece2, sourcePiece3]
def source : String := String.join (sourcePieces.map Prod.fst)
def sourceTokens : List Token := sourcePieces.flatMap Prod.snd
theorem actual_source_lexed : lex source.toList = .ok sourceTokens := by
  apply lex_completed_string_pieces
  simp only [sourcePieces, List.forall_cons]
  exact ⟨sourcePiece0_lex, sourcePiece1_lex, sourcePiece2_lex, sourcePiece3_lex, trivial⟩
theorem actual_body_parsed : blockText? [] source.toList = some body := by
  exact block_text_of_parts [] _ sourceTokens _ actual_source_lexed (by rfl)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.EntryMatch


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.Source
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def id (name : String) : CExpr := .identifier name.toList
def field (owner member : String) : CExpr := .field (id owner) member.toList true
def zero : CExpr := id "SYMBOL_ID_NONE"
def slots : CExpr := field "st" "slots"
def indexedSlot : CExpr := .index slots (id "slot")
def slotIdentity : CExpr := .field indexedSlot "id".toList false
def selectedIdentity : CExpr := field "entry" "id"
def lockAddress : CExpr := .unary .address (field "st" "write_mutex")
def badInput : CExpr := .binary .or (.binary .or (.unary .not (id "st"))
  (.unary .not (id "bytes"))) (.unary .not (id "len"))
def hashHome : CExpr := .cast ⟨"uint32_t".toList, 0⟩
  (.binary .mod (id "hash") (field "st" "slot_cap"))
def occupied : CExpr := .binary .ne slotIdentity zero
def slotMatches : CExpr := .binary .and (.binary .eq (field "entry" "hash") (id "hash"))
  (.call "symbol_entry_matches".toList
    [.call "symbol_table_entry_ref".toList [id "st", selectedIdentity],
     id "bytes", id "len", id "hash"])
def advance : CExpr := .binary .mod (.binary .add (id "slot") (.decimal 1))
  (field "st" "slot_cap")
def iteration : List CStatement :=
  [.declarePointeeConst ⟨"SymbolSlot".toList, 1⟩ "entry".toList (.unary .address indexedSlot),
   .branch slotMatches [.assign (id "found") selectedIdentity, .break] [],
   .assign (id "slot") advance]
def body : List CStatement :=
  [.branch badInput [.return (some zero)] [],
   .declare ⟨"SymbolId".toList, 0⟩ "found".toList zero,
   .effect (.call "pthread_mutex_lock".toList [lockAddress]),
   .branch (field "st" "slot_cap")
     [.declare ⟨"uint32_t".toList, 0⟩ "slot".toList hashHome,
      .whileLoop occupied iteration] [],
   .effect (.call "pthread_mutex_unlock".toList [lockAddress]),
   .return (some (id "found"))]


private def sourcePiece0 : String × List Token := ("{\n", [.punctuation "{".toList])
private theorem sourcePiece0_lex : sourcePiece0.1.toList.foldl step initial = completed sourcePiece0.2 := by decide +kernel

private def sourcePiece1 : String × List Token := ("    if (!st || !bytes || !len) return SYMBOL_ID_NONE;\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "st".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "bytes".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "len".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "SYMBOL_ID_NONE".toList, .punctuation ";".toList])
private theorem sourcePiece1_lex : sourcePiece1.1.toList.foldl step initial = completed sourcePiece1.2 := by decide +kernel

private def sourcePiece2 : String × List Token := ("    SymbolId found = SYMBOL_ID_NONE;\n", [.identifier "SymbolId".toList, .identifier "found".toList, .punctuation "=".toList, .identifier "SYMBOL_ID_NONE".toList, .punctuation ";".toList])
private theorem sourcePiece2_lex : sourcePiece2.1.toList.foldl step initial = completed sourcePiece2.2 := by decide +kernel

private def sourcePiece3 : String × List Token := ("    pthread_mutex_lock(&st->write_mutex);\n", [.identifier "pthread_mutex_lock".toList, .punctuation "(".toList, .punctuation "&".toList, .identifier "st".toList, .punctuation "->".toList, .identifier "write_mutex".toList, .punctuation ")".toList, .punctuation ";".toList])
private theorem sourcePiece3_lex : sourcePiece3.1.toList.foldl step initial = completed sourcePiece3.2 := by decide +kernel

private def sourcePiece4 : String × List Token := ("    if (st->slot_cap) {\n", [.identifier "if".toList, .punctuation "(".toList, .identifier "st".toList, .punctuation "->".toList, .identifier "slot_cap".toList, .punctuation ")".toList, .punctuation "{".toList])
private theorem sourcePiece4_lex : sourcePiece4.1.toList.foldl step initial = completed sourcePiece4.2 := by decide +kernel

private def sourcePiece5 : String × List Token := ("        uint32_t slot = (uint32_t)(hash % st->slot_cap);\n", [.identifier "uint32_t".toList, .identifier "slot".toList, .punctuation "=".toList, .punctuation "(".toList, .identifier "uint32_t".toList, .punctuation ")".toList, .punctuation "(".toList, .identifier "hash".toList, .punctuation "%".toList, .identifier "st".toList, .punctuation "->".toList, .identifier "slot_cap".toList, .punctuation ")".toList, .punctuation ";".toList])
private theorem sourcePiece5_lex : sourcePiece5.1.toList.foldl step initial = completed sourcePiece5.2 := by decide +kernel

private def sourcePiece6 : String × List Token := ("        while (st->slots[slot].id != SYMBOL_ID_NONE) {\n", [.identifier "while".toList, .punctuation "(".toList, .identifier "st".toList, .punctuation "->".toList, .identifier "slots".toList, .punctuation "[".toList, .identifier "slot".toList, .punctuation "]".toList, .punctuation ".".toList, .identifier "id".toList, .punctuation "!=".toList, .identifier "SYMBOL_ID_NONE".toList, .punctuation ")".toList, .punctuation "{".toList])
private theorem sourcePiece6_lex : sourcePiece6.1.toList.foldl step initial = completed sourcePiece6.2 := by decide +kernel

private def sourcePiece7 : String × List Token := ("            const SymbolSlot *entry = &st->slots[slot];\n", [.identifier "const".toList, .identifier "SymbolSlot".toList, .punctuation "*".toList, .identifier "entry".toList, .punctuation "=".toList, .punctuation "&".toList, .identifier "st".toList, .punctuation "->".toList, .identifier "slots".toList, .punctuation "[".toList, .identifier "slot".toList, .punctuation "]".toList, .punctuation ";".toList])
private theorem sourcePiece7_lex : sourcePiece7.1.toList.foldl step initial = completed sourcePiece7.2 := by decide +kernel

private def sourcePiece8 : String × List Token := ("            if (entry->hash == hash &&\n", [.identifier "if".toList, .punctuation "(".toList, .identifier "entry".toList, .punctuation "->".toList, .identifier "hash".toList, .punctuation "==".toList, .identifier "hash".toList, .punctuation "&&".toList])
private theorem sourcePiece8_lex : sourcePiece8.1.toList.foldl step initial = completed sourcePiece8.2 := by decide +kernel

private def sourcePiece9 : String × List Token := ("                symbol_entry_matches(symbol_table_entry_ref(st, entry->id),\n", [.identifier "symbol_entry_matches".toList, .punctuation "(".toList, .identifier "symbol_table_entry_ref".toList, .punctuation "(".toList, .identifier "st".toList, .punctuation ",".toList, .identifier "entry".toList, .punctuation "->".toList, .identifier "id".toList, .punctuation ")".toList, .punctuation ",".toList])
private theorem sourcePiece9_lex : sourcePiece9.1.toList.foldl step initial = completed sourcePiece9.2 := by decide +kernel

private def sourcePiece10 : String × List Token := ("                                     bytes, len, hash)) {\n", [.identifier "bytes".toList, .punctuation ",".toList, .identifier "len".toList, .punctuation ",".toList, .identifier "hash".toList, .punctuation ")".toList, .punctuation ")".toList, .punctuation "{".toList])
private theorem sourcePiece10_lex : sourcePiece10.1.toList.foldl step initial = completed sourcePiece10.2 := by decide +kernel

private def sourcePiece11 : String × List Token := ("                found = entry->id;\n", [.identifier "found".toList, .punctuation "=".toList, .identifier "entry".toList, .punctuation "->".toList, .identifier "id".toList, .punctuation ";".toList])
private theorem sourcePiece11_lex : sourcePiece11.1.toList.foldl step initial = completed sourcePiece11.2 := by decide +kernel

private def sourcePiece12 : String × List Token := ("                break;\n", [.identifier "break".toList, .punctuation ";".toList])
private theorem sourcePiece12_lex : sourcePiece12.1.toList.foldl step initial = completed sourcePiece12.2 := by decide +kernel

private def sourcePiece13 : String × List Token := ("            }\n", [.punctuation "}".toList])
private theorem sourcePiece13_lex : sourcePiece13.1.toList.foldl step initial = completed sourcePiece13.2 := by decide +kernel

private def sourcePiece14 : String × List Token := ("            slot = (slot + 1) % st->slot_cap;\n", [.identifier "slot".toList, .punctuation "=".toList, .punctuation "(".toList, .identifier "slot".toList, .punctuation "+".toList, .number "1".toList, .punctuation ")".toList, .punctuation "%".toList, .identifier "st".toList, .punctuation "->".toList, .identifier "slot_cap".toList, .punctuation ";".toList])
private theorem sourcePiece14_lex : sourcePiece14.1.toList.foldl step initial = completed sourcePiece14.2 := by decide +kernel

private def sourcePiece15 : String × List Token := ("        }\n", [.punctuation "}".toList])
private theorem sourcePiece15_lex : sourcePiece15.1.toList.foldl step initial = completed sourcePiece15.2 := by decide +kernel

private def sourcePiece16 : String × List Token := ("    }\n", [.punctuation "}".toList])
private theorem sourcePiece16_lex : sourcePiece16.1.toList.foldl step initial = completed sourcePiece16.2 := by decide +kernel

private def sourcePiece17 : String × List Token := ("    pthread_mutex_unlock(&st->write_mutex);\n", [.identifier "pthread_mutex_unlock".toList, .punctuation "(".toList, .punctuation "&".toList, .identifier "st".toList, .punctuation "->".toList, .identifier "write_mutex".toList, .punctuation ")".toList, .punctuation ";".toList])
private theorem sourcePiece17_lex : sourcePiece17.1.toList.foldl step initial = completed sourcePiece17.2 := by decide +kernel

private def sourcePiece18 : String × List Token := ("    return found;\n", [.identifier "return".toList, .identifier "found".toList, .punctuation ";".toList])
private theorem sourcePiece18_lex : sourcePiece18.1.toList.foldl step initial = completed sourcePiece18.2 := by decide +kernel

private def sourcePiece19 : String × List Token := ("}", [.punctuation "}".toList])
private theorem sourcePiece19_lex : sourcePiece19.1.toList.foldl step initial = completed sourcePiece19.2 := by decide +kernel

private def sourcePieces : List (String × List Token) := [sourcePiece0, sourcePiece1, sourcePiece2, sourcePiece3, sourcePiece4, sourcePiece5, sourcePiece6, sourcePiece7, sourcePiece8, sourcePiece9, sourcePiece10, sourcePiece11, sourcePiece12, sourcePiece13, sourcePiece14, sourcePiece15, sourcePiece16, sourcePiece17, sourcePiece18, sourcePiece19]
def source : String := String.join (sourcePieces.map Prod.fst)
def sourceTokens : List Token := sourcePieces.flatMap Prod.snd
theorem actual_source_lexed : lex source.toList = .ok sourceTokens := by
  apply lex_completed_string_pieces
  simp only [sourcePieces, List.forall_cons]
  exact ⟨sourcePiece0_lex, sourcePiece1_lex, sourcePiece2_lex, sourcePiece3_lex, sourcePiece4_lex, sourcePiece5_lex, sourcePiece6_lex, sourcePiece7_lex, sourcePiece8_lex, sourcePiece9_lex, sourcePiece10_lex, sourcePiece11_lex, sourcePiece12_lex, sourcePiece13_lex, sourcePiece14_lex, sourcePiece15_lex, sourcePiece16_lex, sourcePiece17_lex, sourcePiece18_lex, sourcePiece19_lex, trivial⟩
theorem actual_body_parsed : blockText? ["SymbolId".toList, "SymbolSlot".toList, "uint32_t".toList] source.toList = some body := by
  exact block_text_of_parts _ _ sourceTokens _ actual_source_lexed (by rfl)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.Source

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.ScalarRead.SymbolLookupArithmetic
open Mettapedia.Machines.IncrementalConformance

/-- These are the two authored unsigned expression results. The wide hash
is reduced before narrowing; the loop increments the current 32-bit slot. -/
def home (hash : UInt64) (capacity : UInt32) : UInt32 :=
  UInt32.ofNat (hash % UInt64.ofNat capacity.toNat).toNat

def advance (capacity slot : UInt32) : UInt32 := (slot + 1) % capacity

theorem home_toNat (hash : UInt64) (capacity : UInt32) (nonzero : capacity ≠ 0) :
    (home hash capacity).toNat = hash.toNat % capacity.toNat :=
  hash_remainder_narrowing_exact hash capacity nonzero

theorem capacity_positive (capacity : UInt32) (nonzero : capacity ≠ 0) :
    0 < capacity.toNat := by
  by_contra notPositive
  have zero : capacity.toNat = 0 := by omega
  exact nonzero (UInt32.toNat.inj zero)

/-- The actual symbol-table load policy is seven tenths, not the directory
half-load policy. Its mathematical inventory inequality guarantees a vacant
slot; correspondence of the mutating intern/resize code is separate. -/
theorem native_load_has_vacancy (capacity : UInt32) (nonzero : capacity ≠ 0)
    (occupied : Nat) (loadBound : occupied * 10 ≤ capacity.toNat * 7) :
    occupied < capacity.toNat := by
  have positive := capacity_positive capacity nonzero
  omega

theorem home_within (hash : UInt64) (capacity : UInt32) (nonzero : capacity ≠ 0) :
    (home hash capacity).toNat < capacity.toNat := by
  rw [home_toNat hash capacity nonzero]
  exact Nat.mod_lt _ (capacity_positive capacity nonzero)

theorem advance_toNat (capacity slot : UInt32) (within : slot.toNat < capacity.toNat) :
    (advance capacity slot).toNat = (slot.toNat + 1) % capacity.toNat :=
  probe_successor_no_word_wrap slot capacity within

theorem advance_within (capacity slot : UInt32) (within : slot.toNat < capacity.toNat) :
    (advance capacity slot).toNat < capacity.toNat := by
  rw [advance_toNat capacity slot within]
  exact Nat.mod_lt _ (by omega)

/-- Iterating the native word expression visits precisely the generic
physical sequence's positions; no mask or alternative hash is substituted. -/
theorem advance_iterate_toNat (capacity slot : UInt32)
    (within : slot.toNat < capacity.toNat) (steps : Nat) :
    ((advance capacity)^[steps] slot).toNat = (slot.toNat + steps) % capacity.toNat := by
  induction steps generalizing slot with
  | zero => simp only [Function.iterate_zero_apply, Nat.add_zero, Nat.mod_eq_of_lt within]
  | succ steps ih =>
      rw [Function.iterate_succ_apply, ih _ (advance_within capacity slot within),
        advance_toNat capacity slot within]
      rw [Nat.mod_add_mod]
      congr 1
      omega

/-- The established generic probe sequence can therefore be read at the
actual native positions. This is an index bridge, not a second search routine. -/
theorem physical_sequence_cell {Value : Type} (capacity : UInt32)
    (nonzero : capacity ≠ 0) (hash : UInt64)
    (table : Fin capacity.toNat → Option ((UInt64 × List UInt8) × Value))
    (offset : Fin capacity.toNat) :
    (DirectoryProbe.sequence table
      ⟨(home hash capacity).toNat, home_within hash capacity nonzero⟩)[offset.val]'(by
        simpa only [DirectoryProbe.sequence, List.length_ofFn] using offset.isLt) =
      table ⟨((advance capacity)^[offset.val] (home hash capacity)).toNat, by
        rw [advance_iterate_toNat capacity _ (home_within hash capacity nonzero)]
        exact Nat.mod_lt _ (capacity_positive capacity nonzero)⟩ := by
  simp only [DirectoryProbe.sequence, List.getElem_ofFn]
  congr 1
  apply Fin.ext
  exact (advance_iterate_toNat capacity _ (home_within hash capacity nonzero) offset.val).symm

/-- The pre-existing finite probe admits exactly an independently stored
key/ID row under the ordinary no-hole and uniqueness invariants. -/
theorem stored_id_iff (capacity : UInt32) (nonzero : capacity ≠ 0)
    (table : Fin capacity.toNat → Option ((UInt64 × List UInt8) × UInt32))
    (paths : DirectoryProbe.PathsOccupied table
      (fun key => ⟨(home key.1 capacity).toNat, home_within key.1 capacity nonzero⟩))
    (unique : DirectoryProbe.KeysCoherent table) (key : UInt64 × List UInt8) (identifier : UInt32) :
    (InternProbe.probe key (DirectoryProbe.sequence table
      ⟨(home key.1 capacity).toNat, home_within key.1 capacity nonzero⟩)).1 = some identifier ↔
      ∃ slot, table slot = some (key, identifier) :=
  DirectoryProbe.sequence_found_iff table _ paths unique key identifier

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.Physical
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.IncrementalConformance
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

abbrev Key := UInt64 × List UInt8
abbrev Context := UInt32 × UInt32

/-- The declared three-field slot view keeps the actual indexed address.
It is a logical scalar-cell stride, with native byte layout still separate. -/
def slotAddress (table : Ptr) (slot : UInt32) : CProg CVal Ptr := do
  let slots ← CProg.loadPtr table
  match slots with
  | none => CProg.undefined
  | some slots => pure (slots + slot.toNat * 3)

/-- Each while guard reloads the pointer table and selected identity. -/
def guard (table : Ptr) (context : Context) : CProg CVal Bool := do
  let slot ← slotAddress table context.1
  let identifier ← CProg.loadU32 (slot + 2)
  pure (identifier != 0)

/-- The source's increment reloads slot_cap; zero remains undefined here.
The native nonzero-capacity loop invariant discharges that branch. -/
def next (table : Ptr) (context : Context) : CProg CVal (ReadBlock.Result Context) := do
  let capacity ← CProg.loadU32 (table + 1)
  if capacity = 0 then CProg.undefined else
    pure (.finished (.next (advance capacity context.1, context.2)))

/-- A true guard enters the authored body. Its local slot pointer is loaded
again, and success reads the selected identity again for the returned value. -/
def iteration (compare : EntryMatch.Compare) (table bytes : Ptr)
    (length : UInt32) (hash : UInt64) (context : Context) : CProg CVal (ReadBlock.Result Context) := do
  let slot ← slotAddress table context.1
  let candidateHash ← CProg.loadU64 slot
  if candidateHash == hash then do
    let identifier ← CProg.loadU32 (slot + 2)
    let entry ← entryRef (some table) identifier
    let accepted ← EntryMatch.operations compare entry (some bytes) length hash
    if accepted then do
      let selected ← CProg.loadU32 (slot + 2)
      pure (.finished (.broken (context.1, selected)))
    else next table context
  else next table context

def search (compare : EntryMatch.Compare) (table bytes : Ptr)
    (length : UInt32) (hash : UInt64) (fuel : Nat) (context : Context) :
    CProg CVal (ReadBlock.Result Context) :=
  ReadBlock.whileWith (guard table) (iteration compare table bytes length hash) fuel context

variable {L : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- The independent table cell inventory. An occupied slot points through
actual published chunks to an owned byte span. No lookup result is a field. -/
def CellRead (table : Ptr) (slot : UInt32) (cell : Option (Key × UInt32))
    (heap : Heap L) : Prop :=
  ∃ slots, Reads table (.ptr (some slots)) heap ∧
    match cell with
    | none => Reads (slots + slot.toNat * 3 + 2) (.u32 0) heap
    | some (key, identifier) =>
      Reads (slots + slot.toNat * 3 + 2) (.u32 identifier) heap ∧
      Reads (slots + slot.toNat * 3) (.u64 key.1) heap ∧
      ∃ row : PublishedRow heap table identifier,
      ∃ buffer length,
        Valid heap (entryPointer row.chunk identifier) ∧ Valid heap buffer ∧
        Reads (entryPointer row.chunk identifier) (.ptr (some buffer)) heap ∧
        Reads (entryPointer row.chunk identifier + 1) (.u32 length) heap ∧
        Reads (entryPointer row.chunk identifier + 2) (.u64 key.1) heap ∧
        key.2.length = length.toNat ∧ EntryMatch.Span heap buffer key.2

/-- Finite physical traversal in the native modulo direction. -/
def SequenceRead (table : Ptr) (capacity : UInt32) :
    UInt32 → InternProbe.Cells Key UInt32 → Heap L → Prop
  | _, [], _ => True
  | slot, cell :: tail, heap => CellRead table slot cell heap ∧
      SequenceRead table capacity (advance capacity slot) tail heap

private theorem loadPointer_wp {heap : Heap L} {pointer : Ptr} {value : Option Ptr}
    {post : Option Ptr → Heap L → Prop} (held : Reads pointer (.ptr value) heap)
    (after : post value heap) : (CProg.loadPtr pointer).wp act post heap := by
  refine wp_consequence act
    (loadPtr_rule (P := fun reached => reached = heap) (q := value) ?_) rfl ?_
  · rintro reached rfl
    exact held
  · rintro _ _ ⟨rfl, rfl⟩
    exact after

private theorem loadWord_wp {heap : Heap L} {pointer : Ptr} {value : UInt32}
    {post : UInt32 → Heap L → Prop} (held : Reads pointer (.u32 value) heap)
    (after : post value heap) : (CProg.loadU32 pointer).wp act post heap := by
  refine wp_consequence act
    (loadU32_rule (P := fun reached => reached = heap) (n := value) ?_) rfl ?_
  · rintro reached rfl
    exact held
  · rintro _ _ ⟨rfl, rfl⟩
    exact after

private theorem loadWide_wp {heap : Heap L} {pointer : Ptr} {value : UInt64}
    {post : UInt64 → Heap L → Prop} (held : Reads pointer (.u64 value) heap)
    (after : post value heap) : (CProg.loadU64 pointer).wp act post heap := by
  refine wp_consequence act
    (loadU64_rule (P := fun reached => reached = heap) (n := value) ?_) rfl ?_
  · rintro reached rfl
    exact held
  · rintro _ _ ⟨rfl, rfl⟩
    exact after

theorem slot_address_wp (heap : Heap L) (table slots : Ptr) (slot : UInt32)
    (stored : Reads table (.ptr (some slots)) heap) (post : Ptr → Heap L → Prop)
    (after : post (slots + slot.toNat * 3) heap) :
    (slotAddress table slot).wp act post heap := by
  unfold slotAddress
  rw [wp_bind']
  apply loadPointer_wp stored
  simpa only [wp_pure] using after

theorem guard_wp (heap : Heap L) (table : Ptr) (context : Context)
    (cell : Option (Key × UInt32)) (stored : CellRead table context.1 cell heap)
    (post : Bool → Heap L → Prop) (after : post cell.isSome heap) :
    (guard table context).wp act post heap := by
  obtain ⟨slots, tableCell, payload⟩ := stored
  unfold guard
  rw [wp_bind']
  apply slot_address_wp heap table slots context.1 tableCell
  rw [wp_bind']
  cases cell with
  | none =>
    apply loadWord_wp payload
    simpa only [bne, beq_self_eq_true, Bool.not_true, Option.isSome_none, wp_pure] using after
  | some cell =>
    obtain ⟨identifierCell, _, row, buffer, length, _⟩ := payload
    apply loadWord_wp identifierCell
    simpa only [bne, beq_eq_false_iff_ne.mpr row.nonzero, Bool.not_false, Option.isSome_some, wp_pure] using after

theorem next_wp (heap : Heap L) (table : Ptr) (context : Context) (capacity : UInt32)
    (stored : Reads (table + 1) (.u32 capacity) heap) (nonzero : capacity ≠ 0)
    (post : ReadBlock.Result Context → Heap L → Prop)
    (after : post (.finished (.next (advance capacity context.1, context.2))) heap) :
    (next table context).wp act post heap := by
  unfold next
  rw [wp_bind']
  apply loadWord_wp stored
  simpa only [if_neg nonzero, wp_pure] using after

/-- The source body admits an ID exactly after the current slot's actual
hash and byte key pass. The returned ID is loaded again from that same slot. -/
theorem iteration_wp (compare : EntryMatch.Compare)
    (library : EntryMatch.MemcmpContract (L := L) compare)
    (heap : Heap L) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (query : List UInt8) (context : Context) (capacity : UInt32)
    (key : Key) (identifier : UInt32)
    (queryCount : query.length = length.toNat) (queryLive : Valid heap bytes)
    (querySpan : EntryMatch.Span heap bytes query)
    (capCell : Reads (table + 1) (.u32 capacity) heap) (nonzero : capacity ≠ 0)
    (stored : CellRead table context.1 (some (key, identifier)) heap)
    (post : ReadBlock.Result Context → Heap L → Prop)
    (after : post (if key = (hash, query) then .finished (.broken (context.1, identifier))
      else .finished (.next (advance capacity context.1, context.2))) heap) :
    (iteration compare table bytes length hash context).wp act post heap := by
  obtain ⟨slots, tableCell, identifierCell, hashCell, row, buffer, storedLength,
    rowLive, bufferLive, bytesCell, lengthCell, rowHashCell, byteCount, span⟩ := stored
  unfold iteration
  rw [wp_bind']
  apply slot_address_wp heap table slots context.1 tableCell
  rw [wp_bind']
  apply loadWide_wp hashCell
  by_cases sameHash : key.1 = hash
  · simp only [sameHash, beq_self_eq_true, ↓reduceIte]
    rw [wp_bind']
    apply loadWord_wp identifierCell
    rw [wp_bind']
    apply entry_ref_wp heap table identifier row
    rw [wp_bind']
    apply EntryMatch.entry_compares_owned_key_wp compare library heap
      (entryPointer row.chunk identifier) buffer bytes length storedLength hash key.1
      key.2 query rowLive bufferLive queryLive bytesCell lengthCell rowHashCell
      byteCount queryCount span querySpan
    by_cases same : key = (hash, query)
    · simp only [same, decide_true, ↓reduceIte]
      rw [wp_bind']
      apply loadWord_wp identifierCell
      simpa only [if_pos same, wp_pure] using after
    · simp only [Prod.eta, same, decide_false, Bool.false_eq_true, ↓reduceIte]
      apply next_wp heap table context capacity capCell nonzero
      simpa only [if_neg same] using after
  · simp only [beq_eq_false_iff_ne.mpr sameHash, Bool.false_eq_true, ↓reduceIte]
    apply next_wp heap table context capacity capCell nonzero
    have different : key ≠ (hash, query) := by
      intro equal
      exact sameHash (congrArg Prod.fst equal)
    simpa only [if_neg different] using after


/-- The finite inventory is stated independently at physical table indices;
the actual modulo expression determines the traversal order. -/
theorem sequenceRead_iff (table : Ptr) (capacity slot : UInt32)
    (cells : InternProbe.Cells Key UInt32) (heap : Heap L) :
    SequenceRead table capacity slot cells heap ↔
      ∀ offset : Fin cells.length,
        CellRead table ((advance capacity)^[offset.val] slot) cells[offset.val] heap := by
  induction cells generalizing slot with
  | nil => simp [SequenceRead]
  | cons cell tail ih =>
    rw [SequenceRead, ih]
    constructor
    · rintro ⟨first, rest⟩ offset
      rcases offset with ⟨offset, bound⟩
      cases offset with
      | zero => exact first
      | succ offset =>
        simpa only [List.getElem_cons_succ, Function.iterate_succ_apply] using
          rest ⟨offset, by simpa using bound⟩
    · intro all
      refine ⟨all ⟨0, by simp⟩, ?_⟩
      intro offset
      simpa only [List.getElem_cons_succ, Function.iterate_succ_apply] using
        all ⟨offset.val + 1, by simp⟩

theorem sequenceRead_of_inventory (table : Ptr) (capacity slot : UInt32)
    (inside : slot.toNat < capacity.toNat)
    (inventory : Fin capacity.toNat → Option (Key × UInt32)) (heap : Heap L)
    (reads : ∀ position,
      CellRead table (UInt32.ofNat position.val) (inventory position) heap) :
    SequenceRead table capacity slot
      (DirectoryProbe.sequence inventory ⟨slot.toNat, inside⟩) heap := by
  rw [sequenceRead_iff]
  intro offset
  let position : Fin capacity.toNat :=
    ⟨(slot.toNat + offset.val) % capacity.toNat, Nat.mod_lt _ (by omega)⟩
  have coordinate : UInt32.ofNat position.val = (advance capacity)^[offset.val] slot := by
    have index := advance_iterate_toNat capacity slot inside offset.val
    rw [show position.val = ((advance capacity)^[offset.val] slot).toNat from index.symm]
    exact UInt32.ofNat_toNat
  simpa only [DirectoryProbe.sequence, List.getElem_ofFn, coordinate] using reads position

/-- Successful physical probing agrees with the established independent
finite probe. A read-only libc byte comparison is the only comparison
component contract; the source's guard, header loads, repeated selected-ID
read, and modulo continuation are all executed here. -/
theorem search_returns_probe (compare : EntryMatch.Compare)
    (library : EntryMatch.MemcmpContract (L := L) compare)
    (table bytes : Ptr) (length : UInt32) (hash : UInt64) (query : List UInt8)
    (capacity : UInt32) (nonzero : capacity ≠ 0)
    (queryCount : query.length = length.toNat)
    (cells : InternProbe.Cells Key UInt32) (pre : Heap L → Prop)
    (stops : (InternProbe.probe (hash, query) cells).1 ≠ none ∨
      (InternProbe.probe (hash, query) cells).2 ≠ none)
    (fuel : Nat) (context : Context) (enough : cells.length ≤ fuel)
    (inventory : ∀ heap, pre heap → SequenceRead table capacity context.1 cells heap)
    (capCell : ∀ heap, pre heap → Reads (table + 1) (.u32 capacity) heap)
    (queryLive : ∀ heap, pre heap → Valid heap bytes)
    (querySpan : ∀ heap, pre heap → EntryMatch.Span heap bytes query) :
    CTriple pre (search compare table bytes length hash fuel context)
      (fun result heap => pre heap ∧ ∃ finalSlot,
        result = .finished (.next (finalSlot,
          (InternProbe.probe (hash, query) cells).1.getD context.2))) := by
  induction cells generalizing fuel context with
  | nil => simp [InternProbe.probe] at stops
  | cons cell tail ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      intro heap held
      obtain ⟨readCell, _⟩ := inventory heap held
      change (search compare table bytes length hash (fuel + 1) context).wp act _ heap
      rw [search, ReadBlock.whileWith.eq_def, wp_bind']
      apply guard_wp heap table context cell readCell
      cases cell with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, wp_pure]
        exact ⟨held, context.1, by simp [InternProbe.probe]⟩
      | some pair =>
        rcases pair with ⟨key, identifier⟩
        simp only [Option.isSome_some, ↓reduceIte]
        rw [wp_bind']
        apply iteration_wp compare library heap table bytes length hash query context capacity
          key identifier queryCount (queryLive heap held) (querySpan heap held)
          (capCell heap held) nonzero readCell
        by_cases same : key = (hash, query)
        · simp only [if_pos same, wp_pure]
          exact ⟨held, context.1, by simp [InternProbe.probe, same]⟩
        · simp only [if_neg same]
          have tailStops : (InternProbe.probe (hash, query) tail).1 ≠ none ∨
              (InternProbe.probe (hash, query) tail).2 ≠ none := by
            simpa [InternProbe.probe, Ne.symm same] using stops
          have remainder := ih tailStops fuel (advance capacity context.1, context.2)
            (by simp only [List.length_cons] at enough; omega)
            (fun reached owns => (inventory reached owns).2)
            heap held
          simpa only [search, Prog.wp, InternProbe.probe,
            if_neg (Ne.symm same)] using remainder

/-- Any physical inventory with a vacant slot supplies a stopping point in
one finite turn. This includes the native 7/10 load frontier; neither a
termination result nor the expected identifier is an inventory premise. -/
theorem search_returns_inventory (compare : EntryMatch.Compare)
    (library : EntryMatch.MemcmpContract (L := L) compare)
    (table bytes : Ptr) (length : UInt32) (hash : UInt64) (query : List UInt8)
    (capacity : UInt32) (nonzero : capacity ≠ 0)
    (queryCount : query.length = length.toNat)
    (entries : Fin capacity.toNat → Option (Key × UInt32))
    (loaded : (List.ofFn entries).countP Option.isSome < capacity.toNat)
    (fuel : Nat) (enough : capacity.toNat ≤ fuel) (pre : Heap L → Prop)
    (reads : ∀ heap, pre heap → ∀ position,
      CellRead table (UInt32.ofNat position.val) (entries position) heap)
    (capCell : ∀ heap, pre heap → Reads (table + 1) (.u32 capacity) heap)
    (queryLive : ∀ heap, pre heap → Valid heap bytes)
    (querySpan : ∀ heap, pre heap → EntryMatch.Span heap bytes query) :
    CTriple pre (search compare table bytes length hash fuel (home hash capacity, 0))
      (fun result heap => pre heap ∧ ∃ finalSlot,
        result = .finished (.next (finalSlot,
          (InternProbe.probe (hash, query) (DirectoryProbe.sequence entries
            ⟨(home hash capacity).toNat, home_within hash capacity nonzero⟩)).1.getD 0))) := by
  have vacancy := InternProbe.vacancy_of_count_lt (List.ofFn entries)
    (by simpa only [List.length_ofFn] using loaded)
  obtain ⟨slot, empty⟩ := List.mem_ofFn.mp vacancy
  have stops := InternProbe.stops_if_vacancy (hash, query)
    (DirectoryProbe.sequence entries
      ⟨(home hash capacity).toNat, home_within hash capacity nonzero⟩)
    ((DirectoryProbe.sequence_mem_iff entries _ none).mpr ⟨slot, empty⟩)
  exact search_returns_probe compare library table bytes length hash query capacity nonzero
    queryCount _ pre stops
    fuel (home hash capacity, 0)
    (by simpa only [DirectoryProbe.sequence, List.length_ofFn] using enough)
    (fun heap held => sequenceRead_of_inventory table capacity _
      (home_within hash capacity nonzero) entries heap (reads heap held))
    capCell queryLive querySpan

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.Physical


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

abbrev Context := ObjectBindings.Context
abbrev MutexCall := Bool → Ptr → CProg CVal CVal

def uint32 : CType := ⟨"uint32_t".toList, 0⟩
def uint64 : CType := ⟨"uint64_t".toList, 0⟩
def identityType : CType := ⟨"SymbolId".toList, 0⟩
def slotType : CType := ⟨"SymbolSlot".toList, 0⟩
def slotPointerType : CType := ⟨"SymbolSlot".toList, 1⟩
def tablePointerType : CType := ⟨"SymbolTable".toList, 1⟩
def bytePointerType : CType := ⟨"uint8_t".toList, 1⟩

def layout : Layout := fun name =>
  if name = "slots".toList then some ⟨0, .pointer⟩
  else if name = "slot_cap".toList then some ⟨1, .word⟩
  else if name = "hash".toList then some ⟨0, .word64⟩
  else if name = "id".toList then some ⟨2, .word⟩
  else if name = "write_mutex".toList then some ⟨6, .embedded⟩ else none

/-- The two source helpers use their constructed operation trees. Only the
mutex ABI/service remains external here; libc comparison is isolated inside
the already source-checked entry helper. -/
def calls (compare : EntryMatch.Compare) (mutex : MutexCall) : Calls := fun name values =>
  if name = "symbol_table_entry_ref".toList then
    match values with
    | [.ptr table, .u32 identifier] => entryRef table identifier >>= fun row => pure (.ptr row)
    | _ => CProg.undefined
  else if name = "symbol_entry_matches".toList then
    match values with
    | [.ptr entry, .ptr bytes, .u32 length, .u64 hash] =>
        EntryMatch.operations compare entry bytes length hash >>= fun accepted => pure (.bool accepted)
    | _ => CProg.undefined
  else if name = "pthread_mutex_lock".toList then
    match values with
    | [.ptr (some lock)] => mutex true lock
    | _ => CProg.undefined
  else if name = "pthread_mutex_unlock".toList then
    match values with
    | [.ptr (some lock)] => mutex false lock
    | _ => CProg.undefined
  else CProg.undefined

def profile (compare : EntryMatch.Compare) (mutex : MutexCall) : ObjectBindings.Profile where
  values := calls compare mutex
  locations := fun _ => none
  outsideTypes := fun _ => none
  outsidePlaces := fun _ => none
  fieldTypes := fun type name =>
    if type = ⟨"SymbolTable".toList, 0⟩ ∧ name = "slots".toList then some slotPointerType else none
  cellExtent := fun type => if type = slotType then some 3 else none
  byteExtent := fun _ => none
  sizeWidth := .bits64
  scalarAliases := fun type => if type = identityType then some uint32 else none

def read (compare : EntryMatch.Compare) (mutex : MutexCall)
    (context : Context) (operand : CExpr) : CProg CVal CVal :=
  ObjectBindings.read (profile compare mutex) layout context operand

def services (compare : EntryMatch.Compare) (mutex : MutexCall) : ScopedServices Context :=
  { ObjectBindings.services (profile compare mutex) (fun _ _ _ => CProg.undefined)
      (fun _ context operand => read compare mutex context operand >>= fun _ => pure ())
    with physicalWhile := true }

def scalar (type : CType) (value : CVal) : Option ObjectBindings.Binding :=
  some (.scalar type (some value))

structure Parameters (context : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64) : Prop where
  tableLocal : context "st".toList = scalar tablePointerType (.ptr (some table))
  bytesLocal : context "bytes".toList = scalar bytePointerType (.ptr (some bytes))
  lengthLocal : context "len".toList = scalar uint32 (.u32 length)
  hashLocal : context "hash".toList = scalar uint64 (.u64 hash)
  noneLocal : context "SYMBOL_ID_NONE".toList = scalar identityType (.u32 0)

def loopContext (outer : Context) (state : Physical.Context) : Context :=
  Function.update (Function.update outer "found".toList (scalar identityType (.u32 state.2)))
    "slot".toList (scalar uint32 (.u32 state.1))

def entryContext (outer : Context) (state : Physical.Context) (entry : Ptr) : Context :=
  Function.update (loopContext outer state) "entry".toList
    (scalar slotPointerType (.ptr (some entry)))

theorem read_scalar (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (name : Name) (type : CType) (value : CVal)
    (known : context name = scalar type value) :
    read compare mutex context (.identifier name) = pure value := by
  simp only [read, ObjectBindings.read, expressionWithNames, localOrLocated,
    ObjectBindings.values, known, scalar]

theorem read_named (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (name : String) (type : CType) (value : CVal)
    (known : context name.toList = scalar type value) :
    read compare mutex context (Source.id name) = pure value :=
  read_scalar compare mutex context name.toList type value known

theorem parameters_loop (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (known : Parameters outer table bytes length hash) (state : Physical.Context) :
    Parameters (loopContext outer state) table bytes length hash := by
  constructor
  · change outer "st".toList = _
    exact known.tableLocal
  · change outer "bytes".toList = _
    exact known.bytesLocal
  · change outer "len".toList = _
    exact known.lengthLocal
  · change outer "hash".toList = _
    exact known.hashLocal
  · change outer "SYMBOL_ID_NONE".toList = _
    exact known.noneLocal

theorem parameters_entry (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (known : Parameters outer table bytes length hash) (state : Physical.Context) (entry : Ptr) :
    Parameters (entryContext outer state entry) table bytes length hash := by
  constructor
  · change outer "st".toList = _
    exact known.tableLocal
  · change outer "bytes".toList = _
    exact known.bytesLocal
  · change outer "len".toList = _
    exact known.lengthLocal
  · change outer "hash".toList = _
    exact known.hashLocal
  · change outer "SYMBOL_ID_NONE".toList = _
    exact known.noneLocal

theorem read_table (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (table : Ptr) (known : context "st".toList = scalar tablePointerType (.ptr (some table))) :
    read compare mutex context Source.slots =
      (CProg.loadPtr table >>= fun slots => pure (.ptr slots)) := by
  change (read compare mutex context (Source.id "st") >>= fun owner =>
    ReadExpressions.field layout owner "slots".toList) = _
  rw [read_named compare mutex context _ _ _ known]
  rfl

theorem slot_stride (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (table : Ptr) (known : context "st".toList = scalar tablePointerType (.ptr (some table))) :
    (ObjectBindings.objects (profile compare mutex) context).indexStride Source.slots = some 3 := by
  have typed : ScalarBytes.typeOf?
      (ObjectBindings.types context (profile compare mutex).outsideTypes)
      Source.slots (profile compare mutex).fieldTypes = some slotPointerType := by
    simp only [Source.slots, Source.field, Source.id, ScalarBytes.typeOf?,
      ObjectBindings.types, known, scalar]
    rfl
  change (do
    let type ← ScalarBytes.typeOf?
      (ObjectBindings.types context (profile compare mutex).outsideTypes)
      Source.slots (profile compare mutex).fieldTypes
    match type.pointers with
    | 0 => none
    | depth + 1 => (profile compare mutex).cellExtent ⟨type.name, depth⟩) = _
  rw [typed]
  rfl

theorem indexed_place (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (table : Ptr) (slot : UInt32)
    (tableLocal : context "st".toList = scalar tablePointerType (.ptr (some table)))
    (slotLocal : context "slot".toList = scalar uint32 (.u32 slot)) :
    ObjectBindings.place (profile compare mutex) layout context Source.indexedSlot =
      Physical.slotAddress table slot := by
  change (resolved ((ObjectBindings.objects (profile compare mutex) context).indexStride Source.slots)
    >>= fun stride => read compare mutex context Source.slots >>= fun address =>
      read compare mutex context (Source.id "slot") >>= fun position =>
        indexedPlace stride address position) = _
  rw [slot_stride compare mutex context table tableLocal,
    read_table compare mutex context table tableLocal,
    read_named compare mutex context _ _ _ slotLocal]
  simp only [resolved, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  unfold Physical.slotAddress
  congr 1
  funext slots
  cases slots <;> rfl

theorem read_slot_identity (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (table : Ptr) (slot : UInt32)
    (tableLocal : context "st".toList = scalar tablePointerType (.ptr (some table)))
    (slotLocal : context "slot".toList = scalar uint32 (.u32 slot)) :
    read compare mutex context Source.slotIdentity =
      (Physical.slotAddress table slot >>= fun address =>
        CProg.loadU32 (address + 2) >>= fun identifier => pure (.u32 identifier)) := by
  change (ObjectBindings.place (profile compare mutex) layout context Source.indexedSlot >>=
    fun address => ReadExpressions.field layout (.ptr (some address)) "id".toList) = _
  rw [indexed_place compare mutex context table slot tableLocal slotLocal]
  rfl

theorem actual_guard (compare : EntryMatch.Compare) (mutex : MutexCall) (outer : Context)
    (table bytes : Ptr) (length : UInt32) (hash : UInt64) (state : Physical.Context)
    (known : Parameters outer table bytes length hash) :
    (read compare mutex (loopContext outer state) Source.occupied >>= truth) =
      Physical.guard table state := by
  change ((read compare mutex (loopContext outer state) Source.slotIdentity >>= fun identifier =>
    read compare mutex (loopContext outer state) Source.zero >>= fun absent =>
      binary .ne identifier absent) >>= truth) = _
  have actual := parameters_loop outer table bytes length hash known state
  simp only [Source.zero]
  rw [read_slot_identity compare mutex _ table state.1 actual.tableLocal
      (by simp [loopContext]),
    read_named compare mutex _ _ _ _ actual.noneLocal]
  simp only [Physical.guard, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    binary, equal, ReadExpressions.scalar, ScalarRead.equal?, resolved, truth]
  rfl


theorem read_entry_hash (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (entry : Ptr) (known : context "entry".toList = scalar slotPointerType (.ptr (some entry))) :
    read compare mutex context (Source.field "entry" "hash") =
      (CProg.loadU64 entry >>= fun hash => pure (.u64 hash)) := by
  change (read compare mutex context (Source.id "entry") >>= fun owner =>
    ReadExpressions.field layout owner "hash".toList) = _
  rw [read_named compare mutex context _ _ _ known]
  rfl

theorem read_entry_id (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (entry : Ptr) (known : context "entry".toList = scalar slotPointerType (.ptr (some entry))) :
    read compare mutex context Source.selectedIdentity =
      (CProg.loadU32 (entry + 2) >>= fun identifier => pure (.u32 identifier)) := by
  change (read compare mutex context (Source.id "entry") >>= fun owner =>
    ReadExpressions.field layout owner "id".toList) = _
  rw [read_named compare mutex context _ _ _ known]
  rfl

theorem read_capacity (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (table : Ptr) (known : context "st".toList = scalar tablePointerType (.ptr (some table))) :
    read compare mutex context (Source.field "st" "slot_cap") =
      (CProg.loadU32 (table + 1) >>= fun capacity => pure (.u32 capacity)) := by
  change (read compare mutex context (Source.id "st") >>= fun owner =>
    ReadExpressions.field layout owner "slot_cap".toList) = _
  rw [read_named compare mutex context _ _ _ known]
  rfl

theorem read_call_pair (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (name : Name) (left right : CExpr) :
    read compare mutex context (.call name [left, right]) =
      (read compare mutex context left >>= fun first =>
        read compare mutex context right >>= fun second => calls compare mutex name [first, second]) := by
  unfold read ObjectBindings.read
  rw [expressionWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl

theorem read_call_four (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (name : Name) (a b c d : CExpr) :
    read compare mutex context (.call name [a, b, c, d]) =
      (read compare mutex context a >>= fun first =>
        read compare mutex context b >>= fun second =>
          read compare mutex context c >>= fun third =>
            read compare mutex context d >>= fun fourth =>
              calls compare mutex name [first, second, third, fourth]) := by
  unfold read ObjectBindings.read
  rw [expressionWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  rw [argumentsWithNames.eq_def]
  dsimp only
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl

theorem read_entry_ref_call (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (table entry : Ptr)
    (tableLocal : context "st".toList = scalar tablePointerType (.ptr (some table)))
    (entryLocal : context "entry".toList = scalar slotPointerType (.ptr (some entry))) :
    read compare mutex context (.call "symbol_table_entry_ref".toList
      [Source.id "st", Source.selectedIdentity]) =
      (CProg.loadU32 (entry + 2) >>= fun identifier =>
        entryRef (some table) identifier >>= fun row => pure (.ptr row)) := by
  rw [read_call_pair, read_named compare mutex context _ _ _ tableLocal,
    read_entry_id compare mutex context entry entryLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

theorem read_entry_match_call (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (table bytes entry : Ptr) (length : UInt32) (hash : UInt64)
    (known : Parameters context table bytes length hash)
    (entryLocal : context "entry".toList = scalar slotPointerType (.ptr (some entry))) :
    (read compare mutex context (.call "symbol_entry_matches".toList
      [.call "symbol_table_entry_ref".toList [Source.id "st", Source.selectedIdentity],
       Source.id "bytes", Source.id "len", Source.id "hash"]) >>= truth) =
      (CProg.loadU32 (entry + 2) >>= fun identifier =>
        entryRef (some table) identifier >>= fun row =>
          EntryMatch.operations compare row (some bytes) length hash) := by
  rw [read_call_four,
    read_entry_ref_call compare mutex context table entry known.tableLocal entryLocal,
    read_named compare mutex context _ _ _ known.bytesLocal,
    read_named compare mutex context _ _ _ known.lengthLocal,
    read_named compare mutex context _ _ _ known.hashLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext identifier
  congr 1
  funext row
  change ((EntryMatch.operations compare row (some bytes) length hash >>= fun accepted =>
    (pure (.bool accepted) : CProg CVal CVal)) >>= truth) = _
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth, Prog.bind_ret]

theorem actual_slot_test (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (table bytes entry : Ptr) (length : UInt32) (hash : UInt64)
    (known : Parameters context table bytes length hash)
    (entryLocal : context "entry".toList = scalar slotPointerType (.ptr (some entry))) :
    (read compare mutex context Source.slotMatches >>= truth) =
      (do let candidateHash ← CProg.loadU64 entry
          if candidateHash == hash then do
            let identifier ← CProg.loadU32 (entry + 2)
            let row ← entryRef (some table) identifier
            EntryMatch.operations compare row (some bytes) length hash
          else pure false) := by
  have first : read compare mutex context
      (.binary .eq (Source.field "entry" "hash") (Source.id "hash")) =
      (CProg.loadU64 entry >>= fun actual => pure (.bool (actual == hash))) := by
    change (read compare mutex context (Source.field "entry" "hash") >>= fun value =>
      read compare mutex context (Source.id "hash") >>= fun wanted => binary .eq value wanted) = _
    rw [read_entry_hash compare mutex context entry entryLocal,
      read_named compare mutex context _ _ _ known.hashLocal]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    rfl
  change ((do
    let initial ← read compare mutex context
      (.binary .eq (Source.field "entry" "hash") (Source.id "hash"))
    let selected ← truth initial
    if selected then do
      let second ← read compare mutex context
        (.call "symbol_entry_matches".toList
          [.call "symbol_table_entry_ref".toList [Source.id "st", Source.selectedIdentity],
           Source.id "bytes", Source.id "len", Source.id "hash"])
      let accepted ← truth second
      pure (CVal.bool accepted)
    else pure (CVal.bool false)) >>= truth) = _
  rw [first]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext candidateHash
  by_cases selected : (candidateHash == hash) = true
  · simp only [selected, ↓reduceIte, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth, Prog.bind_ret]
    exact read_entry_match_call compare mutex context table bytes entry length hash known entryLocal
  · simp only [Bool.eq_false_iff.mpr selected, Bool.false_eq_true, ↓reduceIte,
      Prog.pure_eq, Prog.ret_bind, truth]

theorem read_advance (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (table : Ptr) (slot : UInt32)
    (tableLocal : context "st".toList = scalar tablePointerType (.ptr (some table)))
    (slotLocal : context "slot".toList = scalar uint32 (.u32 slot)) :
    read compare mutex context Source.advance =
      (CProg.loadU32 (table + 1) >>= fun capacity =>
        if capacity = 0 then CProg.undefined else pure (.u32 (advance capacity slot))) := by
  change ((read compare mutex context (Source.id "slot") >>= fun current =>
    (pure (.i32 1) : CProg CVal CVal) >>= fun one => binary .add current one) >>= fun incremented =>
      read compare mutex context (Source.field "st" "slot_cap") >>= fun capacity =>
        binary .mod incremented capacity) = _
  rw [read_named compare mutex context _ _ _ slotLocal,
    read_capacity compare mutex context table tableLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  change (CProg.loadU32 (table + 1) >>= fun capacity =>
    binary .mod (.u32 (slot + 1)) (.u32 capacity)) = _
  congr 1
  funext capacity
  by_cases zero : capacity = 0
  · simp only [zero, ↓reduceIte]
    rfl
  · simp only [zero, ↓reduceIte]
    change resolved ((if capacity = 0 then none else
      some (ScalarRead.Value.unsigned ((slot + 1) % capacity))).bind cell?) = _
    rw [if_neg zero]
    rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- This factorization keeps the source's guarded helper calls, rather than
replacing them by the mathematical key predicate. -/
def slotTest (compare : EntryMatch.Compare) (table bytes entry : Ptr)
    (length : UInt32) (hash : UInt64) : CProg CVal Bool := do
  let candidateHash ← CProg.loadU64 entry
  if candidateHash == hash then do
    let identifier ← CProg.loadU32 (entry + 2)
    let row ← entryRef (some table) identifier
    EntryMatch.operations compare row (some bytes) length hash
  else pure false

theorem iteration_factors_slot_test (compare : EntryMatch.Compare) (table bytes : Ptr)
    (length : UInt32) (hash : UInt64) (state : Physical.Context) :
    Physical.iteration compare table bytes length hash state =
      (do let entry ← Physical.slotAddress table state.1
          let accepted ← slotTest compare table bytes entry length hash
          if accepted then do
            let identifier ← CProg.loadU32 (entry + 2)
            pure (.finished (.broken (state.1, identifier)))
          else Physical.next table state) := by
  simp only [Physical.iteration, slotTest, Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext entry
  congr 1
  funext candidateHash
  by_cases same : (candidateHash == hash) = true
  · simp only [same, ↓reduceIte, Prog.bind_assoc]
  · simp only [Bool.eq_false_iff.mpr same, Bool.false_eq_true, ↓reduceIte,
      Prog.pure_eq, Prog.ret_bind]

theorem read_slot_address (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (table : Ptr) (slot : UInt32)
    (tableLocal : context "st".toList = scalar tablePointerType (.ptr (some table)))
    (slotLocal : context "slot".toList = scalar uint32 (.u32 slot)) :
    read compare mutex context (.unary .address Source.indexedSlot) =
      (Physical.slotAddress table slot >>= fun address => pure (.ptr (some address))) := by
  change (ObjectBindings.place (profile compare mutex) layout context Source.indexedSlot >>=
    fun address => pure (CVal.ptr (some address))) = _
  rw [indexed_place compare mutex context table slot tableLocal slotLocal]

theorem local_type (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (name : String) (type : CType) (value : CVal)
    (known : context name.toList = scalar type value) :
    ScalarBytes.typeOf? (ObjectBindings.types context (profile compare mutex).outsideTypes)
      (Source.id name) (profile compare mutex).fieldTypes = some type := by
  simp only [Source.id, ScalarBytes.typeOf?, ObjectBindings.types, known, scalar]

theorem found_assignment (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (entry : Ptr) (previous : UInt32)
    (entryLocal : context "entry".toList = scalar slotPointerType (.ptr (some entry)))
    (foundLocal : context "found".toList = scalar identityType (.u32 previous)) :
    (services compare mutex).assignment layout context
      (.assign (Source.id "found") Source.selectedIdentity) =
      (CProg.loadU32 (entry + 2) >>= fun identifier =>
        pure (Function.update context "found".toList (scalar identityType (.u32 identifier)))) := by
  dsimp only [services, ObjectBindings.services]
  rw [ObjectBindings.scalar_assignment_retains_read_and_conversion _ _ _ _ _ identityType
    (local_type compare mutex context "found" identityType (.u32 previous) foundLocal) (by rfl)]
  change (read compare mutex context Source.selectedIdentity >>= _) = _
  rw [read_entry_id compare mutex context entry entryLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext identifier
  unfold Source.id
  rw [ObjectBindings.local_scalar_write_refines_existing_inventory _ _ _ _ identityType
    (some (.u32 previous)) (.u32 identifier) foundLocal]
  rfl

theorem slot_assignment (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (table : Ptr) (slot : UInt32)
    (tableLocal : context "st".toList = scalar tablePointerType (.ptr (some table)))
    (slotLocal : context "slot".toList = scalar uint32 (.u32 slot)) :
    (services compare mutex).assignment layout context
      (.assign (Source.id "slot") Source.advance) =
      (CProg.loadU32 (table + 1) >>= fun capacity =>
        if capacity = 0 then CProg.undefined else
          pure (Function.update context "slot".toList
            (scalar uint32 (.u32 (advance capacity slot))))) := by
  dsimp only [services, ObjectBindings.services]
  rw [ObjectBindings.scalar_assignment_retains_read_and_conversion _ _ _ _ _ uint32
    (local_type compare mutex context "slot" uint32 (.u32 slot) slotLocal) (by rfl)]
  change (read compare mutex context Source.advance >>= _) = _
  rw [read_advance compare mutex context table slot tableLocal slotLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext capacity
  by_cases zero : capacity = 0
  · simp only [if_pos zero]
    exact undefined_bind _
  · simp only [if_neg zero, Prog.pure_eq, Prog.ret_bind]
    unfold Source.id
    rw [ObjectBindings.local_scalar_write_refines_existing_inventory _ _ _ _ uint32
      (some (.u32 slot)) (.u32 (advance capacity slot)) slotLocal]
    rfl

theorem restore_entry_after_found (outer : Context) (state : Physical.Context)
    (entry : Ptr) (selected : UInt32) :
    Function.update (Function.update (entryContext outer state entry) "found".toList
      (scalar identityType (.u32 selected))) "entry".toList
      (loopContext outer state "entry".toList) = loopContext outer (state.1, selected) := by
  funext name
  simp only [entryContext, loopContext, Function.update_apply]
  split_ifs <;> simp_all

theorem restore_entry_after_slot (outer : Context) (state : Physical.Context)
    (entry : Ptr) (next : UInt32) :
    Function.update (Function.update (entryContext outer state entry) "slot".toList
      (scalar uint32 (.u32 next))) "entry".toList
      (loopContext outer state "entry".toList) = loopContext outer (next, state.2) := by
  funext name
  simp only [entryContext, loopContext, Function.update_apply]
  split_ifs <;> simp_all

private theorem branch_control (compare : EntryMatch.Compare) (mutex : MutexCall)
    (allowance fuel : Nat) (context : Context) (condition : CExpr)
    (yes no rest : List CStatement) :
    executeScopedWith (services compare mutex) layout allowance (fuel + 1) context
      (.branch condition yes no :: rest) =
      ((read compare mutex context condition >>= truth) >>= fun selected =>
        executeScopedWith (services compare mutex) layout allowance fuel context
          (if selected then yes else no) >>= ReadBlock.resume
            (fun reached => executeScopedWith (services compare mutex) layout allowance fuel reached rest)) := by
  rw [executeScopedWith.eq_def]
  simp only [services, Prog.bind_eq, Prog.bind_assoc]
  rfl

/-- The exact parsed iteration uses the declared temporary pointer, actual
condition and selected assignment, then restores that temporary. All older
locals and the reached slot/found values survive in their actual scopes. -/
theorem actual_iteration (compare : EntryMatch.Compare) (mutex : MutexCall)
    (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (state : Physical.Context) (allowance : Nat)
    (known : Parameters outer table bytes length hash) :
    executeScopedWith (services compare mutex) layout allowance 8
      (loopContext outer state) Source.iteration =
      (Physical.iteration compare table bytes length hash state >>= fun result =>
        pure (result.mapContext (loopContext outer))) := by
  rw [iteration_factors_slot_test]
  unfold Source.iteration
  rw [PointeeConstControls.typed_pointer_keeps_declaration_provider _ _ _ 7 _ _ _ _ _ (by rfl) (by rfl)]
  rw [scoped_initialized_declaration_keeps_continuation]
  dsimp only [services, ObjectBindings.services]
  rw [ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow _ _ _ _ _ _ _ (by rfl)]
  change (read compare mutex (loopContext outer state) (.unary .address Source.indexedSlot) >>= _) = _
  rw [read_slot_address compare mutex _ table state.1
    (parameters_loop outer table bytes length hash known state).tableLocal (by rfl)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext entry
  change (executeScopedWith (services compare mutex) layout allowance 7
    (entryContext outer state entry)
    [.branch Source.slotMatches [.assign (Source.id "found") Source.selectedIdentity, .break] [],
     .assign (Source.id "slot") Source.advance] >>= fun result =>
       pure (ObjectBindings.restore "entry".toList (loopContext outer state "entry".toList) result)) = _
  rw [branch_control, actual_slot_test compare mutex _ table bytes entry length hash
    (parameters_entry outer table bytes length hash known state entry) (by rfl)]
  change ((slotTest compare table bytes entry length hash >>= _) >>= _) = _
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext accepted
  cases accepted with
  | true =>
    simp only [↓reduceIte]
    rw [scoped_assignment_keeps_continuation,
      found_assignment compare mutex _ entry state.2 (by rfl) (by rfl)]
    simp only [Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext selected
    change (pure (ObjectBindings.restore "entry".toList (loopContext outer state "entry".toList)
      (.finished (.broken (Function.update (entryContext outer state entry) "found".toList
        (scalar identityType (.u32 selected)))))) : CProg CVal (ReadBlock.Result Context)) = _
    simp only [ObjectBindings.restore, ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext,
      restore_entry_after_found, Prog.pure_eq, Prog.ret_bind]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (executeScopedWith (services compare mutex) layout allowance 6
      (entryContext outer state entry) [.assign (Source.id "slot") Source.advance] >>= fun result =>
        pure (ObjectBindings.restore "entry".toList (loopContext outer state "entry".toList) result)) = _
    rw [scoped_assignment_keeps_continuation,
      slot_assignment compare mutex _ table state.1
        (parameters_entry outer table bytes length hash known state entry).tableLocal (by rfl)]
    unfold Physical.next
    simp only [Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext capacity
    by_cases zero : capacity = 0
    · simp only [if_pos zero]
      trans CProg.undefined
      · exact undefined_bind _
      · exact (undefined_bind _).symm
    · simp only [if_neg zero, Prog.pure_eq, Prog.ret_bind]
      change (pure (ObjectBindings.restore "entry".toList (loopContext outer state "entry".toList)
        (.finished (.next (Function.update (entryContext outer state entry) "slot".toList
          (scalar uint32 (.u32 (advance capacity state.1))))))) :
          CProg CVal (ReadBlock.Result Context)) = _
      simp only [ObjectBindings.restore, ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext,
        restore_entry_after_slot]
      rfl

theorem actual_loop_uses_search (compare : EntryMatch.Compare) (mutex : MutexCall)
    (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (state : Physical.Context) (allowance : Nat)
    (known : Parameters outer table bytes length hash) :
    ReadBlock.whileWith
      (fun context => read compare mutex context Source.occupied >>= truth)
      (fun context => executeScopedWith (services compare mutex) layout allowance 8 context Source.iteration)
      allowance (loopContext outer state) =
      (Physical.search compare table bytes length hash allowance state >>= fun result =>
        pure (result.mapContext (loopContext outer))) :=
  ReadBlock.while_context_extension (loopContext outer) (Physical.guard table)
    (Physical.iteration compare table bytes length hash) _ _
    (fun reached => actual_guard compare mutex outer table bytes length hash reached known)
    (fun reached => actual_iteration compare mutex outer table bytes length hash reached allowance known)
    allowance state

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.Languages.C11

/-- Home calculation retains the actual capacity load and the source's
wide remainder followed by its explicit narrowing cast. -/
def homeProgram (table : Ptr) (hash : UInt64) : CProg CVal UInt32 := do
  let capacity ← CProg.loadU32 (table + 1)
  if capacity = 0 then CProg.undefined else pure (home hash capacity)

theorem actual_home_expression (compare : EntryMatch.Compare) (mutex : MutexCall)
    (context : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (known : Parameters context table bytes length hash) :
    read compare mutex context Source.hashHome =
      (homeProgram table hash >>= fun slot => pure (.u32 slot)) := by
  change ((read compare mutex context (Source.id "hash") >>= fun hashValue =>
    read compare mutex context (Source.field "st" "slot_cap") >>= fun capacity =>
      binary .mod hashValue capacity) >>= unsignedCast uint32) = _
  rw [read_named compare mutex context _ _ _ known.hashLocal,
    read_capacity compare mutex context table known.tableLocal]
  simp only [homeProgram, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext capacity
  by_cases zero : capacity = 0
  · subst capacity
    change (CProg.undefined >>= unsignedCast uint32) = (CProg.undefined >>= _)
    trans CProg.undefined
    · exact undefined_bind _
    · exact (undefined_bind _).symm
  · rw [if_neg zero]
    have actual := (ScalarRead.SymbolLookupArithmetic.hash_capacity_remainder_implements_c11
      (Ptr := Ptr) hash capacity zero (signalingPolicy 0)).1
    change (resolved ((ScalarRead.numericBinary .mod (.unsigned64 hash)
      (.unsigned capacity)).bind cell?) >>= unsignedCast uint32) = _
    rw [actual]
    change unsignedCast uint32 (.u64 (hash % UInt64.ofNat capacity.toNat)) = _
    exact unsignedCast32_of_u64 _

private theorem resume_empty (result : ReadBlock.Result Context)
    (compare : EntryMatch.Compare) (mutex : MutexCall) (allowance fuel : Nat) :
    ReadBlock.resume
      (fun reached => executeScopedWith (services compare mutex) layout allowance fuel reached []) result =
      pure result := by
  cases result with
  | exhausted => rfl
  | finished flow => cases flow <;> simp only [ReadBlock.resume, executeScopedWith.eq_def]

theorem actual_while_statement (compare : EntryMatch.Compare) (mutex : MutexCall)
    (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (state : Physical.Context) (allowance : Nat)
    (known : Parameters outer table bytes length hash) :
    executeScopedWith (services compare mutex) layout allowance 9
      (loopContext outer state) [.whileLoop Source.occupied Source.iteration] =
      (Physical.search compare table bytes length hash allowance state >>= fun result =>
        pure (result.mapContext (loopContext outer))) := by
  rw [show 9 = 8 + 1 from rfl,
    scoped_while_keeps_guard_body_and_continuation _ _ _ _ _ _ _ _ (by rfl)]
  change (ReadBlock.whileWith
    (fun context => read compare mutex context Source.occupied >>= truth)
    (fun context => executeScopedWith (services compare mutex) layout allowance 8 context Source.iteration)
    allowance (loopContext outer state) >>= _) = _
  rw [actual_loop_uses_search compare mutex outer table bytes length hash state allowance known]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext result
  exact resume_empty _ compare mutex allowance 8

def foundContext (outer : Context) (selected : UInt32) : Context :=
  Function.update outer "found".toList (scalar identityType (.u32 selected))

theorem parameters_found (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (known : Parameters outer table bytes length hash) (selected : UInt32) :
    Parameters (foundContext outer selected) table bytes length hash := by
  constructor
  · change outer "st".toList = _
    exact known.tableLocal
  · change outer "bytes".toList = _
    exact known.bytesLocal
  · change outer "len".toList = _
    exact known.lengthLocal
  · change outer "hash".toList = _
    exact known.hashLocal
  · change outer "SYMBOL_ID_NONE".toList = _
    exact known.noneLocal

theorem restore_slot_context (outer : Context) (state : Physical.Context) (previous : UInt32) :
    Function.update (loopContext outer state) "slot".toList
      (foundContext outer previous "slot".toList) = foundContext outer state.2 := by
  funext name
  simp only [loopContext, foundContext, Function.update_apply]
  split_ifs <;> simp_all

theorem restore_slot_result (outer : Context) (previous : UInt32)
    (result : ReadBlock.Result Physical.Context) :
    ObjectBindings.restore "slot".toList (foundContext outer previous "slot".toList)
      (result.mapContext (loopContext outer)) =
      result.mapContext (fun state => foundContext outer state.2) := by
  cases result with
  | exhausted => rfl
  | finished flow => cases flow <;>
      simp only [ObjectBindings.restore, ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext,
        restore_slot_context]

/-- The actual slot declaration is scoped around the entire physical loop.
The previous slot binding is restored; the caller-visible found local keeps
the selected ID. Exhaustion remains explicit and never fabricates that ID. -/
theorem actual_search_block (compare : EntryMatch.Compare) (mutex : MutexCall)
    (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (previous : UInt32) (allowance : Nat)
    (known : Parameters outer table bytes length hash) :
    executeScopedWith (services compare mutex) layout allowance 10
      (foundContext outer previous)
      [.declare uint32 "slot".toList Source.hashHome,
       .whileLoop Source.occupied Source.iteration] =
      (homeProgram table hash >>= fun slot =>
        Physical.search compare table bytes length hash allowance (slot, previous) >>= fun result =>
          pure (result.mapContext (fun state => foundContext outer state.2))) := by
  rw [show 10 = 9 + 1 from rfl, scoped_initialized_declaration_keeps_continuation]
  dsimp only [services, ObjectBindings.services]
  rw [ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow _ _ _ _ _ _ _ (by rfl)]
  change (read compare mutex (foundContext outer previous) Source.hashHome >>= _) = _
  rw [actual_home_expression compare mutex (foundContext outer previous) table bytes length hash
    (parameters_found outer table bytes length hash known previous)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext slot
  change (executeScopedWith (services compare mutex) layout allowance 9
    (loopContext outer (slot, previous)) [.whileLoop Source.occupied Source.iteration] >>= fun result =>
      pure (ObjectBindings.restore "slot".toList (foundContext outer previous "slot".toList) result)) = _
  rw [actual_while_statement compare mutex outer table bytes length hash (slot, previous) allowance known]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, restore_slot_result]

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

private theorem branch_source (compare : EntryMatch.Compare) (mutex : MutexCall)
    (allowance fuel : Nat) (context : Context) (condition : CExpr)
    (yes no rest : List CStatement) :
    executeScopedWith (services compare mutex) layout allowance (fuel + 1) context
      (.branch condition yes no :: rest) =
      ((read compare mutex context condition >>= truth) >>= fun selected =>
        executeScopedWith (services compare mutex) layout allowance fuel context
          (if selected then yes else no) >>= ReadBlock.resume
            (fun reached => executeScopedWith (services compare mutex) layout allowance fuel reached rest)) := by
  rw [executeScopedWith.eq_def]
  simp only [services, Prog.bind_eq, Prog.bind_assoc]
  rfl

private theorem or_truth (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (left right : CExpr) :
    (read compare mutex context (.binary .or left right) >>= truth) =
      ((read compare mutex context left >>= truth) >>= fun selected =>
        if selected then pure true else read compare mutex context right >>= truth) := by
  change ((do
    let first ← read compare mutex context left
    let selected ← truth first
    if selected then pure (CVal.bool true) else do
      let second ← read compare mutex context right
      let answer ← truth second
      pure (CVal.bool answer)) >>= truth) = _
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext first
  congr 1
  funext selected
  cases selected <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext second
  change (truth second).bind Prog.ret = truth second
  exact Prog.bind_ret _

private theorem not_pointer (compare : EntryMatch.Compare) (mutex : MutexCall) (context : Context)
    (name : String) (type : CType) (pointer : Option Ptr)
    (known : context name.toList = scalar type (.ptr pointer)) :
    (read compare mutex context (.unary .not (Source.id name)) >>= truth) =
      CProg.ptrEq pointer none := by
  change ((read compare mutex context (Source.id name) >>= fun actual =>
    truth actual >>= fun yes => pure (CVal.bool (!yes))) >>= truth) = _
  rw [read_named compare mutex context name type (.ptr pointer) known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, truth, Prog.bind_assoc,
    Bool.not_not, Prog.bind_ret]

/-- The authored short-circuit input guard performs its two validity-checked
pointer tests before observing length. It does not turn a dangling pointer
into the public absent-symbol result. -/
def badInputProgram (table bytes : Ptr) (length : UInt32) : CProg CVal Bool := do
  let tableNull ← CProg.ptrEq (some table) none
  if tableNull then pure true else do
    let bytesNull ← CProg.ptrEq (some bytes) none
    if bytesNull then pure true else pure (length == 0)

theorem actual_input_guard (compare : EntryMatch.Compare) (mutex : MutexCall)
    (context : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (known : Parameters context table bytes length hash) :
    (read compare mutex context Source.badInput >>= truth) = badInputProgram table bytes length := by
  have notLength : (read compare mutex context (.unary .not (Source.id "len")) >>= truth) =
      pure (length == 0) := by
    change ((read compare mutex context (Source.id "len") >>= fun actual =>
      truth actual >>= fun yes => pure (CVal.bool (!yes))) >>= truth) = _
    rw [read_named compare mutex context "len" uint32 (.u32 length) known.lengthLocal]
    simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, truth, bne, Bool.not_not]
  unfold Source.badInput
  rw [or_truth, or_truth,
    not_pointer compare mutex context "st" tablePointerType (some table) known.tableLocal,
    not_pointer compare mutex context "bytes" bytePointerType (some bytes) known.bytesLocal,
    notLength]
  simp only [badInputProgram, Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext tableNull
  cases tableNull <;> simp only [Bool.false_eq_true, ↓reduceIte, Prog.pure_eq, Prog.ret_bind]

theorem read_mutex_call (compare : EntryMatch.Compare) (mutex : MutexCall)
    (context : Context) (table : Ptr) (lock : Bool)
    (known : context "st".toList = scalar tablePointerType (.ptr (some table))) :
    read compare mutex context
      (.call (if lock then "pthread_mutex_lock".toList else "pthread_mutex_unlock".toList)
        [Source.lockAddress]) = mutex lock (table + 6) := by
  have address : read compare mutex context Source.lockAddress =
      pure (.ptr (some (table + 6))) := by
    change (read compare mutex context (Source.id "st") >>= fun owner =>
      fieldAddress layout owner "write_mutex".toList >>= fun address => pure (CVal.ptr (some address))) = _
    rw [read_named compare mutex context "st" tablePointerType _ known]
    rfl
  have callOne (name : Name) : read compare mutex context (.call name [Source.lockAddress]) =
      (read compare mutex context Source.lockAddress >>= fun value => calls compare mutex name [value]) := by
    unfold read ObjectBindings.read
    rw [expressionWithNames.eq_def]
    dsimp only
    rw [argumentsWithNames.eq_def]
    dsimp only
    rw [argumentsWithNames.eq_def]
    dsimp only
    simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
    rfl
  rw [callOne, address]
  cases lock <;> rfl

/-- The source ignores the mutex return value but retains its actual operation
and effects. A success/acquire contract is supplied separately when proving
lookup from an independently published table. -/
theorem mutex_effect (compare : EntryMatch.Compare) (mutex : MutexCall)
    (context : Context) (table : Ptr) (lock : Bool)
    (known : context "st".toList = scalar tablePointerType (.ptr (some table))) :
    (services compare mutex).effect layout context
      (.call (if lock then "pthread_mutex_lock".toList else "pthread_mutex_unlock".toList)
        [Source.lockAddress]) = (mutex lock (table + 6) >>= fun _ => pure ()) := by
  change (read compare mutex context _ >>= fun _ => pure ()) = _
  rw [read_mutex_call compare mutex context table lock known]

def ending : List CStatement :=
  [.effect (.call "pthread_mutex_unlock".toList [Source.lockAddress]),
   .return (some (Source.id "found"))]

theorem actual_unlock_and_return (compare : EntryMatch.Compare) (mutex : MutexCall)
    (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (selected : UInt32) (allowance fuel : Nat)
    (known : Parameters outer table bytes length hash) :
    executeScopedWith (services compare mutex) layout allowance (fuel + 2)
      (foundContext outer selected) ending =
      (mutex false (table + 6) >>= fun _ =>
        pure (.finished (.returned (foundContext outer selected) (some (.u32 selected))))) := by
  unfold ending
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl, scoped_effect_keeps_continuation]
  have known' := parameters_found outer table bytes length hash known selected
  rw [show (services compare mutex).effect layout (foundContext outer selected)
      (.call "pthread_mutex_unlock".toList [Source.lockAddress]) =
      (mutex false (table + 6) >>= fun _ => pure ()) from
    mutex_effect compare mutex _ table false known'.tableLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1

def finishSearch (mutex : MutexCall) (table : Ptr) : ReadBlock.Result Physical.Context →
    CProg CVal (ReadBlock.Result Unit)
  | .exhausted => pure .exhausted
  | .finished (.next (_, selected)) =>
      mutex false (table + 6) >>= fun _ => pure (.finished (.returned () (some (.u32 selected))))
  | .finished (.broken _) => pure (.finished (.broken ()))
  | .finished (.returned _ value) => pure (.finished (.returned () value))

theorem restore_found (outer : Context) (selected : UInt32) :
    Function.update (foundContext outer selected) "found".toList (outer "found".toList) = outer := by
  funext name
  simp only [foundContext, Function.update_apply]
  split_ifs <;> simp_all

theorem finish_search_scope (compare : EntryMatch.Compare) (mutex : MutexCall)
    (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (allowance fuel : Nat) (result : ReadBlock.Result Physical.Context)
    (known : Parameters outer table bytes length hash) :
    (ReadBlock.resume
      (fun reached => executeScopedWith (services compare mutex) layout allowance (fuel + 2) reached ending)
      (result.mapContext (fun state => foundContext outer state.2)) >>= fun reached =>
        pure (ObjectBindings.restore "found".toList (outer "found".toList) reached)) =
      (finishSearch mutex table result >>= fun reached => pure (reached.mapContext (fun _ => outer))) := by
  cases result with
  | exhausted => rfl
  | finished flow =>
    cases flow with
    | next state =>
      simp only [ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext, ReadBlock.resume]
      rw [actual_unlock_and_return compare mutex outer table bytes length hash state.2 allowance fuel known]
      simp only [finishSearch, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
        ObjectBindings.restore, ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext, restore_found]
    | broken state =>
      simp only [ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext, ReadBlock.resume,
        finishSearch, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, ObjectBindings.restore, restore_found]
    | returned state value =>
      simp only [ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext, ReadBlock.resume,
        finishSearch, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, ObjectBindings.restore, restore_found]

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

private theorem lookup_branch_control (compare : EntryMatch.Compare) (mutex : MutexCall)
    (allowance fuel : Nat) (context : Context) (condition : CExpr)
    (yes no rest : List CStatement) :
    executeScopedWith (services compare mutex) layout allowance (fuel + 1) context
      (.branch condition yes no :: rest) =
      ((read compare mutex context condition >>= truth) >>= fun selected =>
        executeScopedWith (services compare mutex) layout allowance fuel context
          (if selected then yes else no) >>= ReadBlock.resume
            (fun reached => executeScopedWith (services compare mutex) layout allowance fuel reached rest)) := by
  rw [executeScopedWith.eq_def]
  simp only [services, Prog.bind_eq, Prog.bind_assoc]
  rfl

/-- The source's control after its input guard. Both capacity reads, the
actual lookup loop, and exactly the selected unlock continuation remain here.
An exhausted body does not manufacture a successful unlock or return. -/
def afterGuardProgram (compare : EntryMatch.Compare) (mutex : MutexCall)
    (table bytes : Ptr) (length : UInt32) (hash : UInt64) (allowance : Nat) :
    CProg CVal (ReadBlock.Result Unit) := do
  let _ ← mutex true (table + 6)
  let capacity ← CProg.loadU32 (table + 1)
  if capacity != 0 then do
    let slot ← homeProgram table hash
    let result ← Physical.search compare table bytes length hash allowance (slot, 0)
    finishSearch mutex table result
  else do
    let _ ← mutex false (table + 6)
    pure (.finished (.returned () (some (.u32 0))))

theorem actual_after_guard (compare : EntryMatch.Compare) (mutex : MutexCall)
    (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64) (allowance : Nat)
    (known : Parameters outer table bytes length hash) :
    executeScopedWith (services compare mutex) layout allowance 13 outer Source.body.tail =
      (afterGuardProgram compare mutex table bytes length hash allowance >>= fun result =>
        pure (result.mapContext (fun _ => outer))) := by
  unfold Source.body
  simp only [List.tail_cons]
  rw [show 13 = 12 + 1 from rfl, scoped_initialized_declaration_keeps_continuation]
  dsimp only [services, ObjectBindings.services]
  rw [ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow _ _ _ _ _ _ _ (by rfl)]
  change (read compare mutex outer Source.zero >>= _) = _
  unfold Source.zero
  rw [read_named compare mutex outer _ _ _ known.noneLocal]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  change (executeScopedWith (services compare mutex) layout allowance 12 (foundContext outer 0)
    [.effect (.call "pthread_mutex_lock".toList [Source.lockAddress]),
     .branch (Source.field "st" "slot_cap")
       [.declare uint32 "slot".toList Source.hashHome, .whileLoop Source.occupied Source.iteration] [],
     .effect (.call "pthread_mutex_unlock".toList [Source.lockAddress]),
     .return (some (Source.id "found"))] >>= fun result =>
       pure (ObjectBindings.restore "found".toList (outer "found".toList) result)) = _
  rw [scoped_effect_keeps_continuation]
  have parameters := parameters_found outer table bytes length hash known 0
  rw [show (services compare mutex).effect layout (foundContext outer 0)
      (.call "pthread_mutex_lock".toList [Source.lockAddress]) =
      (mutex true (table + 6) >>= fun _ => pure ()) from
    mutex_effect compare mutex _ table true parameters.tableLocal]
  unfold afterGuardProgram
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext ignored
  rw [lookup_branch_control, read_capacity compare mutex _ table parameters.tableLocal]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext capacity
  cases active : (capacity != 0) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (executeScopedWith (services compare mutex) layout allowance 10 (foundContext outer 0) ending >>=
      fun result => pure (ObjectBindings.restore "found".toList (outer "found".toList) result)) = _
    rw [show 10 = 8 + 2 from rfl,
      actual_unlock_and_return compare mutex outer table bytes length hash 0 allowance 8 known]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
      ObjectBindings.restore, ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext, restore_found]
  | true =>
    simp only [↓reduceIte]
    rw [actual_search_block compare mutex outer table bytes length hash 0 allowance known]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    congr 1
    funext slot
    congr 1
    funext result
    exact finish_search_scope compare mutex outer table bytes length hash allowance 8 result known

/-- Full logical operation tree of the actual source body. This uses the
maintained scalar-cell ABI and explicit mutex/libc components; it is not a
claim about arbitrary native C execution or concurrent table mutation. -/
def lookupProgram (compare : EntryMatch.Compare) (mutex : MutexCall)
    (table bytes : Ptr) (length : UInt32) (hash : UInt64) (allowance : Nat) :
    CProg CVal (ReadBlock.Result Unit) := do
  let bad ← badInputProgram table bytes length
  if bad then pure (.finished (.returned () (some (.u32 0))))
  else afterGuardProgram compare mutex table bytes length hash allowance

/-- The complete, actually parsed function body is the retained operation
tree above. Every pointer guard, typed declaration, nested helper call,
selected branch, scoped local, mutex call and return is retained. -/
theorem actual_lookup_body (compare : EntryMatch.Compare) (mutex : MutexCall)
    (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64) (allowance : Nat)
    (known : Parameters outer table bytes length hash) :
    executeScopedWith (services compare mutex) layout allowance 14 outer Source.body =
      (lookupProgram compare mutex table bytes length hash allowance >>= fun result =>
        pure (result.mapContext (fun _ => outer))) := by
  change executeScopedWith _ _ _ _ _
    (.branch Source.badInput [.return (some Source.zero)] [] :: Source.body.tail) = _
  rw [show 14 = 13 + 1 from rfl, lookup_branch_control,
    actual_input_guard compare mutex outer table bytes length hash known]
  unfold lookupProgram
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext bad
  cases bad with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    change executeScopedWith (services compare mutex) layout allowance 13 outer Source.body.tail = _
    exact actual_after_guard compare mutex outer table bytes length hash allowance known
  | true =>
    simp only [↓reduceIte]
    rw [executeScopedWith.eq_def]
    change ((read compare mutex outer Source.zero >>= fun value =>
      pure (ReadBlock.Result.finished (.returned outer (some value)))) >>= _) = _
    unfold Source.zero
    rw [read_named compare mutex outer _ _ _ known.noneLocal]
    rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.IncrementalConformance
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

variable {L : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- The expected ID is read from the independently supplied finite physical
inventory, not from the function's execution or a callback response. -/
def inventoryID (capacity : UInt32) (nonzero : capacity ≠ 0)
    (entries : Fin capacity.toNat → Option (Physical.Key × UInt32))
    (hash : UInt64) (query : List UInt8) : UInt32 :=
  (InternProbe.probe (hash, query) (DirectoryProbe.sequence entries
    ⟨(home hash capacity).toNat, home_within hash capacity nonzero⟩)).1.getD 0

/-- A nonzero public answer is exactly a stored key/ID occurrence under the
table's ordinary placement and key-coherence invariants. The zero sentinel
is not identified with a valid stored identifier. -/
theorem inventoryID_eq_nonzero_iff (capacity : UInt32) (nonzero : capacity ≠ 0)
    (entries : Fin capacity.toNat → Option (Physical.Key × UInt32))
    (paths : DirectoryProbe.PathsOccupied entries
      (fun key => ⟨(home key.1 capacity).toNat, home_within key.1 capacity nonzero⟩))
    (unique : DirectoryProbe.KeysCoherent entries) (key : Physical.Key) (identifier : UInt32)
    (identifierNonzero : identifier ≠ 0) :
    inventoryID capacity nonzero entries key.1 key.2 = identifier ↔
      ∃ slot, entries slot = some (key, identifier) := by
  rw [← stored_id_iff capacity nonzero entries paths unique key identifier]
  unfold inventoryID
  cases (InternProbe.probe key (DirectoryProbe.sequence entries
    ⟨(home key.1 capacity).toNat, home_within key.1 capacity nonzero⟩)).1 <;>
    simp [Ne.symm identifierNonzero]

private theorem loadWord_wp {heap : Heap L} {pointer : Ptr} {value : UInt32}
    {post : UInt32 → Heap L → Prop} (held : Reads pointer (.u32 value) heap)
    (after : post value heap) : (CProg.loadU32 pointer).wp act post heap := by
  refine wp_consequence act
    (loadU32_rule (P := fun reached => reached = heap) (n := value) ?_) rfl ?_
  · rintro reached rfl
    exact held
  · rintro _ _ ⟨rfl, rfl⟩
    exact after

theorem bad_input_false_wp (heap : Heap L) (table bytes : Ptr) (length : UInt32)
    (tableLive : Valid heap table) (bytesLive : Valid heap bytes) (nonempty : length ≠ 0)
    (post : Bool → Heap L → Prop) (after : post false heap) :
    (badInputProgram table bytes length).wp act post heap := by
  unfold badInputProgram
  rw [wp_bind']
  apply wp_ptrEq (p := some table) (q := none) tableLive trivial
  simp only [Option.some_ne_none, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [wp_bind']
  apply wp_ptrEq (p := some bytes) (q := none) bytesLive trivial
  simpa only [Option.some_ne_none, decide_false, Bool.false_eq_true, ↓reduceIte,
    beq_eq_false_iff_ne.mpr nonempty, wp_pure] using after

/-- Acquire and release are named external synchronization contracts. The
acquired heap may differ from the incoming heap; the finite published table
and borrowed byte spans are proved stable within that protected state. This
law derives the returned ID by running the actual guards, reads and probe. -/
theorem lookup_returns_inventory (compare : EntryMatch.Compare) (mutex : MutexCall)
    (library : EntryMatch.MemcmpContract (L := L) compare)
    (table bytes : Ptr) (length : UInt32) (hash : UInt64) (query : List UInt8)
    (capacity : UInt32) (nonzero : capacity ≠ 0) (nonempty : length ≠ 0)
    (queryCount : query.length = length.toNat)
    (entries : Fin capacity.toNat → Option (Physical.Key × UInt32))
    (loaded : (List.ofFn entries).countP Option.isSome < capacity.toNat)
    (allowance : Nat) (enough : capacity.toNat ≤ allowance)
    (pre locked released : Heap L → Prop)
    (tableLive : ∀ heap, pre heap → Valid heap table)
    (bytesLive : ∀ heap, pre heap → Valid heap bytes)
    (acquire : CTriple pre (mutex true (table + 6)) (fun _ => locked))
    (release : CTriple locked (mutex false (table + 6)) (fun _ => released))
    (reads : ∀ heap, locked heap → ∀ position,
      Physical.CellRead table (UInt32.ofNat position.val) (entries position) heap)
    (capCell : ∀ heap, locked heap → Reads (table + 1) (.u32 capacity) heap)
    (queryLive : ∀ heap, locked heap → Valid heap bytes)
    (querySpan : ∀ heap, locked heap → EntryMatch.Span heap bytes query) :
    CTriple pre (lookupProgram compare mutex table bytes length hash allowance)
      (fun result heap => released heap ∧
        result = .finished (.returned () (some (.u32 (inventoryID capacity nonzero entries hash query))))) := by
  intro heap initial
  change (lookupProgram compare mutex table bytes length hash allowance).wp act _ heap
  unfold lookupProgram
  rw [wp_bind']
  apply bad_input_false_wp heap table bytes length (tableLive heap initial) (bytesLive heap initial) nonempty
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold afterGuardProgram
  rw [wp_bind']
  refine wp_mono act ?_ (acquire heap initial)
  intro ignored reached held
  rw [wp_bind']
  apply loadWord_wp (capCell reached held)
  simp only [bne, beq_eq_false_iff_ne.mpr nonzero, Bool.not_false, ↓reduceIte]
  unfold homeProgram
  rw [wp_bind', wp_bind']
  apply loadWord_wp (capCell reached held)
  simp only [if_neg nonzero, wp_pure]
  rw [wp_bind']
  have searched := Physical.search_returns_inventory compare library table bytes length hash query
    capacity nonzero queryCount entries loaded allowance enough locked reads capCell queryLive querySpan
  refine wp_mono act ?_ (searched reached held)
  rintro result final ⟨heldFinal, slot, equal⟩
  rw [equal]
  unfold finishSearch
  rw [wp_bind']
  refine wp_mono act ?_ (release final heldFinal)
  intro ignored final releasedNow
  simp only [wp_pure]
  exact ⟨releasedNow, rfl⟩

/-- The source-body observer retains the caller's lexical context and the
exact public ID derived from table storage. ABI, mutex and libc contracts
remain separate from the checked source-to-operation-tree construction. -/
theorem actual_lookup_returns_inventory (compare : EntryMatch.Compare) (mutex : MutexCall)
    (library : EntryMatch.MemcmpContract (L := L) compare)
    (outer : Context) (table bytes : Ptr) (length : UInt32) (hash : UInt64)
    (known : Parameters outer table bytes length hash)
    (query : List UInt8) (capacity : UInt32) (nonzero : capacity ≠ 0) (nonempty : length ≠ 0)
    (queryCount : query.length = length.toNat)
    (entries : Fin capacity.toNat → Option (Physical.Key × UInt32))
    (loaded : (List.ofFn entries).countP Option.isSome < capacity.toNat)
    (allowance : Nat) (enough : capacity.toNat ≤ allowance)
    (pre locked released : Heap L → Prop)
    (tableLive : ∀ heap, pre heap → Valid heap table)
    (bytesLive : ∀ heap, pre heap → Valid heap bytes)
    (acquire : CTriple pre (mutex true (table + 6)) (fun _ => locked))
    (release : CTriple locked (mutex false (table + 6)) (fun _ => released))
    (reads : ∀ heap, locked heap → ∀ position,
      Physical.CellRead table (UInt32.ofNat position.val) (entries position) heap)
    (capCell : ∀ heap, locked heap → Reads (table + 1) (.u32 capacity) heap)
    (queryLive : ∀ heap, locked heap → Valid heap bytes)
    (querySpan : ∀ heap, locked heap → EntryMatch.Span heap bytes query) :
    CTriple pre (StatementBlock.executeScopedWith (services compare mutex) layout allowance 14 outer Source.body)
      (fun result heap => released heap ∧
        result = .finished (.returned outer (some (.u32 (inventoryID capacity nonzero entries hash query))))) := by
  rw [actual_lookup_body compare mutex outer table bytes length hash allowance known]
  intro heap initial
  change (lookupProgram compare mutex table bytes length hash allowance >>= _).wp act _ heap
  rw [wp_bind']
  refine wp_mono act ?_ (lookup_returns_inventory compare mutex library table bytes length hash query
    capacity nonzero nonempty queryCount entries loaded allowance enough pre locked released
    tableLive bytesLive acquire release reads capCell queryLive querySpan heap initial)
  rintro result final ⟨held, rfl⟩
  simp only [wp_pure]
  exact ⟨held, rfl⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead


end


/-! ## Managed spelling lookup and current-ID source composition

The actual selected helper bodies compose through physical forwarding,
header loads, the readonly character-pointer view, collision comparison and
published table lookup. Numeric and managed readouts agree on exact bytes.
Native ABI, preprocessor configuration, publication/acquire, libc byte-span
comparison and borrowed lifetime remain component contracts. This is not an
allocator, GC, compiler or whole evaluator correctness theorem.
-/
section ManagedSpellingLookupSource
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup.Source
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def atom : CExpr := .identifier "atom".toList
def spelling : CExpr := .field atom "spelling".toList true
def bytes : CExpr := .field spelling "bytes".toList true
def length : CExpr := .field spelling "len".toList true
def hash : CExpr := .field spelling "hash".toList true
def number : CExpr := .field atom "symbol_number".toList true
def bytePointer : CType := ⟨"uint8_t".toList, 1⟩
def isSpelled : CExpr := .call "atom_symbol_is_spelled".toList [atom]
def fallback : CExpr := .conditional atom number (.identifier "SYMBOL_ID_NONE".toList)
def invoke : CExpr := .call "symbol_lookup_span_hashed".toList
  [.identifier "g_symbols".toList, .castPointeeConst bytePointer bytes, length, hash]
def body : List CStatement :=
  [.assign atom (.call "atom_symbol_unforward".toList [atom]),
   .branch (.unary .not isSpelled) [.return (some fallback)] [],
   .return (some invoke)]

private def sourcePiece0 : String × List Token := ("{\n", [.punctuation "{".toList])
private theorem sourcePiece0_lex : sourcePiece0.1.toList.foldl step initial = completed sourcePiece0.2 := by decide +kernel

private def sourcePiece1 : String × List Token := ("    atom = atom_symbol_unforward(atom);\n", [.identifier "atom".toList, .punctuation "=".toList, .identifier "atom_symbol_unforward".toList, .punctuation "(".toList, .identifier "atom".toList, .punctuation ")".toList, .punctuation ";".toList])
private theorem sourcePiece1_lex : sourcePiece1.1.toList.foldl step initial = completed sourcePiece1.2 := by decide +kernel

private def sourcePiece2 : String × List Token := ("    if (!atom_symbol_is_spelled(atom))\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "atom_symbol_is_spelled".toList, .punctuation "(".toList, .identifier "atom".toList, .punctuation ")".toList, .punctuation ")".toList])
private theorem sourcePiece2_lex : sourcePiece2.1.toList.foldl step initial = completed sourcePiece2.2 := by decide +kernel

private def sourcePiece3 : String × List Token := ("        return atom ? atom->symbol_number : SYMBOL_ID_NONE;\n", [.identifier "return".toList, .identifier "atom".toList, .punctuation "?".toList, .identifier "atom".toList, .punctuation "->".toList, .identifier "symbol_number".toList, .punctuation ":".toList, .identifier "SYMBOL_ID_NONE".toList, .punctuation ";".toList])
private theorem sourcePiece3_lex : sourcePiece3.1.toList.foldl step initial = completed sourcePiece3.2 := by decide +kernel

private def sourcePiece4 : String × List Token := ("    return symbol_lookup_span_hashed(g_symbols,\n", [.identifier "return".toList, .identifier "symbol_lookup_span_hashed".toList, .punctuation "(".toList, .identifier "g_symbols".toList, .punctuation ",".toList])
private theorem sourcePiece4_lex : sourcePiece4.1.toList.foldl step initial = completed sourcePiece4.2 := by decide +kernel

private def sourcePiece5 : String × List Token := ("        (const uint8_t *)atom->spelling->bytes, atom->spelling->len,\n", [.punctuation "(".toList, .identifier "const".toList, .identifier "uint8_t".toList, .punctuation "*".toList, .punctuation ")".toList, .identifier "atom".toList, .punctuation "->".toList, .identifier "spelling".toList, .punctuation "->".toList, .identifier "bytes".toList, .punctuation ",".toList, .identifier "atom".toList, .punctuation "->".toList, .identifier "spelling".toList, .punctuation "->".toList, .identifier "len".toList, .punctuation ",".toList])
private theorem sourcePiece5_lex : sourcePiece5.1.toList.foldl step initial = completed sourcePiece5.2 := by decide +kernel

private def sourcePiece6 : String × List Token := ("        atom->spelling->hash);\n", [.identifier "atom".toList, .punctuation "->".toList, .identifier "spelling".toList, .punctuation "->".toList, .identifier "hash".toList, .punctuation ")".toList, .punctuation ";".toList])
private theorem sourcePiece6_lex : sourcePiece6.1.toList.foldl step initial = completed sourcePiece6.2 := by decide +kernel

private def sourcePiece7 : String × List Token := ("}", [.punctuation "}".toList])
private theorem sourcePiece7_lex : sourcePiece7.1.toList.foldl step initial = completed sourcePiece7.2 := by decide +kernel

private def sourcePieces : List (String × List Token) := [sourcePiece0, sourcePiece1, sourcePiece2, sourcePiece3, sourcePiece4, sourcePiece5, sourcePiece6, sourcePiece7]
def source : String := String.join (sourcePieces.map Prod.fst)
def sourceTokens : List Token := sourcePieces.flatMap Prod.snd

theorem actual_source_lexed : lex source.toList = .ok sourceTokens := by
  apply lex_completed_string_pieces
  simp only [sourcePieces, List.forall_cons]
  exact ⟨sourcePiece0_lex, sourcePiece1_lex, sourcePiece2_lex, sourcePiece3_lex, sourcePiece4_lex, sourcePiece5_lex, sourcePiece6_lex, sourcePiece7_lex, trivial⟩

theorem actual_body_parsed : blockText? ["uint8_t".toList] source.toList = some body :=
  block_text_of_parts _ _ sourceTokens _ actual_source_lexed (by rfl)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup.Source


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

abbrev Forward := Option Ptr → CProg CVal (Option Ptr)
abbrev IsSpelled := Option Ptr → CProg CVal Bool
abbrev Span := Option Ptr → Option Ptr → UInt32 → UInt64 → CProg CVal UInt32

/-- Selected logical-cell ABI. The hash belongs to the spelling header;
kind belongs to the Atom header. Storage ownership validates the reached arm. -/
def layout : Layout := fun name =>
  if name = "hash".toList then some ⟨0, .word64⟩ else SymbolSpelling.layout name

/-- These types follow the actual declared member and the admitted uint8_t
ABI. No spelling contents, table slot or symbol ID enters the cast admission. -/
def objects : ObjectReads := { SymbolSpelling.objects with
  sourceType := fun operand => match operand with
    | .field (.field (.identifier name) member true) field true =>
        if name == "atom".toList && member == "spelling".toList && field == "bytes".toList
        then some (.pointer {} .character) else none
    | _ => none
  targetType := fun type => if type = Source.bytePointer then
    some (.pointer {} Mettapedia.Languages.C11.CharacterPointerViews.unsignedCharacter) else none }

/-- Calls remain separately justified components. In particular, a spelling
lookup is not a registration operation and its answer is not inferred here. -/
def calls (forward : Forward) (spelled : IsSpelled) (span : Span) : Calls := fun name values =>
  if name = "atom_symbol_unforward".toList then
    match values with
    | [.ptr atom] => forward atom >>= fun result => pure (.ptr result)
    | _ => CProg.undefined
  else if name = "atom_symbol_is_spelled".toList then
    match values with
    | [.ptr atom] => spelled atom >>= fun result => pure (.bool result)
    | _ => CProg.undefined
  else if name = "symbol_lookup_span_hashed".toList then
    match values with
    | [.ptr table, .ptr buffer, .u32 length, .u64 hash] =>
        span table buffer length hash >>= fun result => pure (.u32 result)
    | _ => CProg.undefined
  else CProg.undefined

def read (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (operand : CExpr) : CProg CVal CVal :=
  expressionWithNames (Current.names environment) (calls forward spelled span)
    layout operand objects

/-- The hash expression performs its own spelling-pointer load, as the source
does. It is not silently shared with the preceding bytes or length operands. -/
def readHash (atom : Option Ptr) : CProg CVal UInt64 := do
  let spelling ← SymbolSpelling.readSpelling atom
  match spelling with
  | none => CProg.undefined
  | some spelling => CProg.loadU64 (spelling + 0)

theorem atom_parameter (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment Source.atom = pure (.ptr atom) := by
  change resolved (environment "atom".toList) = _
  rw [known]
  rfl

theorem table_parameter (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (table : Option Ptr)
    (known : environment "g_symbols".toList = some (.ptr table)) :
    read forward spelled span environment (.identifier "g_symbols".toList) =
      pure (.ptr table) := by
  change resolved (environment "g_symbols".toList) = _
  rw [known]
  rfl

theorem spelling_field (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment Source.spelling =
      (SymbolSpelling.readSpelling atom >>= fun pointer => pure (.ptr pointer)) := by
  change (read forward spelled span environment Source.atom >>= fun actual =>
    objects.fieldRead layout Source.atom true actual "spelling".toList) = _
  rw [atom_parameter forward spelled span environment atom known]
  cases atom with
  | none => exact (undefined_bind _).symm
  | some atom => rfl

theorem bytes_field (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment Source.bytes =
      (SymbolSpelling.bytes atom >>= fun pointer => pure (.ptr pointer)) := by
  change (read forward spelled span environment Source.spelling >>= fun actual =>
    objects.fieldRead layout Source.spelling true actual "bytes".toList) = _
  rw [spelling_field forward spelled span environment atom known]
  unfold SymbolSpelling.bytes
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext spelling
  cases spelling with
  | none =>
      simp [ObjectReads.fieldRead, arrayFieldAddress, ObjectReads.fieldLayout,
        objects, SymbolSpelling.objects, layout, SymbolSpelling.layout,
        fieldAddress, resolved, pointer, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
      change (CProg.undefined >>= fun address => pure (CVal.ptr (some address))) =
        (CProg.undefined >>= fun value => pure (CVal.ptr value))
      rw [undefined_bind, undefined_bind]
  | some spelling => rfl

/-- The actual qualified cast retains the pointer earned by the physical
embedded-array read. Its static type proof supplies no storage or result. -/
theorem qualified_bytes_operand (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment (.castPointeeConst Source.bytePointer Source.bytes) =
      (SymbolSpelling.bytes atom >>= fun pointer => pure (.ptr pointer)) := by
  change (read forward spelled span environment Source.bytes >>=
    objects.readonlyCast Source.bytePointer Source.bytes) = _
  rw [bytes_field forward spelled span environment atom known]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1

theorem length_field (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment Source.length =
      (SymbolSpelling.length atom >>= fun length => pure (.u32 length)) := by
  change (read forward spelled span environment Source.spelling >>= fun actual =>
    objects.fieldRead layout Source.spelling true actual "len".toList) = _
  rw [spelling_field forward spelled span environment atom known]
  unfold SymbolSpelling.length
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext spelling
  cases spelling with
  | none => exact (undefined_bind _).symm
  | some spelling => rfl

theorem hash_field (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment Source.hash =
      (readHash atom >>= fun hash => pure (.u64 hash)) := by
  change (read forward spelled span environment Source.spelling >>= fun actual =>
    objects.fieldRead layout Source.spelling true actual "hash".toList) = _
  rw [spelling_field forward spelled span environment atom known]
  unfold readHash
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext spelling
  cases spelling with
  | none => exact (undefined_bind _).symm
  | some spelling => rfl

/-- Every argument is read at its own source occurrence. Three separate
spelling-pointer loads precede the actual span call. This fixes an evaluation
order for the admitted reader; a native compiler/order comparison is separate. -/
theorem actual_span_arguments (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom table : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom))
    (global : environment "g_symbols".toList = some (.ptr table)) :
    read forward spelled span environment Source.invoke =
      (do let buffer ← SymbolSpelling.bytes atom
          let length ← SymbolSpelling.length atom
          let hash ← readHash atom
          let result ← span table buffer length hash
          pure (.u32 result)) := by
  change (argumentsWithNames (Current.names environment) (calls forward spelled span) layout
    [.identifier "g_symbols".toList, .castPointeeConst Source.bytePointer Source.bytes,
      Source.length, Source.hash] objects .scalar >>=
    calls forward spelled span "symbol_lookup_span_hashed".toList) = _
  simp only [argumentsWithNames, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  change (read forward spelled span environment (.identifier "g_symbols".toList) >>= fun table =>
    read forward spelled span environment (.castPointeeConst Source.bytePointer Source.bytes) >>= fun buffer =>
      read forward spelled span environment Source.length >>= fun length =>
        read forward spelled span environment Source.hash >>= fun hash =>
          calls forward spelled span "symbol_lookup_span_hashed".toList [table, buffer, length, hash]) = _
  rw [table_parameter forward spelled span environment table global,
    qualified_bytes_operand forward spelled span environment atom known,
    length_field forward spelled span environment atom known,
    hash_field forward spelled span environment atom known]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

/-- Only the ordinary scalar-local assignment needed by this source body.
The common assignment conversion reads the old local type and the reached
operand. There is no physical write or implicit forwarding here. -/
def assignment (forward : Forward) (spelled : IsSpelled) (span : Span) : Assignment :=
  fun _ environment statement => match statement with
    | .assign (.identifier name) operand => do
        let old ← resolved (environment name)
        let value ← read forward spelled span environment operand
        let converted ← ReadLoops.assignValue old value
        pure (Function.update environment name (some converted))
    | _ => CProg.undefined

def services (forward : Forward) (spelled : IsSpelled) (span : Span) : Services :=
  { read := fun _ => read forward spelled span }

def retarget (environment : Environment) (atom : Option Ptr) : Environment :=
  Function.update environment "atom".toList (some (.ptr atom))

def program (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) : CProg CVal ReadBlock.Result :=
  executeWith (services forward spelled span) (assignment forward spelled span)
    layout 0 6 environment Source.body

def fallback (atom : Option Ptr) : CProg CVal UInt32 := do
  let null ← CProg.ptrEq atom none
  if null then pure 0 else SymbolSpelling.readWord atom 3

def afterForward (spelled : IsSpelled) (span : Span) (table atom : Option Ptr) :
    CProg CVal UInt32 := do
  let managed ← spelled atom
  if managed then do
    let buffer ← SymbolSpelling.bytes atom
    let length ← SymbolSpelling.length atom
    let hash ← readHash atom
    span table buffer length hash
  else fallback atom

/-- The result includes the actual reached local parameter. The caller's
other local bindings are retained by the source-block theorem below. -/
def operations (forward : Forward) (spelled : IsSpelled) (span : Span)
    (table atom : Option Ptr) : CProg CVal (Option Ptr × UInt32) := do
  let current ← forward atom
  let identifier ← afterForward spelled span table current
  pure (current, identifier)

theorem forward_call (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment (.call "atom_symbol_unforward".toList [Source.atom]) =
      (forward atom >>= fun pointer => pure (.ptr pointer)) := by
  change ((read forward spelled span environment Source.atom >>= fun value => pure [value]) >>=
    calls forward spelled span "atom_symbol_unforward".toList) = _
  rw [atom_parameter forward spelled span environment atom known]
  rfl

theorem spelled_call (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment Source.isSpelled =
      (spelled atom >>= fun yes => pure (.bool yes)) := by
  change ((read forward spelled span environment Source.atom >>= fun value => pure [value]) >>=
    calls forward spelled span "atom_symbol_is_spelled".toList) = _
  rw [atom_parameter forward spelled span environment atom known]
  rfl

theorem not_spelled_guard (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    (read forward spelled span environment (.unary .not Source.isSpelled) >>= truth) =
      (spelled atom >>= fun yes => pure (!yes)) := by
  change ((read forward spelled span environment Source.isSpelled >>= fun value => do
    let yes ← truth value
    pure (CVal.bool (!yes))) >>= truth) = _
  rw [spelled_call forward spelled span environment atom known]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]

theorem number_field (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment Source.number =
      (SymbolSpelling.readWord atom 3 >>= fun number => pure (.u32 number)) := by
  change (read forward spelled span environment Source.atom >>= fun actual =>
    objects.fieldRead layout Source.atom true actual "symbol_number".toList) = _
  rw [atom_parameter forward spelled span environment atom known]
  cases atom with
  | none => exact (undefined_bind _).symm
  | some atom => rfl

theorem fallback_read (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment Source.fallback =
      (fallback atom >>= fun identifier => pure (.u32 identifier)) := by
  change (read forward spelled span environment Source.atom >>= fun actual => do
    let yes ← truth actual
    if yes then read forward spelled span environment Source.number
    else read forward spelled span environment (.identifier "SYMBOL_ID_NONE".toList)) = _
  rw [atom_parameter forward spelled span environment atom known,
    number_field forward spelled span environment atom known]
  have zero : read forward spelled span environment (.identifier "SYMBOL_ID_NONE".toList) =
      pure (.u32 0) := rfl
  rw [zero]
  simp only [fallback, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext null
  cases null <;> rfl

theorem actual_assignment (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    assignment forward spelled span layout environment
      (.assign Source.atom (.call "atom_symbol_unforward".toList [Source.atom])) =
      (forward atom >>= fun current => pure (retarget environment current)) := by
  change (resolved (environment "atom".toList) >>= fun old =>
    read forward spelled span environment (.call "atom_symbol_unforward".toList [Source.atom]) >>=
      fun value => ReadLoops.assignValue old value >>= fun converted =>
        pure (Function.update environment "atom".toList (some converted))) = _
  rw [known, forward_call forward spelled span environment atom known]
  simp only [resolved, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

private theorem return_block (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (fuel : Nat) (operand : CExpr) :
    executeWith (services forward spelled span) (assignment forward spelled span)
      layout 0 (fuel + 1) environment [.return (some operand)] =
      (read forward spelled span environment operand >>= fun value =>
        pure (.finished (.returned environment (some value)))) := rfl

private theorem empty_block (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (fuel : Nat) :
    executeWith (services forward spelled span) (assignment forward spelled span)
      layout 0 fuel environment [] = pure (.finished (.next environment)) := by
  rw [executeWith_equation]

theorem actual_tail (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (table atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom))
    (global : environment "g_symbols".toList = some (.ptr table)) :
    executeWith (services forward spelled span) (assignment forward spelled span)
      layout 0 5 environment
      [.branch (.unary .not Source.isSpelled) [.return (some Source.fallback)] [],
       .return (some Source.invoke)] =
      (afterForward spelled span table atom >>= fun identifier =>
        pure (.finished (.returned environment (some (.u32 identifier))))) := by
  rw [executeWith_equation]
  simp only [Prog.bind_eq]
  rw [← Prog.bind_assoc]
  change ((read forward spelled span environment (.unary .not Source.isSpelled) >>= truth) >>=
    fun negative => executeWith (services forward spelled span) (assignment forward spelled span)
      layout 0 4 environment (if negative then [.return (some Source.fallback)] else []) >>=
        ReadBlock.resume (fun current => executeWith (services forward spelled span)
          (assignment forward spelled span) layout 0 4 current [.return (some Source.invoke)])) = _
  rw [not_spelled_guard forward spelled span environment atom known]
  simp only [afterForward, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext yes
  cases yes with
  | false =>
      simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
      rw [return_block, fallback_read forward spelled span environment atom known]
      simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [empty_block]
      simp only [Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
      rw [return_block, actual_span_arguments forward spelled span environment atom table known global]
      simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

/-- The actual parsed assignment, branch and return compose through the
maintained block interpreter. The three helper services remain explicit here;
their finite physical realizations are a separate theorem. -/
theorem actual_body_uses_operations (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (table atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom))
    (global : environment "g_symbols".toList = some (.ptr table)) :
    program forward spelled span environment =
      (operations forward spelled span table atom >>= fun reached =>
        pure (.finished (.returned (retarget environment reached.1) (some (.u32 reached.2))))) := by
  unfold program Source.body
  rw [executeWith_equation]
  change (assignment forward spelled span layout environment
    (.assign Source.atom (.call "atom_symbol_unforward".toList [Source.atom])) >>= fun current =>
      executeWith (services forward spelled span) (assignment forward spelled span) layout 0 5 current
        [.branch (.unary .not Source.isSpelled) [.return (some Source.fallback)] [],
         .return (some Source.invoke)]) = _
  rw [actual_assignment forward spelled span environment atom known]
  simp only [operations, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext current
  rw [actual_tail forward spelled span (retarget environment current) table current
    (Function.update_self _ _ _)
    (by simpa only [retarget, Function.update_of_ne (by decide : "g_symbols".toList ≠ "atom".toList)] using global)]
  rfl

theorem retarget_preserves_other_locals (environment : Environment) (current : Option Ptr)
    (name : Name) (other : name ≠ "atom".toList) :
    retarget environment current name = environment name := Function.update_of_ne other _ _

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

theorem kind_field (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment SymbolSpelling.kindOperand =
      (SymbolSpelling.readWord atom 0 >>= fun kind => pure (.u32 kind)) := by
  change (read forward spelled span environment Source.atom >>= fun actual =>
    objects.fieldRead layout Source.atom true actual "kind".toList) = _
  rw [atom_parameter forward spelled span environment atom known]
  cases atom with
  | none => exact (undefined_bind _).symm
  | some atom => rfl

private theorem read_kind_guard (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment SymbolSpelling.kindGuard =
      (SymbolSpelling.readWord atom 0 >>= fun kind => pure (.bool (kind == 0))) := by
  change (read forward spelled span environment SymbolSpelling.kindOperand >>= fun kind =>
    pure (CVal.u32 0) >>= fun zero => binary .eq kind zero) = _
  rw [kind_field forward spelled span environment atom known]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

private theorem read_number_guard (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment SymbolSpelling.numberGuard =
      (SymbolSpelling.readWord atom 3 >>= fun number => pure (.bool (number == 0))) := by
  change (read forward spelled span environment Source.number >>= fun number =>
    pure (CVal.u32 0) >>= fun zero => binary .eq number zero) = _
  rw [number_field forward spelled span environment atom known]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

private theorem read_spelling_guard (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment SymbolSpelling.spellingGuard =
      (SymbolSpelling.readSpelling atom >>= fun pointer =>
        CProg.ptrEq pointer none >>= fun isNull => pure (.bool (!isNull))) := by
  change (read forward spelled span environment Source.spelling >>= fun pointer =>
    pure (CVal.ptr none) >>= fun null => binary .ne pointer null) = _
  rw [spelling_field forward spelled span environment atom known]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

private theorem and_read (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (left right : CExpr) :
    (read forward spelled span environment (.binary .and left right) >>= truth) =
      (do let value ← read forward spelled span environment left
          let selected ← truth value
          if selected then read forward spelled span environment right >>= truth else pure false) := by
  change ((do let value ← read forward spelled span environment left
              let selected ← truth value
              if selected then do
                let next ← read forward spelled span environment right
                let selectedNext ← truth next
                pure (CVal.bool selectedNext)
              else pure (CVal.bool false)) >>= truth) = _
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext value
  congr 1
  funext selected
  cases selected <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext next
  change (truth next).bind Prog.ret = truth next
  exact Prog.bind_ret _

theorem actual_spelled_guard (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    (read forward spelled span environment SymbolSpelling.condition >>= truth) =
      SymbolSpelling.test atom := by
  have join (left right : CExpr) :
      Prog.bind (read forward spelled span environment (.binary .and left right)) truth =
        Prog.bind (read forward spelled span environment left) (fun value => Prog.bind (truth value)
          (fun selected => if selected then Prog.bind (read forward spelled span environment right) truth
            else pure false)) := by
    simpa only [Prog.bind_eq] using and_read forward spelled span environment left right
  unfold SymbolSpelling.condition
  simp only [Prog.bind_eq]
  rw [join, ← Prog.bind_assoc, join, ← Prog.bind_assoc, join,
    show SymbolSpelling.atomOperand = Source.atom from rfl,
    atom_parameter forward spelled span environment atom known,
    read_kind_guard forward spelled span environment atom known,
    read_number_guard forward spelled span environment atom known,
    read_spelling_guard forward spelled span environment atom known]
  simp only [SymbolSpelling.test, truth, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext isNull
  cases isNull with
  | true => rfl
  | false =>
      simp only [Bool.not_false, ↓reduceIte, Prog.ret_bind, Prog.bind_assoc]
      congr 1
      funext kind
      by_cases zero : (kind == 0) = true <;>
        simp [zero, Prog.bind_assoc, Prog.ret_bind]

private theorem and_returns_boolean (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (left right : CExpr) :
    ((read forward spelled span environment (.binary .and left right) >>= truth) >>=
      fun value => pure (.bool value)) =
      read forward spelled span environment (.binary .and left right) := by
  change (((do let first ← read forward spelled span environment left
               let yes ← truth first
               if yes then do
                 let second ← read forward spelled span environment right
                 let selected ← truth second
                 pure (CVal.bool selected)
               else pure (CVal.bool false)) >>= truth) >>= fun value => pure (CVal.bool value)) = _
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext first
  congr 1
  funext yes
  cases yes <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1

theorem actual_spelled_value (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    read forward spelled span environment SymbolSpelling.condition =
      (SymbolSpelling.test atom >>= fun yes => pure (.bool yes)) := by
  rw [← actual_spelled_guard forward spelled span environment atom known]
  exact (and_returns_boolean forward spelled span environment _ _).symm

def spelledBody : List CStatement :=
  [.assign Source.atom (.call "atom_symbol_unforward".toList [Source.atom]),
   .return (some SymbolSpelling.condition)]

def spelledProgram (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) : CProg CVal ReadBlock.Result :=
  executeWith (services forward spelled span) (assignment forward spelled span)
    layout 0 2 environment spelledBody

/-- The called predicate performs its own parameter update and the actual
short-circuit field guard; no lookup or byte payload is used to decide it. -/
theorem actual_spelled_body (forward : Forward) (spelled : IsSpelled) (span : Span)
    (environment : Environment) (atom : Option Ptr)
    (known : environment "atom".toList = some (.ptr atom)) :
    spelledProgram forward spelled span environment =
      (do let current ← forward atom
          let yes ← SymbolSpelling.test current
          pure (.finished (.returned (retarget environment current) (some (.bool yes))))) := by
  unfold spelledProgram spelledBody
  rw [executeWith_equation]
  change (assignment forward spelled span layout environment
    (.assign Source.atom (.call "atom_symbol_unforward".toList [Source.atom])) >>= fun current =>
      executeWith (services forward spelled span) (assignment forward spelled span) layout 0 1 current
        [.return (some SymbolSpelling.condition)]) = _
  rw [actual_assignment forward spelled span environment atom known]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext current
  change (read forward spelled span (retarget environment current) SymbolSpelling.condition >>= _) = _
  rw [actual_spelled_value forward spelled span (retarget environment current) current
    (Function.update_self _ _ _)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

private def spelledPiece0 : String × List Token :=
  ("{\n", [.punctuation "{".toList])
private theorem spelledPiece0_lex :
    spelledPiece0.1.toList.foldl step initial = completed spelledPiece0.2 := by decide +kernel
private def spelledPiece1 : String × List Token :=
  ("    atom = atom_symbol_unforward(atom);\n",
   [.identifier "atom".toList, .punctuation "=".toList,
    .identifier "atom_symbol_unforward".toList, .punctuation "(".toList,
    .identifier "atom".toList, .punctuation ")".toList, .punctuation ";".toList])
private theorem spelledPiece1_lex :
    spelledPiece1.1.toList.foldl step initial = completed spelledPiece1.2 := by decide +kernel
private def spelledPiece2 : String × List Token :=
  ("    return atom && atom->kind == ATOM_SYMBOL &&\n",
   [.identifier "return".toList, .identifier "atom".toList, .punctuation "&&".toList,
    .identifier "atom".toList, .punctuation "->".toList, .identifier "kind".toList,
    .punctuation "==".toList, .identifier "ATOM_SYMBOL".toList, .punctuation "&&".toList])
private theorem spelledPiece2_lex :
    spelledPiece2.1.toList.foldl step initial = completed spelledPiece2.2 := by decide +kernel
private def spelledPiece3 : String × List Token :=
  ("           atom->symbol_number == SYMBOL_ID_NONE && atom->spelling != NULL;\n",
   [.identifier "atom".toList, .punctuation "->".toList, .identifier "symbol_number".toList,
    .punctuation "==".toList, .identifier "SYMBOL_ID_NONE".toList, .punctuation "&&".toList,
    .identifier "atom".toList, .punctuation "->".toList, .identifier "spelling".toList,
    .punctuation "!=".toList, .identifier "NULL".toList, .punctuation ";".toList])
private theorem spelledPiece3_lex :
    spelledPiece3.1.toList.foldl step initial = completed spelledPiece3.2 := by decide +kernel
private def spelledPiece4 : String × List Token :=
  ("}", [.punctuation "}".toList])
private theorem spelledPiece4_lex :
    spelledPiece4.1.toList.foldl step initial = completed spelledPiece4.2 := by decide +kernel

private def spelledPieces : List (String × List Token) :=
  [spelledPiece0, spelledPiece1, spelledPiece2, spelledPiece3, spelledPiece4]

/-- The body selected by `CETTA_MANAGED_SYMBOLS`. The preprocessor selection
is explicit; the two enclosed source statements are unchanged. -/
def spelledSource : String := String.join (spelledPieces.map Prod.fst)
def spelledTokens : List Token := spelledPieces.flatMap Prod.snd

theorem spelled_source_lexed : lex spelledSource.toList = .ok spelledTokens := by
  apply lex_completed_string_pieces
  simp only [spelledPieces, List.forall_cons]
  exact ⟨spelledPiece0_lex, spelledPiece1_lex, spelledPiece2_lex, spelledPiece3_lex,
    spelledPiece4_lex, trivial⟩

theorem spelled_source_parsed : blockText? [] spelledSource.toList = some spelledBody :=
  block_text_of_parts _ _ spelledTokens _ spelled_source_lexed (by rfl)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open CellPermission

/-- An expression callback can consume only a completed helper reply. The
separate checked operation below retains allowance exhaustion. Its coverage
theorem is required before this partial scalar adapter models a native call. -/
def completedForward (allowance : Nat) : Forward := fun atom => do
  let result ← SymbolForward.traversal allowance atom
  match result with
  | .finished (.next current) => pure current
  | _ => CProg.undefined

/-- `atom_symbol_is_spelled` has its own forwarding call. Even when its input
was just unforwarded by its caller, the second physical guard remains. -/
def completedSpelled (allowance : Nat) : IsSpelled := fun atom => do
  let current ← completedForward allowance atom
  SymbolSpelling.test current

/-- This component admits nonnull table and byte arguments. Those facts are
earned by the managed-header proof, not guessed from the returned ID. The
actual span helper still runs its own pointer and length guards. -/
def spanResult (compare : EntryMatch.Compare) (mutex : Lookup.SourceRead.MutexCall)
    (allowance : Nat) (table buffer : Option Ptr) (length : UInt32) (hash : UInt64) :
    CProg CVal (ReadBlock.Result Unit) :=
  match table, buffer with
  | some table, some buffer =>
      Lookup.SourceRead.lookupProgram compare mutex table buffer length hash allowance
  | _, _ => CProg.undefined

def completedSpan (compare : EntryMatch.Compare) (mutex : Lookup.SourceRead.MutexCall)
    (allowance : Nat) : Span := fun table buffer length hash => do
  let result ← spanResult compare mutex allowance table buffer length hash
  let value ← resolved result.returnedValue?
  word value

/-- Physical composition with explicit helper exhaustion. The caller's first
forwarded pointer remains the source of the header arguments; the callee's
second forwarding call affects only its own spelled test. The native borrow
contract below proves that both reach the same stable terminal. -/
def checkedOperations (compare : EntryMatch.Compare) (mutex : Lookup.SourceRead.MutexCall)
    (forwardAllowance spelledAllowance lookupAllowance : Nat)
    (table atom : Option Ptr) : CProg CVal (ReadBlock.Result (Option Ptr)) := do
  let first ← SymbolForward.traversal forwardAllowance atom
  match first with
  | .finished (.next current) => do
      let second ← SymbolForward.traversal spelledAllowance current
      match second with
      | .finished (.next observed) => do
          let managed ← SymbolSpelling.test observed
          if managed then do
            let buffer ← SymbolSpelling.bytes current
            let length ← SymbolSpelling.length current
            let hash ← readHash current
            let result ← spanResult compare mutex lookupAllowance table buffer length hash
            pure (result.mapContext (fun _ => current))
          else do
            let identifier ← fallback current
            pure (.finished (.returned current (some (.u32 identifier))))
      | other => pure (other.mapContext (fun _ => current))
  | other => pure other

variable {L : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem completedForward_path_wp (heap : Heap L) {start terminal : Option Ptr} {hops : Nat}
    (path : SymbolForward.ForwardPath heap start terminal hops) (allowance : Nat)
    (enough : hops ≤ allowance) (post : Option Ptr → Heap L → Prop)
    (after : post terminal heap) :
    (completedForward allowance start).wp act post heap := by
  unfold completedForward
  rw [wp_bind']
  apply SymbolForward.traversal_path_wp heap path allowance enough
  simpa only [wp_pure] using after

theorem completedSpelled_managed_wp (heap : Heap L) {start : Option Ptr} (atom spelling : Ptr)
    {hops : Nat} (path : SymbolForward.ForwardPath heap start (some atom) hops)
    (allowance : Nat) (enough : hops ≤ allowance)
    (live : Valid heap atom) (spellingLive : Valid heap spelling)
    (kind : Reads atom (.u32 0) heap) (number : Reads (atom + 3) (.u32 0) heap)
    (stored : Reads (atom + 5) (.ptr (some spelling)) heap)
    (post : Bool → Heap L → Prop) (after : post true heap) :
    (completedSpelled allowance start).wp act post heap := by
  unfold completedSpelled
  rw [wp_bind']
  apply completedForward_path_wp heap path allowance enough
  exact SymbolSpelling.test_spelled_wp heap atom spelling live spellingLive kind number stored post after

theorem readHash_spelled_wp (heap : Heap L) (atom spelling : Ptr) (hash : UInt64)
    (stored : Reads (atom + 5) (.ptr (some spelling)) heap)
    (header : Reads spelling (.u64 hash) heap)
    (post : UInt64 → Heap L → Prop) (after : post hash heap) :
    (readHash (some atom)).wp act post heap := by
  unfold readHash SymbolSpelling.readSpelling
  rw [wp_bind']
  refine wp_consequence act
    (loadPtr_rule (P := fun reached => reached = heap) (q := some spelling) ?_) rfl ?_
  · rintro reached rfl
    exact stored
  rintro result reached ⟨same, value⟩
  subst reached
  subst result
  simp only [ptr_add_zero]
  refine wp_consequence act
    (loadU64_rule (P := fun reached => reached = heap) (n := hash) ?_) rfl ?_
  · rintro reached rfl
    exact header
  · rintro _ _ ⟨rfl, rfl⟩
    exact after

variable (compare : EntryMatch.Compare) (mutex : Lookup.SourceRead.MutexCall)

/-- The scalar adapter gets its answer from the actual bounded source
helper. Its coverage is proved from the independent table inventory, its
load bound and the libc/synchronization/borrow contracts. -/
theorem completedSpan_inventory_wp
    (library : EntryMatch.MemcmpContract (L := L) compare)
    (table buffer : Ptr) (length : UInt32) (hash : UInt64) (query : List UInt8)
    (capacity : UInt32) (nonzero : capacity ≠ 0) (nonempty : length ≠ 0)
    (queryCount : query.length = length.toNat)
    (entries : Fin capacity.toNat → Option (Lookup.Physical.Key × UInt32))
    (loaded : (List.ofFn entries).countP Option.isSome < capacity.toNat)
    (allowance : Nat) (enough : capacity.toNat ≤ allowance)
    (pre locked released : Heap L → Prop)
    (tableLive : ∀ heap, pre heap → Valid heap table)
    (bytesLive : ∀ heap, pre heap → Valid heap buffer)
    (acquire : CTriple pre (mutex true (table + 6)) (fun _ => locked))
    (release : CTriple locked (mutex false (table + 6)) (fun _ => released))
    (reads : ∀ heap, locked heap → ∀ position,
      Lookup.Physical.CellRead table (UInt32.ofNat position.val) (entries position) heap)
    (capCell : ∀ heap, locked heap → Reads (table + 1) (.u32 capacity) heap)
    (queryLive : ∀ heap, locked heap → Valid heap buffer)
    (querySpan : ∀ heap, locked heap → EntryMatch.Span heap buffer query) :
    CTriple pre (completedSpan compare mutex allowance (some table) (some buffer) length hash)
      (fun result heap => released heap ∧
        result = Lookup.SourceRead.inventoryID capacity nonzero entries hash query) := by
  intro heap initial
  change (completedSpan compare mutex allowance (some table) (some buffer) length hash).wp act _ heap
  unfold completedSpan spanResult
  rw [wp_bind']
  refine wp_mono act ?_ (Lookup.SourceRead.lookup_returns_inventory compare mutex library table buffer
    length hash query capacity nonzero nonempty queryCount entries loaded allowance enough
    pre locked released tableLive bytesLive acquire release reads capCell queryLive querySpan heap initial)
  rintro result final ⟨held, rfl⟩
  simpa only [ReadBlock.Result.returnedValue?, resolved, word,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, wp_ret, and_true] using held

/-- Physical active-arm and borrowed-header evidence. These fields say which
cells exist and are readable, not what lookup will return. -/
structure ManagedHeader (heap : Heap L) (atom spelling : Ptr) (length : UInt32)
    (hash : UInt64) : Prop where
  atomLive : Valid heap atom
  spellingLive : Valid heap spelling
  kind : Reads atom (.u32 0) heap
  number : Reads (atom + 3) (.u32 0) heap
  spellingCell : Reads (atom + 5) (.ptr (some spelling)) heap
  lengthCell : Reads (spelling + 1) (.u32 length) heap
  hashCell : Reads spelling (.u64 hash) heap

/-- The actual managed path completes from independent forwarding, storage
and table invariants. The table's returned identifier is computed by its
physical probe, including collision checks and the acquire/release calls.
Insufficient allowance remains visible in `checkedOperations` outside this
coverage theorem; it is never a successful zero identifier. -/
theorem checked_managed_inventory
    (library : EntryMatch.MemcmpContract (L := L) compare)
    (start : Option Ptr) (atom spelling table : Ptr) (length : UInt32) (hash : UInt64)
    (hops forwardAllowance spelledAllowance lookupAllowance : Nat)
    (forwardEnough : hops ≤ forwardAllowance)
    (query : List UInt8) (capacity : UInt32) (nonzero : capacity ≠ 0) (nonempty : length ≠ 0)
    (queryCount : query.length = length.toNat)
    (entries : Fin capacity.toNat → Option (Lookup.Physical.Key × UInt32))
    (loaded : (List.ofFn entries).countP Option.isSome < capacity.toNat)
    (lookupEnough : capacity.toNat ≤ lookupAllowance)
    (pre locked released : Heap L → Prop)
    (path : ∀ heap, pre heap → SymbolForward.ForwardPath heap start (some atom) hops)
    (header : ∀ heap, pre heap → ManagedHeader heap atom spelling length hash)
    (tableLive : ∀ heap, pre heap → Valid heap table)
    (bytesLive : ∀ heap, pre heap → Valid heap (spelling + 2))
    (acquire : CTriple pre (mutex true (table + 6)) (fun _ => locked))
    (release : CTriple locked (mutex false (table + 6)) (fun _ => released))
    (reads : ∀ heap, locked heap → ∀ position,
      Lookup.Physical.CellRead table (UInt32.ofNat position.val) (entries position) heap)
    (capCell : ∀ heap, locked heap → Reads (table + 1) (.u32 capacity) heap)
    (queryLive : ∀ heap, locked heap → Valid heap (spelling + 2))
    (querySpan : ∀ heap, locked heap → EntryMatch.Span heap (spelling + 2) query) :
    CTriple pre (checkedOperations compare mutex forwardAllowance spelledAllowance lookupAllowance
      (some table) start)
      (fun result heap => released heap ∧ result = .finished (.returned (some atom)
        (some (.u32 (Lookup.SourceRead.inventoryID capacity nonzero entries hash query))))) := by
  intro heap initial
  change (checkedOperations compare mutex forwardAllowance spelledAllowance lookupAllowance
    (some table) start).wp act _ heap
  have head := header heap initial
  unfold checkedOperations
  rw [wp_bind']
  apply SymbolForward.traversal_path_wp heap (path heap initial) forwardAllowance forwardEnough
  rw [wp_bind']
  apply SymbolForward.traversal_path_wp heap (SymbolSpelling.terminal_path (path heap initial))
    spelledAllowance (Nat.zero_le _)
  rw [wp_bind']
  apply SymbolSpelling.test_spelled_wp heap atom spelling head.atomLive head.spellingLive
    head.kind head.number head.spellingCell
  simp only [↓reduceIte]
  rw [wp_bind']
  apply SymbolSpelling.bytes_spelled_wp heap atom spelling head.spellingCell
  rw [wp_bind']
  apply SymbolSpelling.length_spelled_wp heap atom spelling length head.spellingCell head.lengthCell
  rw [wp_bind']
  apply readHash_spelled_wp heap atom spelling hash head.spellingCell head.hashCell
  change (Lookup.SourceRead.lookupProgram compare mutex table (spelling + 2) length hash lookupAllowance >>=
    fun result => pure (result.mapContext (fun _ => some atom))).wp act _ heap
  rw [wp_bind']
  refine wp_mono act ?_ (Lookup.SourceRead.lookup_returns_inventory compare mutex library table
    (spelling + 2) length hash query capacity nonzero nonempty queryCount entries loaded
    lookupAllowance lookupEnough pre locked released tableLive bytesLive acquire release reads
    capCell queryLive querySpan heap initial)
  rintro result final ⟨held, rfl⟩
  simpa only [ReadBlock.Result.mapContext, ReadBlock.Flow.mapContext, wp_pure, and_true] using held

/-- The same physical facts earn the expression-call interface on the actual
parsed source body. The completed helper adapters do not assume an ID, a
completed forwarding path, or a completed search: those are proved above from
their native storage invariants and the sufficient finite bounds. -/
theorem actual_managed_body_inventory
    (library : EntryMatch.MemcmpContract (L := L) compare)
    (environment : Environment) (start : Option Ptr) (atom spelling table : Ptr)
    (known : environment "atom".toList = some (.ptr start))
    (global : environment "g_symbols".toList = some (.ptr (some table)))
    (length : UInt32) (hash : UInt64)
    (hops forwardAllowance spelledAllowance lookupAllowance : Nat)
    (forwardEnough : hops ≤ forwardAllowance)
    (query : List UInt8) (capacity : UInt32) (nonzero : capacity ≠ 0) (nonempty : length ≠ 0)
    (queryCount : query.length = length.toNat)
    (entries : Fin capacity.toNat → Option (Lookup.Physical.Key × UInt32))
    (loaded : (List.ofFn entries).countP Option.isSome < capacity.toNat)
    (lookupEnough : capacity.toNat ≤ lookupAllowance)
    (pre locked released : Heap L → Prop)
    (path : ∀ heap, pre heap → SymbolForward.ForwardPath heap start (some atom) hops)
    (header : ∀ heap, pre heap → ManagedHeader heap atom spelling length hash)
    (tableLive : ∀ heap, pre heap → Valid heap table)
    (bytesLive : ∀ heap, pre heap → Valid heap (spelling + 2))
    (acquire : CTriple pre (mutex true (table + 6)) (fun _ => locked))
    (release : CTriple locked (mutex false (table + 6)) (fun _ => released))
    (reads : ∀ heap, locked heap → ∀ position,
      Lookup.Physical.CellRead table (UInt32.ofNat position.val) (entries position) heap)
    (capCell : ∀ heap, locked heap → Reads (table + 1) (.u32 capacity) heap)
    (queryLive : ∀ heap, locked heap → Valid heap (spelling + 2))
    (querySpan : ∀ heap, locked heap → EntryMatch.Span heap (spelling + 2) query) :
    CTriple pre (program (completedForward forwardAllowance) (completedSpelled spelledAllowance)
      (completedSpan compare mutex lookupAllowance) environment)
      (fun result heap => released heap ∧ result = .finished (.returned
        (retarget environment (some atom))
        (some (.u32 (Lookup.SourceRead.inventoryID capacity nonzero entries hash query))))) := by
  rw [actual_body_uses_operations _ _ _ environment (some table) start known global]
  intro heap initial
  change (operations (completedForward forwardAllowance) (completedSpelled spelledAllowance)
    (completedSpan compare mutex lookupAllowance) (some table) start >>=
    fun result => pure (.finished (.returned (retarget environment result.1)
      (some (.u32 result.2))) : ReadBlock.Result Environment)).wp act _ heap
  have head := header heap initial
  simp only [operations, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rw [wp_bind]
  apply completedForward_path_wp heap (path heap initial) forwardAllowance forwardEnough
  simp only [afterForward, Prog.bind_eq, Prog.bind_assoc]
  rw [wp_bind]
  apply completedSpelled_managed_wp heap atom spelling
    (SymbolSpelling.terminal_path (path heap initial)) spelledAllowance (Nat.zero_le _)
    head.atomLive head.spellingLive head.kind head.number head.spellingCell
  simp only [↓reduceIte]
  simp only [Prog.bind_assoc]
  rw [wp_bind]
  apply SymbolSpelling.bytes_spelled_wp heap atom spelling head.spellingCell
  rw [wp_bind]
  apply SymbolSpelling.length_spelled_wp heap atom spelling length head.spellingCell head.lengthCell
  rw [wp_bind]
  apply readHash_spelled_wp heap atom spelling hash head.spellingCell head.hashCell
  rw [wp_bind]
  refine wp_mono act ?_ (completedSpan_inventory_wp compare mutex library table (spelling + 2)
    length hash query capacity nonzero nonempty queryCount entries loaded lookupAllowance lookupEnough
    pre locked released tableLive bytesLive acquire release reads capCell queryLive querySpan heap initial)
  rintro result final ⟨held, rfl⟩
  simpa only [wp_ret, and_true] using held

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open CellPermission

variable {L : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- An occupied physical hash slot and the acquired published-ID snapshot
read the same entry bytes. The proof compares their actual chunk/header loads;
no relation between a lookup answer and a spelling is supplied. -/
theorem occupied_slot_reads_published_bytes
    (inventory : PhysicalAtoms.Inventory) (heap : Heap L)
    (snapshot : PublishedTable inventory heap) (slot : UInt32)
    (key : Lookup.Physical.Key) (identifier : UInt32)
    (cell : Lookup.Physical.CellRead snapshot.table slot (some (key, identifier)) heap) :
    physicalBytes? inventory heap snapshot.table identifier = some ⟨key.2.toArray⟩ := by
  obtain ⟨slots, _slotsCell, _idCell, _slotHash, row, buffer, length,
    _entryLive, _bufferLive, bytesCell, lengthCell, _entryHash, count, span⟩ := cell
  have sameCount : row.count = snapshot.count := by
    have same : (some (some (CVal.u32 row.count)) : Option (Option CVal)) =
        some (some (.u32 snapshot.count)) := row.countCell.symm.trans snapshot.countCell
    exact CVal.u32.inj (Option.some.inj (Option.some.inj same))
  obtain ⟨entry, member, sameId⟩ := snapshot.covered identifier row.nonzero
    (by simpa only [← sameCount] using row.within)
  have first := spelling_projection heap snapshot.table identifier row buffer length bytesCell lengthCell
  have second := spelling_projection heap snapshot.table entry.identifier
    (snapshot.rows entry member) entry.buffer entry.length
    (snapshot.buffers entry member) (snapshot.lengths entry member)
  rw [sameId] at second
  have pairSame : (buffer, length) = (entry.buffer, entry.length) :=
    Option.some.inj (first.symm.trans second)
  have bufferSame : buffer = entry.buffer := congrArg Prod.fst pairSame
  have lengthSame : length = entry.length := congrArg Prod.snd pairSame
  obtain ⟨rest, owned⟩ := span
  exact physical_bytes_from_owned inventory heap snapshot.table identifier row buffer length key.2 rest
    bytesCell lengthCell count (by
      intro index inside
      rw [bufferSame]
      exact snapshot.registered entry member index (by
        rw [snapshot.byteCount entry member, ← lengthSame, ← count]
        exact inside)) owned

/-- Under the actual placement invariant a nonzero lookup result denotes the
queried bytes in the independently acquired numeric table. The source label
can therefore use either its managed byte form or its published numeric ID
without identifying all ID-zero spellings. -/
theorem nonzero_inventory_reads_query
    (inventory : PhysicalAtoms.Inventory) (heap : Heap L)
    (snapshot : PublishedTable inventory heap)
    (capacity : UInt32) (nonzero : capacity ≠ 0)
    (entries : Fin capacity.toNat → Option (Lookup.Physical.Key × UInt32))
    (paths : DirectoryProbe.PathsOccupied entries
      (fun key => ⟨(Lookup.home key.1 capacity).toNat, Lookup.home_within key.1 capacity nonzero⟩))
    (unique : DirectoryProbe.KeysCoherent entries)
    (reads : ∀ position, Lookup.Physical.CellRead snapshot.table (UInt32.ofNat position.val)
      (entries position) heap)
    (hash : UInt64) (query : List UInt8)
    (found : Lookup.SourceRead.inventoryID capacity nonzero entries hash query ≠ 0) :
    physicalBytes? inventory heap snapshot.table
      (Lookup.SourceRead.inventoryID capacity nonzero entries hash query) = some ⟨query.toArray⟩ := by
  obtain ⟨slot, selected⟩ := (Lookup.SourceRead.inventoryID_eq_nonzero_iff capacity nonzero entries
    paths unique (hash, query) _ found).mp rfl
  exact occupied_slot_reads_published_bytes inventory heap snapshot (UInt32.ofNat slot.val)
    (hash, query) _ (by simpa only [selected] using reads slot)

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup


namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open CellPermission

/-- The native helper's scalar parameter and global table view. Automatic
storage/ABI entry is not fabricated by this local environment. -/
def callEnvironment (table atom : Option Ptr) : Environment := fun name =>
  if name = "atom".toList then some (.ptr atom)
  else if name = "g_symbols".toList then some (.ptr table)
  else none

/-- The actual source helper supplies the formerly abstract current-ID call.
Only completed source replies cross this scalar interface. Its physical
coverage theorem below earns completion; the parallel checked operation
retains every exhausted state. No identifier is a constructor argument. -/
def lookupFromBody (compare : EntryMatch.Compare) (mutex : Lookup.SourceRead.MutexCall)
    (forwardAllowance spelledAllowance lookupAllowance : Nat) (table : Option Ptr) : Current.Lookup :=
  fun atom => do
    let result ← program (completedForward forwardAllowance) (completedSpelled spelledAllowance)
      (completedSpan compare mutex lookupAllowance) (callEnvironment table atom)
    let value ← resolved result.returnedValue?
    word value

variable {L : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]
variable (compare : EntryMatch.Compare) (mutex : Lookup.SourceRead.MutexCall)

/-- Completion and returned ID are constructed by the exact managed helper
body from its forwarding path, actual header cells and finite table inventory. -/
theorem lookup_from_body_inventory
    (library : EntryMatch.MemcmpContract (L := L) compare)
    (start : Option Ptr) (atom spelling table : Ptr)
    (length : UInt32) (hash : UInt64)
    (hops forwardAllowance spelledAllowance lookupAllowance : Nat)
    (forwardEnough : hops ≤ forwardAllowance)
    (query : List UInt8) (capacity : UInt32) (nonzero : capacity ≠ 0) (nonempty : length ≠ 0)
    (queryCount : query.length = length.toNat)
    (entries : Fin capacity.toNat → Option (Lookup.Physical.Key × UInt32))
    (loaded : (List.ofFn entries).countP Option.isSome < capacity.toNat)
    (lookupEnough : capacity.toNat ≤ lookupAllowance)
    (pre locked released : Heap L → Prop)
    (path : ∀ heap, pre heap → SymbolForward.ForwardPath heap start (some atom) hops)
    (header : ∀ heap, pre heap → ManagedHeader heap atom spelling length hash)
    (tableLive : ∀ heap, pre heap → Valid heap table)
    (bytesLive : ∀ heap, pre heap → Valid heap (spelling + 2))
    (acquire : CTriple pre (mutex true (table + 6)) (fun _ => locked))
    (release : CTriple locked (mutex false (table + 6)) (fun _ => released))
    (reads : ∀ heap, locked heap → ∀ position,
      Lookup.Physical.CellRead table (UInt32.ofNat position.val) (entries position) heap)
    (capCell : ∀ heap, locked heap → Reads (table + 1) (.u32 capacity) heap)
    (queryLive : ∀ heap, locked heap → Valid heap (spelling + 2))
    (querySpan : ∀ heap, locked heap → EntryMatch.Span heap (spelling + 2) query) :
    CTriple pre (lookupFromBody compare mutex forwardAllowance spelledAllowance lookupAllowance
      (some table) start)
      (fun result heap => released heap ∧
        result = Lookup.SourceRead.inventoryID capacity nonzero entries hash query) := by
  intro heap initial
  change (lookupFromBody compare mutex forwardAllowance spelledAllowance lookupAllowance
    (some table) start).wp act _ heap
  unfold lookupFromBody
  rw [wp_bind']
  refine wp_mono act ?_ (actual_managed_body_inventory compare mutex library (callEnvironment (some table) start) start atom spelling table
    (by simp [callEnvironment]) (by simp [callEnvironment]) length hash
    hops forwardAllowance spelledAllowance lookupAllowance forwardEnough
    query capacity nonzero nonempty queryCount entries loaded lookupEnough pre locked released
    path header tableLive bytesLive acquire release reads capCell queryLive querySpan heap initial)
  rintro result final ⟨held, rfl⟩
  simpa only [ReadBlock.Result.returnedValue?, resolved, word,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, wp_ret, and_true] using held

/-- The current-ID dispatch reads its own incoming active arm before the
called helper un-forwards. These fields do not imply arbitrary forwarding
invariance; in particular, the numbered branch never calls this helper. -/
structure CurrentDispatch (heap : Heap L) (atom spelling : Ptr) : Prop where
  live : Valid heap atom
  spellingLive : Valid heap spelling
  kind : Reads atom (.u32 0) heap
  number : Reads (atom + 3) (.u32 0) heap
  stored : Reads (atom + 5) (.ptr (some spelling)) heap

/-- Actual current-ID source dispatch composed with the exact managed helper
body and actual physical table probe. The initial active arm and the eventual
unforwarded header are independently checked; the theorem does not change the
native choice to inspect the incoming raw number before forwarding. -/
theorem actual_current_id_managed_inventory
    (library : EntryMatch.MemcmpContract (L := L) compare)
    (start : Ptr) (atom spelling table : Ptr)
    (length : UInt32) (hash : UInt64)
    (hops forwardAllowance spelledAllowance lookupAllowance : Nat)
    (forwardEnough : hops ≤ forwardAllowance)
    (query : List UInt8) (capacity : UInt32) (nonzero : capacity ≠ 0) (nonempty : length ≠ 0)
    (queryCount : query.length = length.toNat)
    (entries : Fin capacity.toNat → Option (Lookup.Physical.Key × UInt32))
    (loaded : (List.ofFn entries).countP Option.isSome < capacity.toNat)
    (lookupEnough : capacity.toNat ≤ lookupAllowance)
    (pre locked released : Heap L → Prop)
    (path : ∀ heap, pre heap → SymbolForward.ForwardPath heap (some start) (some atom) hops)
    (header : ∀ heap, pre heap → ManagedHeader heap atom spelling length hash)
    (tableLive : ∀ heap, pre heap → Valid heap table)
    (bytesLive : ∀ heap, pre heap → Valid heap (spelling + 2))
    (acquire : CTriple pre (mutex true (table + 6)) (fun _ => locked))
    (release : CTriple locked (mutex false (table + 6)) (fun _ => released))
    (reads : ∀ heap, locked heap → ∀ position,
      Lookup.Physical.CellRead table (UInt32.ofNat position.val) (entries position) heap)
    (capCell : ∀ heap, locked heap → Reads (table + 1) (.u32 capacity) heap)
    (queryLive : ∀ heap, locked heap → Valid heap (spelling + 2))
    (querySpan : ∀ heap, locked heap → EntryMatch.Span heap (spelling + 2) query)
    (environment : Environment)
    (parameter : environment "atom".toList = some (.ptr (some start)))
    (dispatch : ∀ heap, pre heap → ∃ originalSpelling, CurrentDispatch heap start originalSpelling) :
    CTriple pre (Current.program
      (lookupFromBody compare mutex forwardAllowance spelledAllowance lookupAllowance (some table))
      environment)
      (fun result heap => released heap ∧ result = .finished (.returned environment
        (some (.u32 (Lookup.SourceRead.inventoryID capacity nonzero entries hash query))))) := by
  rw [Current.actual_body_uses_operations _ environment (some start) parameter]
  intro heap initial
  change (Current.operations
    (lookupFromBody compare mutex forwardAllowance spelledAllowance lookupAllowance (some table))
    (some start) >>= fun identifier => pure (.finished (.returned environment
      (some (.u32 identifier))) : ReadBlock.Result Environment)).wp act _ heap
  rw [wp_bind']
  obtain ⟨originalSpelling, active⟩ := dispatch heap initial
  apply Current.managed_current_id_wp _ heap start originalSpelling active.live active.spellingLive
    active.kind active.number active.stored
  refine wp_mono act ?_ (lookup_from_body_inventory compare mutex library (some start) atom spelling table
    length hash hops forwardAllowance spelledAllowance lookupAllowance forwardEnough
    query capacity nonzero nonempty queryCount entries loaded lookupEnough pre locked released
    path header tableLive bytesLive acquire release reads capCell queryLive querySpan heap initial)
  rintro result final ⟨held, rfl⟩
  simpa only [wp_pure, and_true] using held

/-- Borrowed published rows after release give the actual returned nonzero
identifier its byte meaning. The post-release facts concern physical cells;
no lookup answer or name is supplied. Arbitrary framed heap changes made by
synchronization remain allowed. -/
theorem actual_current_id_published_bytes
    (library : EntryMatch.MemcmpContract (L := L) compare)
    (start : Ptr) (atom spelling table : Ptr)
    (length : UInt32) (hash : UInt64)
    (hops forwardAllowance spelledAllowance lookupAllowance : Nat)
    (forwardEnough : hops ≤ forwardAllowance)
    (query : List UInt8) (capacity : UInt32) (nonzero : capacity ≠ 0) (nonempty : length ≠ 0)
    (queryCount : query.length = length.toNat)
    (entries : Fin capacity.toNat → Option (Lookup.Physical.Key × UInt32))
    (loaded : (List.ofFn entries).countP Option.isSome < capacity.toNat)
    (lookupEnough : capacity.toNat ≤ lookupAllowance)
    (pre locked released : Heap L → Prop)
    (path : ∀ heap, pre heap → SymbolForward.ForwardPath heap (some start) (some atom) hops)
    (header : ∀ heap, pre heap → ManagedHeader heap atom spelling length hash)
    (tableLive : ∀ heap, pre heap → Valid heap table)
    (bytesLive : ∀ heap, pre heap → Valid heap (spelling + 2))
    (acquire : CTriple pre (mutex true (table + 6)) (fun _ => locked))
    (release : CTriple locked (mutex false (table + 6)) (fun _ => released))
    (reads : ∀ heap, locked heap → ∀ position,
      Lookup.Physical.CellRead table (UInt32.ofNat position.val) (entries position) heap)
    (capCell : ∀ heap, locked heap → Reads (table + 1) (.u32 capacity) heap)
    (queryLive : ∀ heap, locked heap → Valid heap (spelling + 2))
    (querySpan : ∀ heap, locked heap → EntryMatch.Span heap (spelling + 2) query)
    (environment : Environment)
    (parameter : environment "atom".toList = some (.ptr (some start)))
    (dispatch : ∀ heap, pre heap → ∃ originalSpelling, CurrentDispatch heap start originalSpelling)
    (inventory : PhysicalAtoms.Inventory)
    (published : ∀ heap, released heap → PublishedTable inventory heap)
    (sameTable : ∀ heap held, (published heap held).table = table)
    (releasedReads : ∀ heap, released heap → ∀ position,
      Lookup.Physical.CellRead table (UInt32.ofNat position.val) (entries position) heap)
    (paths : DirectoryProbe.PathsOccupied entries
      (fun key => ⟨(Lookup.home key.1 capacity).toNat, Lookup.home_within key.1 capacity nonzero⟩))
    (unique : DirectoryProbe.KeysCoherent entries) :
    CTriple pre (Current.program
      (lookupFromBody compare mutex forwardAllowance spelledAllowance lookupAllowance (some table))
      environment)
      (fun result heap => released heap ∧ result = .finished (.returned environment
        (some (.u32 (Lookup.SourceRead.inventoryID capacity nonzero entries hash query)))) ∧
        (Lookup.SourceRead.inventoryID capacity nonzero entries hash query ≠ 0 →
          physicalBytes? inventory heap table
            (Lookup.SourceRead.inventoryID capacity nonzero entries hash query) = some ⟨query.toArray⟩)) := by
  intro heap initial
  refine wp_mono act ?_ (actual_current_id_managed_inventory compare mutex library start atom spelling table
    length hash hops forwardAllowance spelledAllowance lookupAllowance forwardEnough query capacity
    nonzero nonempty queryCount entries loaded lookupEnough pre locked released path header tableLive
    bytesLive acquire release reads capCell queryLive querySpan environment parameter dispatch heap initial)
  rintro result final ⟨held, exactResult⟩
  refine ⟨held, exactResult, ?_⟩
  intro found
  have exactBytes := nonzero_inventory_reads_query inventory final (published final held)
    capacity nonzero entries paths unique (by
      simpa only [sameTable final held] using releasedReads final held) hash query found
  simpa only [sameTable final held] using exactBytes

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup


end ManagedSpellingLookupSource
