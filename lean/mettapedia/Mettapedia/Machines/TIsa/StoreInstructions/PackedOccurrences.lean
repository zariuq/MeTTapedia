import Mettapedia.Machines.TIsa.StoreInstructions.Execution
import Mettapedia.Machines.TIsa.X86PlacedQwordLoad

/-!
# Word layout for an occurrence store

An array entry contains an occurrence identity and a value code.
Equal value codes do not make two entries one occurrence. A separate
counter supplies new identities. The allocation refuses rather than
wrapping a counter or claiming to encode a value without a code.
The published count is a word; the checked x86 load of that word
implements SIZE.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurrences

open Derivation
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86BoundedLoad (Instruction Fits Readable layout bytes count physical writes)
open X86PlacedQwordLoad (CapabilityView Checked input)
local instance : MemoryPrimitives := X86Memory.ordinary

universe u v w

structure Codes (V : Type v) where
  encode : V → Option Word
  decode : Word → Option V
  reads : ∀ {value word}, encode value = some word → decode word = some value

abbrev Row := Word × Word

structure Layout where
  sizeWord : Word
  occurrences : Array Row
  nextIdentity : Word

variable {V : Type v} (codes : Codes V)

def packRow (occurrence : ℕ × V) : Option Row :=
  if occurrence.1 < 2 ^ 64 then
    (codes.encode occurrence.2).map fun word => (BitVec.ofNat 64 occurrence.1, word)
  else none

def unpackRow (row : Row) : Option (ℕ × V) :=
  (codes.decode row.2).map (fun value => (row.1.toNat, value))

theorem row_roundtrip {occurrence : ℕ × V} {row : Row} (packed : packRow codes occurrence = some row) :
    unpackRow codes row = some occurrence := by
  obtain ⟨identity, value⟩ := occurrence
  by_cases fits : identity < 2 ^ 64
  · have wordPacked : (codes.encode value).map (fun word => (BitVec.ofNat 64 identity, word)) = some row :=
      by simpa only [packRow, if_pos fits] using packed
    obtain ⟨word, written, rfl⟩ := Option.map_eq_some_iff.mp wordPacked
    simp only [unpackRow, codes.reads written, Option.map_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  · simp only [packRow, if_neg fits] at packed
    cases packed

theorem rows_roundtrip (records : List (ℕ × V)) {words : List Row}
    (packed : records.mapM (packRow codes) = some words) :
    words.mapM (unpackRow codes) = some records ∧ words.length = records.length := by
  induction records generalizing words with
  | nil =>
    have empty : [] = words := Option.some.inj packed
    subst words
    exact ⟨rfl, rfl⟩
  | cons first rest ih =>
    simp only [List.mapM_cons] at packed
    obtain ⟨head, packedHead, more⟩ := Option.bind_eq_some_iff.mp packed
    obtain ⟨tail, packedTail, returned⟩ := Option.bind_eq_some_iff.mp more
    have same : head :: tail = words := Option.some.inj returned
    subst words
    obtain ⟨decoded, width⟩ := ih packedTail
    simp [row_roundtrip codes packedHead, decoded, width]

def pack (store : Store V) : Option Layout :=
  if store.occurrences.length < 2 ^ 64 ∧ store.fresh < 2 ^ 64 then
    (store.occurrences.mapM (packRow codes)).map fun rows =>
      ⟨BitVec.ofNat 64 rows.length, rows.toArray, BitVec.ofNat 64 store.fresh⟩
  else none

def unpack (memory : Layout) : Option (Store V) :=
  if memory.occurrences.size = memory.sizeWord.toNat then
    (memory.occurrences.toList.mapM (unpackRow codes)).map fun rows => ⟨rows, memory.nextIdentity.toNat⟩
  else none

theorem pack_roundtrip {store : Store V} {packed : Layout} (formed : pack codes store = some packed) :
    unpack codes packed = some store ∧ packed.sizeWord.toNat = store.occurrences.length := by
  by_cases fits : store.occurrences.length < 2 ^ 64 ∧ store.fresh < 2 ^ 64
  · unfold pack at formed
    rw [if_pos fits] at formed
    obtain ⟨rows, filled, rfl⟩ := Option.map_eq_some_iff.mp formed
    obtain ⟨inverse, width⟩ := rows_roundtrip codes store.occurrences filled
    have small : rows.length < 2 ^ 64 := width ▸ fits.1
    have len : rows.toArray.size = (BitVec.ofNat 64 rows.length).toNat := by
      change rows.length = (BitVec.ofNat 64 rows.length).toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    constructor
    · unfold unpack
      dsimp only
      rw [if_pos len]
      change (rows.mapM (unpackRow codes)).map
        (fun occurrences => ⟨occurrences, (BitVec.ofNat 64 store.fresh).toNat⟩) = some store
      rw [inverse, Option.map_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits.2]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, width]
  · simp only [pack, if_neg fits] at formed
    cases formed

theorem packed_count {store : Store V} {packed : Layout} (formed : pack codes store = some packed) :
    packed.sizeWord = BitVec.ofNat 64 store.occurrences.length :=
  BitVec.eq_of_toNat_eq (by
    have exact := (pack_roundtrip codes formed).2
    have fits := packed.sizeWord.isLt
    rw [exact] at fits
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, exact])

private theorem nth_decoded (words : List Row) {occurrences : List (ℕ × V)}
    (decoded : words.mapM (unpackRow codes) = some occurrences) (index : ℕ) :
    ((words[index]?).bind (unpackRow codes)) = occurrences[index]? := by
  induction words generalizing occurrences index with
  | nil =>
    have empty : ([] : List (ℕ × V)) = occurrences := Option.some.inj decoded
    subst occurrences
    cases index <;> rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at decoded
    obtain ⟨first, read, rest⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨later, found, emitted⟩ := Option.bind_eq_some_iff.mp rest
    have same : first :: later = occurrences := Option.some.inj emitted
    subst occurrences
    cases index with
    | zero => exact read
    | succ index => exact ih found index

def at? (packed : Layout) (index : ℕ) : Option (ℕ × V) :=
  (packed.occurrences[index]?).bind (unpackRow codes)

/-- A scan cursor on the packed array sees the same identity and value,
in the same order, including refusal past the published extent. -/
theorem at_exact {store : Store V} {packed : Layout} (formed : pack codes store = some packed) (index : ℕ) :
    at? codes packed index = store.occurrences[index]? := by
  have inverse := (pack_roundtrip codes formed).1
  unfold unpack at inverse
  split at inverse
  · obtain ⟨ordered, decoded, same⟩ := Option.map_eq_some_iff.mp inverse
    have exact : ordered = store.occurrences := congrArg Store.occurrences same
    subst ordered
    unfold at?
    rw [← Array.getElem?_toList]
    exact nth_decoded codes _ decoded index
  · cases inverse

theorem lower_size_word {T : Type u} {B : Type w} [DecidableEq V] (matcher : Matcher T V B)
    {st : StoreInstructions.State V B} {packed : Layout} (formed : pack codes st.store = some packed)
    {code : Instruction} {native : X86RegisterRefinement.State} (facts : X86Bounds.Facts (layout code) native)
    (view : CapabilityView facts st.machine)
    (inside : (facts.pointer - facts.base).toNat + code.offset.val + 8 ≤ facts.length.toNat)
    (aligned : (facts.pointer.toNat + code.offset.val) % 8 = 0)
    (header : st.machine.memory (facts.pointer.toNat + code.offset.val) = some packed.sizeWord) :
    ∃ next, executeInstruction matcher st (.transform (.size code.destination)) = .ok next ∧
      P1WordExecution.execute st.machine (.instruction (X86PlacedQwordLoad.source code)) =
        .continuing next.machine := by
  refine ⟨st.write code.destination packed.sizeWord, ?_,
    X86PlacedQwordLoad.source_reads facts st.machine view inside aligned _ header⟩
  rw [packed_count codes formed]
  rfl

private theorem word_of_bytes {left right : Word}
    (same : ∀ i < 8, left.extractLsb' (8 * i) 8 = right.extractLsb' (8 * i) 8) :
    left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inWord
  have agree := congrArg (fun byte : BitVec 8 => byte.getLsbD (i % 8)) (same (i / 8) (by omega))
  have index : 8 * (i / 8) + i % 8 = i := by omega
  simpa [BitVec.getLsbD_extractLsb', Nat.mod_lt _ (by decide : 0 < 8), index] using agree

theorem lower_size_x86 {store : Store V} {packed : Layout} (formed : pack codes store = some packed)
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {native : X86RegisterRefinement.State} {base : BitVec 48} {offset : ℕ}
    {code : Instruction} (point : At image native base offset) (checked : Checked image offset code)
    (facts : X86Bounds.Facts (layout code) native) (wide : code.wide = true)
    (inside : Fits (input point checked facts)) (data : Readable (input point checked facts))
    (header : ∀ i < 8, native.mem.get? ((address data.dataAddress.toInt i).signExtend 52).toNat =
      some (packed.sizeWord.extractLsb' (8 * i) 8)) :
    letI : OtherOpcodeHandlers := X86PlacedQwordLoad.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (count code)).run native = .ok () after ∧
      RegisterFrame (writes code) native after ∧
      lookup after (physical code.destination) = some (BitVec.ofNat 64 store.occurrences.length) ∧
      Nonempty (At image after base (offset + (bytes code).length)) := by
  have size : data.word = packed.sizeWord := by
    apply word_of_bytes
    intro i within
    have available := data.present i (by simpa [wide, X86DataLoad.byteCount] using within)
    exact Option.some.inj (available.symm.trans (header i within))
  obtain ⟨after, fetched, framed, result, next⟩ := X86PlacedQwordLoad.reads
    other extra vector point checked facts wide inside data
  rw [size, packed_count codes formed] at result
  exact ⟨after, fetched, framed, result, next⟩

namespace Examples

private def words : Codes Word := ⟨some, some, fun h => by cases h; rfl⟩
private def two : Store Word := ⟨[(0, 42), (1, 42)], 2⟩

theorem equal_values_keep_two_occurrences :
    (pack words two).map (fun memory => memory.occurrences.toList) = some [(0, 42), (1, 42)] := by
  decide +kernel

theorem cursor_keeps_the_second_identity :
    (pack words two).bind (fun memory => at? words memory 1) = some (1, 42) := by
  decide +kernel

theorem rejects_wraparound :
    (pack words ⟨[(2 ^ 64, 42)], 2⟩).isNone = true := by
  decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurrences
