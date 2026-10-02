import Mettapedia.GSLT.LanguageDef.NativeOpsTypedViews
import Mettapedia.Languages.VibeITP.Native.RadixCounters

/-!
# Native Vibe symbol and term storage

These records expose the ordered fields actually used by the native guest.
They distinguish raw storage from interpretation as an independently specified
symbol or term. Reference counts are machine words; their positivity is not
assumed by the content view. Ownership, lifetime and complete guest-function
execution remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.HeapCells

open Mettapedia.GSLT.LanguageDef.NativeOps
open Mettapedia.GSLT.LanguageDef.NativeWord64 (Word encode)

structure ArrayCell where
  address : Option Address
  length : Word
  deriving DecidableEq, Repr

def ArrayCell.sourceValue (cell : ArrayCell) (element : NativeType) : SourceValue :=
  .array element cell.address cell.length

def ArrayCell.targetValue (cell : ArrayCell) (element : NativeType) : TargetValue :=
  .array element cell.address (encode cell.length)

structure SymbolCell where
  kind : Word
  arity : Word
  binders : ArrayCell
  identity : ArrayCell
  references : Word
  immortal : Bool
  deriving DecidableEq, Repr

def SymbolCell.sourceValue (cell : SymbolCell) : SourceValue :=
  .record "Symbol" [.word cell.kind, .word cell.arity,
    cell.binders.sourceValue .word, cell.identity.sourceValue .word,
    .word cell.references, .bool cell.immortal]

def SymbolCell.targetValue (cell : SymbolCell) : TargetValue :=
  .record "Symbol" [.word (encode cell.kind), .word (encode cell.arity),
    cell.binders.targetValue .word, cell.identity.targetValue .word,
    .word (encode cell.references), .bool cell.immortal]

structure TermCell where
  symbol : Option Address
  number : Word
  literal : ArrayCell
  arguments : ArrayCell
  depth : Word
  hasFreeVariable : Bool
  references : Word
  deriving DecidableEq, Repr

def TermCell.sourceValue (cell : TermCell) : SourceValue :=
  .record "Term" [.reference cell.symbol, .word cell.number,
    cell.literal.sourceValue .byte, cell.arguments.sourceValue (.ref (.named "Term")),
    .word cell.depth, .bool cell.hasFreeVariable, .word cell.references]

def TermCell.targetValue (cell : TermCell) : TargetValue :=
  .record "Term" [.reference cell.symbol, .word (encode cell.number),
    cell.literal.targetValue .byte, cell.arguments.targetValue (.ref (.named "Term")),
    .word (encode cell.depth), .bool cell.hasFreeVariable, .word (encode cell.references)]

theorem symbol_value_encoding (cell : SymbolCell) :
    encodeValue cell.sourceValue = cell.targetValue := rfl

theorem term_value_encoding (cell : TermCell) :
    encodeValue cell.sourceValue = cell.targetValue := rfl

theorem symbol_read_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (cell : SymbolCell) :
    targetRead target address = some cell.targetValue ↔
      sourceRead source address = some cell.sourceValue :=
  memory_read_result_iff source target related address cell.sourceValue

theorem term_read_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (cell : TermCell) :
    targetRead target address = some cell.targetValue ↔
      sourceRead source address = some cell.sourceValue :=
  memory_read_result_iff source target related address cell.sourceValue

theorem symbol_cell_injective : Function.Injective SymbolCell.sourceValue := by
  intro left right same
  cases left with
  | mk kind arity binders identity references immortal =>
    cases right with
    | mk otherKind otherArity otherBinders otherIdentity otherReferences otherImmortal =>
      cases binders; cases identity; cases otherBinders; cases otherIdentity
      simp only [SymbolCell.sourceValue, ArrayCell.sourceValue, SourceValue.record.injEq,
        List.cons.injEq, SourceValue.word.injEq, SourceValue.array.injEq,
        SourceValue.bool.injEq, and_true, true_and] at same
      rcases same with ⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
      rfl

theorem term_cell_injective : Function.Injective TermCell.sourceValue := by
  intro left right same
  cases left with
  | mk symbol number literal arguments depth free references =>
    cases right with
    | mk otherSymbol otherNumber otherLiteral otherArguments otherDepth otherFree otherReferences =>
      cases literal; cases arguments; cases otherLiteral; cases otherArguments
      simp only [TermCell.sourceValue, ArrayCell.sourceValue, SourceValue.record.injEq,
        List.cons.injEq, SourceValue.reference.injEq, SourceValue.word.injEq,
        SourceValue.array.injEq, SourceValue.bool.injEq, and_true, true_and] at same
      rcases same with ⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
      rfl

theorem symbol_cell_unique (memory : SourceMemory) (address : Address) (left right : SymbolCell)
    (first : sourceRead memory address = some left.sourceValue)
    (second : sourceRead memory address = some right.sourceValue) : left = right :=
  symbol_cell_injective (Option.some.inj (first.symm.trans second))

theorem term_cell_unique (memory : SourceMemory) (address : Address) (left right : TermCell)
    (first : sourceRead memory address = some left.sourceValue)
    (second : sourceRead memory address = some right.sourceValue) : left = right :=
  term_cell_injective (Option.some.inj (first.symm.trans second))

theorem symbol_reference_write (memory : SourceMemory) (storage element : Nat)
    (cell : SymbolCell) (references : Word)
    (read : memory.cells storage element = some cell.sourceValue) :
    sourceWrite memory ⟨storage, element, [4]⟩ (.word references) =
      some (sourceStoreCell memory storage element { cell with references := references }.sourceValue) := by
  simp only [sourceWrite, read, bind, Option.bind]
  rfl

theorem term_reference_write (memory : SourceMemory) (storage element : Nat)
    (cell : TermCell) (references : Word)
    (read : memory.cells storage element = some cell.sourceValue) :
    sourceWrite memory ⟨storage, element, [6]⟩ (.word references) =
      some (sourceStoreCell memory storage element { cell with references := references }.sourceValue) := by
  simp only [sourceWrite, read, bind, Option.bind]
  rfl

def words (memory : SourceMemory) (cell : ArrayCell) : Option (List Nat) :=
  TypedViews.sourceView .word TypedViews.sourceWord memory (cell.sourceValue .word)

def references (memory : SourceMemory) (cell : ArrayCell) : Option (List Address) :=
  TypedViews.sourceView (.ref (.named "Term")) TypedViews.sourceReference memory
    (cell.sourceValue (.ref (.named "Term")))

def literal (memory : SourceMemory) (cell : ArrayCell) : Option (List UInt8) :=
  ByteViews.sourceView memory (cell.sourceValue .byte)

theorem words_length (memory : SourceMemory) (cell : ArrayCell) (values : List Nat)
    (read : words memory cell = some values) : values.length = cell.length.val :=
  TypedViews.source_view_length .word TypedViews.sourceWord memory cell.address cell.length values read

theorem references_length (memory : SourceMemory) (cell : ArrayCell) (values : List Address)
    (read : references memory cell = some values) : values.length = cell.length.val :=
  TypedViews.source_view_length (.ref (.named "Term")) TypedViews.sourceReference
    memory cell.address cell.length values read

theorem literal_length (memory : SourceMemory) (cell : ArrayCell) (values : List UInt8)
    (read : literal memory cell = some values) : values.length = cell.length.val :=
  ByteViews.source_view_length memory cell.address cell.length values read

theorem words_bounded (memory : SourceMemory) (cell : ArrayCell) (values : List Nat)
    (read : words memory cell = some values) : ∀ value ∈ values, value < 2 ^ 64 :=
  TypedViews.word_view_bounded memory cell.address cell.length values read

def identityValue (words : List Nat) : Nat :=
  words.foldr (fun digit rest => digit + Spec.wordBound * rest) 0

theorem identity_value_is_radix (values : List Nat)
    (bounded : ∀ value ∈ values, value < 2 ^ 64) :
    identityValue values = RadixCounters.value (values.map (BitVec.ofNat 64)) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      have firstBound := bounded first (List.mem_cons_self)
      have restBound := fun value member => bounded value (List.mem_cons_of_mem first member)
      simp only [identityValue, List.map_cons, List.foldr_cons, RadixCounters.value,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt firstBound]
      exact congrArg (fun value => first + Spec.wordBound * value) (ih restBound)

theorem stored_identity_is_radix (memory : SourceMemory) (cell : ArrayCell) (values : List Nat)
    (read : words memory cell = some values) :
    identityValue values = RadixCounters.value (values.map (BitVec.ofNat 64)) :=
  identity_value_is_radix values (words_bounded memory cell values read)

end Mettapedia.Languages.VibeITP.Native.HeapCells
