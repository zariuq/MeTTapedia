import Mettapedia.GSLT.Core.Composition

/-!
# Contiguous-slice compilation

When a local analysis establishes that finite sequences are immutable and do
not escape their owner, a generated realization may concatenate their payloads
into one arena and retain `(offset, length)` handles.  This module proves the
representation substitution independently of any proof or parser vocabulary.
-/

namespace Mettapedia.GSLT.LanguageDef.ContiguousSliceCompilation

universe u

/-- A position-independent handle into one immutable flat carrier. -/
structure Slice where
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

def Slice.shift (amount : Nat) (slice : Slice) : Slice :=
  { offset := amount + slice.offset, length := slice.length }

def Slice.read (storage : List α) (slice : Slice) : List α :=
  (storage.drop slice.offset).take slice.length

/-- One persistent allocation plus compact handles for the source sequences. -/
structure PackedSequences (α : Type u) where
  storage : List α
  slices : List Slice
  deriving DecidableEq, Repr

/-- Compile recursively so every later handle is shifted by the exact prefix
length introduced at the current step. -/
def pack : List (List α) → PackedSequences α
  | [] => { storage := [], slices := [] }
  | sequence :: sequences =>
      let tail := pack sequences
      { storage := sequence ++ tail.storage
        slices := { offset := 0, length := sequence.length } ::
          tail.slices.map (Slice.shift sequence.length) }

def unpack (packed : PackedSequences α) : List (List α) :=
  packed.slices.map (Slice.read packed.storage)

/-- Shifting a handle by an appended prefix preserves the selected payload. -/
theorem Slice.read_shift_append (front storage : List α) (slice : Slice) :
    (slice.shift front.length).read (front ++ storage) =
      slice.read storage := by
  simp only [Slice.read, Slice.shift]
  rw [← List.drop_drop]
  simp

/-- Every source sequence is reconstructed exactly, in order and with its
multiplicity preserved. -/
theorem unpack_pack (sequences : List (List α)) :
    unpack (pack sequences) = sequences := by
  induction sequences with
  | nil => rfl
  | cons sequence sequences inductionHypothesis =>
      simp only [pack, unpack, List.map_cons]
      rw [List.cons.injEq]
      constructor
      · simp [Slice.read]
      · rw [List.map_map]
        calc
          List.map
              (Slice.read (sequence ++ (pack sequences).storage) ∘
                Slice.shift sequence.length)
              (pack sequences).slices =
              List.map (Slice.read (pack sequences).storage)
                (pack sequences).slices := by
            apply List.map_congr_left
            intro slice member
            exact Slice.read_shift_append sequence
              (pack sequences).storage slice
          _ = unpack (pack sequences) := rfl
          _ = sequences := inductionHypothesis

/-- The concatenated storage has exactly the source payload length. -/
theorem pack_storage_length (sequences : List (List α)) :
    (pack sequences).storage.length =
      (sequences.map List.length).sum := by
  induction sequences with
  | nil => rfl
  | cons sequence sequences inductionHypothesis =>
      simp [pack, inductionHypothesis]

/-- The handle inventory has exactly one occurrence per source sequence. -/
theorem pack_slices_length (sequences : List (List α)) :
    (pack sequences).slices.length = sequences.length := by
  induction sequences with
  | nil => rfl
  | cons sequence sequences inductionHypothesis =>
      simp [pack, inductionHypothesis]

def contiguousSliceRealization :
    Mettapedia.GSLT.SimpleRealization
      (List (List α)) (PackedSequences α) (List (List α)) where
  compile := fun _ source => pack source
  observeSource := fun _ source => source
  observeArtifact := fun _ artifact => unpack artifact
  adequate := by
    intro _ source
    exact unpack_pack source

/-! ## Local admission and cost -/

def uint32MaxNat : Nat := 4294967295

/-- The physical arena uses nonempty sequences and 32-bit offsets. -/
def locallyAdmissible (sequences : List (List α)) : Bool :=
  sequences.all (fun sequence => !sequence.isEmpty) &&
    decide (sequences.flatten.length ≤ uint32MaxNat)

structure AdmittedPackedSequences (α : Type u) where
  source : List (List α)
  packed : PackedSequences α
  sourceAdmitted : locallyAdmissible source = true
  exact : unpack packed = source
  deriving DecidableEq, Repr

def admit? [DecidableEq α] (source : List (List α)) :
    Option (AdmittedPackedSequences α) :=
  if accepted : locallyAdmissible source then
    some
      { source
        packed := pack source
        sourceAdmitted := accepted
        exact := unpack_pack source }
  else
    none

def sourceAllocationCount (source : List (List α)) : Nat := source.length

def packedAllocationCount (source : List (List α)) : Nat :=
  if source.isEmpty then 0 else 1

theorem packedAllocationCount_le_source (source : List (List α)) :
    packedAllocationCount source ≤ sourceAllocationCount source := by
  cases source <;> simp [packedAllocationCount, sourceAllocationCount]

theorem packedAllocationCount_lt_source_of_two
    (first second : List α) (rest : List (List α)) :
    packedAllocationCount (first :: second :: rest) <
      sourceAllocationCount (first :: second :: rest) := by
  simp [packedAllocationCount, sourceAllocationCount]

/-! ## Transaction-local watermark reset -/

def watermark (storage : List α) : Nat := storage.length

def reset (storage : List α) (mark : Nat) : List α := storage.take mark

/-- Scratch appended after a transaction watermark is discarded by one prefix
reset, retaining the complete pre-transaction carrier. -/
theorem reset_append_to_watermark (storage scratch : List α) :
    reset (storage ++ scratch) (watermark storage) = storage := by
  exact List.take_append_length

/-- A handle into the retained prefix has the same observation after scratch
allocation and watermark reset. -/
theorem Slice.read_reset_append (storage scratch : List α) (slice : Slice) :
    slice.read (reset (storage ++ scratch) (watermark storage)) =
      slice.read storage := by
  rw [reset_append_to_watermark]

/-! ## Independent guests and fail-closed canaries -/

private def proofFormulaVectors : List (List Nat) :=
  [[1, 10, 11], [1, 20], [1, 10, 11]]

private def parserTokenSpans : List (List Nat) :=
  [[0, 4], [4, 9], [9, 12], [12, 18]]

example : unpack (pack proofFormulaVectors) = proofFormulaVectors := by
  exact unpack_pack proofFormulaVectors

example : unpack (pack parserTokenSpans) = parserTokenSpans := by
  exact unpack_pack parserTokenSpans

example : (admit? proofFormulaVectors).isSome = true := by
  decide

example : (admit? parserTokenSpans).isSome = true := by
  decide

/-- Empty physical payloads are outside the admitted compact-slice fragment. -/
example : (admit? ([[1, 2], []] : List (List Nat))).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.ContiguousSliceCompilation
