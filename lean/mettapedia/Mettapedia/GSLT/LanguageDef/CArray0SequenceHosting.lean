import Batteries.Data.Array.Lemmas
import Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting

/-!
# Finite-sequence hosting by a bounded C-like array slice

`CArray0` is the next target rung after the scalar arithmetic pilot.  It is an
immutable, stack-owned array-and-slice machine covering four finite-sequence
observations: length, first element, rest, and indexed access.  A slice carries
its bounds proof, so an out-of-bounds target state has no constructor.

The source uses finite lists; the target executes over `Array` extraction and
array indexing.  Compilation stores a source sequence in one array and selects
the full valid slice.  The central theorem proves that target execution is
two-sided adequate at the declared result observation.

This is not yet Clight or a complete C memory model.  It has no heap, aliasing,
mutation, allocation failure, byte addressing, or machine-word overflow.  Its
purpose is to establish a non-circular sequence representation seam before
those structures are added.
-/

namespace Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting

/-! ## Neutral finite-sequence source -/

inductive SequenceOp where
  | length
  | first
  | rest
  | at (index : Nat)
  deriving DecidableEq, Repr

inductive SequenceObservation (α : Type) where
  | count (value : Nat)
  | element (value : α)
  | sequence (values : List α)
  | declined
  deriving DecidableEq, Repr

def sequenceSem (operation : SequenceOp) (values : List α) :
    SequenceObservation α :=
  match operation with
  | .length => .count values.length
  | .first =>
      match values.head? with
      | some value => .element value
      | none => .declined
  | .rest =>
      match values with
      | [] => .declined
      | _ :: rest => .sequence rest
  | .at index =>
      match values[index]? with
      | some value => .element value
      | none => .declined

inductive SequenceTerm (α : Type) where
  | request (operation : SequenceOp) (values : List α)
  | done (operation : SequenceOp) (values : List α)

inductive SequenceStep : SequenceTerm α → SequenceTerm α → Prop
  | run (operation : SequenceOp) (values : List α) :
      SequenceStep (.request operation values) (.done operation values)

/-- Source states are intrinsically formed: no constructor stores an outcome
that could disagree with `sequenceSem`. -/
inductive SequenceMeaning : SequenceTerm α → Prop
  | request (operation : SequenceOp) (values : List α) :
      SequenceMeaning (.request operation values)
  | done (operation : SequenceOp) (values : List α) :
      SequenceMeaning (.done operation values)

private def eqSetoid (β : Type*) : Setoid β :=
  ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

def sequenceGSLT (α : Type) : GSLT where
  Term := SequenceTerm α
  equations := eqSetoid (SequenceTerm α)
  rewrites := SequenceStep
  rewrites_resp_left := by
    intro first first' last equal step
    cases equal
    exact ⟨last, step, rfl⟩
  rewrites_resp_right := by
    intro first last last' step equal
    cases equal
    exact step

def sequenceObserve : SequenceTerm α → Option (SequenceObservation α)
  | .request _ _ => none
  | .done operation values => some (sequenceSem operation values)

def sourceObject (α : Type) :
    ObservedOperationalObject (SequenceObservation α) where
  operational := ⟨sequenceGSLT α, SequenceMeaning⟩
  observe := fun {_ last} _ => sequenceObserve last

/-! ## Intrinsically bounded stack slices -/

/-- One immutable stack-owned array slice.  The backing array is retained so
`rest` can advance without allocation; the proof makes invalid slices
unrepresentable. -/
structure StackSlice (α : Type) where
  cells : Array α
  start : Nat
  count : Nat
  inBounds : start + count ≤ cells.size

namespace StackSlice

def toArray (slice : StackSlice α) : Array α :=
  slice.cells.extract slice.start (slice.start + slice.count)

def toList (slice : StackSlice α) : List α :=
  slice.toArray.toList

def ofList (values : List α) : StackSlice α where
  cells := values.toArray
  start := 0
  count := values.length
  inBounds := by simp

def ofArray (cells : Array α) : StackSlice α where
  cells := cells
  start := 0
  count := cells.size
  inBounds := by simp

@[simp] theorem ofList_count (values : List α) :
    (ofList values).count = values.length := rfl

@[simp] theorem toArray_ofList (values : List α) :
    (ofList values).toArray = values.toArray := by
  simp [ofList, toArray]

@[simp] theorem toList_ofList (values : List α) :
    (ofList values).toList = values := by
  simp [toList]

@[simp] theorem toArray_ofArray (cells : Array α) :
    (ofArray cells).toArray = cells := by
  simp [ofArray, toArray]

@[simp] theorem toList_ofArray (cells : Array α) :
    (ofArray cells).toList = cells.toList := by
  simp [toList]

def advance (slice : StackSlice α) (nonempty : 0 < slice.count) :
    StackSlice α where
  cells := slice.cells
  start := slice.start + 1
  count := slice.count - 1
  inBounds := by
    calc
      slice.start + 1 + (slice.count - 1) = slice.start + slice.count := by
        omega
      _ ≤ slice.cells.size := slice.inBounds

@[simp] theorem advance_count (slice : StackSlice α)
    (nonempty : 0 < slice.count) :
    (slice.advance nonempty).count = slice.count - 1 := rfl

@[simp] theorem toArray_advance_ofList_cons (head : α) (tail : List α) :
    ((ofList (head :: tail)).advance (by simp)).toArray = tail.toArray := by
  simp [advance, ofList, toArray, List.extract_eq_take_drop]

@[simp] theorem toList_advance_ofList_cons (head : α) (tail : List α) :
    ((ofList (head :: tail)).advance (by simp)).toList = tail := by
  simp [toList]

end StackSlice

/-! ## The CArray0 target machine -/

/-- The instruction family owned by the array target.  It is deliberately
distinct from `SequenceOp`: compilation must establish the source-to-target
mapping, and a later C printer may consume only this target syntax. -/
inductive ArrayInstruction where
  | count
  | loadFirst
  | advance
  | loadAt (index : Nat)
  deriving DecidableEq, Repr

def compileOperation : SequenceOp → ArrayInstruction
  | .length => .count
  | .first => .loadFirst
  | .rest => .advance
  | .at index => .loadAt index

inductive ArrayOutcome (α : Type) where
  | count (value : Nat)
  | element (value : α)
  | slice (value : StackSlice α)
  | declined

def arrayOutcomeObservation : ArrayOutcome α → SequenceObservation α
  | .count value => .count value
  | .element value => .element value
  | .slice value => .sequence value.toList
  | .declined => .declined

def arraySem (instruction : ArrayInstruction) (slice : StackSlice α) :
    ArrayOutcome α :=
  match instruction with
  | .count => .count slice.count
  | .loadFirst =>
      match slice.toArray[0]? with
      | some value => .element value
      | none => .declined
  | .advance =>
      if nonempty : 0 < slice.count then
        .slice (slice.advance nonempty)
      else
        .declined
  | .loadAt index =>
      match slice.toArray[index]? with
      | some value => .element value
      | none => .declined

/-- Representation adequacy for the four covered operations.  The target
computes through `Array`, while the common observation compares it with the
source list semantics. -/
theorem arraySem_ofList (operation : SequenceOp) (values : List α) :
    arrayOutcomeObservation
      (arraySem (compileOperation operation) (StackSlice.ofList values)) =
      sequenceSem operation values := by
  cases operation with
  | length => rfl
  | first =>
      cases values with
      | nil => rfl
      | cons head tail =>
          simp [compileOperation, arraySem, arrayOutcomeObservation, sequenceSem]
  | rest =>
      cases values with
      | nil => simp [compileOperation, arraySem, arrayOutcomeObservation, sequenceSem,
          StackSlice.ofList]
      | cons head tail =>
          simp [compileOperation, arraySem, arrayOutcomeObservation, sequenceSem]
  | «at» index =>
      simp only [compileOperation, arraySem, StackSlice.toArray_ofList,
        List.getElem?_toArray, sequenceSem]
      cases values[index]? <;> rfl

/-- A concrete negative control: incrementing the target length is observably
wrong for every compiled sequence. -/
theorem incremented_length_not_adequate (values : List α) :
    SequenceObservation.count (values.length + 1) ≠
      sequenceSem .length values := by
  simp [sequenceSem]

inductive ArrayTerm (α : Type) where
  | start (instruction : ArrayInstruction) (slice : StackSlice α)
  | halted (instruction : ArrayInstruction) (slice : StackSlice α)

inductive ArrayStep : ArrayTerm α → ArrayTerm α → Prop
  | run (instruction : ArrayInstruction) (slice : StackSlice α) :
      ArrayStep (.start instruction slice) (.halted instruction slice)

inductive ArrayMeaning : ArrayTerm α → Prop
  | start (instruction : ArrayInstruction) (slice : StackSlice α) :
      ArrayMeaning (.start instruction slice)
  | halted (instruction : ArrayInstruction) (slice : StackSlice α) :
      ArrayMeaning (.halted instruction slice)

def arrayGSLT (α : Type) : GSLT where
  Term := ArrayTerm α
  equations := eqSetoid (ArrayTerm α)
  rewrites := ArrayStep
  rewrites_resp_left := by
    intro first first' last equal step
    cases equal
    exact ⟨last, step, rfl⟩
  rewrites_resp_right := by
    intro first last last' step equal
    cases equal
    exact step

def arrayObserve : ArrayTerm α → Option (SequenceObservation α)
  | .start _ _ => none
  | .halted instruction slice =>
      some (arrayOutcomeObservation (arraySem instruction slice))

def targetObject (α : Type) :
    ObservedOperationalObject (SequenceObservation α) where
  operational := ⟨arrayGSLT α, ArrayMeaning⟩
  observe := fun {_ last} _ => arrayObserve last

/-! ## Compilation and two-sided hosting -/

def compileTerm : SequenceTerm α → ArrayTerm α
  | .request operation values =>
      .start (compileOperation operation) (StackSlice.ofList values)
  | .done operation values =>
      .halted (compileOperation operation) (StackSlice.ofList values)

private def one {source target : ArrayTerm α}
    (step : ArrayStep source target) :
    ExecutionPath (arrayGSLT α) source target :=
  .cons ⟨step⟩ (.refl _)

theorem no_sequence_step_from_done {operation : SequenceOp}
    {values : List α} {target : SequenceTerm α}
    (step : SequenceStep (.done operation values) target) : False := by
  cases step

theorem sequence_step_from_request {operation : SequenceOp}
    {values : List α} {target : SequenceTerm α}
    (step : SequenceStep (.request operation values) target) :
    target = .done operation values := by
  cases step
  rfl

def compileStep {source target : SequenceTerm α}
    (step : SequenceStep source target) :
    ExecutionPath (arrayGSLT α) (compileTerm source) (compileTerm target) := by
  cases source with
  | done operation values =>
      exact (no_sequence_step_from_done step).elim
  | request operation values =>
      have targetEq := sequence_step_from_request step
      subst targetEq
      exact one (ArrayStep.run _ _)

def preservesMeaning {term : SequenceTerm α}
    (meaning : SequenceMeaning term) : ArrayMeaning (compileTerm term) := by
  cases meaning with
  | request operation values =>
      exact .start (compileOperation operation) (StackSlice.ofList values)
  | done operation values =>
      exact .halted (compileOperation operation) (StackSlice.ofList values)

def realization : OperationalRealization (sequenceGSLT α) (arrayGSLT α) where
  mapTerm := compileTerm
  mapEquiv := by
    intro left right equal
    cases equal
    rfl
  mapStep := compileStep

def refinement :
    Refinement (sourceObject α).operational (targetObject α).operational where
  realization := realization
  preservesMeaning := fun _ => preservesMeaning

theorem observation_compiles (term : SequenceTerm α) :
    arrayObserve (compileTerm term) = sequenceObserve term := by
  cases term with
  | request operation values => rfl
  | done operation values =>
      exact congrArg some (arraySem_ofList operation values)

def forward : ObservedRefinement (sourceObject α) (targetObject α) where
  refinement := refinement
  commutes := by
    intro first last path
    simpa only [targetObject, sourceObject, refinement, realization] using
      observation_compiles last

theorem no_step_from_halted {instruction : ArrayInstruction}
    {slice : StackSlice α} {target : ArrayTerm α}
    (step : ArrayStep (.halted instruction slice) target) : False := by
  cases step

theorem path_from_halted {instruction : ArrayInstruction}
    {slice : StackSlice α} {target : ArrayTerm α}
    (path : ExecutionPath (arrayGSLT α) (.halted instruction slice) target) :
    target = .halted instruction slice := by
  cases path with
  | refl => rfl
  | cons head _ => exact False.elim (no_step_from_halted head.down)

theorem target_observation_forces_source
    {operation : SequenceOp} {values : List α} {target : ArrayTerm α}
    {observation : SequenceObservation α}
    (path : ExecutionPath (arrayGSLT α)
      (.start (compileOperation operation) (StackSlice.ofList values)) target)
    (observed : arrayObserve target = some observation) :
    observation = sequenceSem operation values := by
  cases path with
  | refl => simp [arrayObserve] at observed
  | cons head rest =>
      cases head.down
      have targetEq := path_from_halted rest
      subst targetEq
      simp [arrayObserve] at observed
      exact observed.symm.trans (arraySem_ofList operation values)

def sequenceHostedByCArray0 :
    BehavioralHosting (sourceObject α) (targetObject α) where
  forward := forward
  noInvention := by
    intro initial observation produced
    obtain ⟨⟨final, path, observed⟩⟩ := produced
    cases initial with
    | request operation values =>
        have exactObservation :
            observation = sequenceSem operation values :=
          target_observation_forces_source path observed
        subst exactObservation
        exact ⟨⟨SequenceTerm.done operation values,
          ⟨Route.cons ⟨SequenceStep.run operation values⟩ (Route.refl _), rfl⟩⟩⟩
    | done operation values =>
        have finalEq := path_from_halted path
        subst finalEq
        change
          some (arrayOutcomeObservation
            (arraySem (compileOperation operation) (StackSlice.ofList values))) =
              some observation at observed
        rw [arraySem_ofList operation values] at observed
        exact ⟨⟨SequenceTerm.done operation values,
          ⟨Route.refl _, observed⟩⟩⟩

theorem hosting_exact (initial : SequenceTerm α)
    (observation : SequenceObservation α) :
    ProducesObservation (targetObject α) (compileTerm initial) observation ↔
      ProducesObservation (sourceObject α) initial observation :=
  sequenceHostedByCArray0.produces_iff initial observation

/-! ## Test-only C boundary

The target instruction family also owns a small C printer used for shadow
qualification against CeTTa's expression-array representation.  This does
not place the printer, C compiler, or machine execution inside the hosting
theorem.  Their correspondence is tested independently, including a
deliberately wrong mutation.

The C slice carries an explicit capacity because the proof in `StackSlice`
is erased at the foreign boundary.  Invalid bounds remain outside the
covered fragment.  Subtraction-first bounds checks avoid unsigned overflow. -/

def cInstructionEnum : ArrayInstruction → String
  | .count => "CETTA_CARRAY0_COUNT"
  | .loadFirst => "CETTA_CARRAY0_LOAD_FIRST"
  | .advance => "CETTA_CARRAY0_ADVANCE"
  | .loadAt _ => "CETTA_CARRAY0_LOAD_AT"

def emitCArray0ShadowHeader : String :=
  "/* Generated test-only CArray0 shadow interface.\n" ++
  "   It is qualification evidence, not a production evaluator. */\n" ++
  "#ifndef CETTA_CARRAY0_SHADOW_V1_GENERATED_H\n" ++
  "#define CETTA_CARRAY0_SHADOW_V1_GENERATED_H\n\n" ++
  "#include <stddef.h>\n\n" ++
  "typedef enum {\n" ++
  "    " ++ cInstructionEnum .count ++ ",\n" ++
  "    " ++ cInstructionEnum .loadFirst ++ ",\n" ++
  "    " ++ cInstructionEnum .advance ++ ",\n" ++
  "    " ++ cInstructionEnum (.loadAt 0) ++ "\n" ++
  "} CettaCArray0Instruction;\n\n" ++
  "typedef struct {\n" ++
  "    const void *const *cells;\n" ++
  "    size_t capacity;\n" ++
  "    size_t start;\n" ++
  "    size_t count;\n" ++
  "} CettaCArray0Slice;\n\n" ++
  "typedef enum {\n" ++
  "    CETTA_CARRAY0_RESULT_COUNT,\n" ++
  "    CETTA_CARRAY0_RESULT_ELEMENT,\n" ++
  "    CETTA_CARRAY0_RESULT_SLICE,\n" ++
  "    CETTA_CARRAY0_RESULT_DECLINED\n" ++
  "} CettaCArray0ResultKind;\n\n" ++
  "typedef struct {\n" ++
  "    CettaCArray0ResultKind kind;\n" ++
  "    size_t count;\n" ++
  "    const void *element;\n" ++
  "    CettaCArray0Slice slice;\n" ++
  "} CettaCArray0Result;\n\n" ++
  "typedef enum {\n" ++
  "    CETTA_CARRAY0_OK,\n" ++
  "    CETTA_CARRAY0_INVALID_SLICE,\n" ++
  "    CETTA_CARRAY0_INVALID_INSTRUCTION\n" ++
  "} CettaCArray0Status;\n\n" ++
  "CettaCArray0Status cetta_carray0_shadow_eval_v1(\n" ++
  "    CettaCArray0Instruction instruction, CettaCArray0Slice input,\n" ++
  "    size_t index, CettaCArray0Result *output);\n\n" ++
  "#endif\n"

def emitCArray0ShadowSource : String :=
  "#include \"tests/generated/carray0_shadow_v1.generated.h\"\n\n" ++
  "CettaCArray0Status cetta_carray0_shadow_eval_v1(\n" ++
  "    CettaCArray0Instruction instruction, CettaCArray0Slice input,\n" ++
  "    size_t index, CettaCArray0Result *output) {\n" ++
  "    if (output == NULL || input.start > input.capacity ||\n" ++
  "        input.count > input.capacity - input.start ||\n" ++
  "        (input.count > 0u && input.cells == NULL))\n" ++
  "        return CETTA_CARRAY0_INVALID_SLICE;\n" ++
  "    switch (instruction) {\n" ++
  "    case " ++ cInstructionEnum .count ++ ":\n" ++
  "        output->kind = CETTA_CARRAY0_RESULT_COUNT;\n" ++
  "        output->count = input.count;\n" ++
  "        return CETTA_CARRAY0_OK;\n" ++
  "    case " ++ cInstructionEnum .loadFirst ++ ":\n" ++
  "        if (input.count == 0u) {\n" ++
  "            output->kind = CETTA_CARRAY0_RESULT_DECLINED;\n" ++
  "        } else {\n" ++
  "            output->kind = CETTA_CARRAY0_RESULT_ELEMENT;\n" ++
  "            output->element = input.cells[input.start];\n" ++
  "        }\n" ++
  "        return CETTA_CARRAY0_OK;\n" ++
  "    case " ++ cInstructionEnum .advance ++ ":\n" ++
  "        if (input.count == 0u) {\n" ++
  "            output->kind = CETTA_CARRAY0_RESULT_DECLINED;\n" ++
  "        } else {\n" ++
  "            output->kind = CETTA_CARRAY0_RESULT_SLICE;\n" ++
  "            output->slice = input;\n" ++
  "            output->slice.start += 1u;\n" ++
  "            output->slice.count -= 1u;\n" ++
  "        }\n" ++
  "        return CETTA_CARRAY0_OK;\n" ++
  "    case " ++ cInstructionEnum (.loadAt 0) ++ ":\n" ++
  "        if (index >= input.count) {\n" ++
  "            output->kind = CETTA_CARRAY0_RESULT_DECLINED;\n" ++
  "        } else {\n" ++
  "            output->kind = CETTA_CARRAY0_RESULT_ELEMENT;\n" ++
  "            output->element = input.cells[input.start + index];\n" ++
  "        }\n" ++
  "        return CETTA_CARRAY0_OK;\n" ++
  "    default:\n" ++
  "        return CETTA_CARRAY0_INVALID_INSTRUCTION;\n" ++
  "    }\n" ++
  "}\n"

end Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting
