import Mettapedia.GSLT.LanguageDef.IndexedInstructionStreamCompilation

/-!
# Fused indexed-effect machine compilation

An indexed instruction stream becomes useful only after its instructions act
on a state.  This module factors that state action as an effect algebra over a
dynamic split table.  The decoder and the algebra remain independent: the
same byte plan may be interpreted by different algebras, and the same algebra
may be driven by different admitted byte plans.

The central theorem proves that one-pass decode-and-execute is identical to
first decoding the complete byte stream and then executing the resulting
instruction list.  The fused form is therefore a semantics-preserving
streaming realization, not a second handwritten semantics.
-/

namespace Mettapedia.GSLT.LanguageDef.IndexedEffectMachineCompilation

open IndexedInstructionStreamCompilation

inductive IndexedValue (Prepared Saved : Type) where
  | prepared (value : Prepared)
  | saved (value : Saved)
  deriving DecidableEq, Repr

inductive ExecutionError (Failure : Type) where
  | indexOutOfRange (index : UInt64)
  | effect (failure : Failure)
  deriving DecidableEq, Repr

inductive MachineError (Failure : Type) where
  | decode (failure : DecodeError)
  | execute (failure : ExecutionError Failure)
  deriving DecidableEq, Repr

/-- A fixed generic interface for the four effects exposed by the indexed
instruction language.  The value inventory is read from the current state,
so successful saves may extend the suffix observed by later uses. -/
structure EffectAlgebra (Prepared Saved State Failure : Type) where
  values : State -> List Prepared × List Saved
  usePrepared : State -> Prepared -> Except Failure State
  useSaved : State -> Saved -> Except Failure State
  saveTop : State -> Except Failure State
  useUnknown : State -> Except Failure State

def lookupSplit (prepared : List Prepared) (saved : List Saved)
    (index : UInt64) : Option (IndexedValue Prepared Saved) :=
  match prepared[index.toNat]? with
  | some value => some (.prepared value)
  | none => (saved[index.toNat - prepared.length]?).map .saved

def executeInstruction
    (algebra : EffectAlgebra Prepared Saved State Failure)
    (state : State) : Instruction -> Except (ExecutionError Failure) State
  | .use index =>
      let values := algebra.values state
      match lookupSplit values.1 values.2 index with
      | none => .error (.indexOutOfRange index)
      | some (.prepared value) =>
          (algebra.usePrepared state value).mapError .effect
      | some (.saved value) =>
          (algebra.useSaved state value).mapError .effect
  | .save => (algebra.saveTop state).mapError .effect
  | .unknown => (algebra.useUnknown state).mapError .effect

def executeInstructions
    (algebra : EffectAlgebra Prepared Saved State Failure) :
    State -> List Instruction -> Except (ExecutionError Failure) State
  | state, [] => .ok state
  | state, instruction :: instructions => do
      let next <- executeInstruction algebra state instruction
      executeInstructions algebra next instructions

theorem executeInstructions_append
    (algebra : EffectAlgebra Prepared Saved State Failure)
    (state : State) (left right : List Instruction) :
    executeInstructions algebra state (left ++ right) =
      match executeInstructions algebra state left with
      | .error failure => .error failure
      | .ok next => executeInstructions algebra next right := by
  induction left generalizing state with
  | nil => rfl
  | cons instruction instructions inductionHypothesis =>
      simp only [List.cons_append, executeInstructions]
      cases stepEq : executeInstruction algebra state instruction with
      | error failure => rfl
      | ok next =>
          exact inductionHypothesis next

/-- Online execution from explicit decoder and effect states. -/
def runFusedBytesFrom
    (plan : Plan) (algebra : EffectAlgebra Prepared Saved State Failure) :
    DecoderState -> State -> List UInt8 ->
      Except (MachineError Failure) (State × DecoderState)
  | decoder, state, [] => .ok (state, decoder)
  | decoder, state, byte :: bytes =>
      match feed plan decoder byte with
      | .error failure => .error (.decode failure)
      | .ok (none, nextDecoder) =>
          runFusedBytesFrom plan algebra nextDecoder state bytes
      | .ok (some instruction, nextDecoder) =>
          match executeInstruction algebra state instruction with
          | .error failure => .error (.execute failure)
          | .ok nextState =>
              runFusedBytesFrom plan algebra nextDecoder nextState bytes

/-- Once the independent decoder has admitted a byte stream, fusing decoding
with effects is identical to executing the admitted instruction list.  The
admission premise is essential: without it, a later malformed byte and an
earlier effect failure would induce different failure orderings. -/
theorem runFusedBytesFrom_eq_execute_of_decode
    (plan : Plan) (algebra : EffectAlgebra Prepared Saved State Failure)
    (decoder : DecoderState) (state : State) (bytes : List UInt8)
    (instructions : List Instruction) (finalDecoder : DecoderState)
    (admitted : runBytesFrom plan decoder bytes =
      .ok (instructions, finalDecoder)) :
    runFusedBytesFrom plan algebra decoder state bytes =
      match executeInstructions algebra state instructions with
      | .error failure => .error (.execute failure)
      | .ok finalState => .ok (finalState, finalDecoder) := by
  induction bytes generalizing decoder state instructions finalDecoder with
  | nil =>
      simp only [runBytesFrom] at admitted
      cases admitted
      rfl
  | cons byte bytes inductionHypothesis =>
      simp only [runBytesFrom] at admitted
      cases feedEq : feed plan decoder byte with
      | error failure =>
          simp only [feedEq] at admitted
          cases admitted
      | ok result =>
          simp only [feedEq] at admitted
          obtain ⟨event, nextDecoder⟩ := result
          cases tailEq : runBytesFrom plan nextDecoder bytes with
          | error failure =>
            simp only [tailEq] at admitted
            cases admitted
          | ok tailResult =>
            simp only [tailEq] at admitted
            obtain ⟨tail, tailDecoder⟩ := tailResult
            cases admitted
            cases event with
            | none =>
                simpa only [runFusedBytesFrom, feedEq, Option.toList_none,
                  List.nil_append] using
                  inductionHypothesis nextDecoder state tail tailDecoder tailEq
            | some instruction =>
                cases effectEq : executeInstruction algebra state instruction with
                | error failure =>
                    simp only [runFusedBytesFrom, feedEq, effectEq]
                    rw [executeInstructions_append]
                    simp_all [Option.toList, executeInstructions,
                      bind, Except.bind]
                | ok nextState =>
                    simp only [runFusedBytesFrom, feedEq, effectEq]
                    rw [executeInstructions_append]
                    simpa [Option.toList, executeInstructions, effectEq,
                      bind, Except.bind] using
                      inductionHypothesis nextDecoder nextState tail
                        tailDecoder tailEq

/-- Complete one-pass execution validates the plan and refuses an unfinished
numeric index exactly as the decoder compiler does. -/
def runMachine
    (plan : Plan) (algebra : EffectAlgebra Prepared Saved State Failure)
    (state : State) (chunks : List (List UInt8)) :
    Except (MachineError Failure) State :=
  if plan.valid != true then .error (.decode .invalidPlan)
  else
    match runFusedBytesFrom plan algebra initialState state chunks.flatten with
    | .error failure => .error failure
    | .ok (finalState, finalDecoder) =>
        match finalDecoder.phase with
        | .openIndex _ => .error (.decode .openIndexAtEnd)
        | .betweenUses | .justCompletedUse => .ok finalState

/-! ## Independent effect-algebra witnesses -/

structure StackState where
  prepared : List Nat
  saved : List Nat
  stack : List Nat
  rejectUnknown : Bool := false
  deriving DecidableEq, Repr

inductive StackFailure where
  | empty
  | unknown
  deriving DecidableEq, Repr

def stackAlgebra : EffectAlgebra Nat Nat StackState StackFailure where
  values := fun state => (state.prepared, state.saved)
  usePrepared := fun state value => .ok { state with stack := value :: state.stack }
  useSaved := fun state value => .ok { state with stack := value :: state.stack }
  saveTop := fun state =>
    match state.stack with
    | [] => .error .empty
    | value :: _ => .ok { state with saved := state.saved ++ [value] }
  useUnknown := fun state =>
    if state.rejectUnknown then .error .unknown
    else .ok { state with stack := 999 :: state.stack }

private def firstPlan : Plan :=
  { terminalLow := 65
    terminalHigh := 84
    continuationLow := 85
    continuationHigh := 89
    saveByte := 90
    unknownByte := 63
    terminalRadix := 20
    terminalDigitBias := 0
    continuationRadix := 5
    continuationDigitBias := 1 }

private def secondPlan : Plan :=
  { terminalLow := 0
    terminalHigh := 9
    continuationLow := 10
    continuationHigh := 19
    saveByte := 20
    unknownByte := 21
    terminalRadix := 10
    terminalDigitBias := 0
    continuationRadix := 10
    continuationDigitBias := 0 }

private def initialStack : StackState :=
  { prepared := [11, 22, 33], saved := [], stack := [] }

example : runMachine firstPlan stackAlgebra initialStack [[65, 90], [68, 63]] =
    .ok { initialStack with saved := [11], stack := [999, 11, 11] } := by
  decide

/-- A different alphabet with no unknown instruction in its positive program
uses the same dynamic split-table algebra. -/
example : runMachine secondPlan stackAlgebra initialStack [[0, 20, 3]] =
    .ok { initialStack with saved := [11], stack := [11, 11] } := by
  decide

example :
    runMachine secondPlan stackAlgebra
      { initialStack with rejectUnknown := true } [[21]] =
      .error (.execute (.effect .unknown)) := by
  decide

example : runMachine secondPlan stackAlgebra initialStack [[20]] =
    .error (.decode .saveWithoutUse) := by
  decide

example : runMachine secondPlan stackAlgebra initialStack [[9]] =
    .error (.execute (.indexOutOfRange 9)) := by
  decide

end Mettapedia.GSLT.LanguageDef.IndexedEffectMachineCompilation
