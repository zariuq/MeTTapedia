import Mettapedia.Computability.BitGenerator
import Mettapedia.Computability.ComputableLists
import Mathlib.Computability.PartrecCode

/-!
# Effective bit-reading programs

A partial-recursive program computes successive machine instructions from
natural-number states. A finite stage runs its transition code with bounded
evaluation and counts exactly the input prefixes that give the observation.
The numerator is computable uniformly in program, history, and stage.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.BitGenerator

open Nat.Partrec (Code)
open Mettapedia.UniversalAI.TimeBoundedAIXI (bitstringsOfLength)
open KolmogorovComplexity.FiniteBitStrings (bitstringsOfLength_primrec)

/-- Instructions in an existing primitive-recursive data type. -/
abbrev InstructionCode := Nat ⊕ ((Nat × Nat) ⊕ (Bool × Nat))

def decodeInstruction : InstructionCode → Instruction Nat Bool
  | .inl next => .silent next
  | .inr (.inl (no, yes)) => .read no yes
  | .inr (.inr (bit, next)) => .emit bit next

def encodeInstruction : Instruction Nat Bool → InstructionCode
  | .silent next => .inl next
  | .read no yes => .inr (.inl (no, yes))
  | .emit bit next => .inr (.inr (bit, next))

@[simp] theorem decode_encode (action : Instruction Nat Bool) :
    decodeInstruction (encodeInstruction action) = action := by
  cases action <;> rfl

/-- An invalid instruction code leaves the machine unable to advance. -/
def instructionAt (code : Code) (stage state : Nat) : Option InstructionCode :=
  (Code.evaln stage code state).bind Encodable.decode

theorem instructionAt_stable (code : Code) {first later state : Nat} {instruction : InstructionCode}
    (order : first ≤ later) (observed : instructionAt code first state = some instruction) :
    instructionAt code later state = some instruction := by
  unfold instructionAt at *
  cases result : Code.evaln first code state with
  | none => simp [result] at observed
  | some raw =>
    have extended : Code.evaln later code state = some raw :=
      Option.mem_def.mp (Code.evaln_mono order (Option.mem_def.mpr result))
    simpa only [result, extended] using observed

def codeGenerator (code : Code) : Generator Nat Bool where
  initial := 0
  atStage stage state := (instructionAt code stage state).map decodeInstruction
  stable := by
    intro first later state action order observed
    cases candidate : instructionAt code first state with
    | none => simp [candidate] at observed
    | some wire =>
      simpa only [instructionAt_stable code order candidate, candidate] using observed

noncomputable def eventualInstruction (code : Code) (state : Nat) : Option InstructionCode := by
  classical
  exact (code.eval state).toOption.bind Encodable.decode

/-- The transition semantics of the actual partial-recursive code. -/
noncomputable def codeMeaning (code : Code) : Transition Nat Bool :=
  fun state => (eventualInstruction code state).map decodeInstruction

private theorem eventualInstruction_iff {code : Code} {state : Nat} {wire : InstructionCode} :
    eventualInstruction code state = some wire ↔
      ∃ raw ∈ code.eval state, Encodable.decode raw = some wire := by
  classical
  simp only [eventualInstruction, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨raw, evaluated, decoded⟩
    exact ⟨raw, Part.mem_toOption.mp (Option.mem_def.mpr evaluated), decoded⟩
  · rintro ⟨raw, evaluated, decoded⟩
    exact ⟨raw, Option.mem_def.mp (Part.mem_toOption.mpr evaluated), decoded⟩

theorem codeGenerator_sound (code : Code) {stage state : Nat} {action : Instruction Nat Bool}
    (found : (codeGenerator code).atStage stage state = some action) :
    codeMeaning code state = some action := by
  change (instructionAt code stage state).map decodeInstruction = some action at found
  obtain ⟨wire, observed, image⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨raw, evaluated, decoded⟩ := Option.bind_eq_some_iff.mp observed
  have complete : eventualInstruction code state = some wire :=
    eventualInstruction_iff.mpr ⟨raw, Code.evaln_sound (Option.mem_def.mpr evaluated), decoded⟩
  simp only [codeMeaning, complete, Option.map_some, image]

theorem codeGenerator_complete (code : Code) {state : Nat} {action : Instruction Nat Bool}
    (known : codeMeaning code state = some action) :
    ∃ stage, (codeGenerator code).atStage stage state = some action := by
  obtain ⟨wire, observed, image⟩ := Option.map_eq_some_iff.mp known
  obtain ⟨raw, evaluated, decoded⟩ := eventualInstruction_iff.mp observed
  obtain ⟨stage, found⟩ := Code.evaln_complete.mp evaluated
  have ready : instructionAt code stage state = some wire :=
    Option.bind_eq_some_iff.mpr ⟨raw, Option.mem_def.mp found, decoded⟩
  exact ⟨stage, by simp only [codeGenerator, ready, Option.map_some, image]⟩

/-- A prefix counts precisely when the code's unbounded streaming execution
can emit it from a finite portion of the random tape. -/
theorem code_event_iff_monitor (code : Code) (history : List Bool) (tape : CantorSpace) :
    tape ∈ (codeGenerator code).event history ↔
      ∃ bits rest, StreamingInput.Runs (monitor (codeMeaning code))
        (0, history) (tapePrefix tape bits) true rest :=
  (codeGenerator code).event_iff_monitor_runs (codeMeaning code)
    (codeGenerator_sound code) (codeGenerator_complete code) history tape

/-- A computable instruction table has an actual transition code. -/
theorem code_realizes_computable (table : Nat → InstructionCode) (computable : Computable table) :
    ∃ code : Code, ∀ state, codeMeaning code state = some (decodeInstruction (table state)) := by
  have comp := Primrec.encode.to_comp.comp computable
  have recursive : Nat.Partrec (fun state => Part.some (Encodable.encode (table state))) :=
    Partrec.nat_iff.mp comp
  obtain ⟨code, runs⟩ := Code.exists_code.mp recursive
  refine ⟨code, fun state => ?_⟩
  have found : eventualInstruction code state = some (table state) := by
    apply eventualInstruction_iff.mpr
    refine ⟨Encodable.encode (table state), ?_, Encodable.encodek _⟩
    rw [runs]
    exact Part.mem_some_iff.mpr rfl
  simp only [codeMeaning, found, Option.map_some]

private theorem instructionAt_primrec :
    Primrec fun input : (Code × Nat) × Nat => instructionAt input.1.1 input.1.2 input.2 := by
  have evaluated : Primrec fun input : (Code × Nat) × Nat =>
      Code.evaln input.1.2 input.1.1 input.2 :=
    Code.primrec_evaln.comp (((Primrec.snd.comp Primrec.fst).pair
      (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)
  exact Primrec.option_bind evaluated (Primrec.decode.comp Primrec.snd).to₂

/-- State, unread input, and the reversed output already emitted. -/
private abbrev Config := Nat × List Bool × List Bool

private def readMove (c : Config) (exits : Nat × Nat) : Config :=
  Option.casesOn c.2.1.head? c fun bit =>
    (cond bit exits.2 exits.1, c.2.1.tail, c.2.2)

private def emitMove (c : Config) (emission : Bool × Nat) : Config :=
  (emission.2, c.2.1, emission.1 :: c.2.2)

private def move (c : Config) (code : InstructionCode) : Config :=
  Sum.casesOn code (fun next => (next, c.2)) fun specific =>
    Sum.casesOn specific (readMove c) (emitMove c)

private def advance (step : Nat → Option InstructionCode) (c : Config) : Config :=
  Option.casesOn (step c.1) c (move c)

/-- The iteration used for the computability proof agrees with the output
interpreter, also when a transition or a tape bit is still unavailable. -/
private theorem iterate_output (step : Nat → Option InstructionCode) (fuel state : Nat)
    (tape reverseHistory : List Bool) :
    (((advance step)^[fuel] (state, tape, reverseHistory)).2.2).reverse =
      reverseHistory.reverse ++ output (fun s => (step s).map decodeInstruction) fuel state tape := by
  induction fuel generalizing state tape reverseHistory with
  | zero => simp [output]
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    cases ready : step state with
    | none =>
      have repeats :
          ((advance step)^[fuel] (state, tape, reverseHistory)) = (state, tape, reverseHistory) :=
        Function.iterate_fixed (by simp [advance, ready]) fuel
      simp [advance, ready, output, repeats]
    | some wire =>
      cases wire with
      | inl next =>
        simpa [advance, move, readMove, emitMove, ready, output, decodeInstruction] using ih next tape reverseHistory
      | inr specific =>
        cases specific with
        | inl exits =>
          cases tape with
          | nil =>
            have repeats :
                ((advance step)^[fuel] (state, [], reverseHistory)) = (state, [], reverseHistory) :=
              Function.iterate_fixed (by simp [advance, move, readMove, ready]) fuel
            simp [advance, move, readMove, emitMove, ready, output, decodeInstruction, repeats]
          | cons bit tail =>
            cases bit <;>
              simp only [advance, move, readMove, ready, output, decodeInstruction, Option.map_some,
                List.head?_cons, List.tail_cons, Bool.cond_false,
                Bool.cond_true, Bool.false_eq_true, if_false, if_true] <;> apply ih
        | inr emission =>
          simpa [advance, move, readMove, emitMove, ready, output, decodeInstruction, List.reverse_cons, List.append_assoc] using
            ih emission.2 tape (emission.1 :: reverseHistory)

private theorem readMove_computable : Computable₂ readMove := by
  let α := Config × (Nat × Nat)
  let β := α × Bool
  have tape : Computable fun input : α => input.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have past : Computable fun input : α => input.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have no : Computable fun input : β => input.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have yes : Computable fun input : β => input.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have t : Computable fun input : β => input.1.1.2.1.tail :=
    Primrec.list_tail.to_comp.comp (tape.comp Computable.fst)
  have u : Computable fun input : β => input.1.1.2.2 := past.comp Computable.fst
  have after : Computable₂ fun (input : α) (bit : Bool) =>
      ((cond bit input.2.2 input.2.1), input.1.2.1.tail, input.1.2.2) :=
    ((Computable.cond Computable.snd yes no).pair (t.pair u)).to₂
  exact Computable.option_casesOn (Primrec.list_head?.to_comp.comp tape) Computable.fst after

private theorem emitMove_computable : Computable₂ emitMove :=
  (Computable.snd.comp Computable.snd).pair
    ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      (Primrec.list_cons.to_comp.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp (Computable.snd.comp Computable.fst))))

private theorem move_computable : Computable₂ move := by
  let α := Config × InstructionCode
  let β := α × ((Nat × Nat) ⊕ (Bool × Nat))
  have c : Computable fun input : α => input.1 := Computable.fst
  have tail : Computable fun input : α => input.1.2 := Computable.snd.comp c
  have silent : Computable₂ fun (input : α) (next : Nat) => (next, input.1.2) :=
    (Computable.snd.pair (tail.comp Computable.fst)).to₂
  have read : Computable₂ fun (input : β) (exits : Nat × Nat) => readMove input.1.1 exits :=
    (readMove_computable.comp
      (c.comp (Computable.fst.comp Computable.fst)) Computable.snd).to₂
  have emit : Computable₂ fun (input : β) (emission : Bool × Nat) => emitMove input.1.1 emission :=
    (emitMove_computable.comp
      (c.comp (Computable.fst.comp Computable.fst)) Computable.snd).to₂
  have specific := Computable.sumCasesOn (α := β) Computable.snd read emit
  exact Computable.sumCasesOn (α := α) Computable.snd silent specific.to₂

private theorem advance_computable {Param : Type*} [Primcodable Param]
    {step : Param → Nat → Option InstructionCode} (hStep : Computable₂ step) :
    Computable₂ fun p (c : Config) => advance (step p) c := by
  let α := Param × Config
  have c : Computable fun input : α => input.2 := Computable.snd
  have next : Computable fun input : α => step input.1 input.2.1 :=
    hStep.comp Computable.fst (Computable.fst.comp c)
  have go : Computable₂ fun (input : α) instruction => move input.2 instruction :=
    (move_computable.comp (c.comp Computable.fst) Computable.snd).to₂
  exact Computable.option_casesOn next c go

private def codeCut (input : (Code × Nat) × List Bool) : List Bool :=
  (codeGenerator input.1.1).cut input.1.2 input.2

private theorem code_cut_computable : Computable codeCut := by
  let α := (Code × Nat) × List Bool
  have initial : Computable fun input : α => ((0, input.2, []) : Config) :=
    (Computable.const 0).pair (Computable.snd.pair (Computable.const []))
  have step : Computable₂ fun (input : Code × Nat) state => instructionAt input.1 input.2 state :=
    instructionAt_primrec.to_comp
  have advance' : Computable₂ fun (input : α) c =>
      advance (instructionAt input.1.1 input.1.2) c :=
    (advance_computable step).comp (Computable.fst.comp Computable.fst) Computable.snd
  have iterated := Computable.iterate' (Computable.snd.comp (Computable.fst : Computable fun input : α => input.1))
    initial advance'
  exact (Primrec.list_reverse.to_comp.comp
    (Computable.snd.comp (Computable.snd.comp iterated))).of_eq fun input => by
      simpa only [List.reverse_nil, List.nil_append, codeCut, Generator.cut, codeGenerator] using
        iterate_output (instructionAt input.1.1 input.1.2) input.1.2 0 input.2 []

private theorem prefixTest_computable :
    Computable₂ (List.isPrefixOf : List Bool → List Bool → Bool) := by
  have truncated : Computable fun input : List Bool × List Bool => input.2.take input.1.length :=
    Primrec.list_take.to_comp.comp
      (Primrec.list_length.to_comp.comp Computable.fst) Computable.snd
  refine ((Primrec.beq (α := List Bool)).to_comp.comp Computable.fst truncated).of_eq ?_
  intro input
  apply Bool.eq_iff_iff.mpr
  change (decide (input.1 = input.2.take input.1.length) = true ↔
    input.1.isPrefixOf input.2 = true)
  rw [decide_eq_true_eq, List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take]

private abbrev Query := (Code × List Bool) × Nat

private def matchesTape (input : Query) (tape : List Bool) : Bool :=
  input.1.2.isPrefixOf (codeCut ((input.1.1, input.2), tape))

private theorem matchesTape_computable : Computable₂ matchesTape := by
  have history : Computable fun input : Query × List Bool => input.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have arguments : Computable fun input : Query × List Bool => ((input.1.1.1, input.1.2), input.2) :=
    (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      (Computable.snd.comp Computable.fst)).pair Computable.snd)
  have emitted := code_cut_computable.comp arguments
  exact (prefixTest_computable.comp history emitted).of_eq (fun _ => rfl)

private def accepted (input : Query) : List (List Bool) :=
  (bitstringsOfLength input.2).filter (matchesTape input)

private theorem accepted_computable : Computable accepted :=
  Computable.list_filter' (bitstringsOfLength_primrec.to_comp.comp Computable.snd)
    matchesTape_computable

/-- Exact bounded counts are uniformly computable on the actual program
codes. This witnesses effectivity without a test for totality. -/
theorem code_count_computable :
    Computable fun input : (Code × List Bool) × Nat =>
      (codeGenerator input.1.1).count input.1.2 input.2 :=
  (Primrec.list_length.to_comp.comp accepted_computable).of_eq fun input =>
    ((codeGenerator input.1.1).count_eq_filter input.1.2 input.2).symm

end Mettapedia.Computability.BitGenerator
