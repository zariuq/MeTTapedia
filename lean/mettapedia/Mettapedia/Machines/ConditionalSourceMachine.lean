import Mettapedia.Machines.FiniteCompiledMachine
import Mettapedia.Computability.KolmogorovComplexity.ConditionalInterpreter

/-!
# One fixed physical source machine for conditional interpretation

The program and auxiliary input occupy two separate natural-word fields of
the compiler's existing physical representation. Any decoding and internal
pair preparation are executed by the fixed source program, not performed as
an uncharged outer operation. A presentation exists for every effective
conditional algorithm and exact natural-word codec, before all calls.

The query reader specifies canonical physical inputs; it is not assigned
unit execution cost. Input encoding, packet preparation and the full IC
reconstruction/shortening checker remain separate operations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.ConditionalSourceMachine

open Turing StateTransition KolmogorovComplexity
open Turing.PartrecToTM2
open Mettapedia.Computability

def readQuery (word : List Γ') : Option (Nat × Nat) :=
  (PrefixMachine.readNumber word).bind fun first =>
    (PrefixMachine.readSingleton first.2).bind fun second =>
      if trList [first.1, second] = word then some (first.1, second) else none

theorem readQuery_pair (program condition : Nat) :
    readQuery (trList [program, condition]) = some (program, condition) := by
  have first := PrefixMachine.readNumber_trNat program (trList [condition])
  simp only [trList] at first
  simp only [readQuery, trList, first, Option.bind_some]
  rw [show PrefixMachine.readSingleton (trNat condition ++ .cons :: []) = some condition from
    PrefixMachine.readSingleton_trList condition]
  simp

theorem readQuery_sound {word : List Γ'} {program condition : Nat}
    (read : readQuery word = some (program, condition)) : word = trList [program, condition] := by
  obtain ⟨first, _initial, following⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨second, _remaining, canonical⟩ := Option.bind_eq_some_iff.mp following
  split at canonical
  · rename_i same
    cases Option.some.inj canonical
    exact same.symm
  · cases canonical

theorem exists_two_argument_code {algorithm : Nat → Nat → Part Nat} (effective : Partrec₂ algorithm) :
    ∃ code : ToPartrec.Code, ∀ program condition,
      code.eval [program, condition] = (algorithm program condition).map (fun output => [output]) := by
  have recursive : Nat.Partrec' (fun input : List.Vector Nat 2 => algorithm input.head input.tail.head) :=
    Nat.Partrec'.part_iff₂.mpr effective
  obtain ⟨code, computes⟩ := ToPartrec.Code.exists_code recursive
  exact ⟨code, fun program condition => computes (⟨[program, condition], rfl⟩ : List.Vector Nat 2)⟩

def encoded (codec : NaturalWordCodec) (algorithm : ConditionalAlgorithm) (program condition : Nat) : Part Nat :=
  (algorithm (codec.decode program) (codec.decode condition)).map codec.encode

theorem encoded_partrec (codec : NaturalWordCodec) {algorithm : ConditionalAlgorithm}
    (effective : Partrec₂ algorithm) : Partrec₂ (encoded codec algorithm) := by
  have evaluated : Partrec fun input : Nat × Nat => algorithm (codec.decode input.1) (codec.decode input.2) :=
    effective.comp (codec.decode_computable.comp Computable.fst) (codec.decode_computable.comp Computable.snd)
  exact (evaluated.map (codec.encode_computable.comp Computable.snd).to₂).to₂

/-- A fixed source code together with its independently stated conditional
interpretation law. Existence is proved from partial recursiveness below. -/
structure Presentation (codec : NaturalWordCodec) (algorithm : ConditionalAlgorithm) where
  code : ToPartrec.Code
  correct : ∀ program condition,
    code.eval [codec.encode program, codec.encode condition] =
      (algorithm program condition).map (fun output => [codec.encode output])

theorem exists_presentation (codec : NaturalWordCodec) {algorithm : ConditionalAlgorithm}
    (effective : Partrec₂ algorithm) : Nonempty (Presentation codec algorithm) := by
  obtain ⟨code, computes⟩ := exists_two_argument_code (encoded_partrec codec effective)
  refine ⟨⟨code, fun program condition => ?_⟩⟩
  have result := computes (codec.encode program) (codec.encode condition)
  simpa only [encoded, codec.decode_encode, Part.map_map, Function.comp_def] using result

theorem universal_has_fixed_source (codec : NaturalWordCodec) :
    Nonempty (Presentation codec universalConditionalAlgorithm) :=
  exists_presentation codec universalConditionalAlgorithm_partrec

variable {codec : NaturalWordCodec} {algorithm : ConditionalAlgorithm}

def machine (source : Presentation codec algorithm) : FinTM2 := FiniteCompiledMachine.machine source.code

attribute [local implicit_reducible] machine FiniteCompiledMachine.machine FiniteSupportMachine.machine

def query (codec : NaturalWordCodec) (program condition : BinString) : List Γ' :=
  trList [codec.encode program, codec.encode condition]

def answer (codec : NaturalWordCodec) (output : BinString) : List Γ' := trList [codec.encode output]

theorem query_fields (codec : NaturalWordCodec) (program condition : BinString) :
    readQuery (query codec program condition) = some (codec.encode program, codec.encode condition) :=
  readQuery_pair _ _

theorem halt_singleton_injective {first second : Nat} (same : halt [first] = halt [second]) : first = second := by
  have read := congrArg (fun state : Cfg' => PrefixMachine.readSingleton (state.stk K'.main)) same
  simpa only [halt, K'.elim, PrefixMachine.readSingleton_trList, Option.some.injEq] using read

/-- A counted physical source result has the declared conditional meaning. -/
theorem sound (source : Presentation codec algorithm) {program condition output : BinString} {time : Nat}
    (executed : TM2OutputsInTime (machine source) (query codec program condition) (some (answer codec output)) time) :
    output ∈ algorithm program condition := by
  have original := FiniteCompiledMachine.reflects_outputs source.code executed
  have evaluated : halt [codec.encode output] ∈ StateTransition.eval (TM2.step tr)
      (init source.code [codec.encode program, codec.encode condition]) :=
    StateTransition.mem_eval.mpr ⟨StackMachineComposition.execution_reaches original.toEvalsTo, by rfl⟩
  rw [Turing.PartrecToTM2.tr_eval, source.correct] at evaluated
  obtain ⟨value, observed, same⟩ := (Part.mem_map_iff halt).mp evaluated
  obtain ⟨word, computed, words⟩ := (Part.mem_map_iff (fun output => [codec.encode output])).mp observed
  have encodedSame := halt_singleton_injective (by simpa only [← words] using same)
  have equal := codec.encode_injective encodedSame
  simpa only [equal] using computed

/-- Every admitted conditional output has a counted run of this one fixed
physical source. No bound on the compiler's speed is inferred here. -/
theorem complete (source : Presentation codec algorithm) {program condition output : BinString}
    (computed : output ∈ algorithm program condition) :
    ∃ time, Nonempty (TM2OutputsInTime (machine source) (query codec program condition) (some (answer codec output)) time) := by
  have interpreted : [codec.encode output] ∈ source.code.eval [codec.encode program, codec.encode condition] := by
    rw [source.correct]
    exact Part.mem_map (fun output => [codec.encode output]) computed
  have evaluated : halt [codec.encode output] ∈ StateTransition.eval (TM2.step tr)
      (init source.code [codec.encode program, codec.encode condition]) := by
    rw [Turing.PartrecToTM2.tr_eval]
    exact Part.mem_map halt interpreted
  obtain ⟨path, _stopped⟩ := StateTransition.mem_eval.mp evaluated
  obtain ⟨original⟩ := StackMachineComposition.reaches_has_execution path
  have counted : EvalsToInTime (TM2.step tr) (init source.code [codec.encode program, codec.encode condition])
      (some (halt [codec.encode output])) original.steps := ⟨original, le_rfl⟩
  exact ⟨original.steps, ⟨FiniteCompiledMachine.outputs source.code counted⟩⟩

/-- A terminal source trace at an admitted query has a genuine conditional
output and a canonical singleton field. Termination is inferred from the trace,
not assumed for the algorithm or its other program strings. -/
theorem terminal_meaning (source : Presentation codec algorithm) {program condition : BinString}
    {final : (machine source).Cfg} {time : Nat}
    (executed : EvalsToInTime (machine source).step (initList (machine source) (query codec program condition))
      (some final) time) (stopped : final.l = none) :
    ∃ output : BinString, output ∈ algorithm program condition ∧
      final = haltList (machine source) (answer codec output) ∧
      Nonempty (TM2OutputsInTime (machine source) (query codec program condition) (some (answer codec output)) time) := by
  obtain ⟨numbers, canonical⟩ := FiniteCompiledMachine.clean_halts_at_encoded_input source.code
    [codec.encode program, codec.encode condition] final
    (StackMachineComposition.execution_reaches executed.toEvalsTo) stopped
  have counted : TM2OutputsInTime (machine source) (query codec program condition) (some (trList numbers)) time := by
    simpa only [canonical, TM2OutputsInTime, Option.map_some, machine] using executed
  have original := FiniteCompiledMachine.reflects_outputs source.code counted
  have evaluated : halt numbers ∈ StateTransition.eval (TM2.step tr)
      (init source.code [codec.encode program, codec.encode condition]) :=
    StateTransition.mem_eval.mpr ⟨StackMachineComposition.execution_reaches original.toEvalsTo, by rfl⟩
  rw [Turing.PartrecToTM2.tr_eval, source.correct] at evaluated
  obtain ⟨value, observed, same⟩ := (Part.mem_map_iff halt).mp evaluated
  obtain ⟨output, computed, words⟩ := (Part.mem_map_iff (fun output => [codec.encode output])).mp observed
  have rawSame : halt [codec.encode output] = halt numbers := by simpa only [← words] using same
  have physical := congrArg (FiniteCompiledMachine.embed source.code) rawSame
  simp only [FiniteCompiledMachine.halt_agrees] at physical
  have finalSame : final = haltList (machine source) (answer codec output) := canonical.trans physical.symm
  exact ⟨output, computed, finalSame, ⟨by
    simpa only [finalSame, TM2OutputsInTime, Option.map_some] using executed⟩⟩

def contextMachine (source : Presentation codec algorithm) : FinTM2 :=
  FiniteCompiledMachine.contextMachine source.code

/-- The fixed source uses separate input fields; all additional physical
argument/result copying remains in this bound. -/
def context_outputs (source : Presentation codec algorithm) {program condition output : BinString} {time : Nat}
    (executed : TM2OutputsInTime (machine source) (query codec program condition) (some (answer codec output)) time) :
    TM2OutputsInTime (contextMachine source) (query codec program condition)
      (some (StackMachineContextCall.packet (machine source) (query codec program condition) (answer codec output)))
      (time + 3 * (query codec program condition).length + 2 * (answer codec output).length + 5) :=
  FiniteCompiledMachine.context_outputs source.code (FiniteCompiledMachine.reflects_outputs source.code executed)

/-- An observed packet supplies both the original query and a genuine
conditional output, together with a counted original source execution. -/
theorem context_reflects_outputs (source : Presentation codec algorithm)
    {program condition : BinString}
    {returned : List (StackMachineContextCall.Cell (machine source))} {time : Nat}
    (executed : TM2OutputsInTime (contextMachine source) (query codec program condition) (some returned) time) :
    ∃ output : BinString, output ∈ algorithm program condition ∧
      StackMachineContextCall.packet (machine source) (query codec program condition) (answer codec output) = returned ∧
      Nonempty (TM2OutputsInTime (machine source) (query codec program condition) (some (answer codec output)) time) := by
  obtain ⟨numbers, packet, ⟨original⟩⟩ := FiniteCompiledMachine.context_reflects_outputs source.code executed
  have evaluated : halt numbers ∈ StateTransition.eval (TM2.step tr)
      (init source.code [codec.encode program, codec.encode condition]) :=
    StateTransition.mem_eval.mpr ⟨StackMachineComposition.execution_reaches original.toEvalsTo, by rfl⟩
  rw [Turing.PartrecToTM2.tr_eval, source.correct] at evaluated
  obtain ⟨value, observed, same⟩ := (Part.mem_map_iff halt).mp evaluated
  obtain ⟨output, computed, words⟩ := (Part.mem_map_iff (fun output => [codec.encode output])).mp observed
  have canonical : halt [codec.encode output] = halt numbers := by simpa only [← words] using same
  have physical := congrArg (fun state : Cfg' => state.stk K'.main) canonical
  have physicalWords : trList [codec.encode output] = trList numbers := physical
  have desired : EvalsToInTime (TM2.step tr) (init source.code [codec.encode program, codec.encode condition])
      (some (halt [codec.encode output])) time := by
    simpa only [← canonical] using original
  refine ⟨output, computed, ?_, ⟨FiniteCompiledMachine.outputs source.code desired⟩⟩
  change StackMachineContextCall.packet (FiniteCompiledMachine.machine source.code)
    (trList [codec.encode program, codec.encode condition]) (trList [codec.encode output]) = returned
  rw [physicalWords]
  exact packet

end Mettapedia.Machines.ConditionalSourceMachine
