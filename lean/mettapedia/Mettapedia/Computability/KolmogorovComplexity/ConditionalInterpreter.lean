import Mettapedia.Computability.KolmogorovComplexity.Conditional

/-!
# A computable universal interpreter with auxiliary input

Conditional prefix complexity and computable interpretation are separate
obligations.  `ConditionalPrefixFreeMachine` states the coding discipline.  This
file constructs the other half: a genuine partial-recursive interpreter that
uniformly simulates every partial-recursive two-input algorithm by prefixing a
fixed code to its program.

The interpreter below is a *plain* conditional interpreter; its payload program
is not asserted to be self-delimiting.  A universal conditional prefix machine
requires an effective enumeration that preserves prefix-free program domains.
Keeping that stronger construction separate prevents a plain interpreter from
silently being advertised as prefix-free.
-/

namespace KolmogorovComplexity

open scoped Classical

/-- A partial algorithm with a program and an auxiliary condition. -/
abbrev ConditionalAlgorithm := BinString → BinString →. BinString

/-- Uniform universality for conditional partial-recursive algorithms.  The
compiler prefix may depend on the simulated algorithm, but not on the payload
program, condition, or output. -/
def IsUniversalConditional (U : ConditionalAlgorithm) : Prop :=
  ∀ V : ConditionalAlgorithm, Partrec₂ V →
    ∃ compilerPrefix : BinString, ∀ p condition x,
      x ∈ V p condition → x ∈ U (compilerPrefix ++ p) condition

/-- Read the unary machine index at the front of a program.  Malformed inputs
containing no delimiter are assigned the length of the complete input; this
total default has no effect on compiler-generated programs. -/
def unaryMachineIndex (program : BinString) : Nat :=
  (program.takeWhile fun bit => bit).length

/-- Drop the unary index and its delimiter. -/
def unaryMachinePayload (program : BinString) : BinString :=
  program.drop (unaryMachineIndex program + 1)

theorem unaryMachineIndex_compiler (machineIndex : Nat) (payload : BinString) :
    unaryMachineIndex (machinePrefix machineIndex ++ payload) = machineIndex := by
  induction machineIndex with
  | zero => simp [unaryMachineIndex, machinePrefix]
  | succ n ih =>
      unfold unaryMachineIndex at ih ⊢
      simp [machinePrefix, ih]

theorem drop_machinePrefix_compiler (machineIndex : Nat) (payload : BinString) :
    (machinePrefix machineIndex ++ payload).drop (machineIndex + 1) = payload := by
  induction machineIndex with
  | zero => simp [machinePrefix]
  | succ n ih => simp [machinePrefix, ih, Nat.add_assoc]

theorem unaryMachinePayload_compiler (machineIndex : Nat) (payload : BinString) :
    unaryMachinePayload (machinePrefix machineIndex ++ payload) = payload := by
  rw [unaryMachinePayload, unaryMachineIndex_compiler]
  exact drop_machinePrefix_compiler machineIndex payload

theorem unaryMachineIndex_computable : Computable unaryMachineIndex := by
  unfold unaryMachineIndex
  exact Computable.list_length.comp
    (Primrec.list_takeWhile (_root_.Primrec.id : Primrec (fun bit : Bool => bit))).to_comp

theorem unaryMachinePayload_computable : Computable unaryMachinePayload := by
  unfold unaryMachinePayload
  exact Primrec.list_drop.to_comp.comp
    (Computable.succ.comp unaryMachineIndex_computable) Computable.id

/-- Interpret a unary-coded `Nat.Partrec.Code` on the encoded pair of payload
program and auxiliary condition. -/
noncomputable def universalConditionalAlgorithm : ConditionalAlgorithm :=
  fun program condition =>
    (Nat.Partrec.Code.eval
      (Nat.Partrec.Code.ofNatCode (unaryMachineIndex program))
      (Encodable.encode (unaryMachinePayload program, condition))).bind fun output =>
        Part.ofOption (Encodable.decode (α := BinString) output)

theorem universalConditionalAlgorithm_isUniversal :
    IsUniversalConditional universalConditionalAlgorithm := by
  classical
  intro V hV
  unfold Partrec₂ Partrec at hV
  obtain ⟨code, hcode⟩ := (Nat.Partrec.Code.exists_code).1 hV
  let compilerPrefix := machinePrefix (Nat.Partrec.Code.encodeCode code)
  refine ⟨compilerPrefix, ?_⟩
  intro p condition x hx
  have hindex :
      unaryMachineIndex (compilerPrefix ++ p) = Nat.Partrec.Code.encodeCode code := by
    simpa [compilerPrefix] using
      unaryMachineIndex_compiler (Nat.Partrec.Code.encodeCode code) p
  have hpayload : unaryMachinePayload (compilerPrefix ++ p) = p := by
    simpa [compilerPrefix] using
      unaryMachinePayload_compiler (Nat.Partrec.Code.encodeCode code) p
  have hdecoded :
      Nat.Partrec.Code.ofNatCode (Nat.Partrec.Code.encodeCode code) = code := by
    simpa [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.ofNatCode_eq] using
      (Denumerable.ofNat_encode (α := Nat.Partrec.Code) code)
  have hcodeApply :
      Nat.Partrec.Code.eval code (Encodable.encode (p, condition)) =
        (V p condition).map Encodable.encode := by
    have h := congrArg (fun f => f (Encodable.encode (p, condition))) hcode
    simpa using h
  have hxEncoded :
      Encodable.encode x ∈
        Nat.Partrec.Code.eval code (Encodable.encode (p, condition)) := by
    rw [hcodeApply]
    exact Part.mem_map Encodable.encode hx
  have hxDecoded :
      x ∈ Part.ofOption (Encodable.decode (α := BinString) (Encodable.encode x)) := by
    simp
  have hxBind :
      x ∈ (Nat.Partrec.Code.eval code (Encodable.encode (p, condition))).bind
        (fun output => Part.ofOption (Encodable.decode (α := BinString) output)) :=
    Part.mem_bind hxEncoded hxDecoded
  simpa [universalConditionalAlgorithm, hindex, hpayload, hdecoded] using hxBind

theorem exists_universalConditionalAlgorithm :
    ∃ U : ConditionalAlgorithm, IsUniversalConditional U :=
  ⟨universalConditionalAlgorithm, universalConditionalAlgorithm_isUniversal⟩

/-- The constructed interpreter is itself partial recursive in the program and
condition. -/
theorem universalConditionalAlgorithm_partrec :
    Partrec₂ universalConditionalAlgorithm := by
  unfold Partrec₂
  let Input := BinString × BinString
  have hCode : Computable (fun input : Input =>
      Nat.Partrec.Code.ofNatCode (unaryMachineIndex input.1)) := by
    simpa [Nat.Partrec.Code.ofNatCode_eq] using
      ((Computable.ofNat Nat.Partrec.Code).comp
        (unaryMachineIndex_computable.comp Computable.fst))
  have hArgument : Computable (fun input : Input =>
      Encodable.encode (unaryMachinePayload input.1, input.2)) := by
    exact Computable.encode.comp
      ((unaryMachinePayload_computable.comp Computable.fst).pair Computable.snd)
  have hEval : Partrec (fun input : Input =>
      Nat.Partrec.Code.eval
        (Nat.Partrec.Code.ofNatCode (unaryMachineIndex input.1))
        (Encodable.encode (unaryMachinePayload input.1, input.2))) :=
    Nat.Partrec.Code.eval_part.comp hCode hArgument
  have hDecode : Partrec₂ (fun (_input : Input) output =>
      Part.ofOption (Encodable.decode (α := BinString) output)) := by
    exact ((Computable.decode.comp Computable.snd).ofOption).to₂
  simpa [universalConditionalAlgorithm, Input] using hEval.bind hDecode

#print axioms universalConditionalAlgorithm_isUniversal
#print axioms universalConditionalAlgorithm_partrec

end KolmogorovComplexity
