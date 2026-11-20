import Mettapedia.Machines.TIsa.RegisterProfile

/-!
# RegisterCode block lowering with actual source-register admission

A translation supplies an executable instruction selector, exact source
readback and a proof about RegisterCode's original single-step executor.
The shared list lowering, execution and liveness results use those local
proofs. Availability is computed from the caller's actual register file.
Native component certificates and code placement remain separate contracts.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.RegisterCodeLowering
universe u
abbrev Values := Fin 12 → Word
abbrev SourceInstruction := RegisterCode.Instr Word Scalar Nat Nat

def valuesAt (values : Values) (register : Nat) : Word :=
  if within : register < 12 then values ⟨register,within⟩ else 0

theorem valuesAt_fin (values : Values) (register : Fin 12) :
    valuesAt values register.val = values register := by simp [valuesAt,register.isLt]

theorem valuesAt_update (values : Values) (destination : Fin 12) (result : Word) :
    valuesAt (Function.update values destination result) =
      Function.update (valuesAt values) destination.val result := by
  funext register
  by_cases same : register = destination.val
  · subst register
    simp [valuesAt,destination.isLt]
  · by_cases within : register < 12
    · have distinct : (⟨register,within⟩ : Fin 12) ≠ destination := fun equal => same (congrArg Fin.val equal)
      simp [valuesAt,within,Function.update_of_ne same,Function.update_of_ne distinct]
    · simp [valuesAt,within,Function.update_of_ne same]

def lowerCode? {Instruction : Type u} (lower : SourceInstruction → Option Instruction) :
    List SourceInstruction → Option (List Instruction)
  | [] => some []
  | input :: later => do
      let instruction ← lower input
      let following ← lowerCode? lower later
      some (instruction :: following)

theorem lowerCode?_source {Instruction : Type u}
    (lower : SourceInstruction → Option Instruction) (source : Instruction → SourceInstruction)
    (exactSource : ∀ input instruction, lower input = some instruction → source instruction = input)
    {inputs : List SourceInstruction} {instructions : List Instruction}
    (accepted : lowerCode? lower inputs = some instructions) : instructions.map source = inputs := by
  induction inputs generalizing instructions with
  | nil => simpa [lowerCode?] using accepted.symm
  | cons input later ih =>
    cases first : lower input with
    | none => simp [lowerCode?,first] at accepted
    | some instruction =>
      cases rest : lowerCode? lower later with
      | none => simp [lowerCode?,first,rest] at accepted
      | some following =>
        have same : instruction :: following = instructions := by simpa [lowerCode?,first,rest] using accepted
        subst instructions
        simp only [List.map_cons,exactSource input instruction first,ih rest]

theorem lowerCode?_roundtrip {Instruction : Type u}
    (lower : SourceInstruction → Option Instruction) (source : Instruction → SourceInstruction)
    (roundtrip : ∀ instruction, lower (source instruction) = some instruction)
    (instructions : List Instruction) : lowerCode? lower (instructions.map source) = some instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction later ih => simp [lowerCode?,roundtrip,ih]

structure Translation (Instruction : Type u) where
  lower : SourceInstruction → Option Instruction
  source : Instruction → SourceInstruction
  update : Instruction → Values → Values
  source_exact : ∀ input instruction, lower input = some instruction → source instruction = input
  step : ∀ instruction values,
    RegisterCode.step RegisterProfile.semantics (fun _ _ => none) (source instruction)
      (RegisterProfile.initialized (valuesAt values)) =
      some (.next (RegisterProfile.initialized (valuesAt (update instruction values))))

def finalValues {Instruction : Type u} (translation : Translation Instruction)
    (instructions : List Instruction) (values : Values) : Values :=
  instructions.foldl (fun before instruction => translation.update instruction before) values

theorem source_exec {Instruction : Type u} (translation : Translation Instruction)
    (instructions : List Instruction) (values : Values) :
    RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) (instructions.map translation.source)
      (RegisterProfile.initialized (valuesAt values)) =
      some (.next (RegisterProfile.initialized (valuesAt (finalValues translation instructions values)))) := by
  induction instructions generalizing values with
  | nil => rfl
  | cons instruction later ih =>
    simp only [List.map_cons,RegisterCode.exec,translation.step,RegisterCode.andThen,ih,
      finalValues,List.foldl_cons]

def available (registers : RegisterCode.Regs Word) : Finset Nat :=
  (Finset.range 12).filter fun register => (registers register).isSome

def valuesOf (registers : RegisterCode.Regs Word) (register : Fin 12) : Word :=
  (registers register.val).getD 0

def admit? {Instruction : Type u} (lower : SourceInstruction → Option Instruction)
    (inputs : List SourceInstruction) (registers : RegisterCode.Regs Word) (out : Finset Nat) :
    Option (List Instruction) :=
  if RegisterProfile.initialCheck inputs (available registers) out then lowerCode? lower inputs else none

theorem admit?_checks {Instruction : Type u} (lower : SourceInstruction → Option Instruction)
    {inputs : List SourceInstruction} {registers : RegisterCode.Regs Word} {out : Finset Nat}
    {instructions : List Instruction} (accepted : admit? lower inputs registers out = some instructions) :
    lowerCode? lower inputs = some instructions ∧
      RegisterProfile.initialCheck inputs (available registers) out = true := by
  unfold admit? at accepted
  split at accepted
  · rename_i checked
    exact ⟨accepted,checked⟩
  · cases accepted

theorem available_readback (registers : RegisterCode.Regs Word) (register : Nat)
    (present : register ∈ available registers) :
    registers register = some (valuesAt (valuesOf registers) register) := by
  obtain ⟨within,initialized⟩ := Finset.mem_filter.mp present
  have bounded := Finset.mem_range.mp within
  cases seen : registers register with
  | none => simp [seen] at initialized
  | some value => simp [valuesAt,valuesOf,bounded,seen]

theorem admitted_source_exec_on {Instruction : Type u} (translation : Translation Instruction)
    (inputs : List SourceInstruction) (registers : RegisterCode.Regs Word) (out : Finset Nat)
    (instructions : List Instruction) (accepted : admit? translation.lower inputs registers out = some instructions) (values : Values)
    (known : ∀ register ∈ available registers, registers register = some (valuesAt values register)) :
    ∃ following,
      RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) inputs registers = some (.next following) ∧
      ∀ register ∈ out,
        following register = some (valuesAt (finalValues translation instructions values) register) := by
  obtain ⟨lowered,checked⟩ := admit?_checks translation.lower accepted
  have related := RegisterCode.exec_live RegisterProfile.semantics (fun _ _ => none) inputs out
    (RegisterProfile.initialized (valuesAt values)) registers (by
      intro register live
      have present := (RegisterProfile.initialCheck_iff inputs (available registers) out).mp checked live
      exact (known register present).symm)
  have total := source_exec translation instructions values
  rw [lowerCode?_source translation.lower translation.source translation.source_exact lowered] at total
  rw [total] at related
  cases execution : RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) inputs registers with
  | none => rw [execution] at related; cases related
  | some result =>
    rw [execution] at related
    cases related with
    | some agrees =>
      cases result with
      | ret value => cases agrees
      | next following => exact ⟨following,rfl,fun register present => (agrees register present).symm⟩

theorem admitted_source_exec {Instruction : Type u} (translation : Translation Instruction)
    (inputs : List SourceInstruction) (registers : RegisterCode.Regs Word) (out : Finset Nat)
    (instructions : List Instruction) (accepted : admit? translation.lower inputs registers out = some instructions) :
    ∃ following,
      RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) inputs registers = some (.next following) ∧
      ∀ register ∈ out,
        following register = some (valuesAt (finalValues translation instructions (valuesOf registers)) register) :=
  admitted_source_exec_on translation inputs registers out instructions accepted (valuesOf registers)
    (available_readback registers)

#print axioms lowerCode?_source
#print axioms lowerCode?_roundtrip
#print axioms valuesAt_update
#print axioms source_exec
#print axioms admit?_checks
#print axioms available_readback
#print axioms admitted_source_exec_on
#print axioms admitted_source_exec
end Mettapedia.Machines.TIsa.RegisterCodeLowering
