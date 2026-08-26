import Mettapedia.Computability.KolmogorovComplexity.Prefix

/-!
# Conditional prefix-free complexity

This file separates three notions that are often conflated in informal uses of
algorithmic information:

* a prefix-free machine whose program domain may depend on a condition;
* shortest-program length relative to that machine and condition;
* a uniform, program-preserving simulation witness between two machines.

The simulation witness is deliberately explicit.  Merely assigning the name
"universal" to a machine is not evidence that it has a computable interpreter
with constant program overhead.

The convention for an output outside a machine's range follows the existing
prefix-complexity development: its infimum is represented by `0`.  Consequently
all comparison theorems carry `HasProgram` premises, and the final canary shows
why those premises are logically necessary.
-/

namespace KolmogorovComplexity

open scoped Classical

/-! ## Machines and relative conditional complexity -/

/-- A conditional prefix-free machine.  For every fixed condition, the halting
programs form a prefix-free set. -/
structure ConditionalPrefixFreeMachine where
  compute : BinString → BinString → Option BinString
  prefix_free : ∀ condition p q, p <+: q → p ≠ q →
    compute p condition ≠ none → compute q condition = none

/-- `p` produces `x` when the auxiliary condition is `condition`. -/
def IsProgram (U : ConditionalPrefixFreeMachine) (p condition x : BinString) : Prop :=
  U.compute p condition = some x

/-- The output `x` is represented under the given condition. -/
def HasProgram (U : ConditionalPrefixFreeMachine) (condition x : BinString) : Prop :=
  ∃ p, IsProgram U p condition x

/-- There is a program of length at most `n` for `x`, conditional on
`condition`. -/
def HasShortProgram (U : ConditionalPrefixFreeMachine)
    (condition x : BinString) (n : Nat) : Prop :=
  ∃ p, IsProgram U p condition x ∧ p.length ≤ n

noncomputable instance : DecidablePred (HasShortProgram U condition x) :=
  Classical.decPred _

/-- The least program length for a represented output. -/
noncomputable def minConditionalProgramLength
    (U : ConditionalPrefixFreeMachine) (condition x : BinString)
    (h : HasProgram U condition x) : Nat :=
  Nat.find (p := HasShortProgram U condition x)
    <| by
      obtain ⟨p, hp⟩ := h
      exact ⟨p.length, p, hp, le_rfl⟩

/-- Prefix-free conditional complexity relative to `U`.

As in the existing unconditional development, an unrepresented output is
assigned `0`; use `HasProgram` whenever that convention matters. -/
noncomputable def conditionalComplexity
    (U : ConditionalPrefixFreeMachine) (x condition : BinString) : Nat :=
  if h : HasProgram U condition x then
    minConditionalProgramLength U condition x h
  else 0

notation "Kc[" U "](" x " | " condition ")" =>
  conditionalComplexity U x condition

/-- Unconditional complexity induced by the distinguished empty condition. -/
noncomputable abbrev inducedPrefixComplexity
    (U : ConditionalPrefixFreeMachine) (x : BinString) : Nat :=
  Kc[U](x | [])

theorem exists_program_of_conditionalComplexity
    (U : ConditionalPrefixFreeMachine) (condition x : BinString)
    (h : HasProgram U condition x) :
    ∃ p, IsProgram U p condition x ∧ p.length = Kc[U](x | condition) := by
  unfold conditionalComplexity minConditionalProgramLength
  rw [dif_pos h]
  have hfind := Nat.find_spec (p := HasShortProgram U condition x)
    (show ∃ n, HasShortProgram U condition x n by
      obtain ⟨p, hp⟩ := h
      exact ⟨p.length, p, hp, le_rfl⟩)
  obtain ⟨p, hp, hlen⟩ := hfind
  refine ⟨p, hp, le_antisymm hlen ?_⟩
  apply Nat.find_min'
  exact ⟨p, hp, le_rfl⟩

theorem conditionalComplexity_le_program_length
    (U : ConditionalPrefixFreeMachine) (condition x p : BinString)
    (hp : IsProgram U p condition x) :
    Kc[U](x | condition) ≤ p.length := by
  unfold conditionalComplexity minConditionalProgramLength
  rw [dif_pos ⟨p, hp⟩]
  apply Nat.find_min'
  exact ⟨p, hp, le_rfl⟩

theorem conditionalComplexity_eq_zero_of_not_hasProgram
    (U : ConditionalPrefixFreeMachine) (condition x : BinString)
    (h : ¬ HasProgram U condition x) :
    Kc[U](x | condition) = 0 := by
  simp [conditionalComplexity, h]

/-- For each condition, the halting programs really are prefix-free. -/
theorem conditionalHaltingPrograms_prefixFree
    (U : ConditionalPrefixFreeMachine) (condition : BinString) :
    PrefixFree {p | U.compute p condition ≠ none} := by
  intro p hp q hq hpq hpref
  exact hq (U.prefix_free condition p q hpref hpq hp)

/-! ## Uniform simulation and invariance -/

/-- `U` simulates `M` with one fixed compiler prefix, uniformly in the
condition, program, and output.  This is stronger than mere agreement of
shortest output lengths. -/
structure UniformlySimulates
    (U M : ConditionalPrefixFreeMachine) : Type where
  compilerPrefix : BinString
  compute_eq : ∀ p condition,
    U.compute (compilerPrefix ++ p) condition = M.compute p condition

namespace UniformlySimulates

theorem program
    {U M : ConditionalPrefixFreeMachine} (simulation : UniformlySimulates U M)
    {p condition x : BinString} (hp : IsProgram M p condition x) :
    IsProgram U (simulation.compilerPrefix ++ p) condition x := by
  simpa [IsProgram, simulation.compute_eq] using hp

theorem hasProgram
    {U M : ConditionalPrefixFreeMachine} (simulation : UniformlySimulates U M)
    {condition x : BinString} (h : HasProgram M condition x) :
    HasProgram U condition x := by
  obtain ⟨p, hp⟩ := h
  exact ⟨simulation.compilerPrefix ++ p, simulation.program hp⟩

theorem conditionalComplexity_le
    {U M : ConditionalPrefixFreeMachine} (simulation : UniformlySimulates U M)
    {condition x : BinString} (h : HasProgram M condition x) :
    Kc[U](x | condition) ≤
      Kc[M](x | condition) + simulation.compilerPrefix.length := by
  obtain ⟨p, hp, hlen⟩ :=
    exists_program_of_conditionalComplexity M condition x h
  have hU := conditionalComplexity_le_program_length U condition x
    (simulation.compilerPrefix ++ p) (simulation.program hp)
  simpa [List.length_append, hlen, Nat.add_comm] using hU

/-- Simulation is transitive, and compiler overheads compose by
concatenation. -/
def trans
    {U M V : ConditionalPrefixFreeMachine}
    (hUM : UniformlySimulates U M) (hMV : UniformlySimulates M V) :
    UniformlySimulates U V where
  compilerPrefix := hUM.compilerPrefix ++ hMV.compilerPrefix
  compute_eq := by
    intro p condition
    rw [List.append_assoc, hUM.compute_eq, hMV.compute_eq]

/-- Every machine uniformly simulates itself with an empty compiler prefix. -/
def refl (U : ConditionalPrefixFreeMachine) : UniformlySimulates U U where
  compilerPrefix := []
  compute_eq := by simp

end UniformlySimulates

/-- Two machines have conditionally invariant complexities when each uniformly
simulates the other. -/
structure UniformSimulationEquiv
    (U V : ConditionalPrefixFreeMachine) : Type where
  forward : UniformlySimulates U V
  backward : UniformlySimulates V U

theorem conditionalComplexity_invariant
    {U V : ConditionalPrefixFreeMachine}
    (equiv : UniformSimulationEquiv U V) :
    ∃ c, ∀ condition x,
      HasProgram U condition x → HasProgram V condition x →
      |((Kc[U](x | condition) : Int) - Kc[V](x | condition))| ≤ (c : Int) := by
  let c := max equiv.forward.compilerPrefix.length
    equiv.backward.compilerPrefix.length
  refine ⟨c, ?_⟩
  intro condition x hU hV
  have hUV := equiv.forward.conditionalComplexity_le hV
  have hVU := equiv.backward.conditionalComplexity_le hU
  rw [abs_le]
  constructor <;> omega

/-! ## Pairing conditions and directional information -/

/-- A self-delimiting pairing of two conditions.  The first component is
length-delimited; the remaining bits are the second component. -/
def pairCondition (left right : BinString) : BinString :=
  machinePrefix left.length ++ left ++ right

theorem pairCondition_primrec : Primrec₂ pairCondition := by
  exact (Primrec.list_append.comp
    (Primrec.list_append.comp
      (machinePrefix_primrec.comp
        (Primrec.list_length.comp Primrec.fst))
      Primrec.fst)
    Primrec.snd).to₂

/-- Decode the length-delimited first condition and leave the remaining bits as
the second condition. -/
def unpairCondition (input : BinString) : Option (BinString × BinString) :=
  match decodeMachinePrefix input with
  | none => none
  | some (leftLength, rest) =>
      if leftLength ≤ rest.length then
        some (rest.take leftLength, rest.drop leftLength)
      else none

theorem unpairCondition_pairCondition (left right : BinString) :
    unpairCondition (pairCondition left right) = some (left, right) := by
  simp [unpairCondition, pairCondition, decodeMachinePrefix_machinePrefix]

theorem pairCondition_injective :
    Function.Injective (Function.uncurry pairCondition) := by
  rintro ⟨left, right⟩ ⟨left', right'⟩ h
  have hdecode := congrArg unpairCondition h
  simp [unpairCondition_pairCondition] at hdecode
  exact Prod.ext hdecode.1 hdecode.2

theorem pairCondition_length (left right : BinString) :
    (pairCondition left right).length =
      (machinePrefix left.length).length + left.length + right.length := by
  simp [pairCondition, List.length_append, Nat.add_assoc]

/-- Directional algorithmic information, represented in `Int` so that the
machine-dependent additive discrepancy is not hidden by truncated subtraction.
This is `K(x) - K(x | condition)`, not a claim of symmetry. -/
noncomputable def directedAlgorithmicInformation
    (U : ConditionalPrefixFreeMachine) (condition x : BinString) : Int :=
  (inducedPrefixComplexity U x : Int) - Kc[U](x | condition)

/-! ## Positive and negative controls -/

/-- A machine with one empty program: under condition `y`, it outputs `y`.
This is a genuine use of auxiliary information. -/
def conditionEchoMachine : ConditionalPrefixFreeMachine where
  compute := fun p condition => if p = [] then some condition else none
  prefix_free := by
    intro condition p q hpref hpq hp
    have hp_nil : p = [] := by
      by_contra hne
      simp [hne] at hp
    subst p
    have hq_nonempty : q ≠ [] := by
      intro hq
      exact hpq hq.symm
    simp [hq_nonempty]

/-- A condition-blind machine with one empty program and one fixed output. -/
def fixedEmptyMachine : ConditionalPrefixFreeMachine where
  compute := fun p _condition => if p = [] then some [] else none
  prefix_free := by
    intro condition p q hpref hpq hp
    have hp_nil : p = [] := by
      by_contra hne
      simp [hne] at hp
    subst p
    have hq_nonempty : q ≠ [] := by
      intro hq
      exact hpq hq.symm
    simp [hq_nonempty]

theorem conditionEchoMachine_hasProgram (condition : BinString) :
    HasProgram conditionEchoMachine condition condition := by
  exact ⟨[], by simp [IsProgram, conditionEchoMachine]⟩

theorem conditionEchoMachine_complexity (condition : BinString) :
    Kc[conditionEchoMachine](condition | condition) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact conditionalComplexity_le_program_length conditionEchoMachine condition condition []
    (by simp [IsProgram, conditionEchoMachine])

theorem conditionEchoMachine_not_hasProgram
    {condition x : BinString} (hne : x ≠ condition) :
    ¬ HasProgram conditionEchoMachine condition x := by
  rintro ⟨p, hp⟩
  simp only [IsProgram, conditionEchoMachine] at hp
  split at hp
  · exact hne (Option.some.inj hp).symm
  · simp at hp

theorem fixedEmptyMachine_condition_irrelevant
    (p left right : BinString) :
    fixedEmptyMachine.compute p left = fixedEmptyMachine.compute p right := by
  rfl

/-- The `0` convention cannot distinguish a genuine zero-length conditional
description from an absent description.  `HasProgram` must therefore remain an
explicit premise of semantic comparison theorems. -/
theorem zero_complexity_does_not_imply_representability :
    let condition : BinString := []
    let absent : BinString := [true]
    Kc[conditionEchoMachine](condition | condition) =
      Kc[conditionEchoMachine](absent | condition) ∧
    HasProgram conditionEchoMachine condition condition ∧
    ¬ HasProgram conditionEchoMachine condition absent := by
  dsimp
  have hAbsent : ¬ HasProgram conditionEchoMachine [] [true] :=
    conditionEchoMachine_not_hasProgram (by simp)
  refine ⟨?_, conditionEchoMachine_hasProgram [], hAbsent⟩
  calc
    Kc[conditionEchoMachine]([] | []) = 0 := conditionEchoMachine_complexity []
    _ = Kc[conditionEchoMachine]([true] | []) :=
      (conditionalComplexity_eq_zero_of_not_hasProgram _ _ _ hAbsent).symm

#print axioms exists_program_of_conditionalComplexity
#print axioms conditionalComplexity_invariant
#print axioms zero_complexity_does_not_imply_representability

end KolmogorovComplexity
