import Mettapedia.Computability.KolmogorovComplexity.ConditionalPrefixBridge
import Mettapedia.Computability.KolmogorovComplexity.ContainmentRepair
import Mettapedia.Computability.KolmogorovComplexity.EffectiveConditionalPrefixInterpreter
import Mettapedia.UniversalAI.TimeBoundedAIXI.ProofEnumeration

/-!
# The effective boundary of universal prefix machines

The standard invariance theorem ranges over an effectively enumerable class of
partial computable prefix machines.  The historical `UniversalPFM` interface in
this development instead ranges over every `PrefixFreeMachine`, whose `compute`
field is an unrestricted set-theoretic function.  This file proves that no
machine can satisfy that stronger interface.

The proof is a bounded diagonalization.  For each length bound, finitely
enumerate all programs up to that bound and choose an output longer than every
output they produce.  A prefix machine with self-delimiting literal programs
then defeats every proposed additive simulation constant.

This is a boundary theorem, not a rejection of Solomonoff induction.  It shows
that subsequent invariance and algorithmic-containment work must quantify over
an effective, indexed family of machines rather than over arbitrary functions.

All proofs are kernel-checked and introduce no additional axioms.
-/

namespace Mettapedia.UniversalAI.UniversalMachineBoundary

open scoped Classical
open KolmogorovComplexity
open Mettapedia.UniversalAI.TimeBoundedAIXI

/-! ## A fresh output beyond every bounded program -/

/-- Outputs produced by programs whose length is at most `bound`. -/
def boundedOutputs (U : PrefixFreeMachine) (bound : Nat) : List BinString :=
  (bitstringsUpTo bound).filterMap U.compute

/-- Maximum output length seen among programs up to `bound`. -/
def boundedOutputLength (U : PrefixFreeMachine) (bound : Nat) : Nat :=
  (boundedOutputs U bound).foldr (fun output current => max output.length current) 0

theorem length_le_foldr_max_of_mem (outputs : List BinString) {output : BinString}
    (h : output ∈ outputs) :
    output.length ≤ outputs.foldr (fun item current => max item.length current) 0 := by
  induction outputs with
  | nil => simp at h
  | cons head tail ih =>
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact le_trans (ih h) (Nat.le_max_right _ _)

theorem output_length_le_boundedOutputLength
    (U : PrefixFreeMachine) {bound : Nat} {program output : BinString}
    (hLength : program.length ≤ bound) (hCompute : U.compute program = some output) :
    output.length ≤ boundedOutputLength U bound := by
  apply length_le_foldr_max_of_mem
  apply List.mem_filterMap.mpr
  exact ⟨program, mem_bitstringsUpTo_of_length_le hLength, hCompute⟩

/-- A concrete output outside the range of every program up to `bound`. -/
def freshBoundedOutput (U : PrefixFreeMachine) (bound : Nat) : BinString :=
  List.replicate (boundedOutputLength U bound + 1) false

theorem freshBoundedOutput_length (U : PrefixFreeMachine) (bound : Nat) :
    (freshBoundedOutput U bound).length = boundedOutputLength U bound + 1 := by
  simp [freshBoundedOutput]

theorem freshBoundedOutput_not_produced
    (U : PrefixFreeMachine) (bound : Nat) (program : BinString)
    (hLength : program.length ≤ bound) :
    U.compute program ≠ some (freshBoundedOutput U bound) := by
  intro hCompute
  have hle := output_length_le_boundedOutputLength U hLength hCompute
  rw [freshBoundedOutput_length] at hle
  omega

/-! ## A diagonal prefix machine -/

/-- Map the outputs of a prefix machine without changing its program domain. -/
def mapOutputs (M : PrefixFreeMachine) (f : BinString → BinString) :
    PrefixFreeMachine where
  compute := fun program => (M.compute program).map f
  prefix_free := by
    intro program extension isPrefix distinct halts
    have sourceHalts : M.compute program ≠ none := by
      intro sourceDoesNotHalt
      simp [sourceDoesNotHalt] at halts
    have extensionDoesNotHalt :=
      M.prefix_free program extension isPrefix distinct sourceHalts
    simp [extensionDoesNotHalt]

/-- The conditional literal machine specialized to the empty condition. -/
def e1LiteralPrefixMachine : PrefixFreeMachine where
  compute := fun program => literalMachine.compute program []
  prefix_free := literalMachine.prefix_free []

theorem e1LiteralPrefixMachine_compute (literal : BinString) :
    e1LiteralPrefixMachine.compute (e1encode literal) = some literal := by
  have decoded := e1decode_e1encode_append literal []
  rw [List.append_nil] at decoded
  simp [e1LiteralPrefixMachine, literalMachine, decoded]

/-- Against a proposed host `U`, literal `index` denotes an output that no `U`
program of length at most twice the literal-program length can produce. -/
def diagonalMachine (U : PrefixFreeMachine) : PrefixFreeMachine :=
  mapOutputs e1LiteralPrefixMachine fun index =>
    freshBoundedOutput U (2 * (e1encode index).length)

theorem diagonalMachine_compute (U : PrefixFreeMachine) (index : BinString) :
    (diagonalMachine U).compute (e1encode index) =
      some (freshBoundedOutput U (2 * (e1encode index).length)) := by
  simp [diagonalMachine, mapOutputs, e1LiteralPrefixMachine_compute]

/-! ## The historical unrestricted interface is uninhabited -/

/-- No prefix machine can additively simulate every arbitrary set-theoretic
prefix machine.  Effective universality must restrict the competitor class. -/
theorem no_unrestrictedUniversalPFM (U : PrefixFreeMachine) :
    ¬ UniversalPFM U := by
  intro universal
  obtain ⟨constant, simulation⟩ := universal.universal (M := diagonalMachine U)
  let index : BinString := List.replicate (constant + 1) false
  let program : BinString := e1encode index
  let output : BinString :=
    freshBoundedOutput U (2 * program.length)
  have programLonger : constant < program.length := by
    simp [program, index, e1encode_length]
    omega
  have diagonalComputes : (diagonalMachine U).compute program = some output := by
    simpa [program, output] using diagonalMachine_compute U index
  obtain ⟨hostProgram, hostComputes, hostLength⟩ :=
    simulation program output diagonalComputes
  have hostBound : hostProgram.length ≤ 2 * program.length := by
    omega
  exact freshBoundedOutput_not_produced U (2 * program.length) hostProgram
    hostBound hostComputes

/-- The corresponding unrestricted conditional interface is also uninhabited:
its empty-condition slice would instantiate the impossible ordinary one. -/
theorem no_unrestrictedUniformlyUniversalConditionalPFM
    (U : ConditionalPrefixFreeMachine) :
    UniformlyUniversalConditionalPFM U → False := by
  intro universal
  letI : UniformlyUniversalConditionalPFM U := universal
  exact no_unrestrictedUniversalPFM (conditionalSlice U [])
    (inferInstance : UniversalPFM (conditionalSlice U []))

/-! ## Consequences of the effective indexed replacement

`EffectiveConditionalPrefixInterpreter` constructs the real replacement:
`trimmedConditionalEnumeration` contains every effective conditional prefix
machine, and `trimmedIndexedHost` uniformly compiles every one of its indices.
The declarations below derive the chain-rule interface and retain a deliberately
small negative-control enumeration. -/

/-- The constructive upper chain rule needs only that the effective
enumeration contain the concatenating pair machine.  It does not need the
impossible quantification over arbitrary set-theoretic machines. -/
noncomputable def upperConditionalChainRule_of_indexedUniversality
    (enumeration : EffectiveConditionalPFMEnumeration)
    (host : ConditionalPrefixFreeMachine)
    (universal : IndexedUniversalConditionalPFM enumeration host)
    (pairMachineIndex : Nat)
    (containsPairMachine :
      enumeration.machineAt pairMachineIndex = chainPairMachine host) :
    UpperConditionalChainRule host :=
  UpperConditionalChainRule.ofPairSimulation
    (containsPairMachine ▸ universal.simulatesCode pairMachineIndex)

/-! ### The effective positive theorem -/

/-- The concrete trimmed host is itself effective and uniformly simulates
every effective conditional prefix machine.  This is the machine-universality
claim used by conditional complexity and algorithmic containment.  It is not a
claim about one policy maximizing value in every environment. -/
theorem effectiveConditionalPrefixMachine_has_fixedCompiler
    (M : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (M.compute program condition)) :
    Nonempty (UniformlySimulates trimmedIndexedHost M) :=
  trimmedIndexedHost_simulates_effective M hEffective

/-- The concrete host closes both obligations: it is an effective partial
algorithm and is universal over the effective prefix-machine class. -/
theorem exists_effectiveIndexedUniversalConditionalPFM :
    ∃ enumeration : EffectiveConditionalPFMEnumeration,
      ∃ host : ConditionalPrefixFreeMachine,
        Partrec₂ (fun program condition =>
          Part.ofOption (host.compute program condition)) ∧
        Nonempty (IndexedUniversalConditionalPFM enumeration host) :=
  ⟨trimmedConditionalEnumeration, trimmedIndexedHost,
    trimmedIndexedHost_effective, ⟨trimmedIndexedUniversality⟩⟩

/-! ### Positive boundary canary -/

/-- An effective enumeration whose every index names the nowhere-defined
machine.  This deliberately small canary checks the replacement interface;
it is not presented as a universal model of computation. -/
def nowhereEnumeration : EffectiveConditionalPFMEnumeration where
  compute := fun _index _program _condition => none
  prefix_free := by simp
  effective := by
    simpa using
      (Partrec.none : Partrec fun _input : Nat × (BinString × BinString) =>
        (Part.none : Part BinString))

/-- The nowhere-defined host machine. -/
def nowhereHost : ConditionalPrefixFreeMachine where
  compute := fun _program _condition => none
  prefix_free := by simp

/-- Relative to `nowhereEnumeration`, `nowhereHost` is genuinely indexed
universal: its compute equation holds for every index, program, and condition. -/
def nowhereIndexedSimulation :
    IndexedUniversalConditionalPFM nowhereEnumeration nowhereHost where
  compilerPrefix := fun _index => []
  compute_eq := by simp [nowhereHost, nowhereEnumeration]

theorem nowhereIndexedSimulation_compute
    (index : Nat) (program condition : BinString) :
    nowhereHost.compute
        (nowhereIndexedSimulation.compilerPrefix index ++ program) condition =
      nowhereEnumeration.compute index program condition := by
  exact nowhereIndexedSimulation.compute_eq index program condition

#print axioms freshBoundedOutput_not_produced
#print axioms no_unrestrictedUniversalPFM
#print axioms no_unrestrictedUniformlyUniversalConditionalPFM
#print axioms upperConditionalChainRule_of_indexedUniversality
#print axioms effectiveConditionalPrefixMachine_has_fixedCompiler
#print axioms exists_effectiveIndexedUniversalConditionalPFM
#print axioms nowhereIndexedSimulation_compute

end Mettapedia.UniversalAI.UniversalMachineBoundary
