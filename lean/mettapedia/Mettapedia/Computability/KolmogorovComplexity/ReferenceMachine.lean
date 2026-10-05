import Mettapedia.Computability.KolmogorovComplexity.EffectiveConditionalPrefixInterpreter
import Mathlib.Computability.RE

/-!
# Effective reference machines

A reference machine is an effective conditional prefix machine that uniformly
simulates every effective conditional prefix machine. The trimmed indexed
host supplies a concrete reference machine. Compiler-prefix translations
compose with additive overhead and bound relative program complexity.
-/

set_option autoImplicit false

noncomputable section

namespace KolmogorovComplexity

/-! ## Reference machines and graded translation -/

/-- A conditional prefix machine is **effective** when its partial map from
programs and conditions to outputs is partial recursive. -/
def Effective (M : ConditionalPrefixFreeMachine) : Prop :=
  Partrec₂ fun program condition => Part.ofOption (M.compute program condition)

/-- A **reference machine** is effective and uniformly simulates every effective
machine. -/
def IsReferenceMachine (U : ConditionalPrefixFreeMachine) : Prop :=
  Effective U ∧ ∀ M, Effective M → Nonempty (UniformlySimulates U M)

/-- **A reference machine exists**: the trimmed indexed host. -/
theorem isReferenceMachine_trimmedIndexedHost : IsReferenceMachine trimmedIndexedHost :=
  ⟨trimmedIndexedHost_effective, trimmedIndexedHost_simulates_effective⟩

/-- `U` translates `V` at grade `n`: it runs every program of `V` behind one
compiler prefix of length at most `n`. -/
def Translates (U V : ConditionalPrefixFreeMachine) (n : Nat) : Prop :=
  ∃ simulation : UniformlySimulates U V, simulation.compilerPrefix.length ≤ n

theorem Translates.refl (U : ConditionalPrefixFreeMachine) : Translates U U 0 :=
  ⟨UniformlySimulates.refl U, le_rfl⟩

/-- **Translations compose, with the grades added.** -/
theorem Translates.trans {U V W : ConditionalPrefixFreeMachine} {m n : Nat}
    (first : Translates U V m) (second : Translates V W n) : Translates U W (m + n) := by
  obtain ⟨simulationUV, boundUV⟩ := first
  obtain ⟨simulationVW, boundVW⟩ := second
  refine ⟨simulationUV.trans simulationVW, ?_⟩
  change (simulationUV.compilerPrefix ++ simulationVW.compilerPrefix).length ≤ m + n
  rw [List.length_append]
  omega

theorem Translates.mono {U V : ConditionalPrefixFreeMachine} {m n : Nat} (le : m ≤ n)
    (translates : Translates U V m) : Translates U V n := by
  obtain ⟨simulation, bound⟩ := translates
  exact ⟨simulation, bound.trans le⟩

/-- **A translation bounds complexity by its grade.** -/
theorem Translates.complexity_le {U V : ConditionalPrefixFreeMachine} {n : Nat}
    (translates : Translates U V n) {condition x : BinString} (program : HasProgram V condition x) :
    Kc[U](x | condition) ≤ Kc[V](x | condition) + n := by
  obtain ⟨simulation, bound⟩ := translates
  have := simulation.conditionalComplexity_le program
  omega

/-- **Any two reference machines translate into each other.** -/
theorem IsReferenceMachine.translates {U V : ConditionalPrefixFreeMachine}
    (referenceU : IsReferenceMachine U) (referenceV : IsReferenceMachine V) :
    ∃ n, Translates U V n := by
  obtain ⟨simulation⟩ := referenceU.2 V referenceV.1
  exact ⟨_, simulation, le_rfl⟩

/-- **Invariance**: the complexities of two reference machines are within a
constant. -/
theorem IsReferenceMachine.invariance {U V : ConditionalPrefixFreeMachine}
    (referenceU : IsReferenceMachine U) (referenceV : IsReferenceMachine V) :
    ∃ c, ∀ condition x, HasProgram U condition x → HasProgram V condition x →
      |((Kc[U](x | condition) : Int) - Kc[V](x | condition))| ≤ (c : Int) := by
  obtain ⟨forward⟩ := referenceU.2 V referenceV.1
  obtain ⟨backward⟩ := referenceV.2 U referenceU.1
  exact conditionalComplexity_invariant ⟨forward, backward⟩

/-- An effective conditional reference machine together with its simulation
witness. -/
structure ReferenceMachine where
  machine : ConditionalPrefixFreeMachine
  reference : IsReferenceMachine machine

/-- The trimmed indexed host as a reference machine. -/
noncomputable def ReferenceMachine.canonical : ReferenceMachine where
  machine := trimmedIndexedHost
  reference := isReferenceMachine_trimmedIndexedHost

/-- A singleton-output machine with one empty program. -/
def constantOutputMachine (x : BinString) : ConditionalPrefixFreeMachine where
  compute := fun program _condition => if program = [] then some x else none
  prefix_free := by
    intro condition p q _ distinct halts
    have hp : p = [] := by
      by_contra hp
      exact halts (by simp [hp])
    have hq : q ≠ [] := by
      intro hq
      exact distinct (hp.trans hq.symm)
    simp [hq]

theorem constantOutputMachine_effective (x : BinString) :
    Effective (constantOutputMachine x) := by
  unfold Effective Partrec₂
  have test : Computable fun input : BinString × BinString => decide (input.1 = []) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const [])).decide.to_comp
  refine (Partrec.cond test (Partrec.const' (Part.some x)) Partrec.none).of_eq ?_
  rintro ⟨program, condition⟩
  by_cases h : program = [] <;> simp [constantOutputMachine, h, Part.ofOption]

/-- Effective universality entails output completeness at every condition. -/
theorem IsReferenceMachine.hasProgram {U : ConditionalPrefixFreeMachine}
    (reference : IsReferenceMachine U) (condition x : BinString) :
    HasProgram U condition x := by
  obtain ⟨simulation⟩ := reference.2 (constantOutputMachine x)
    (constantOutputMachine_effective x)
  exact simulation.hasProgram ⟨[], by simp [IsProgram, constantOutputMachine]⟩

/-- Ordinary complexity and prediction use the empty auxiliary condition. -/
def ReferenceMachine.toPrefixFreeMachine (U : ReferenceMachine) :
    Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine :=
  conditionalSlice U.machine []

instance : Coe ReferenceMachine Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine :=
  ⟨ReferenceMachine.toPrefixFreeMachine⟩

instance ReferenceMachine.slice_outputComplete (U : ReferenceMachine) (condition : BinString) :
    Mettapedia.UniversalAI.SolomonoffPrior.OutputComplete
      (conditionalSlice U.machine condition) :=
  ⟨U.reference.hasProgram condition⟩

instance ReferenceMachine.outputComplete (U : ReferenceMachine) :
    Mettapedia.UniversalAI.SolomonoffPrior.OutputComplete
      (U : Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine) :=
  U.slice_outputComplete []

/-- One-sided invariance against any effective competitor, on its outputs. -/
theorem IsReferenceMachine.invariance_le {U V : ConditionalPrefixFreeMachine}
    (reference : IsReferenceMachine U) (effective : Effective V) :
    ∃ c, ∀ condition x, HasProgram V condition x →
      Kc[U](x | condition) ≤ Kc[V](x | condition) + c := by
  obtain ⟨simulation⟩ := reference.2 V effective
  exact ⟨simulation.compilerPrefix.length,
    fun _ _ represented => simulation.conditionalComplexity_le represented⟩

theorem ReferenceMachine.invariance_le (U V : ReferenceMachine) :
    ∃ c, ∀ x,
      Mettapedia.UniversalAI.SolomonoffPrior.kolmogorovComplexity U x ≤
        Mettapedia.UniversalAI.SolomonoffPrior.kolmogorovComplexity V x + c := by
  obtain ⟨c, bound⟩ := U.reference.invariance_le V.reference.1
  refine ⟨c, fun x => ?_⟩
  have h := bound [] x (V.reference.hasProgram [] x)
  simpa only [conditionalComplexity_eq_kolmogorovComplexity_slice,
    ReferenceMachine.toPrefixFreeMachine] using h

#print axioms isReferenceMachine_trimmedIndexedHost
#print axioms Translates.trans
#print axioms Translates.complexity_le
#print axioms IsReferenceMachine.invariance

end KolmogorovComplexity
