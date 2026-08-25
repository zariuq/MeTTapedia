import Mettapedia.Enactive.GeneralizationOptimality
import Mettapedia.UniversalAI.ZetaProgramPrior
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Stochastic task processes and the boundary of weakness optimality

Michael Timothy Bennett's finite generalization theorem uses a uniform law on
subsets of future demands.  Eray Ozkural, *Zeta Distribution and Transfer
Learning Problem* (arXiv:1806.08908, 2018), instead studies a training sequence
as a stochastic process and distinguishes four models:

* independent uniform fixed-width programs (random typing, section 3.3);
* independent zeta-ranked programs (section 3.5);
* programs assembled from a shared subprogram database (section 3.6);
* sequential zeta-distributed mutations, retaining the prior program when a
  sampled transformation is invalid (section 3.7, equations 32--33).

This file gives all four models one history-indexed `PMF` interface.  It then
states the exact condition under which a stochastic law preserves Bennett's
weakness ordering.  Process structure alone is not enough: a strictly increasing
factorization of success probability through weakness is sufficient, while a
biased two-outcome process is an explicit negative control.  Thus the uniform
theorem survives where its symmetry survives; zeta or evolutionary structure
does not silently imply a transfer theorem.

Entropy is represented only with an explicit summability certificate.  The file
does not assert the numerical entropy approximations or feasibility claims in
Ozkural's paper.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.StochasticTaskProcess

open scoped BigOperators

universe uTask uCandidate uProgram uInstruction uMutation

/-! ## General history-indexed process -/

/-- A discrete stochastic task process.  `next history` is the predictive law
for the next task after the exact chronological history. -/
structure TaskProcess (Task : Type uTask) where
  next : List Task → PMF Task

namespace TaskProcess

variable {Task : Type uTask}

/-- An independent identically distributed process ignores its history. -/
def iid (law : PMF Task) : TaskProcess Task where
  next := fun _ ↦ law

@[simp]
theorem iid_next (law : PMF Task) (history : List Task) :
    (iid law).next history = law := rfl

/-- Probability that a candidate handles the next task.  The full task law is
retained; this scalar is only a derived observation. -/
noncomputable def successProbability (process : TaskProcess Task)
    {Candidate : Type uCandidate} (handles : Candidate → Task → Prop)
    (history : List Task) (candidate : Candidate) : ENNReal :=
  (process.next history).toOuterMeasure {task | handles candidate task}

/-- The process preserves a weakness order at one history exactly when its
next-task success probabilities induce the same preorder on candidates. -/
def PreservesWeaknessAt (process : TaskProcess Task)
    {Candidate : Type uCandidate} (handles : Candidate → Task → Prop)
    (weakness : Candidate → ℕ) (history : List Task) : Prop :=
  ∀ left right,
    process.successProbability handles history left ≤
        process.successProbability handles history right ↔
      weakness left ≤ weakness right

/-- A concrete sufficient certificate: success factors through weakness by a
strictly increasing curve.  This is stronger than merely selecting a weakness
maximizer and is therefore kept as an explicit premise. -/
structure CardinalityFactorizationAt (process : TaskProcess Task)
    {Candidate : Type uCandidate} (handles : Candidate → Task → Prop)
    (weakness : Candidate → ℕ) (history : List Task) where
  curve : ℕ → ENNReal
  curve_strictMono : StrictMono curve
  success_eq : ∀ candidate,
    process.successProbability handles history candidate = curve (weakness candidate)

theorem preservesWeaknessAt_of_cardinalityFactorization
    (process : TaskProcess Task)
    {Candidate : Type uCandidate} (handles : Candidate → Task → Prop)
    (weakness : Candidate → ℕ) (history : List Task)
    (certificate : CardinalityFactorizationAt process handles weakness history) :
    PreservesWeaknessAt process handles weakness history := by
  intro left right
  rw [certificate.success_eq left, certificate.success_eq right,
    certificate.curve_strictMono.le_iff_le]

/-! ### Entropy with an honest existence boundary -/

/-- Shannon entropy summand in bits, with the standard `0 log 0 = 0`
convention. -/
noncomputable def entropyTerm (law : PMF Task) (task : Task) : ℝ :=
  if law task = 0 then 0
  else -(law task).toReal *
    (Real.log (law task).toReal / Real.log 2)

/-- The exact finiteness premise required before reading a real-valued entropy
from a countable PMF. -/
def HasFiniteEntropy (law : PMF Task) : Prop :=
  Summable (entropyTerm law)

/-- Entropy is exposed only together with a summability certificate. -/
noncomputable def entropy (law : PMF Task) (_finite : HasFiniteEntropy law) : ℝ :=
  ∑' task, entropyTerm law task

/-- Conditional next-task entropy at a named history. -/
def HasFiniteNextEntropy (process : TaskProcess Task) (history : List Task) : Prop :=
  HasFiniteEntropy (process.next history)

end TaskProcess

/-! ## Ozkural's four process presentations -/

namespace Ozkural

/-! ### Random typing -/

/-- A source-faithful random-typing model: every fixed-width bit program has
the same mass.  The normalization is carried by `PMF`; equiprobability is not
inferred from the type. -/
structure RandomTypingModel (width : ℕ) where
  law : PMF (Fin width → Bool)
  equiprobable : ∀ left right, law left = law right

def RandomTypingModel.toProcess {width : ℕ}
    (model : RandomTypingModel width) : TaskProcess (Fin width → Bool) :=
  TaskProcess.iid model.law

/-- Random typing has no predictive update from the task history: this is the
precise process-level content behind its no-transfer role in Ozkural's section
3.3, without asserting a universal no-free-lunch theorem. -/
theorem RandomTypingModel.history_independent {width : ℕ}
    (model : RandomTypingModel width)
    (leftHistory rightHistory : List (Fin width → Bool)) :
    model.toProcess.next leftHistory = model.toProcess.next rightHistory := rfl

/-! ### Independent zeta tasks -/

/-- Independent zeta-ranked programs, corresponding to Ozkural's section 3.5.
The bijective enumeration is the normalization boundary proved in
`ZetaProgramPrior`. -/
noncomputable def independentZetaProcess {Program : Type uProgram}
    (enumeration : Mettapedia.UniversalAI.ZetaProgramPrior.ProgramEnumeration Program)
    (exponent : Mettapedia.UniversalAI.ZetaProgramPrior.Exponent) :
    TaskProcess Program :=
  TaskProcess.iid (enumeration.pmf exponent)

theorem independentZetaProcess_is_iid {Program : Type uProgram}
    (enumeration : Mettapedia.UniversalAI.ZetaProgramPrior.ProgramEnumeration Program)
    (exponent : Mettapedia.UniversalAI.ZetaProgramPrior.Exponent)
    (leftHistory rightHistory : List Program) :
    (independentZetaProcess enumeration exponent).next leftHistory =
      (independentZetaProcess enumeration exponent).next rightHistory := rfl

/-! ### Shared subprogram database -/

/-- A program law assembled from a finite shared instruction database.
`codeLaw` is the joint law of the fixed-length instruction vector; it need not
be independent or uniform.  This preserves the informative object behind
Ozkural's section 3.6 instead of replacing it by an entropy scalar. -/
structure CommonSubprogramModel (Task : Type uTask)
    (Instruction : Type uInstruction) [DecidableEq Instruction] where
  database : Finset Instruction
  database_nonempty : database.Nonempty
  instructionCount : ℕ
  codeLaw : PMF (Fin instructionCount → Instruction)
  code_supported : ∀ code ∈ codeLaw.support,
    ∀ position, code position ∈ database
  assemble : (Fin instructionCount → Instruction) → Task

noncomputable def CommonSubprogramModel.programLaw
    {Task : Type uTask} {Instruction : Type uInstruction} [DecidableEq Instruction]
    (model : CommonSubprogramModel Task Instruction) : PMF Task :=
  model.codeLaw.map model.assemble

noncomputable def CommonSubprogramModel.toProcess
    {Task : Type uTask} {Instruction : Type uInstruction} [DecidableEq Instruction]
    (model : CommonSubprogramModel Task Instruction) : TaskProcess Task :=
  TaskProcess.iid model.programLaw

theorem CommonSubprogramModel.programLaw_support
    {Task : Type uTask} {Instruction : Type uInstruction} [DecidableEq Instruction]
    (model : CommonSubprogramModel Task Instruction) :
    model.programLaw.support = model.assemble '' model.codeLaw.support := by
  exact PMF.support_map model.assemble model.codeLaw

/-- Every task with positive probability retains a receipt naming a code whose
instructions all come from the shared database. -/
theorem CommonSubprogramModel.supported_task_has_database_code
    {Task : Type uTask} {Instruction : Type uInstruction} [DecidableEq Instruction]
    (model : CommonSubprogramModel Task Instruction)
    {task : Task} (supported : task ∈ model.programLaw.support) :
    ∃ code ∈ model.codeLaw.support,
      model.assemble code = task ∧ ∀ position, code position ∈ model.database := by
  rw [model.programLaw_support] at supported
  obtain ⟨code, codeSupported, rfl⟩ := supported
  exact ⟨code, codeSupported, rfl, model.code_supported code codeSupported⟩

/-! ### Evolutionary zeta mutations -/

/-- Ozkural's evolutionary process before choosing a particular zeta mutation
encoding.  `applyMutation = none` means the transformation is invalid. -/
structure EvolutionaryZetaModel (Program : Type uProgram)
    (Mutation : Type uMutation) where
  initial : Program
  mutationLaw : PMF Mutation
  applyMutation : Mutation → Program → Option Program

namespace EvolutionaryZetaModel

variable {Program : Type uProgram} {Mutation : Type uMutation}

/-- Equation (33): apply a valid mutation, otherwise retain the old program. -/
def evolve (model : EvolutionaryZetaModel Program Mutation)
    (mutation : Mutation) (program : Program) : Program :=
  (model.applyMutation mutation program).getD program

theorem evolve_of_valid (model : EvolutionaryZetaModel Program Mutation)
    (mutation : Mutation) (program result : Program)
    (valid : model.applyMutation mutation program = some result) :
    model.evolve mutation program = result := by
  simp [evolve, valid]

theorem evolve_of_invalid (model : EvolutionaryZetaModel Program Mutation)
    (mutation : Mutation) (program : Program)
    (invalid : model.applyMutation mutation program = none) :
    model.evolve mutation program = program := by
  simp [evolve, invalid]

/-- The source's sequence law: emit the initial program first; subsequently
sample a mutation and apply the valid-or-retain update to the latest program. -/
noncomputable def toProcess (model : EvolutionaryZetaModel Program Mutation) :
    TaskProcess Program where
  next history := match history with
    | [] => PMF.pure model.initial
    | head :: tail =>
        model.mutationLaw.map
          (fun mutation ↦ model.evolve mutation (List.getLast (head :: tail) (by simp)))

@[simp]
theorem toProcess_next_nil (model : EvolutionaryZetaModel Program Mutation) :
    model.toProcess.next [] = PMF.pure model.initial := rfl

end EvolutionaryZetaModel

end Ozkural

/-! ## Positive and negative controls for the survival criterion -/

namespace SurvivalCanary

inductive Candidate where
  | handlesFalse
  | handlesTrue
deriving DecidableEq

def handles : Candidate → Bool → Prop
  | .handlesFalse, task => task = false
  | .handlesTrue, task => task = true

/-- Equal weakness records the fact that both candidates cover one atomic
outcome. -/
def weakness (_ : Candidate) : ℕ := 1

/-- A maximally biased process.  It is a concrete nonuniform-task negative
control, in the spirit of testing whether a distributional premise is doing
real work. -/
noncomputable def biasedProcess : TaskProcess Bool :=
  TaskProcess.iid (PMF.pure false)

theorem biased_false_success :
    biasedProcess.successProbability handles [] .handlesFalse = 1 := by
  simp [TaskProcess.successProbability, biasedProcess, handles]

theorem biased_true_success :
    biasedProcess.successProbability handles [] .handlesTrue = 0 := by
  simp [TaskProcess.successProbability, biasedProcess, handles]

/-- Negative control: equal coverage cardinality does not determine success
under a nonuniform law. -/
theorem biasedProcess_does_not_preserve_weakness :
    ¬ biasedProcess.PreservesWeaknessAt handles weakness [] := by
  intro preserves
  have wrong := (preserves .handlesFalse .handlesTrue).2 (by simp [weakness])
  rw [biased_false_success, biased_true_success] at wrong
  exact one_ne_zero (le_antisymm wrong zero_le)

/-- Positive theorem inherited from the exact uniform-subset model: its success
preorder agrees with coverage cardinality. -/
theorem uniformSubsetProblem_preserves_cardinality
    {CandidateType Outcome : Type*} [DecidableEq Outcome]
    (problem : GeneralizationOptimality.UniformSubsetProblem CandidateType Outcome)
    (left right : CandidateType) :
    problem.probability left ≤ problem.probability right ↔
      (problem.coverage left).card ≤ (problem.coverage right).card :=
  problem.probability_le_iff_card_coverage_le left right

/-! ### A nontrivial evolutionary witness -/

namespace Evolutionary

/-- A valid mutation flips a Boolean program; `false` is an invalid mutation.
The mutation law always proposes the valid flip. -/
noncomputable def toggleModel : Ozkural.EvolutionaryZetaModel Bool Bool where
  initial := false
  mutationLaw := PMF.pure true
  applyMutation mutation program :=
    if mutation then some (!program) else none

@[simp]
theorem toggle_evolve_true (program : Bool) :
    toggleModel.evolve true program = !program := by
  cases program <;> simp [toggleModel, Ozkural.EvolutionaryZetaModel.evolve]

/-- Positive control for evolutionary structure: unlike the two independent
models, the next law can genuinely depend on the previous program. -/
theorem toggleModel_is_history_sensitive :
    toggleModel.toProcess.next [false] ≠
      toggleModel.toProcess.next [true] := by
  intro lawsEqual
  have pointwise := congrArg (fun law : PMF Bool ↦ law false) lawsEqual
  simp [Ozkural.EvolutionaryZetaModel.toProcess, toggleModel,
    Ozkural.EvolutionaryZetaModel.evolve] at pointwise

end Evolutionary

end SurvivalCanary

#print axioms TaskProcess.preservesWeaknessAt_of_cardinalityFactorization
#print axioms Ozkural.independentZetaProcess_is_iid
#print axioms Ozkural.EvolutionaryZetaModel.evolve_of_invalid
#print axioms SurvivalCanary.biasedProcess_does_not_preserve_weakness
#print axioms Ozkural.CommonSubprogramModel.supported_task_has_database_code
#print axioms SurvivalCanary.Evolutionary.toggleModel_is_history_sensitive

end Mettapedia.Enactive.StochasticTaskProcess
