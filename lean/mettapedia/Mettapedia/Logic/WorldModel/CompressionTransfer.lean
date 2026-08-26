import Mettapedia.CognitiveArchitecture.GuidedAlgorithmicMemory
import Mettapedia.Logic.WorldModel.Algorithmic
import Mettapedia.UniversalAI.ZetaProgramPrior

/-!
# Incremental compression and cross-task algorithmic memory

Arthur Franz, Anton Antonenko, and Anton Soletskyi, *A Theory of Incremental
Compression* (Information Sciences 547, 2021), study within-object
decomposition into feature programs and residuals.  Arthur Franz,
*Grounded Reasoning: Implication as Algorithmic Containment* (AGI 2026), uses
the same feature/residual split to interpret implication.

Eray Ozkural, *Towards Heuristic Algorithmic Memory* (AGI 2011), instead
updates a cross-task program guide from solved problems and retains earlier
solutions, idioms, and frequent subprograms.  Ozkural's *Omega* (2018) extends
that memory to multiple reference machines.  His zeta rank law (2018) is a
separate proposal for a program prior, not by itself a memory update.

These are distinct mechanisms that can be compared by their formal roles:

* within-object compression decomposes one source;
* retention stores a proof-relevant execution for later reuse;
* guidance learning changes a search prior or ranking across tasks; and
* reference-machine plurality changes the program representation family.

The operations can reinforce one another, but none is silently identified
with another here.

This file states that distinction using the existing proof-relevant
problem-solving-method memory interface.  A positive bridge promotes an
executable compression feature to a retained program.  Negative controls
separate compression, retention, guide learning, and machine plurality.
-/

namespace Mettapedia.Logic.WorldModel.CompressionTransfer

open KolmogorovComplexity
open Mettapedia.CognitiveArchitecture.ProblemSolvingMethods
open Mettapedia.CognitiveArchitecture.GuidedAlgorithmicMemory

/-- There is a strict executable decomposition of this one source. -/
def HasWithinObjectCompression
    (U : ConditionalAlgorithm) (source : BinString) : Prop :=
  Nonempty (CompressionStep U source)

/-- A cross-task memory contains at least one retained execution. -/
def HasRetainedExperience
    {Machine Input Output : Type*}
    {family : ReferenceMachineFamily Machine Input Output}
    (memory : MultiMachineMemory family) : Prop :=
  ∃ experience : Experience family, Nonempty (memory.Retained experience)

/-- Treat a conditional algorithm as a one-machine family.  Programs are
retained with their exact input, output, and execution evidence. -/
def compressionReferenceMachineFamily (U : ConditionalAlgorithm) :
    ReferenceMachineFamily Unit BinString BinString where
  Program := fun _ => BinString
  Run := fun _ program input output => PLift (output ∈ U program input)

/-- A compression step supplies a genuine execution experience for its feature
program: reconstruction is the run receipt. -/
def compressionStepToExperience
    {U : ConditionalAlgorithm} {source : BinString}
    (step : CompressionStep U source) :
    Experience (compressionReferenceMachineFamily U) where
  machine := ()
  program := step.featureProgram
  input := step.residual
  output := source
  run := ⟨step.reconstructs⟩

/-- A proof-relevant memory that retains every supplied execution and transfers
only the very same program.  It does not manufacture evidence for unrelated
candidate programs. -/
def exactProgramMemory (U : ConditionalAlgorithm) :
    MultiMachineMemory (compressionReferenceMachineFamily U) where
  Retained := fun _ => Unit
  Transfer := fun experience _target candidate =>
    PLift (candidate = experience.program)

/-- A contrasting memory with no retained executions. -/
def noRetentionMemory (U : ConditionalAlgorithm) :
    MultiMachineMemory (compressionReferenceMachineFamily U) where
  Retained := fun _ => Empty
  Transfer := fun experience _target candidate =>
    PLift (candidate = experience.program)

/-- Promoting a compression feature into exact-program memory retains the
feature execution and licenses reuse of precisely that program. -/
theorem compressionStep_promotes_to_exactProgramMemory
    {U : ConditionalAlgorithm} {source : BinString}
    (step : CompressionStep U source) :
    Nonempty ((exactProgramMemory U).Retained
      (compressionStepToExperience step)) ∧
      Nonempty ((exactProgramMemory U).Transfer
        (compressionStepToExperience step) ()
        step.featureProgram) := by
  exact ⟨⟨()⟩, ⟨⟨rfl⟩⟩⟩

/-- The empty source cannot have a strict feature under any algorithm, because
the strict length inequality has no solution. -/
theorem emptySource_has_no_withinObjectCompression
    (U : ConditionalAlgorithm) :
    ¬ HasWithinObjectCompression U [] := by
  rintro ⟨step⟩
  have := step.compresses
  simp at this

theorem noRetentionMemory_has_no_retainedExperience
    (U : ConditionalAlgorithm) :
    ¬ HasRetainedExperience (noRetentionMemory U) := by
  rintro ⟨experience, retained⟩
  obtain ⟨receipt⟩ := retained
  exact receipt.elim

/-- Positive within-object compression does not by itself update a cross-task
memory. -/
theorem withinObjectCompression_does_not_imply_crossTaskRetention :
    HasWithinObjectCompression finiteCompressionAlgorithm fourTrue ∧
      ¬ HasRetainedExperience (noRetentionMemory finiteCompressionAlgorithm) := by
  exact ⟨⟨finiteCompressionStep⟩,
    noRetentionMemory_has_no_retainedExperience finiteCompressionAlgorithm⟩

/-- A concrete retained execution over the literal algorithm. -/
def emptyLiteralExperience :
    Experience (compressionReferenceMachineFamily literalResidualAlgorithm) where
  machine := ()
  program := []
  input := []
  output := []
  run := ⟨by simp [literalResidualAlgorithm]⟩

theorem exactLiteralMemory_has_retainedExperience :
    HasRetainedExperience (exactProgramMemory literalResidualAlgorithm) := by
  exact ⟨emptyLiteralExperience, ⟨()⟩⟩

/-- Retaining programs from one conditional algorithm does not manufacture a
multiple-reference-machine architecture.  Promotion and machine plurality are
separate operations. -/
theorem exactProgramMemory_not_usesMultipleMachines
    (U : ConditionalAlgorithm) :
    ¬ UsesMultipleMachines (exactProgramMemory U) := by
  rintro ⟨first, second, _retainsFirst, _retainsSecond, distinct⟩
  exact distinct (Subsingleton.elim first.machine second.machine)

/-- Cross-task retention may exist even when the chosen source admits no
within-object compression. -/
theorem crossTaskRetention_does_not_imply_withinObjectCompression :
    HasRetainedExperience (exactProgramMemory literalResidualAlgorithm) ∧
      ¬ HasWithinObjectCompression literalResidualAlgorithm [] := by
  exact ⟨exactLiteralMemory_has_retainedExperience,
    emptySource_has_no_withinObjectCompression literalResidualAlgorithm⟩

/-- The positive overlap case: the finite compression feature is retained and
transferred with the execution that reconstructs its source. -/
theorem finiteCompression_feature_is_promoted :
    Nonempty ((exactProgramMemory finiteCompressionAlgorithm).Retained
      (compressionStepToExperience finiteCompressionStep)) ∧
    Nonempty ((exactProgramMemory finiteCompressionAlgorithm).Transfer
      (compressionStepToExperience finiteCompressionStep) ()
      finiteCompressionStep.featureProgram) :=
  compressionStep_promotes_to_exactProgramMemory finiteCompressionStep

/-- The overlap is exact but modest: the feature becomes reusable cross-task
memory, while the one-machine promotion still lacks machine plurality. -/
theorem finiteCompression_promotion_is_not_multiMachine :
    HasWithinObjectCompression finiteCompressionAlgorithm fourTrue ∧
    HasRetainedExperience (exactProgramMemory finiteCompressionAlgorithm) ∧
    ¬ UsesMultipleMachines (exactProgramMemory finiteCompressionAlgorithm) := by
  refine ⟨⟨finiteCompressionStep⟩, ?_,
    exactProgramMemory_not_usesMultipleMachines finiteCompressionAlgorithm⟩
  exact ⟨compressionStepToExperience finiteCompressionStep, ⟨()⟩⟩

/-! ## Guidance learning is a third, independent operation -/

/-- Add an arbitrary program guide to exact-program memory.  The guide may be
a rank, cost, code length, or calibrated probability; retaining a run does not
by itself determine which interpretation is intended. -/
def exactGuidedProgramMemory
    (U : ConditionalAlgorithm) {Priority : Type*}
    (guide : BinString → Priority) :
    GuidedMemory (compressionReferenceMachineFamily U) Priority where
  toMultiMachineMemory := exactProgramMemory U
  guide := fun _ program => guide program

/-- Every compression step can be retained in a guided memory without changing
the supplied guide.  Promotion to memory is therefore weaker than HAM-style
learning. -/
theorem compressionStep_retained_under_staticGuide
    {U : ConditionalAlgorithm} {source : BinString} {Priority : Type*}
    (guide : BinString → Priority) (step : CompressionStep U source) :
    Nonempty ((exactGuidedProgramMemory U guide).Retained
      (compressionStepToExperience step)) := by
  exact ⟨()⟩

/-- Concrete separation: Franz-style strict compression exists, its execution
is retained, but an unchanged search guide is not an Ozkural-style learning
update. -/
theorem withinObjectCompression_and_retention_do_not_imply_guideLearning :
    HasWithinObjectCompression finiteCompressionAlgorithm fourTrue ∧
    Nonempty ((exactGuidedProgramMemory finiteCompressionAlgorithm
      (fun _ => (0 : Nat))).Retained
        (compressionStepToExperience finiteCompressionStep)) ∧
    IsEmpty (GuideLearningUpdate
      (exactGuidedProgramMemory finiteCompressionAlgorithm (fun _ => (0 : Nat)))
      (exactGuidedProgramMemory finiteCompressionAlgorithm (fun _ => (0 : Nat)))) := by
  exact ⟨⟨finiteCompressionStep⟩, ⟨()⟩,
    no_learning_update_to_self _⟩

/-- A baseline guide for the literal-machine counterexample. -/
def literalGuideBefore :
    GuidedMemory (compressionReferenceMachineFamily literalResidualAlgorithm)
      Nat :=
  exactGuidedProgramMemory literalResidualAlgorithm (fun _ => 0)

/-- A guide that promotes the empty program after retaining the empty-output
experience.  The execution memory is unchanged; only the controller-facing
priority changes. -/
def literalGuideAfter :
    GuidedMemory (compressionReferenceMachineFamily literalResidualAlgorithm)
      Nat :=
  exactGuidedProgramMemory literalResidualAlgorithm
    (fun program => if program = [] then 1 else 0)

/-- A genuine guide-learning update over a source that admits no strict
within-object compression. -/
def literalGuideLearningUpdate :
    GuideLearningUpdate literalGuideBefore literalGuideAfter where
  extension := {
    retained := fun _ => Function.Embedding.refl Unit
    transfer := fun _ _ _ => Function.Embedding.refl (PLift (_ = _)) }
  source := emptyLiteralExperience
  sourceRetained := ⟨()⟩
  guideChanged := ⟨(), [], by
    simp [literalGuideBefore, literalGuideAfter, exactGuidedProgramMemory]⟩

/-- Converse separation: a retained cross-task guide update may exist even
when its source output has no strict compressive feature. -/
theorem guideLearning_does_not_imply_withinObjectCompression :
    Nonempty (GuideLearningUpdate literalGuideBefore literalGuideAfter) ∧
      ¬ HasWithinObjectCompression literalResidualAlgorithm [] := by
  exact ⟨⟨literalGuideLearningUpdate⟩,
    emptySource_has_no_withinObjectCompression literalResidualAlgorithm⟩

/-- The guide update above still uses only one reference machine.  Learning a
program priority and HAM-2.0 machine plurality are separate claims. -/
theorem guideLearning_does_not_imply_multipleReferenceMachines :
    Nonempty (GuideLearningUpdate literalGuideBefore literalGuideAfter) ∧
      ¬ UsesMultipleMachines literalGuideAfter.toMultiMachineMemory := by
  exact ⟨⟨literalGuideLearningUpdate⟩,
    exactProgramMemory_not_usesMultipleMachines literalResidualAlgorithm⟩

/-! ## A static Ozkural zeta guide is not a learned update -/

/-- Instantiate the controller-facing guide with Ozkural's 2018 zeta score.
This reuses the separately normalized/source-audited prior layer and does not
identify a static prior with HAM's cross-task update rule. -/
noncomputable def zetaGuidedProgramMemory
    (U : ConditionalAlgorithm)
    (s : Mettapedia.UniversalAI.ZetaProgramPrior.Exponent) :
    GuidedMemory (compressionReferenceMachineFamily U) Real :=
  exactGuidedProgramMemory U
    (Mettapedia.UniversalAI.ZetaProgramPrior.arithmetizationScore s)

/-- The source-level binary arithmetization gives the same zeta score to
distinct leading-zero strings.  A zeta guide is useful ordering data, but not
a duplicate-free program code without an additional representation theorem. -/
theorem zetaGuide_has_leadingZero_collision
    (U : ConditionalAlgorithm)
    (s : Mettapedia.UniversalAI.ZetaProgramPrior.Exponent) :
    (zetaGuidedProgramMemory U s).guide () [false] =
      (zetaGuidedProgramMemory U s).guide () [false, false] := by
  simp [zetaGuidedProgramMemory, exactGuidedProgramMemory,
    Mettapedia.UniversalAI.ZetaProgramPrior.arithmetizationScore]

/-- A fixed zeta guide is not, merely by existing, a cross-task learning
event. -/
theorem staticZetaGuide_is_not_guideLearningUpdate
    (U : ConditionalAlgorithm)
    (s : Mettapedia.UniversalAI.ZetaProgramPrior.Exponent) :
    IsEmpty (GuideLearningUpdate
      (zetaGuidedProgramMemory U s) (zetaGuidedProgramMemory U s)) :=
  no_learning_update_to_self _

#print axioms compressionStep_promotes_to_exactProgramMemory
#print axioms withinObjectCompression_does_not_imply_crossTaskRetention
#print axioms crossTaskRetention_does_not_imply_withinObjectCompression
#print axioms finiteCompression_feature_is_promoted
#print axioms finiteCompression_promotion_is_not_multiMachine
#print axioms compressionStep_retained_under_staticGuide
#print axioms withinObjectCompression_and_retention_do_not_imply_guideLearning
#print axioms guideLearning_does_not_imply_withinObjectCompression
#print axioms guideLearning_does_not_imply_multipleReferenceMachines
#print axioms zetaGuide_has_leadingZero_collision
#print axioms staticZetaGuide_is_not_guideLearningUpdate

end Mettapedia.Logic.WorldModel.CompressionTransfer
