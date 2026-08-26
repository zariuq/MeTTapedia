import Mettapedia.CognitiveArchitecture.ProblemSolvingMethods

/-!
# Guided algorithmic memory

This file isolates the extra structure that turns retained executions into
cross-task search guidance.  The distinction is source-driven:

* Eray Ozkural, *Towards Heuristic Algorithmic Memory* (AGI 2011), updates a
  program-generating distribution from solved problems and reuses earlier
  solutions, idioms, and frequent subprograms;
* Eray Ozkural, *Omega: An Architecture for AI Unification* (2018), extends
  that programme to HAM 2.0 over multiple reference machines.

`MultiMachineMemory` already records retained executions and transfer
receipts.  `GuidedMemory` adds only a program guide.  A `GuideLearningUpdate`
must preserve every old receipt, retain a source experience, and genuinely
change the guide somewhere.  It deliberately does not assume that priorities
are probabilities: ranks, code lengths, costs, and calibrated probabilities
are different realizations of the same controller-facing interface.
-/

namespace Mettapedia.CognitiveArchitecture.GuidedAlgorithmicMemory

open Mettapedia.CognitiveArchitecture.ProblemSolvingMethods

universe uMachine uInput uOutput uProgram uRun uRetained uTransfer uPriority
  uRetained' uTransfer'

/-- A proof-relevant algorithmic memory together with a program-level search
guide.  The guide affects search order; it is not an execution receipt. -/
structure GuidedMemory
    {Machine : Type uMachine} {Input : Type uInput} {Output : Type uOutput}
    (family : ReferenceMachineFamily.{uInput, uOutput, uMachine, uProgram, uRun}
      Machine Input Output)
    (Priority : Type uPriority) extends
      MultiMachineMemory.{uInput, uOutput, uMachine, uRetained, uTransfer,
        uProgram, uRun} family where
  guide : ∀ machine, family.Program machine → Priority

/-- An evidence-preserving extension of the memory component.  It may add
receipts, but cannot identify two distinct old receipts. -/
structure MemoryExtension
    {Machine : Type uMachine} {Input : Type uInput} {Output : Type uOutput}
    {family : ReferenceMachineFamily.{uInput, uOutput, uMachine, uProgram, uRun}
      Machine Input Output}
    {Priority : Type uPriority}
    (before : GuidedMemory.{uMachine, uInput, uOutput, uProgram, uRun,
      uRetained, uTransfer, uPriority} family Priority)
    (after : GuidedMemory.{uMachine, uInput, uOutput, uProgram, uRun,
      uRetained', uTransfer', uPriority} family Priority) where
  retained : ∀ experience, before.Retained experience ↪ after.Retained experience
  transfer : ∀ experience target candidate,
    before.Transfer experience target candidate ↪
      after.Transfer experience target candidate

namespace MemoryExtension

/-- An unchanged guided memory preserves all receipts. -/
def refl
    {Machine : Type uMachine} {Input : Type uInput} {Output : Type uOutput}
    {family : ReferenceMachineFamily.{uInput, uOutput, uMachine, uProgram, uRun}
      Machine Input Output}
    {Priority : Type uPriority}
    (memory : GuidedMemory.{uMachine, uInput, uOutput, uProgram, uRun,
      uRetained, uTransfer, uPriority} family Priority) :
    MemoryExtension memory memory where
  retained _ := Function.Embedding.refl _
  transfer _ _ _ := Function.Embedding.refl _

end MemoryExtension

/-- A genuine cross-task guidance update.  Besides preserving the old memory,
it retains the experience that motivated the update and changes at least one
program priority.  This is the minimum proof-relevant interface shared by the
HAM-style updates; it does not claim that the changed guide is calibrated or
optimal. -/
structure GuideLearningUpdate
    {Machine : Type uMachine} {Input : Type uInput} {Output : Type uOutput}
    {family : ReferenceMachineFamily.{uInput, uOutput, uMachine, uProgram, uRun}
      Machine Input Output}
    {Priority : Type uPriority}
    (before : GuidedMemory.{uMachine, uInput, uOutput, uProgram, uRun,
      uRetained, uTransfer, uPriority} family Priority)
    (after : GuidedMemory.{uMachine, uInput, uOutput, uProgram, uRun,
      uRetained', uTransfer', uPriority} family Priority) where
  extension : MemoryExtension before after
  source : Experience family
  sourceRetained : Nonempty (after.Retained source)
  guideChanged : ∃ machine program,
    before.guide machine program ≠ after.guide machine program

/-- Merely re-presenting an unchanged guided memory is not a learning update:
retention alone does not imply that the search guide changed. -/
theorem no_learning_update_to_self
    {Machine : Type uMachine} {Input : Type uInput} {Output : Type uOutput}
    {family : ReferenceMachineFamily.{uInput, uOutput, uMachine, uProgram, uRun}
      Machine Input Output}
    {Priority : Type uPriority}
    (memory : GuidedMemory.{uMachine, uInput, uOutput, uProgram, uRun,
      uRetained, uTransfer, uPriority} family Priority) :
    IsEmpty (GuideLearningUpdate memory memory) :=
  ⟨fun update => by
    obtain ⟨machine, program, changed⟩ := update.guideChanged
    exact changed rfl⟩

/-! ## Positive and negative controls -/

inductive ToyProgram where
  | inherited
  | learned
  deriving DecidableEq

def toyFamily : ReferenceMachineFamily Unit Unit Bool where
  Program := fun _ => ToyProgram
  Run := fun _ _ _ _ => Unit

def toyExperience : Experience toyFamily where
  machine := ()
  program := .learned
  input := ()
  output := true
  run := ()

def beforeToyMemory : GuidedMemory toyFamily Nat where
  Retained := fun _ => Unit
  Transfer := fun _ _ _ => Unit
  guide := fun _ _ => 0

def afterToyMemory : GuidedMemory toyFamily Nat where
  Retained := fun _ => Unit
  Transfer := fun _ _ _ => Unit
  guide := fun _ program =>
    match program with
    | .inherited => 0
    | .learned => 1

/-- Positive control: the learned program changes priority while every old
receipt remains embedded and the motivating execution is retained. -/
def toyGuideLearningUpdate : GuideLearningUpdate beforeToyMemory afterToyMemory where
  extension := {
    retained := fun _ => Function.Embedding.refl Unit
    transfer := fun _ _ _ => Function.Embedding.refl Unit }
  source := toyExperience
  sourceRetained := ⟨()⟩
  guideChanged := ⟨(), .learned, by simp [beforeToyMemory, afterToyMemory]⟩

/-- The positive control is genuinely nonempty. -/
theorem toy_has_guideLearningUpdate :
    Nonempty (GuideLearningUpdate beforeToyMemory afterToyMemory) :=
  ⟨toyGuideLearningUpdate⟩

/-- Negative control: retained experience by itself is insufficient when the
program guide is unchanged. -/
theorem beforeToyMemory_has_retention_but_no_self_update :
    Nonempty (beforeToyMemory.Retained toyExperience) ∧
      IsEmpty (GuideLearningUpdate beforeToyMemory beforeToyMemory) := by
  exact ⟨⟨()⟩, no_learning_update_to_self beforeToyMemory⟩

#print axioms no_learning_update_to_self
#print axioms toy_has_guideLearningUpdate
#print axioms beforeToyMemory_has_retention_but_no_self_update

end Mettapedia.CognitiveArchitecture.GuidedAlgorithmicMemory
