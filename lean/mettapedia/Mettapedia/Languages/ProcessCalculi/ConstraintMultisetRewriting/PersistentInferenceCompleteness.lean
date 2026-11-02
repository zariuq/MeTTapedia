import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceComposition

/-!
# Every source proof vector has an actual physical inference realization

Compilation follows the source proof's primitive rule nodes. Each node uses
the installed rule ID and original admission evidence, posts a request, reads
the compiled children at their exact physical positions, and publishes one
fresh theorem occurrence. Assumption nodes select the supplied positions.
The resulting observation is the original proof vector, with its input
position map substituted; this is stronger than concluding only derivability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaKernel (Value locatedAction)
open InferenceRequestExecution (Occurrence payload system)
open InferenceJudgmentBoards
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}

def singletonSelection {source context : List Pattern} (inputs : ContextMap source context)
    (index : Fin context.length) : ContextMap source [context.get index] where
  position _ := inputs.position index
  judgment port := by simpa using inputs.judgment index

theorem singletonSelection_interpret {source context : List Pattern}
    (inputs : ContextMap source context) (index : Fin context.length) :
    (singletonSelection inputs index).interpret definition =
      .cons ((inputs.interpret definition).get index) .nil := by
  rw [ContextMap.interpret_get]
  rfl

mutual

theorem realizes_derivation {context : List Pattern} {goal : Pattern}
    (proof : OpenDerivation definition context goal)
    (before : Configuration Value Occurrence) (background : locatedAction.Consistent before.equations)
    (prior : Board before) (inputs : ContextMap prior.judgments context) :
    ∃ execution : Execution (definition := definition) before prior [goal],
      execution.observe = .cons (proof.bind (inputs.interpret definition)) .nil := by
  cases proof with
  | assumption index =>
      refine ⟨identityExecution prior (singletonSelection inputs index), ?_⟩
      rw [identityExecution_observe, singletonSelection_interpret]
      rfl
  | byRule instance_ application children =>
      obtain ⟨prefixRun, prefixReplay⟩ := realizes_derivations children before background prior inputs
      obtain ⟨lastRun, _actors, lastReplay⟩ := application_realizes definition application
        prefixRun.after (prefixRun.ordinary.consistent background) prefixRun.board prefixRun.outputs
      refine ⟨prefixRun.follow lastRun, ?_⟩
      rw [Execution.follow_observe]
      change lastRun.observe.bind prefixRun.arrow = _
      rw [lastReplay]
      change OpenDerivationList.cons (.byRule instance_ application prefixRun.observe) .nil = _
      rw [prefixReplay]
      rfl
termination_by sizeOf proof

theorem realizes_derivations {context goals : List Pattern}
    (proofs : OpenDerivationList definition context goals)
    (before : Configuration Value Occurrence) (background : locatedAction.Consistent before.equations)
    (prior : Board before) (inputs : ContextMap prior.judgments context) :
    ∃ execution : Execution (definition := definition) before prior goals,
      execution.observe = proofs.bind (inputs.interpret definition) := by
  cases proofs with
  | nil =>
      let outputs : ContextMap prior.judgments [] :=
        ⟨Fin.elim0, fun index => Fin.elim0 index⟩
      refine ⟨identityExecution prior outputs, ?_⟩
      rw [identityExecution_observe]
      rfl
  | cons head tail =>
      obtain ⟨firstRun, firstReplay⟩ := realizes_derivation head before background prior inputs
      let nextInputs := firstRun.initialPositions.comp inputs
      obtain ⟨secondRun, secondReplay⟩ := realizes_derivations tail firstRun.after
        (firstRun.ordinary.consistent background) firstRun.board nextInputs
      have retainedInput : firstRun.arrow ≫ nextInputs.interpret definition = inputs.interpret definition := by
        rw [ContextMap.interpret_comp]
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun kept => kept ≫ inputs.interpret definition) firstRun.preserves_initial).trans
            (Category.id_comp _))
      have replayTail : firstRun.arrow ≫ secondRun.observe = tail.bind (inputs.interpret definition) := by
        rw [secondReplay]
        change firstRun.arrow ≫ (nextInputs.interpret definition ≫ tail) =
          inputs.interpret definition ≫ tail
        exact (Category.assoc _ _ _).symm.trans (congrArg (fun selected => selected ≫ tail) retainedInput)
      refine ⟨firstRun.join secondRun, ?_⟩
      rw [Execution.join_observe, firstReplay, replayTail]
      rfl
termination_by sizeOf proofs

end

theorem every_vector_is_observed {before : Configuration Value Occurrence}
    (background : locatedAction.Consistent before.equations) (prior : Board before)
    {goals : List Pattern} (proofs : OpenDerivationList definition prior.judgments goals) :
    ∃ execution : Execution (definition := definition) before prior goals,
      execution.observe = proofs := by
  obtain ⟨execution, observed⟩ := realizes_derivations proofs before background prior (ContextMap.id _)
  exact ⟨execution, observed.trans (OpenDerivationList.bind_assumptionEnvironment proofs)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference
