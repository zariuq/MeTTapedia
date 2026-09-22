import Mettapedia.GSLT.Core.PolicyFamilySufficiency
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationSpecification

/-!
# Admission and continuation consumers of scoped execution views

The native admission policy observes result terms in their actual formed
context and expected dependent type. Its full family factors through the
ordered answer list, forgetting private state, branch histories and intents.
This is a semantic family of propositions, not an executable type checker.

The same answer view cannot determine a following stateful operation's
intents. Actual independently typed native calls supply the collision. A
bounded prefix is a different contract again: every observed answer is real,
but an absent answer need not be absent from the whole execution.

These are separate consumers and views of the same scoped computations, not
one globally sufficient observer or a choice of final evaluation strategy.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedComputation
namespace ObservationStudy

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

universe uState uIntent

variable {Head Operation : Type} {State : Type uState} {Intent : Type uIntent}
  {n m : Nat}

def answerView (worlds : List (WorldResult State (Tm Head m) Intent)) : List (Tm Head m) :=
  worlds.map WorldResult.answer

/-- The semantic request retains both the native context and expected type.
It does not infer either from an untyped output or from an erased receipt. -/
def admissionFamily (rules : Rules Head) :
    PolicyFamily (List (WorldResult State (Tm Head m) Intent)) where
  Policy := Ctx Head m × Tm Head m
  Result _ := Prop
  decide request worlds := ∀ output ∈ worlds,
    FormationSensitive.Judgment rules request.1 output.answer request.2

/-- All context/type admission policies use the same answer-list projection.
The result is a proposition, not a decision procedure for that proposition. -/
def answerAdmission (rules : Rules Head) :
    (admissionFamily (State := State) (Intent := Intent) (m := m) rules).ReadoutRealization
      answerView where
  run request answers := ∀ answer ∈ answers,
    FormationSensitive.Judgment rules request.1 answer request.2
  agrees := by
    intro request worlds
    apply propext
    constructor
    · intro admitted output member
      exact admitted output.answer (List.mem_map.mpr ⟨output, member, rfl⟩)
    · intro admitted answer member
      obtain ⟨output, outputMember, rfl⟩ := List.mem_map.mp member
      exact admitted output outputMember

/-- Native admission for the actual shared implementation remains available
through this view after arbitrary refined source substitution. -/
theorem qualified_answer_admission
    {rules : Rules Head} {signature : OperationSignature Head Operation}
    (implementation : ImplementationStudy.Implementation Head Operation State Intent m)
    (qualified : (ImplementationStudy.specification rules signature).Satisfies implementation)
    {sourceContext : Ctx Head n} {targetContext : Ctx Head m}
    {code : Code Head Operation n} {resultType : Tm Head n}
    (judgment : Judgment rules signature sourceContext code resultType)
    {environment : Sub Head n m}
    (target : FormationSensitive.ContextFormation rules targetContext)
    (typed : FormationSensitive.CtxMor rules sourceContext targetContext environment)
    (state : State) (branch : BranchTrace) :
    (answerAdmission (State := State) (Intent := Intent) rules).run
      (targetContext, subst environment resultType)
      (answerView
        (runWorldsAt (Code.interpret implementation.handler environment code) state branch)) := by
  apply Eq.mpr ((answerAdmission (State := State) (Intent := Intent) (m := m) rules).agrees
    (targetContext, subst environment resultType)
    (runWorldsAt (Code.interpret implementation.handler environment code) state branch))
  intro output returned
  exact ImplementationStudy.qualified_interpretation implementation qualified judgment
    target typed returned

/-- A prefix is a sound sample, not an exact replacement for all answers. -/
theorem prefix_answer_is_real (worlds : List (WorldResult State (Tm Head m) Intent))
    (bound : Nat) {answer : Tm Head m}
    (observed : answer ∈ answerView (worlds.take bound)) :
    answer ∈ answerView worlds := by
  obtain ⟨output, member, rfl⟩ := List.mem_map.mp observed
  exact List.mem_map.mpr ⟨output, List.mem_of_mem_take member, rfl⟩

/-- Completeness requires actual coverage of the finite world list. -/
theorem prefix_exact_of_coverage (worlds : List (WorldResult State (Tm Head m) Intent))
    (bound : Nat) (coverage : worlds.length ≤ bound) :
    answerView (worlds.take bound) = answerView worlds := by
  rw [List.take_of_length_le coverage]

/-- Soundness of observed native results is retained at every budget; an
empty prefix supplies no existence or exhaustive-negative conclusion. -/
theorem prefix_admission (rules : Rules Head)
    (request : Ctx Head m × Tm Head m)
    (worlds : List (WorldResult State (Tm Head m) Intent)) (bound : Nat)
    (admitted : (answerAdmission (State := State) (Intent := Intent) rules).run
      request (answerView worlds)) :
    (answerAdmission (State := State) (Intent := Intent) rules).run
      request (answerView (worlds.take bound)) := by
  intro answer observed
  exact admitted answer (prefix_answer_is_real worlds bound observed)

namespace Native

open NativeExamples

def trueProducer : Code Tower.Head NativeExamples.Operation 2 := .call .markTrue older

def falseProducer : Code Tower.Head NativeExamples.Operation 2 := .call .markFalse older

theorem producers_typed :
    Typing Tower.rules signature context trueProducer ground ∧
      Typing Tower.rules signature context falseProducer ground :=
  ⟨.call (operation_formation .markTrue) (.var 1),
    .call (operation_formation .markFalse) (.var 1)⟩

/-- The source programs carry the full formed-context computation judgment.
Native `FormationSensitive.Judgment` is used for their returned terms below. -/
theorem producers_judgments :
    Judgment Tower.rules signature context trueProducer ground ∧
      Judgment Tower.rules signature context falseProducer ground :=
  ⟨⟨context_formed, producers_typed.1⟩, ⟨context_formed, producers_typed.2⟩⟩

/-- Each producer binds its actual answer in the existing dependent body. -/
def trueResumption : Code Tower.Head NativeExamples.Operation 2 :=
  .sequenceSigma trueProducer body

def falseResumption : Code Tower.Head NativeExamples.Operation 2 :=
  .sequenceSigma falseProducer body

theorem resumptions_judgments :
    Judgment Tower.rules signature context trueResumption (.sigma ground identityFamily) ∧
      Judgment Tower.rules signature context falseResumption (.sigma ground identityFamily) :=
  ⟨⟨context_formed,
      .sequenceSigma sigma_formed (.sort _) producers_typed.1 body_typing⟩,
    ⟨context_formed,
      .sequenceSigma sigma_formed (.sort _) producers_typed.2 body_typing⟩⟩

def trueWorlds := Code.worlds primitiveWorlds ids trueProducer false []
def falseWorlds := Code.worlds primitiveWorlds ids falseProducer false []

def trueResumedWorlds := Code.worlds primitiveWorlds ids trueResumption false []
def falseResumedWorlds := Code.worlds primitiveWorlds ids falseResumption false []

private theorem admitted_world_result
    {code : Code Tower.Head NativeExamples.Operation 2} {resultType : Tower.Tm 2}
    (judgment : Judgment Tower.rules signature context code resultType)
    {output : WorldResult Bool (Tower.Tm 2) Nat}
    (returned : output ∈ Code.worlds primitiveWorlds ids code false []) :
    FormationSensitive.Judgment Tower.rules context output.answer resultType := by
  have typed : FormationSensitive.CtxMor Tower.rules context context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index)
  have interpreted :
      output ∈ runWorldsAt (Code.interpret handler ids code) false [] := by
    rw [Code.interpret_worlds handler primitiveWorlds handler_realizes]
    exact returned
  simpa only [subst_ids] using
    admitted_program_results judgment context_formed typed interpreted

/-- Every actual producer result has a full native formed-context judgment,
derived from the qualified handler rather than attached to the raw outputs. -/
theorem producers_results_judgments
    (output : WorldResult Bool (Tower.Tm 2) Nat)
    (returned : output ∈ trueWorlds ++ falseWorlds) :
    FormationSensitive.Judgment Tower.rules context output.answer ground := by
  rcases List.mem_append.mp returned with fromTrue | fromFalse
  · exact admitted_world_result producers_judgments.1 fromTrue
  · exact admitted_world_result producers_judgments.2 fromFalse

theorem resumptions_results_judgments
    (output : WorldResult Bool (Tower.Tm 2) Nat)
    (returned : output ∈ trueResumedWorlds ++ falseResumedWorlds) :
    FormationSensitive.Judgment Tower.rules context output.answer
      (.sigma ground identityFamily) := by
  rcases List.mem_append.mp returned with fromTrue | fromFalse
  · exact admitted_world_result resumptions_judgments.1 fromTrue
  · exact admitted_world_result resumptions_judgments.2 fromFalse

/-- Both admitted resumptions are interpreted by the actual handler, with
exact agreement on answer, state, branch and ordered intents. -/
theorem resumptions_interpretation :
    runWorldsAt (Code.interpret handler ids trueResumption) false [] = trueResumedWorlds ∧
      runWorldsAt (Code.interpret handler ids falseResumption) false [] = falseResumedWorlds :=
  ⟨Code.interpret_worlds handler primitiveWorlds handler_realizes ids trueResumption false [],
    Code.interpret_worlds handler primitiveWorlds handler_realizes ids falseResumption false []⟩

theorem producers_same_answers : answerView trueWorlds = answerView falseWorlds := rfl

/-- Resume the actual native reflexivity operation from each returned world.
Only the continuation's new intents are observed in this consumer. -/
def continuationIntents (worlds : List (WorldResult Bool (Tower.Tm 2) Nat)) :
    List (List Nat) :=
  worlds.flatMap fun prior =>
    (Code.worlds primitiveWorlds (consSub prior.answer ids) body
      prior.state prior.branch).map WorldResult.intents

theorem resumed_intents_differ : continuationIntents trueWorlds ≠
    continuationIntents falseWorlds := by decide

/-- Each concrete producer emits one marking intent. Removing exactly that
prefix from the full resumed execution exposes the existing continuation
consumer, without resetting the selected state or branch. -/
theorem resumed_continuation_intent_suffixes :
    (runWorldsAt (Code.interpret handler ids trueResumption) false []).map
        (fun output => output.intents.drop 1) = continuationIntents trueWorlds ∧
      (runWorldsAt (Code.interpret handler ids falseResumption) false []).map
        (fun output => output.intents.drop 1) = continuationIntents falseWorlds := by
  rw [resumptions_interpretation.1, resumptions_interpretation.2]
  exact ⟨rfl, rfl⟩

theorem resumed_handler_continuation_intents_differ :
    (runWorldsAt (Code.interpret handler ids trueResumption) false []).map
        (fun output => output.intents.drop 1) ≠
      (runWorldsAt (Code.interpret handler ids falseResumption) false []).map
        (fun output => output.intents.drop 1) := by
  rw [resumed_continuation_intent_suffixes.1, resumed_continuation_intent_suffixes.2]
  exact resumed_intents_differ

/-- A view sufficient for all native result-admission requests cannot
automatically be reused for this operation-sensitive consumer. -/
theorem answer_view_cannot_resume_intents :
    ¬ NonFactorization.Factors answerView continuationIntents :=
  NonFactorization.NonTrivialFiber.not_factors
    ⟨trueWorlds, falseWorlds, producers_same_answers, resumed_intents_differ⟩

/-- End-to-end negative control: all four programs are admitted in the same
formed context, their actual returned native values are admitted, and the
answer collision still cannot support the actual resumed intent consumer. -/
theorem admitted_continuation_collision :
    (Judgment Tower.rules signature context trueProducer ground ∧
      Judgment Tower.rules signature context falseProducer ground) ∧
    (Judgment Tower.rules signature context trueResumption (.sigma ground identityFamily) ∧
      Judgment Tower.rules signature context falseResumption (.sigma ground identityFamily)) ∧
    (∀ output ∈ trueWorlds ++ falseWorlds,
      FormationSensitive.Judgment Tower.rules context output.answer ground) ∧
    (∀ output ∈ trueResumedWorlds ++ falseResumedWorlds,
      FormationSensitive.Judgment Tower.rules context output.answer
        (.sigma ground identityFamily)) ∧
    answerView trueWorlds = answerView falseWorlds ∧
    ((runWorldsAt (Code.interpret handler ids trueResumption) false []).map
        (fun output => output.intents.drop 1) ≠
      (runWorldsAt (Code.interpret handler ids falseResumption) false []).map
        (fun output => output.intents.drop 1)) ∧
    ¬ NonFactorization.Factors answerView continuationIntents :=
  ⟨producers_judgments, resumptions_judgments,
    producers_results_judgments, resumptions_results_judgments,
    producers_same_answers, resumed_handler_continuation_intents_differ,
    answer_view_cannot_resume_intents⟩

/-- The second genuine dependent answer lies outside a one-world budget.
Its absence from that view is not logical or operational rejection. -/
theorem prefix_miss_is_not_absence :
    .pair newer (.refl newer) ∉
        answerView ((Code.worlds primitiveWorlds ids source false []).take 1) ∧
      .pair newer (.refl newer) ∈
        answerView (Code.worlds primitiveWorlds ids source false []) := by decide

end Native

#print axioms answerAdmission
#print axioms qualified_answer_admission
#print axioms prefix_answer_is_real
#print axioms prefix_exact_of_coverage
#print axioms prefix_admission
#print axioms Native.producers_typed
#print axioms Native.producers_judgments
#print axioms Native.resumptions_judgments
#print axioms Native.producers_results_judgments
#print axioms Native.resumptions_results_judgments
#print axioms Native.resumptions_interpretation
#print axioms Native.resumed_continuation_intent_suffixes
#print axioms Native.resumed_handler_continuation_intents_differ
#print axioms Native.admitted_continuation_collision
#print axioms Native.answer_view_cannot_resume_intents
#print axioms Native.prefix_miss_is_not_absence

end ObservationStudy
end ScopedComputation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
