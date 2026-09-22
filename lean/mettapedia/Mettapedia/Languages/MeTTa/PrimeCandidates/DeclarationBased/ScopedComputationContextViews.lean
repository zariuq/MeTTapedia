import Mettapedia.GSLT.Core.PolicyFamilyContextClosure
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationObservation

/-!
# Contextual views for the native dependent-resumption protocol

The declared protocol observes producer answers, permits the existing native
reflexivity body once, and then observes dependent pair answers and newly
emitted intents. States are actual world lists. The resumed stage additionally
records each producer's intent-prefix length; erasing this annotation recovers
the existing `sequenceSigma` semantics exactly.

A producer needs its ordered answer/state-bit list. A terminal resumed state
needs its ordered answer/new-intent list. These finite-list readouts realize
every permitted contextual consumer and identify exactly its indistinguishable
states. Leastness is informational and relative to these consumers and this
single typed operation, not a bound on list length, a finite type of terms, a
global observer, or a runtime-cost optimum.

Branch histories and old intents are not public consumers here. The resumed
stage is terminal: no arbitrary further continuation or evaluation strategy
is selected. Native source and result admission remain separate judgments.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedComputation.ContextViews

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open NativeExamples

universe uReadout

inductive Scope where
  | producer
  | resumed

inductive Operation : Scope → Scope → Type where
  | resume : Operation .producer .resumed

instance : Quiver Scope where
  Hom := Operation

/-- The annotation is the old intent-prefix length, not an alternate world. -/
abbrev State : Scope → Type
  | .producer => List (WorldResult Bool (Tower.Tm 2) Nat)
  | .resumed => List (Nat × WorldResult Bool (Tower.Tm 2) Nat)

/-- Resume the actual native body with the selected answer, state and branch.
The additional natural number only marks where its new intents begin. -/
def resume (worlds : State .producer) : State .resumed :=
  worlds.flatMap fun prior =>
    (Code.worlds primitiveWorlds (consSub prior.answer ids) body
      prior.state prior.branch).map fun later =>
        (prior.intents.length,
          { branch := later.branch, answer := .pair prior.answer later.answer,
            state := later.state, intents := prior.intents ++ later.intents })

/-- Removing observation metadata gives the existing complete source-world
semantics, including order, multiplicity, branches, states and old intents. -/
theorem resume_erases_to_sequenceSigma
    (producer : Code Tower.Head NativeExamples.Operation 2)
    (state : Bool) (branch : BranchTrace) :
    (resume (Code.worlds primitiveWorlds ids producer state branch)).map Prod.snd =
      Code.worlds primitiveWorlds ids (.sequenceSigma producer body) state branch := by
  simp only [resume, Code.worlds, List.map_flatMap, List.map_map, Function.comp_def]

theorem resume_erases_to_interpretation
    (producer : Code Tower.Head NativeExamples.Operation 2)
    (state : Bool) (branch : BranchTrace) :
    (resume (Code.worlds primitiveWorlds ids producer state branch)).map Prod.snd =
      runWorldsAt (Code.interpret handler ids (.sequenceSigma producer body)) state branch := by
  rw [Code.interpret_worlds handler primitiveWorlds handler_realizes]
  exact resume_erases_to_sequenceSigma producer state branch

theorem resume_interpreted_worlds
    (producer : Code Tower.Head NativeExamples.Operation 2)
    (state : Bool) (branch : BranchTrace) :
    (resume (runWorldsAt (Code.interpret handler ids producer) state branch)).map Prod.snd =
      runWorldsAt (Code.interpret handler ids (.sequenceSigma producer body)) state branch := by
  rw [Code.interpret_worlds handler primitiveWorlds handler_realizes]
  exact resume_erases_to_interpretation producer state branch

/-- This equation is computed from the independently authored native body. -/
theorem resume_worlds (worlds : State .producer) :
    resume worlds = worlds.map fun prior =>
      (prior.intents.length,
        { branch := prior.branch, answer := .pair prior.answer (.refl prior.answer),
          state := prior.state, intents := prior.intents ++ [if prior.state then 30 else 40] }) := by
  induction worlds with
  | nil => rfl
  | cons prior rest ih =>
      change _ :: resume rest = _ :: rest.map _
      simp only [ih, subst_consSub_var_zero]

def newIntents (entry : Nat × WorldResult Bool (Tower.Tm 2) Nat) : List Nat :=
  entry.2.intents.drop entry.1

def suffixes (worlds : State .resumed) : List (List Nat) := worlds.map newIntents

theorem resume_suffixes (worlds : State .producer) :
    suffixes (resume worlds) =
      worlds.map (fun prior => [if prior.state then 30 else 40]) := by
  simp [suffixes, resume_worlds, newIntents, List.map_map]

/-- The suffix observer agrees with the independently declared continuation
consumer, rather than reading all intents of the resumed execution. -/
theorem resume_suffixes_eq_continuationIntents (worlds : State .producer) :
    suffixes (resume worlds) = ObservationStudy.Native.continuationIntents worlds := by
  rw [resume_suffixes]
  induction worlds with
  | nil => rfl
  | cons prior rest ih =>
      change _ :: rest.map _ = _ :: ObservationStudy.Native.continuationIntents rest
      rw [ih]

def execute {a b : Scope} (operation : a ⟶ b) : State a → State b :=
  match operation with
  | .resume => resume

inductive Request : Scope → Type where
  | answers (scope : Scope) : Request scope
  | newIntents : Request .resumed

def Request.Result {scope : Scope} : Request scope → Type
  | .answers _ => List (Tower.Tm 2)
  | .newIntents => List (List Nat)

def answers : (scope : Scope) → State scope → List (Tower.Tm 2)
  | .producer, worlds => ObservationStudy.answerView worlds
  | .resumed, worlds => worlds.map (fun entry => entry.2.answer)

def base (scope : Scope) : PolicyFamily (State scope) where
  Policy := Request scope
  Result := Request.Result
  decide request := match request with
    | .answers target => answers target
    | .newIntents => suffixes

def observations (scope : Scope) : PolicyFamily (State scope) :=
  PolicyFamily.ContextClosure.family execute base scope

abbrev Readout : Scope → Type
  | .producer => List (Tower.Tm 2 × Bool)
  | .resumed => List (Tower.Tm 2 × List Nat)

def readout : (scope : Scope) → State scope → Readout scope
  | .producer, worlds => worlds.map (fun world => (world.answer, world.state))
  | .resumed, worlds => worlds.map (fun entry => (entry.2.answer, newIntents entry))

def resumeReadout (observed : Readout .producer) : Readout .resumed :=
  observed.map fun entry =>
    (.pair entry.1 (.refl entry.1), [if entry.2 then 30 else 40])

/-- The compact operation square is derived by executing the actual body. -/
theorem readout_resume (worlds : State .producer) :
    readout .resumed (resume worlds) = resumeReadout (readout .producer worlds) := by
  simp [readout, resume_worlds, resumeReadout, newIntents, List.map_map]

def baseRealization (scope : Scope) : (base scope).ReadoutRealization (readout scope) where
  run request := match scope, request with
    | .producer, .answers _ => List.map Prod.fst
    | .resumed, .answers _ => List.map Prod.fst
    | .resumed, .newIntents => List.map Prod.snd
  agrees := by
    intro request worlds
    cases scope <;> cases request <;>
      simp [readout, base, answers, suffixes, ObservationStudy.answerView,
        List.map_map, Function.comp_def] <;> rfl

/-- Closing the actual consumers under the actual operation derives
congruence; operation stability is not an assumed field of a view record. -/
theorem equivalent_of_readout {scope : Scope} {first second : State scope}
    (same : readout scope first = readout scope second) :
    (observations scope).PolicyEquivalent first second := by
  apply PolicyFamily.ContextClosure.greatest execute base
    (fun target left right => readout target left = readout target right) ?_ ?_ same
  · intro target left right equal request
    rw [← (baseRealization target).agrees request left,
      ← (baseRealization target).agrees request right, equal]
  · intro a b operation left right equal
    change Operation a b at operation
    cases operation
    change readout .resumed (resume left) = readout .resumed (resume right)
    rw [readout_resume, readout_resume, equal]

def intentBit (intents : List Nat) : Bool := intents == [30]

theorem intentBit_native (state : Bool) : intentBit [if state then 30 else 40] = state := by
  cases state <;> rfl

theorem producer_readout_coordinates (worlds : State .producer) :
    readout .producer worlds =
      (answers .producer worlds).zip ((suffixes (resume worlds)).map intentBit) := by
  rw [resume_suffixes]
  simp only [List.map_map, Function.comp_def, intentBit_native]
  exact (List.zip_map').symm

theorem resumed_readout_coordinates (worlds : State .resumed) :
    readout .resumed worlds = (answers .resumed worlds).zip (suffixes worlds) :=
  (List.zip_map').symm

theorem readout_of_equivalent {scope : Scope} {first second : State scope}
    (same : (observations scope).PolicyEquivalent first second) :
    readout scope first = readout scope second := by
  cases scope with
  | producer =>
      have sameAnswers : answers .producer first = answers .producer second :=
        same ⟨.producer, .nil, .answers .producer⟩
      have sameIntents : suffixes (resume first) = suffixes (resume second) :=
        same ⟨.resumed, (show Scope.producer ⟶ Scope.resumed from Operation.resume).toPath,
          .newIntents⟩
      rw [producer_readout_coordinates, producer_readout_coordinates, sameAnswers, sameIntents]
  | resumed =>
      have sameAnswers : answers .resumed first = answers .resumed second :=
        same ⟨.resumed, .nil, .answers .resumed⟩
      have sameIntents : suffixes first = suffixes second :=
        same ⟨.resumed, .nil, .newIntents⟩
      rw [resumed_readout_coordinates, resumed_readout_coordinates, sameAnswers, sameIntents]

/-- Exact compatibility for all finite world lists at the declared stages. -/
theorem equivalent_iff_readout (scope : Scope) (first second : State scope) :
    (observations scope).PolicyEquivalent first second ↔
      readout scope first = readout scope second :=
  ⟨readout_of_equivalent, equivalent_of_readout⟩

/-- Representatives supply all readout values without choice. They need not
be admitted source outputs: this section is solely a semantic reconstruction
for the already specified policy family. -/
def representative : (scope : Scope) → Readout scope → State scope
  | .producer, observed => observed.map fun entry =>
      { branch := [], answer := entry.1, state := entry.2, intents := [] }
  | .resumed, observed => observed.map fun entry =>
      (0, { branch := [], answer := entry.1, state := false, intents := entry.2 })

theorem representative_section (scope : Scope) :
    Function.RightInverse (representative scope) (readout scope) := by
  intro observed
  cases scope <;> simp [representative, readout, newIntents, List.map_map, Function.comp_def]

/-- An actual runner for every typed operation path and requested consumer. -/
def realization (scope : Scope) :
    (observations scope).ReadoutRealization (readout scope) :=
  (observations scope).readoutRealizationOfSection (readout scope) (representative scope)
    (representative_section scope) (fun _ _ same => equivalent_of_readout same)

/-- Every other sufficient view reconstructs this joint readout. The decoder
uses the public current-answer and resumed-intent requests, not private access
to the original worlds and not a choice of unknown representatives. -/
theorem readout_is_least (scope : Scope) :
    (observations scope).SupportsReadout (readout scope) ∧
      ∀ (Other : Type uReadout) (other : State scope → Other),
        (observations scope).SupportsReadout other →
          NonFactorization.Factors other (readout scope) := by
  refine ⟨⟨realization scope⟩, ?_⟩
  rintro Other other ⟨runner⟩
  cases scope with
  | producer =>
      refine ⟨fun observed =>
        (runner.run ⟨.producer, .nil, .answers .producer⟩ observed).zip
          ((runner.run ⟨.resumed,
            (show Scope.producer ⟶ Scope.resumed from Operation.resume).toPath,
            .newIntents⟩ observed).map intentBit), ?_⟩
      intro worlds
      exact (congrArg₂ List.zip
        (runner.agrees ⟨.producer, .nil, .answers .producer⟩ worlds)
        (congrArg (List.map intentBit)
          (runner.agrees ⟨.resumed,
            (show Scope.producer ⟶ Scope.resumed from Operation.resume).toPath,
            .newIntents⟩ worlds))).trans (producer_readout_coordinates worlds).symm
  | resumed =>
      refine ⟨fun observed =>
        (runner.run ⟨.resumed, .nil, .answers .resumed⟩ observed).zip
          (runner.run ⟨.resumed, .nil, .newIntents⟩ observed), ?_⟩
      intro worlds
      exact (congrArg₂ List.zip
        (runner.agrees ⟨.resumed, .nil, .answers .resumed⟩ worlds)
        (runner.agrees ⟨.resumed, .nil, .newIntents⟩ worlds)).trans
          (resumed_readout_coordinates worlds).symm

def executeReadout {a b : Scope} (operation : a ⟶ b) : Readout a → Readout b :=
  match operation with
  | .resume => resumeReadout

theorem readout_execute {a b : Scope} (operation : a ⟶ b) (worlds : State a) :
    readout b (execute operation worlds) = executeReadout operation (readout a worlds) := by
  change Operation a b at operation
  cases operation
  exact readout_resume worlds

/-- The same square holds along every path in this explicitly typed graph. -/
theorem readout_runPath {a b : Scope} (path : Quiver.Path a b) (worlds : State a) :
    readout b (PolicyFamily.ContextClosure.runPath execute path worlds) =
      PolicyFamily.ContextClosure.runPath executeReadout path (readout a worlds) := by
  induction path with
  | nil => rfl
  | cons previous operation ih =>
      change readout _ (execute operation
        (PolicyFamily.ContextClosure.runPath execute previous worlds)) = _
      rw [readout_execute, ih]
      rfl

theorem readout_runPath_comp {a b c : Scope}
    (first : Quiver.Path a b) (second : Quiver.Path b c) (worlds : State a) :
    readout c (PolicyFamily.ContextClosure.runPath execute (first.comp second) worlds) =
      PolicyFamily.ContextClosure.runPath executeReadout second
        (PolicyFamily.ContextClosure.runPath executeReadout first (readout a worlds)) := by
  rw [readout_runPath, PolicyFamily.ContextClosure.runPath_comp]

/-- The generic closure supplies the actual precomposition-coordinate
witness. It therefore also induces an operation on observational classes. -/
def resumptionReindex :
    PolicyFamily.OperationReindex (observations .producer) (observations .resumed) resume :=
  PolicyFamily.ContextClosure.operationReindex execute base
    (show Scope.producer ⟶ Scope.resumed from Operation.resume)

theorem resumption_stable {first second : State .producer}
    (same : (observations .producer).PolicyEquivalent first second) :
    (observations .resumed).PolicyEquivalent (resume first) (resume second) :=
  resumptionReindex.preserves_policyEquivalent same

theorem resumption_class_square (worlds : State .producer) :
    resumptionReindex.classMap ((observations .producer).toObservationClass worlds) =
      (observations .resumed).toObservationClass (resume worlds) :=
  resumptionReindex.classMap_toObservationClass worlds

/-- Exact finite-list realization and informational leastness, coherent with
the actual handler execution. Every quantifier remains inside this protocol. -/
theorem contextual_readout_contract :
    (∀ scope, (observations scope).SupportsReadout (readout scope) ∧
      ∀ (Other : Type uReadout) (other : State scope → Other),
        (observations scope).SupportsReadout other →
          NonFactorization.Factors other (readout scope)) ∧
    (∀ scope (first second : State scope),
      (observations scope).PolicyEquivalent first second ↔
        readout scope first = readout scope second) ∧
    (∀ worlds, readout .resumed (resume worlds) = resumeReadout (readout .producer worlds)) ∧
    (∀ producer state branch,
      (resume (runWorldsAt (Code.interpret handler ids producer) state branch)).map Prod.snd =
        runWorldsAt (Code.interpret handler ids (.sequenceSigma producer body)) state branch) :=
  ⟨readout_is_least, equivalent_iff_readout, readout_resume, resume_interpreted_worlds⟩

namespace Native

open ObservationStudy.Native

/-- The positive workload includes both effectful alternatives and their
distinct native dependent answers, not only a one-world observation. -/
theorem choice_readout :
    readout .producer (Code.worlds primitiveWorlds ids first false []) =
      [(older, true), (newer, false)] ∧
    readout .resumed (resume (Code.worlds primitiveWorlds ids first false [])) =
      [(.pair older (.refl older), [30]), (.pair newer (.refl newer), [40])] := by
  constructor
  · rfl
  · rw [readout_resume]
    rfl

/-- Source admission is proved independently of the semantic observation
construction, in the same formed native context. -/
theorem choice_source_judgments :
    Judgment Tower.rules signature context first ground ∧
      Judgment Tower.rules signature context source (.sigma ground identityFamily) :=
  ⟨⟨context_formed, first_typing⟩, source_judgment⟩

theorem admitted_resumption_erasure :
    (resume trueWorlds).map Prod.snd = trueResumedWorlds ∧
      (resume falseWorlds).map Prod.snd = falseResumedWorlds :=
  ⟨resume_erases_to_sequenceSigma trueProducer false [],
    resume_erases_to_sequenceSigma falseProducer false []⟩

theorem admitted_resumption_results
    (entry : Nat × WorldResult Bool (Tower.Tm 2) Nat)
    (returned : entry ∈ resume trueWorlds ++ resume falseWorlds) :
    FormationSensitive.Judgment Tower.rules context entry.2.answer
      (.sigma ground identityFamily) := by
  apply resumptions_results_judgments entry.2
  have erased : entry.2 ∈ (resume trueWorlds ++ resume falseWorlds).map Prod.snd :=
    List.mem_map.mpr ⟨entry, returned, rfl⟩
  rw [List.map_append, admitted_resumption_erasure.1,
    admitted_resumption_erasure.2] at erased
  exact erased

/-- The two source-admitted producer states are separated by this readout
precisely where the answer-only view collides. -/
theorem answer_only_failure :
    ObservationStudy.answerView trueWorlds = ObservationStudy.answerView falseWorlds ∧
      readout .producer trueWorlds ≠ readout .producer falseWorlds ∧
      ¬ (observations .producer).SupportsReadout ObservationStudy.answerView := by
  refine ⟨producers_same_answers, by decide, ?_⟩
  apply (observations .producer).not_supportsReadout_of_policy_collision
    ObservationStudy.answerView producers_same_answers
    ⟨.resumed, (show Scope.producer ⟶ Scope.resumed from Operation.resume).toPath, .newIntents⟩
  change suffixes (resume trueWorlds) ≠ suffixes (resume falseWorlds)
  rw [resume_suffixes_eq_continuationIntents, resume_suffixes_eq_continuationIntents]
  exact resumed_intents_differ

/-- Executing the same admitted producer under another branch prefix changes
actual world data but not any observation allowed by this protocol. -/
def differentBranchWorlds : State .producer :=
  Code.worlds primitiveWorlds ids trueProducer false [true]

/-- A pure native return has no marking intent, while retaining the same
answer and selected state as the marked producer. -/
def unmarkedWorlds : State .producer :=
  Code.worlds primitiveWorlds ids (.returnValue older) true []

theorem unmarked_source_judgment :
    Judgment Tower.rules signature context (.returnValue older) ground :=
  ⟨context_formed, .returnValue (.var 1)⟩

theorem histories_can_be_forgotten :
    trueWorlds ≠ differentBranchWorlds ∧
      (observations .producer).PolicyEquivalent trueWorlds differentBranchWorlds ∧
    trueWorlds ≠ unmarkedWorlds ∧
      (observations .producer).PolicyEquivalent trueWorlds unmarkedWorlds := by
  refine ⟨?_, equivalent_of_readout rfl, ?_, equivalent_of_readout rfl⟩
  · intro same
    have different : trueWorlds.map WorldResult.branch ≠
        differentBranchWorlds.map WorldResult.branch := by decide
    exact different (congrArg (List.map WorldResult.branch) same)
  · intro same
    have different : trueWorlds.map WorldResult.intents ≠
        unmarkedWorlds.map WorldResult.intents := by decide
    exact different (congrArg (List.map WorldResult.intents) same)

/-- Adding branch histories as a public consumer invalidates this readout. -/
theorem branches_require_more_information :
    ¬ NonFactorization.Factors (readout .producer)
      (fun worlds : State .producer => worlds.map WorldResult.branch) := by
  intro factors
  have impossible := factors.constantOnFibers trueWorlds differentBranchWorlds rfl
  have different : trueWorlds.map WorldResult.branch ≠
      differentBranchWorlds.map WorldResult.branch := by decide
  exact different impossible

/-- Observing all intents, instead of just the resumed suffix, is a genuinely
different contract even on independently admitted native source programs. -/
theorem old_intents_require_more_information :
    ¬ NonFactorization.Factors (readout .producer)
      (fun worlds : State .producer => worlds.map WorldResult.intents) := by
  intro factors
  have impossible := factors.constantOnFibers trueWorlds unmarkedWorlds rfl
  have different : trueWorlds.map WorldResult.intents ≠
      unmarkedWorlds.map WorldResult.intents := by decide
  exact different impossible

/-- The operation-sensitive distinction occurs between independently admitted
programs and admitted native results, not only arbitrary semantic list entries. -/
theorem admitted_contextual_protocol :
    (Judgment Tower.rules signature context trueProducer ground ∧
      Judgment Tower.rules signature context falseProducer ground) ∧
    (Judgment Tower.rules signature context trueResumption (.sigma ground identityFamily) ∧
      Judgment Tower.rules signature context falseResumption (.sigma ground identityFamily)) ∧
    (∀ output ∈ trueWorlds ++ falseWorlds,
      FormationSensitive.Judgment Tower.rules context output.answer ground) ∧
    (∀ entry ∈ resume trueWorlds ++ resume falseWorlds,
      FormationSensitive.Judgment Tower.rules context entry.2.answer
        (.sigma ground identityFamily)) ∧
    ((resume trueWorlds).map Prod.snd = trueResumedWorlds ∧
      (resume falseWorlds).map Prod.snd = falseResumedWorlds) ∧
    (observations .producer).SupportsReadout (readout .producer) ∧
    (observations .resumed).SupportsReadout (readout .resumed) ∧
    ObservationStudy.answerView trueWorlds = ObservationStudy.answerView falseWorlds ∧
    readout .producer trueWorlds ≠ readout .producer falseWorlds ∧
    ¬ (observations .producer).SupportsReadout ObservationStudy.answerView :=
  ⟨producers_judgments, resumptions_judgments, producers_results_judgments,
    admitted_resumption_results, admitted_resumption_erasure,
    ⟨realization .producer⟩, ⟨realization .resumed⟩,
    answer_only_failure⟩

end Native

#print axioms resume_erases_to_sequenceSigma
#print axioms resume_erases_to_interpretation
#print axioms resume_interpreted_worlds
#print axioms resume_worlds
#print axioms resume_suffixes_eq_continuationIntents
#print axioms readout_resume
#print axioms baseRealization
#print axioms equivalent_iff_readout
#print axioms representative_section
#print axioms realization
#print axioms readout_is_least
#print axioms readout_runPath
#print axioms readout_runPath_comp
#print axioms resumptionReindex
#print axioms resumption_stable
#print axioms resumption_class_square
#print axioms contextual_readout_contract
#print axioms Native.choice_readout
#print axioms Native.choice_source_judgments
#print axioms Native.admitted_resumption_erasure
#print axioms Native.admitted_resumption_results
#print axioms Native.answer_only_failure
#print axioms Native.unmarked_source_judgment
#print axioms Native.histories_can_be_forgotten
#print axioms Native.branches_require_more_information
#print axioms Native.old_intents_require_more_information
#print axioms Native.admitted_contextual_protocol

end ScopedComputation.ContextViews
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
