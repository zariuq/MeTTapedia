import Mettapedia.Algebra.WorkSpan
import Mettapedia.GSLT.Core.InteractionEvent
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mettapedia.GSLT.Dynamics.ObservationDiscipline
import Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

/-!
# Dependent choice over proof-relevant interactions

An enabled interaction may determine the type of its continuation result.
The conservative result of sequencing such a choice is therefore a sigma:
the selected event remains beside the value in its event-indexed fibre.

This module connects four independently defined structures:

* proof-relevant interaction events authorize operational steps;
* sigma-retaining bind sequences event-dependent continuations;
* answer-effect morphisms expose ordered, bag, or support observations;
* work/span values are receipts on retained occurrences, not endpoint meaning.

Endpoint erasure is explicit.  It preserves the dependent result and the
authorized target, but forgets the interaction site and occurrence evidence.
An exact factorization theorem states when a parallel work/span receipt can be
recovered from the ordered endpoint history.  Equal-endpoint events with
different costs provide the separating counterexample, and support erasure is
shown to lose at least the same distinction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.DependentInteractionChoice

open Mettapedia.Algebra
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Core.InteractionEvent.InteractionPresentation
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.Dynamics.AnswerEffects.AnswerEffect
open Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

universe uTerm uSite uEvent

variable {theory : GSLT.{uTerm}}
  {presentation : InteractionPresentation.{uSite, uEvent} theory}
  {source : theory.Term}

/-! ## Dependent outcomes -/

/-- A continuation result retains the exact enabled event on which its fibre
depends. -/
abbrev Outcome
    (presentation : InteractionPresentation.{uSite, uEvent} theory)
    (source : theory.Term)
    (Result : theory.Term → Type (max uTerm (max uSite uEvent))) :=
  Σ event : presentation.Enabled source, Result event.target

/-- Sequence an answer collection of enabled events with an event-dependent
continuation.  The selected event is retained in the result sigma. -/
def chooseDependent
    (effect : AnswerEffect.{max uTerm (max uSite uEvent)})
    (Result : theory.Term → Type (max uTerm (max uSite uEvent)))
    (events : effect.Carrier (presentation.Enabled source))
    (next : (event : presentation.Enabled source) →
      effect.Carrier (Result event.target)) :
    effect.Carrier (Outcome presentation source Result) :=
  bindSigma effect events next

/-- Every operation-preserving answer-effect map commutes with dependent
interaction choice.  Order and multiplicity loss therefore remain explicit
in the selected downstream morphism. -/
theorem morphism_map_chooseDependent
    {first second : AnswerEffect.{max uTerm (max uSite uEvent)}}
    (morphism : AnswerEffect.Morphism first second)
    (Result : theory.Term → Type (max uTerm (max uSite uEvent)))
    (events : first.Carrier (presentation.Enabled source))
    (next : (event : presentation.Enabled source) →
      first.Carrier (Result event.target)) :
    morphism.map (chooseDependent first Result events next) =
      chooseDependent second Result (morphism.map events)
        (fun event => morphism.map (next event)) :=
  morphism_map_bindSigma morphism events next

/-- Forget interaction identity while retaining the endpoint and its
dependent result. -/
def eraseOccurrence
    {Result : theory.Term → Type (max uTerm (max uSite uEvent))} :
    Outcome presentation source Result → Sigma Result
  | ⟨event, result⟩ => ⟨event.target, result⟩

/-- The retained event in every dependent outcome authorizes its endpoint. -/
theorem outcome_step
    {Result : theory.Term → Type (max uTerm (max uSite uEvent))}
    (outcome : Outcome presentation source Result) :
    theory.Step source outcome.1.target :=
  outcome.1.step

/-- Erase every occurrence in an ordered outcome history. -/
def orderedErasure
    {Result : theory.Term → Type (max uTerm (max uSite uEvent))}
    (outcomes : List (Outcome presentation source Result)) :
    List (Sigma Result) :=
  outcomes.map eraseOccurrence

/-! ## Independent work/span receipts -/

/-- Combine already-certified independent occurrence costs.  This operation
does not certify independence; it values a history whose independence was
established by the operational semantics. -/
def parallelReceipt {Event : Type*} (eventCost : Event → WorkSpan) :
    List Event → WorkSpan
  | [] => 0
  | event :: events =>
      WorkSpan.parallel (eventCost event) (parallelReceipt eventCost events)

@[simp] theorem parallelReceipt_nil {Event : Type*}
    (eventCost : Event → WorkSpan) :
    parallelReceipt eventCost [] = 0 :=
  rfl

@[simp] theorem parallelReceipt_cons {Event : Type*}
    (eventCost : Event → WorkSpan) (event : Event) (events : List Event) :
    parallelReceipt eventCost (event :: events) =
      WorkSpan.parallel (eventCost event)
        (parallelReceipt eventCost events) :=
  rfl

/-- Parallel receipt collection is a list-concatenation homomorphism into the
commutative work/span parallel algebra. -/
theorem parallelReceipt_append {Event : Type*}
    (eventCost : Event → WorkSpan) (first second : List Event) :
    parallelReceipt eventCost (first ++ second) =
      WorkSpan.parallel (parallelReceipt eventCost first)
        (parallelReceipt eventCost second) := by
  induction first with
  | nil => simp
  | cons event events inductionHypothesis =>
      simp only [List.cons_append, parallelReceipt_cons,
        inductionHypothesis]
      exact (WorkSpan.parallel_assoc _ _ _).symm

/-- **Exact endpoint-recoverability criterion.**  Parallel work/span for every
ordered outcome history factors through ordered endpoint erasure exactly when
the one-occurrence cost already factors through endpoint erasure. -/
theorem parallelReceipt_factors_iff_eventCost_factors
    {Result : theory.Term → Type (max uTerm (max uSite uEvent))}
    (eventCost : Outcome presentation source Result → WorkSpan) :
    Factors (fun outcomes => orderedErasure outcomes)
        (parallelReceipt eventCost) ↔
      Factors (fun outcome => eraseOccurrence outcome) eventCost := by
  constructor
  · rintro ⟨recover, recovers⟩
    refine ⟨fun endpoint => recover [endpoint], fun outcome => ?_⟩
    have singleton := recovers [outcome]
    simpa [orderedErasure] using singleton
  · rintro ⟨endpointCost, recovers⟩
    refine ⟨parallelReceipt endpointCost, fun outcomes => ?_⟩
    induction outcomes with
    | nil => rfl
    | cons outcome outcomes inductionHypothesis =>
        simp only [orderedErasure, List.map_cons, parallelReceipt_cons]
        rw [recovers outcome]
        change parallelReceipt endpointCost (outcomes.map eraseOccurrence) =
          parallelReceipt eventCost outcomes at inductionHypothesis
        rw [inductionHypothesis]

/-! ## Equal-endpoint separating controls -/

namespace Canary

open Mettapedia.GSLT.Core.InteractionEvent.Canary

/-- The continuation fibre is deliberately constant here.  Thus the
counterexample comes solely from occurrence identity, not from incompatible
result types. -/
abbrev LoopResult (_target : loopTheory.Term) : Type := Unit

def cheapOutcome : Outcome loopPresentation () LoopResult :=
  ⟨cheapEvent, ()⟩

def dearOutcome : Outcome loopPresentation () LoopResult :=
  ⟨dearEvent, ()⟩

/-- Equal endpoint-dependent results can arise from distinct interaction
occurrences. -/
theorem distinct_occurrences_same_endpoint_result :
    cheapOutcome ≠ dearOutcome ∧
      eraseOccurrence cheapOutcome = eraseOccurrence dearOutcome := by
  constructor
  · intro equalOutcomes
    have equalSites := congrArg (fun outcome => outcome.1.site) equalOutcomes
    exact LoopSite.noConfusion equalSites
  · rfl

/-- A dependent list computation retains both equal-endpoint occurrences. -/
def retainedList : List (Outcome loopPresentation () LoopResult) :=
  chooseDependent listEffect LoopResult [cheapEvent, dearEvent]
    (fun _ => [()])

theorem retainedList_exact :
    retainedList = [cheapOutcome, dearOutcome] :=
  rfl

/-- The same dependent computation commutes with the order-forgetting
list-to-bag morphism. -/
theorem retainedList_to_bag_natural :
    listToBag.map retainedList =
      chooseDependent bagEffect LoopResult
        (listToBag.map ([cheapEvent, dearEvent] :
          List (loopPresentation.Enabled ())))
        (fun event => listToBag.map ([()] : List (LoopResult event.target))) := by
  exact morphism_map_chooseDependent listToBag LoopResult
    ([cheapEvent, dearEvent] : List (loopPresentation.Enabled ()))
    (fun _ => [()])

/-- The two occurrence sites have distinct work/span receipts. -/
def loopWorkSpan : InteractionPresentation.EventCost loopPresentation WorkSpan where
  cost := fun {site} {_source _target} _ =>
    match site with
    | .cheap => ⟨1, 1⟩
    | .dear => ⟨2, 2⟩

def outcomeWorkSpan
    (outcome : Outcome loopPresentation () LoopResult) : WorkSpan :=
  loopWorkSpan.cost outcome.1.evidence

/-- Endpoint erasure cannot reconstruct occurrence-sensitive work/span. -/
theorem outcomeWorkSpan_not_endpoint_determined :
    ¬ Factors
      (fun outcome : Outcome loopPresentation () LoopResult =>
        eraseOccurrence outcome)
      outcomeWorkSpan := by
  let fiber : NonTrivialFiber
      (fun outcome : Outcome loopPresentation () LoopResult =>
        eraseOccurrence outcome)
      outcomeWorkSpan :=
    { left := cheapOutcome
      right := dearOutcome
      sameShadow := rfl
      differentValue := by decide }
  exact fiber.not_factors

/-- Hence ordered endpoint histories cannot reconstruct the parallel receipt
either; this is the history-level consequence of the exact criterion. -/
theorem parallelReceipt_not_endpoint_determined :
    ¬ Factors
      (fun outcomes : List (Outcome loopPresentation () LoopResult) =>
        orderedErasure outcomes)
      (parallelReceipt outcomeWorkSpan) := by
  intro factors
  exact outcomeWorkSpan_not_endpoint_determined
    ((parallelReceipt_factors_iff_eventCost_factors outcomeWorkSpan).mp factors)

/-- Parallel valuation retains total work three and critical path two. -/
theorem retainedList_parallel_receipt :
    parallelReceipt outcomeWorkSpan retainedList = ⟨3, 2⟩ :=
  rfl

/-- Extensional endpoint support forgets both occurrence identity and
multiplicity. -/
noncomputable def endpointSupport
    (outcomes : List (Outcome loopPresentation () LoopResult)) :
    Finset Unit :=
  (outcomes.map fun _outcome => ()).toFinset

/-- The coarser support observer also cannot reconstruct work/span. -/
theorem parallelReceipt_not_support_determined :
    ¬ Factors endpointSupport (parallelReceipt outcomeWorkSpan) := by
  let fiber : NonTrivialFiber endpointSupport
      (parallelReceipt outcomeWorkSpan) :=
    { left := [cheapOutcome]
      right := [dearOutcome]
      sameShadow := by
        classical
        simp [endpointSupport]
      differentValue := by decide }
  exact fiber.not_factors

end Canary

/-! ## Axiom audit -/

#print axioms morphism_map_chooseDependent
#print axioms outcome_step
#print axioms parallelReceipt_append
#print axioms parallelReceipt_factors_iff_eventCost_factors
#print axioms Canary.distinct_occurrences_same_endpoint_result
#print axioms Canary.retainedList_to_bag_natural
#print axioms Canary.outcomeWorkSpan_not_endpoint_determined
#print axioms Canary.parallelReceipt_not_endpoint_determined
#print axioms Canary.retainedList_parallel_receipt
#print axioms Canary.parallelReceipt_not_support_determined

end Mettapedia.GSLT.Dynamics.DependentInteractionChoice
