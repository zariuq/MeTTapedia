import Mettapedia.GSLT.Dynamics.ContextualEffectInitiality
import Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolComparison
import Mettapedia.TypeTheory.DependentSequencingReadout

/-!
# Response-indexed protocols and free contextual choice

One finite response-indexed protocol can be organized in two different ways:

* externally, as a command whose response selects a successor-indexed result;
* internally, as a free contextual choice computation returning the selected
  response together with its dependent result.

For the two-response protocol, the dependent outcome types are equivalent and
the ordered list handler enumerates exactly the two authored protocol
outcomes.  The isolated-world and shared-state handlers agree on this pure
choice fragment, but they remain observably different on stateful programs.
Thus this bridge does not select a global state/choice handler.

Reversing the response enumeration changes the ordered answer list while
leaving its occurrence bag unchanged.  Hiding the response index altogether
is impossible because the two result fibres are not equivalent.  Cost remains
an independent valuation of the retained protocol event.

These are comparison results, not a choice of CBPV syntax, algebraic-effect
syntax, handler policy, scheduler, or language calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ResponseIndexedEffectOrganizationComparison

open Mettapedia.Algebra
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ContextualEffectInitiality
open Mettapedia.GSLT.Dynamics.ContextualEffectInitiality.EffectAlgebra
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.VaryingCanary
open Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolComparison
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality
open Mettapedia.TypeTheory.DependentSequencingReadout
open Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

/-! ## Exact dependent-outcome bridge -/

/-- A response-indexed value for the command's two Boolean replies. -/
abbrev ResponseResult := varyingBoolFamily

/-- A retained event occurrence paired with a result in its exact target
fibre. -/
abbrev ProtocolOutcome :=
  Sigma fun event : (interaction codedQuery).Enabled Phase.start =>
    Result event.target

/-- The two canonical outcomes of the coded protocol, disambiguated from the
corresponding uncoded outcomes. -/
abbrev codedUnitOutcome : ProtocolOutcome :=
  DependentReflectiveProtocolComparison.unitOutcome

abbrev codedBoolOutcome : ProtocolOutcome :=
  DependentReflectiveProtocolComparison.boolOutcome

/-- Map a Boolean-indexed dependent answer to its corresponding protocol
event occurrence. -/
def responseToProtocolOutcome : Sigma ResponseResult → ProtocolOutcome
  | ⟨false, result⟩ => ⟨unitEvent, result⟩
  | ⟨true, result⟩ => ⟨boolEvent, result⟩

/-- Recover the Boolean response and its correctly indexed result from a
protocol occurrence. -/
def protocolOutcomeToResponse : ProtocolOutcome → Sigma ResponseResult
  | ⟨event, result⟩ => by
      rcases event with ⟨site, target, evidence⟩
      cases site
      cases evidence with
      | fire code response =>
          cases code with
          | mk command =>
              cases command
              cases response with
              | false => exact ⟨false, result⟩
              | true => exact ⟨true, result⟩

/-- The external protocol occurrence and the internal response-indexed sigma
retain exactly the same dependent information. -/
def responseProtocolEquiv : Sigma ResponseResult ≃ ProtocolOutcome where
  toFun := responseToProtocolOutcome
  invFun := protocolOutcomeToResponse
  left_inv := by
    rintro ⟨response, result⟩
    cases response <;> rfl
  right_inv := by
    rintro ⟨event, result⟩
    rcases event with ⟨site, target, evidence⟩
    cases site
    cases evidence with
    | fire code response =>
        cases code with
        | mk command =>
            cases command
            cases response <;> rfl

@[simp] theorem responseProtocolEquiv_false :
    responseProtocolEquiv ⟨false, PUnit.unit⟩ = codedUnitOutcome :=
  rfl

@[simp] theorem responseProtocolEquiv_true :
    responseProtocolEquiv ⟨true, false⟩ = codedBoolOutcome :=
  rfl

/-! ## Answer-effect and contextual-program organizations -/

/-- Each response contributes the result selected by the authored complete
round. -/
def responseContinuation :
    (response : Bool) → List (ResponseResult response)
  | false => [PUnit.unit]
  | true => [false]

/-- Sigma-retaining sequencing under the ordered-list answer effect. -/
def responseIndexedAnswers : List (Sigma ResponseResult) :=
  bindSigma listEffect [false, true] responseContinuation

theorem responseIndexedAnswers_exact :
    responseIndexedAnswers =
      [⟨false, PUnit.unit⟩, ⟨true, false⟩] :=
  rfl

/-- Transport the dependent answer enumeration to retained protocol
occurrences. -/
def protocolListAnswers : List ProtocolOutcome :=
  listEffect.map responseProtocolEquiv responseIndexedAnswers

theorem protocolListAnswers_exact :
    protocolListAnswers = [codedUnitOutcome, codedBoolOutcome] :=
  rfl

/-- The same two dependent outcomes as a free contextual choice
computation. -/
def protocolChoiceProgram : Program Unit ProtocolOutcome Unit :=
  .choose (.pure codedUnitOutcome) (.pure codedBoolOutcome)

/-- Isolated-world evaluation retains both branches, their order, and their
branch occurrences. -/
theorem protocolChoiceProgram_isolated_exact :
    runWorlds protocolChoiceProgram () =
      [{ branch := [false], answer := codedUnitOutcome,
          state := (), intents := [] },
       { branch := [true], answer := codedBoolOutcome,
          state := (), intents := [] }] :=
  rfl

/-- The isolated handler's answer list is exactly the answer-effect
enumeration of the external protocol outcomes. -/
theorem isolated_answers_agree_protocol :
    (runWorlds protocolChoiceProgram ()).map WorldResult.answer =
      protocolListAnswers :=
  rfl

/-- The shared-state handler agrees on answers for this state-free fragment. -/
theorem shared_answers_agree_protocol :
    (runShared protocolChoiceProgram ()).answers = protocolListAnswers :=
  rfl

/-- Both operational policies are the unique constructor-preserving folds of
the same free effect syntax on this protocol computation. -/
theorem protocolChoiceProgram_has_both_initial_folds :
    fold
        (worldsAlgebra (State := Unit) (Answer := ProtocolOutcome)
          (Intent := Unit)) protocolChoiceProgram () [] =
        runWorlds protocolChoiceProgram () ∧
      fold
        (sharedAlgebra (State := Unit) (Answer := ProtocolOutcome)
          (Intent := Unit)) protocolChoiceProgram () =
        runShared protocolChoiceProgram () := by
  constructor
  · rw [fold_worlds_eq_runWorldsAt]
    rfl
  · rw [fold_shared_eq_runShared]

/-- Agreement on the pure choice corpus does not choose a global state
handler: the same two handlers remain distinct on the existing stateful
canary. -/
theorem pure_choice_agreement_does_not_select_state_handler :
    (runWorlds protocolChoiceProgram ()).map WorldResult.answer =
        (runShared protocolChoiceProgram ()).answers ∧
      (fold
          (worldsAlgebra (State := Nat) (Answer := Nat) (Intent := Unit))
          ContextualEffectHandlers.Canary.twoIncrements 0 []).map
          WorldResult.answer ≠
        (fold
          (sharedAlgebra (State := Nat) (Answer := Nat) (Intent := Unit))
          ContextualEffectHandlers.Canary.twoIncrements 0).answers :=
  ⟨rfl, EffectAlgebra.initial_folds_are_observably_distinct⟩

/-! ## Order, occurrence, index, and cost boundaries -/

/-- Reverse only the selected response enumeration. -/
def reversedProtocolChoiceProgram : Program Unit ProtocolOutcome Unit :=
  .choose (.pure codedBoolOutcome) (.pure codedUnitOutcome)

/-- The two programs retain different ordered observations. -/
theorem response_order_is_visible :
    (runWorlds protocolChoiceProgram ()).map
        (fun world => world.answer.1.target) ≠
      (runWorlds reversedProtocolChoiceProgram ()).map
        (fun world => world.answer.1.target) := by
  intro sameOrder
  change
    [Phase.unitDone, Phase.boolDone] =
      [Phase.boolDone, Phase.unitDone] at sameOrder
  injection sameOrder with firstEqual _secondEqual
  cases firstEqual

/-- Forgetting list order to an occurrence bag identifies the two response
enumerations.  Occurrence multiplicity is still retained. -/
theorem response_order_forgotten_by_bag :
    listToBag.map
        ((runWorlds protocolChoiceProgram ()).map WorldResult.answer) =
      listToBag.map
        ((runWorlds reversedProtocolChoiceProgram ()).map
          WorldResult.answer) := by
  change
    (Multiset.cons codedUnitOutcome 0) +
        (Multiset.cons codedBoolOutcome 0) =
      (Multiset.cons codedBoolOutcome 0) +
        (Multiset.cons codedUnitOutcome 0)
  exact add_comm _ _

/-- No exact common result carrier can hide the Boolean response index. -/
theorem response_index_cannot_be_hidden :
    ¬ Nonempty (UniformFibreRepresentation ResponseResult) :=
  varying_family_has_no_uniform_representation

/-- Work/span is evaluated from the retained protocol event after either
organization; it is not supplied by the answer effect itself. -/
theorem protocolChoiceProgram_costs :
    (runWorlds protocolChoiceProgram ()).map
        (fun world => workSpan world.answer.1) =
      [⟨1, 1⟩, ⟨3, 2⟩] :=
  rfl

/-! ## Combined effect-organization boundary -/

/-- The external protocol, sigma-retaining answer effect, and free contextual
choice program agree exactly on dependent outcomes.  They do not determine a
global state handler, an order-erasing observation, index hiding, or cost
policy. -/
theorem response_indexed_effect_organization_boundary :
    Nonempty (Sigma ResponseResult ≃ ProtocolOutcome) ∧
      responseIndexedAnswers =
        [⟨false, PUnit.unit⟩, ⟨true, false⟩] ∧
      protocolListAnswers = [codedUnitOutcome, codedBoolOutcome] ∧
      (runWorlds protocolChoiceProgram ()).map WorldResult.answer =
        protocolListAnswers ∧
      (runShared protocolChoiceProgram ()).answers =
        protocolListAnswers ∧
      (runWorlds protocolChoiceProgram ()).map WorldResult.answer =
        (runShared protocolChoiceProgram ()).answers ∧
      (runWorlds protocolChoiceProgram ()).map
          (fun world => world.answer.1.target) ≠
        (runWorlds reversedProtocolChoiceProgram ()).map
          (fun world => world.answer.1.target) ∧
      listToBag.map
          ((runWorlds protocolChoiceProgram ()).map WorldResult.answer) =
        listToBag.map
          ((runWorlds reversedProtocolChoiceProgram ()).map
            WorldResult.answer) ∧
      (¬ Nonempty (UniformFibreRepresentation ResponseResult)) ∧
      (runWorlds protocolChoiceProgram ()).map
          (fun world => workSpan world.answer.1) =
        [⟨1, 1⟩, ⟨3, 2⟩] :=
  ⟨⟨responseProtocolEquiv⟩,
    responseIndexedAnswers_exact,
    protocolListAnswers_exact,
    isolated_answers_agree_protocol,
    shared_answers_agree_protocol,
    rfl,
    response_order_is_visible,
    response_order_forgotten_by_bag,
    response_index_cannot_be_hidden,
    protocolChoiceProgram_costs⟩

#print axioms responseProtocolEquiv
#print axioms responseIndexedAnswers_exact
#print axioms protocolListAnswers_exact
#print axioms protocolChoiceProgram_isolated_exact
#print axioms protocolChoiceProgram_has_both_initial_folds
#print axioms pure_choice_agreement_does_not_select_state_handler
#print axioms response_order_is_visible
#print axioms response_order_forgotten_by_bag
#print axioms response_index_cannot_be_hidden
#print axioms protocolChoiceProgram_costs
#print axioms response_indexed_effect_organization_boundary

end Mettapedia.GSLT.Dynamics.ResponseIndexedEffectOrganizationComparison
