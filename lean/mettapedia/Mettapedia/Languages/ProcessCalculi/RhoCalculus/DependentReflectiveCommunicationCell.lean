import Mathlib.Data.Fintype.Card
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.RevisionedTypedCommunicationDemand
import Mettapedia.TypeTheory.FibrewiseFullyFaithfulCwfMorphism
import Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

/-!
# A dependent reflective communication cell for rho

An exact typed rho communication retains its source, target, semantic
revision, and strict-COMM receipt.  This module uses that authentic index as
the base of a genuinely varying continuation family.  At revision `r`, the
continuation has one finite token for every revision up to `r`.

The resulting cell connects four existing faces without identifying them:

* every exact index supplies a typed COMM step and enters the established
  modulo-equations rho GSLT;
* its continuation is a type in the set-family CwF and is not in the
  constant-family simple fragment;
* ordered dependent sequencing retains the selected exact communication in a
  sigma, naturally through the order-forgetting list-to-bag morphism; and
* endpoint observation carries endpoint-indexed receipt families but cannot
  carry the revision-sensitive continuation or reconstruct its retained
  outcome.

The finite token family is a canary for revision-sensitive dependency, not a
claim that semantic history is finite.  No evaluation strategy, product
calculus, or runtime realization is selected here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.DependentReflectiveCommunicationCell

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.ProofRelevantRelationProtocol
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ProtocolModuloEquationsBridge
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.RevisionedTypedCommunicationDemand
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationProtocol
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

/-! ## The exact communication index and its operational face -/

/-- One exact index retains a revisioned claim and its typed COMM receipt. -/
abbrev ExactCommunication := TotalCommunicationEvidence

/-- Forget the semantic revision and typed receipt, retaining only the source
and target processes. -/
def exactEndpoints (communication : ExactCommunication) :
    CommunicationEndpoints :=
  endpointReadout.observe communication.1

/-- Every exact communication is a literal typed-protocol step. -/
def exactTypedStep (communication : ExactCommunication) :
    typedCommSystem.Step
      (exactEndpoints communication).1 (exactEndpoints communication).2 :=
  (lts_step_iff StrictCoreCommOccurrence).2 ⟨communication.2⟩

/-- Hence every exact communication enters both the quotient-aware protocol
and the established rho GSLT, while retaining the strongest proved native
typing judgment for its endpoints. -/
theorem exactCommunication_enters_saturated_rho
    (communication : ExactCommunication) :
    saturatedRhoProtocolSystem.Step
        (exactEndpoints communication).1 (exactEndpoints communication).2 /\
      rhoLanguageDefGSLT.Step
        (exactEndpoints communication).1 (exactEndpoints communication).2 /\
      HasType TypingContext.empty
        (exactEndpoints communication).1.1 processTruth /\
      HasTypeUpToSubjectEquiv TypingContext.empty
        (exactEndpoints communication).2.1 processTruth :=
  typed_step_enters_saturated_protocol (exactTypedStep communication)

/-! ## A genuinely varying continuation over exact communication -/

/-- At revision `r`, a continuation result can name any finite history token
up to and including `r`. -/
def revisionContinuation (communication : ExactCommunication) : Type :=
  Fin (communication.1.revision + 1)

/-- The continuation as a displayed type in the set-family CwF. -/
def continuationDisplay :
    TypeOver (familiesCwf.{0}) ExactCommunication :=
  ⟨revisionContinuation⟩

/-- The exact closed COMM receipt retained at revision zero. -/
noncomputable def zeroCommunication : ExactCommunication :=
  evidencedClosedClaim 0

/-- The same exact receipt retained at revision one. -/
noncomputable def oneCommunication : ExactCommunication :=
  evidencedClosedClaim 1

@[simp] theorem zeroCommunication_revision :
    zeroCommunication.1.revision = 0 :=
  rfl

@[simp] theorem oneCommunication_revision :
    oneCommunication.1.revision = 1 :=
  rfl

/-- The two exact communications have the same visible endpoints. -/
theorem zero_one_same_endpoints :
    exactEndpoints zeroCommunication = exactEndpoints oneCommunication :=
  rfl

/-- Their continuation fibres have different finite cardinalities. -/
theorem zero_one_continuations_not_equivalent :
    Not (Nonempty
      (revisionContinuation zeroCommunication ≃
        revisionContinuation oneCommunication)) := by
  rintro ⟨equivalence⟩
  have finiteEquivalence : Fin 1 ≃ Fin 2 := by
    simpa [revisionContinuation] using equivalence
  have equalCardinality := Fintype.card_congr finiteEquivalence
  simp at equalCardinality

/-- Endpoint observation cannot carry the revision-sensitive continuation
family: it identifies the two selected communications while their fibres are
not equivalent. -/
theorem revisionContinuation_does_not_factor_through_endpoints :
    Not (Nonempty
      (FamilyFactorization exactEndpoints revisionContinuation)) := by
  exact FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := zeroCommunication) (right := oneCommunication)
    zero_one_same_endpoints zero_one_continuations_not_equivalent

/-- In contrast, a family defined from the visible endpoint pair factors
through endpoint observation by construction. -/
def endpointReceiptFamily (communication : ExactCommunication) : Type :=
  StrictCoreCommOccurrence
    (exactEndpoints communication).1 (exactEndpoints communication).2

def endpointReceiptFamilyFactors :
    FamilyFactorization exactEndpoints endpointReceiptFamily :=
  FamilyFactorization.pullback exactEndpoints
    (fun endpoints => StrictCoreCommOccurrence endpoints.1 endpoints.2)

/-- The retained receipt inhabits the endpoint-indexed positive family. -/
def retainedReceipt (communication : ExactCommunication) :
    endpointReceiptFamily communication :=
  communication.2

/-! ## The constant-family control -/

/-- The revision-sensitive continuation is not merely a simple type spelled
as a dependent family.  Its revision-zero and revision-one fibres have
different cardinalities. -/
theorem continuationDisplay_not_in_simple_image :
    Not (Exists fun simpleType :
        TypeOver (SimpleFamiliesCwf.{0}) ExactCommunication =>
      simpleToDependentPseudoMorphism.mapTypeObject simpleType =
        continuationDisplay) := by
  rintro ⟨simpleType, imageEquality⟩
  have familyEquality :
      constantFamily simpleType.val = revisionContinuation :=
    congrArg TypeOver.val imageEquality
  have atZero : simpleType.val = revisionContinuation zeroCommunication :=
    congrFun familyEquality zeroCommunication
  have atOne : simpleType.val = revisionContinuation oneCommunication :=
    congrFun familyEquality oneCommunication
  have fibreEquality :
      revisionContinuation zeroCommunication =
        revisionContinuation oneCommunication :=
    atZero.symm.trans atOne
  exact zero_one_continuations_not_equivalent
    ⟨Equiv.cast fibreEquality⟩

/-! ## Sigma-retaining dependent sequencing -/

/-- Every selected communication has its initial history token. -/
def initialContinuationToken (communication : ExactCommunication) :
    revisionContinuation communication :=
  ⟨0, Nat.succ_pos communication.1.revision⟩

/-- One dependent continuation answer at every selected communication. -/
def continuationAnswers (communication : ExactCommunication) :
    List (revisionContinuation communication) :=
  [initialContinuationToken communication]

/-- Ordered choice between the same typed communication at two revisions. -/
noncomputable def selectedCommunications : List ExactCommunication :=
  [zeroCommunication, oneCommunication]

/-- Safe dependent sequencing retains each exact communication beside the
value in its selected continuation fibre. -/
noncomputable def sequencedContinuations :
    List (Sigma revisionContinuation) :=
  bindSigma listEffect selectedCommunications continuationAnswers

/-- Read the retained semantic revision from one dependent result. -/
def selectedRevision (outcome : Sigma revisionContinuation) : Nat :=
  outcome.1.1.revision

/-- The ordered effect preserves the chronology of the two selected
revisions. -/
theorem sequencedContinuation_revisions :
    sequencedContinuations.map selectedRevision = [0, 1] := by
  rfl

/-- The dependent sequence is natural through the canonical order-forgetting
map from answer lists to occurrence bags.  Naturality does not claim that the
map is faithful. -/
theorem sequencedContinuation_listToBag_natural :
    listToBag.map sequencedContinuations =
      bindSigma bagEffect (listToBag.map selectedCommunications)
        (fun communication => listToBag.map
          (continuationAnswers communication)) := by
  exact morphism_map_bindSigma listToBag selectedCommunications
    continuationAnswers

/-! ## Total-outcome non-collapse -/

/-- The canonical retained outcome at a selected revision. -/
noncomputable def closedOutcome (revision : Nat) :
    Sigma revisionContinuation :=
  ⟨evidencedClosedClaim revision,
    initialContinuationToken (evidencedClosedClaim revision)⟩

/-- Erase a dependent result to the visible communication endpoints. -/
def outcomeEndpoints (outcome : Sigma revisionContinuation) :
    CommunicationEndpoints :=
  exactEndpoints outcome.1

/-- The two retained outcomes are distinct because their exact communication
indices retain distinct revisions. -/
theorem zero_one_outcomes_distinct :
    closedOutcome 0 ≠ closedOutcome 1 := by
  intro equalOutcomes
  have equalClaims : closedClaim 0 = closedClaim 1 :=
    congrArg (fun outcome : Sigma revisionContinuation => outcome.1.1)
      equalOutcomes
  exact closedClaims_distinct (by decide) equalClaims

/-- Endpoint erasure identifies those distinct dependent outcomes. -/
theorem zero_one_outcomes_same_endpoints :
    outcomeEndpoints (closedOutcome 0) =
      outcomeEndpoints (closedOutcome 1) :=
  rfl

/-- Visible endpoints cannot reconstruct the retained dependent result. -/
theorem outcomeEndpoints_not_injective :
    Not (Function.Injective outcomeEndpoints) := by
  intro injective
  exact zero_one_outcomes_distinct
    (injective zero_one_outcomes_same_endpoints)

/-! ## Connected boundary -/

/-- One authentic rho cell now crosses the operational, dependent,
effectful, and observer-relative faces.  Endpoint-indexed receipts descend;
revision-sensitive continuations do not. -/
theorem dependent_reflective_communication_boundary :
    (forall communication : ExactCommunication,
      saturatedRhoProtocolSystem.Step
          (exactEndpoints communication).1
          (exactEndpoints communication).2 /\
        rhoLanguageDefGSLT.Step
          (exactEndpoints communication).1
          (exactEndpoints communication).2 /\
        HasType TypingContext.empty
          (exactEndpoints communication).1.1 processTruth /\
        HasTypeUpToSubjectEquiv TypingContext.empty
          (exactEndpoints communication).2.1 processTruth) /\
      Nonempty
        (FamilyFactorization exactEndpoints endpointReceiptFamily) /\
      Not (Nonempty
        (FamilyFactorization exactEndpoints revisionContinuation)) /\
      Not (Exists fun simpleType :
          TypeOver (SimpleFamiliesCwf.{0}) ExactCommunication =>
        simpleToDependentPseudoMorphism.mapTypeObject simpleType =
          continuationDisplay) /\
      sequencedContinuations.map selectedRevision = [0, 1] /\
      listToBag.map sequencedContinuations =
        bindSigma bagEffect (listToBag.map selectedCommunications)
          (fun communication => listToBag.map
            (continuationAnswers communication)) /\
      Not (Function.Injective outcomeEndpoints) :=
  ⟨exactCommunication_enters_saturated_rho,
    ⟨endpointReceiptFamilyFactors⟩,
    revisionContinuation_does_not_factor_through_endpoints,
    continuationDisplay_not_in_simple_image,
    sequencedContinuation_revisions,
    sequencedContinuation_listToBag_natural,
    outcomeEndpoints_not_injective⟩

/-! ## Axiom audit -/

#print axioms exactCommunication_enters_saturated_rho
#print axioms zero_one_continuations_not_equivalent
#print axioms revisionContinuation_does_not_factor_through_endpoints
#print axioms endpointReceiptFamilyFactors
#print axioms continuationDisplay_not_in_simple_image
#print axioms sequencedContinuation_revisions
#print axioms sequencedContinuation_listToBag_natural
#print axioms zero_one_outcomes_distinct
#print axioms outcomeEndpoints_not_injective
#print axioms dependent_reflective_communication_boundary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.DependentReflectiveCommunicationCell
