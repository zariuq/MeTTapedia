import Mettapedia.TypeTheory.Models.RevisionedFamilies.FamilyDescent
import Mettapedia.Logic.Bridges.WMNativeCapabilityComputation

/-!
# Supported WM answer receipts as observable dependent families

A state-dependent query capability descends to the observational quotient
because it respects behavioral agreement. At a fixed answer, its checked
receipt is a dependent family in the staged families semantic families CwF.
Pulling that family back to raw requests recovers exactly the proof-relevant
GSLT-IL capability receipt. Its inhabitance at a raw request also coincides
with the OSLF native supported answer graph. At authored WM terms, the
complete relational chain fibre is equivalent to the same observable
dependent fibre.

This comparison retains the checked answer and the support obligation. It
does not turn the partial relation into a total compiler, or retain an
operational derivation that the extensional receipt never stored.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL

open Mettapedia.TypeTheory.Models.RevisionedFamilies.FamilyDescent
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
open Mettapedia.Logic.Bridges.WMNativeCapabilityComputation
open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure

variable {State Query V : Type} {R : WMReading State Query V}

/-- Support is well-defined on observable state classes precisely because
the capability respects all the reading's state observations. -/
def observableSupport (capability : WMCapability R) :
    ObsState R → Query → Prop :=
  Quotient.lift (fun state => capability.supports state) (by
    intro first second agree
    funext query
    exact propext (capability.respectsAgree first second query agree))

theorem observableSupport_classOf (capability : WMCapability R)
    (state : State) (query : Query) :
    observableSupport capability (classOf R state) query ↔
      capability.supports state query := Iff.rfl

/-- Observable state-query requests are a context of the staged families
base-stage semantic families CwF. -/
def observableRequestContext (R : WMReading State Query V) :
    familiesCwF.Con (stageOfNat 0) := ObsState R × Query

/-- Raw requests enter that context through the quotient substitution. -/
def observationRequestSub (R : WMReading State Query V) :
    familiesCwF.Sub (State × Query) (observableRequestContext R) :=
  fun request => (classOf R request.1, request.2)

/-- An actual dependent receipt at an observable request and fixed answer.
Both support and equality with extracted evidence are retained as fields. -/
structure ObservableReceipt (capability : WMCapability R)
    (request : observableRequestContext R) (answer : V) : Type where
  supported : observableSupport capability request.1 request.2
  checked : extractObs R request.1 request.2 = answer

/-- The checked receipt family is a type over observable requests, not only
a predicate about them. -/
def observableReceiptFamily (capability : WMCapability R) (answer : V) :
    familiesCwF.Ty (observableRequestContext R) :=
  fun request => ObservableReceipt capability request answer

/-- Pulling the family back along the observational substitution recovers
the GSLT-IL relational receipt fibre, with both evidence checks preserved. -/
def rawReceiptEquiv (capability : WMCapability R)
    (request : State × Query) (answer : V) :
    CapabilityAnswerReceipt capability request answer ≃
      familiesCwF.tySub (observableReceiptFamily capability answer)
        (observationRequestSub R) request where
  toFun receipt := ⟨receipt.supported, receipt.checked⟩
  invFun receipt := ⟨receipt.supported, receipt.checked⟩
  left_inv := by
    intro receipt
    cases receipt
    rfl
  right_inv := by
    intro receipt
    cases receipt
    rfl

/-- The Prime semantic receipt fibre, GSLT-IL's retained answer receipt,
and OSLF's native supported graph agree on one raw request and answer.
The comparison uses actual graph membership, not merely a matching name. -/
theorem observableReceipt_iff_nativeSupportedGraph
    (capability : WMCapability R)
    (X : Opposite (ConstructorObj
      (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)))
    (state : State) (query : Query) (answer : V) :
    Nonempty (observableReceiptFamily capability answer
      (classOf R state, query)) ↔
      ((state, query), answer) ∈ (supportedGraph capability).obj X := by
  rw [← receipt_iff_supportedGraph capability X state query answer]
  constructor
  · rintro ⟨receipt⟩
    exact ⟨(rawReceiptEquiv capability (state, query) answer).symm receipt⟩
  · rintro ⟨receipt⟩
    exact ⟨(rawReceiptEquiv capability (state, query) answer) receipt⟩

/-- On authored typed WM requests, the complete proof-relevant GSLT-IL
chain fibre is precisely an observable dependent family fibre. The middle
semantic request is reconstructed, not replaced by an arbitrary witness. -/
def termChainReceiptEquiv (capability : WMCapability R)
    (terms : WMTerm .state × WMTerm .query) (answer : V) :
    (termCapabilityChain capability).evidence terms answer ≃
      observableReceiptFamily capability answer
        (classOf R (R.denote terms.1), R.denote terms.2) where
  toFun := by
    rintro ⟨request, pairReceipt, answerReceipt⟩
    cases pairReceipt.checked
    exact ⟨answerReceipt.supported, answerReceipt.checked⟩
  invFun := by
    intro receipt
    exact ⟨(R.denote terms.1, R.denote terms.2), ⟨rfl⟩,
      ⟨receipt.supported, receipt.checked⟩⟩
  left_inv := by
    intro witness
    exact (chainEvidence_subsingleton capability terms answer).allEq _ _
  right_inv := by
    intro receipt
    cases receipt
    rfl

/-- Computation on both authored request components transports the actual
observable CwF receipt fibre at the same answer. This follows by identifying
it with the already checked GSLT-IL receipt, transporting that receipt, and
identifying the target fibre again. -/
def observableReceiptEquivOfPairSteps (capability : WMCapability R)
    (laws : R.CoreLaws)
    {state₁ state₂ : WMTerm .state} {query₁ query₂ : WMTerm .query}
    (stateSteps : Mettapedia.OSLF.Framework.WMCalculusContextEncoding.WMContextStepStar
      state₁ state₂)
    (querySteps : Mettapedia.OSLF.Framework.WMCalculusContextEncoding.WMContextStepStar
      query₁ query₂)
    (answer : V) :
    observableReceiptFamily capability answer
        (classOf R (R.denote state₁), R.denote query₁) ≃
      observableReceiptFamily capability answer
        (classOf R (R.denote state₂), R.denote query₂) :=
  (termChainReceiptEquiv capability (state₁, query₁) answer).symm.trans
    ((chainEvidenceEquivOfPairSteps capability laws stateSteps querySteps answer).trans
      (termChainReceiptEquiv capability (state₂, query₂) answer))

/-- A real supported Boolean request inhabits its observable receipt fibre. -/
theorem truth_receipt_inhabited :
    Nonempty (observableReceiptFamily
      Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityExample.truthCapability
      true
      (classOf
        Mettapedia.OSLF.Framework.WMCalculusNativeContextExample.booleanReading true,
        ())) := by
  exact ⟨⟨rfl, rfl⟩⟩

/-- The same capability's unsupported Boolean request has no inhabitant
at any candidate answer, so the family is genuinely partial. -/
theorem false_receipt_empty (answer : Bool) :
    ¬ Nonempty (observableReceiptFamily
      Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityExample.truthCapability
      answer
      (classOf
        Mettapedia.OSLF.Framework.WMCalculusNativeContextExample.booleanReading false,
        ())) := by
  rintro ⟨receipt⟩
  exact Bool.noConfusion receipt.supported

end Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
