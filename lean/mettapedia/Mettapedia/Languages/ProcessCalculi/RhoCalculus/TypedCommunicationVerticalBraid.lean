import Mettapedia.GSLT.LanguageDef.InteractionEventAuthority
import Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DependentReflectiveCommunicationCell
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ScopedRefinement
import Mettapedia.Languages.MeTTa.Prime.SelectedCostLayerIterationBoundary

/-!
# A vertical braid for one dependent typed rho communication

The revision-indexed typed COMM cell retains a strict occurrence and its
literal rho endpoints.  This module carries that same closed communication
through exact NIK authority, a funded operational Cost1 step, the generated
Cost1 grammar and reduction, and one selected Cost2 displayed fibre.

The endpoints commute after the already-declared rho equations.  The
dependent boundary is retained as well: endpoint-indexed receipt families
descend, while revision-indexed continuations do not.  At Cost2, an exact
provenance key remains available even though compact erasure is not globally
exact.  Positive and negative controls therefore cross the entire vertical
without identifying its distinct semantic faces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationVerticalBraid

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.ProofRelevantRelationProtocol
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.GSLT.LanguageDef.Cost.Elaboration
open Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InteractionEventAuthority
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyContract
open Mettapedia.Languages.MeTTa.Prime.SelectedCostLayerIterationBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DependentReflectiveCommunicationCell
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.RevisionedTypedCommunicationDemand
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationProtocol
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

/-! ## Exact occurrence replay -/

/-- Authority identifier for the typed COMM checker. -/
inductive AuthorityId where
  | typedCommunication
deriving DecidableEq, Repr

/-- Structural rho syntax is an executable exact endpoint identity.  The
well-sortedness proof is not hashed or assumed: injectivity follows from the
subtype projection itself. -/
def rhoProcessIdentity : ExactEndpointIdentity RhoProcess where
  Identity := Pattern
  decEq := inferInstance
  identify := Subtype.val
  identify_injective := Subtype.val_injective

/-- The local NIK authority generated from the exact typed-COMM event family. -/
abbrev typedCommunicationAuthority :=
  stepAuthorityByIdentity AuthorityId.typedCommunication rhoProcessIdentity
    (interaction typedCommProtocol)

/-- The existing revision-zero communication retained as an enabled event. -/
noncomputable def zeroCommunicationEvent :
    (interaction typedCommProtocol).Enabled
      (exactEndpoints zeroCommunication).1 :=
  eventOfOutgoing StrictCoreCommOccurrence
    ⟨(exactEndpoints zeroCommunication).2, zeroCommunication.2⟩

/-- Exact certificate for the existing revision-zero communication. -/
noncomputable def zeroCommunicationCertificate :
    typedCommunicationAuthority.Certificate where
  source := (exactEndpoints zeroCommunication).1
  event := zeroCommunicationEvent

/-- Claim checked by the positive certificate. -/
noncomputable def zeroCommunicationClaim : StepClaim typedCommSystem where
  source := (exactEndpoints zeroCommunication).1
  target := (exactEndpoints zeroCommunication).2

/-- The certificate containing the actual strict occurrence is accepted for
its exact endpoint claim. -/
theorem zeroCommunicationCertificate_accepted :
    typedCommunicationAuthority.check zeroCommunicationClaim
      zeroCommunicationCertificate = true := by
  rfl

/-- Negative control: reusing the live occurrence certificate as a self-loop
claim is rejected by endpoint replay. -/
theorem zeroCommunicationCertificate_rejects_forged_target :
    typedCommunicationAuthority.check
      { source := (exactEndpoints zeroCommunication).1
        target := (exactEndpoints zeroCommunication).1 }
      zeroCommunicationCertificate = false := by
  change decide
      ((exactEndpoints zeroCommunication).1.1 =
          (exactEndpoints zeroCommunication).1.1 ∧
        (exactEndpoints zeroCommunication).1.1 =
          (exactEndpoints zeroCommunication).2.1) = false
  simp only [true_and, decide_eq_false_iff_not]
  intro samePattern
  apply typedCommOccurrence_source_ne_target zeroCommunication.2
  apply Subtype.ext
  exact samePattern

/-- The generated NIK authority is complete for every typed protocol step,
not only for the closed control occurrence. -/
theorem typedCommunicationAuthority_complete :
    typedCommunicationAuthority.Complete :=
  by
    simpa [typedCommunicationAuthority] using
      stepAuthorityByIdentity_complete AuthorityId.typedCommunication
        rhoProcessIdentity (interaction_complete typedCommProtocol)

/-- Acceptance is sound for the same typed COMM step already used by the
dependent cell. -/
theorem accepted_zeroCommunication_enters_typed_protocol :
    zeroCommunicationClaim.Meaning :=
  typedCommunicationAuthority.sound zeroCommunicationCertificate_accepted

/-! ## A funded Cost1 refinement of the same COMM step -/

/-- The smallest concrete funding authority used by the closed communication.
It is an operational resource atom, not the rho channel itself. -/
abbrev CommunicationFundingAtom := Unit

/-- One nonempty authority seal funds the communication. -/
def communicationSeal : CostSig CommunicationFundingAtom := {()}

theorem communicationSeal_valid : communicationSeal.RuntimeValid := by
  simp [CostSig.RuntimeValid, communicationSeal]

/-- The funded channel; its pure erasure is selected separately below. -/
def communicationCostChannel : CostName CommunicationFundingAtom :=
  .signature communicationSeal

/-- One exact purse-head occurrence covers the whole communication demand. -/
def communicationFunding :
    FundingSelection CommunicationFundingAtom communicationCostChannel
      communicationSeal where
  chosen := {⟨communicationSeal, .empty, communicationSeal_valid⟩}
  demand_eq := by simp [communicationSeal]

/-- The funded version of the existing nil-body/nil-payload COMM occurrence. -/
def communicationCostEvent : CostedEvent CommunicationFundingAtom :=
  .wholeRecvSend communicationCostChannel .nil .nil communicationSeal
    communicationSeal_valid communicationFunding

/-- Exact source resources owned by the funded occurrence. -/
def communicationCostSource : CostConfig CommunicationFundingAtom :=
  communicationCostEvent.consumed

/-- Exact target resources produced by the funded occurrence. -/
def communicationCostTarget : CostConfig CommunicationFundingAtom :=
  communicationCostEvent.produced

/-- The computational endpoint component before funding erasure. -/
def communicationCostRedex : CostTerm CommunicationFundingAtom :=
  .signed
    (.par (.recv communicationCostChannel .nil)
      (.send communicationCostChannel .nil))
    communicationSeal

/-- The exact purse occurrence consumed by the funded event. -/
def communicationFundingPurse : CostTerm CommunicationFundingAtom :=
  .purse communicationCostChannel (.cons communicationSeal .empty)

/-- The exhausted purse remains an inert operational resource after firing. -/
def communicationResidualPurse : CostTerm CommunicationFundingAtom :=
  .purse communicationCostChannel .empty

theorem communicationCostSource_components :
    communicationCostSource =
      communicationCostRedex ::ₘ communicationFundingPurse ::ₘ 0 := by
  rfl

theorem communicationCostTarget_components :
    communicationCostTarget = communicationResidualPurse ::ₘ 0 := by
  rfl

/-- The singleton matching keeps the event occurrence distinct from its
untouched frame, which is empty here. -/
def communicationCostMatching : CostMatching CommunicationFundingAtom where
  source := communicationCostSource
  events := [communicationCostEvent]
  frame := 0
  source_eq := by
    simp [communicationCostSource, costWaveSource]

/-- The funded occurrence is one genuine nonempty parallel Cost step. -/
theorem communicationParallelCostStep :
    ParallelCostStep communicationCostSource
      communicationCostMatching.receipt communicationCostTarget := by
  refine ⟨communicationCostMatching, rfl, ?_, rfl, ?_⟩
  · simp [communicationCostMatching]
  · simp [communicationCostMatching, communicationCostTarget,
      CostMatching.target, costWaveTarget]

/-- Cost1 retains the exact occurrence receipt and a one-wave schedule. -/
def communicationCostSchedule :
    OperationalSchedule CommunicationFundingAtom communicationCostSource
      communicationCostTarget :=
  oneWave communicationParallelCostStep

/-- This declared WorkSpan is derived from the singleton retained receipt. -/
theorem communicationCostSchedule_workSpan :
    communicationCostSchedule.workSpan = ⟨1, 1⟩ := by
  rw [show communicationCostSchedule = oneWave communicationParallelCostStep by
    rfl, oneWave_workSpan]
  simp [communicationCostMatching, CostMatching.receipt, costWaveReceipt,
    communicationCostEvent]

/-- The chronology valuation returns the complete singleton wave history,
not merely the WorkSpan pair. -/
theorem communicationCostSchedule_chronology :
    scheduleGrade (chronologyValuation CommunicationFundingAtom)
        communicationCostSchedule =
      some (Mettapedia.GSLT.LanguageDef.CostScheduleObservation.Schedule.events
        communicationCostSchedule) := by
  exact scheduleGrade_chronology communicationCostSchedule

/-- Every cost signature is erased to the same already-derived closed rho
name.  This is sufficient for this one-channel specimen and is stated as an
explicit semantic choice. -/
def communicationSignatureName :
    SignatureNameEncoding CommunicationFundingAtom :=
  fun _ => closedNilName.1

theorem communicationSignatureName_closed :
    communicationSignatureName.MapsToClosedRhoNames := by
  intro _signature
  exact closedNilName.2

/-- The concrete funded source is binder safe. -/
theorem communicationCostSource_binderSafe :
    communicationCostSource.BinderSafe := by
  unfold communicationCostSource communicationCostEvent
  apply CostConfig.BinderSafe.add
  · exact CostTerm.BinderSafe.singleton
      (.signed (.par (.recv .signature .nil) (.send .signature .nil)))
  · exact LocatedPurse.configComponents_binderSafe _

/-- The corresponding interleaving step is the singleton event with no
surrounding frame. -/
def communicationCostStep :
    CostStep communicationCostSource communicationCostChannel
      communicationSeal communicationCostTarget := by
  simpa [communicationCostSource, communicationCostTarget,
    communicationCostEvent, communicationCostChannel, communicationSeal,
    CostedEvent.location, CostedEvent.spend] using
    communicationCostEvent.toCostStepIn 0

/-- Binder safety of the target is derived by preservation, rather than
rechecked independently. -/
def communicationCostTarget_binderSafe :
    communicationCostTarget.BinderSafe :=
  communicationCostStep.preserves_binderSafe
    communicationCostSource_binderSafe

/-- Canonical cost erasure sends the funded step into the established rho
GSLT. -/
theorem communicationCostStep_erases_to_rho :
    rhoLanguageDefGSLT.Step
      (communicationCostSource.eraseCanonicalProcess
        communicationSignatureName_closed communicationCostSource_binderSafe)
      (communicationCostTarget.eraseCanonicalProcess
        communicationSignatureName_closed communicationCostTarget_binderSafe) :=
  communicationCostStep.eraseCanonical_rhoLanguageDefGSLTStep
    communicationSignatureName_closed communicationCostSource_binderSafe

private theorem applicationCongruenceTwo {constructor : String}
    {left₁ left₂ right₁ right₂ : Pattern}
    (first : StructuralCongruence left₁ right₁)
    (second : StructuralCongruence left₂ right₂) :
    StructuralCongruence
      (.apply constructor [left₁, left₂])
      (.apply constructor [right₁, right₂]) := by
  refine StructuralCongruence.apply_cong constructor
    [left₁, left₂] [right₁, right₂] rfl ?_
  intro index leftBound _rightBound
  have indexBound : index < 2 := by simpa using leftBound
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl
  · simpa using first
  · simpa using second

private theorem parallelCongruenceTwo
    {left₁ left₂ right₁ right₂ : Pattern}
    (first : StructuralCongruence left₁ right₁)
    (second : StructuralCongruence left₂ right₂) :
    StructuralCongruence
      (.collection .hashBag [left₁, left₂] none)
      (.collection .hashBag [right₁, right₂] none) := by
  refine StructuralCongruence.par_cong
    [left₁, left₂] [right₁, right₂] rfl ?_
  intro index leftBound _rightBound
  have indexBound : index < 2 := by simpa using leftBound
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl
  · simpa using first
  · simpa using second

/-- The funded source erases into the exact source equation class of the
dependent typed communication.  Literal equality is intentionally not
claimed: canonical erasure removes representation-only parallel wrappers. -/
theorem communicationCostSource_erases_equivalent_exactSource :
    rhoProcessEquations.r
      (communicationCostSource.eraseCanonicalProcess
        communicationSignatureName_closed communicationCostSource_binderSafe)
      (exactEndpoints zeroCommunication).1 := by
  change rhoProcessEquations.r
    (communicationCostSource.eraseCanonicalProcess
      communicationSignatureName_closed communicationCostSource_binderSafe)
    closedNilCommData.source
  rw [closedNilCommData_source_eq]
  rw [rhoProcessEquations_iff_structuralCongruence]
  change StructuralCongruence
    (CostConfig.eraseCanonical communicationSignatureName
      communicationSignatureName_closed.wellSorted.hashSetFree
      communicationCostSource)
    closedCommSource.1
  rw [communicationCostSource_components]
  change StructuralCongruence
    (CostConfig.eraseCanonical communicationSignatureName
      communicationSignatureName_closed.wellSorted.hashSetFree
      (Quotient.mk _
        [communicationCostRedex, communicationFundingPurse]))
    closedCommSource.1
  have erasedToRaw := CostConfig.eraseCanonical_structural_quotientMk
    communicationSignatureName
    communicationSignatureName_closed.wellSorted.hashSetFree
    [communicationCostRedex, communicationFundingPurse]
  let rawNil : Pattern := .collection .hashBag [] none
  let nilProcess : Pattern := .apply "PZero" []
  let rawInput : Pattern := .apply "PInput"
    [closedNilName.1, .lambda none rawNil]
  let input : Pattern := .apply "PInput"
    [closedNilName.1, .lambda none nilProcess]
  let rawOutput : Pattern := .apply "POutput"
    [closedNilName.1, rawNil]
  let output : Pattern := .apply "POutput"
    [closedNilName.1, nilProcess]
  have nilCongruent : StructuralCongruence rawNil nilProcess := by
    exact StructuralCongruence.par_empty
  have inputCongruent : StructuralCongruence rawInput input := by
    exact applicationCongruenceTwo (StructuralCongruence.refl _)
      (StructuralCongruence.lambda_cong none _ _ nilCongruent)
  have outputCongruent : StructuralCongruence rawOutput output := by
    exact applicationCongruenceTwo (StructuralCongruence.refl _) nilCongruent
  have redexCongruent : StructuralCongruence
      (.collection .hashBag [rawInput, rawOutput] none)
      (.collection .hashBag [input, output] none) :=
    parallelCongruenceTwo inputCongruent outputCongruent
  have rawToSource : StructuralCongruence
      (.collection .hashBag
        [.collection .hashBag [rawInput, rawOutput] none, rawNil] none)
      (.collection .hashBag [input, output] none) :=
    StructuralCongruence.trans _ _ _
      (parallelCongruenceTwo redexCongruent nilCongruent)
      (StructuralCongruence.par_nil_right _)
  exact StructuralCongruence.trans _ _ _ erasedToRaw (by
    simpa [communicationCostRedex, communicationFundingPurse,
      communicationCostChannel, communicationSeal,
      communicationSignatureName, CostName.erase, CostTerm.erase,
      CostProc.erase, closedCommSource, rawNil, nilProcess,
      rawInput, input, rawOutput, output] using rawToSource)

/-- The funded target likewise erases into the exact target equation class;
the exhausted purse and singleton parallel wrapper are observationally inert
under the established rho equations. -/
theorem communicationCostTarget_erases_equivalent_exactTarget :
    rhoProcessEquations.r
      (communicationCostTarget.eraseCanonicalProcess
        communicationSignatureName_closed communicationCostTarget_binderSafe)
      (exactEndpoints zeroCommunication).2 := by
  change rhoProcessEquations.r
    (communicationCostTarget.eraseCanonicalProcess
      communicationSignatureName_closed communicationCostTarget_binderSafe)
    closedNilCommData.target
  rw [closedNilCommData_target_eq]
  rw [rhoProcessEquations_iff]
  change Canonical.canonicalize
      (CostConfig.eraseCanonical communicationSignatureName
        communicationSignatureName_closed.wellSorted.hashSetFree
        communicationCostTarget) =
    Canonical.canonicalize closedCommTarget.1
  rw [communicationCostTarget_components]
  change Canonical.canonicalize
      (CostConfig.eraseCanonical communicationSignatureName
        communicationSignatureName_closed.wellSorted.hashSetFree
        (Quotient.mk _ [communicationResidualPurse])) =
    Canonical.canonicalize closedCommTarget.1
  rw [CostConfig.eraseCanonical_quotientMk]
  simp [communicationResidualPurse, communicationCostChannel,
    communicationSeal, CostTerm.erase, closedCommTarget,
    Canonical.canonicalize, Canonical.canonicalizeList,
    Canonical.normalizeBagElements, Canonical.sortPatterns,
    Canonical.bagSplice, Canonical.collapseBag]

/-- The Cost1 refinement square lands on the exact typed COMM endpoints after
the explicitly declared rho equations, with no endpoint step imported from
the typed proof. -/
theorem communicationCostStep_exact_commuting_square :
    rhoLanguageDefGSLT.Step
      (exactEndpoints zeroCommunication).1
      (exactEndpoints zeroCommunication).2 := by
  obtain ⟨middle, exactSourceStep, costTargetEquivalentMiddle⟩ :=
    rhoLanguageDefGSLT.rewrites_resp_left
      communicationCostSource_erases_equivalent_exactSource
      communicationCostStep_erases_to_rho
  apply rhoLanguageDefGSLT.rewrites_resp_right exactSourceStep
  exact rhoProcessEquations.iseqv.trans
    (rhoProcessEquations.iseqv.symm costTargetEquivalentMiddle)
    communicationCostTarget_erases_equivalent_exactTarget

/-! ## The same funded communication in the generated Cost language -/

/-- The generated Cost signature unit chosen to denote the operational
singleton seal.  This is an explicit comparison datum between the runtime
resource algebra and the declaration-generated Cost language. -/
def communicationGeneratedSignature : Pattern :=
  .apply costSignatureUnitConstructorName []

/-- Empty residual stack in the declaration-generated Cost language. -/
def communicationGeneratedEmptyStack : Pattern :=
  .apply costTokenStackEmptyConstructorName []

/-- The one-token stack corresponding to `communicationSeal`. -/
def communicationGeneratedStack : Pattern :=
  .apply costTokenStackConsConstructorName
    [communicationGeneratedSignature, communicationGeneratedEmptyStack]

/-- Base-colour nil process used by the generated communication core. -/
def communicationGeneratedBaseNil : Pattern :=
  .apply (costBaseConstructorName "PZero") []

/-- Wrapped-colour nil continuation used at the selected interaction cut. -/
def communicationGeneratedWrappedNil : Pattern :=
  .apply (costWrappedConstructorName "PZero") []

/-- Generated base-colour copy of the same closed rho channel. -/
def communicationGeneratedName : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [communicationGeneratedBaseNil]

/-- Generated base interaction core of the closed input/output pair. -/
def communicationGeneratedCore : Pattern :=
  .collection .hashBag
    [.apply (costBaseConstructorName "PInput")
      [communicationGeneratedName,
        .lambda none communicationGeneratedWrappedNil],
     .apply (costBaseConstructorName "POutput")
      [communicationGeneratedName, communicationGeneratedWrappedNil]] none

/-- Closed first generated Cost term for the same funded communication.  Its
outer shape is the generated whole-redex discipline: contact of a signed
interaction core with a stack carrying the identical signature. -/
def communicationGeneratedCost1Pattern : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName
      [communicationGeneratedCore, communicationGeneratedSignature],
     .apply costFundingConstructorName [communicationGeneratedStack]]

/-- The generated term lies in the wrapped interacting fibre. -/
def communicationGeneratedCost1Sort : LangSort rhoCIGSLT.costWholeLanguage :=
  ⟨costWrappedSortName, rhoCIGSLT.costWrappedSortName_mem_costWhole⟩

private theorem communicationGeneratedSignature_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedSignature (.base costSignatureSortName) := by
  apply HasType.constructor (rule := costSignatureUnitConstructor)
  · rw [rhoCIGSLT.costWholeLanguage_terms]
    apply List.mem_append_right
    simp [costCoreConstructors]
  · simp [UsesBareCollection, costSignatureUnitConstructor]
  · exact .nil

private theorem communicationGeneratedEmptyStack_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedEmptyStack (.base costTokenStackSortName) := by
  apply HasType.constructor (rule := costTokenStackEmptyConstructor)
  · rw [rhoCIGSLT.costWholeLanguage_terms]
    apply List.mem_append_right
    simp [costCoreConstructors]
  · simp [UsesBareCollection, costTokenStackEmptyConstructor]
  · exact .nil

private theorem communicationGeneratedStack_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedStack (.base costTokenStackSortName) := by
  apply HasType.constructor (rule := costTokenStackConsConstructor)
  · rw [rhoCIGSLT.costWholeLanguage_terms]
    apply List.mem_append_right
    simp [costCoreConstructors]
  · simp [UsesBareCollection, costTokenStackConsConstructor]
  · exact .cons trivial rfl communicationGeneratedSignature_typed
      (.cons trivial rfl communicationGeneratedEmptyStack_typed .nil)

private theorem communicationGeneratedBaseNil_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedBaseNil (.base (costBaseSortName "Proc")) := by
  exact checkHasType_sound (by decide)

private theorem communicationGeneratedWrappedNil_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedWrappedNil (.base costWrappedSortName) := by
  exact checkHasType_sound (by decide)

private theorem communicationGeneratedName_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedName (.base (costBaseSortName "Name")) := by
  exact checkHasType_sound (by decide)

private theorem communicationGeneratedWrappedNil_under_input_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty
      [.base (costBaseSortName "Name")]
      communicationGeneratedWrappedNil (.base costWrappedSortName) := by
  exact checkHasType_sound (by decide)

private theorem communicationGeneratedInput_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (.apply (costBaseConstructorName "PInput")
      [communicationGeneratedName,
          .lambda none communicationGeneratedWrappedNil])
      (.base (costBaseSortName "Proc")) := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[5])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (List.getElem_mem _)
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseInputConstructor_params]
    exact .cons trivial rfl communicationGeneratedName_typed
      (.cons trivial rfl
        (.lambda communicationGeneratedWrappedNil_under_input_typed) .nil)

private theorem communicationGeneratedOutput_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (.apply (costBaseConstructorName "POutput")
        [communicationGeneratedName, communicationGeneratedWrappedNil])
      (.base (costBaseSortName "Proc")) := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[4])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (List.getElem_mem _)
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseOutputConstructor_params]
    exact .cons trivial rfl communicationGeneratedName_typed
      (.cons trivial rfl communicationGeneratedWrappedNil_typed .nil)

private theorem communicationGeneratedCore_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedCore (.base (costBaseSortName "Proc")) := by
  apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[3])
      (parameterName := "ps")
      (elementType := .base (costBaseSortName "Proc"))
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (List.getElem_mem _)
  · exact rho_costBaseParallelConstructor_params
  · exact .cons communicationGeneratedInput_typed
      (.cons communicationGeneratedOutput_typed (.nil _ _))

private theorem communicationGeneratedSigned_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (.apply costSignedConstructorName
        [communicationGeneratedCore, communicationGeneratedSignature])
      (.base costWrappedSortName) := by
  apply HasType.constructor
      (rule := costSignedConstructor
        rhoCIGSLT.theory.presentation.interactingSort.1.name)
  · rw [rhoCIGSLT.costWholeLanguage_terms]
    apply List.mem_append_right
    simp [costCoreConstructors]
  · simp [UsesBareCollection, costSignedConstructor]
  · have coreTyped : HasType rhoCIGSLT.costWholeLanguage
        FreeTypeContext.empty [] communicationGeneratedCore
        (.base (costBaseSortName
          rhoCIGSLT.theory.presentation.interactingSort.1.name)) := by
      simpa [rhoCIGSLT, rhoIGSLT, rhoInteractivePresentation, rhoCalc,
        TypeDecl.plain] using communicationGeneratedCore_typed
    exact .cons trivial rfl coreTyped
      (.cons trivial rfl communicationGeneratedSignature_typed .nil)

private theorem communicationGeneratedFunding_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (.apply costFundingConstructorName [communicationGeneratedStack])
      (.base costWrappedSortName) := by
  apply HasType.constructor (rule := costFundingConstructor)
  · rw [rhoCIGSLT.costWholeLanguage_terms]
    apply List.mem_append_right
    simp [costCoreConstructors]
  · simp [UsesBareCollection, costFundingConstructor]
  · exact .cons trivial rfl communicationGeneratedStack_typed .nil

/-- The declaration-derived checker accepts the complete closed funded term.
This derivation uses the generated grammar and sort checker, independently of
the operational `CostStep` proof above. -/
theorem communicationGeneratedCost1_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedCost1Pattern (.base costWrappedSortName) := by
  apply HasType.constructor (rule := costContactConstructor)
  · rw [rhoCIGSLT.costWholeLanguage_terms]
    apply List.mem_append_right
    simp [costCoreConstructors]
  · simp [UsesBareCollection, costContactConstructor]
  · exact .cons trivial rfl communicationGeneratedSigned_typed
      (.cons trivial rfl communicationGeneratedFunding_typed .nil)

/-- Checked first generated Cost object corresponding to the operational
communication. -/
def communicationGeneratedCost1Term :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedCost1Sort := by
  refine ⟨communicationGeneratedCost1Pattern,
    ⟨⟨communicationGeneratedCost1_typed, rfl, rfl,
      communicationGeneratedCost1_typed.isWellScopedAt⟩, ?_⟩⟩
  intro declaration membership
  simp [communicationGeneratedCost1Pattern, communicationGeneratedCore,
    communicationGeneratedName, communicationGeneratedBaseNil,
    communicationGeneratedWrappedNil, communicationGeneratedSignature,
    communicationGeneratedStack, communicationGeneratedEmptyStack,
    binderSafeAt, binderSafeListAt]

/-- Its proof-relevant Cost1 elaboration is constructed by the actual region
compiler, not postulated from compact syntax. -/
def communicationGeneratedCost1Elaboration :
    CostElabTerm rhoCIGSLT FreeTypeContext.empty []
      communicationGeneratedCost1Sort :=
  CostOpenElaboration.compileTerm rhoCIGSLT communicationGeneratedCost1Term

/-- Compiling the generated Cost1 term preserves its complete compact term. -/
theorem communicationGeneratedCost1Elaboration_erases :
    CostOpenElaboration.erase communicationGeneratedCost1Elaboration =
      communicationGeneratedCost1Term :=
  CostOpenElaboration.erase_compileTerm rhoCIGSLT
    communicationGeneratedCost1Term

/-- Removing both generated static colours from the computational core
recovers the literal closed rho COMM source.  The administrative signature,
stack, and contact remain outside this theorem on purpose. -/
theorem communicationGeneratedCore_erases_to_exactSource :
    CostAuthoredAtomKey.eraseColor .wrapped
        (CostAuthoredAtomKey.eraseColor .base communicationGeneratedCore) =
      (exactEndpoints zeroCommunication).1.1 := by
  change CostAuthoredAtomKey.eraseColor .wrapped
      (CostAuthoredAtomKey.eraseColor .base communicationGeneratedCore) =
    closedNilCommData.source.1
  rw [closedNilCommData_source_eq]
  rfl

/-- Computational contractum selected by the authored generated Cost rule. -/
def communicationGeneratedTargetCore : Pattern :=
  .collection .hashBag [communicationGeneratedWrappedNil] none

/-- The exhausted generated Cost state retains the wrapped contractum and the
empty residual funding stack under the same contact node. -/
def communicationGeneratedCost1TargetPattern : Pattern :=
  .apply costContactConstructorName
    [communicationGeneratedTargetCore,
      .apply costFundingConstructorName
        [communicationGeneratedEmptyStack]]

/-- The generated target's computational component erases to the literal rho
COMM target. -/
theorem communicationGeneratedTargetCore_erases_to_exactTarget :
    CostAuthoredAtomKey.eraseColor .wrapped
        (CostAuthoredAtomKey.eraseColor .base
          communicationGeneratedTargetCore) =
      (exactEndpoints zeroCommunication).2.1 := by
  change CostAuthoredAtomKey.eraseColor .wrapped
      (CostAuthoredAtomKey.eraseColor .base
        communicationGeneratedTargetCore) = closedNilCommData.target.1
  rw [closedNilCommData_target_eq]
  rfl

private def communicationGeneratedParallelConstructor :
    DeclaredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[3], List.getElem_mem _⟩

private theorem communicationGeneratedParallel_selected :
    communicationGeneratedParallelConstructor ∈
      rhoContinuationRetyping.wrappedConstructors := by
  apply (rhoContinuationRetyping.mem_wrappedConstructors_iff
    communicationGeneratedParallelConstructor).2
  constructor <;> decide

private theorem communicationGeneratedWrappedParallel_mem :
    costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[3] ∈
      rhoCIGSLT.costWholeLanguage.terms := by
  change costWrappedConstructor (theory := rhoCIGSLT.theory)
      communicationGeneratedParallelConstructor.1 ∈
        rhoCIGSLT.costWholeLanguage.terms
  exact rhoCIGSLT.costWrappedConstructor_mem_costWhole
    communicationGeneratedParallelConstructor
      communicationGeneratedParallel_selected

private theorem communicationGeneratedTargetCore_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedTargetCore (.base costWrappedSortName) := by
  apply HasType.collectionConstructor
      (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[3])
      (parameterName := "ps")
      (elementType := .base costWrappedSortName)
  · exact communicationGeneratedWrappedParallel_mem
  · exact rho_costWrappedParallelConstructor_params
  · exact .cons communicationGeneratedWrappedNil_typed (.nil _ _)

private theorem communicationGeneratedResidualFunding_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (.apply costFundingConstructorName [communicationGeneratedEmptyStack])
      (.base costWrappedSortName) := by
  apply HasType.constructor (rule := costFundingConstructor)
  · rw [rhoCIGSLT.costWholeLanguage_terms]
    apply List.mem_append_right
    simp [costCoreConstructors]
  · simp [UsesBareCollection, costFundingConstructor]
  · exact .cons trivial rfl communicationGeneratedEmptyStack_typed .nil

/-- The independently named exhausted state is admitted by the same generated
Cost grammar as its source. -/
theorem communicationGeneratedCost1Target_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedCost1TargetPattern (.base costWrappedSortName) := by
  apply HasType.constructor (rule := costContactConstructor)
  · rw [rhoCIGSLT.costWholeLanguage_terms]
    apply List.mem_append_right
    simp [costCoreConstructors]
  · simp [UsesBareCollection, costContactConstructor]
  · exact .cons trivial rfl communicationGeneratedTargetCore_typed
      (.cons trivial rfl communicationGeneratedResidualFunding_typed .nil)

/-- Executing the generated language at one contextual layer returns exactly
the independently named exhausted state. -/
theorem communicationGeneratedCost1_rewriteAt :
    rewriteAt (engineBasePremises RelationEnv.empty)
        rhoCIGSLT.costWholeLanguage 1
        communicationGeneratedCost1Pattern =
      [communicationGeneratedCost1TargetPattern] := by
  decide +kernel

/-- Thus the first generated Cost face contains an actual authored reduction,
not merely a well-sorted encoding of the operational event. -/
theorem communicationGeneratedCost1_step :
    Step (engineBasePremises RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage communicationGeneratedCost1Pattern
        communicationGeneratedCost1TargetPattern := by
  refine ⟨1, (mem_rewriteAt_iff_stepAt).1 ?_⟩
  rw [communicationGeneratedCost1_rewriteAt]
  simp

/-! ## A concrete displayed Cost2 state -/

/-- The selected compact output of the established first rho Cost layer. -/
noncomputable abbrev communicationCost2Source : CIGSLT :=
  rhoSelectedCostLayerConfiguration.source

/-- Repeated Cost transports the complete first generated term through the
declaration-derived closure symbol map. -/
def communicationGeneratedCost2Pattern : Pattern :=
  mapPattern rhoCIGSLT.costClosureSymbols communicationGeneratedCost1Pattern

/-- The transported communication remains in the wrapped interacting sort of
the selected second Cost language. -/
def communicationGeneratedCost2Sort :
    LangSort communicationCost2Source.costWholeLanguage :=
  ⟨costWrappedSortName,
    communicationCost2Source.costWrappedSortName_mem_costWhole⟩

private theorem communicationGeneratedCost2_typed_in_generatedLanguage :
    HasType rhoCIGSLT.costContinuationRetyping.generatedLanguage
      FreeTypeContext.empty [] communicationGeneratedCost2Pattern
      (.base costWrappedSortName) := by
  have mapped :=
    communicationGeneratedCost1_typed.mapTyping rhoCIGSLT.costClosureTyping
  change HasType rhoCIGSLT.costContinuationRetyping.generatedLanguage
      (FreeTypeContext.empty.map rhoCIGSLT.costClosureSymbols) []
      (mapPattern rhoCIGSLT.costClosureSymbols
        communicationGeneratedCost1Pattern)
      (mapTypeExpr rhoCIGSLT.costClosureSymbols
        (.base costWrappedSortName)) at mapped
  simpa [communicationGeneratedCost2Pattern, CIGSLT.costClosureTyping,
    FreeTypeContext.map,
    rhoCIGSLT.mapTypeExpr_costClosureSymbols, costWrappedTypeExpr] using mapped

/-- The mapped term is admitted by the actual selected second Cost language,
whose static signature extends the closure-generated language. -/
theorem communicationGeneratedCost2_typed :
    HasType communicationCost2Source.costWholeLanguage
      FreeTypeContext.empty [] communicationGeneratedCost2Pattern
      (.base costWrappedSortName) := by
  apply communicationGeneratedCost2_typed_in_generatedLanguage.weakenTerms
  intro rule membership
  change rule ∈
    rhoSelectedCostLayerConfiguration.source.costWholeLanguage.terms
  rw [CIGSLT.costWholeLanguage_terms]
  apply List.mem_append_left
  change rule ∈
    rhoCIGSLT.costContinuationRetyping.generatedLanguage.terms
  exact membership

/-- Checked compact term in the selected Cost2 language. -/
noncomputable def communicationGeneratedCost2Term :
    ReflectiveWellSorted.OpenTerm
      communicationCost2Source.costWholeReflectionProfile
      communicationCost2Source.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedCost2Sort := by
  refine ⟨communicationGeneratedCost2Pattern,
    ⟨⟨communicationGeneratedCost2_typed, rfl, rfl,
      communicationGeneratedCost2_typed.isWellScopedAt⟩, ?_⟩⟩
  intro declaration membership
  simp [communicationGeneratedCost2Pattern,
    communicationGeneratedCost1Pattern, communicationGeneratedCore,
    communicationGeneratedName, communicationGeneratedBaseNil,
    communicationGeneratedWrappedNil, communicationGeneratedSignature,
    communicationGeneratedStack, communicationGeneratedEmptyStack,
    CIGSLT.costClosureSymbols, mapPattern, mapPatternList_eq_map,
    binderSafeAt, binderSafeListAt]

/-- The selected Cost2 compiler retains a checked region tree over this exact
transported communication term. -/
noncomputable def communicationGeneratedCost2Elaboration :
    CostElabTerm communicationCost2Source FreeTypeContext.empty []
      communicationGeneratedCost2Sort :=
  CostOpenElaboration.compileTerm communicationCost2Source
    communicationGeneratedCost2Term

/-- The selected second-layer compiler preserves the complete checked compact
communication term. -/
theorem communicationGeneratedCost2Elaboration_erases :
    CostOpenElaboration.erase communicationGeneratedCost2Elaboration =
      communicationGeneratedCost2Term :=
  CostOpenElaboration.erase_compileTerm communicationCost2Source
    communicationGeneratedCost2Term

/-- The concrete communication as an inhabitant of the unconditional
selected Cost2 displayed carrier. -/
noncomputable def communicationGeneratedCost2State :
    RhoSelectedCostLayerIterationState :=
  ⟨⟨FreeTypeContext.empty, [], communicationGeneratedCost2Sort⟩,
    communicationGeneratedCost2Elaboration⟩

/-- Compact erasure of the concrete displayed state retains the complete
typed Cost2 term and its dependent indices. -/
theorem communicationGeneratedCost2State_compactKey :
    rhoSelectedCostLayerIterationCompactKey
        communicationGeneratedCost2State =
      ⟨⟨FreeTypeContext.empty, [], communicationGeneratedCost2Sort⟩,
        communicationGeneratedCost2Term⟩ := by
  rfl

/-- Inside the exact communication fibre, retained elaboration provenance is
an exact replay key. -/
theorem communicationGeneratedCost2_provenance_exact :
    ReplayKey.IsExact
      (provenanceKey
        (source := communicationCost2Source)
        (term := communicationGeneratedCost2Term)) :=
  provenanceKey_isExact

/-- In contrast, the complete selected compact Cost2 carrier is not an exact
replay key.  This is the established global nonfactorization boundary, now
adjacent to an actual transported communication inhabitant. -/
theorem selectedCost2_compactKey_not_exact :
    ¬ ReplayKey.IsExact
      (compactCarrierKey rhoSelectedCostLayerConfiguration.source) := by
  rw [compactCarrierKey_exactReplay_iff_erasureFaithful]
  exact rhoSelectedCostLayerIteration_boundary_package.2.1

/-! ## The connected vertical boundary -/

/-- Checked evidence that one and the same typed rho communication crosses all
five selected faces.  The fields deliberately retain both preservation and
non-preservation results: exact event replay, two genuine Cost executions,
dependent-family descent and its revision-sensitive failure, and the Cost2
distinction between an exact provenance key and a nonexact global compact
key. -/
structure VerticalBraidEvidence : Prop where
  authorityAccepts :
    typedCommunicationAuthority.check zeroCommunicationClaim
      zeroCommunicationCertificate = true
  authorityRejectsForgedTarget :
    typedCommunicationAuthority.check
      { source := (exactEndpoints zeroCommunication).1
        target := (exactEndpoints zeroCommunication).1 }
      zeroCommunicationCertificate = false
  fundedStep :
    ParallelCostStep communicationCostSource
      communicationCostMatching.receipt communicationCostTarget
  exactWorkSpan : communicationCostSchedule.workSpan = ⟨1, 1⟩
  completeChronology :
    scheduleGrade (chronologyValuation CommunicationFundingAtom)
        communicationCostSchedule =
      some (Mettapedia.GSLT.LanguageDef.CostScheduleObservation.Schedule.events
        communicationCostSchedule)
  operationalSourceReadout :
    rhoProcessEquations.r
      (communicationCostSource.eraseCanonicalProcess
        communicationSignatureName_closed communicationCostSource_binderSafe)
      (exactEndpoints zeroCommunication).1
  operationalTargetReadout :
    rhoProcessEquations.r
      (communicationCostTarget.eraseCanonicalProcess
        communicationSignatureName_closed communicationCostTarget_binderSafe)
      (exactEndpoints zeroCommunication).2
  exactRhoStep :
    rhoLanguageDefGSLT.Step
      (exactEndpoints zeroCommunication).1
      (exactEndpoints zeroCommunication).2
  generatedSourceTyped :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedCost1Pattern (.base costWrappedSortName)
  generatedTargetTyped :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      communicationGeneratedCost1TargetPattern (.base costWrappedSortName)
  generatedStep :
    Step (engineBasePremises RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage communicationGeneratedCost1Pattern
        communicationGeneratedCost1TargetPattern
  generatedSourceReadout :
    CostAuthoredAtomKey.eraseColor .wrapped
        (CostAuthoredAtomKey.eraseColor .base communicationGeneratedCore) =
      (exactEndpoints zeroCommunication).1.1
  generatedTargetReadout :
    CostAuthoredAtomKey.eraseColor .wrapped
        (CostAuthoredAtomKey.eraseColor .base
          communicationGeneratedTargetCore) =
      (exactEndpoints zeroCommunication).2.1
  endpointReceiptDescends :
    Nonempty (FamilyFactorization exactEndpoints endpointReceiptFamily)
  revisionContinuationDoesNotDescend :
    Not (Nonempty
      (FamilyFactorization exactEndpoints revisionContinuation))
  continuationIsNotConstant :
    Not (Exists fun simpleType :
        TypeOver (SimpleFamiliesCwf.{0}) ExactCommunication =>
      simpleToDependentPseudoMorphism.mapTypeObject simpleType =
        continuationDisplay)
  sequencingRetainsChronology :
    sequencedContinuations.map selectedRevision = [0, 1]
  sequencingIsNaturalThroughBagReadout :
    listToBag.map sequencedContinuations =
      bindSigma bagEffect (listToBag.map selectedCommunications)
        (fun communication => listToBag.map
          (continuationAnswers communication))
  endpointOutcomeReadoutIsNotInjective :
    Not (Function.Injective outcomeEndpoints)
  selectedCost2Key :
    rhoSelectedCostLayerIterationCompactKey
        communicationGeneratedCost2State =
      ⟨⟨FreeTypeContext.empty, [], communicationGeneratedCost2Sort⟩,
        communicationGeneratedCost2Term⟩
  exactCost2Provenance :
    ReplayKey.IsExact
      (provenanceKey
        (source := communicationCost2Source)
        (term := communicationGeneratedCost2Term))
  globalCost2CompactReadoutIsNotExact :
    Not (ReplayKey.IsExact
      (compactCarrierKey rhoSelectedCostLayerConfiguration.source))

/-- The full concrete braid.  Every field is discharged by a theorem about
the shared typed COMM occurrence; no face is identified with another. -/
theorem typedCommunication_vertical_braid : VerticalBraidEvidence where
  authorityAccepts := zeroCommunicationCertificate_accepted
  authorityRejectsForgedTarget :=
    zeroCommunicationCertificate_rejects_forged_target
  fundedStep := communicationParallelCostStep
  exactWorkSpan := communicationCostSchedule_workSpan
  completeChronology := communicationCostSchedule_chronology
  operationalSourceReadout :=
    communicationCostSource_erases_equivalent_exactSource
  operationalTargetReadout :=
    communicationCostTarget_erases_equivalent_exactTarget
  exactRhoStep := communicationCostStep_exact_commuting_square
  generatedSourceTyped := communicationGeneratedCost1_typed
  generatedTargetTyped := communicationGeneratedCost1Target_typed
  generatedStep := communicationGeneratedCost1_step
  generatedSourceReadout :=
    communicationGeneratedCore_erases_to_exactSource
  generatedTargetReadout :=
    communicationGeneratedTargetCore_erases_to_exactTarget
  endpointReceiptDescends := ⟨endpointReceiptFamilyFactors⟩
  revisionContinuationDoesNotDescend :=
    revisionContinuation_does_not_factor_through_endpoints
  continuationIsNotConstant := continuationDisplay_not_in_simple_image
  sequencingRetainsChronology := sequencedContinuation_revisions
  sequencingIsNaturalThroughBagReadout :=
    sequencedContinuation_listToBag_natural
  endpointOutcomeReadoutIsNotInjective := outcomeEndpoints_not_injective
  selectedCost2Key := communicationGeneratedCost2State_compactKey
  exactCost2Provenance := communicationGeneratedCost2_provenance_exact
  globalCost2CompactReadoutIsNotExact := selectedCost2_compactKey_not_exact

#print axioms zeroCommunicationCertificate_accepted
#print axioms zeroCommunicationCertificate_rejects_forged_target
#print axioms typedCommunicationAuthority_complete
#print axioms accepted_zeroCommunication_enters_typed_protocol
#print axioms communicationParallelCostStep
#print axioms communicationCostSchedule_workSpan
#print axioms communicationCostSchedule_chronology
#print axioms communicationCostStep_erases_to_rho
#print axioms communicationCostSource_erases_equivalent_exactSource
#print axioms communicationCostTarget_erases_equivalent_exactTarget
#print axioms communicationCostStep_exact_commuting_square
#print axioms communicationGeneratedCost1_typed
#print axioms communicationGeneratedCost1Target_typed
#print axioms communicationGeneratedCost1_step
#print axioms communicationGeneratedCore_erases_to_exactSource
#print axioms communicationGeneratedTargetCore_erases_to_exactTarget
#print axioms communicationGeneratedCost2_typed
#print axioms communicationGeneratedCost2Elaboration_erases
#print axioms communicationGeneratedCost2State_compactKey
#print axioms communicationGeneratedCost2_provenance_exact
#print axioms selectedCost2_compactKey_not_exact
#print axioms typedCommunication_vertical_braid

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationVerticalBraid
