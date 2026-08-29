import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedNativeSearch
import Mettapedia.Languages.MeTTa.Prime.DataFibration
import Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection
import Mettapedia.Languages.MeTTa.Prime.NativeRelationalSearchNIKSelection

/-!
# Current native-policy selection for checked intrinsic hypotheses

A checked raw MIL proof may construct a formed intrinsic `Hyp` program and,
when its primitive relations have exact finite fibres, derive a complete
proof-relevant native search.  This module places that existing construction
under the common native-plus-policy NIK selection theorem.

The policy readout deliberately retains the complete dependent search result
but forgets which execution face produced it.  It therefore supports exact
result and occurrence-count policies, while a face-sensitive policy is
provably unsupported.  Current activation runs the retained native search and
requested policies together; staleness disables both without destroying the
raw query or complete receipt.

The construction is generic over checked finite searches in the runtime-sized
Prime fragment.  It does not make MIL, `Hyp`, or finite search primitive to
NIK, and it does not infer functional representability from finite evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeCheckedHypothesisPolicyNIKSelection

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicMILNativeSearch
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedNativeSearch
open Mettapedia.Languages.MeTTa.Prime.NativeRelationalSearchNIKSelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection
open Mettapedia.Languages.MeTTa.Prime.DataFibration

/-! ## A family-relative result readout -/

inductive ReceiptPolicy where
  | exactResult
  | occurrenceCount
  | executionFace
  deriving DecidableEq, Repr

/-- Policies over one complete native-search receipt.  The exact result
retains the source query, every target occurrence, and every derivation. -/
def receiptPolicies {Source Target : Type}
    (relation : ProofRel Source Target) :
    PolicyFamily (NativeSearchReceipt relation) where
  Policy := ReceiptPolicy
  Result
    | .exactResult => FiniteEvidenceProvider.SearchResult relation
    | .occurrenceCount => Nat
    | .executionFace => SearchFace
  decide
    | .exactResult => NativeSearchReceipt.result
    | .occurrenceCount => fun receipt => receipt.result.answers.card
    | .executionFace => NativeSearchReceipt.face

/-- The result-only readout supports semantic proof-result policies but not
the operational provenance face that it intentionally forgets. -/
def resultOnlySupports (_ : Unit) : ReceiptPolicy -> Prop
  | .exactResult => True
  | .occurrenceCount => True
  | .executionFace => False

def resultOnlyCatalog {Source Target : Type}
    (relation : ProofRel Source Target) :
    PolicyReadoutCatalog Unit (NativeSearchReceipt relation)
      (receiptPolicies relation) where
  Key := fun _ => FiniteEvidenceProvider.SearchResult relation
  readout := fun _ receipt => receipt.result
  Supports := resultOnlySupports
  runner := by
    intro index policy support
    cases index
    cases policy with
    | exactResult => exact id
    | occurrenceCount => exact fun result => result.answers.card
    | executionFace => exact False.elim support
  agrees := by
    intro index policy support state
    cases index
    cases policy with
    | exactResult => rfl
    | occurrenceCount => rfl
    | executionFace => exact False.elim support
  supports_mono := by
    intro weaker stronger _related policy supported
    cases weaker
    cases stronger
    exact supported

/-- The declared request asks for the complete proof result and its occurrence
count, but not for the intentionally forgotten execution face. -/
def requiredReceiptPolicies : Set ReceiptPolicy :=
  fun policy => policy = .exactResult ∨ policy = .occurrenceCount

/-- Exact finite search plus the two supported receipt policies. -/
noncomputable def receiptRequest {Source Target : Type}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    PolicyCapabilityRequest (resultOnlyCatalog relation)
      (finiteOnlyRequest provider) where
  requiredPolicies := requiredReceiptPolicies
  candidates := {()}
  candidates_exact := by
    intro candidate
    cases candidate
    constructor
    · intro _member
      constructor
      · simp [finiteOnlyRequest]
      · intro policy required
        rcases required with left | right
        · subst policy
          trivial
        · subst policy
          trivial
    · intro _data
      simp
  candidates_nonempty := ⟨(), by simp⟩

/-- The singleton exact fibre has a genuinely strongest member. -/
noncomputable def receiptSelection {Source Target : Type}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    (receiptRequest provider).toCapabilityRequest.StrongestNativeCalculusPrinciple where
  val := ()
  property := by
    constructor
    · change () ∈ (receiptRequest provider).candidates
      simp [receiptRequest]
    · intro candidate _member
      cases candidate
      exact le_rfl

/-- Retain the checked finite-search operation and its exact result policies
at one dependency revision. -/
noncomputable def selectedAt {Source Target : Type}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    SelectedPolicyAdmissionAt (receiptRequest provider) dependencies revision :=
  SelectedPolicyAdmissionAt.ofStrongest (receiptRequest provider)
    (receiptSelection provider) dependencies revision

def exactResultPolicy {Source Target : Type}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    (receiptRequest provider).requestedFamily.Policy :=
  ⟨.exactResult, Or.inl rfl⟩

def occurrenceCountPolicy {Source Target : Type}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    (receiptRequest provider).requestedFamily.Policy :=
  ⟨.occurrenceCount, Or.inr rfl⟩

/-- Run the selected native operation once and apply one retained policy to
that same result. -/
noncomputable def runObserved {Source Target : Type}
    {relation : ProofRel Source Target}
    {provider : FiniteEvidenceProvider relation}
    {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {selected : SelectedPolicyAdmissionAt
      (receiptRequest provider) dependencies revision}
    (active : selected.Active currentRevision)
    (input : Source)
    (policy : (receiptRequest provider).requestedFamily.Policy) :
    NativeSearchReceipt relation ×
      (receiptRequest provider).requestedFamily.Result policy :=
  let receipt : NativeSearchReceipt relation := active.run input
  (receipt,
    active.policyActive.runKey policy
      ((resultOnlyCatalog relation).readout selected.candidate receipt))

/-- Native execution and policy evaluation agree with the original selected
operation and the declared policy on its exact result. -/
@[simp] theorem runObserved_eq {Source Target : Type}
    {relation : ProofRel Source Target}
    {provider : FiniteEvidenceProvider relation}
    {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {selected : SelectedPolicyAdmissionAt
      (receiptRequest provider) dependencies revision}
    (active : selected.Active currentRevision)
    (input : Source)
    (policy : (receiptRequest provider).requestedFamily.Policy) :
    runObserved active input policy =
      let receipt : NativeSearchReceipt relation := selected.operation.run input
      (receipt,
        (receiptRequest provider).requestedFamily.decide policy receipt) := by
  simp [runObserved]

/-- Once the checked program has constructed its native provider and NIK has
selected the operation, the hot path is the existing certificate-free
`admittedFlow` entry mode.  The raw checker remains an ingress boundary rather
than an interior execution regime. -/
noncomputable def admittedFlowMode {Source Target : Type}
    {relation : ProofRel Source Target}
    {provider : FiniteEvidenceProvider relation}
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    (selected : SelectedPolicyAdmissionAt
      (receiptRequest provider) dependencies revision) :
    EntryMode (NativeSearchReceipt relation) :=
  .admittedFlow (queryObject Source)
    (fun receipt => RelationalEvidence.AnswerBag.Complete receipt.result.answers)
    selected.operation

@[simp] theorem admittedFlowMode_certificateFree {Source Target : Type}
    {relation : ProofRel Source Target}
    {provider : FiniteEvidenceProvider relation}
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    (selected : SelectedPolicyAdmissionAt
      (receiptRequest provider) dependencies revision) :
    EntryMode.requiresCertificate (admittedFlowMode selected) = false :=
  rfl

/-- Current selected execution is accepted by that admitted-flow meaning using
the preservation proof retained in the selected native operation. -/
theorem currentRun_acceptedByAdmittedFlow {Source Target : Type}
    {relation : ProofRel Source Target}
    {provider : FiniteEvidenceProvider relation}
    {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {selected : SelectedPolicyAdmissionAt
      (receiptRequest provider) dependencies revision}
    (active : selected.Active currentRevision) (input : Source) :
    EntryMode.Accepted (admittedFlowMode selected) (active.run input) :=
  active.run_preserves input trivial

/-- The result-only readout cannot realize the larger family containing the
face-sensitive policy.  Two receipts with the same proof result but different
native faces are its separating collision. -/
theorem resultOnlyReadout_refuses_fullFamily {Source Target : Type}
    (relation : ProofRel Source Target)
    (result : FiniteEvidenceProvider.SearchResult relation) :
    Not ((receiptPolicies relation).SupportsReadout
      (fun receipt : NativeSearchReceipt relation => receipt.result)) := by
  apply (receiptPolicies relation).not_supportsReadout_of_policy_collision
    (fun receipt : NativeSearchReceipt relation => receipt.result)
    (first := ⟨.finiteSearch, result⟩)
    (second := ⟨.directMap, result⟩)
    rfl .executionFace
  intro equal
  cases equal

/-! ## The checked grandparent chain -/

namespace GrandparentCanary

open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedChain
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedNativePrograms

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

noncomputable def selected :=
  selectedAt grandparentPlan.provider dependencies false

noncomputable def active : selected.Active false :=
  selected.activate (dependencies.sameDependencies_refl false)

noncomputable def exactPolicy :
    (receiptRequest grandparentPlan.provider).requestedFamily.Policy :=
  exactResultPolicy grandparentPlan.provider

noncomputable def countPolicy :
    (receiptRequest grandparentPlan.provider).requestedFamily.Policy :=
  occurrenceCountPolicy grandparentPlan.provider

noncomputable def exactObservation :=
  runObserved active alice exactPolicy

noncomputable def countObservation :=
  runObserved active alice countPolicy

/-- The selected face is exact finite search: the checked chain does not mint
a functional representation that its primitive capabilities did not supply. -/
theorem current_selection_runs_finite_search :
    exactObservation.1.face = .finiteSearch :=
  rfl

/-- After raw ingress, the selected search is an accepted certificate-free
admitted flow rather than repeated generic checking. -/
theorem current_selection_uses_admitted_flow :
    EntryMode.requiresCertificate (admittedFlowMode selected) = false ∧
      EntryMode.Accepted (admittedFlowMode selected)
        (active.run alice) :=
  ⟨rfl, currentRun_acceptedByAdmittedFlow active alice⟩

/-- The exact-result policy returns the very proof-relevant result emitted by
the selected native operation, not a support or endpoint projection. -/
theorem current_result_policy_is_exact :
    exactObservation.2 = exactObservation.1.result :=
  rfl

/-- The checked occurrence, including its chain derivation, survives in the
current policy result. -/
theorem current_policy_retains_checked_occurrence :
    let occurrence : RelationalEvidence.AnswerOccurrence
        grandparentPlan.checked.toChecked.intrinsicProgram.denotation alice :=
      ⟨carol, grandparentPlan.checked.toChecked.nativeEvidence⟩
    occurrence ∈ exactObservation.2.answers := by
  intro occurrence
  change occurrence ∈ grandparentPlan.provider.answers alice
  exact grandparentPlan.checked_evidence_occurs

/-- The derived count agrees with the cardinality of the exact occurrence
bag; it is an observation of that bag, not its replacement. -/
theorem current_count_is_valuation_of_exact_result :
    countObservation.2 = exactObservation.2.answers.card :=
  rfl

noncomputable def prepared : selected.Prepared :=
  selected.prepare alice (selected.operation.run alice)

theorem changed_revision_is_stale : selected.StaleAt true := by
  intro same
  have impossible := same ()
  simp [dependencies] at impossible

/-- A relevant change disables native search and its policies together while
retaining the raw query and complete search receipt for fallback. -/
theorem changed_revision_refuses_selection_and_preserves_fallback :
    (Not (selected.Active true)) ∧
      prepared.fallback = (alice, selected.operation.run alice) :=
  selected.stale_prevents_activation_and_preserves_fallback
    changed_revision_is_stale prepared

/-- The same result-only key cannot be silently widened to observe operational
face provenance. -/
theorem result_key_does_not_support_execution_face :
    Not ((receiptPolicies
      grandparentPlan.checked.toChecked.intrinsicProgram.denotation).SupportsReadout
        (fun receipt => receipt.result)) :=
  resultOnlyReadout_refuses_fullFamily _ (grandparentPlan.run alice)

/-- An ill-shared chain cannot construct the checked native plan required by
the selected policy admission.  Native capability never repairs bad typing. -/
theorem wrong_middle_never_reaches_policy_selection :
    Not (Exists fun plan : NativeSearchPlan FormedQuotationCanary.quotation
      alice bob wrongMiddleProof =>
        Nonempty
          (SelectedPolicyAdmissionAt (receiptRequest plan.provider)
            dependencies false)) := by
  rintro ⟨plan, _selection⟩
  exact wrong_middle_has_no_native_search_plan ⟨plan⟩

end GrandparentCanary

/-! ## The checked strictly-positive List relator -/

namespace MapRelCanary

open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedNativeListPrograms
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedNativeListSearch

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

noncomputable def selected :=
  selectedAt singletonPlan.provider dependencies false

noncomputable def active : selected.Active false :=
  selected.activate (dependencies.sameDependencies_refl false)

noncomputable def exactPolicy :
    (receiptRequest singletonPlan.provider).requestedFamily.Policy :=
  exactResultPolicy singletonPlan.provider

noncomputable def countPolicy :
    (receiptRequest singletonPlan.provider).requestedFamily.Policy :=
  occurrenceCountPolicy singletonPlan.provider

noncomputable def exactObservation :=
  runObserved active singletonPlan.sourceList exactPolicy

noncomputable def countObservation :=
  runObserved active singletonPlan.sourceList countPolicy

/-- The generic selected-current path also consumes a checked native
strictly-positive `mapRel` plan without adding a List-specific NIK face. -/
theorem current_selection_runs_native_mapRel :
    exactObservation.1.face = .finiteSearch ∧
      RelationalEvidence.AnswerBag.Complete exactObservation.2.answers := by
  constructor
  · rfl
  · change RelationalEvidence.AnswerBag.Complete
      (singletonPlan.provider.run singletonPlan.sourceList).answers
    exact singletonPlan.run_complete singletonPlan.sourceList

/-- The checked native relator likewise crosses into the certificate-free
admitted-flow mode after its one ingress check. -/
theorem current_mapRel_uses_admitted_flow :
    EntryMode.requiresCertificate (admittedFlowMode selected) = false ∧
      EntryMode.Accepted (admittedFlowMode selected)
        (active.run singletonPlan.sourceList) :=
  ⟨rfl, currentRun_acceptedByAdmittedFlow active singletonPlan.sourceList⟩

/-- The checked head and recursive-tail derivations survive as one exact
occurrence in the requested proof result. -/
theorem current_policy_retains_checked_mapRel_occurrence :
    singletonPlan.checkedOccurrence ∈ exactObservation.2.answers := by
  change singletonPlan.checkedOccurrence ∈
    singletonPlan.provider.answers singletonPlan.sourceList
  exact singletonPlan.checked_evidence_occurs

/-- Occurrence counting remains a valuation of the complete dependent bag. -/
theorem current_count_is_valuation_of_exact_mapRel_result :
    countObservation.2 = exactObservation.2.answers.card :=
  rfl

noncomputable def prepared : selected.Prepared :=
  selected.prepare singletonPlan.sourceList
    (selected.operation.run singletonPlan.sourceList)

theorem changed_revision_is_stale : selected.StaleAt true := by
  intro same
  have impossible := same ()
  simp [dependencies] at impossible

/-- Staleness refuses both the native relator and its observation runners,
while preserving the exact intrinsic List input and complete result. -/
theorem changed_revision_refuses_mapRel_and_preserves_fallback :
    (Not (selected.Active true)) ∧
      prepared.fallback =
        (singletonPlan.sourceList,
          selected.operation.run singletonPlan.sourceList) :=
  selected.stale_prevents_activation_and_preserves_fallback
    changed_revision_is_stale prepared

/-- A missing recursive tail cannot cross the checker/native-family waist and
therefore cannot be upgraded merely because `List.mapRel` has a provider. -/
theorem missing_tail_never_reaches_policy_selection :
    Not (Exists fun plan : NativeMapSearchPlan singletonSource singletonTarget
      missingTailProof =>
        Nonempty
          (SelectedPolicyAdmissionAt (receiptRequest plan.provider)
            dependencies false)) := by
  rintro ⟨plan, _selection⟩
  exact missing_tail_has_no_native_search_plan ⟨plan⟩

end MapRelCanary

#print axioms runObserved_eq
#print axioms resultOnlyReadout_refuses_fullFamily
#print axioms admittedFlowMode_certificateFree
#print axioms currentRun_acceptedByAdmittedFlow
#print axioms GrandparentCanary.current_selection_runs_finite_search
#print axioms GrandparentCanary.current_selection_uses_admitted_flow
#print axioms GrandparentCanary.current_result_policy_is_exact
#print axioms GrandparentCanary.current_policy_retains_checked_occurrence
#print axioms GrandparentCanary.current_count_is_valuation_of_exact_result
#print axioms GrandparentCanary.changed_revision_refuses_selection_and_preserves_fallback
#print axioms GrandparentCanary.result_key_does_not_support_execution_face
#print axioms GrandparentCanary.wrong_middle_never_reaches_policy_selection
#print axioms MapRelCanary.current_selection_runs_native_mapRel
#print axioms MapRelCanary.current_mapRel_uses_admitted_flow
#print axioms MapRelCanary.current_policy_retains_checked_mapRel_occurrence
#print axioms MapRelCanary.current_count_is_valuation_of_exact_mapRel_result
#print axioms MapRelCanary.changed_revision_refuses_mapRel_and_preserves_fallback
#print axioms MapRelCanary.missing_tail_never_reaches_policy_selection

end Mettapedia.Languages.MeTTa.Prime.NativeCheckedHypothesisPolicyNIKSelection
