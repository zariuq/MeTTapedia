import Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedNativeListSearch

/-!
# Request-local NIK selection for proof-relevant native search

Direct functional realization and exact finite proof search are comparable
only after they are placed over one semantic contract.  Here that contract is
a typed query mapped to a complete bag of target/derivation occurrences.

For a represented relation, NIK recognizes both a finite-search face and a
direct-map face.  The direct face supports every finite-search capability plus
the additional functional-representation capability, so it is the unique
strongest member of the exact request fibre.  For a finite nondeterministic
relation, the one-face family exposes complete search without inventing
functionality.  Relations without finite evidence fibres remain in the
ambient relational semantics and do not enter this finite-result fibre.

Selections are stored through the common revision-indexed admission bridge.
Current activation runs only the selected operation; relevant dependency
changes prevent reuse.  A checked List-relator plan retains its raw and
intrinsic evidence separately while its finite provider enters this selection
calculus.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeRelationalSearchNIKSelection

open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RelationalInternalLanguage.Semantic
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicMILNativeSearch
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicMILNativeListSearch
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

/-! ## One exact finite-result contract -/

inductive SearchFace where
  | finiteSearch
  | directMap
  deriving DecidableEq, Repr

def SearchFace.le : SearchFace → SearchFace → Prop
  | .finiteSearch, _ => True
  | .directMap, .directMap => True
  | .directMap, .finiteSearch => False

instance : PartialOrder SearchFace where
  le := SearchFace.le
  le_refl := by
    intro face
    cases face <;> trivial
  le_trans := by
    intro first middle last firstMiddle middleLast
    cases first <;> cases middle <;> cases last <;>
      simp_all [SearchFace.le]
  le_antisymm := by
    intro first second firstSecond secondFirst
    cases first <;> cases second <;> simp_all [SearchFace.le]

inductive SearchCapability where
  | exactEvidenceFibre
  | certificateFree
  | functionalRepresentation
  deriving DecidableEq, Repr

def supports : SearchFace → SearchCapability → Prop
  | _, .exactEvidenceFibre => True
  | _, .certificateFree => True
  | .directMap, .functionalRepresentation => True
  | .finiteSearch, .functionalRepresentation => False

/-- The native result records its operational face without changing the
proof-relevant semantic result. -/
structure NativeSearchReceipt {Source Target : Type u}
    (relation : ProofRel Source Target) where
  face : SearchFace
  result : FiniteEvidenceProvider.SearchResult relation

def queryObject (Source : Type u) : AdmissionObject.{u} where
  Carrier := Source
  Meaning := fun _ => True

/-- The shared target fibre asks only for exact completeness.  Functionality
is an additional capability of an implementation, not a different truth
condition. -/
def completeResultObject {Source Target : Type u}
    (relation : ProofRel Source Target) : AdmissionObject.{u} where
  Carrier := NativeSearchReceipt relation
  Meaning := fun receipt =>
    RelationalEvidence.AnswerBag.Complete receipt.result.answers

noncomputable def finiteSearchOperation {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    queryObject Source ⟶ completeResultObject relation where
  run := fun source => ⟨.finiteSearch, provider.run source⟩
  preserves := fun source _ => provider.run_complete source

noncomputable def directMapOperation {Source Target : Type u}
    {relation : ProofRel Source Target}
    (representation : Rel.Representation relation) :
    queryObject Source ⟶ completeResultObject relation where
  run := fun source =>
    ⟨.directMap,
      (FiniteEvidenceProvider.ofRepresentation representation).run source⟩
  preserves := fun source _ =>
    (FiniteEvidenceProvider.ofRepresentation representation).run_complete source

@[simp] theorem finiteSearchOperation_face {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) (source : Source) :
    ((finiteSearchOperation provider).run source).face = .finiteSearch :=
  rfl

@[simp] theorem directMapOperation_face {Source Target : Type u}
    {relation : ProofRel Source Target}
    (representation : Rel.Representation relation) (source : Source) :
    ((directMapOperation representation).run source).face = .directMap :=
  rfl

/-! ## Represented relations: direct map is request-locally strongest -/

noncomputable def representedFamily {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (representation : Rel.Representation relation) :
    RecognizedFamily SearchFace (queryObject Source)
      (completeResultObject relation) where
  package
    | .finiteSearch => finiteSearchOperation provider
    | .directMap => directMapOperation representation
  Capability := SearchCapability
  supports := supports
  supports_mono := by
    intro weaker stronger related capability supported
    cases weaker with
    | finiteSearch =>
        cases stronger with
        | finiteSearch => exact supported
        | directMap =>
            cases capability <;> trivial
    | directMap =>
        cases stronger with
        | finiteSearch =>
            change False at related
            exact related.elim
        | directMap => exact supported
  strict_support_gain := by
    intro weaker stronger strict
    cases weaker with
    | finiteSearch =>
        cases stronger with
        | finiteSearch => exact (lt_irrefl _ strict).elim
        | directMap =>
            exact ⟨.functionalRepresentation, trivial, by
              simp [supports]⟩
    | directMap =>
        cases stronger with
        | finiteSearch =>
            have impossible := strict.le
            change False at impossible
            exact impossible.elim
        | directMap => exact (lt_irrefl _ strict).elim
  recognized := {.finiteSearch, .directMap}
  licensed := {.finiteSearch, .directMap}
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := ⟨.finiteSearch, by simp⟩

theorem represented_order_iff_capability_inclusion
    {Source Target : Type u} {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (representation : Rel.Representation relation)
    (first second : SearchFace) :
    first ≤ second ↔
      ∀ capability,
        (representedFamily provider representation).supports first capability →
          (representedFamily provider representation).supports second
            capability := by
  constructor
  · exact fun related capability supported =>
      (representedFamily provider representation).supports_mono
        related capability supported
  · intro included
    cases first <;> cases second
    · trivial
    · trivial
    · have impossible := included .functionalRepresentation
      simp [representedFamily, supports] at impossible
    · trivial

theorem representedFamily_directed
    {Source Target : Type u} {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (representation : Rel.Representation relation) :
    (representedFamily provider representation).LicensedDirected := by
  intro first _ second _
  refine ⟨.directMap, by simp [representedFamily], ?_, ?_⟩
  · cases first <;> trivial
  · cases second <;> trivial

def exactSearchCapabilities : Set SearchCapability :=
  fun capability =>
    capability = .exactEvidenceFibre ∨ capability = .certificateFree

def completeSearchRequest
    {Source Target : Type u} {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (representation : Rel.Representation relation) :
    (representedFamily provider representation).CapabilityRequest where
  required := exactSearchCapabilities
  candidates := {.finiteSearch, .directMap}
  candidates_exact := by
    intro candidate
    constructor
    · intro candidateMember
      refine ⟨?_, ?_⟩
      · simpa [representedFamily] using candidateMember
      · intro capability required
        change capability = .exactEvidenceFibre ∨
          capability = .certificateFree at required
        rcases required with rfl | rfl <;> trivial
    · intro candidateData
      simpa [representedFamily] using candidateData.1
  candidates_nonempty := ⟨.finiteSearch, by simp⟩

def directSelection
    {Source Target : Type u} {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (representation : Rel.Representation relation) :
    (completeSearchRequest provider representation).StrongestNativeCalculusPrinciple where
  val := .directMap
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        completeSearchRequest]
    · intro candidate _
      cases candidate <;> trivial

theorem represented_request_uniqueStrongest
    {Source Target : Type u} {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (representation : Rel.Representation relation) :
    ∃! chosen,
      (completeSearchRequest provider representation).restrictedFamily.IsGreatestLicensed
        chosen :=
  (completeSearchRequest provider representation).existsUnique_strongest
    (representedFamily_directed provider representation)

@[simp] theorem represented_selected_face
    {Source Target : Type u} {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (representation : Rel.Representation relation) (source : Source) :
    (((completeSearchRequest provider representation).strongestOperation
      (directSelection provider representation)).run source).face =
        .directMap :=
  rfl

/-! ## Finite nondeterminism: exact search without functionality -/

def finiteOnlySupports (_ : Unit) : SearchCapability → Prop
  | .exactEvidenceFibre => True
  | .certificateFree => True
  | .functionalRepresentation => False

noncomputable def finiteOnlyFamily {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    RecognizedFamily Unit (queryObject Source)
      (completeResultObject relation) where
  package _ := finiteSearchOperation provider
  Capability := SearchCapability
  supports := finiteOnlySupports
  supports_mono := by
    intro weaker stronger _ capability supported
    cases weaker
    cases stronger
    exact supported
  strict_support_gain := by
    intro weaker stronger strict
    cases weaker
    cases stronger
    exact (lt_irrefl () strict).elim
  recognized := {()}
  licensed := {()}
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := ⟨(), by simp⟩

def finiteOnlyRequest {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    (finiteOnlyFamily provider).CapabilityRequest where
  required := exactSearchCapabilities
  candidates := {()}
  candidates_exact := by
    intro candidate
    constructor
    · intro candidateMember
      refine ⟨?_, ?_⟩
      · simp [finiteOnlyFamily]
      · intro capability required
        change capability = .exactEvidenceFibre ∨
          capability = .certificateFree at required
        rcases required with rfl | rfl <;> trivial
    · intro candidateData
      simp
  candidates_nonempty := ⟨(), by simp⟩

def finiteOnlySelection {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    (finiteOnlyRequest provider).StrongestNativeCalculusPrinciple where
  val := ()
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        finiteOnlyRequest]
    · intro candidate _
      cases candidate
      exact le_rfl

theorem finiteOnly_does_not_claim_functionality
    {Source Target : Type u} {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    ¬ (finiteOnlyFamily provider).supports ()
      .functionalRepresentation :=
  by simp [finiteOnlyFamily, finiteOnlySupports]

@[simp] theorem finiteOnly_selected_face
    {Source Target : Type u} {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) (source : Source) :
    (((finiteOnlyRequest provider).strongestOperation
      (finiteOnlySelection provider)).run source).face = .finiteSearch :=
  rfl

/-! ## Revision-current List instances -/

namespace Canary

open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeIndexedFamilies
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedNativeListSearch

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

noncomputable def branchingFamily :=
  finiteOnlyFamily IntrinsicMILNativeListSearch.Canary.branchingListProvider

noncomputable def branchingAdmission :=
  admitStrongestAt branchingFamily
    (finiteOnlyRequest
      IntrinsicMILNativeListSearch.Canary.branchingListProvider)
    (finiteOnlySelection
      IntrinsicMILNativeListSearch.Canary.branchingListProvider)
    dependencies false

noncomputable def activeBranching : branchingAdmission.Active false :=
  branchingAdmission.activate (dependencies.sameDependencies_refl false)

noncomputable def activeBranchingRun :
    Semantic.List Unit →
      NativeSearchReceipt
        (Semantic.mapRel Semantic.branchingRelation) :=
  activeBranching.run

/-- NIK selects the exact finite face for a genuinely nondeterministic native
List relator and preserves both proof occurrences. -/
theorem branching_selection_retains_two_proofs :
    (activeBranchingRun ListExample.singletonUnit).face = .finiteSearch ∧
      (activeBranchingRun ListExample.singletonUnit).result.answers.card = 2 := by
  constructor
  · rfl
  · change
      (IntrinsicMILNativeListSearch.Canary.branchingListProvider.run
        ListExample.singletonUnit).answers.card = 2
    exact
      IntrinsicMILNativeListSearch.Canary.branching_list_search_retains_two_proofs

noncomputable def boolNotElementProvider :
    FiniteEvidenceProvider (Rel.graph Bool.not) :=
  FiniteEvidenceProvider.ofRepresentation (Rel.graphRepresentation Bool.not)

noncomputable def boolNotListProvider :=
  mapRelProvider boolNotElementProvider

noncomputable def boolNotFamily :=
  representedFamily boolNotListProvider
    IntrinsicMILNativeListSearch.Canary.boolNotListRepresentation

noncomputable def boolNotAdmission :=
  admitStrongestAt boolNotFamily
    (completeSearchRequest boolNotListProvider
      IntrinsicMILNativeListSearch.Canary.boolNotListRepresentation)
    (directSelection boolNotListProvider
      IntrinsicMILNativeListSearch.Canary.boolNotListRepresentation)
    dependencies false

noncomputable def activeBoolNot : boolNotAdmission.Active false :=
  boolNotAdmission.activate (dependencies.sameDependencies_refl false)

noncomputable def activeBoolNotRun :
    Semantic.List Bool →
      NativeSearchReceipt
        (Semantic.mapRel (Rel.graph Bool.not)) :=
  activeBoolNot.run

/-- When functional representation is actually available, the same complete
result request selects the stronger direct-map face. -/
theorem represented_selection_runs_direct :
    (activeBoolNotRun (ListExample.ofList [false])).face = .directMap ∧
      RelationalEvidence.AnswerBag.Complete
        (activeBoolNotRun (ListExample.ofList [false])).result.answers := by
  constructor
  · rfl
  · exact boolNotAdmission.refinement.preservesMeaning _ trivial

/-- Relevant revision change prevents reuse rather than falling through to a
different face. -/
theorem changed_revision_prevents_selected_search :
    ¬ Nonempty (boolNotAdmission.Active true) := by
  rintro ⟨active⟩
  have changed := active.current ()
  simp [dependencies] at changed

/-- The checked recursive List proof remains a cold retained receipt while
its provider is selected and run through the common NIK admission path. -/
noncomputable def checkedFamily :=
  finiteOnlyFamily singletonPlan.provider

noncomputable def checkedAdmission :=
  admitStrongestAt checkedFamily
    (finiteOnlyRequest singletonPlan.provider)
    (finiteOnlySelection singletonPlan.provider)
    dependencies false

noncomputable def activeChecked : checkedAdmission.Active false :=
  checkedAdmission.activate (dependencies.sameDependencies_refl false)

noncomputable def activeCheckedRun :
    Semantic.List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      NativeSearchReceipt
        (Semantic.mapRel successorRelation) :=
  activeChecked.run

theorem checked_occurrence_survives_selected_native_run :
    singletonPlan.checkedOccurrence ∈
      (activeCheckedRun singletonPlan.sourceList).result.answers := by
  change singletonPlan.checkedOccurrence ∈
    (singletonPlan.provider.run singletonPlan.sourceList).answers
  exact singletonPlan.checked_evidence_occurs

/-- The infinite singleton List fibre remains outside the finite-result
selection calculus. -/
theorem infinite_list_has_no_finite_selection_capability :
    ¬ Nonempty
      (FiniteEvidenceProvider
        (Semantic.mapRel
          IntrinsicMILNativeSearch.Canary.infinitelyManyProofs)) :=
  IntrinsicMILNativeListSearch.Canary.infinite_element_fibre_has_no_finite_list_provider

end Canary

#print axioms represented_order_iff_capability_inclusion
#print axioms represented_request_uniqueStrongest
#print axioms finiteOnly_does_not_claim_functionality
#print axioms Canary.branching_selection_retains_two_proofs
#print axioms Canary.represented_selection_runs_direct
#print axioms Canary.changed_revision_prevents_selected_search
#print axioms Canary.checked_occurrence_survives_selected_native_run
#print axioms Canary.infinite_list_has_no_finite_selection_capability

end Mettapedia.Languages.MeTTa.Prime.NativeRelationalSearchNIKSelection
