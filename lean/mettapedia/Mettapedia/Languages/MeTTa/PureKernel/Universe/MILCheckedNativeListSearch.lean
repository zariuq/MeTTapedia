import Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicMILNativeListSearch
import Mettapedia.Languages.MeTTa.PureKernel.Universe.MILCheckedNativeListPresentation

/-!
# Checked List-relator programs as exact native searches

The generic inference checker, the intrinsic strictly-positive `List.mapRel`
family, and exact finite native search meet here without becoming one
authority.  A raw proof is checked once and interpreted as an independent
proof-relevant List spine.  Its intrinsic image retains native typing, while
the structurally derived provider enumerates the complete semantic occurrence
fibre without replaying the checker.

The authored endpoint syntax, exact raw proof, intrinsic term, and returned
semantic evidence remain separately inspectable.  A missing recursive premise
cannot construct the plan.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace MILCheckedNativeListSearch

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.IndexedPolynomial
open RelationalEvidence
open IntrinsicMILNativeSearch
open IntrinsicMILNativeListSearch
open MILCheckedNativeListPresentation

abbrev RawInferenceProof :=
  Mettapedia.GSLT.LanguageDef.InferenceChecker.RawProof

/-! ## Exact primitive and lifted providers -/

/-- The independently interpreted successor relation as a Prime semantic
relation over authored Pattern endpoints. -/
def successorRelation : IntrinsicMILNativeSearch.ProofRel Pattern Pattern where
  evidence source target := Step successor source target

private theorem successorOccurrence_subsingleton (source : Pattern) :
    Subsingleton (AnswerOccurrence successorRelation source) := by
  constructor
  rintro ⟨firstTarget, firstEvidence⟩ ⟨secondTarget, secondEvidence⟩
  cases firstEvidence
  cases secondEvidence
  rfl

/-- Every source has an exact finite successor fibre: it is empty away from
`one` and contains the unique `two` occurrence at `one`. -/
noncomputable def successorProvider :
    FiniteEvidenceProvider successorRelation where
  fibre := fun source => by
    letI : Subsingleton (AnswerOccurrence successorRelation source) :=
      successorOccurrence_subsingleton source
    letI : Finite (AnswerOccurrence successorRelation source) :=
      Finite.of_injective (fun _ => PUnit.unit)
        (fun _ _ _ => Subsingleton.elim _ _)
    exact
      { Index := AnswerOccurrence successorRelation source
        indexFintype := Fintype.ofFinite _
        occurrenceEquiv := Equiv.refl _ }

/-- The native List provider is derived from the general strictly-positive
lifting theorem, not implemented as a second recursive evaluator. -/
noncomputable def successorListProvider :
    FiniteEvidenceProvider
      (NativeIndexedFamilies.Semantic.mapRel successorRelation) :=
  mapRelProvider successorProvider

/-! ## Exact authored-to-polynomial evidence transport -/

/-- Re-encode one ordinary element spine in the checked presentation's
authored List syntax. -/
def encodeAuthoredList : List Pattern → Pattern
  | [] => MILCheckedNativeListPresentation.nil
  | head :: tail => MILCheckedNativeListPresentation.cons head
      (encodeAuthoredList tail)

/-- Recover the source element spine from the proof-relevant checked
successor lifting. -/
def sourceSpine : {sources targets : Pattern} →
    ListStep successor sources targets → List Pattern
  | _, _, .nil => []
  | _, _, .cons head tail => by
      cases head
      exact one :: sourceSpine tail

/-- Recover the target element spine without forgetting the checked head
relation witnesses. -/
def targetSpine : {sources targets : Pattern} →
    ListStep successor sources targets → List Pattern
  | _, _, .nil => []
  | _, _, .cons head tail => by
      cases head
      exact two :: targetSpine tail

/-- The checked evidence spine is the same proof-relevant List relator used
by the native polynomial semantics. -/
def ordinaryEvidence : {sources targets : Pattern} →
    (evidence : ListStep successor sources targets) →
      ListExample.ListRel successorRelation.evidence
        (sourceSpine evidence) (targetSpine evidence)
  | _, _, .nil => .nil
  | _, _, .cons head tail => by
      cases head
      exact .cons Step.successor (ordinaryEvidence tail)

/-- Transport the checked evidence into the native polynomial List fibre. -/
noncomputable def polynomialEvidence {sources targets : Pattern}
    (evidence : ListStep successor sources targets) :
    (NativeIndexedFamilies.Semantic.mapRel successorRelation).evidence
      (ListExample.ofList (sourceSpine evidence))
      (ListExample.ofList (targetSpine evidence)) := by
  change ListExample.ListRel successorRelation.evidence
    (ListExample.toList (ListExample.ofList (sourceSpine evidence)))
    (ListExample.toList (ListExample.ofList (targetSpine evidence)))
  simpa using ordinaryEvidence evidence

/-- The recovered source spine encodes to exactly the authored source index. -/
theorem encode_sourceSpine {sources targets : Pattern}
    (evidence : ListStep successor sources targets) :
    encodeAuthoredList (sourceSpine evidence) = sources := by
  induction evidence with
  | nil => rfl
  | cons head tail hypothesis =>
      cases head
      simp [sourceSpine, encodeAuthoredList, hypothesis]

/-- The recovered target spine encodes to exactly the authored target index. -/
theorem encode_targetSpine {sources targets : Pattern}
    (evidence : ListStep successor sources targets) :
    encodeAuthoredList (targetSpine evidence) = targets := by
  induction evidence with
  | nil => rfl
  | cons head tail hypothesis =>
      cases head
      simp [targetSpine, encodeAuthoredList, hypothesis]

/-! ## Checked native-search plans -/

/-- A boundary plan retains the exact checked raw proof and the generic
native provider. -/
structure NativeMapSearchPlan
    (sources targets : Pattern) (raw : RawInferenceProof) where
  checked : CheckedRawNativeMapProgram sources targets raw
  provider : FiniteEvidenceProvider
    (NativeIndexedFamilies.Semantic.mapRel successorRelation)

namespace NativeMapSearchPlan

noncomputable def semanticEvidence {sources targets : Pattern}
    {raw : RawInferenceProof}
    (plan : NativeMapSearchPlan sources targets raw) :
    ListStep successor sources targets :=
  plan.checked.toChecked.semanticEvidence

noncomputable def sourceList {sources targets : Pattern}
    {raw : RawInferenceProof}
    (plan : NativeMapSearchPlan sources targets raw) :
    NativeIndexedFamilies.Semantic.List Pattern :=
  ListExample.ofList (sourceSpine plan.semanticEvidence)

noncomputable def targetList {sources targets : Pattern}
    {raw : RawInferenceProof}
    (plan : NativeMapSearchPlan sources targets raw) :
    NativeIndexedFamilies.Semantic.List Pattern :=
  ListExample.ofList (targetSpine plan.semanticEvidence)

/-- The exact semantic occurrence obtained from the checked derivation. -/
noncomputable def checkedOccurrence
    {sources targets : Pattern} {raw : RawInferenceProof}
    (plan : NativeMapSearchPlan sources targets raw) :
    AnswerOccurrence
      (NativeIndexedFamilies.Semantic.mapRel successorRelation)
      plan.sourceList :=
  ⟨plan.targetList, polynomialEvidence plan.semanticEvidence⟩

/-- Hot execution consumes only the constructed provider. -/
noncomputable def run {sources targets : Pattern} {raw : RawInferenceProof}
    (plan : NativeMapSearchPlan sources targets raw)
    (input : NativeIndexedFamilies.Semantic.List Pattern) :
    FiniteEvidenceProvider.SearchResult
      (NativeIndexedFamilies.Semantic.mapRel successorRelation) :=
  plan.provider.run input

theorem run_complete {sources targets : Pattern} {raw : RawInferenceProof}
    (plan : NativeMapSearchPlan sources targets raw)
    (input : NativeIndexedFamilies.Semantic.List Pattern) :
    AnswerBag.Complete (plan.run input).answers :=
  plan.provider.run_complete input

/-- The exact checked semantic derivation occurs in the native answer bag;
endpoint support alone is not the acceptance criterion. -/
theorem checked_evidence_occurs
    {sources targets : Pattern} {raw : RawInferenceProof}
    (plan : NativeMapSearchPlan sources targets raw) :
    plan.checkedOccurrence ∈ (plan.run plan.sourceList).answers := by
  change plan.checkedOccurrence ∈ plan.provider.answers plan.sourceList
  exact (plan.provider.fibre plan.sourceList).mem_answers
    plan.checkedOccurrence

/-- All four layers remain inspectable: raw proof identity, authored endpoint
indices, and intrinsic native typing. -/
theorem retains_raw_endpoints_and_native_typing
    {sources targets : Pattern} {raw : RawInferenceProof}
    (plan : NativeMapSearchPlan sources targets raw) :
    plan.checked.checked.erase = raw ∧
      encodeAuthoredList (sourceSpine plan.semanticEvidence) = sources ∧
      encodeAuthoredList (targetSpine plan.semanticEvidence) = targets ∧
      NativeCanary.NativeHasType NativeCanary.contextABRSourceTargetEdge
        plan.checked.toChecked.nativeTerm.code
        plan.checked.toChecked.nativeImage.typeOver.code :=
  ⟨plan.checked.erases,
    encode_sourceSpine plan.semanticEvidence,
    encode_targetSpine plan.semanticEvidence,
    plan.checked.toChecked.nativeTerm.typed⟩

end NativeMapSearchPlan

/-- Successful generic checking constructs the native List-search plan once
at ingress. -/
noncomputable def planOfAccepted
    (sources targets : Pattern) (raw : RawInferenceProof)
    (accepted : Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw
      learned.target (mapRel successor sources targets) raw = true) :
    NativeMapSearchPlan sources targets raw := by
  let checked := Classical.choice
    ((checkedRaw_iff_nonempty_native sources targets raw).mp accepted)
  exact ⟨checked, successorListProvider⟩

noncomputable def singletonPlan :
    NativeMapSearchPlan singletonSource singletonTarget singletonMapProof :=
  ⟨singletonNative, successorListProvider⟩

/-- The recursive positive witness crosses checking, intrinsic typing, exact
authored indices, and complete native search while retaining its checked
semantic occurrence. -/
theorem singleton_checked_typed_complete_and_occurrence_retaining :
    singletonPlan.checked.checked.erase = singletonMapProof ∧
      encodeAuthoredList
        (sourceSpine singletonPlan.semanticEvidence) = singletonSource ∧
      encodeAuthoredList
        (targetSpine singletonPlan.semanticEvidence) = singletonTarget ∧
      NativeCanary.NativeHasType NativeCanary.contextABRSourceTargetEdge
        singletonPlan.checked.toChecked.nativeTerm.code
        singletonPlan.checked.toChecked.nativeImage.typeOver.code ∧
      AnswerBag.Complete
        (singletonPlan.run singletonPlan.sourceList).answers ∧
      singletonPlan.checkedOccurrence ∈
        (singletonPlan.run singletonPlan.sourceList).answers := by
  rcases singletonPlan.retains_raw_endpoints_and_native_typing with
    ⟨raw, source, target, typed⟩
  exact ⟨raw, source, target, typed,
    singletonPlan.run_complete singletonPlan.sourceList,
    singletonPlan.checked_evidence_occurs⟩

/-- A proof missing its recursive child cannot cross ingress and therefore
cannot receive the otherwise valid native List capability. -/
theorem missing_tail_has_no_native_search_plan :
    ¬ Nonempty
      (NativeMapSearchPlan singletonSource singletonTarget missingTailProof) := by
  rintro ⟨plan⟩
  exact missing_tail_has_no_native_program ⟨plan.checked⟩

#print axioms successorProvider
#print axioms ordinaryEvidence
#print axioms polynomialEvidence
#print axioms NativeMapSearchPlan.run_complete
#print axioms NativeMapSearchPlan.checked_evidence_occurs
#print axioms planOfAccepted
#print axioms singleton_checked_typed_complete_and_occurrence_retaining
#print axioms missing_tail_has_no_native_search_plan

end MILCheckedNativeListSearch
end Mettapedia.Languages.MeTTa.PureKernel.Universe
