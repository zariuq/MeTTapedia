import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedNativePrograms
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicMILNativeSearch

/-!
# Checked MIL programs as exact native searches

This module composes two already independent boundaries.  A raw proof first
crosses the generic checked-to-native waist and becomes a formed intrinsic
`Hyp` program.  If the program's primitive relations provide exact finite
evidence fibres, native execution then materializes the complete dependent
occurrence bag.  The execution function consumes the constructed program and
its capability; it does not replay the raw proof checker.

The composition is intentionally capability-indexed.  Finite enumeration is
strictly weaker than functional representability, while an infinite fibre
remains a valid relational program without this native-search realization.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILCheckedNativeSearch

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open IntrinsicMILNativeSearch
open MILCheckedNativePrograms
open MILLearnedProofRelevantAdmission
open RelationalEvidence
open Presentation

/-! ## The checked-to-native-search composition -/

/-- Exact finite search for the intrinsic program constructed from a checked
MIL derivation. -/
abbrev CheckedFiniteSearchProvider
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern}
    (program : CheckedNativeProgram quotation source target) :=
  ProgramFiniteSearchProvider program.intrinsicProgram

/-- Primitive capabilities derive a complete search provider structurally
from the checked program.  No MIL-specific evaluator is introduced. -/
noncomputable def deriveCheckedFiniteSearchProvider
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern}
    (primitiveProviders :
      PrimitiveFiniteSearchProviders
        MILLearnedProofRelevantAdmission.vocabulary)
    (program : CheckedNativeProgram quotation source target) :
    CheckedFiniteSearchProvider program :=
  programFiniteSearchProvider primitiveProviders program.intrinsicProgram

/-- A plan is constructed at the raw boundary and retains the exact checked
proof together with the native capability derived for its intrinsic image. -/
structure NativeSearchPlan
    {context : Tower.Ctx n} (quotation : HostedQuotation context)
    (source target : Pattern) (raw : RawProof) where
  checked : CheckedRawNativeProgram quotation source target raw
  provider : CheckedFiniteSearchProvider checked.toChecked

namespace NativeSearchPlan

/-- Hot native execution consumes only the already-constructed plan and the
typed source query. -/
noncomputable def run
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern} {raw : RawProof}
    (plan : NativeSearchPlan quotation source target raw) (input : Pattern) :
    FiniteEvidenceProvider.SearchResult
      plan.checked.toChecked.intrinsicProgram.denotation :=
  plan.provider.run input

@[simp] theorem run_source
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern} {raw : RawProof}
    (plan : NativeSearchPlan quotation source target raw) (input : Pattern) :
    (plan.run input).source = input :=
  rfl

/-- Native execution enumerates every target/derivation occurrence of the
same proof-relevant relation denoted by the checked intrinsic program. -/
theorem run_complete
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern} {raw : RawProof}
    (plan : NativeSearchPlan quotation source target raw) (input : Pattern) :
    AnswerBag.Complete (plan.run input).answers :=
  plan.provider.run_complete input

/-- The exact evidence obtained from the checked derivation itself occurs in
the native result bag.  Hence execution cannot retain only endpoint support
while dropping the checked proof occurrence. -/
theorem checked_evidence_occurs
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern} {raw : RawProof}
    (plan : NativeSearchPlan quotation source target raw) :
    let occurrence : AnswerOccurrence
        plan.checked.toChecked.intrinsicProgram.denotation source :=
      ⟨target, plan.checked.toChecked.nativeEvidence⟩
    occurrence ∈ (plan.run source).answers := by
  intro occurrence
  change occurrence ∈ plan.provider.answers source
  exact (plan.provider.fibre source).mem_answers occurrence

/-- The boundary proof and intrinsic typing derivation remain available as
construction receipts, while `run` itself is exactly the selected provider
operation. -/
theorem retains_raw_and_native_typing
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern} {raw : RawProof}
    (plan : NativeSearchPlan quotation source target raw) :
    plan.checked.checked.erase = raw ∧
      IntrinsicMILHypothesis.HasType context
        plan.checked.toChecked.nativeTerm.code
        (quotation.hypothesisType () ()).code :=
  ⟨plan.checked.erases, plan.checked.toChecked.nativeTerm.typed⟩

end NativeSearchPlan

/-- A successfully checked raw proof and primitive finite capabilities
construct a native-search plan once, at the boundary. -/
noncomputable def planOfAccepted
    {context : Tower.Ctx n} (quotation : HostedQuotation context)
    (primitiveProviders :
      PrimitiveFiniteSearchProviders
        MILLearnedProofRelevantAdmission.vocabulary)
    (source target : Pattern) (raw : RawProof)
    (accepted : Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw
        MILCheckedChain.learned.target (MILCheckedChain.relates source target)
        raw = true) :
    NativeSearchPlan quotation source target raw := by
  let checked := Classical.choice
    ((checkedRaw_iff_nonempty_native quotation source target raw).mp accepted)
  exact
    { checked := checked
      provider := deriveCheckedFiniteSearchProvider primitiveProviders
        checked.toChecked }

/-- Raw checking is a boundary constructor, not an interior execution mode:
after admission, the plan's run is the derived native provider verbatim. -/
@[simp] theorem planOfAccepted_run
    {context : Tower.Ctx n} (quotation : HostedQuotation context)
    (primitiveProviders :
      PrimitiveFiniteSearchProviders
        MILLearnedProofRelevantAdmission.vocabulary)
    (source target : Pattern) (raw : RawProof)
    (accepted : Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw
        MILCheckedChain.learned.target (MILCheckedChain.relates source target)
        raw = true)
    (input : Pattern) :
    (planOfAccepted quotation primitiveProviders source target raw accepted).run
        input =
      (planOfAccepted quotation primitiveProviders source target raw accepted).provider.run
        input :=
  rfl

/-! ## Learned grandparent capabilities -/

private theorem motherOccurrence_subsingleton (source : Pattern) :
    Subsingleton
      (AnswerOccurrence
        (MILLearnedProofRelevantAdmission.vocabulary.meaning Primitive.mother)
        source) := by
  constructor
  rintro ⟨leftTarget, leftEvidence⟩ ⟨rightTarget, rightEvidence⟩
  cases leftEvidence
  cases rightEvidence
  rfl

private theorem fatherOccurrence_subsingleton (source : Pattern) :
    Subsingleton
      (AnswerOccurrence
        (MILLearnedProofRelevantAdmission.vocabulary.meaning Primitive.father)
        source) := by
  constructor
  rintro ⟨leftTarget, leftEvidence⟩ ⟨rightTarget, rightEvidence⟩
  cases leftEvidence
  cases rightEvidence
  rfl

noncomputable def motherProvider :
    FiniteEvidenceProvider
      (MILLearnedProofRelevantAdmission.vocabulary.meaning Primitive.mother) where
  fibre := fun source => by
    letI : Subsingleton
        (AnswerOccurrence
          (MILLearnedProofRelevantAdmission.vocabulary.meaning Primitive.mother)
          source) := motherOccurrence_subsingleton source
    letI : Finite
        (AnswerOccurrence
          (MILLearnedProofRelevantAdmission.vocabulary.meaning Primitive.mother)
          source) :=
      Finite.of_injective (fun _ => PUnit.unit)
        (fun _ _ _ => Subsingleton.elim _ _)
    exact
      { Index := AnswerOccurrence
          (MILLearnedProofRelevantAdmission.vocabulary.meaning Primitive.mother)
          source
        indexFintype := Fintype.ofFinite _
        occurrenceEquiv := Equiv.refl _ }

noncomputable def fatherProvider :
    FiniteEvidenceProvider
      (MILLearnedProofRelevantAdmission.vocabulary.meaning Primitive.father) where
  fibre := fun source => by
    letI : Subsingleton
        (AnswerOccurrence
          (MILLearnedProofRelevantAdmission.vocabulary.meaning Primitive.father)
          source) := fatherOccurrence_subsingleton source
    letI : Finite
        (AnswerOccurrence
          (MILLearnedProofRelevantAdmission.vocabulary.meaning Primitive.father)
          source) :=
      Finite.of_injective (fun _ => PUnit.unit)
        (fun _ _ _ => Subsingleton.elim _ _)
    exact
      { Index := AnswerOccurrence
          (MILLearnedProofRelevantAdmission.vocabulary.meaning Primitive.father)
          source
        indexFintype := Fintype.ofFinite _
        occurrenceEquiv := Equiv.refl _ }

noncomputable def learnedPrimitiveProviders :
    PrimitiveFiniteSearchProviders
      MILLearnedProofRelevantAdmission.vocabulary where
  provide := fun {source} {target} symbol => by
    cases symbol with
    | mother => exact motherProvider
    | father => exact fatherProvider

noncomputable def grandparentPlan :
    NativeSearchPlan FormedQuotationCanary.quotation MILCheckedChain.alice
      MILCheckedChain.carol MILCheckedChain.grandparentProof :=
  { checked := MILCheckedNativePrograms.grandparent
      FormedQuotationCanary.quotation
    provider := deriveCheckedFiniteSearchProvider learnedPrimitiveProviders
      (MILCheckedNativePrograms.grandparent
        FormedQuotationCanary.quotation).toChecked }

/-- The concrete learned chain crosses all three layers: exact raw proof,
formed intrinsic typing, and complete proof-relevant native execution. -/
theorem grandparent_checked_typed_complete_and_occurrence_retaining :
    grandparentPlan.checked.checked.erase = MILCheckedChain.grandparentProof ∧
      IntrinsicMILHypothesis.HasType FormedQuotationCanary.contextSPSMF
        grandparentPlan.checked.toChecked.nativeTerm.code
        (FormedQuotationCanary.quotation.hypothesisType () ()).code ∧
      AnswerBag.Complete
        (grandparentPlan.run MILCheckedChain.alice).answers ∧
      let occurrence : AnswerOccurrence
          grandparentPlan.checked.toChecked.intrinsicProgram.denotation
          MILCheckedChain.alice :=
        ⟨MILCheckedChain.carol,
          grandparentPlan.checked.toChecked.nativeEvidence⟩
      occurrence ∈ (grandparentPlan.run MILCheckedChain.alice).answers := by
  exact ⟨grandparentPlan.checked.erases,
    grandparentPlan.checked.toChecked.nativeTerm.typed,
    grandparentPlan.run_complete MILCheckedChain.alice,
    grandparentPlan.checked_evidence_occurs⟩

/-- An ill-shared middle cannot construct the boundary plan from which native
search begins.  It therefore cannot be accidentally upgraded by the finite
primitive capability. -/
theorem wrong_middle_has_no_native_search_plan :
    ¬ Nonempty
      (NativeSearchPlan FormedQuotationCanary.quotation
        MILCheckedChain.alice MILCheckedChain.bob
        MILCheckedChain.wrongMiddleProof) := by
  rintro ⟨plan⟩
  exact MILCheckedNativePrograms.concrete_wrong_middle_has_no_native_program
    ⟨plan.checked⟩

#print axioms deriveCheckedFiniteSearchProvider
#print axioms NativeSearchPlan.run_complete
#print axioms NativeSearchPlan.checked_evidence_occurs
#print axioms planOfAccepted
#print axioms grandparent_checked_typed_complete_and_occurrence_retaining
#print axioms wrong_middle_has_no_native_search_plan

end MILCheckedNativeSearch
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
