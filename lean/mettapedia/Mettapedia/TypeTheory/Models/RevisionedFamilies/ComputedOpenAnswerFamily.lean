import Mettapedia.TypeTheory.Calculi.StagedScopedReflective.Presentation
import Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
import Mettapedia.OSLF.Framework.WMCalculusCombinedGenericOpenCodec
import Mettapedia.OSLF.Framework.WMCalculusSupportedContextCategory

/-!
# Computed open WM answers in Prime's semantic dependent families

The combined WM reading interprets supported intrinsic constructor terms.
Its evidence-answer predicate is lifted to a family in the staged families
semantic CwF. A checked, executable open match computes both the intrinsic
source and its constructor-tree substitution. The resulting answer family is
equivalent, at every answer and model environment, to the source family pulled
back along that computed substitution.

This is a semantic family comparison on the supported first-order fragment.
It adds no Prime syntax, does not totalize partial matching, and does not
identify observational agreement with intensional identity.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.ComputedOpenAnswerFamily

open Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.OpenReification
open Mettapedia.GSLT.LanguageDef.NamedFreeContext
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
open Mettapedia.OSLF.Framework.WMCalculusCombinedNamedFirstOrder
open Mettapedia.OSLF.Framework.WMCalculusCombinedOpenReification
open Mettapedia.OSLF.Framework.WMCalculusCombinedGenericOpenCodec
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusSupportedContextCategory

private abbrev EvidenceSort : TypeExpr := .base "BinaryEvidence"
private abbrev CombinedLang : LanguageDef :=
  wmExtVertexLanguageDefGuarded combinedVertex

/-- An evidence answer carries the actual equality with the interpretation
of a supported intrinsic term. This Type-valued receipt is subsingleton;
it records correctness, not execution provenance. -/
structure EvidenceAnswerReceipt {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    {term : Term CombinedSignature Γ EvidenceSort}
    (fragment : FirstOrder term) (answer : Ev)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ) : Type where
  checked : EvidenceFibre reading fragment answer environment

instance {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    {term : Term CombinedSignature Γ EvidenceSort}
    (fragment : FirstOrder term) (answer : Ev)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ) :
    Subsingleton (EvidenceAnswerReceipt reading fragment answer environment) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- The interpreted evidence-answer fibre is a dependent type over the model
environments of its intrinsic variable context. -/
def evidenceAnswerFamily {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    {term : Term CombinedSignature Γ EvidenceSort}
    (fragment : FirstOrder term) (answer : Ev) :
    familiesCwF.Ty (mode := stageOfNat 0)
      (Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ) :=
  fun environment => EvidenceAnswerReceipt reading fragment answer environment

/-- Any supported certificate for a substituted target yields the same
dependent answer fibre as pulling the source family back along the semantic
substitution of environments. The target certificate need not be the
particular certificate chosen by `FirstOrder.substitute`. -/
def evidenceAnswerFamily_reindex_equiv {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ sort (position : Var Γ sort),
      FirstOrder (sigma sort position))
    {term : Term CombinedSignature Γ EvidenceSort}
    (fragment : FirstOrder term)
    (targetCertificate : FirstOrder (bind sigma term))
    (answer : Ev)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ) :
    evidenceAnswerFamily reading targetCertificate answer environment ≃
      familiesCwF.tySub (evidenceAnswerFamily reading fragment answer)
        (reindexEnvironment reading sigma supported) environment := by
  have sameCertificate :
      FirstOrder.denote reading environment targetCertificate =
        FirstOrder.denote reading environment
          (FirstOrder.substitute sigma supported fragment) :=
    (denote_heq_of_erase_eq reading environment targetCertificate
      (FirstOrder.substitute sigma supported fragment) rfl).eq
  have semanticSubstitution :=
    denote_substitute reading sigma supported environment fragment
  have sameAnswer :
      FirstOrder.denote reading environment targetCertificate =
        FirstOrder.denote reading
          (reindexEnvironment reading sigma supported environment) fragment :=
    sameCertificate.trans semanticSubstitution
  refine {
    toFun := fun receipt => ⟨sameAnswer.symm.trans receipt.checked⟩
    invFun := fun receipt => ⟨sameAnswer.trans receipt.checked⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro receipt
    cases receipt
    rfl
  · intro receipt
    cases receipt
    rfl

/-- A checked open Evidence match computes one source term and one
constructor-tree substitution. The exact resulting target certificate gives
an equivalence of Prime semantic answer fibres for every answer and every
target environment, not just the environment used to obtain the receipt. -/
theorem checkedOpenAnswers_computed_family
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (sourceFree targetFree : FreeTypeContext)
    (pattern concrete : Pattern) (bindings : Bindings)
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern EvidenceSort concrete) :
    let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
    let targetEntries := fromUsed targetFree
      (capturedTargetNames sourceEntries bindings)
    ∃ sigma : Sub CombinedSignature
        (contextSorts sourceEntries) (contextSorts targetEntries),
      reifyOpenImages? CombinedLang targetEntries bindings sourceEntries =
        some sigma ∧
      ∃ term : Term CombinedSignature (contextSorts sourceEntries) EvidenceSort,
        reifyOpen? CombinedLang sourceEntries pattern EvidenceSort = some term ∧
        ∃ fragment : FirstOrder term,
          namedErase (names sourceEntries) fragment = pattern ∧
          ∃ supported : ∀ imageSort
              (position : Var (contextSorts sourceEntries) imageSort),
              FirstOrder (sigma imageSort position),
            ∃ targetCertificate : FirstOrder (bind sigma term),
              namedErase (names targetEntries) targetCertificate = concrete ∧
              ∀ answer : Ev,
                ∀ targetEnvironment : Environment (State := State)
                    (Query := Query) (Ev := Ev) (Ov := Ov) (Scope := Scope)
                    (contextSorts targetEntries),
                  Nonempty
                    (evidenceAnswerFamily reading targetCertificate answer
                        targetEnvironment ≃
                      familiesCwF.tySub
                        (evidenceAnswerFamily reading fragment answer)
                        (reindexEnvironment reading sigma supported)
                        targetEnvironment) := by
  obtain ⟨sigma, sigmaComputed, term, termComputed, fragment, sourceNamed,
      supported, targetNamed⟩ :=
    checkedOpenAnswers_computed_substitution sourceFree targetFree pattern
      bindings concrete returned
  let targetCertificate := FirstOrder.substitute sigma supported fragment
  exact ⟨sigma, sigmaComputed, term, termComputed, fragment, sourceNamed,
    supported, targetCertificate, targetNamed,
    fun answer targetEnvironment =>
      ⟨evidenceAnswerFamily_reindex_equiv reading sigma supported fragment
        targetCertificate answer targetEnvironment⟩⟩

/-- Family transport uses the actual context-category interpretation.
No equality of arbitrary equivalent Type-valued fibres is assumed. -/
noncomputable def evidenceAnswerFamily_categorical_equiv
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ sort position, FirstOrder (sigma sort position))
    {term : Term CombinedSignature Γ EvidenceSort}
    (fragment : FirstOrder term)
    (targetCertificate : FirstOrder (bind sigma term))
    (answer : Ev)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ) :
    evidenceAnswerFamily reading targetCertificate answer environment ≃
      evidenceAnswerFamily reading fragment answer
        ((environmentFunctor reading).map
          (supportedMap sigma supported) environment) := by
  rw [environmentFunctor_map_supportedMap]
  exact evidenceAnswerFamily_reindex_equiv reading sigma supported fragment
    targetCertificate answer environment

/-- Changing the intrinsic index by a proved syntactic equality does not
change the answer or its environment. -/
def castAnswerReceipt {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    {first second : Term CombinedSignature Γ EvidenceSort}
    (same : first = second) (fragment : FirstOrder first)
    {answer : Ev}
    {environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ}
    (receipt : evidenceAnswerFamily reading fragment answer environment) :
    evidenceAnswerFamily reading (same ▸ fragment) answer environment := by
  cases same
  exact receipt

private theorem answerReceipt_heq_of_environment_eq
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    {term : Term CombinedSignature Γ EvidenceSort}
    (fragment : FirstOrder term) (answer : Ev)
    {first second : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ}
    (same : first = second)
    (left : evidenceAnswerFamily reading fragment answer first)
    (right : evidenceAnswerFamily reading fragment answer second) :
    HEq left right := by
  cases same
  cases left
  cases right
  rfl

/-- Identity substitution acts as the identity on answer receipts, after
the syntactic identity law changes the substituted term's index. -/
theorem evidenceAnswerFamily_reindex_id
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    {term : Term CombinedSignature Γ EvidenceSort}
    (fragment : FirstOrder term) (answer : Ev)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (receipt : evidenceAnswerFamily reading fragment answer environment) :
    HEq
      ((evidenceAnswerFamily_reindex_equiv reading
          (fun _ position => Term.var position)
          (fun _ position => FirstOrder.variable position) fragment
          ((bind_id term).symm ▸ fragment) answer environment)
        (castAnswerReceipt reading (bind_id term).symm fragment receipt))
      receipt := by
  exact answerReceipt_heq_of_environment_eq reading fragment answer
    (reindexEnvironment_id reading environment) _ _

/-- Further substitution is coherent on the answer families. Both routes
start with the same final receipt; the direct route changes its intrinsic
index only by the generic binding-composition theorem. -/
theorem evidenceAnswerFamily_reindex_comp
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ Θ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ) (tau : Sub CombinedSignature Δ Θ)
    (hs : ∀ sort position, FirstOrder (sigma sort position))
    (ht : ∀ sort position, FirstOrder (tau sort position))
    {term : Term CombinedSignature Γ EvidenceSort}
    (fragment : FirstOrder term)
    (middle : FirstOrder (bind sigma term))
    (last : FirstOrder (bind tau (bind sigma term)))
    (answer : Ev)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Θ)
    (receipt : evidenceAnswerFamily reading last answer environment) :
    HEq
      ((evidenceAnswerFamily_reindex_equiv reading sigma hs fragment middle
          answer (reindexEnvironment reading tau ht environment))
        ((evidenceAnswerFamily_reindex_equiv reading tau ht middle last
          answer environment) receipt))
      ((evidenceAnswerFamily_reindex_equiv reading
          (fun sort position => bind tau (sigma sort position))
          (fun sort position => FirstOrder.substitute tau ht (hs sort position))
          fragment ((bind_comp sigma tau term) ▸ last) answer environment)
        (castAnswerReceipt reading (bind_comp sigma tau term) last receipt)) := by
  exact answerReceipt_heq_of_environment_eq reading fragment answer
    (reindexEnvironment_comp reading sigma tau hs ht environment) _ _

private abbrev RequestContext : Ctx CombinedSignature :=
  [.base "State", .base "Query"]

/-- Interpret the two free intrinsic handles of an authored `Extract` term
at one semantic state-query request. -/
def requestEnvironment {State Query Ev Ov Scope : Type}
    (state : State) (query : Query) :
    Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) RequestContext :=
  by
    intro sort position
    cases position with
    | zero => exact state
    | succ earlier =>
        cases earlier with
        | zero => exact query
        | succ impossible => cases impossible

private def requestState : Term CombinedSignature RequestContext (.base "State") :=
  .var .zero

private def requestQuery : Term CombinedSignature RequestContext (.base "Query") :=
  .var (.succ .zero)

private def extractRequestCertificate : FirstOrder
    (extract requestState requestQuery) :=
  .extract (.variable .zero) (.variable (.succ .zero))

/-- The GSLT-IL capability receipt corresponds to the intrinsic `Extract`
observation only while its original support proof is retained. -/
structure IntrinsicSupportedRequestReceipt {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (capability : WMCapability reading.core)
    (state : State) (query : Query) (answer : Ev) : Type where
  supported : capability.supports state query
  checked : evidenceAnswerFamily reading extractRequestCertificate answer
    (requestEnvironment (Ev := Ev) (Ov := Ov) (Scope := Scope) state query)

/-- At each request and answer, the existing observable GSLT-IL/Prime
capability receipt is equivalent to a supported intrinsic `Extract` answer
in the new environment-indexed family. The support premise is indispensable:
the intrinsic observation alone remains defined at unsupported requests. -/
def observableReceipt_intrinsicEquiv {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (capability : WMCapability reading.core)
    (state : State) (query : Query) (answer : Ev) :
    observableReceiptFamily capability answer
        (classOf reading.core state, query) ≃
      IntrinsicSupportedRequestReceipt reading capability state query answer := by
  refine {
    toFun := fun receipt =>
      ⟨(observableSupport_classOf capability state query).mp receipt.supported,
        ⟨receipt.checked⟩⟩
    invFun := fun receipt =>
      ⟨(observableSupport_classOf capability state query).mpr receipt.supported,
        receipt.checked.checked⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro receipt
    cases receipt
    rfl
  · intro receipt
    cases receipt
    rfl

/-- Every supported request has the intrinsic extraction answer, retaining
the capability support proof as well as the model's exact evidence value. -/
def intrinsicReceipt_of_supported {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (capability : WMCapability reading.core)
    (state : State) (query : Query)
    (supported : capability.supports state query) :
    IntrinsicSupportedRequestReceipt reading capability state query
      (reading.core.extract state query) :=
  ⟨supported, ⟨rfl⟩⟩

/-- A capability's unsupported request has no intrinsic supported receipt
at any candidate answer, even though bare WM extraction is still defined. -/
theorem intrinsicReceipt_empty_of_unsupported
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (capability : WMCapability reading.core)
    (state : State) (query : Query)
    (unsupported : ¬ capability.supports state query)
    (answer : Ev) :
    ¬ Nonempty (IntrinsicSupportedRequestReceipt reading capability
      state query answer) := by
  rintro ⟨receipt⟩
  exact unsupported receipt.supported

private def compoundEvidence : Pattern :=
  pCombine pEvidenceZero pEvidenceZero

private def evidenceHandleFree : FreeTypeContext :=
  FreeTypeContext.ofList [("e", EvidenceSort)]

/-- The executable checker really accepts a compound constructor-tree image
for an open Evidence handle; the family theorem above therefore has a
nonvariable-image instance. -/
theorem compoundEvidence_checked :
    [("e", compoundEvidence)] ∈
      checkedOpenAnswers evidenceHandleFree FreeTypeContext.empty
        (.fvar "e") EvidenceSort compoundEvidence := by
  simpa [compoundEvidence, evidenceHandleFree]
    using checked_compound_evidence_explicit

private abbrev EmptyContext : Ctx CombinedSignature := []

private def emptyEnvironment :
    Environment (State := CountState) (Query := String)
      (Ev := Nat) (Ov := Nat) (Scope := CountScope) EmptyContext :=
  fun _ position => nomatch position

private def combinedZeroCertificate : FirstOrder
    (combine (zero (Γ := EmptyContext)) (zero (Γ := EmptyContext))) :=
  .combine .zero .zero

/-- The dependent evidence family has an actual inhabitant at the correct
answer for a compound term in the counting reading. -/
theorem compoundZero_answer_inhabited :
    Nonempty (evidenceAnswerFamily countingCombined combinedZeroCertificate
      0 emptyEnvironment) :=
  ⟨⟨rfl⟩⟩

/-- The same computed constructor meaning cannot inhabit the fibre at a
wrong answer. The family is an answer-indexed type, not a constant witness. -/
theorem compoundZero_wrong_answer_empty :
    ¬ Nonempty (evidenceAnswerFamily countingCombined
      combinedZeroCertificate 1 emptyEnvironment) := by
  rintro ⟨receipt⟩
  exact Nat.zero_ne_one receipt.checked

#print axioms evidenceAnswerFamily_reindex_equiv
#print axioms checkedOpenAnswers_computed_family
#print axioms evidenceAnswerFamily_categorical_equiv
#print axioms evidenceAnswerFamily_reindex_id
#print axioms evidenceAnswerFamily_reindex_comp
#print axioms observableReceipt_intrinsicEquiv
#print axioms intrinsicReceipt_of_supported
#print axioms intrinsicReceipt_empty_of_unsupported
#print axioms compoundEvidence_checked
#print axioms compoundZero_answer_inhabited
#print axioms compoundZero_wrong_answer_empty

end Mettapedia.TypeTheory.Models.RevisionedFamilies.ComputedOpenAnswerFamily
