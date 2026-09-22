import Mettapedia.Languages.MeTTa.Experimental.StagedReflective.Presentation
import Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
import Mettapedia.GSLT.Dynamics.RevisionedOccurrenceReturnedFibre

/-!
# Selected-language instances of the staged-reflective theory

The named staged-reflective calculus and its generic capability interfaces do
not depend on candidate assemblies.  This downstream module supplies the
chosen Zero/query-first language image, concrete quotation examples,
structural inclusion, and families-model assembly.

The revisioned-occurrence adaptation below uses the candidate's actual
occurrence source and revision keying.  No separate operational model or
candidate-shaped foundational interface is introduced.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.StagedReflectiveInstances

open Mettapedia.Languages.MeTTa.Experimental.StagedReflective
open Mettapedia.Languages.MeTTa.PrimeCandidates.Language
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax (ScopedTerm)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.TypeTheory

/-- Different revisions in the selected candidate authority induce different
answer identities in the generic proof flow, even with the same subject and
occurrence. -/
theorem candidate_answer_identity_changes_with_revision (model : Model)
    {first second : model.Space} (subject result : Pattern) (occurrence : Nat)
    (different : model.revision first ≠ model.revision second) :
    (Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow.answerClaim
      model.base.source (needRevisionKeying model)
      first subject result occurrence).term ≠
    (Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow.answerClaim
      model.base.source (needRevisionKeying model)
      second subject result occurrence).term :=
  Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow.answer_identity_changes_with_key
    model.base.source (needRevisionKeying model) subject result occurrence
    (needKey_ne_of_revision_ne model subject different)

/-- The exact selected region initially exposed as Pattern data.  This is a
two-point region of the full intrinsic carrier, not a claim to serialize every
future presentation. -/
inductive CurrentLanguageHandle where
  | zero
  | prime
  deriving DecidableEq, Repr

instance : Nonempty CurrentLanguageHandle := ⟨.zero⟩

def currentLanguagePresentation : CurrentLanguageHandle →
    Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef
  | .zero =>
      Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.currentZeroPresentation
  | .prime =>
      Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation

/-- Today's Zero and staged-reflective candidate presentations are distinct objects. -/
theorem currentZeroPresentation_ne_queryFirstCandidatePresentation :
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.currentZeroPresentation ≠
      Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation := by
  intro equal
  have names := congrArg
    (fun presentation : Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef =>
      presentation.language.name) equal
  change "metta-zero-query-kernel" = "metta-prime-spec-probe" at names
  have distinct : "metta-zero-query-kernel" ≠ "metta-prime-spec-probe" := by decide
  exact distinct names

theorem currentLanguagePresentation_injective :
    Function.Injective currentLanguagePresentation := by
  intro first second equal
  cases first <;> cases second
  · rfl
  · exact (currentZeroPresentation_ne_queryFirstCandidatePresentation equal).elim
  · exact (currentZeroPresentation_ne_queryFirstCandidatePresentation equal.symm).elim
  · rfl

def currentLanguagePattern : CurrentLanguageHandle → Pattern
  | .zero => .fvar "native-language/zero"
  | .prime => .fvar "native-language/prime"

def decodeCurrentLanguagePattern (pattern : Pattern) :
    Option CurrentLanguageHandle :=
  if pattern = currentLanguagePattern .zero then some .zero
  else if pattern = currentLanguagePattern .prime then some .prime
  else none

theorem decodeCurrentLanguagePattern_encode (value : CurrentLanguageHandle) :
    decodeCurrentLanguagePattern (currentLanguagePattern value) = some value := by
  cases value <;> decide

theorem currentLanguagePattern_decode
    {pattern : Pattern} {value : CurrentLanguageHandle}
    (decoded : decodeCurrentLanguagePattern pattern = some value) :
    currentLanguagePattern value = pattern := by
  unfold decodeCurrentLanguagePattern at decoded
  split at decoded
  · rename_i isZero
    have valueIsZero : CurrentLanguageHandle.zero = value :=
      Option.some.inj decoded
    subst value
    exact isZero.symm
  · split at decoded
    · rename_i isPrime
      have valueIsPrime : CurrentLanguageHandle.prime = value :=
        Option.some.inj decoded
      subst value
      exact isPrime.symm
    · cases decoded

def outsideCurrentLanguagePattern : Pattern :=
  .fvar "not-a-native-language-code"

theorem outsideCurrentLanguagePattern_not_decoded :
    decodeCurrentLanguagePattern outsideCurrentLanguagePattern = none := by
  decide

/-- Full intrinsic language values plus an exact, explicitly selected Pattern
codec. -/
def familiesLanguageCodeWitness :
    LanguageCodeWitness stageModeTheory familiesCwF familiesPatternSpaceModel where
  LanguageValue := Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef
  asValidated := _root_.id
  langCode := familiesValidatedLanguageCode
  languageValueEquiv :=
    { toFun := fun term => term PUnit.unit
      invFun := fun value _ => value
      left_inv := by intro term; funext value; cases value; rfl
      right_inv := by intro value; rfl }
  SelectedValue := CurrentLanguageHandle
  selectedValue := currentLanguagePresentation
  selectedValue_injective := currentLanguagePresentation_injective
  encodePattern := currentLanguagePattern
  decodePattern := decodeCurrentLanguagePattern
  decode_encode := decodeCurrentLanguagePattern_encode
  encode_decode := currentLanguagePattern_decode
  outside := outsideCurrentLanguagePattern
  outside_not_decoded := outsideCurrentLanguagePattern_not_decoded

/-- Positive image witness for the current staged-reflective candidate presentation. -/
theorem queryFirstCandidatePattern_is_languagePattern :
    familiesLanguageCodeWitness.IsLanguagePattern
      (currentLanguagePattern .prime) :=
  ⟨.prime, rfl⟩

/-- Negative image witness: the selected codec rejects an unrelated Pattern. -/
theorem outsideCurrentLanguagePattern_not_languagePattern :
    ¬ familiesLanguageCodeWitness.IsLanguagePattern
      outsideCurrentLanguagePattern :=
  familiesLanguageCodeWitness.image_proper

/-- A real constructor value in today's Zero presentation. -/
def currentZeroEquationConstructor :
    Mettapedia.GSLT.LanguageDef.StructuralMorphism.DeclaredConstructor
      Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.currentZeroPresentation :=
  ⟨Mettapedia.Languages.MeTTa.MeTTaZero.equationConstructor, by
    change List.Mem Mettapedia.Languages.MeTTa.MeTTaZero.equationConstructor
      [Mettapedia.Languages.MeTTa.MeTTaZero.equationConstructor,
       Mettapedia.Languages.MeTTa.MeTTaZero.queryRequestConstructor,
       Mettapedia.Languages.MeTTa.MeTTaZero.queryAnswerConstructor,
       Mettapedia.Languages.MeTTa.MeTTaZero.evaluationRequestConstructor,
       Mettapedia.Languages.MeTTa.MeTTaZero.evaluationAnswerConstructor]
    exact List.mem_cons_self⟩

/-- Positive operational content: the admitted current Zero-to-staged-reflective candidate map
really transports an authored constructor value into staged-reflective candidate. -/
theorem queryFirstZeroToCandidate_maps_equationConstructor :
    ((structuralConstructorAdmission
      Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstZeroToCandidatePresentation).run
        currentZeroEquationConstructor).1 =
      Mettapedia.Languages.MeTTa.MeTTaZero.equationConstructor := by
  exact Mettapedia.GSLT.LanguageDef.mapGrammarRule_id _

/-- Audit package for first-class language manipulation.  Its map is the live
proper Zero-to-staged-reflective candidate structural inclusion; the reverse identity-symbol map is
required to remain impossible. -/
structure LanguageManipulationWitness where
  codes : LanguageCodeWitness stageModeTheory familiesCwF
    familiesPatternSpaceModel
  structural : Mettapedia.GSLT.LanguageDef.StructuralMorphism
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.currentZeroPresentation
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation
  endpointsDistinct :
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.currentZeroPresentation ≠
      Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation
  sourceConstructor :
    Mettapedia.GSLT.LanguageDef.StructuralMorphism.DeclaredConstructor
      Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.currentZeroPresentation
  mapsSourceConstructor :
    ((structuralConstructorAdmission structural).run sourceConstructor).1 =
      Mettapedia.Languages.MeTTa.MeTTaZero.equationConstructor
  noIdentityReverse :
    ¬ ∃ retraction : Mettapedia.GSLT.LanguageDef.StructuralMorphism
        Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation
        Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.currentZeroPresentation,
      retraction.symbols = Mettapedia.GSLT.LanguageDef.LanguageDefSymbolMap.id

/-- O13's intrinsic carrier, exact selected Pattern image, nonidentity typed
operation, and negative reverse witness. -/
def nativeLanguageManipulationWitness : LanguageManipulationWitness where
  codes := familiesLanguageCodeWitness
  structural :=
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstZeroToCandidatePresentation
  endpointsDistinct := currentZeroPresentation_ne_queryFirstCandidatePresentation
  sourceConstructor := currentZeroEquationConstructor
  mapsSourceConstructor := queryFirstZeroToCandidate_maps_equationConstructor
  noIdentityReverse :=
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.no_identity_symbol_retraction

/-- Positive first-class language witness: today's validated staged-reflective candidate
presentation is an intrinsic native value, but is not confused with a Pure
term. -/
def nativeQueryFirstCandidateLanguage : StagedReflectiveTm 0 0 :=
  .language
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation

theorem nativeQueryFirstCandidateLanguage_not_in_pure_image :
    ¬ ∃ pure : ScopedTerm 0, embedTwoSort 0 pure = nativeQueryFirstCandidateLanguage :=
  twoSortProjection_none_not_in_twoSort_image nativeQueryFirstCandidateLanguage rfl

/-- A concrete program from the current authored staged-reflective candidate interface: the left side
of its reflected-demand rewrite. -/
def queryFirstCandidateReflectedDemandProgram : Pattern :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.reflectedDemandRewrite.left

/-- Positive source-faithfulness witness: a real current staged-reflective candidate program
round-trips through the native raw inclusion. -/
theorem queryFirstCandidateReflectedDemandProgram_roundtrip :
    (embedRuntimePattern queryFirstCandidateReflectedDemandProgram :
      StagedReflectiveTm 0 0).runtimePattern? =
        some queryFirstCandidateReflectedDemandProgram :=
  rfl

/-- The current staged-reflective candidate presentation is taken directly from the carrier
classified by the existing Tarski language-type code. -/
def queryFirstCandidateLanguageUniverseValue :
    (familiesCwF.el familiesValidatedLanguageCode) PUnit.unit :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation

def quotedQueryFirstCandidateLanguage : StagedReflectiveTm 0 0 :=
  nativeQuotedLanguage 0 queryFirstCandidateLanguageUniverseValue

theorem quotedQueryFirstCandidateLanguage_strictly_raises :
    (StagedReflectiveTm.language queryFirstCandidateLanguageUniverseValue :
        StagedReflectiveTm 1 0).reflectiveDepth <
      quotedQueryFirstCandidateLanguage.reflectiveDepth :=
  nativeQuoteNext_strictly_raises 0 _

/-- Positive bridge witness: the real current staged-reflective candidate presentation, classified
by the Tarski language carrier, round-trips through the single raw quotation
former. -/
theorem quotedQueryFirstCandidateLanguage_roundtrip :
    quotedQueryFirstCandidateLanguage.quotedLanguage? =
      some Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation :=
  rfl

/-- Concrete witnesses for the families candidate's stated audit fields,
including its scoped equality architecture.  These constructions establish
their own laws and positive or negative/noncollapse properties, not a
necessity or completeness theorem for the requirement policies. -/
def familiesNativeTheoryAudit : NativeTheoryAudit familiesCandidate where
  equality := selectedNativeEqualityArchitecture
  spaceModel := familiesPatternSpaceModel
  spaceCode := familiesSpaceCodeWitness
  quotation := familiesQuotationWitness
  contextualBox := familiesContextualBoxWitness
  levels := stageLevelWitness
  grading := nativeGradingWitness
  evidence := nativeEvidenceFibration
  InterfaceClaim := HESuccessClaim
  interface := heSuccessInterface
  dependentFamilies := familiesDependentFamilyWitness
  identityTypes := familiesIdentityTypes
  inductiveFamilies := familiesBooleanInductive
  languageCodes := familiesLanguageCodeWitness
  universeTower := familiesUniverseTower
  directTyping := fastDirectPatternTypingWitness
  authorityParity := fastNativeAuthorityParityWitness
  proofFlow := fun occurrences keying =>
    Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow.witness occurrences keying

/-- The concrete law-complete candidate, its nondegenerate audit, and its
exact direct-typing parity square form one inhabitant of the assembled target. -/
def familiesAssembledNativeTheory : AssembledNativeTheory where
  candidate := familiesCandidate
  audit := familiesNativeTheoryAudit

/-- Positive crown witness: the assembled theory's primary checker accepts a
real unknown-typed Pattern claim. -/
theorem familiesAssembledNativeTheory_primary_positive :
    familiesAssembledNativeTheory.audit.directTyping.kernel.toChecker.check
      ⟨Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.empty, .bvar 0,
        Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩ () = true :=
  fastPatternTyping_unknown_positive _ _

/-- Negative crown witness: assembly does not turn the direct typing boundary
into an always-accepting facade. -/
theorem familiesAssembledNativeTheory_primary_negative :
    familiesAssembledNativeTheory.audit.directTyping.kernel.toChecker.check
      fastPatternTypingRejected () = false :=
  fastPatternTyping_unsupported_negative

#print axioms candidate_answer_identity_changes_with_revision
#print axioms familiesAssembledNativeTheory_primary_positive
#print axioms familiesAssembledNativeTheory_primary_negative
#print axioms currentZeroPresentation_ne_queryFirstCandidatePresentation
#print axioms currentLanguagePresentation_injective
#print axioms decodeCurrentLanguagePattern_encode
#print axioms currentLanguagePattern_decode
#print axioms familiesLanguageCodeWitness
#print axioms queryFirstCandidatePattern_is_languagePattern
#print axioms outsideCurrentLanguagePattern_not_languagePattern
#print axioms queryFirstZeroToCandidate_maps_equationConstructor
#print axioms nativeLanguageManipulationWitness
#print axioms nativeQueryFirstCandidateLanguage_not_in_pure_image
#print axioms queryFirstCandidateReflectedDemandProgram_roundtrip
#print axioms familiesNativeTheoryAudit
#print axioms quotedQueryFirstCandidateLanguage_strictly_raises
#print axioms quotedQueryFirstCandidateLanguage_roundtrip

end Mettapedia.Languages.MeTTa.PrimeCandidates.StagedReflectiveInstances
