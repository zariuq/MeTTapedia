import Mettapedia.GSLT.LanguageDef.CheckedSource
import Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTLayers
import Mettapedia.OSLF.Framework.RelationalAnswerTypeSynthesis

/-!
# Checked typing profiles over PeTTa's operational GSLT

PeTTa's operational core and its optional typing profiles are different
semantic layers.  The operational core determines state change and ordered
answer occurrences.  A typing profile contributes an admitted inference
definition and a translation from an emitted answer to a typing goal.

This module composes the two without making either one a fallback for the
other.  A typed answer contains both:

* a `CoreDecl` run producing a particular answer occurrence; and
* a proof-relevant derivation accepted by the generic inference checker.

The first instance is the authored typecheck-v2 stage-1 calculus.  It remains a
named optional profile, not part of untyped PeTTa core.  Its symbolic witness
domain (`VNum`, `VStr`, and so on) is retained honestly; bridging the complete
runtime value domain is a later exact-image obligation.

No generated runtime artifact occurs here.  The construction is a Lean
specification and conformance boundary for a directly implemented runtime.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TypedOperationalGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CalculusExtension
open Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
open Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT
open Mettapedia.OSLF.Framework.RelationalAnswerTypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- An optional PeTTa typing profile admitted at the generic proof-checking
waist.  `goal` may inspect the final space, so declaration-aware profiles do
not need a second interface later.  `covered` is the profile's explicit
competence boundary: failure to translate an operational answer into the
profile is not confused with failure to derive the translated judgment. -/
structure TypingProfile where
  checked : CheckedGSLT
  covered : EvalState → Pattern → Pattern → Bool
  goal : EvalState → Pattern → Pattern → Pattern

/-- PeTTa core is operationally meaningful without a typing profile.  A typed
profile adds judgments without replacing or changing that operational core. -/
inductive Profile where
  | core
  | typed (typing : TypingProfile)

/-- Every profile shares the same state- and occurrence-preserving operational
GSLT.  Profiles refine observations of runs; they do not rewrite the runs. -/
def Profile.operationalGSLT (_profile : Profile) : GSLT :=
  CoreOperationalGSLT

@[simp] theorem operationalGSLT_core :
    Profile.core.operationalGSLT = CoreOperationalGSLT :=
  rfl

@[simp] theorem operationalGSLT_typed (typing : TypingProfile) :
    (Profile.typed typing).operationalGSLT = CoreOperationalGSLT :=
  rfl

/-- The profile observation on an emitted answer is inhabitation of the
profile's typing goal by an exact generic-checker derivation. -/
def checkedTypeObservation (profile : TypingProfile) (type : Pattern)
    (_initial : EvalState) (_request : Pattern) (final : EvalState)
    (answer : Pattern) : Prop :=
  profile.covered final answer type = true ∧
    Nonempty
      (Derivation profile.checked.definition (profile.goal final answer type))

/-- A proof-carrying extension between optional typing profiles.  Coverage may
grow, but every judgment covered and derivable in the base profile must remain
covered and acquire a translated derivation in the extension.  This is the
criterion a future v3 profile must satisfy before it can claim to extend v2. -/
structure TypingProfile.Extension (base extension : TypingProfile) where
  covered : ∀ final answer type,
    base.covered final answer type = true →
      extension.covered final answer type = true
  derivation : ∀ final answer type,
    Derivation base.checked.definition (base.goal final answer type) →
      Derivation extension.checked.definition
        (extension.goal final answer type)

namespace TypingProfile.Extension

/-- A profile extends itself without changing either coverage or evidence. -/
def refl (profile : TypingProfile) : profile.Extension profile where
  covered := fun _ _ _ evidence => evidence
  derivation := fun _ _ _ evidence => evidence

/-- Profile extension composes while retaining the translated derivation. -/
def trans {first second third : TypingProfile}
    (firstToSecond : first.Extension second)
    (secondToThird : second.Extension third) : first.Extension third where
  covered := fun final answer type evidence =>
    secondToThird.covered final answer type
      (firstToSecond.covered final answer type evidence)
  derivation := fun final answer type evidence =>
    secondToThird.derivation final answer type
      (firstToSecond.derivation final answer type evidence)

end TypingProfile.Extension

/-- An extension preserves every checked answer observation, including the
explicit evidence that the answer lies in the profile's image. -/
theorem checkedTypeObservation_mono
    {base extension : TypingProfile} (extensionWitness : base.Extension extension)
    (type initial request final answer) :
  checkedTypeObservation base type initial request final answer →
      checkedTypeObservation extension type initial request final answer := by
  rintro ⟨covered, ⟨derivation⟩⟩
  exact ⟨extensionWitness.covered final answer type covered,
    ⟨extensionWitness.derivation final answer type derivation⟩⟩

/-- OSLF-derived type of requests which can emit at least one answer carrying
a checked derivation in the selected typing profile. -/
def producesCheckedType (profile : TypingProfile) (type : Pattern) :
    CoreOperationalTerm → Prop :=
  producesAnswerSatisfying coreSource (checkedTypeObservation profile type)

/-- Provable profile extension is conservative for the behavioral types
derived from PeTTa execution.  The operational witness is reused unchanged;
only the profile derivation is translated. -/
theorem producesCheckedType_mono
    {base extension : TypingProfile} (extensionWitness : base.Extension extension)
    (type : Pattern) (term : CoreOperationalTerm) :
    producesCheckedType base type term →
      producesCheckedType extension type term := by
  exact producesAnswerSatisfying_mono coreSource
    (fun initial request final answer =>
      checkedTypeObservation_mono extensionWitness type initial request final answer)
    term

/-- Exact operational meaning of profile-checked behavioral typing.  The final
space, complete ordered answer bag, and exact occurrence are all retained. -/
theorem producesCheckedType_request_iff
    (profile : TypingProfile) (type : Pattern)
    (initial : EvalState) (request : Pattern) :
    producesCheckedType profile type (.request initial request) ↔
      ∃ (final : EvalState) (answers : Answers),
        ∃ occurrence : Fin answers.length,
          CoreDecl initial request final answers ∧
            profile.covered final (answers.get occurrence) type = true ∧
              Nonempty (Derivation profile.checked.definition
                (profile.goal final (answers.get occurrence) type)) := by
  simpa [producesCheckedType, checkedTypeObservation, coreSource] using
    producesAnswerSatisfying_request_iff coreSource
      (checkedTypeObservation profile type) initial request

/-- A proof-relevant typed answer.  The occurrence prevents duplicate equal
answers from collapsing; the derivation prevents a Boolean acceptance from
becoming the semantic object. -/
structure CheckedAnswer (profile : TypingProfile) (initial : EvalState)
    (request type : Pattern) where
  final : EvalState
  answers : Answers
  occurrence : Fin answers.length
  evaluation : CoreDecl initial request final answers
  covered : profile.covered final (answers.get occurrence) type = true
  derivation : Derivation profile.checked.definition
    (profile.goal final (answers.get occurrence) type)

/-- The Type-valued answer object presents exactly the OSLF-derived
profile-checked behavioral type. -/
theorem nonempty_checkedAnswer_iff_producesCheckedType
    (profile : TypingProfile) (type : Pattern)
    (initial : EvalState) (request : Pattern) :
    Nonempty (CheckedAnswer profile initial request type) ↔
      producesCheckedType profile type (.request initial request) := by
  constructor
  · rintro ⟨answer⟩
    rw [producesCheckedType_request_iff]
    exact ⟨answer.final, answer.answers, answer.occurrence,
      answer.evaluation, answer.covered, ⟨answer.derivation⟩⟩
  · rw [producesCheckedType_request_iff]
    rintro ⟨final, answers, occurrence, evaluation, covered, ⟨derivation⟩⟩
    exact ⟨⟨final, answers, occurrence, evaluation, covered, derivation⟩⟩

/-- Erasing the retained derivation yields a finite proof object accepted by
the one generic checker. -/
def CheckedAnswer.rawProof {profile : TypingProfile} {initial : EvalState}
    {request type : Pattern}
    (answer : CheckedAnswer profile initial request type) : RawProof :=
  answer.derivation.erase

theorem CheckedAnswer.rawProof_checks
    {profile : TypingProfile} {initial : EvalState} {request type : Pattern}
    (answer : CheckedAnswer profile initial request type) :
    profile.checked.checkRaw
        (profile.goal answer.final
          (answer.answers.get answer.occurrence) type)
        answer.rawProof = true :=
  CheckedGSLT.checkRaw_erase answer.derivation

/-- Equivalent external waist: a request has the behavioral checked type iff
one exact emitted occurrence has a finite proof accepted by the generic
checker.  Search may produce that proof, but only the checker acceptance is
used here. -/
theorem producesCheckedType_iff_exists_checkedProof
    (profile : TypingProfile) (type : Pattern)
    (initial : EvalState) (request : Pattern) :
    producesCheckedType profile type (.request initial request) ↔
      ∃ (final : EvalState) (answers : Answers),
        ∃ occurrence : Fin answers.length,
          CoreDecl initial request final answers ∧
            profile.covered final (answers.get occurrence) type = true ∧
              ∃ proof : RawProof,
                profile.checked.checkRaw
                  (profile.goal final (answers.get occurrence) type) proof = true := by
  rw [producesCheckedType_request_iff]
  constructor
  · rintro ⟨final, answers, occurrence, evaluation, covered, ⟨derivation⟩⟩
    exact ⟨final, answers, occurrence, evaluation, covered,
      derivation.erase, CheckedGSLT.checkRaw_erase derivation⟩
  · rintro ⟨final, answers, occurrence, evaluation, covered, proof, checked⟩
    exact ⟨final, answers, occurrence, evaluation, covered,
      CheckedGSLT.checkRaw_soundness checked⟩

/-! ## The optional typecheck-v2 profile -/

/-- Full pinned upstream revision from which the v2 stage-1 calculus was
authored. -/
def v2Identity : SourceIdentity where
  systemId := "trueagi-io/PeTTa:typecheck-v2"
  revision := "e038e4dbb587e48fdb9d14990966108d38fde0b3"
  artifactDigest := "git-tree:08a65a248998f6484d4c70fbf882a1efd9b8c7ea"

/-- This is explicitly the symbolic stage-1 v2 profile, not untyped PeTTa
core and not the later typecheck-v3 profile. -/
def v2Profiles : ProfileLedger where
  entries :=
    [{ name := "typecheck-v2-stage1"
       version := "e038e4dbb587e48fdb9d14990966108d38fde0b3"
       payload := .apply "SymbolicWitnessDomain" [] }]

/-- One rooted source package for the optional v2 proof calculus. -/
def v2Source : GSLTSource where
  identity := v2Identity
  assumptions := { entries := [] }
  profiles := v2Profiles
  definition := TypeSystemGSLT.definition

private theorem v2Identity_valid : v2Identity.isValid = true := by
  decide

private theorem v2Assumptions_valid :
    v2Source.assumptions.isValid = true := by
  decide

private theorem v2Profiles_valid : v2Profiles.isValid = true := by
  decide

/-- The generic checker consumes the exact authored 21-rule definition
inside the pinned v2 source package. -/
def v2Checked : CheckedGSLT where
  source := v2Source
  identityValid := v2Identity_valid
  assumptionsValid := v2Assumptions_valid
  profilesValid := v2Profiles_valid
  definitionValid := TypeSystemGSLT.definition_valid

@[simp] theorem v2Checked_presentation :
    v2Checked.definition = TypeSystemGSLT.checked :=
  rfl

/-- The definition stored in the optional v2 profile is not an independent
flat checker specification: it is exactly the elaboration of the four authored
calculus layers (union membership, consistency, value typing, and guards). -/
theorem v2Source_presentation_elaborated_from_layers :
    elaborateDefinition? TypeSystemGSLT.language
        TypeSystemGSLTLayers.assembledSource =
      some v2Source.definition := by
  simpa [v2Source] using TypeSystemGSLTLayers.assembledSource_definition

/-- Consequently v2 derivability at the generic checker waist is exactly
multi-step execution in the proof-search GSLT generated from the composed
calculus.  Search produces evidence; replay by `checkRaw` remains the authority
boundary used by typed operational observations. -/
theorem v2Checked_derivation_iff_layeredProofSearch (goals : GoalState) :
    Nonempty (DerivationList v2Checked.definition goals) ↔
      (proofSearchGSLT TypeSystemGSLT.checked).MultiStep goals [] := by
  simpa using
    (TypeSystemGSLTLayers.typeSystem_conservativeExtension goals).2.2

/-- The exact rooted v2 package satisfies every executable admission
condition. -/
theorem v2Source_isValid : v2Source.isValid = true := by
  simpa [v2Checked] using CheckedGSLT.source_isValid v2Checked

/-- Executable source admission accepts the exact rooted v2 package. -/
theorem v2Source_validationAccepted :
    validationAccepted v2Source.validate = true := by
  rw [validationAccepted_validate_eq_isValid]
  exact v2Source_isValid

/-- Exact executable image of the stage-1 symbolic witness profile.  Both the
emitted value and proposed type must be closed canonical terms whose fixed
constructors belong to the authored v2 language.  An ordinary PeTTa term is
therefore outside this profile rather than silently receiving a negative
typing result. -/
def v2Covered (_final : EvalState) (answer type : Pattern) : Bool :=
  argumentValidAt 0 answer &&
    fixedConstructorsValid TypeSystemGSLT.language answer &&
    argumentValidAt 0 type &&
    fixedConstructorsValid TypeSystemGSLT.language type

/-- The v2 typing goal is independent of runtime state at stage 1.  A future
declaration-aware extension may use the `final` argument without changing the
typed-operational interface. -/
def v2Typing : TypingProfile where
  checked := v2Checked
  covered := v2Covered
  goal := fun _final answer type => valueHasType answer type

/-- The v2 profile is an optional refinement of the unchanged PeTTa core. -/
def v2Profile : Profile := .typed v2Typing

theorem v2_operational_core_unchanged :
    v2Profile.operationalGSLT = Profile.core.operationalGSLT :=
  rfl

/-- Positive end-to-end witness: the operational core emits the symbolic v2
number witness, and the generic checker validates its authored typing proof. -/
theorem v2_vNum_produces_tNum :
    producesCheckedType v2Typing tNum
      (.request EvalState.empty vNum) := by
  rw [producesCheckedType_iff_exists_checkedProof]
  let occurrence : Fin ([vNum] : Answers).length := ⟨0, by simp⟩
  refine ⟨EvalState.empty, [vNum], occurrence, ?_, ?_, hasTypeNumProof, ?_⟩
  · simpa [vNum] using
      (CoreDecl.pure EvalState.empty vNum [vNum]
        (PureDecl.ground "VNum"))
  · change v2Covered EvalState.empty vNum tNum = true
    simp [v2Covered, argumentValidAt, fixedConstructorsValid,
      fixedConstructorListsValid, languageHasConstructorArity,
      TypeSystemGSLT.language, TypeSystemGSLT.termConstructor, vNum, tNum,
      Pattern.isGroundAt, Pattern.isGroundListAt,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]
  · change checkRaw TypeSystemGSLT.checked
      (valueHasType vNum tNum) hasTypeNumProof = true
    exact value_num_has_type_number

/-- Ordinary PeTTa constructors are not silently interpreted as members of
the optional symbolic v2 witness algebra. -/
theorem v2_ordinary_petta_symbol_outside_stage1 :
    v2Covered EvalState.empty (.apply "ordinary-petta-symbol" []) tNum = false := by
  simp [v2Covered, argumentValidAt, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    TypeSystemGSLT.language, TypeSystemGSLT.termConstructor, tNum,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-- Negative checker witness: the number rule cannot be replayed as evidence
that the symbolic Boolean witness has type Number.  This is rejection of one
purported proof, not a closed-world claim that failed search refutes typing. -/
theorem v2_wrong_base_proof_rejected :
    v2Checked.checkRaw (valueHasType vTrue tNum) wrongBaseProof = false := by
  change checkRaw TypeSystemGSLT.checked
    (valueHasType vTrue tNum) wrongBaseProof = false
  exact value_true_not_number

/-- The operational run exists independently of whether the optional typing
profile recognizes the emitted value. -/
theorem v2_vTrue_operates_without_number_proof :
    CoreDecl EvalState.empty vTrue EvalState.empty [vTrue] ∧
      v2Checked.checkRaw (valueHasType vTrue tNum) wrongBaseProof = false := by
  constructor
  · simpa [vTrue] using
      (CoreDecl.pure EvalState.empty vTrue [vTrue]
        (PureDecl.ground "VTrue"))
  · exact v2_wrong_base_proof_rejected

end Mettapedia.Languages.MeTTa.PeTTa.TypedOperationalGSLT
