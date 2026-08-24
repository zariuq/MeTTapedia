import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwarePatternCodec

/-!
# The finite data language of declaration-aware Prime judgments

The exact Pattern codec for the intrinsic Prime kernel uses only the fixed
constructors declared here.  This turns its wire image into ordinary finite
`LanguageDef` data and reserves `prime-has-type` as a judgment head rather
than a term constructor.

No typing rules are imposed in this module.  Later proof calculi extend this
same validated base, so the data representation and the inference theory
cannot silently drift into separate languages.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwareDataLanguage

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwarePatternCodec
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.OSLF.MeTTaIL.Syntax

def kernelDataType : TypeDecl := TypeDecl.plain "PrimeKernelData"

def dataConstructor (head : String) (arity : Nat) : GrammarRule :=
  { label := head
    category := "PrimeKernelData"
    params := (List.range arity).map fun index =>
      .simple s!"field{index}" (.base "PrimeKernelData")
    syntaxPattern := [] }

/-- The entire fixed constructor alphabet used by the exact intrinsic codec.
The judgment head is deliberately absent. -/
def constructorArities : List (String × Nat) :=
  [ ("prime-nat-zero", 0),
    ("prime-nat-succ", 1),
    ("prime-string-nil", 0),
    ("prime-string-cons", 2),
    ("prime-name-anonymous", 0),
    ("prime-name-string", 2),
    ("prime-name-number", 2),
    ("prime-level-const", 1),
    ("prime-level-param", 1),
    ("prime-level-succ", 1),
    ("prime-level-max", 2),
    ("prime-head-legacy-ground", 0),
    ("prime-head-sort", 1),
    ("prime-tm-var", 1),
    ("prime-tm-const", 1),
    ("prime-tm-head", 1),
    ("prime-tm-pi", 2),
    ("prime-tm-sigma", 2),
    ("prime-tm-id", 3),
    ("prime-tm-lam", 1),
    ("prime-tm-app", 2),
    ("prime-tm-pair", 2),
    ("prime-tm-fst", 1),
    ("prime-tm-snd", 1),
    ("prime-tm-refl", 1),
    ("prime-ctx-nil", 0),
    ("prime-ctx-snoc", 2) ]

def definition : CalculusLanguageDef :=
  { name := "prime-declaration-aware-data-v1"
    types := [kernelDataType]
    terms := constructorArities.map fun specification =>
      dataConstructor specification.1 specification.2
    equations := []
    rewrites := []
    judgments := [{ head := "prime-has-type", arity := 4 }]
    rules := [] }

def language : LanguageDef := definition.toLanguageDef
def presentation : Presentation := definition.toNested

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly language <;>
    simp [language, definition, constructorArities, kernelDataType,
      dataConstructor, LanguageDef.typeNames, TypeDecl.plain,
      TermParam.typeExpr, TypeExpr.baseNames]

theorem presentation_valid : presentation.isValidV2 = true := by
  have validatedLanguage : presentation.language.validate = [] := by
    simpa [presentation, language] using language_validate
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [validatedLanguage]
  simp [presentation, definition, constructorArities,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.conversionDeclarationValid,
    Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, kernelDataType, dataConstructor]
  decide

def checked : ValidatedPresentation := ⟨presentation, presentation_valid⟩

/-! The finite signature is exposed through small availability facts.  Codec
inductions use these facts without repeatedly unfolding the whole table. -/

@[simp] theorem has_nat_zero :
    languageHasConstructorArity language "prime-nat-zero" 0 = true := by decide
@[simp] theorem has_nat_succ :
    languageHasConstructorArity language "prime-nat-succ" 1 = true := by decide
@[simp] theorem has_string_nil :
    languageHasConstructorArity language "prime-string-nil" 0 = true := by decide
@[simp] theorem has_string_cons :
    languageHasConstructorArity language "prime-string-cons" 2 = true := by decide
@[simp] theorem has_name_anonymous :
    languageHasConstructorArity language "prime-name-anonymous" 0 = true := by decide
@[simp] theorem has_name_string :
    languageHasConstructorArity language "prime-name-string" 2 = true := by decide
@[simp] theorem has_name_number :
    languageHasConstructorArity language "prime-name-number" 2 = true := by decide
@[simp] theorem has_level_const :
    languageHasConstructorArity language "prime-level-const" 1 = true := by decide
@[simp] theorem has_level_param :
    languageHasConstructorArity language "prime-level-param" 1 = true := by decide
@[simp] theorem has_level_succ :
    languageHasConstructorArity language "prime-level-succ" 1 = true := by decide
@[simp] theorem has_level_max :
    languageHasConstructorArity language "prime-level-max" 2 = true := by decide
@[simp] theorem has_head_legacy_ground :
    languageHasConstructorArity language "prime-head-legacy-ground" 0 = true := by decide
@[simp] theorem has_head_sort :
    languageHasConstructorArity language "prime-head-sort" 1 = true := by decide
@[simp] theorem has_tm_var :
    languageHasConstructorArity language "prime-tm-var" 1 = true := by decide
@[simp] theorem has_tm_const :
    languageHasConstructorArity language "prime-tm-const" 1 = true := by decide
@[simp] theorem has_tm_head :
    languageHasConstructorArity language "prime-tm-head" 1 = true := by decide
@[simp] theorem has_tm_pi :
    languageHasConstructorArity language "prime-tm-pi" 2 = true := by decide
@[simp] theorem has_tm_sigma :
    languageHasConstructorArity language "prime-tm-sigma" 2 = true := by decide
@[simp] theorem has_tm_id :
    languageHasConstructorArity language "prime-tm-id" 3 = true := by decide
@[simp] theorem has_tm_lam :
    languageHasConstructorArity language "prime-tm-lam" 1 = true := by decide
@[simp] theorem has_tm_app :
    languageHasConstructorArity language "prime-tm-app" 2 = true := by decide
@[simp] theorem has_tm_pair :
    languageHasConstructorArity language "prime-tm-pair" 2 = true := by decide
@[simp] theorem has_tm_fst :
    languageHasConstructorArity language "prime-tm-fst" 1 = true := by decide
@[simp] theorem has_tm_snd :
    languageHasConstructorArity language "prime-tm-snd" 1 = true := by decide
@[simp] theorem has_tm_refl :
    languageHasConstructorArity language "prime-tm-refl" 1 = true := by decide
@[simp] theorem has_ctx_nil :
    languageHasConstructorArity language "prime-ctx-nil" 0 = true := by decide
@[simp] theorem has_ctx_snoc :
    languageHasConstructorArity language "prime-ctx-snoc" 2 = true := by decide

@[simp] theorem fixed_encodeNat (value : Nat) :
    fixedConstructorsValid language (encodeNat value) = true := by
  induction value with
  | zero =>
      simp [encodeNat, fixedConstructorsValid, fixedConstructorListsValid]
  | succ value ih =>
      simp [encodeNat, fixedConstructorsValid, fixedConstructorListsValid, ih]

@[simp] theorem fixed_encodeChars (characters : List Char) :
    fixedConstructorsValid language (encodeChars characters) = true := by
  induction characters with
  | nil =>
      simp [encodeChars, fixedConstructorsValid, fixedConstructorListsValid]
  | cons character rest ih =>
      simp [encodeChars, fixedConstructorsValid, fixedConstructorListsValid,
        fixed_encodeNat, ih]

@[simp] theorem fixed_encodeDeclName (name : Lean.Name) :
    fixedConstructorsValid language (encodeDeclName name) = true := by
  induction name with
  | anonymous =>
      simp [encodeDeclName, fixedConstructorsValid, fixedConstructorListsValid]
  | str pre component ih =>
      simp [encodeDeclName, encodeString, fixedConstructorsValid,
        fixedConstructorListsValid, fixed_encodeChars, ih]
  | num pre component ih =>
      simp [encodeDeclName, fixedConstructorsValid,
        fixedConstructorListsValid, fixed_encodeNat, ih]

@[simp] theorem fixed_encodeLevel (level : LevelExpr) :
    fixedConstructorsValid language (encodeLevel level) = true := by
  induction level with
  | const value =>
      simp [encodeLevel, fixedConstructorsValid, fixedConstructorListsValid,
        fixed_encodeNat]
  | param index =>
      simp [encodeLevel, fixedConstructorsValid, fixedConstructorListsValid,
        fixed_encodeNat]
  | succ level ih =>
      simp [encodeLevel, fixedConstructorsValid, fixedConstructorListsValid,
        ih]
  | max left right leftIH rightIH =>
      simp [encodeLevel, fixedConstructorsValid, fixedConstructorListsValid,
        leftIH, rightIH]

@[simp] theorem fixed_encodeTowerHead (head : Tower.Head) :
    fixedConstructorsValid language (encodeTowerHead head) = true := by
  cases head with
  | legacyGround =>
      simp [encodeTowerHead, fixedConstructorsValid,
        fixedConstructorListsValid]
  | sort level =>
      simp [encodeTowerHead, fixedConstructorsValid,
        fixedConstructorListsValid, fixed_encodeLevel]

@[simp] theorem fixed_encodeTm {n : Nat} (term : Tower.Tm n) :
    fixedConstructorsValid language (encodeTm towerHeadCodec term) = true := by
  induction term with
  | var index =>
      simp [encodeTm, fixedConstructorsValid, fixedConstructorListsValid,
        fixed_encodeNat]
  | const name =>
      simp [encodeTm, fixedConstructorsValid, fixedConstructorListsValid,
        fixed_encodeDeclName]
  | head head =>
      simp [encodeTm, towerHeadCodec, fixedConstructorsValid,
        fixedConstructorListsValid, fixed_encodeTowerHead]
  | pi domain body domainIH bodyIH =>
      simp [encodeTm, fixedConstructorsValid, fixedConstructorListsValid,
        domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [encodeTm, fixedConstructorsValid, fixedConstructorListsValid,
        domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [encodeTm, fixedConstructorsValid, fixedConstructorListsValid,
        typeIH, leftIH, rightIH]
  | lam body bodyIH =>
      simp [encodeTm, fixedConstructorsValid, fixedConstructorListsValid,
        bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encodeTm, fixedConstructorsValid, fixedConstructorListsValid,
        functionIH, argumentIH]
  | pair first second firstIH secondIH =>
      simp [encodeTm, fixedConstructorsValid, fixedConstructorListsValid,
        firstIH, secondIH]
  | fst pair pairIH =>
      simp [encodeTm, fixedConstructorsValid, fixedConstructorListsValid,
        pairIH]
  | snd pair pairIH =>
      simp [encodeTm, fixedConstructorsValid, fixedConstructorListsValid,
        pairIH]
  | refl term termIH =>
      simp [encodeTm, fixedConstructorsValid, fixedConstructorListsValid,
        termIH]

@[simp] theorem fixed_encodeCtx {n : Nat} (context : Tower.Ctx n) :
    fixedConstructorsValid language (encodeCtx towerHeadCodec context) = true := by
  induction context with
  | nil =>
      simp [encodeCtx, fixedConstructorsValid, fixedConstructorListsValid]
  | snoc context type contextIH =>
      simp [encodeCtx, fixedConstructorsValid, fixedConstructorListsValid,
        contextIH, fixed_encodeTm]

/-- Every exact intrinsic typing claim is a well-shaped judgment over this
finite language.  This is the representation-side premise needed by every
subsequent Prime inference-rule adequacy theorem. -/
theorem encodeTowerTypingClaim_judgmentSchemaValid
    (claim : TypingClaim Tower.Head) :
    presentation.judgmentSchemaValid
        (encodeTypingClaim towerHeadCodec claim) = true := by
  cases claim with
  | mk arity context subject type =>
      change
        ((presentation.lookupJudgment? "prime-has-type" 4).isSome &&
          fixedConstructorListsValid language
            [encodeNat arity, encodeCtx towerHeadCodec context,
              encodeTm towerHeadCodec subject,
              encodeTm towerHeadCodec type]) = true
      have lookup :
          (presentation.lookupJudgment? "prime-has-type" 4).isSome = true := by
        decide
      rw [lookup]
      simp [fixedConstructorListsValid, fixed_encodeNat, fixed_encodeCtx,
        fixed_encodeTm]

/-- Negative control: using the judgment head as ordinary nested data is not
licensed by the term language. -/
theorem judgmentHead_is_not_dataConstructor :
    languageHasConstructorArity language "prime-has-type" 4 = false := by
  decide

#print axioms presentation_valid
#print axioms encodeTowerTypingClaim_judgmentSchemaValid
#print axioms judgmentHead_is_not_dataConstructor

end Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwareDataLanguage
