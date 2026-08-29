import Mettapedia.GSLT.LanguageDef.ExtensionComposition
import Mettapedia.GSLT.LanguageDef.CalculusAsLanguage

/-!
# Authored calculus extension

`CalculusLanguageDef` is the canonical flat language object obtained by
extending an ordinary `LanguageDef` with an authored proof calculus.  The
operation is conservative on the object language by projection, but it is not
semantically inert:

1. an authored calculus document is a term of `calculusSyntaxGSLT`;
2. its equations and rewrites preserve elaboration;
3. elaboration produces one flat `CalculusLanguageDef`;
4. admission checks that component against the unchanged object language;
5. the admitted definition induces `proofSearchGSLT`, whose rewrites are
   exactly rule applications and whose reachability is equivalent to
   derivability.

Thus judgments and inference rules reduce to `(T,E,R)` at the meta-level.  No
opaque checker behavior is postulated beside the GSLT, and clients never carry
a nested base/calculus pair.
-/

namespace Mettapedia.GSLT.LanguageDef.CalculusExtension

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Calculus-authoring GSLTs -/

/-- A calculus-authoring GSLT is one free document over the authored
calculus-declaration generators, with exact elaboration to `ProofCalculus`.
The generator system remains available for flat composition; the document
closure is derived rather than nested by callers. -/
abbrev CalculusAuthoringGSLT :=
  GSLT.FreeDocumentElaboration ProofCalculus

namespace CalculusAuthoringGSLT

/-- Regard one calculus-authoring GSLT as a base-independent flat layer over
exact five-field language definitions. -/
def authoringLayer (system : CalculusAuthoringGSLT) :
    FreeDocumentLayer LanguageDef :=
  FreeDocumentLayer.constant LanguageDef system

/-- Forget only the flat generator boundary at the ordinary coGSLT interface. -/
def toLayer (system : CalculusAuthoringGSLT) : CoGSLTLayer LanguageDef :=
  system.authoringLayer.toCoGSLTLayer

end CalculusAuthoringGSLT

/-- The canonical proof-calculus declaration language, with concatenation and
its exact elaboration packaged as one reusable class. -/
def canonicalCalculusAuthoringGSLT : CalculusAuthoringGSLT :=
  calculusAuthoringGSLT

/-- Forgetting the canonical generator boundary yields exactly the general
compositional extension interface. -/
@[simp] theorem canonicalCalculusAuthoringGSLT_toCompositionalElaboration
    (language : LanguageDef) :
    canonicalCalculusAuthoringGSLT.toCompositionalElaboration =
      calculusLayer.system language :=
  rfl

@[simp] theorem canonicalCalculusAuthoringGSLT_source (language : LanguageDef) :
    canonicalCalculusAuthoringGSLT.toLayer.sourceGSLT language =
      calculusSyntaxGSLT :=
  rfl

@[simp] theorem canonicalCalculusAuthoringGSLT_elaborate
    (language : LanguageDef) (source : CalculusSyntax) :
    canonicalCalculusAuthoringGSLT.toLayer.elaborate language source =
      elaborate source :=
  rfl

@[simp] theorem canonicalCalculusAuthoringGSLT_quote
    (language : LanguageDef) (calculus : ProofCalculus) :
    canonicalCalculusAuthoringGSLT.toLayer.quote language calculus = quote calculus :=
  rfl

/-- Elaborate an authored calculus document and attach it to an unchanged
five-field object-language definition. -/
def elaborateDefinition? (language : LanguageDef) (source : CalculusSyntax) :
    Option CalculusLanguageDef :=
  (elaborate source).map (CalculusLanguageDef.extend language)

/-- Canonical calculus syntax elaborates to the named conservative extension
object. -/
@[simp] theorem elaborateDefinition?_quote (language : LanguageDef)
    (calculus : ProofCalculus) :
    elaborateDefinition? language (quote calculus) =
      some (CalculusLanguageDef.extend language calculus) := by
  simp [elaborateDefinition?]

/-- The canonical authored GSLT document corresponding to an extended
language definition.  This is a retraction into the calculus authoring
language, not a second proof-calculus representation. -/
def authoredSource (definition : CalculusLanguageDef) : CalculusSyntax :=
  quote definition.toCalculus

/-- Every directly constructed calculus extension is denoted by an exact term
of the authored calculus GSLT. -/
@[simp] theorem elaborate_authoredSource (definition : CalculusLanguageDef) :
    elaborate (authoredSource definition) = some definition.toCalculus := by
  simp [authoredSource]

/-- Elaborating the canonical authored document recovers the whole extended
definition, including its unchanged five-field base. -/
@[simp] theorem elaborateDefinition?_authoredSource
    (definition : CalculusLanguageDef) :
    elaborateDefinition? definition.toLanguageDef (authoredSource definition) =
      some definition := by
  simp [elaborateDefinition?, authoredSource]

/-- The generic grounding certificate for flat calculus language definitions:
their calculus is the elaboration of a term of `calculusSyntaxGSLT`, while
projection recovers the exact object language. -/
theorem authored_grounding (definition : CalculusLanguageDef) :
    elaborate (authoredSource definition) = some definition.toCalculus ∧
      CalculusLanguageDef.extend definition.toLanguageDef
          definition.toCalculus = definition :=
  ⟨elaborate_authoredSource definition, CalculusLanguageDef.extend_eta definition⟩

/-- Successful elaboration cannot alter the object-language base. -/
theorem erase_of_elaborateDefinition?_eq_some
    {language : LanguageDef} {source : CalculusSyntax}
    {definition : CalculusLanguageDef}
    (elaborated : elaborateDefinition? language source = some definition) :
    definition.toLanguageDef = language := by
  unfold elaborateDefinition? at elaborated
  cases result : elaborate source with
  | none => simp [result] at elaborated
  | some calculus =>
      simp [result] at elaborated
      subst definition
      rfl

/-- Successful attachment contains exactly the calculus denoted by the
authored document. -/
theorem calculus_of_elaborateDefinition?_eq_some
    {language : LanguageDef} {source : CalculusSyntax}
    {definition : CalculusLanguageDef}
    (elaborated : elaborateDefinition? language source = some definition) :
    elaborate source = some definition.toCalculus := by
  unfold elaborateDefinition? at elaborated
  cases result : elaborate source with
  | none => simp [result] at elaborated
  | some calculus =>
      simp [result] at elaborated
      subst definition
      rfl

/-- Object-language observations lifted through erasure are definitionally
conservative. -/
theorem baseObservation_conservative {Observation : Type*}
    (observe : LanguageDef → Observation) (definition : CalculusLanguageDef) :
    observe (CalculusLanguageDef.extend definition.toLanguageDef
      definition.toCalculus).toLanguageDef = observe definition.toLanguageDef :=
  rfl

/-- Equated authored documents elaborate to the same conservative extension. -/
theorem elaborateDefinition?_eq_of_equation (language : LanguageDef)
    {source target : CalculusSyntax}
    (equivalent : calculusSyntaxGSLT.Equiv source target) :
    elaborateDefinition? language source =
      elaborateDefinition? language target := by
  unfold elaborateDefinition?
  rw [elaborate_equation equivalent]

/-- An authored syntax rewrite cannot change the conservative extension it
denotes. -/
theorem elaborateDefinition?_eq_of_rewrite (language : LanguageDef)
    {source target : CalculusSyntax}
    (step : calculusSyntaxGSLT.Step source target) :
    elaborateDefinition? language source =
      elaborateDefinition? language target := by
  unfold elaborateDefinition?
  rw [elaborate_rewrite step]

/-- Elaborate and then run the contextual admission check. -/
def admit? (language : LanguageDef) (source : CalculusSyntax) :
    Option ValidatedCalculusLanguageDef := do
  let definition ← elaborateDefinition? language source
  definition.validate?

/-- Admission is invariant under authored equations. -/
theorem admit?_eq_of_equation (language : LanguageDef)
    {source target : CalculusSyntax}
    (equivalent : calculusSyntaxGSLT.Equiv source target) :
    admit? language source = admit? language target := by
  unfold admit?
  rw [elaborateDefinition?_eq_of_equation language equivalent]

/-- Admission is invariant under authored syntax rewrites. -/
theorem admit?_eq_of_rewrite (language : LanguageDef)
    {source target : CalculusSyntax}
    (step : calculusSyntaxGSLT.Step source target) :
    admit? language source = admit? language target := by
  unfold admit?
  rw [elaborateDefinition?_eq_of_rewrite language step]

/-- A successfully admitted authored definition still has the exact base with
which admission began. -/
theorem admitted_erase_eq {language : LanguageDef} {source : CalculusSyntax}
    {checked : ValidatedCalculusLanguageDef}
    (admitted : admit? language source = some checked) :
    checked.1.toLanguageDef = language := by
  unfold admit? at admitted
  change (elaborateDefinition? language source).bind
      CalculusLanguageDef.validate? = some checked at admitted
  rw [Option.bind_eq_some_iff] at admitted
  obtain ⟨definition, elaborated, validated⟩ := admitted
  have erased := erase_of_elaborateDefinition?_eq_some elaborated
  unfold CalculusLanguageDef.validate? at validated
  split at validated
  · cases validated
    exact erased
  · simp at validated

/-- Successful admission also retains the exact elaborated calculus. -/
theorem admitted_calculus_eq {language : LanguageDef}
    {source : CalculusSyntax} {checked : ValidatedCalculusLanguageDef}
    (admitted : admit? language source = some checked) :
    elaborate source = some checked.1.toCalculus := by
  unfold admit? at admitted
  change (elaborateDefinition? language source).bind
      CalculusLanguageDef.validate? = some checked at admitted
  rw [Option.bind_eq_some_iff] at admitted
  obtain ⟨definition, elaborated, validated⟩ := admitted
  have calculus := calculus_of_elaborateDefinition?_eq_some elaborated
  unfold CalculusLanguageDef.validate? at validated
  split at validated
  · cases validated
    exact calculus
  · simp at validated

/-- **The conservative-extension square.**  A successfully admitted authored
calculus preserves its exact five-field base, retains exactly the calculus
denoted by the source GSLT, and reduces derivability to reachability in the
derived proof-search GSLT. -/
theorem admitted_source_adequacy {language : LanguageDef}
    {source : CalculusSyntax} {checked : ValidatedCalculusLanguageDef}
    (admitted : admit? language source = some checked)
    (goals : GoalState) :
    checked.1.toLanguageDef = language ∧
      elaborate source = some checked.1.toCalculus ∧
      (Nonempty (DerivationList checked goals) ↔
        (proofSearchGSLT checked).MultiStep goals []) :=
  ⟨admitted_erase_eq admitted, admitted_calculus_eq admitted,
    derivationList_nonempty_iff_proofSearch checked goals⟩

/-! ## Admission and realization as canonical layers -/

/-- A proof calculus admitted over one exact five-field language definition.
This is the contextual fibre of the existing `ValidatedCalculusLanguageDef`,
not a second language representation. -/
abbrev AdmittedCalculusAt (language : LanguageDef) :=
  { calculus : ProofCalculus //
    (CalculusLanguageDef.extend language calculus).isValid = true }

namespace AdmittedCalculusAt

/-- Flatten one point of the admitted calculus fibre into the checked language
object consumed by the generic inference checker. -/
def checked (language : LanguageDef) (calculus : AdmittedCalculusAt language) :
    ValidatedCalculusLanguageDef :=
  ⟨CalculusLanguageDef.extend language calculus.1, calculus.2⟩

@[simp] theorem checked_language (language : LanguageDef)
    (calculus : AdmittedCalculusAt language) :
    (calculus.checked language).1.toLanguageDef = language :=
  rfl

@[simp] theorem checked_calculus (language : LanguageDef)
    (calculus : AdmittedCalculusAt language) :
    (calculus.checked language).1.toCalculus = calculus.1 :=
  rfl

end AdmittedCalculusAt

/-- Elaborate an authored calculus and retain it exactly when contextual
admission succeeds.  The gate is the existing `CalculusLanguageDef.isValid`; this
definition merely exposes its dependent fibre. -/
def admitCalculus? (language : LanguageDef) (source : CalculusSyntax) :
    Option (AdmittedCalculusAt language) := do
  let calculus ← elaborate source
  if valid : (CalculusLanguageDef.extend language calculus).isValid = true then
    some ⟨calculus, valid⟩
  else
    none

@[simp] theorem admitCalculus?_quote (language : LanguageDef)
    (calculus : AdmittedCalculusAt language) :
    admitCalculus? language (quote calculus.1) = some calculus := by
  cases calculus with
  | mk calculus valid =>
      simp [admitCalculus?, valid]

/-- The dependent admission layer and the established checker gate are the
same computation.  Mapping a fibre point back to `ValidatedCalculusLanguageDef`
recovers `admit?` exactly. -/
theorem admit?_eq_map_admitCalculus? (language : LanguageDef)
    (source : CalculusSyntax) :
    admit? language source =
      (admitCalculus? language source).map
        (AdmittedCalculusAt.checked language) := by
  cases elaborated : elaborate source with
  | none =>
      simp [admit?, elaborateDefinition?, admitCalculus?, elaborated]
  | some calculus =>
      by_cases valid :
          (CalculusLanguageDef.extend language calculus).isValid = true
      · simp [admit?, elaborateDefinition?, admitCalculus?, elaborated,
          CalculusLanguageDef.validate?, valid, AdmittedCalculusAt.checked]
      · simp [admit?, elaborateDefinition?, admitCalculus?, elaborated,
          CalculusLanguageDef.validate?, valid]

/-- Contextual admission itself is a coGSLT layer.  Its authored terms are
the same calculus-declaration terms; only the fibre is restricted to
admitted payloads. -/
def calculusAdmissionLayer : CoGSLTLayer LanguageDef where
  Fiber := AdmittedCalculusAt
  sourceGSLT := fun _ => calculusSyntaxGSLT
  elaborate := admitCalculus?
  quote := fun _ calculus => quote calculus.1
  elaborate_quote := admitCalculus?_quote
  elaborate_equation := by
    intro language source target equivalent
    unfold admitCalculus?
    rw [elaborate_equation equivalent]
  elaborate_rewrite := by
    intro language source target step
    unfold admitCalculus?
    rw [elaborate_rewrite step]

/-- The semantic observation shared by proof-search realizations: which
ordered goal lists are accepted. -/
abbrev ProofSearchObservation := GoalState → Prop

/-- **Proof search is the canonical certified realization of an admitted
calculus.**  Compilation maps the calculus to the acceptance relation induced
by its proof-search GSLT.  Adequacy is the independently proved equivalence
between derivation inhabitation and reachability of the empty goal state. -/
def proofSearchRealization :
    CoGSLTLayer.Realization calculusAdmissionLayer
      (fun _ => ProofSearchObservation)
      (fun _ => ProofSearchObservation) where
  compile := fun language calculus goals =>
    (proofSearchGSLT (calculus.checked language)).MultiStep goals []
  observeSource := fun language calculus goals =>
    Nonempty (DerivationList (calculus.checked language) goals)
  observeArtifact := fun _ artifact => artifact
  adequate := by
    intro language calculus
    funext goals
    exact propext
      (derivationList_nonempty_iff_proofSearch
        (calculus.checked language) goals).symm

/-- The realization's certificate, pointwise: compiled proof search accepts
exactly the derivable ordered goal lists. -/
theorem proofSearchRealization_adequate (language : LanguageDef)
    (calculus : AdmittedCalculusAt language) (goals : GoalState) :
    proofSearchRealization.compile language calculus goals ↔
      Nonempty (DerivationList (calculus.checked language) goals) := by
  exact derivationList_nonempty_iff_proofSearch
    (calculus.checked language) goals |>.symm

/-! ## Positive and negative canaries -/

private def canaryLanguage : LanguageDef :=
  LanguageDef.empty "calculus-extension-canary"

private def canaryJudgment : JudgmentDecl := ⟨"Provable", 0⟩

private def canaryRule : RuleSchema :=
  { id := ⟨"provable"⟩
    metavariables := []
    premises := []
    conclusion := .apply "Provable" [] }

private def canaryCalculus : ProofCalculus :=
  { judgments := [canaryJudgment], rules := [canaryRule] }

private def canarySource : CalculusSyntax := quote canaryCalculus

private theorem canaryValid :
    (CalculusLanguageDef.extend canaryLanguage canaryCalculus).isValid = true := by
  have languageValid : canaryLanguage.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [canaryLanguage, LanguageDef.empty, LanguageDef.typeNames]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp only [CalculusLanguageDef.extend]
  rw [languageValid]
  simp [canaryCalculus, canaryJudgment, canaryRule,
    canaryLanguage, LanguageDef.empty,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid,
    fixedConstructorListsValid, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  constructor <;> decide

private def canaryChecked : ValidatedCalculusLanguageDef :=
  ⟨CalculusLanguageDef.extend canaryLanguage canaryCalculus, canaryValid⟩

private def canaryAdmittedCalculus : AdmittedCalculusAt canaryLanguage :=
  ⟨canaryCalculus, canaryValid⟩

private theorem canaryAdmitted :
    admit? canaryLanguage canarySource = some canaryChecked := by
  simp [admit?, canarySource, elaborateDefinition?, canaryChecked,
    CalculusLanguageDef.validate?, canaryValid]

/-- Positive: an authored zero-premise rule becomes a genuine proof-search
rewrite and derives its judgment. -/
theorem canary_proofSearch_accepts :
    (proofSearchGSLT canaryChecked).MultiStep
      [.apply "Provable" []] [] := by
  have oneStep :
      (proofSearchGSLT canaryChecked).Step
        [.apply "Provable" []] [] := by
    apply
      (proofSearchGSLT_step_iff_instantiation canaryChecked
        [.apply "Provable" []] []).mpr
    refine ⟨{ ruleId := ⟨"provable"⟩, arguments := [] },
      [], .apply "Provable" [], [], ?_, rfl, rfl⟩
    simp [instantiateRule?, canaryChecked, canaryCalculus, canaryRule,
      CalculusLanguageDef.extend, CalculusLanguageDef.lookupRule?,
      argumentsValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
      instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?]
  exact .step oneStep
    (@GSLT.MultiStep.refl (proofSearchGSLT canaryChecked) [])

/-- The same positive witness passes through the generic realization
interface: this is an actual certified instance, not a standalone adequacy
theorem beside the class hierarchy. -/
theorem canary_realization_accepts :
    proofSearchRealization.compile canaryLanguage canaryAdmittedCalculus
      [.apply "Provable" []] := by
  simpa [proofSearchRealization, canaryAdmittedCalculus,
    AdmittedCalculusAt.checked, canaryChecked] using
    canary_proofSearch_accepts

private def undeclaredCalculus : ProofCalculus :=
  { rules := [canaryRule] }

private theorem undeclaredInvalid :
    (CalculusLanguageDef.extend canaryLanguage undeclaredCalculus).isValid = false := by
  have languageValid : canaryLanguage.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [canaryLanguage, LanguageDef.empty, LanguageDef.typeNames]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp only [CalculusLanguageDef.extend]
  rw [languageValid]
  simp [undeclaredCalculus, canaryRule, canaryLanguage, LanguageDef.empty,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.lookupJudgment?,
    CalculusLanguageDef.judgmentSchemaValid, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    fixedConstructorListsValid, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]

/-- Negative: an undeclared judgment is rejected by admission rather than
silently becoming a proof-search language. -/
example :
    admit? canaryLanguage
      (quote undeclaredCalculus) = none := by
  unfold admit?
  rw [elaborateDefinition?_quote]
  simp [CalculusLanguageDef.validate?, undeclaredInvalid]

/-- The canonical admission layer rejects the same malformed calculus, so a
realization cannot compile it through `compileTerm?`. -/
theorem undeclared_calculusAdmission_rejected :
    calculusAdmissionLayer.elaborate canaryLanguage
      (quote undeclaredCalculus) = none := by
  simp [calculusAdmissionLayer, admitCalculus?, undeclaredInvalid]

end Mettapedia.GSLT.LanguageDef.CalculusExtension
