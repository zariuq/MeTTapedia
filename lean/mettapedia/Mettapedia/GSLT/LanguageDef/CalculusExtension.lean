import Mettapedia.GSLT.LanguageDef.ExtensionComposition
import Mettapedia.GSLT.LanguageDef.CalculusAsLanguage

/-!
# Conservative checker definitions

`Presentation` is the checker-facing nested object obtained by attaching a
proof calculus to an exact five-field `LanguageDef`.  The attachment is conservative
on the object language by erasure, but it is not semantically inert:

1. an authored calculus document is a term of `calculusSyntaxGSLT`;
2. its equations and rewrites preserve elaboration;
3. elaboration produces the calculus component of a `Presentation`;
4. admission checks that component against the unchanged object language;
5. the admitted definition induces `proofSearchGSLT`, whose rewrites are
   exactly rule applications and whose reachability is equivalent to
   derivability.

Thus judgments and inference rules reduce to `(T,E,R)` at the meta-level.  No
judgment or rule field is added to the five-field object-language definition,
and no opaque checker behavior is postulated beside the GSLT.
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

/-- A calculus-authoring GSLT is precisely a compositional elaboration whose
payload is `ProofCalculus`; it is a specialization of the general class, not a
parallel calculus representation. -/
abbrev CalculusAuthoringGSLT :=
  GSLT.CompositionalElaboration ProofCalculus

namespace CalculusAuthoringGSLT

/-- Every calculus-authoring GSLT induces a dependent coGSLT layer over exact
five-field language definitions. -/
def toLayer (system : CalculusAuthoringGSLT) : CoGSLTLayer LanguageDef where
  Fiber := fun _ => ProofCalculus
  sourceGSLT := fun _ => system.authoring.theory
  elaborate := fun _ => system.elaboration.elaborate
  quote := fun _ => system.elaboration.quote
  elaborate_quote := fun _ => system.elaboration.elaborate_quote
  elaborate_equation := fun _ => system.elaboration.equation
  elaborate_rewrite := fun _ => system.elaboration.rewrite

end CalculusAuthoringGSLT

/-- The canonical proof-calculus declaration language, with concatenation and
its exact elaboration packaged as one reusable class. -/
def canonicalCalculusAuthoringGSLT : CalculusAuthoringGSLT :=
  calculusAuthoringGSLT

/-- The admitted-calculus interface and the general compositional extension
layer share the same authoring object definitionally. -/
@[simp] theorem canonicalCalculusAuthoringGSLT_eq_calculusLayer
    (language : LanguageDef) :
    canonicalCalculusAuthoringGSLT = calculusLayer.system language :=
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
    Option Presentation :=
  (elaborate source).map fun calculus => { language, calculus }

/-- Canonical calculus syntax elaborates to the named conservative extension
object. -/
@[simp] theorem elaborateDefinition?_quote (language : LanguageDef)
    (calculus : ProofCalculus) :
    elaborateDefinition? language (quote calculus) =
      some ({ language, calculus } : Presentation) := by
  simp [elaborateDefinition?]

/-- The canonical authored GSLT document corresponding to an extended
language definition.  This is a retraction into the calculus authoring
language, not a second proof-calculus representation. -/
def authoredSource (definition : Presentation) : CalculusSyntax :=
  quote definition.calculus

/-- Every directly constructed calculus extension is denoted by an exact term
of the authored calculus GSLT. -/
@[simp] theorem elaborate_authoredSource (definition : Presentation) :
    elaborate (authoredSource definition) = some definition.calculus := by
  simp [authoredSource]

/-- Elaborating the canonical authored document recovers the whole extended
definition, including its unchanged five-field base. -/
@[simp] theorem elaborateDefinition?_authoredSource
    (definition : Presentation) :
    elaborateDefinition? definition.language (authoredSource definition) =
      some definition := by
  cases definition
  simp [authoredSource]

/-- The generic grounding certificate for checker-facing presentations:
their calculus is the elaboration of a term of `calculusSyntaxGSLT`, and
erasing the attached fibre recovers the exact object language. -/
theorem authored_grounding (definition : Presentation) :
    elaborate (authoredSource definition) = some definition.calculus ∧
      definition.erase = definition.language :=
  ⟨elaborate_authoredSource definition, rfl⟩

/-- Successful elaboration cannot alter the object-language base. -/
theorem erase_of_elaborateDefinition?_eq_some
    {language : LanguageDef} {source : CalculusSyntax}
    {definition : Presentation}
    (elaborated : elaborateDefinition? language source = some definition) :
    definition.erase = language := by
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
    {definition : Presentation}
    (elaborated : elaborateDefinition? language source = some definition) :
    elaborate source = some definition.calculus := by
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
    (observe : LanguageDef → Observation) (definition : Presentation) :
    observe definition.erase = observe definition.language :=
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
    Option ValidatedPresentation := do
  let definition ← elaborateDefinition? language source
  definition.validateV2?

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
    {checked : ValidatedPresentation}
    (admitted : admit? language source = some checked) :
    checked.1.erase = language := by
  unfold admit? at admitted
  change (elaborateDefinition? language source).bind
      Presentation.validateV2? = some checked at admitted
  rw [Option.bind_eq_some_iff] at admitted
  obtain ⟨definition, elaborated, validated⟩ := admitted
  have erased := erase_of_elaborateDefinition?_eq_some elaborated
  unfold Presentation.validateV2? at validated
  split at validated
  · cases validated
    exact erased
  · simp at validated

/-- Successful admission also retains the exact elaborated calculus. -/
theorem admitted_calculus_eq {language : LanguageDef}
    {source : CalculusSyntax} {checked : ValidatedPresentation}
    (admitted : admit? language source = some checked) :
    elaborate source = some checked.1.calculus := by
  unfold admit? at admitted
  change (elaborateDefinition? language source).bind
      Presentation.validateV2? = some checked at admitted
  rw [Option.bind_eq_some_iff] at admitted
  obtain ⟨definition, elaborated, validated⟩ := admitted
  have calculus := calculus_of_elaborateDefinition?_eq_some elaborated
  unfold Presentation.validateV2? at validated
  split at validated
  · cases validated
    exact calculus
  · simp at validated

/-- **The conservative-extension square.**  A successfully admitted authored
calculus preserves its exact five-field base, retains exactly the calculus
denoted by the source GSLT, and reduces derivability to reachability in the
derived proof-search GSLT. -/
theorem admitted_source_adequacy {language : LanguageDef}
    {source : CalculusSyntax} {checked : ValidatedPresentation}
    (admitted : admit? language source = some checked)
    (goals : GoalState) :
    checked.1.erase = language ∧
      elaborate source = some checked.1.calculus ∧
      (Nonempty (DerivationList checked goals) ↔
        (proofSearchGSLT checked).MultiStep goals []) :=
  ⟨admitted_erase_eq admitted, admitted_calculus_eq admitted,
    derivationList_nonempty_iff_proofSearch checked goals⟩

/-! ## Admission and realization as canonical layers -/

/-- A proof calculus admitted over one exact five-field language definition.
This is the contextual fibre of the existing `ValidatedPresentation`, not a
second presentation record. -/
abbrev AdmittedCalculusAt (language : LanguageDef) :=
  { calculus : ProofCalculus //
    (Presentation.mk language calculus).isValidV2 = true }

namespace AdmittedCalculusAt

/-- Recover the established checker-facing validated presentation from one
point of the admitted calculus fibre. -/
def checked (language : LanguageDef) (calculus : AdmittedCalculusAt language) :
    ValidatedPresentation :=
  ⟨{ language, calculus := calculus.1 }, calculus.2⟩

@[simp] theorem checked_language (language : LanguageDef)
    (calculus : AdmittedCalculusAt language) :
    (calculus.checked language).1.language = language :=
  rfl

@[simp] theorem checked_calculus (language : LanguageDef)
    (calculus : AdmittedCalculusAt language) :
    (calculus.checked language).1.calculus = calculus.1 :=
  rfl

end AdmittedCalculusAt

/-- Elaborate an authored calculus and retain it exactly when contextual
admission succeeds.  The gate is the existing `Presentation.isValidV2`; this
definition merely exposes its dependent fibre. -/
def admitCalculus? (language : LanguageDef) (source : CalculusSyntax) :
    Option (AdmittedCalculusAt language) := do
  let calculus ← elaborate source
  if valid : (Presentation.mk language calculus).isValidV2 = true then
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
same computation.  Mapping a fibre point back to `ValidatedPresentation`
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
          (Presentation.mk language calculus).isValidV2 = true
      · simp [admit?, elaborateDefinition?, admitCalculus?, elaborated,
          Presentation.validateV2?, valid, AdmittedCalculusAt.checked]
      · simp [admit?, elaborateDefinition?, admitCalculus?, elaborated,
          Presentation.validateV2?, valid]

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
    ({ language := canaryLanguage, calculus := canaryCalculus } :
      Presentation).isValidV2 = true := by
  have languageValid : canaryLanguage.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [canaryLanguage, LanguageDef.empty, LanguageDef.typeNames]
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [languageValid]
  simp [canaryCalculus, canaryJudgment, canaryRule,
    canaryLanguage, LanguageDef.empty,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.conversionDeclarationValid,
    Presentation.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Presentation.judgmentSchemaValid,
    fixedConstructorListsValid, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  constructor <;> decide

private def canaryChecked : ValidatedPresentation :=
  ⟨{ language := canaryLanguage, calculus := canaryCalculus }, canaryValid⟩

private def canaryAdmittedCalculus : AdmittedCalculusAt canaryLanguage :=
  ⟨canaryCalculus, canaryValid⟩

private theorem canaryAdmitted :
    admit? canaryLanguage canarySource = some canaryChecked := by
  simp [admit?, canarySource, elaborateDefinition?, canaryChecked,
    Presentation.validateV2?, canaryValid]

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
      Presentation.lookupRule?, argumentsValidAt,
      RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?]
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
    ({ language := canaryLanguage, calculus := undeclaredCalculus } :
      Presentation).isValidV2 = false := by
  have languageValid : canaryLanguage.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [canaryLanguage, LanguageDef.empty, LanguageDef.typeNames]
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [languageValid]
  simp [undeclaredCalculus, canaryRule, canaryLanguage, LanguageDef.empty,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.lookupJudgment?,
    Presentation.judgmentSchemaValid, RuleSchema.isValidIn,
    RuleSchema.isValidV1, RuleSchema.metavariableNames,
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
  simp [Presentation.validateV2?, undeclaredInvalid]

/-- The canonical admission layer rejects the same malformed calculus, so a
realization cannot compile it through `compileTerm?`. -/
theorem undeclared_calculusAdmission_rejected :
    calculusAdmissionLayer.elaborate canaryLanguage
      (quote undeclaredCalculus) = none := by
  simp [calculusAdmissionLayer, admitCalculus?, undeclaredInvalid]

end Mettapedia.GSLT.LanguageDef.CalculusExtension
