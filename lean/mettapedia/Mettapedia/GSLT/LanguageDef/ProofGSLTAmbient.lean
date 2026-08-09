import Mettapedia.GSLT.LanguageDef.ProofGSLTArticleIdentity

/-!
# The ambient object and its shadow

Checking is what a proof artifact can be *verified* to be; reasoning is what
a proof artifact *is*.  These are different objects, related by a
projection, and the direction of that projection is not symmetric.  This
module makes the asymmetry a theorem rather than a slogan, and then
de-truncates the statements that were needlessly stated about the shadow.

For a validated presentation `P` and judgment `J`:

```
   Derivation P J          the proof — proof-relevant, a Type
        │
        │ truncate          (the projection: forget which proof)
        ▼
   Nonempty (Derivation P J)   provability — a Prop
```

Everything the checker returns lives below the line.  Everything reasoning
needs — proof identity, cost, provenance, which of two routes was taken,
whether two translations agree — lives above it.

`cost_does_not_factor_through_provability` is the steelman: it exhibits one
judgment with two derivations of different size and concludes that **no
function on provability can compute cost**.  The argument is short and
completely mechanical: `Nonempty` is a `Prop`, so its two inhabitants are
*equal* by proof irrelevance, while the derivations they came from are not.
Anything that distinguishes proofs therefore cannot be recovered downstream.

The practical reading, and the reason this module exists: a development that
states its theorems about the shadow has not merely lost precision, it has
made a class of facts *unstatable*.  Cost ledgers, provenance, proof
transport coherence, and the comparison of two translations are all facts
about the ambient object.  Where we already have proof-relevant machinery —
`Derivation` is a `Type`, `Derivation.transport` is a function, article
linearisation is a function — the theorems should be stated there and the
truncated corollaries derived, not the reverse.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT.Ambient

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ProofGSLT

/-! ## The projection -/

/-- Forget which proof.  This is the only direction that is canonical. -/
@[reducible] def truncate {presentation : ValidatedPresentation}
    {goal : Pattern} (derivation : Derivation presentation goal) :
    Nonempty (Derivation presentation goal) := ⟨derivation⟩

/-! ### Size of a closed derivation, as a proof-relevant measure -/

mutual

def derivationSize {presentation : ValidatedPresentation} :
    {goal : Pattern} → Derivation presentation goal → Nat
  | _, .byRule _ _ children => derivationListSize children + 1

def derivationListSize {presentation : ValidatedPresentation} :
    {goals : List Pattern} → DerivationList presentation goals → Nat
  | _, .nil => 0
  | _, .cons head tail => derivationSize head + derivationListSize tail

end

/-! ## The fixture: one judgment, two proofs of different size -/

private def ambientType : TypeDecl := TypeDecl.plain "AT"

private def atomRule (label : String) : GrammarRule :=
  { label := label, category := "AT", params := [], syntaxPattern := [] }

def target : Pattern := .apply "amb-target" []
private def middle : Pattern := .apply "amb-middle" []

def goalJ (subject : Pattern) : Pattern := .apply "AJ" [subject]

/-- The short route: the goal outright. -/
private def directRule : RuleSchema :=
  { id := ⟨"amb-direct"⟩, metavariables := [], premises := []
    conclusion := goalJ target }

/-- The long route, step one. -/
private def viaAxiom : RuleSchema :=
  { id := ⟨"amb-via-axiom"⟩, metavariables := [], premises := []
    conclusion := goalJ middle }

/-- The long route, step two: the same goal, via the detour. -/
private def viaStep : RuleSchema :=
  { id := ⟨"amb-via-step"⟩, metavariables := []
    premises := [goalJ middle], conclusion := goalJ target }

private def ambientLanguage : LanguageDef :=
  { name := "proof-gslt-ambient-two-routes"
    types := [ambientType]
    terms := [atomRule "amb-target", atomRule "amb-middle"]
    equations := []
    rewrites := [] }

private def ambientCalculus :
    Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus :=
  { judgments := [{ head := "AJ", arity := 1 }]
    rules := [directRule, viaAxiom, viaStep] }

private def ambientPresentation : Presentation :=
  { language := ambientLanguage, calculus := ambientCalculus }

private theorem ambient_validate :
    ambientPresentation.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [ambientPresentation, ambientLanguage, ambientType, atomRule,
      LanguageDef.typeNames, TermParam.typeExpr, TypeDecl.plain]

theorem ambient_valid : ambientPresentation.isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [ambient_validate]
  simp [ambientPresentation, ambientCalculus, ambientLanguage, ambientType, atomRule,
    directRule, viaAxiom, viaStep, goalJ, target, middle,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.ruleIds, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    Presentation.conversionDeclarationValid]
  decide

def ambientValidated : ValidatedPresentation :=
  ⟨ambientPresentation, ambient_valid⟩

private theorem direct_instantiates :
    instantiateRule? ambientValidated ⟨⟨"amb-direct"⟩, []⟩ =
      some ([], goalJ target) := by
  simp [instantiateRule?, ambientValidated, ambientPresentation, ambientCalculus,
    ambientLanguage, directRule, viaAxiom, viaStep, Presentation.lookupRule?,
    argumentsValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?, goalJ,
    target]

private theorem viaAxiom_instantiates :
    instantiateRule? ambientValidated ⟨⟨"amb-via-axiom"⟩, []⟩ =
      some ([], goalJ middle) := by
  simp [instantiateRule?, ambientValidated, ambientPresentation, ambientCalculus,
    ambientLanguage, directRule, viaAxiom, viaStep, Presentation.lookupRule?,
    argumentsValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?, goalJ,
    middle]

private theorem viaStep_instantiates :
    instantiateRule? ambientValidated ⟨⟨"amb-via-step"⟩, []⟩ =
      some ([goalJ middle], goalJ target) := by
  simp [instantiateRule?, ambientValidated, ambientPresentation, ambientCalculus,
    ambientLanguage, directRule, viaAxiom, viaStep, Presentation.lookupRule?,
    argumentsValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?, goalJ,
    target, middle]

/-- The one-node proof. -/
def shortProof : Derivation ambientValidated (goalJ target) :=
  .byRule ⟨⟨"amb-direct"⟩, []⟩
    (instantiateRule?_eq_some_iff_application.mp direct_instantiates) .nil

/-- The two-node proof of the very same judgment. -/
def longProof : Derivation ambientValidated (goalJ target) :=
  .byRule ⟨⟨"amb-via-step"⟩, []⟩
    (instantiateRule?_eq_some_iff_application.mp viaStep_instantiates)
    (.cons
      (.byRule ⟨⟨"amb-via-axiom"⟩, []⟩
        (instantiateRule?_eq_some_iff_application.mp viaAxiom_instantiates)
        .nil)
      .nil)

theorem shortProof_size : derivationSize shortProof = 1 := rfl

theorem longProof_size : derivationSize longProof = 2 := rfl

/-! ## The steelman -/

/-- **Cost is not a function of provability.**  There is one judgment with
two proofs of different size, and the two truncations of those proofs are
*equal* — `Nonempty` is a `Prop`, so proof irrelevance identifies them.  Any
map out of provability is therefore constant across proofs, and cannot
compute anything that distinguishes them.

This is the precise sense in which checking is a shadow.  Cost ledgers,
provenance, proof identity, and the comparison of two routes are facts about
the ambient object; they do not merely become harder after truncation, they
become unstatable. -/
theorem cost_does_not_factor_through_provability :
    ¬ ∃ measure : Nonempty (Derivation ambientValidated (goalJ target)) → Nat,
        ∀ derivation : Derivation ambientValidated (goalJ target),
          measure (truncate derivation) = derivationSize derivation := by
  rintro ⟨measure, agrees⟩
  have shortValue := agrees shortProof
  have longValue := agrees longProof
  have truncationsEqual :
      truncate shortProof = truncate longProof := Subsingleton.elim _ _
  rw [truncationsEqual, longValue] at shortValue
  rw [shortProof_size, longProof_size] at shortValue
  cases shortValue

/-- The same asymmetry stated positively: the projection is not injective,
so it has no left inverse. -/
theorem truncate_not_injective :
    ¬ Function.Injective
      (truncate (presentation := ambientValidated) (goal := goalJ target)) := by
  intro injective
  have equal : shortProof = longProof := injective (Subsingleton.elim _ _)
  have sizes : derivationSize shortProof = derivationSize longProof := by
    rw [equal]
  rw [shortProof_size, longProof_size] at sizes
  cases sizes

/-- Both routes are of course accepted, so the loss is invisible to the
checker: acceptance cannot tell the two apart even in principle. -/
theorem both_routes_accepted :
    checkRaw ambientValidated (goalJ target) shortProof.erase = true ∧
      checkRaw ambientValidated (goalJ target) longProof.erase = true ∧
      shortProof.erase ≠ longProof.erase :=
  ⟨checkRaw_erase shortProof, checkRaw_erase longProof, by
    simp [Derivation.erase, shortProof, longProof, DerivationList.erase]⟩

/-! ## Compact proof support: a finite article needs only a finite theory

The growth story for a large library.  An article over a presentation with
tens of thousands of rules cites a handful of them; the restriction of the
presentation to exactly those identifiers accepts exactly the same article.
So a proof over an ever-growing theory factors through a finite stage of
that theory, which is what makes an ind-completion the right home for
growth rather than a decoration on it. -/

/-- Restrict a presentation to a named set of rule identifiers.  Everything
else — syntax, judgments, conversion interface — is untouched. -/
def restrictRules (presentation : Presentation) (ids : List RuleId) :
    Presentation :=
  { presentation with
    calculus :=
      { presentation.calculus with
        rules := presentation.rules.filter fun rule => ids.contains rule.id } }

@[simp] theorem restrictRules_rules (presentation : Presentation)
    (ids : List RuleId) :
    (restrictRules presentation ids).rules =
      presentation.rules.filter (fun rule => ids.contains rule.id) := rfl

/-- Filtering a rule table cannot move the first match: any rule the filter
keeps is still found, and any rule it drops was not the match anyway.  No
uniqueness hypothesis is needed. -/
private theorem find?_filter_id :
    ∀ (rules : List RuleSchema) (ids : List RuleId) (id : RuleId),
      ids.contains id = true →
      (rules.filter (fun rule => ids.contains rule.id)).find?
          (fun rule => decide (rule.id = id)) =
        rules.find? (fun rule => decide (rule.id = id)) := by
  intro rules
  induction rules with
  | nil => intro _ _ _; rfl
  | cons rule rest inductionHypothesis =>
      intro ids id retained
      by_cases matches' : rule.id = id
      · have kept : ids.contains rule.id = true := matches' ▸ retained
        rw [List.filter_cons_of_pos (by simpa using kept)]
        simp [matches']
      · by_cases kept : ids.contains rule.id = true
        · rw [List.filter_cons_of_pos (by simpa using kept)]
          simpa [List.find?_cons, matches'] using
            inductionHypothesis ids id retained
        · rw [List.filter_cons_of_neg (by simpa using kept)]
          simpa [List.find?_cons, matches'] using
            inductionHypothesis ids id retained

/-- Looking up a retained identifier in the restriction finds the same
rule. -/
theorem lookupRule?_restrictRules {presentation : Presentation}
    (ids : List RuleId) {id : RuleId} (retained : ids.contains id = true) :
    (restrictRules presentation ids).lookupRule? id =
      presentation.lookupRule? id :=
  find?_filter_id presentation.rules ids id retained

/-- **Compact proof support.**  An article is accepted by a presentation
exactly when it is accepted by the restriction of that presentation to the
identifiers the article cites.  A finite proof therefore never depends on
the size of the ambient theory, only on its own finite cone — the property
that makes growth by filtered colimit sound, and the reason a proof over a
library the size of a mathematical corpus remains a finite object. -/
theorem checkWireArticle_restrictRules {article : WireArticle}
    {presentation : Presentation} (valid : presentation.isValidV2 = true)
    (restrictedValid :
      (restrictRules presentation article.citedRuleIds).isValidV2 = true) :
    checkWireArticle ⟨presentation, valid⟩ article = true ↔
      checkWireArticle
        ⟨restrictRules presentation article.citedRuleIds, restrictedValid⟩
        article = true := by
  refine checkWireArticle_iff_articleRuleAgreement ?_
  intro id cited
  exact (lookupRule?_restrictRules article.citedRuleIds
    (by simpa using cited)).symm

/-! ## Scaffolding for the remaining ambient constructions

The two shapes below are stated so that later work lands on a fixed
interface rather than reinventing one.  Neither is inhabited here; each is a
named obligation. -/

/-- A confluence diamond as a **construction** rather than an existential:
the joining object together with both closing moves.  A development that
returns this can be composed; one that returns `∃` cannot, and the higher
cells of a multiway rewriting system are exactly these fillers. -/
structure DiamondFiller {State : Type} (Step : State → State → Prop)
    (source left right : State) where
  join : State
  fromLeft : Step left join
  fromRight : Step right join

/-- A conversion edge is an ordinary derivation of the presentation's
declared conversion judgment.  Reading it as a path, transport along it is
what a cast term denotes; this is the interface the certified conversion
tier should be stated over. -/
def ConversionEdge (presentation : ValidatedPresentation)
    (declaration : ConversionDecl) (left right : Pattern) : Type :=
  Derivation presentation (.apply declaration.judgmentHead [left, right])

end Mettapedia.GSLT.LanguageDef.ProofGSLT.Ambient
