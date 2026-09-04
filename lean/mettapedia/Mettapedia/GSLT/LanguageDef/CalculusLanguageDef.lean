import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.ExtendedLanguageDef

/-!
# A flat calculus language definition

`CalculusLanguageDef` literally extends `LanguageDef` with judgments and
inference rules.  The inherited fields remain flat in record syntax, so a
human authors one definition rather than a language block, a calculus block,
and a pairing step.

```
def myLanguage : CalculusLanguageDef where
  name      := "..."
  types     := [...]
  terms     := [...]
  equations := [...]
  rewrites  := [...]
  judgments := [...]
  rules     := [...]
```

Every field has a default, so an author writes only what the language has, in
one record — no separate calculus and no pairing step.

The generic extension mechanism is `ExtendedLanguageDef layer`.  This record
is its proof-calculus-specific flat front end; it is not a closed list of every
extension a language may ever have.  Logic, oracle, reflection, and future
layers compose through `CompositionalLayer.product` rather than by adding
unrelated optional fields here.  A human-facing authoring DSL may flatten
those products syntactically without changing their canonical meaning.

The five original fields are untouched and remain canonical: `toLanguageDef`
is a plain field selection.  The checker, totalizer, and downstream compilers
consume this same flat object; there is no parallel pair representation.

`toGSLTUsing` is the general point.  An admitted `CalculusLanguageDef` whose
reductions respect its equations in an explicit relation environment denotes
one GSLT — one carrier, one equation relation, and one reduction relation —
with the object language embedding faithfully, the rules embedding
faithfully, and no step crossing between them.  `toGSLT` is exactly its empty
relation-environment specialization, while the two no-equation conveniences
discharge the compatibility law for exact-syntax languages.

## When a further field may be added

Growth is allowed but not free.  A new field earns its place only if it is
**not determined by the ones already there** — the `Factors` / `NonTrivialFiber`
criterion.  Judgments and rules pass that test; anything proposed later ships
the same canary or it is redundant by construction.

`Example` authors a complete small language in this record and runs it:
admitted, and one goal discharged by reduction of the theory it denotes.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.TotalGSLT

namespace CalculusLanguageDef

variable (extended : CalculusLanguageDef)

/-! ## Grounding in the general compositional extension family -/

/-- The flat record is the proof-calculus specialization of the general
layer-indexed definition.  This conversion changes no field: it merely exposes
the canonical `calculusLayer` index that supplies the authored GSLT and its
concatenation laws. -/
def toExtended : ExtendedLanguageDef calculusLayer where
  toLanguageDef := extended.toLanguageDef
  extension := extended.toCalculus

/-- Recover the flat calculus specialization from the generic calculus layer.
This is field selection in the opposite direction; no validation or semantic
information is reconstructed. -/
def ofExtended (definition : ExtendedLanguageDef calculusLayer) :
    CalculusLanguageDef where
  toLanguageDef := definition.toLanguageDef
  judgments := definition.extension.judgments
  rules := definition.extension.rules
  conversion := definition.extension.conversion

/-- Flattening and then exposing the generic calculus layer loses nothing. -/
@[simp] theorem ofExtended_toExtended :
    ofExtended extended.toExtended = extended :=
  rfl

/-- A generic calculus-layer definition is recovered exactly after flattening. -/
@[simp] theorem toExtended_ofExtended
    (definition : ExtendedLanguageDef calculusLayer) :
    (ofExtended definition).toExtended = definition :=
  rfl

/-- The ergonomic flat record and the generic coGSLT-indexed calculus
extension are equivalent authoring forms. -/
def equivExtended :
    CalculusLanguageDef ≃ ExtendedLanguageDef calculusLayer where
  toFun := toExtended
  invFun := ofExtended
  left_inv := ofExtended_toExtended
  right_inv := toExtended_ofExtended

@[simp] theorem toExtended_language :
    extended.toExtended.toLanguageDef = extended.toLanguageDef :=
  rfl

@[simp] theorem toExtended_calculus :
    extended.toExtended.extension = extended.toCalculus :=
  rfl

/-- The source theory of the general layered definition is exactly the
canonical calculus-authoring GSLT. -/
@[simp] theorem toExtended_authoredGSLT :
    extended.toExtended.authoredGSLT = calculusSyntaxGSLT :=
  rfl

/-- The human-facing flat fields elaborate through that GSLT to exactly the
calculus projection. -/
@[simp] theorem toExtended_elaborate_authoredSource :
    calculusLayer.elaborate extended.toLanguageDef
        extended.toExtended.authoredSource =
      some extended.toCalculus :=
  extended.toExtended.elaborate_authoredSource

/-! ## Admission -/

/-- Whether the extended calculus is admitted against its own object language. -/
abbrev isAdmitted : Bool := extended.isValid

/-- The validated form consumed by checking and totalization. -/
abbrev validated (admitted : extended.isAdmitted = true) :
    ValidatedCalculusLanguageDef :=
  ⟨extended, admitted⟩

/-! ## The theory it denotes

An admitted extended language *is* a GSLT. -/

/-- **The relation-aware theory.**  Premise-bearing object rewrites use the
supplied relation environment; proof search remains the admitted generic
calculus. -/
def toGSLTUsing (relations : RelationEnv)
    (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquationsUsing relations
      extended.toLanguageDef) : GSLT :=
  combinedGSLTUsing relations (extended.validated admitted) laws

/-- Convenient relation-aware totalization for equation-free languages. -/
def toGSLTUsingOfEquationFree (relations : RelationEnv)
    (admitted : extended.isAdmitted = true)
    (free : extended.toLanguageDef.isEquationFree = true) : GSLT :=
  extended.toGSLTUsing relations admitted
    (ReductionRespectsEquationsUsing.of_equation_free relations free)

/-- **The one theory.**  The additional law is exactly the compatibility
required for authored rewrites to descend through authored equations in the
empty relation environment. -/
def toGSLT (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquations extended.toLanguageDef) : GSLT :=
  combinedGSLT (extended.validated admitted) laws

/-- Convenient totalization for languages with no equation generators. -/
def toGSLTOfEquationFree (admitted : extended.isAdmitted = true)
    (free : extended.toLanguageDef.isEquationFree = true) : GSLT :=
  extended.toGSLT admitted (ReductionRespectsEquations.of_equation_free free)

theorem toGSLT_eq_toGSLTUsing_empty (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquations extended.toLanguageDef) :
    extended.toGSLT admitted laws =
      extended.toGSLTUsing RelationEnv.empty admitted laws :=
  rfl

/-- **The relation-aware carrier**: an object pattern, or a proof-obligation
state. -/
theorem toGSLTUsing_Term (relations : RelationEnv)
    (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquationsUsing relations
      extended.toLanguageDef) :
    (extended.toGSLTUsing relations admitted laws).Term =
      (Pattern ⊕ GoalState) :=
  rfl

/-- **The relation-aware reduction relation**: object reduction under the
supplied premise interpretation on the left and generic proof search on the
right. -/
theorem toGSLTUsing_rewrites (relations : RelationEnv)
    (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquationsUsing relations
      extended.toLanguageDef) :
    (extended.toGSLTUsing relations admitted laws).rewrites =
      GSLT.SumStep
        (languageGSLTUsing relations extended.toLanguageDef laws)
        (proofSearchGSLT (extended.validated admitted)) :=
  rfl

/-- **The object projection is exact in the supplied environment.** -/
theorem toGSLTUsing_object_step (relations : RelationEnv)
    (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquationsUsing relations
      extended.toLanguageDef)
    (source target : Pattern) :
    (extended.toGSLTUsing relations admitted laws).Step
        (inLanguage source) (inLanguage target) ↔
      langReducesUsing relations extended.toLanguageDef source target :=
  combinedGSLTUsing_language_step relations (extended.validated admitted)
    laws source target

/-- **The calculus projection is independent of the object environment.** -/
theorem toGSLTUsing_proof_step (relations : RelationEnv)
    (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquationsUsing relations
      extended.toLanguageDef)
    (source target : GoalState) :
    (extended.toGSLTUsing relations admitted laws).Step
        (inCalculus source) (inCalculus target) ↔
      (proofSearchGSLT (extended.validated admitted)).Step source target :=
  combinedGSLTUsing_calculus_step relations (extended.validated admitted)
    laws source target

/-- **Nothing crosses** between relation-aware object execution and proof
search. -/
theorem toGSLTUsing_no_crossing (relations : RelationEnv)
    (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquationsUsing relations
      extended.toLanguageDef)
    (pattern : Pattern) (state : GoalState) :
    ¬ (extended.toGSLTUsing relations admitted laws).Step
        (inLanguage pattern) (inCalculus state) ∧
      ¬ (extended.toGSLTUsing relations admitted laws).Step
        (inCalculus state) (inLanguage pattern) :=
  combinedGSLTUsing_no_crossing relations (extended.validated admitted)
    laws pattern state

/-- **Derivability remains proof search** inside the right summand. -/
theorem toGSLTUsing_derivability (relations : RelationEnv)
    (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquationsUsing relations
      extended.toLanguageDef)
    (goals : GoalState) :
    Nonempty (DerivationList (extended.validated admitted) goals) ↔
      (extended.toGSLTUsing relations admitted laws).MultiStep
        (inCalculus goals) (inCalculus []) :=
  derivability_iff_combinedGSLTUsing relations (extended.validated admitted)
    laws goals

/-- **The carrier**: an object pattern, or a proof-obligation state. -/
theorem toGSLT_Term (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquations extended.toLanguageDef) :
    (extended.toGSLT admitted laws).Term = (Pattern ⊕ GoalState) := rfl

/-- **The reduction relation**: extended object reduction on one side, backward
inference-rule application on the other. -/
theorem toGSLT_rewrites (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquations extended.toLanguageDef) :
    (extended.toGSLT admitted laws).rewrites =
      GSLT.SumStep (languageGSLT extended.toLanguageDef laws)
        (proofSearchGSLT (extended.validated admitted)) := rfl

/-- **The object language embeds faithfully.**  Declaring judgments and rules
changes no object-term reduction, in either direction. -/
theorem toGSLT_object_step (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquations extended.toLanguageDef)
    (source target : Pattern) :
    (extended.toGSLT admitted laws).Step
        (inLanguage source) (inLanguage target) ↔
      langReducesUsing RelationEnv.empty extended.toLanguageDef source target :=
  combinedGSLT_language_step (extended.validated admitted) laws source target

/-- **The calculus embeds faithfully.** -/
theorem toGSLT_proof_step (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquations extended.toLanguageDef)
    (source target : GoalState) :
    (extended.toGSLT admitted laws).Step
        (inCalculus source) (inCalculus target) ↔
      (proofSearchGSLT (extended.validated admitted)).Step source target :=
  combinedGSLT_calculus_step (extended.validated admitted) laws source target

/-- **Nothing crosses**, so the object fragment of the theory is exactly the
extended object language. -/
theorem toGSLT_no_crossing (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquations extended.toLanguageDef)
    (pattern : Pattern) (state : GoalState) :
    ¬ (extended.toGSLT admitted laws).Step
        (inLanguage pattern) (inCalculus state) ∧
      ¬ (extended.toGSLT admitted laws).Step
        (inCalculus state) (inLanguage pattern) :=
  combinedGSLT_no_crossing (extended.validated admitted) laws pattern state

/-- **Derivability is reduction**, inside the one theory. -/
theorem toGSLT_derivability (admitted : extended.isAdmitted = true)
    (laws : ReductionRespectsEquations extended.toLanguageDef)
    (goals : GoalState) :
    Nonempty (DerivationList (extended.validated admitted) goals) ↔
      (extended.toGSLT admitted laws).MultiStep
        (inCalculus goals) (inCalculus []) :=
  derivability_iff_combinedGSLT (extended.validated admitted) laws goals

end CalculusLanguageDef

/-! ## A complete language, extended flat

Everything a small language needs, in one record, with the theory it denotes
and one reduction of that theory. -/

namespace Example

open CalculusLanguageDef

/-- A one-sort language with a zero and a successor, and one judgment saying a
term is even, with two rules. -/
def evenNumbers : CalculusLanguageDef where
  name := "even-numbers"
  types := [TypeDecl.plain "N"]
  terms :=
    [{ label := "z", category := "N", params := [], syntaxPattern := [] },
     { label := "s", category := "N",
       params := [TermParam.simple "predecessor" (.base "N")],
       syntaxPattern := [] }]
  equations := []
  rewrites := []
  judgments := [{ head := "Even", arity := 1 }]
  rules :=
    [{ id := ⟨"even-zero"⟩
       metavariables := []
       premises := []
       conclusion := .apply "Even" [.apply "z" []] },
     { id := ⟨"even-step"⟩
       metavariables := [("n", 0)]
       premises := [.apply "Even" [.fvar "n"]]
       conclusion :=
         .apply "Even" [.apply "s" [.apply "s" [.fvar "n"]]] }]

theorem evenNumbers_admitted : evenNumbers.isAdmitted = true := by
  have validate : evenNumbers.toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [evenNumbers, LanguageDef.typeNames, TypeDecl.plain,
        TermParam.typeExpr, TypeExpr.baseNames]
  unfold isAdmitted CalculusLanguageDef.isValid
    CalculusLanguageDef.hasValidLocalRules
  rw [validate]
  simp [evenNumbers,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]
  decide

/-- The theory the record denotes. -/
def theory : GSLT :=
  evenNumbers.toGSLTOfEquationFree evenNumbers_admitted rfl

/-- Zero is even, and its goal discharges in one reduction of that theory. -/
theorem zero_is_even :
    theory.Step
      (Sum.inr (α := Pattern) [Pattern.apply "Even" [Pattern.apply "z" []]])
      (Sum.inr (α := Pattern) []) := by
  unfold theory toGSLTOfEquationFree toGSLT combinedGSLT
  apply GSLT.SumStep.right
  refine ⟨{ ruleId := ⟨"even-zero"⟩, arguments := [] },
    [], .apply "Even" [.apply "z" []], [], ?_, rfl, rfl⟩
  simp [evenNumbers,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemas?, instantiateSchemasAt?]

end Example

end Mettapedia.GSLT.LanguageDef
