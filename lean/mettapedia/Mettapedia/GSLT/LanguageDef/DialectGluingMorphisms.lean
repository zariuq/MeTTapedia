import Mettapedia.GSLT.LanguageDef.DialectGluing
import Mettapedia.GSLT.LanguageDef.StructuralPresentationCategory

/-!
# Structural inclusion morphisms for dialect gluing

`DialectGluing.glue` joins two extensions of a common base presentation at the
list level.  This module upgrades that construction to categorical data in the
structural presentation category:

* validated glued presentations: `zeroWithChoice` and the glued
  `quoteAndChoice` presentation pass the ordinary five-field validator
  (`zeroWithChoice_validate`, `quoteAndChoice_validate`), so both become
  `ValidatedLanguageDef` objects (`zeroWithChoiceValidated`,
  `quoteAndChoiceValidated`);
* inclusion `StructuralMorphism`s with identity symbol action: the left
  extension always includes into the glued presentation
  (`leftInclusionMorphism`), and the right extension includes exactly when the
  span satisfies `RightBaseCollisionsCovered` — every right declaration whose
  gluing key collides
  with the base is already a declaration of the left extension
  (`rightInclusionMorphism`);
* a positive collision-coverage instance
  (`quoteAndChoice_rightBaseCollisionsCovered`) giving the
  concrete right inclusion, and a negative instance
  (`zeroWithDivergentQuery_rightBaseCollisionsNotCovered`): a dialect that
  redeclares a base
  constructor with different content is not covered, and `glue` silently
  discards its divergent declaration (`divergentQueryConstructor_not_glued`);
* the clash canary: the presentation glued from the `clashingQuote` span has
  its right/base collisions covered
  (`clashSpan_rightBaseCollisionsCovered` — the predicate constrains only
  base collisions)
  but fails validation (`clashingGlued_validate_ne_nil`), connecting to
  `no_presentation_glues_clash`: coherence does not excuse a left–right label
  clash, validation remains an independent gate;
* the concrete commuting cocone square
  (`quoteAndChoice_gluingSquare_commutes`): base → left → glued
  equals base → right → glued, on the nose and hence in the extensional
  `Equivalent`/`Arrow` quotient; the base → left leg is the existing
  `Prime.LanguageDef.currentZeroToPrimePresentation`;
* a same-action mediator out of the glued presentation
  (`sameActionMediator`): structural maps from the left and right extensions
  into a common target with the same *global* symbol action induce a map from
  the glued presentation, and both triangles commute
  (`sameActionMediator_comp_left_inclusion`,
  `sameActionMediator_comp_right_inclusion`);
* a counterexample showing why this is not yet the pushout mediator: two maps
  may agree on the shared base while acting differently on the extensions'
  private symbols.  Such a cocone has a mediator in the extensional category
  but does not satisfy global symbol-action equality
  (`baseAgreement_does_not_imply_same_global_action`).

**Deliberately not claimed**: a universal property.  A genuine pushout must
construct a mediator whenever the two maps agree *after restriction to the
base*.  `sameActionMediator` assumes the strictly stronger equality of their
total symbol actions.  The general mediator and its uniqueness in the
extensional `Arrow` category are both future work.
-/

namespace Mettapedia.GSLT.LanguageDef.DialectGluingMorphisms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DialectGluing
open Mettapedia.GSLT.LanguageDef.StructuralPresentationCategory
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.Prime.NucleusDerivedModalTyping

/-! ## Literal readouts of the authored constructor lists

The constructor helpers of `MeTTaZero` and `Prime.LanguageDef` are private, so
row-level validation proofs in this module first rewrite the constructor lists
to proof-local explicit literals.  Each readout is kernel-checked by `decide`
against the authored definitions and is not treated as an independent
authority.  (This mirrors the projection-transparent bridge lemmas used
inside `Prime.LanguageDef`.) -/

private def zeroWithChoiceTermLiterals : List GrammarRule :=
  [{ label := "=", category := "Atom",
     params := [.simple "left" (.base "Atom"), .simple "right" (.base "Atom")],
     syntaxPattern := [] },
   { label := "zero-query", category := "Process",
     params := [.simple "space" (.base "Space"), .simple "pattern" (.base "Atom"),
       .simple "template" (.base "Atom")],
     syntaxPattern := [] },
   { label := "zero-query-answer", category := "Process",
     params := [.simple "answer" (.base "Atom")], syntaxPattern := [] },
   { label := "zero-evaluate", category := "Process",
     params := [.simple "space" (.base "Space"), .simple "subject" (.base "Atom")],
     syntaxPattern := [] },
   { label := "zero-evaluate-answer", category := "Process",
     params := [.simple "answer" (.base "Atom")], syntaxPattern := [] },
   { label := "prime-choose", category := "Process",
     params := [.simple "left" (.base "Process"), .simple "right" (.base "Process")],
     syntaxPattern := [] },
   { label := "prime-collect", category := "Alternatives",
     params := [.simple "process" (.base "Process")], syntaxPattern := [] }]

private def quoteAndChoiceTermLiterals : List GrammarRule :=
  [{ label := "=", category := "Atom",
     params := [.simple "left" (.base "Atom"), .simple "right" (.base "Atom")],
     syntaxPattern := [] },
   { label := "zero-query", category := "Process",
     params := [.simple "space" (.base "Space"), .simple "pattern" (.base "Atom"),
       .simple "template" (.base "Atom")],
     syntaxPattern := [] },
   { label := "zero-query-answer", category := "Process",
     params := [.simple "answer" (.base "Atom")], syntaxPattern := [] },
   { label := "zero-evaluate", category := "Process",
     params := [.simple "space" (.base "Space"), .simple "subject" (.base "Atom")],
     syntaxPattern := [] },
   { label := "zero-evaluate-answer", category := "Process",
     params := [.simple "answer" (.base "Atom")], syntaxPattern := [] },
   { label := "prime-unit", category := "Atom", params := [], syntaxPattern := [] },
   { label := "prime-quote", category := "PrimeName",
     params := [.simple "term" (.base "Atom")], syntaxPattern := [] },
   { label := "prime-drop", category := "Atom",
     params := [.simple "name" (.base "PrimeName")], syntaxPattern := [] },
   { label := "prime-evaluate-name", category := "Process",
     params := [.simple "space" (.base "Space"), .simple "name" (.base "PrimeName")],
     syntaxPattern := [] },
   { label := "prime-need", category := "Process",
     params := [.simple "space" (.base "Space"), .simple "subject" (.base "Atom")],
     syntaxPattern := [] },
   { label := "prime-need-answer", category := "Process",
     params := [.simple "answer" (.base "Atom"),
       .simple "receipt" (.base "PrimeReceipt")],
     syntaxPattern := [] },
   { label := "prime-need-key", category := "Atom",
     params := [.simple "revision" (.base "Atom"), .simple "subject" (.base "Atom")],
     syntaxPattern := [] },
   { label := "prime-request-dependency", category := "Atom",
     params := [.simple "key" (.base "Atom")], syntaxPattern := [] },
   { label := "prime-space-atom-dependency", category := "Atom",
     params := [.simple "key" (.base "Atom"), .simple "atom" (.base "Atom")],
     syntaxPattern := [] },
   { label := "prime-capability-dependency", category := "Atom",
     params := [.simple "key" (.base "Atom"), .simple "result" (.base "Atom")],
     syntaxPattern := [] },
   { label := "prime-inert-dependency", category := "Atom",
     params := [.simple "key" (.base "Atom")], syntaxPattern := [] },
   { label := "prime-receipt", category := "PrimeReceipt",
     params := [.simple "root" (.base "Atom")], syntaxPattern := [] },
   { label := "prime-choose", category := "Process",
     params := [.simple "left" (.base "Process"), .simple "right" (.base "Process")],
     syntaxPattern := [] },
   { label := "prime-collect", category := "Alternatives",
     params := [.simple "process" (.base "Process")], syntaxPattern := [] }]

private theorem zeroWithChoice_typeNames_eq :
    zeroWithChoice.typeNames = ["Atom", "Space", "Process", "Alternatives"] := by
  decide

private theorem zeroWithChoice_terms_eq :
    zeroWithChoice.terms = zeroWithChoiceTermLiterals := by
  decide

private theorem quoteAndChoice_typeNames_eq :
    quoteAndChoice.typeNames =
      ["Atom", "Space", "Process", "Alternatives", "PrimeName", "PrimeReceipt"] := by
  decide

private theorem quoteAndChoice_terms_eq :
    quoteAndChoice.terms = quoteAndChoiceTermLiterals := by
  decide

private theorem quoteAndChoice_constructorLabels_eq :
    quoteAndChoice.terms.map (fun term => term.label) =
      ["=", "zero-query", "zero-query-answer", "zero-evaluate",
       "zero-evaluate-answer", "prime-unit", "prime-quote", "prime-drop",
       "prime-evaluate-name", "prime-need", "prime-need-answer",
       "prime-need-key", "prime-request-dependency",
       "prime-space-atom-dependency", "prime-capability-dependency",
       "prime-inert-dependency", "prime-receipt", "prime-choose",
       "prime-collect"] := by
  rw [quoteAndChoice_terms_eq]
  rfl

/-! ## Row validation of the choice extension's rewrites -/

private theorem zeroWithChoice_queryRewrite_row :
    LanguageDef.validateRewrite zeroWithChoice MeTTaZero.queryRewrite = [] := by
  simp [LanguageDef.validateRewrite, zeroWithChoice_typeNames_eq,
    zeroWithChoice_terms_eq, zeroWithChoiceTermLiterals,
    MeTTaZero.queryRewrite, MeTTaZero.queryRequestPattern,
    MeTTaZero.queryAnswerPattern, MeTTaZero.metavariable,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

private theorem zeroWithChoice_evaluationRewrite_row :
    LanguageDef.validateRewrite zeroWithChoice MeTTaZero.evaluationRewrite = [] := by
  simp [LanguageDef.validateRewrite, zeroWithChoice_typeNames_eq,
    zeroWithChoice_terms_eq, zeroWithChoiceTermLiterals,
    MeTTaZero.evaluationRewrite, MeTTaZero.evaluationRequestPattern,
    MeTTaZero.evaluationAnswerPattern, MeTTaZero.metavariable,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

private theorem zeroWithChoice_chooseLeftRewrite_row :
    LanguageDef.validateRewrite zeroWithChoice chooseLeftRewrite = [] := by
  simp [LanguageDef.validateRewrite, zeroWithChoice_typeNames_eq,
    zeroWithChoice_terms_eq, zeroWithChoiceTermLiterals, chooseLeftRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

private theorem zeroWithChoice_chooseRightRewrite_row :
    LanguageDef.validateRewrite zeroWithChoice chooseRightRewrite = [] := by
  simp [LanguageDef.validateRewrite, zeroWithChoice_typeNames_eq,
    zeroWithChoice_terms_eq, zeroWithChoiceTermLiterals, chooseRightRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

/-! ## Row validation of the glued presentation's equation and rewrites -/

private theorem quoteAndChoice_quoteDropEquation_row :
    LanguageDef.validateEquation quoteAndChoice
      Prime.LanguageDef.quoteDropEquation = [] := by
  simp [LanguageDef.validateEquation, quoteAndChoice_typeNames_eq,
    quoteAndChoice_terms_eq, quoteAndChoiceTermLiterals,
    Prime.LanguageDef.quoteDropEquation,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

private theorem quoteAndChoice_queryRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice MeTTaZero.queryRewrite = [] := by
  unfold LanguageDef.validateRewrite
  simp only [List.append_eq_nil_iff]
  constructor
  · constructor
    · constructor <;> decide +kernel
    · decide +kernel
  · rw [quoteAndChoice_constructorLabels_eq]
    simp [LanguageDef.validateRulePatterns, MeTTaZero.queryRewrite,
      MeTTaZero.queryRequestPattern, MeTTaZero.queryAnswerPattern,
      MeTTaZero.metavariable, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
      LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

private theorem quoteAndChoice_evaluationRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice MeTTaZero.evaluationRewrite = [] := by
  unfold LanguageDef.validateRewrite
  simp only [List.append_eq_nil_iff]
  constructor
  · constructor
    · constructor <;> decide +kernel
    · decide +kernel
  · rw [quoteAndChoice_constructorLabels_eq]
    simp [LanguageDef.validateRulePatterns, MeTTaZero.evaluationRewrite,
      MeTTaZero.evaluationRequestPattern, MeTTaZero.evaluationAnswerPattern,
      MeTTaZero.metavariable, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
      LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

private theorem quoteAndChoice_evaluationDemandRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice
      Prime.LanguageDef.evaluationDemandRewrite = [] := by
  simp [LanguageDef.validateRewrite, quoteAndChoice_typeNames_eq,
    quoteAndChoice_terms_eq, quoteAndChoiceTermLiterals,
    Prime.LanguageDef.evaluationDemandRewrite,
    MeTTaZero.evaluationRequestPattern,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

private theorem quoteAndChoice_needRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice
      Prime.LanguageDef.needRewrite = [] := by
  unfold LanguageDef.validateRewrite
  simp only [List.append_eq_nil_iff]
  constructor
  · constructor
    · constructor <;> decide +kernel
    · decide +kernel
  · rw [quoteAndChoice_constructorLabels_eq]
    simp [LanguageDef.validateRulePatterns, Prime.LanguageDef.needRewrite,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

private theorem quoteAndChoice_needReturnRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice
      Prime.LanguageDef.needReturnRewrite = [] := by
  simp [LanguageDef.validateRewrite, quoteAndChoice_typeNames_eq,
    quoteAndChoice_terms_eq, quoteAndChoiceTermLiterals,
    Prime.LanguageDef.needReturnRewrite,
    MeTTaZero.evaluationAnswerPattern,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

private theorem quoteAndChoice_reflectedDemandRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice
      Prime.LanguageDef.reflectedDemandRewrite = [] := by
  simp [LanguageDef.validateRewrite, quoteAndChoice_typeNames_eq,
    quoteAndChoice_terms_eq, quoteAndChoiceTermLiterals,
    Prime.LanguageDef.reflectedDemandRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

private theorem quoteAndChoice_chooseLeftRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice chooseLeftRewrite = [] := by
  simp [LanguageDef.validateRewrite, quoteAndChoice_typeNames_eq,
    quoteAndChoice_terms_eq, quoteAndChoiceTermLiterals, chooseLeftRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

private theorem quoteAndChoice_chooseRightRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice chooseRightRewrite = [] := by
  simp [LanguageDef.validateRewrite, quoteAndChoice_typeNames_eq,
    quoteAndChoice_terms_eq, quoteAndChoiceTermLiterals, chooseRightRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

/-! ## Validation of the extension and glued presentations -/

/-- The choice extension of MeTTa Zero passes the five-field validator. -/
theorem zeroWithChoice_validate : zeroWithChoice.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  case hequations => decide
  case htypes => decide
  case hconstructors => decide
  case hrewrites => decide
  case hcategory => decide
  case hparams => decide
  case hsyntax => decide
  case hrewriteValid =>
    intro rewrite membership
    change rewrite ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
      chooseLeftRewrite, chooseRightRewrite] at membership
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl
    · exact zeroWithChoice_queryRewrite_row
    · exact zeroWithChoice_evaluationRewrite_row
    · exact zeroWithChoice_chooseLeftRewrite_row
    · exact zeroWithChoice_chooseRightRewrite_row

/-- The glued quote-and-choice presentation passes the five-field validator.
This is the fact `DialectGluing` left unearned: the glued presentation is a
legitimate object of the structural presentation category. -/
theorem quoteAndChoice_validate : quoteAndChoice.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  case htypes => decide
  case hconstructors => exact quoteAndChoice_constructor_names_nodup
  case hequations => decide
  case hrewrites => exact quoteAndChoice_rewrite_names_nodup
  case hcategory => decide
  case hparams => decide
  case hsyntax => decide
  case hequationValid =>
    intro equation membership
    change equation ∈ [Prime.LanguageDef.quoteDropEquation] at membership
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
    subst membership
    exact quoteAndChoice_quoteDropEquation_row
  case hrewriteValid =>
    intro rewrite membership
    change rewrite ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
      Prime.LanguageDef.evaluationDemandRewrite, Prime.LanguageDef.needRewrite,
      Prime.LanguageDef.needReturnRewrite,
      Prime.LanguageDef.reflectedDemandRewrite,
      chooseLeftRewrite, chooseRightRewrite] at membership
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quoteAndChoice_queryRewrite_row
    · exact quoteAndChoice_evaluationRewrite_row
    · exact quoteAndChoice_evaluationDemandRewrite_row
    · exact quoteAndChoice_needRewrite_row
    · exact quoteAndChoice_needReturnRewrite_row
    · exact quoteAndChoice_reflectedDemandRewrite_row
    · exact quoteAndChoice_chooseLeftRewrite_row
    · exact quoteAndChoice_chooseRightRewrite_row

/-- The validated choice extension.  The base and the quotation extension are
already validated elsewhere: `Prime.LanguageDef.currentZeroPresentation` and
`Prime.LanguageDef.currentPrimePresentation`. -/
def zeroWithChoiceValidated : ValidatedLanguageDef :=
  ⟨zeroWithChoice, zeroWithChoice_validate⟩

/-- The validated glued presentation. -/
def quoteAndChoiceValidated : ValidatedLanguageDef :=
  ⟨quoteAndChoice, quoteAndChoice_validate⟩

/-! ## The left inclusion -/

/-- The left extension includes into any gluing over it, with identity symbol
action: `glue` keeps every left declaration verbatim in append-left position. -/
def leftInclusionMorphism (name : String) (base : LanguageDef)
    {left right : LanguageDef}
    (leftValid : left.validate = [])
    (gluedValid : (glue name base left right).validate = []) :
    StructuralMorphism ⟨left, leftValid⟩ ⟨glue name base left right, gluedValid⟩ where
  symbols := PresentationSymbols.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms rule membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations equation membership := by
    rw [mapEquation_id]
    exact List.mem_append_left _ membership
  mapsRewrites rewrite membership := by
    rw [mapRewriteRule_id]
    exact List.mem_append_left _ membership

/-- The concrete left inclusion: the quotation extension (the Prime spec
probe) into the glued quote-and-choice presentation. -/
def quoteAndChoiceLeftInclusion :
    StructuralMorphism Prime.LanguageDef.currentPrimePresentation
      quoteAndChoiceValidated :=
  leftInclusionMorphism "metta-zero-quote-and-choice" MeTTaZero.language
    Prime.LanguageDef.language_validate quoteAndChoice_validate

/-! ## Right/base collision coverage and the right inclusion -/

/-- Right/base collisions are *covered* when every right declaration whose gluing key
already occurs in the base is itself a declaration of the left extension.
The four keys mirror the four filters of `glue` exactly: type name,
constructor label, equation name, rewrite name.  Collision coverage is what
makes the filter of `glue` harmless: a filtered-out right declaration is not
lost, because the left extension already carries it verbatim.

The `types` field is stated with `List.Mem`, as in `StructuralMorphism`,
because the `Membership String (List TypeDecl)` instance in the syntax module
captures `∈` on type-declaration lists through its out-param. -/
structure RightBaseCollisionsCovered (base left right : LanguageDef) : Prop where
  types : ∀ declaration : TypeDecl, List.Mem declaration right.types →
    declaration.name ∈ base.typeNames → List.Mem declaration left.types
  terms : ∀ rule ∈ right.terms,
    (∃ baseRule ∈ base.terms, baseRule.label = rule.label) → rule ∈ left.terms
  equations : ∀ equation ∈ right.equations,
    (∃ baseEquation ∈ base.equations, baseEquation.name = equation.name) →
      equation ∈ left.equations
  rewrites : ∀ rewrite ∈ right.rewrites,
    (∃ baseRewrite ∈ base.rewrites, baseRewrite.name = rewrite.name) →
      rewrite ∈ left.rewrites

/-- The right extension includes into the gluing when right/base collisions
are covered, with
identity symbol action.  A right declaration either passes the gluing filter
(append-right membership) or collides with the base on its key, in which case
coherence places it verbatim in the left extension (append-left membership). -/
def rightInclusionMorphism (name : String) {base left right : LanguageDef}
    (collisionsCovered : RightBaseCollisionsCovered base left right)
    (rightValid : right.validate = [])
    (gluedValid : (glue name base left right).validate = []) :
    StructuralMorphism ⟨right, rightValid⟩ ⟨glue name base left right, gluedValid⟩ where
  symbols := PresentationSymbols.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    by_cases collision : declaration.name ∈ base.typeNames
    · exact List.mem_append_left _
        (collisionsCovered.types declaration membership collision)
    · refine List.mem_append_right _ (List.mem_filter.mpr ⟨membership, ?_⟩)
      simpa using collision
  mapsTerms rule membership := by
    rw [mapGrammarRule_id]
    by_cases collision : ∃ baseRule ∈ base.terms, baseRule.label = rule.label
    · exact List.mem_append_left _
        (collisionsCovered.terms rule membership collision)
    · refine List.mem_append_right _ (List.mem_filter.mpr ⟨membership, ?_⟩)
      simpa using collision
  mapsEquations equation membership := by
    rw [mapEquation_id]
    by_cases collision :
        ∃ baseEquation ∈ base.equations, baseEquation.name = equation.name
    · exact List.mem_append_left _
        (collisionsCovered.equations equation membership collision)
    · refine List.mem_append_right _ (List.mem_filter.mpr ⟨membership, ?_⟩)
      simpa using collision
  mapsRewrites rewrite membership := by
    rw [mapRewriteRule_id]
    by_cases collision :
        ∃ baseRewrite ∈ base.rewrites, baseRewrite.name = rewrite.name
    · exact List.mem_append_left _
        (collisionsCovered.rewrites rewrite membership collision)
    · refine List.mem_append_right _ (List.mem_filter.mpr ⟨membership, ?_⟩)
      simpa using collision

/-! ## Collision coverage for the concrete span -/

/-- The quote-and-choice span covers every right/base collision: the choice
extension repeats the
base declarations verbatim, and the quotation extension carries all of them. -/
theorem quoteAndChoice_rightBaseCollisionsCovered :
    RightBaseCollisionsCovered MeTTaZero.language Prime.LanguageDef.language
      zeroWithChoice where
  types declaration membership _collision := List.mem_append_left _ membership
  terms := by decide
  equations := by
    intro equation membership _collision
    rw [show zeroWithChoice.equations = [] from by decide] at membership
    cases membership
  rewrites := by
    intro rewrite membership collision
    change rewrite ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
      chooseLeftRewrite, chooseRightRewrite] at membership
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl
    · change _ ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
        Prime.LanguageDef.evaluationDemandRewrite, Prime.LanguageDef.needRewrite,
        Prime.LanguageDef.needReturnRewrite,
        Prime.LanguageDef.reflectedDemandRewrite]
      simp
    · change _ ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
        Prime.LanguageDef.evaluationDemandRewrite, Prime.LanguageDef.needRewrite,
        Prime.LanguageDef.needReturnRewrite,
        Prime.LanguageDef.reflectedDemandRewrite]
      simp
    · obtain ⟨baseRewrite, baseMembership, nameEqual⟩ := collision
      change baseRewrite ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite]
        at baseMembership
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at baseMembership
      rcases baseMembership with rfl | rfl <;> exact absurd nameEqual (by decide)
    · obtain ⟨baseRewrite, baseMembership, nameEqual⟩ := collision
      change baseRewrite ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite]
        at baseMembership
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at baseMembership
      rcases baseMembership with rfl | rfl <;> exact absurd nameEqual (by decide)

/-- The concrete right inclusion: the choice extension into the glued
quote-and-choice presentation, through coherence. -/
def quoteAndChoiceRightInclusion :
    StructuralMorphism zeroWithChoiceValidated quoteAndChoiceValidated :=
  rightInclusionMorphism "metta-zero-quote-and-choice"
    quoteAndChoice_rightBaseCollisionsCovered
    zeroWithChoice_validate quoteAndChoice_validate

/-! ## Negative instances

Two distinct failure modes, deliberately separated:

* an *uncovered right/base collision* (`zeroWithDivergentQuery`): the right dialect
  redeclares the base constructor `zero-query` at different structure, so the
  right inclusion is unavailable along this design — and `glue` silently
  discards the divergent declaration, which is exactly the data loss
  `RightBaseCollisionsCovered` rules out;
* a *collision-covered but invalid* gluing (the `clashingQuote` span): the
  collision predicate
  constrains only base-key collisions, so the clash span satisfies it, yet its
  glued presentation fails validation because the left and right extensions
  declare the same label at different categories
  (`no_presentation_glues_clash` in `DialectGluing`). -/

/-- A rival dialect's redeclaration of `zero-query`: same label, different
category and arity. -/
def divergentQueryConstructor : GrammarRule :=
  { label := "zero-query"
    category := "Atom"
    params := []
    syntaxPattern := [] }

/-- A right side that redeclares a base constructor divergently. -/
def zeroWithDivergentQuery : LanguageDef :=
  { MeTTaZero.language with
    name := "metta-zero-divergent-query"
    terms := [divergentQueryConstructor] }

/-- Negative instance: a span whose right side redeclares a base label with
different content does not cover its right/base collision. -/
theorem zeroWithDivergentQuery_rightBaseCollisionsNotCovered :
    ¬ RightBaseCollisionsCovered MeTTaZero.language Prime.LanguageDef.language
      zeroWithDivergentQuery := by
  intro collisionsCovered
  have placed :=
    collisionsCovered.terms divergentQueryConstructor (by decide) (by decide)
  exact absurd placed (by decide)

/-- What incoherence costs: `glue` silently drops the divergent declaration,
so the authored right dialect is *not* included in the glued presentation. -/
theorem divergentQueryConstructor_not_glued :
    divergentQueryConstructor ∉
      (glue "metta-zero-divergent-glued" MeTTaZero.language
        Prime.LanguageDef.language zeroWithDivergentQuery).terms := by
  decide

/-- The clash side from `DialectGluing`, packaged as a right extension. -/
def zeroWithClashingQuote : LanguageDef :=
  { MeTTaZero.language with
    name := "metta-zero-with-clashing-quote"
    terms := MeTTaZero.language.terms ++ [clashingQuote] }

/-- The glued clash presentation. -/
def clashingGlued : LanguageDef :=
  glue "metta-zero-quote-clash" MeTTaZero.language Prime.LanguageDef.language
    zeroWithClashingQuote

/-- The clash span's right/base collisions are covered: `clashingQuote`
collides with the left extension, not with the base, and this predicate
constrains base collisions only. -/
theorem clashSpan_rightBaseCollisionsCovered :
    RightBaseCollisionsCovered MeTTaZero.language Prime.LanguageDef.language
      zeroWithClashingQuote where
  types declaration membership _collision := List.mem_append_left _ membership
  terms := by decide
  equations := by
    intro equation membership _collision
    rw [show zeroWithClashingQuote.equations = [] from by decide] at membership
    cases membership
  rewrites := by
    intro rewrite membership _collision
    change rewrite ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite]
      at membership
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
    rcases membership with rfl | rfl <;>
      · change _ ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
          Prime.LanguageDef.evaluationDemandRewrite,
          Prime.LanguageDef.needRewrite, Prime.LanguageDef.needReturnRewrite,
          Prime.LanguageDef.reflectedDemandRewrite]
        simp

/-- Negative canary: the glued clash presentation fails validation.  Both the
probe's quotation constructor and its rival survive the gluing filter (their
labels collide between left and right, not with the base), so the glued
constructor labels are not duplicate-free and `no_presentation_glues_clash`
applies.  Collision coverage (`clashSpan_rightBaseCollisionsCovered`) does not
rescue it: validation is
an independent gate. -/
theorem clashingGlued_validate_ne_nil : clashingGlued.validate ≠ [] := by
  intro valid
  exact no_presentation_glues_clash clashingGlued (by decide) (by decide)
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil clashingGlued valid)

/-! ## The cocone square -/

/-- The base includes into the choice extension with identity symbol action.
The base → left leg already exists as
`Prime.LanguageDef.currentZeroToPrimePresentation`. -/
def zeroToZeroWithChoiceMorphism :
    StructuralMorphism Prime.LanguageDef.currentZeroPresentation
      zeroWithChoiceValidated where
  symbols := PresentationSymbols.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact membership
  mapsTerms rule membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations equation membership := by
    rw [mapEquation_id]
    exact membership
  mapsRewrites rewrite membership := by
    rw [mapRewriteRule_id]
    exact List.mem_append_left _ membership

/-- The cocone square commutes on the nose: both composites are structural
morphisms with identity symbol action, and structural-morphism identity is
determined by symbol action. -/
theorem quoteAndChoice_gluingSquare_commutes :
    StructuralMorphism.comp Prime.LanguageDef.currentZeroToPrimePresentation
        quoteAndChoiceLeftInclusion =
      StructuralMorphism.comp zeroToZeroWithChoiceMorphism
        quoteAndChoiceRightInclusion :=
  StructuralMorphism.ext rfl

/-- The square in the extensional quotient: both composites act identically on
every authored declaration of the base. -/
theorem quoteAndChoice_gluingSquare_equivalent :
    Equivalent
      (StructuralMorphism.comp Prime.LanguageDef.currentZeroToPrimePresentation
        quoteAndChoiceLeftInclusion)
      (StructuralMorphism.comp zeroToZeroWithChoiceMorphism
        quoteAndChoiceRightInclusion) :=
  quoteAndChoice_gluingSquare_commutes ▸ Equivalent.refl _

/-- The square as arrow equality in the structural presentation category. -/
theorem quoteAndChoice_gluingSquare_commutes_arrow :
    Arrow.ofMorphism
        (StructuralMorphism.comp Prime.LanguageDef.currentZeroToPrimePresentation
          quoteAndChoiceLeftInclusion) =
      Arrow.ofMorphism
        (StructuralMorphism.comp zeroToZeroWithChoiceMorphism
          quoteAndChoiceRightInclusion) :=
  congrArg Arrow.ofMorphism quoteAndChoice_gluingSquare_commutes

/-! ## A same-global-action mediator (not a universal property) -/

/-- Structural maps out of the left and right extensions with the same total
symbol action induce a structural map out of the glued presentation: a glued
declaration comes either from the left extension or through the gluing filter
from the right one, and is mapped accordingly.  This special case does not
cover a general cocone, whose maps need only agree after restriction to the
shared base. -/
def sameActionMediator (name : String) {base left right : LanguageDef}
    {target : ValidatedLanguageDef}
    {leftValid : left.validate = []} {rightValid : right.validate = []}
    (gluedValid : (glue name base left right).validate = [])
    (leftMorphism : StructuralMorphism ⟨left, leftValid⟩ target)
    (rightMorphism : StructuralMorphism ⟨right, rightValid⟩ target)
    (sharedSymbols : leftMorphism.symbols = rightMorphism.symbols) :
    StructuralMorphism ⟨glue name base left right, gluedValid⟩ target where
  symbols := leftMorphism.symbols
  mapsTypes declaration membership := by
    have split : List.Mem declaration (left.types ++ right.types.filter
        (fun declaration => !(base.typeNames.contains declaration.name))) :=
      membership
    rcases List.mem_append.mp split with leftMember | rightMember
    · exact leftMorphism.mapsTypes declaration leftMember
    · rw [sharedSymbols]
      exact rightMorphism.mapsTypes declaration (List.mem_filter.mp rightMember).1
  mapsTerms rule membership := by
    have split : rule ∈ left.terms ++ right.terms.filter
        (fun rule => !(base.terms.any (·.label == rule.label))) :=
      membership
    rcases List.mem_append.mp split with leftMember | rightMember
    · exact leftMorphism.mapsTerms rule leftMember
    · rw [sharedSymbols]
      exact rightMorphism.mapsTerms rule (List.mem_filter.mp rightMember).1
  mapsEquations equation membership := by
    have split : equation ∈ left.equations ++ right.equations.filter
        (fun equation => !(base.equations.any (·.name == equation.name))) :=
      membership
    rcases List.mem_append.mp split with leftMember | rightMember
    · exact leftMorphism.mapsEquations equation leftMember
    · rw [sharedSymbols]
      exact rightMorphism.mapsEquations equation
        (List.mem_filter.mp rightMember).1
  mapsRewrites rewrite membership := by
    have split : rewrite ∈ left.rewrites ++ right.rewrites.filter
        (fun rewrite => !(base.rewrites.any (·.name == rewrite.name))) :=
      membership
    rcases List.mem_append.mp split with leftMember | rightMember
    · exact leftMorphism.mapsRewrites rewrite leftMember
    · rw [sharedSymbols]
      exact rightMorphism.mapsRewrites rewrite (List.mem_filter.mp rightMember).1

/-- The left triangle commutes on the nose. -/
theorem sameActionMediator_comp_left_inclusion (name : String)
    {base left right : LanguageDef} {target : ValidatedLanguageDef}
    {leftValid : left.validate = []} {rightValid : right.validate = []}
    (gluedValid : (glue name base left right).validate = [])
    (leftMorphism : StructuralMorphism ⟨left, leftValid⟩ target)
    (rightMorphism : StructuralMorphism ⟨right, rightValid⟩ target)
    (sharedSymbols : leftMorphism.symbols = rightMorphism.symbols) :
    StructuralMorphism.comp (leftInclusionMorphism name base leftValid gluedValid)
        (sameActionMediator name gluedValid leftMorphism rightMorphism
          sharedSymbols) =
      leftMorphism :=
  StructuralMorphism.ext rfl

/-- The right triangle commutes on the nose, given the shared symbol action;
the coherence witness is needed only to state the right inclusion. -/
theorem sameActionMediator_comp_right_inclusion (name : String)
    {base left right : LanguageDef} {target : ValidatedLanguageDef}
    (collisionsCovered : RightBaseCollisionsCovered base left right)
    {leftValid : left.validate = []} {rightValid : right.validate = []}
    (gluedValid : (glue name base left right).validate = [])
    (leftMorphism : StructuralMorphism ⟨left, leftValid⟩ target)
    (rightMorphism : StructuralMorphism ⟨right, rightValid⟩ target)
    (sharedSymbols : leftMorphism.symbols = rightMorphism.symbols) :
    StructuralMorphism.comp
        (rightInclusionMorphism name collisionsCovered rightValid gluedValid)
        (sameActionMediator name gluedValid leftMorphism rightMorphism
          sharedSymbols) =
      rightMorphism :=
  StructuralMorphism.ext (by rw [← sharedSymbols]; rfl)

/-! ## Why base agreement is strictly weaker than one global action

The following all-sort presentations isolate the categorical gap without any
operational or validator noise.  Both component maps fix the shared sort `B`.
The left map independently renames `L`, while the right map independently
renames `R`.  Hence the two composites out of the base are extensionally
equal, although the total symbol actions are unequal.  A piecewise mediator
exists and satisfies both triangles in the quotient category.
-/

private def agreementBase : LanguageDef :=
  { name := "gluing-base-agreement-base"
    types := [TypeDecl.plain "B"]
    terms := []
    equations := []
    rewrites := [] }

private def agreementLeft : LanguageDef :=
  { name := "gluing-base-agreement-left"
    types := [TypeDecl.plain "B", TypeDecl.plain "L"]
    terms := []
    equations := []
    rewrites := [] }

private def agreementRight : LanguageDef :=
  { name := "gluing-base-agreement-right"
    types := [TypeDecl.plain "B", TypeDecl.plain "R"]
    terms := []
    equations := []
    rewrites := [] }

private def agreementTarget : LanguageDef :=
  { name := "gluing-base-agreement-target"
    types := [TypeDecl.plain "B", TypeDecl.plain "TL", TypeDecl.plain "TR"]
    terms := []
    equations := []
    rewrites := [] }

private theorem agreementBase_validate : agreementBase.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [agreementBase, LanguageDef.typeNames, TypeDecl.plain]

private theorem agreementLeft_validate : agreementLeft.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [agreementLeft, LanguageDef.typeNames, TypeDecl.plain]

private theorem agreementRight_validate : agreementRight.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [agreementRight, LanguageDef.typeNames, TypeDecl.plain]

private theorem agreementTarget_validate : agreementTarget.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [agreementTarget, LanguageDef.typeNames, TypeDecl.plain]

private def agreementGlued : LanguageDef :=
  glue "gluing-base-agreement" agreementBase agreementLeft agreementRight

private theorem agreementGlued_validate : agreementGlued.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [agreementGlued, glue, agreementBase, agreementLeft, agreementRight,
      LanguageDef.typeNames, TypeDecl.plain]

private def renameSort (source target : String) (name : String) : String :=
  if name = source then target else name

private def agreementLeftSymbols : PresentationSymbols :=
  { PresentationSymbols.id with sort := renameSort "L" "TL" }

private def agreementRightSymbols : PresentationSymbols :=
  { PresentationSymbols.id with sort := renameSort "R" "TR" }

private def agreementMediatorSymbols : PresentationSymbols :=
  { PresentationSymbols.id with
    sort := fun name =>
      if name = "L" then "TL" else if name = "R" then "TR" else name }

private theorem agreementTarget_has_B :
    List.Mem (TypeDecl.plain "B") agreementTarget.types := by
  change List.Mem (TypeDecl.plain "B")
    [TypeDecl.plain "B", TypeDecl.plain "TL", TypeDecl.plain "TR"]
  exact List.Mem.head _

private theorem agreementTarget_has_TL :
    List.Mem (TypeDecl.plain "TL") agreementTarget.types := by
  change List.Mem (TypeDecl.plain "TL")
    [TypeDecl.plain "B", TypeDecl.plain "TL", TypeDecl.plain "TR"]
  exact List.Mem.tail _ (List.Mem.head _)

private theorem agreementTarget_has_TR :
    List.Mem (TypeDecl.plain "TR") agreementTarget.types := by
  change List.Mem (TypeDecl.plain "TR")
    [TypeDecl.plain "B", TypeDecl.plain "TL", TypeDecl.plain "TR"]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private def agreementLeftMap :
    StructuralMorphism ⟨agreementLeft, agreementLeft_validate⟩
      ⟨agreementTarget, agreementTarget_validate⟩ where
  symbols := agreementLeftSymbols
  mapsTypes declaration membership := by
    change List.Mem declaration [TypeDecl.plain "B", TypeDecl.plain "L"]
      at membership
    rcases List.mem_cons.mp membership with head | tail
    · subst declaration
      simpa [agreementLeftSymbols, renameSort, mapTypeDecl, TypeDecl.plain] using
        agreementTarget_has_B
    · have head := List.mem_singleton.mp tail
      subst declaration
      simpa [agreementLeftSymbols, renameSort, mapTypeDecl, TypeDecl.plain] using
        agreementTarget_has_TL
  mapsTerms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  mapsEquations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

private def agreementRightMap :
    StructuralMorphism ⟨agreementRight, agreementRight_validate⟩
      ⟨agreementTarget, agreementTarget_validate⟩ where
  symbols := agreementRightSymbols
  mapsTypes declaration membership := by
    change List.Mem declaration [TypeDecl.plain "B", TypeDecl.plain "R"]
      at membership
    rcases List.mem_cons.mp membership with head | tail
    · subst declaration
      simpa [agreementRightSymbols, renameSort, mapTypeDecl, TypeDecl.plain] using
        agreementTarget_has_B
    · have head := List.mem_singleton.mp tail
      subst declaration
      simpa [agreementRightSymbols, renameSort, mapTypeDecl, TypeDecl.plain] using
        agreementTarget_has_TR
  mapsTerms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  mapsEquations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

private theorem agreementRightBaseCollisionsCovered :
    RightBaseCollisionsCovered agreementBase agreementLeft agreementRight where
  types declaration rightMember collision := by
    change List.Mem declaration [TypeDecl.plain "B", TypeDecl.plain "R"]
      at rightMember
    rcases List.mem_cons.mp rightMember with head | tail
    · subst declaration
      change List.Mem (TypeDecl.plain "B")
        [TypeDecl.plain "B", TypeDecl.plain "L"]
      exact List.Mem.head _
    · have head := List.mem_singleton.mp tail
      subst declaration
      simp [agreementBase, LanguageDef.typeNames, TypeDecl.plain] at collision
  terms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  equations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  rewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

private def agreementLeftInclusion :
    StructuralMorphism ⟨agreementLeft, agreementLeft_validate⟩
      ⟨agreementGlued, agreementGlued_validate⟩ :=
  leftInclusionMorphism "gluing-base-agreement" agreementBase
    agreementLeft_validate agreementGlued_validate

private def agreementRightInclusion :
    StructuralMorphism ⟨agreementRight, agreementRight_validate⟩
      ⟨agreementGlued, agreementGlued_validate⟩ :=
  rightInclusionMorphism "gluing-base-agreement"
    agreementRightBaseCollisionsCovered
    agreementRight_validate agreementGlued_validate

private def agreementBaseIntoLeft :
    StructuralMorphism ⟨agreementBase, agreementBase_validate⟩
      ⟨agreementLeft, agreementLeft_validate⟩ where
  symbols := PresentationSymbols.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    change List.Mem declaration [TypeDecl.plain "B"] at membership
    have head := List.mem_singleton.mp membership
    subst declaration
    change List.Mem (TypeDecl.plain "B")
      [TypeDecl.plain "B", TypeDecl.plain "L"]
    exact List.Mem.head _
  mapsTerms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  mapsEquations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

private def agreementBaseIntoRight :
    StructuralMorphism ⟨agreementBase, agreementBase_validate⟩
      ⟨agreementRight, agreementRight_validate⟩ where
  symbols := PresentationSymbols.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    change List.Mem declaration [TypeDecl.plain "B"] at membership
    have head := List.mem_singleton.mp membership
    subst declaration
    change List.Mem (TypeDecl.plain "B")
      [TypeDecl.plain "B", TypeDecl.plain "R"]
    exact List.Mem.head _
  mapsTerms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  mapsEquations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

private def agreementMediator :
    StructuralMorphism ⟨agreementGlued, agreementGlued_validate⟩
      ⟨agreementTarget, agreementTarget_validate⟩ where
  symbols := agreementMediatorSymbols
  mapsTypes declaration membership := by
    change List.Mem declaration
      [TypeDecl.plain "B", TypeDecl.plain "L", TypeDecl.plain "R"]
      at membership
    rcases List.mem_cons.mp membership with head | tail
    · subst declaration
      simpa [agreementMediatorSymbols, mapTypeDecl, TypeDecl.plain] using
        agreementTarget_has_B
    · rcases List.mem_cons.mp tail with head | tail
      · subst declaration
        simpa [agreementMediatorSymbols, mapTypeDecl, TypeDecl.plain] using
          agreementTarget_has_TL
      · have head := List.mem_singleton.mp tail
        subst declaration
        simpa [agreementMediatorSymbols, mapTypeDecl, TypeDecl.plain] using
          agreementTarget_has_TR
  mapsTerms rule membership := by
    change List.Mem rule ([] ++ []) at membership
    cases membership
  mapsEquations equation membership := by
    change List.Mem equation ([] ++ []) at membership
    cases membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite ([] ++ []) at membership
    cases membership

/-
The definitions above intentionally spell out the two base inclusions and the
piecewise mediator.  Keeping them independent of the special-case helper is
what makes the canary capable of detecting that helper's stronger premise.
-/

/-- The two component maps form a genuine cocone over the shared base. -/
theorem agreement_maps_agree_on_base :
    Equivalent
      (StructuralMorphism.comp agreementBaseIntoLeft agreementLeftMap)
      (StructuralMorphism.comp agreementBaseIntoRight agreementRightMap) where
  types declaration membership := by
    change List.Mem declaration [TypeDecl.plain "B"] at membership
    have head := List.mem_singleton.mp membership
    subst declaration
    simp [StructuralMorphism.comp, PresentationSymbols.comp,
      agreementBaseIntoLeft, agreementBaseIntoRight, agreementLeftMap,
      agreementRightMap, agreementLeftSymbols, agreementRightSymbols,
      renameSort, mapTypeDecl, PresentationSymbols.id, TypeDecl.plain]
  terms rule membership := by
    change List.Mem rule [] at membership
    cases membership
  equations equation membership := by
    change List.Mem equation [] at membership
    cases membership
  rewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    cases membership

/-- The same cocone's total symbol actions differ away from the shared base.
Consequently, base agreement cannot justify the `sharedSymbols` premise of
`sameActionMediator`. -/
theorem baseAgreement_does_not_imply_same_global_action :
    agreementLeftMap.symbols ≠ agreementRightMap.symbols := by
  intro equal
  have atLeft := congrArg (fun symbols => symbols.sort "L") equal
  simp [agreementLeftMap, agreementRightMap, agreementLeftSymbols,
    agreementRightSymbols, renameSort] at atLeft

/-- A mediator nevertheless exists for this cocone in the extensional
category; the missing general construction must synthesize such a piecewise
symbol action rather than require the two component actions to be equal. -/
theorem agreement_mediator_triangles :
    Equivalent
        (StructuralMorphism.comp agreementLeftInclusion agreementMediator)
        agreementLeftMap ∧
      Equivalent
        (StructuralMorphism.comp agreementRightInclusion agreementMediator)
        agreementRightMap := by
  constructor
  · constructor <;> intro declaration membership
    · change List.Mem declaration [TypeDecl.plain "B", TypeDecl.plain "L"]
        at membership
      rcases List.mem_cons.mp membership with head | tail
      · subst declaration
        simp [StructuralMorphism.comp, PresentationSymbols.comp,
          agreementLeftInclusion, agreementMediator, agreementLeftMap,
          agreementMediatorSymbols, agreementLeftSymbols, renameSort,
          mapTypeDecl, leftInclusionMorphism, PresentationSymbols.id,
          TypeDecl.plain]
      · have head := List.mem_singleton.mp tail
        subst declaration
        simp [StructuralMorphism.comp, PresentationSymbols.comp,
          agreementLeftInclusion, agreementMediator, agreementLeftMap,
          agreementMediatorSymbols, agreementLeftSymbols, renameSort,
          mapTypeDecl, leftInclusionMorphism, PresentationSymbols.id,
          TypeDecl.plain]
    · change List.Mem declaration [] at membership; cases membership
    · change List.Mem declaration [] at membership; cases membership
    · change List.Mem declaration [] at membership; cases membership

  · constructor <;> intro declaration membership
    · change List.Mem declaration [TypeDecl.plain "B", TypeDecl.plain "R"]
        at membership
      rcases List.mem_cons.mp membership with head | tail
      · subst declaration
        simp [StructuralMorphism.comp, PresentationSymbols.comp,
          agreementRightInclusion, agreementMediator, agreementRightMap,
          agreementMediatorSymbols, agreementRightSymbols, renameSort,
          mapTypeDecl, rightInclusionMorphism, PresentationSymbols.id,
          TypeDecl.plain]
      · have head := List.mem_singleton.mp tail
        subst declaration
        simp [StructuralMorphism.comp, PresentationSymbols.comp,
          agreementRightInclusion, agreementMediator, agreementRightMap,
          agreementMediatorSymbols, agreementRightSymbols, renameSort,
          mapTypeDecl, rightInclusionMorphism, PresentationSymbols.id,
          TypeDecl.plain]
    · change List.Mem declaration [] at membership; cases membership
    · change List.Mem declaration [] at membership; cases membership
    · change List.Mem declaration [] at membership; cases membership

/-- There is a validated gluing cocone whose component maps agree on the
shared base but have different total symbol actions, while a piecewise
mediator still satisfies both triangles.  This exposes the exact scope gap in
`sameActionMediator` without exporting the private canary presentations.

The result is deliberately existential: it proves that a general gluing
construction must synthesize declaration-supported piecewise actions.  It
does not claim that the current `glue` operation already has a pushout
universal property for every compatible span. -/
theorem exists_base_agreeing_cocone_with_piecewise_mediator :
    ∃ (base left right glued target : ValidatedLanguageDef)
      (baseIntoLeft : StructuralMorphism base left)
      (baseIntoRight : StructuralMorphism base right)
      (leftInclusion : StructuralMorphism left glued)
      (rightInclusion : StructuralMorphism right glued)
      (leftMap : StructuralMorphism left target)
      (rightMap : StructuralMorphism right target)
      (mediator : StructuralMorphism glued target),
      glued.language =
          glue "gluing-base-agreement" base.language left.language
            right.language ∧
        Equivalent
            (StructuralMorphism.comp baseIntoLeft leftMap)
            (StructuralMorphism.comp baseIntoRight rightMap) ∧
        leftMap.symbols ≠ rightMap.symbols ∧
        Equivalent
            (StructuralMorphism.comp leftInclusion mediator) leftMap ∧
        Equivalent
            (StructuralMorphism.comp rightInclusion mediator) rightMap := by
  refine ⟨⟨agreementBase, agreementBase_validate⟩,
    ⟨agreementLeft, agreementLeft_validate⟩,
    ⟨agreementRight, agreementRight_validate⟩,
    ⟨agreementGlued, agreementGlued_validate⟩,
    ⟨agreementTarget, agreementTarget_validate⟩,
    agreementBaseIntoLeft, agreementBaseIntoRight,
    agreementLeftInclusion, agreementRightInclusion,
    agreementLeftMap, agreementRightMap, agreementMediator, ?_⟩
  exact ⟨rfl, agreement_maps_agree_on_base,
    baseAgreement_does_not_imply_same_global_action,
    agreement_mediator_triangles.1, agreement_mediator_triangles.2⟩

/-! ## Axiom audit -/

#print axioms zeroWithChoice_validate
#print axioms quoteAndChoice_validate
#print axioms quoteAndChoiceLeftInclusion
#print axioms quoteAndChoiceRightInclusion
#print axioms quoteAndChoice_rightBaseCollisionsCovered
#print axioms zeroWithDivergentQuery_rightBaseCollisionsNotCovered
#print axioms clashSpan_rightBaseCollisionsCovered
#print axioms clashingGlued_validate_ne_nil
#print axioms quoteAndChoice_gluingSquare_commutes
#print axioms sameActionMediator_comp_left_inclusion
#print axioms sameActionMediator_comp_right_inclusion
#print axioms agreement_maps_agree_on_base
#print axioms baseAgreement_does_not_imply_same_global_action
#print axioms agreement_mediator_triangles
#print axioms exists_base_agreeing_cocone_with_piecewise_mediator

end Mettapedia.GSLT.LanguageDef.DialectGluingMorphisms
