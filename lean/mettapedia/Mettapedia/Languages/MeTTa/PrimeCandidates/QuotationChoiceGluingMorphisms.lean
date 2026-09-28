import Mettapedia.GSLT.LanguageDef.DialectGluingMorphisms
import Mettapedia.Languages.MeTTa.PrimeCandidates.QuotationChoiceGluing

/-!
# Structural cocone for the quotation-and-choice gluing candidate

The selected quotation and choice extensions of MeTTaZero instantiate the
generic inclusion and collision-coverage laws of `DialectGluingMorphisms`.
Both the choice extension and the glued presentation pass the full authored
validator.  Their structural inclusions form a commuting cocone on the nose,
and therefore also in the extensional arrow quotient.

Two connected negative controls retain distinct boundaries.  A divergent
redeclaration of a base constructor fails collision coverage and is lost by
the gluing filter.  A quotation-label clash satisfies base-collision coverage
but fails validation.  These specimens do not establish a pushout universal
property or select a final language.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.QuotationChoiceGluingMorphisms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DialectGluing
open Mettapedia.GSLT.LanguageDef.DialectGluingMorphisms
open Mettapedia.GSLT.LanguageDef.StructuralLanguageDefCategory
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.NucleusDerivedModalTyping
open Mettapedia.Languages.MeTTa.PrimeCandidates.QuotationChoiceGluing

/-! ## Literal readouts of the authored constructor lists

The constructor helpers of `MeTTaZero` and `PrimeCandidates.LanguageDef` are private, so
row-level validation proofs in this module first rewrite the constructor lists
to proof-local explicit literals.  Each readout is kernel-checked by `decide`
against the authored definitions and is not treated as an independent
authority.  (This mirrors the projection-transparent bridge lemmas used
inside `PrimeCandidates.LanguageDef`.) -/

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
   { label := "prime-quote", category := "CandidateName",
     params := [.simple "term" (.base "Atom")], syntaxPattern := [] },
   { label := "prime-drop", category := "Atom",
     params := [.simple "name" (.base "CandidateName")], syntaxPattern := [] },
   { label := "prime-evaluate-name", category := "Process",
     params := [.simple "space" (.base "Space"), .simple "name" (.base "CandidateName")],
     syntaxPattern := [] },
   { label := "prime-need", category := "Process",
     params := [.simple "space" (.base "Space"), .simple "subject" (.base "Atom")],
     syntaxPattern := [] },
   { label := "prime-need-answer", category := "Process",
     params := [.simple "answer" (.base "Atom"),
       .simple "receipt" (.base "CandidateReceipt")],
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
   { label := "prime-receipt", category := "CandidateReceipt",
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
      ["Atom", "Space", "Process", "Alternatives", "CandidateName", "CandidateReceipt"] := by
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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem zeroWithChoice_queryRewrite_row :
    LanguageDef.validateRewrite zeroWithChoice MeTTaZero.queryRewrite = [] := by
  simp [LanguageDef.validateRewrite, LanguageDef.validateTypeExpr_eq_nil_iff, zeroWithChoice_typeNames_eq,
    zeroWithChoice_terms_eq, zeroWithChoiceTermLiterals,
    MeTTaZero.queryRewrite, MeTTaZero.queryRequestPattern,
    MeTTaZero.queryAnswerPattern, MeTTaZero.metavariable,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
    LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem zeroWithChoice_evaluationRewrite_row :
    LanguageDef.validateRewrite zeroWithChoice MeTTaZero.evaluationRewrite = [] := by
  simp [LanguageDef.validateRewrite, LanguageDef.validateTypeExpr_eq_nil_iff, zeroWithChoice_typeNames_eq,
    zeroWithChoice_terms_eq, zeroWithChoiceTermLiterals,
    MeTTaZero.evaluationRewrite, MeTTaZero.evaluationRequestPattern,
    MeTTaZero.evaluationAnswerPattern, MeTTaZero.metavariable,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
    LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem zeroWithChoice_chooseLeftRewrite_row :
    LanguageDef.validateRewrite zeroWithChoice chooseLeftRewrite = [] := by
  simp [LanguageDef.validateRewrite, LanguageDef.validateTypeExpr_eq_nil_iff, zeroWithChoice_typeNames_eq,
    zeroWithChoice_terms_eq, zeroWithChoiceTermLiterals, chooseLeftRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem zeroWithChoice_chooseRightRewrite_row :
    LanguageDef.validateRewrite zeroWithChoice chooseRightRewrite = [] := by
  simp [LanguageDef.validateRewrite, LanguageDef.validateTypeExpr_eq_nil_iff, zeroWithChoice_typeNames_eq,
    zeroWithChoice_terms_eq, zeroWithChoiceTermLiterals, chooseRightRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

/-! ## Row validation of the glued presentation's equation and rewrites -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem quoteAndChoice_quoteDropEquation_row :
    LanguageDef.validateEquation quoteAndChoice
      PrimeCandidates.LanguageDef.quoteDropEquation = [] := by
  simp [LanguageDef.validateEquation, LanguageDef.validateTypeExpr_eq_nil_iff, quoteAndChoice_typeNames_eq,
    quoteAndChoice_terms_eq, quoteAndChoiceTermLiterals,
    PrimeCandidates.LanguageDef.quoteDropEquation,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
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
      LanguageDef.premiseLocallyScoped,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
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
      LanguageDef.premiseLocallyScoped,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

set_option maxHeartbeats 200000 in
private theorem demand_left_fvars : LanguageDef.patternFvarNames [] (PrimeCandidates.LanguageDef.evaluationDemandRewrite.left) = ["space", "subject"] := by
  simp [PrimeCandidates.LanguageDef.evaluationDemandRewrite,
    MeTTaZero.evaluationRequestPattern,
    LanguageDef.patternFvarNames, Pattern.freeFvarNames]

set_option maxHeartbeats 200000 in
private theorem demand_left_binders : LanguageDef.patternBinderNames (PrimeCandidates.LanguageDef.evaluationDemandRewrite.left) = [] := by
  simp [PrimeCandidates.LanguageDef.evaluationDemandRewrite,
    MeTTaZero.evaluationRequestPattern,
    LanguageDef.patternBinderNames]

set_option maxHeartbeats 200000 in
private theorem demand_left_scope : Pattern.isWellScoped (PrimeCandidates.LanguageDef.evaluationDemandRewrite.left) = true := by
  simp [PrimeCandidates.LanguageDef.evaluationDemandRewrite,
    MeTTaZero.evaluationRequestPattern,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

set_option maxHeartbeats 200000 in
private theorem demand_right_fvars : LanguageDef.patternFvarNames [] (PrimeCandidates.LanguageDef.evaluationDemandRewrite.right) = ["space", "subject"] := by
  simp [PrimeCandidates.LanguageDef.evaluationDemandRewrite,
    MeTTaZero.evaluationRequestPattern,
    LanguageDef.patternFvarNames, Pattern.freeFvarNames]

set_option maxHeartbeats 200000 in
private theorem demand_right_binders : LanguageDef.patternBinderNames (PrimeCandidates.LanguageDef.evaluationDemandRewrite.right) = [] := by
  simp [PrimeCandidates.LanguageDef.evaluationDemandRewrite,
    MeTTaZero.evaluationRequestPattern,
    LanguageDef.patternBinderNames]

set_option maxHeartbeats 200000 in
private theorem demand_right_scope : Pattern.isWellScoped (PrimeCandidates.LanguageDef.evaluationDemandRewrite.right) = true := by
  simp [PrimeCandidates.LanguageDef.evaluationDemandRewrite,
    MeTTaZero.evaluationRequestPattern,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

set_option maxHeartbeats 200000 in
private theorem reflected_left_fvars : LanguageDef.patternFvarNames [] (PrimeCandidates.LanguageDef.reflectedDemandRewrite.left) = ["space", "subject"] := by
  simp [PrimeCandidates.LanguageDef.reflectedDemandRewrite, LanguageDef.patternFvarNames, Pattern.freeFvarNames]

set_option maxHeartbeats 200000 in
private theorem reflected_left_binders : LanguageDef.patternBinderNames (PrimeCandidates.LanguageDef.reflectedDemandRewrite.left) = [] := by
  simp [PrimeCandidates.LanguageDef.reflectedDemandRewrite, LanguageDef.patternBinderNames]

set_option maxHeartbeats 200000 in
private theorem reflected_left_scope : Pattern.isWellScoped (PrimeCandidates.LanguageDef.reflectedDemandRewrite.left) = true := by
  simp [PrimeCandidates.LanguageDef.reflectedDemandRewrite, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]


private theorem reflected_right_fvars :
    LanguageDef.patternFvarNames [] PrimeCandidates.LanguageDef.reflectedDemandRewrite.right = ["space", "subject"] :=
  demand_right_fvars

private theorem reflected_right_binders :
    LanguageDef.patternBinderNames PrimeCandidates.LanguageDef.reflectedDemandRewrite.right = [] :=
  demand_right_binders

private theorem reflected_right_scope :
    Pattern.isWellScoped PrimeCandidates.LanguageDef.reflectedDemandRewrite.right = true :=
  demand_right_scope

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem quoteAndChoice_evaluationDemandRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice
      PrimeCandidates.LanguageDef.evaluationDemandRewrite = [] := by
  unfold LanguageDef.validateRewrite
  simp only [List.append_eq_nil_iff]
  constructor
  · constructor
    · constructor <;> decide +kernel
    · decide +kernel
  · rw [quoteAndChoice_constructorLabels_eq]
    simp only [LanguageDef.validateRulePatterns,
      show PrimeCandidates.LanguageDef.evaluationDemandRewrite.premises = [] from rfl,
      List.flatMap_nil, List.append_nil, List.all_nil,
      demand_left_fvars, demand_left_binders, demand_left_scope,
      demand_right_fvars, demand_right_binders, demand_right_scope]
    decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem quoteAndChoice_needRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice
      PrimeCandidates.LanguageDef.needRewrite = [] := by
  unfold LanguageDef.validateRewrite
  simp only [List.append_eq_nil_iff]
  constructor
  · constructor
    · constructor <;> decide +kernel
    · decide +kernel
  · rw [quoteAndChoice_constructorLabels_eq]
    simp [LanguageDef.validateRulePatterns, PrimeCandidates.LanguageDef.needRewrite,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.freeFvarNames,
      LanguageDef.premiseLocallyScoped,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem quoteAndChoice_needReturnRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice
      PrimeCandidates.LanguageDef.needReturnRewrite = [] := by
  unfold LanguageDef.validateRewrite
  simp only [List.append_eq_nil_iff]
  constructor
  · constructor
    · constructor <;> decide +kernel
    · decide +kernel
  · rw [quoteAndChoice_constructorLabels_eq]
    simp [LanguageDef.validateRulePatterns, PrimeCandidates.LanguageDef.needReturnRewrite,
      MeTTaZero.evaluationAnswerPattern,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem quoteAndChoice_reflectedDemandRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice
      PrimeCandidates.LanguageDef.reflectedDemandRewrite = [] := by
  unfold LanguageDef.validateRewrite
  simp only [List.append_eq_nil_iff]
  constructor
  · constructor
    · constructor <;> decide +kernel
    · decide +kernel
  · rw [quoteAndChoice_constructorLabels_eq]
    simp only [LanguageDef.validateRulePatterns,
      show PrimeCandidates.LanguageDef.reflectedDemandRewrite.premises = [] from rfl,
      List.flatMap_nil, List.append_nil, List.all_nil,
      reflected_left_fvars, reflected_left_binders, reflected_left_scope,
      reflected_right_fvars, reflected_right_binders, reflected_right_scope]
    decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem quoteAndChoice_chooseLeftRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice chooseLeftRewrite = [] := by
  simp [LanguageDef.validateRewrite, LanguageDef.validateTypeExpr_eq_nil_iff, quoteAndChoice_typeNames_eq,
    quoteAndChoice_terms_eq, quoteAndChoiceTermLiterals, chooseLeftRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, TypeExpr.baseNames]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem quoteAndChoice_chooseRightRewrite_row :
    LanguageDef.validateRewrite quoteAndChoice chooseRightRewrite = [] := by
  simp [LanguageDef.validateRewrite, LanguageDef.validateTypeExpr_eq_nil_iff, quoteAndChoice_typeNames_eq,
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
This strengthens the list-level results of `QuotationChoiceGluing`: the glued
presentation is a legitimate object of the structural presentation category. -/
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
    change equation ∈ [PrimeCandidates.LanguageDef.quoteDropEquation] at membership
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
    subst membership
    exact quoteAndChoice_quoteDropEquation_row
  case hrewriteValid =>
    intro rewrite membership
    change rewrite ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
      PrimeCandidates.LanguageDef.evaluationDemandRewrite, PrimeCandidates.LanguageDef.needRewrite,
      PrimeCandidates.LanguageDef.needReturnRewrite,
      PrimeCandidates.LanguageDef.reflectedDemandRewrite,
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
already validated elsewhere: `PrimeCandidates.LanguageDef.currentZeroPresentation` and
`PrimeCandidates.LanguageDef.queryFirstCandidatePresentation`. -/
def zeroWithChoiceValidated : ValidatedLanguageDef :=
  ⟨zeroWithChoice, zeroWithChoice_validate⟩

/-- The validated glued presentation. -/
def quoteAndChoiceValidated : ValidatedLanguageDef :=
  ⟨quoteAndChoice, quoteAndChoice_validate⟩

/-- The concrete left inclusion: the quotation extension (the Prime spec
probe) into the glued quote-and-choice presentation. -/
def quoteAndChoiceLeftInclusion :
    StructuralMorphism PrimeCandidates.LanguageDef.queryFirstCandidatePresentation
      quoteAndChoiceValidated :=
  leftInclusionMorphism "metta-zero-quote-and-choice" MeTTaZero.language
    PrimeCandidates.LanguageDef.language_validate quoteAndChoice_validate

/-! ## Collision coverage for the concrete span -/

/-- The quote-and-choice span covers every right/base collision: the choice
extension repeats the
base declarations verbatim, and the quotation extension carries all of them. -/
theorem quoteAndChoice_rightBaseCollisionsCovered :
    RightBaseCollisionsCovered MeTTaZero.language PrimeCandidates.LanguageDef.language
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
        PrimeCandidates.LanguageDef.evaluationDemandRewrite, PrimeCandidates.LanguageDef.needRewrite,
        PrimeCandidates.LanguageDef.needReturnRewrite,
        PrimeCandidates.LanguageDef.reflectedDemandRewrite]
      simp
    · change _ ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
        PrimeCandidates.LanguageDef.evaluationDemandRewrite, PrimeCandidates.LanguageDef.needRewrite,
        PrimeCandidates.LanguageDef.needReturnRewrite,
        PrimeCandidates.LanguageDef.reflectedDemandRewrite]
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
  (`no_presentation_glues_clash` in `QuotationChoiceGluing`). -/

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
    ¬ RightBaseCollisionsCovered MeTTaZero.language PrimeCandidates.LanguageDef.language
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
        PrimeCandidates.LanguageDef.language zeroWithDivergentQuery).terms := by
  decide

/-- The clash side from `QuotationChoiceGluing`, packaged as a right extension. -/
def zeroWithClashingQuote : LanguageDef :=
  { MeTTaZero.language with
    name := "metta-zero-with-clashing-quote"
    terms := MeTTaZero.language.terms ++ [clashingQuote] }

/-- The glued clash presentation. -/
def clashingGlued : LanguageDef :=
  glue "metta-zero-quote-clash" MeTTaZero.language PrimeCandidates.LanguageDef.language
    zeroWithClashingQuote

/-- The clash span's right/base collisions are covered: `clashingQuote`
collides with the left extension, not with the base, and this predicate
constrains base collisions only. -/
theorem clashSpan_rightBaseCollisionsCovered :
    RightBaseCollisionsCovered MeTTaZero.language PrimeCandidates.LanguageDef.language
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
          PrimeCandidates.LanguageDef.evaluationDemandRewrite,
          PrimeCandidates.LanguageDef.needRewrite, PrimeCandidates.LanguageDef.needReturnRewrite,
          PrimeCandidates.LanguageDef.reflectedDemandRewrite]
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
`PrimeCandidates.LanguageDef.queryFirstZeroToCandidatePresentation`. -/
def zeroToZeroWithChoiceMorphism :
    StructuralMorphism PrimeCandidates.LanguageDef.currentZeroPresentation
      zeroWithChoiceValidated where
  symbols := LanguageDefSymbolMap.id
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
    StructuralMorphism.comp PrimeCandidates.LanguageDef.queryFirstZeroToCandidatePresentation
        quoteAndChoiceLeftInclusion =
      StructuralMorphism.comp zeroToZeroWithChoiceMorphism
        quoteAndChoiceRightInclusion :=
  StructuralMorphism.ext rfl

/-- The square in the extensional quotient: both composites act identically on
every authored declaration of the base. -/
theorem quoteAndChoice_gluingSquare_equivalent :
    Equivalent
      (StructuralMorphism.comp PrimeCandidates.LanguageDef.queryFirstZeroToCandidatePresentation
        quoteAndChoiceLeftInclusion)
      (StructuralMorphism.comp zeroToZeroWithChoiceMorphism
        quoteAndChoiceRightInclusion) :=
  quoteAndChoice_gluingSquare_commutes ▸ Equivalent.refl _

/-- The square as arrow equality in the structural presentation category. -/
theorem quoteAndChoice_gluingSquare_commutes_arrow :
    Arrow.ofMorphism
        (StructuralMorphism.comp PrimeCandidates.LanguageDef.queryFirstZeroToCandidatePresentation
          quoteAndChoiceLeftInclusion) =
      Arrow.ofMorphism
        (StructuralMorphism.comp zeroToZeroWithChoiceMorphism
          quoteAndChoiceRightInclusion) :=
  congrArg Arrow.ofMorphism quoteAndChoice_gluingSquare_commutes

/-! ## Axiom audit -/

#print axioms zeroWithChoice_validate
#print axioms quoteAndChoice_validate
#print axioms zeroWithChoiceValidated
#print axioms quoteAndChoiceValidated
#print axioms quoteAndChoiceLeftInclusion
#print axioms quoteAndChoiceRightInclusion
#print axioms quoteAndChoice_rightBaseCollisionsCovered
#print axioms zeroWithDivergentQuery_rightBaseCollisionsNotCovered
#print axioms divergentQueryConstructor_not_glued
#print axioms clashSpan_rightBaseCollisionsCovered
#print axioms clashingGlued_validate_ne_nil
#print axioms zeroToZeroWithChoiceMorphism
#print axioms quoteAndChoice_gluingSquare_commutes
#print axioms quoteAndChoice_gluingSquare_equivalent
#print axioms quoteAndChoice_gluingSquare_commutes_arrow

end Mettapedia.Languages.MeTTa.PrimeCandidates.QuotationChoiceGluingMorphisms
