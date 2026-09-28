import Mettapedia.OSLF.Framework.WMCalculusEvidenceConversion
import Mettapedia.OSLF.Framework.WMCalculusSortedBoundary
import Mettapedia.GSLT.LanguageDef.SortedEquationInstance
import Mettapedia.GSLT.LanguageDef.OpenSortedEquationInstance
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceReplacement
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceAdmission
import Mettapedia.GSLT.LanguageDef.CanonicalSection
import Mettapedia.OSLF.Framework.WMCalculusSortedEncoding

/-!
# A structural-equation presentation of the WM core

The core signature is shared with the authored directed presentation. The
three evidence monoid laws are authored equations. Extraction through revision
and revision's two observational laws remain directed rules, with the existing
premise-aware congruence rules. In particular no state unit is declared.

The generic raw equation matcher does not enforce its `typeContext` during
instantiation. The closed sorted-instance relation supplies that discipline,
but the existing WM atom encoder uses free variables, so a typed open-context
comparison needs a separate context-indexed instance theorem. This module
states only relations earned by the current matcher.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusStructuralPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusRewriteCompletenessBoundary
open Mettapedia.OSLF.Framework.WMCalculusSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusSortedEncoding
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting

/-- Evidence combination is commutative at the observational algebra layer. -/
def combineCommEquation : Equation :=
  ⟨"WM_CombineComm",
    [("e1", .base "BinaryEvidence"), ("e2", .base "BinaryEvidence")],
    [], pCombine (.fvar "e1") (.fvar "e2"),
    pCombine (.fvar "e2") (.fvar "e1"), none⟩

def combineAssocEquation : Equation :=
  ⟨"WM_CombineAssoc",
    [("e1", .base "BinaryEvidence"), ("e2", .base "BinaryEvidence"),
      ("e3", .base "BinaryEvidence")], [],
    pCombine (pCombine (.fvar "e1") (.fvar "e2")) (.fvar "e3"),
    pCombine (.fvar "e1") (pCombine (.fvar "e2") (.fvar "e3")), none⟩

def combineZeroEquation : Equation :=
  ⟨"WM_CombineZero", [("e", .base "BinaryEvidence")], [],
    pCombine (.fvar "e") pEvidenceZero, .fvar "e", none⟩

def structuralEquations : List Equation :=
  [combineCommEquation, combineAssocEquation, combineZeroEquation]

def computationalRules : List RewriteRule :=
  [ruleEvidenceAdd, ruleRevisionComm, ruleRevisionAssoc]

/-- A second presentation of the same typed signature. Structural equations
change representatives; only authored rewrite rules denote computations. -/
def wmStructuralLanguageDef : LanguageDef :=
  LanguageDef.ofCore "WMCalculusStructural" wmCoreLanguageDef.types
    coreTerms structuralEquations (computationalRules ++ coreCongruenceRules)

theorem structural_signature_eq_core :
    wmStructuralLanguageDef.types = wmCoreLanguageDef.types ∧
    wmStructuralLanguageDef.terms = wmCoreLanguageDef.terms := ⟨rfl, rfl⟩

theorem extraction_is_directed :
    ruleEvidenceAdd ∈ wmStructuralLanguageDef.rewrites := by
  change ruleEvidenceAdd ∈ computationalRules ++ coreCongruenceRules
  simp [computationalRules]

theorem combine_comm_is_equation :
    combineCommEquation ∈ wmStructuralLanguageDef.equations := by
  change combineCommEquation ∈ structuralEquations
  simp [structuralEquations]

theorem combine_assoc_is_equation :
    combineAssocEquation ∈ wmStructuralLanguageDef.equations := by
  change combineAssocEquation ∈ structuralEquations
  simp [structuralEquations]

theorem combine_zero_is_equation :
    combineZeroEquation ∈ wmStructuralLanguageDef.equations := by
  change combineZeroEquation ∈ structuralEquations
  simp [structuralEquations]

theorem combine_assoc_not_rewrite :
    ∀ rule ∈ wmStructuralLanguageDef.rewrites,
      rule.name ≠ combineAssocEquation.name := by
  intro rule member
  simp [wmStructuralLanguageDef, LanguageDef.ofCore, computationalRules,
    coreCongruenceRules, ruleEvidenceAdd, ruleRevisionComm, ruleRevisionAssoc,
    ruleReviseCongLeft, ruleReviseCongRight,
    ruleExtractCongLeft, ruleExtractCongRight,
    ruleCombineCongLeft, ruleCombineCongRight] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- The structural presentation has the same typed core, but its evidence
associativity law is not a directed step in the authored rule inventory. -/
theorem directed_vs_structural_rules :
    ruleCombineComm ∈ wmCoreLanguageDef.rewrites ∧
    ruleCombineComm ∉ wmStructuralLanguageDef.rewrites ∧
    combineAssocEquation ∈ wmStructuralLanguageDef.equations := by
  constructor
  · simp [wmCoreLanguageDef, coreRules]
  constructor
  · simp [wmStructuralLanguageDef, LanguageDef.ofCore, computationalRules,
      coreCongruenceRules, ruleCombineComm, ruleEvidenceAdd,
      ruleRevisionComm, ruleRevisionAssoc,
      ruleReviseCongLeft, ruleReviseCongRight, ruleExtractCongLeft,
      ruleExtractCongRight, ruleCombineCongLeft, ruleCombineCongRight]
  · exact combine_assoc_is_equation

private theorem same_term_validation (term : GrammarRule) :
    LanguageDef.validateTerm wmStructuralLanguageDef term =
      LanguageDef.validateTerm
        (wmExtVertexLanguageDefWithCong wmExtVertexMinimal) term := rfl

private theorem same_rewrite_validation (rule : RewriteRule) :
    LanguageDef.validateRewrite wmStructuralLanguageDef rule =
      LanguageDef.validateRewrite
        (wmExtVertexLanguageDefWithCong wmExtVertexMinimal) rule := rfl

private theorem combine_comm_equation_valid :
    LanguageDef.validateEquation wmStructuralLanguageDef combineCommEquation = [] := by
  simp only [LanguageDef.validateEquation, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, ← fvarNames_eq, ← binderNames_eq,
    ← binderNamesList_eq]
  decide +kernel

private theorem combine_assoc_equation_valid :
    LanguageDef.validateEquation wmStructuralLanguageDef combineAssocEquation = [] := by
  simp only [LanguageDef.validateEquation, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, ← fvarNames_eq, ← binderNames_eq,
    ← binderNamesList_eq]
  decide +kernel

private theorem combine_zero_equation_valid :
    LanguageDef.validateEquation wmStructuralLanguageDef combineZeroEquation = [] := by
  simp only [LanguageDef.validateEquation, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, ← fvarNames_eq, ← binderNames_eq,
    ← binderNamesList_eq]
  decide +kernel

private theorem structural_rule_in_contextual
    {rule : RewriteRule} (membership : rule ∈ wmStructuralLanguageDef.rewrites) :
    rule ∈ (wmExtVertexLanguageDefWithCong wmExtVertexMinimal).rewrites := by
  change rule ∈ computationalRules ++ coreCongruenceRules at membership
  change rule ∈ coreRules ++ coreCongruenceRules
  rcases List.mem_append.mp membership with computational | congruence
  · apply List.mem_append.mpr
    left
    simp only [computationalRules, List.mem_cons, List.not_mem_nil,
      or_false] at computational
    simp only [coreRules, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · exact List.mem_append.mpr (Or.inr congruence)

theorem structural_validation : wmStructuralLanguageDef.validate = [] := by
  have termRows : wmStructuralLanguageDef.terms.flatMap
      (LanguageDef.validateTerm wmStructuralLanguageDef) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro term member
    rw [same_term_validation]
    apply LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
      _ contextual_validation
    exact member
  have equationRows : wmStructuralLanguageDef.equations.flatMap
      (LanguageDef.validateEquation wmStructuralLanguageDef) = [] := by
    change [combineCommEquation, combineAssocEquation, combineZeroEquation].flatMap
      (LanguageDef.validateEquation wmStructuralLanguageDef) = []
    simp only [List.flatMap_cons, List.flatMap_nil,
      combine_comm_equation_valid, combine_assoc_equation_valid,
      combine_zero_equation_valid, List.nil_append]
  have rewriteRows : wmStructuralLanguageDef.rewrites.flatMap
      (LanguageDef.validateRewrite wmStructuralLanguageDef) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    rw [same_rewrite_validation]
    exact LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil
      _ contextual_validation rule (structural_rule_in_contextual member)
  unfold LanguageDef.validate
  simp only [termRows, equationRows, rewriteRows,
    List.append_nil]
  decide +kernel

private theorem comm_equation_sorted :
    Mettapedia.GSLT.LanguageDef.EquationWellSorted
      wmStructuralLanguageDef combineCommEquation := by
  refine ⟨.base "BinaryEvidence", ?_, ?_⟩
  · exact checkHasType_sound (by decide +kernel)
  · exact checkHasType_sound (by decide +kernel)

private theorem assoc_equation_sorted :
    Mettapedia.GSLT.LanguageDef.EquationWellSorted
      wmStructuralLanguageDef combineAssocEquation := by
  refine ⟨.base "BinaryEvidence", ?_, ?_⟩
  · exact checkHasType_sound (by decide +kernel)
  · exact checkHasType_sound (by decide +kernel)

private theorem zero_equation_sorted :
    Mettapedia.GSLT.LanguageDef.EquationWellSorted
      wmStructuralLanguageDef combineZeroEquation := by
  refine ⟨.base "BinaryEvidence", ?_, ?_⟩
  · exact checkHasType_sound (by decide +kernel)
  · exact checkHasType_sound (by decide +kernel)

theorem structural_equations_sorted
    {equation : Equation} (member : equation ∈ wmStructuralLanguageDef.equations) :
    Mettapedia.GSLT.LanguageDef.EquationWellSorted
      wmStructuralLanguageDef equation := by
  change equation ∈ structuralEquations at member
  simp only [structuralEquations, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl
  · exact comm_equation_sorted
  · exact assoc_equation_sorted
  · exact zero_equation_sorted

theorem structural_rules_checked :
    wmStructuralLanguageDef.rewrites.all
      (checkRewriteWellSorted wmStructuralLanguageDef) = true := by
  decide +kernel

theorem structural_rules_sorted
    {rule : RewriteRule} (member : rule ∈ wmStructuralLanguageDef.rewrites) :
    Mettapedia.GSLT.LanguageDef.RewriteWellSorted
      wmStructuralLanguageDef rule :=
  checkRewriteWellSorted_sound
    ((List.all_eq_true.mp structural_rules_checked) rule member)

/-- The authored zero equation is instantiated by the canonical equation
matcher. The raw matcher accepts an arbitrary pattern at its schema variable. -/
theorem combine_zero_equivalent (term : Pattern) :
    (langGSLT wmStructuralLanguageDef).Equiv
      (pCombine term pEvidenceZero) term := by
  apply Relation.EqvGen.rel
  apply EquationContextStep.inContext .hole
  apply Or.inl
  refine ⟨0, EquationInstanceAt.forward (equation := combineZeroEquation)
    (initialBindings := [("e", term)]) (finalBindings := [("e", term)])
    combine_zero_is_equation ?_
    (.nil _) ?_⟩
  · simp [combineZeroEquation, pCombine, pEvidenceZero,
      matchPattern, matchArgs, mergeBindings]
  · simp [combineZeroEquation, pCombine, pEvidenceZero, applyBindings]

/-- The canonical raw matcher accepts the zero law with an arbitrary pattern
at its schema variable. This is a genuine root contextual generator. -/
theorem combine_zero_contextStep (term : Pattern) :
    EquationContextStep Mettapedia.GSLT.LanguageDef.defaultBasePremises
      wmStructuralLanguageDef
      (pCombine term pEvidenceZero) term := by
  apply EquationContextStep.inContext .hole
  apply Or.inl
  refine ⟨0, EquationInstanceAt.forward (equation := combineZeroEquation)
    (initialBindings := [("e", term)]) (finalBindings := [("e", term)])
    combine_zero_is_equation ?_
    (.nil _) ?_⟩
  · simp [combineZeroEquation, pCombine, pEvidenceZero,
      matchPattern, matchArgs, mergeBindings]
  · simp [combineZeroEquation, pCombine, pEvidenceZero, applyBindings]

theorem combine_assoc_equivalent (first second third : Pattern) :
    (langGSLT wmStructuralLanguageDef).Equiv
      (pCombine (pCombine first second) third)
      (pCombine first (pCombine second third)) := by
  apply Relation.EqvGen.rel
  apply EquationContextStep.inContext .hole
  apply Or.inl
  let bindings : Bindings :=
    [("e3", third), ("e2", second), ("e1", first)]
  refine ⟨0, EquationInstanceAt.forward (equation := combineAssocEquation)
    (initialBindings := bindings) (finalBindings := bindings)
    combine_assoc_is_equation ?_ (.nil _) ?_⟩
  · simp [bindings, combineAssocEquation, pCombine, matchPattern,
      matchArgs, mergeBindings]
  · simp [bindings, combineAssocEquation, pCombine, applyBindings]

theorem combine_comm_equivalent (first second : Pattern) :
    (langGSLT wmStructuralLanguageDef).Equiv
      (pCombine first second) (pCombine second first) := by
  apply Relation.EqvGen.rel
  apply EquationContextStep.inContext .hole
  apply Or.inl
  let bindings : Bindings := [("e2", second), ("e1", first)]
  refine ⟨0, EquationInstanceAt.forward (equation := combineCommEquation)
    (initialBindings := bindings) (finalBindings := bindings)
    combine_comm_is_equation ?_ (.nil _) ?_⟩
  · simp [bindings, combineCommEquation, pCombine, matchPattern,
      matchArgs, mergeBindings]
  · simp [bindings, combineCommEquation, pCombine, applyBindings]

/-- Root-level structural laws of the typed evidence syntax. This excludes
extraction, which is computational, and excludes any state identity. -/
inductive EvidenceStructuralLaw : WMTerm .evidence → WMTerm .evidence → Prop where
  | comm (first second) :
      EvidenceStructuralLaw (.combine first second) (.combine second first)
  | assoc (first second third) :
      EvidenceStructuralLaw (.combine (.combine first second) third)
        (.combine first (.combine second third))
  | zero (term) : EvidenceStructuralLaw (.combine term .zero) term

/-- Each typed structural generator is realized by an actual authored
equation instance on its encoded image. -/
theorem encoded_structural_law_equivalent
    {first second : WMTerm .evidence}
    (law : EvidenceStructuralLaw first second) :
    (langGSLT wmStructuralLanguageDef).Equiv
      (encodeWM first) (encodeWM second) := by
  cases law with
  | comm _ _ => exact combine_comm_equivalent _ _
  | assoc _ _ _ => exact combine_assoc_equivalent _ _ _
  | zero _ => exact combine_zero_equivalent _

/-- The same typed generators belong to the semantically complete
conversion; the two presentations share the intended evidence laws. -/
theorem structural_law_conversion
    {first second : WMTerm .evidence}
    (law : EvidenceStructuralLaw first second) :
    WMCalculusEvidenceConversion.EvidenceConversion first second := by
  cases law with
  | comm _ _ => exact .comm _ _
  | assoc _ _ _ => exact .assoc _ _ _
  | zero _ => exact .zero _

/-- The actual authored structural generators have the same interpretation
in every lawful WM reading as the previously proved free semantic model. -/
theorem structural_law_allReadings
    {first second : WMTerm .evidence}
    (law : EvidenceStructuralLaw first second) :
    ∀ (State Query V : Type)
      (reading : Mettapedia.OSLF.Framework.WMCalculusSemantics.WMReading State Query V),
      reading.CoreLaws → reading.denote first = reading.denote second :=
  (WMCalculusEvidenceConversion.conversion_iff_allReadings first second).1
    (structural_law_conversion law)

/-- Unlike the raw instance above, this schema substitution checks the
encoded evidence term under the ambient free-atom typing context. -/
theorem typed_zero_instance (free : FreeTypeContext)
    (term : WMTerm .evidence) (typed : AtomsTyped free term) :
    OpenSortedEquationInstance free (engineBasePremises RelationEnv.empty)
      wmStructuralLanguageDef
      (pCombine (encodeWM term) pEvidenceZero) (encodeWM term) := by
  refine ⟨0, OpenSortedEquationInstanceAt.forward
    (equation := combineZeroEquation)
    (initialBindings := [("e", encodeWM term)])
    (finalBindings := [("e", encodeWM term)])
    combine_zero_is_equation ?_ (.nil _) ?_ ?_⟩
  · simp [combineZeroEquation, pCombine, pEvidenceZero,
      matchPattern, matchArgs, mergeBindings]
  · intro key ty member
    simp only [combineZeroEquation, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    constructor
    · simpa [applyBindings] using (encodeWM_isObject term)
    · simpa [applyBindings, sortType] using
        ((encodeWM_hasType_iff wmStructuralLanguageDef rfl free term).2 typed)
  · simp [combineZeroEquation, applyBindings]

theorem typed_comm_instance (free : FreeTypeContext)
    (first second : WMTerm .evidence)
    (firstTyped : AtomsTyped free first)
    (secondTyped : AtomsTyped free second) :
    OpenSortedEquationInstance free (engineBasePremises RelationEnv.empty)
      wmStructuralLanguageDef
      (pCombine (encodeWM first) (encodeWM second))
      (pCombine (encodeWM second) (encodeWM first)) := by
  let bindings : Bindings :=
    [("e2", encodeWM second), ("e1", encodeWM first)]
  refine ⟨0, OpenSortedEquationInstanceAt.forward
    (equation := combineCommEquation)
    (initialBindings := bindings) (finalBindings := bindings)
    combine_comm_is_equation ?_ (.nil _) ?_ ?_⟩
  · simp [bindings, combineCommEquation, pCombine,
      matchPattern, matchArgs, mergeBindings]
  · intro key ty member
    simp only [combineCommEquation, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · constructor
      · simpa [bindings, applyBindings] using (encodeWM_isObject first)
      · simpa [bindings, applyBindings, sortType] using
          ((encodeWM_hasType_iff wmStructuralLanguageDef rfl free first).2 firstTyped)
    · constructor
      · simpa [bindings, applyBindings] using (encodeWM_isObject second)
      · simpa [bindings, applyBindings, sortType] using
          ((encodeWM_hasType_iff wmStructuralLanguageDef rfl free second).2 secondTyped)
  · simp [bindings, combineCommEquation, pCombine, applyBindings]

theorem typed_assoc_instance (free : FreeTypeContext)
    (first second third : WMTerm .evidence)
    (firstTyped : AtomsTyped free first)
    (secondTyped : AtomsTyped free second)
    (thirdTyped : AtomsTyped free third) :
    OpenSortedEquationInstance free (engineBasePremises RelationEnv.empty)
      wmStructuralLanguageDef
      (pCombine (pCombine (encodeWM first) (encodeWM second)) (encodeWM third))
      (pCombine (encodeWM first) (pCombine (encodeWM second) (encodeWM third))) := by
  let bindings : Bindings :=
    [("e3", encodeWM third), ("e2", encodeWM second),
      ("e1", encodeWM first)]
  refine ⟨0, OpenSortedEquationInstanceAt.forward
    (equation := combineAssocEquation)
    (initialBindings := bindings) (finalBindings := bindings)
    combine_assoc_is_equation ?_ (.nil _) ?_ ?_⟩
  · simp [bindings, combineAssocEquation, pCombine,
      matchPattern, matchArgs, mergeBindings]
  · intro key ty member
    simp only [combineAssocEquation, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · constructor
      · simpa [bindings, applyBindings] using (encodeWM_isObject first)
      · simpa [bindings, applyBindings, sortType] using
          ((encodeWM_hasType_iff wmStructuralLanguageDef rfl free first).2 firstTyped)
    · constructor
      · simpa [bindings, applyBindings] using (encodeWM_isObject second)
      · simpa [bindings, applyBindings, sortType] using
          ((encodeWM_hasType_iff wmStructuralLanguageDef rfl free second).2 secondTyped)
    · constructor
      · simpa [bindings, applyBindings] using (encodeWM_isObject third)
      · simpa [bindings, applyBindings, sortType] using
          ((encodeWM_hasType_iff wmStructuralLanguageDef rfl free third).2 thirdTyped)
  · simp [bindings, combineAssocEquation, pCombine, applyBindings]

/-- A query of a named world supplies an open, well-sorted evidence value.
The closed sorted-instance discipline cannot admit the same substitution,
because its two atom names have no types in the empty context. -/
theorem named_evidence_open_not_closed :
    let term : WMTerm .evidence :=
      .extract (.state "world") (.query "question")
    let bindings : Bindings := [("e", encodeWM term)]
    SortedBindingsIn wmStructuralLanguageDef specimenFree
        combineZeroEquation.typeContext bindings ∧
      ¬ SortedBindings wmStructuralLanguageDef
        combineZeroEquation.typeContext bindings := by
  dsimp
  constructor
  · intro key ty member
    simp only [combineZeroEquation, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    constructor
    · simpa [applyBindings] using
        (encodeWM_isObject (.extract (.state "world") (.query "question")))
    · simpa [applyBindings, sortType] using
        ((encodeWM_hasType_iff wmStructuralLanguageDef rfl specimenFree
          (.extract (.state "world") (.query "question"))).2
          (by simp [AtomsTyped, specimenFree, sortType]))
  · intro closed
    have typed := (closed "e" (.base "BinaryEvidence")
      (by simp [combineZeroEquation])).2
    have typed' : HasType wmStructuralLanguageDef FreeTypeContext.empty []
        (encodeWM (.extract (.state "world") (.query "question")))
        (sortType .evidence) := by
      simpa [applyBindings, sortType] using typed
    have atoms := (encodeWM_hasType_iff wmStructuralLanguageDef rfl
      FreeTypeContext.empty
      (.extract (.state "world") (.query "question"))).1 typed'
    simp [AtomsTyped, FreeTypeContext.empty, sortType] at atoms

/-- Every typed structural generator has a schema-sort-respecting authored
instance in the same free-variable context as its encoded source. -/
theorem typed_structural_law_open_instance (free : FreeTypeContext)
    {first second : WMTerm .evidence}
    (law : EvidenceStructuralLaw first second)
    (typed : AtomsTyped free first) :
    OpenSortedEquationInstance free (engineBasePremises RelationEnv.empty)
      wmStructuralLanguageDef (encodeWM first) (encodeWM second) := by
  cases law with
  | comm left right =>
      exact typed_comm_instance free left right typed.1 typed.2
  | assoc left middle right =>
      exact typed_assoc_instance free left middle right
        typed.1.1 typed.1.2 typed.2
  | zero _ =>
      exact typed_zero_instance free _ typed.1

/-- The existing authored GSLT receives those type-checked generators
through the generic inclusion of open sorted instances. -/
theorem typed_structural_law_authored_equivalent (free : FreeTypeContext)
    {first second : WMTerm .evidence}
    (law : EvidenceStructuralLaw first second)
    (typed : AtomsTyped free first) :
    (langGSLT wmStructuralLanguageDef).Equiv
      (encodeWM first) (encodeWM second) :=
  equationEquiv_of_openSortedEquationInstance
    (typed_structural_law_open_instance free law typed)

private theorem structural_law_atomsTyped (free : FreeTypeContext)
    {first second : WMTerm .evidence}
    (law : EvidenceStructuralLaw first second)
    (typed : AtomsTyped free first) : AtomsTyped free second := by
  cases law with
  | comm _ _ => exact ⟨typed.2, typed.1⟩
  | assoc _ _ _ => exact ⟨typed.1.1, typed.1.2, typed.2⟩
  | zero _ => exact typed.1

private theorem encoded_evidence_representationCompatible
    (first second : WMTerm .evidence) :
    RepresentationCompatible (encodeWM first) (encodeWM second) := by
  cases first <;> cases second <;>
    exact representationCompatible_apply _ _ _ _

private theorem encoded_evidence_admissionProfileEquivalent
    (first second : WMTerm .evidence) :
    AdmissionProfileEquivalent (encodeWM first) (encodeWM second) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [encodeWM_hasCanonicalBinderMetadata,
      encodeWM_hasCanonicalBinderMetadata]
  · rw [encodeWM_isObject, encodeWM_isObject]
  · intro depth
    rw [encodeWM_isWellScopedAt, encodeWM_isWellScopedAt]

/-- Replacing encoded evidence inside an already typed occurrence preserves
the ambient sort when both values typecheck under the same free-atom context.
The occurrence may cross binders; its exact focus fibre comes from the
existing typed zipper. -/
theorem encoded_evidence_replacement_typed_in_context (free : FreeTypeContext)
    (context : OneHoleContext) (bound : List TypeExpr)
    (ambientType : TypeExpr)
    {first second : WMTerm .evidence}
    (firstTyped : AtomsTyped free first)
    (secondTyped : AtomsTyped free second)
    (sourceTyped : HasType wmStructuralLanguageDef free bound
      (context.fill (encodeWM first)) ambientType) :
    HasType wmStructuralLanguageDef free bound
      (context.fill (encodeWM second)) ambientType := by
  obtain ⟨focusBound, focusType, selected⟩ :=
    hasType_typedAt context sourceTyped
  have firstAtFocus : HasType wmStructuralLanguageDef free focusBound
      (encodeWM first) focusType := selected.focus_typed
  have firstAtEvidence : HasType wmStructuralLanguageDef free focusBound
      (encodeWM first) (sortType .evidence) :=
    (encodeWM_hasType_iff_bound wmStructuralLanguageDef rfl free
      focusBound first).2 firstTyped
  have focusSort : focusType = sortType .evidence := by
    cases first <;>
      exact HasType.apply_type_unique_of_validate_eq_nil
        structural_validation firstAtFocus firstAtEvidence
  have secondAtFocus : HasType wmStructuralLanguageDef free focusBound
      (encodeWM second) focusType := by
    rw [focusSort]
    exact (encodeWM_hasType_iff_bound wmStructuralLanguageDef rfl free
      focusBound second).2 secondTyped
  exact selected.replace
    (encoded_evidence_representationCompatible first second) secondAtFocus

/-- One authored structural equation preserves typing at any selected
occurrence of an encoded WM evidence term. -/
theorem structural_law_typed_in_context (free : FreeTypeContext)
    (context : OneHoleContext) (bound : List TypeExpr)
    (ambientType : TypeExpr)
    {first second : WMTerm .evidence}
    (law : EvidenceStructuralLaw first second)
    (typed : AtomsTyped free first)
    (sourceTyped : HasType wmStructuralLanguageDef free bound
      (context.fill (encodeWM first)) ambientType) :
    HasType wmStructuralLanguageDef free bound
      (context.fill (encodeWM second)) ambientType :=
  encoded_evidence_replacement_typed_in_context free context bound ambientType
    typed (structural_law_atomsTyped free law typed) sourceTyped

/-- Encoded evidence replacement preserves all four conditions of the native
open-pattern carrier: typing, canonical binder metadata, object form, and
scope. The surrounding context may cross a binder. -/
theorem encoded_evidence_replacement_openPatternWellSorted_in_context
    (free : FreeTypeContext) (context : OneHoleContext)
    (bound : List TypeExpr) (ambientType : TypeExpr)
    {first second : WMTerm .evidence}
    (firstTyped : AtomsTyped free first)
    (secondTyped : AtomsTyped free second)
    (sourceAdmitted : OpenPatternWellSorted wmStructuralLanguageDef free bound
      ambientType (context.fill (encodeWM first))) :
    OpenPatternWellSorted wmStructuralLanguageDef free bound ambientType
      (context.fill (encodeWM second)) := by
  obtain ⟨focusBound, focusType, selected⟩ :=
    hasType_typedAt context sourceAdmitted.1
  have firstAtFocus : HasType wmStructuralLanguageDef free focusBound
      (encodeWM first) focusType := selected.focus_typed
  have firstAtEvidence : HasType wmStructuralLanguageDef free focusBound
      (encodeWM first) (sortType .evidence) :=
    (encodeWM_hasType_iff_bound wmStructuralLanguageDef rfl free
      focusBound first).2 firstTyped
  have focusSort : focusType = sortType .evidence := by
    cases first <;>
      exact HasType.apply_type_unique_of_validate_eq_nil
        structural_validation firstAtFocus firstAtEvidence
  have secondAtFocus : HasType wmStructuralLanguageDef free focusBound
      (encodeWM second) focusType := by
    rw [focusSort]
    exact (encodeWM_hasType_iff_bound wmStructuralLanguageDef rfl free
      focusBound second).2 secondTyped
  exact selected.replace_openPatternWellSorted sourceAdmitted
    (encoded_evidence_representationCompatible first second)
    (encoded_evidence_admissionProfileEquivalent first second)
    secondAtFocus

/-- Every typed authored evidence-law generator preserves the complete native
open-pattern carrier through an arbitrary admitted syntactic context. -/
theorem structural_law_openPatternWellSorted_in_context
    (free : FreeTypeContext) (context : OneHoleContext)
    (bound : List TypeExpr) (ambientType : TypeExpr)
    {first second : WMTerm .evidence}
    (law : EvidenceStructuralLaw first second)
    (typed : AtomsTyped free first)
    (sourceAdmitted : OpenPatternWellSorted wmStructuralLanguageDef free bound
      ambientType (context.fill (encodeWM first))) :
    OpenPatternWellSorted wmStructuralLanguageDef free bound ambientType
      (context.fill (encodeWM second)) :=
  encoded_evidence_replacement_openPatternWellSorted_in_context
    free context bound ambientType typed
    (structural_law_atomsTyped free law typed) sourceAdmitted

/-- One certified authored law acts within the exact native open-pattern
fiber and supplies its actual equation equivalence at the same time. -/
theorem structural_law_authored_equiv_and_native_open_in_context
    (free : FreeTypeContext) (context : OneHoleContext)
    (bound : List TypeExpr) (ambientType : TypeExpr)
    {first second : WMTerm .evidence}
    (law : EvidenceStructuralLaw first second)
    (typed : AtomsTyped free first)
    (sourceAdmitted : OpenPatternWellSorted wmStructuralLanguageDef free bound
      ambientType (context.fill (encodeWM first))) :
    (langGSLT wmStructuralLanguageDef).Equiv
      (context.fill (encodeWM first)) (context.fill (encodeWM second)) ∧
    OpenPatternWellSorted wmStructuralLanguageDef free bound ambientType
      (context.fill (encodeWM second)) := by
  constructor
  · exact equationEquiv_fill context
      (typed_structural_law_authored_equivalent free law typed)
  · exact structural_law_openPatternWellSorted_in_context
      free context bound ambientType law typed sourceAdmitted

/-- The typed WM generator is an edge of the existing native open-pattern
equation setoid. The edge uses the canonical authored equation instance;
the native carrier supplies typing, binder, object, and scope certificates. -/
theorem structural_law_native_open_equation_setoid
    (free : FreeTypeContext) (context : OneHoleContext)
    (bound : List TypeExpr) (ambientType : TypeExpr)
    {first second : WMTerm .evidence}
    (law : EvidenceStructuralLaw first second)
    (typed : AtomsTyped free first)
    (sourceAdmitted : OpenPatternWellSorted wmStructuralLanguageDef free bound
      ambientType (context.fill (encodeWM first))) :
    (Mettapedia.GSLT.LanguageDef.openPatternEquationSetoid
      wmStructuralLanguageDef free bound ambientType).r
      ⟨context.fill (encodeWM first), sourceAdmitted⟩
      ⟨context.fill (encodeWM second),
        structural_law_openPatternWellSorted_in_context
          free context bound ambientType law typed sourceAdmitted⟩ := by
  apply Relation.EqvGen.rel
  exact EquationContextStep.inContext context
    (Or.inl (equationInstance_of_openSortedEquationInstance
      (typed_structural_law_open_instance free law typed)))

/-- A named observation inside both a Combine argument and a canonical
lambda inhabits the native open-pattern statement, not only `HasType`. -/
theorem specimen_structural_under_lambda_native_open :
    let observation : WMTerm .evidence :=
      .extract (.state "world") (.query "question")
    let context : OneHoleContext :=
      .lambda none (.apply "Combine" [pEvidenceZero] .hole [])
    (langGSLT wmStructuralLanguageDef).Equiv
      (context.fill (encodeWM (.combine observation .zero)))
      (context.fill (encodeWM observation)) ∧
    OpenPatternWellSorted wmStructuralLanguageDef specimenFree []
      (.arrow (.base "State") (.base "BinaryEvidence"))
      (context.fill (encodeWM observation)) := by
  dsimp
  apply structural_law_authored_equiv_and_native_open_in_context
    specimenFree
    (.lambda none (.apply "Combine" [pEvidenceZero] .hole [])) []
    (.arrow (.base "State") (.base "BinaryEvidence"))
    (EvidenceStructuralLaw.zero
      (.extract (.state "world") (.query "question")))
  · simp [AtomsTyped, specimenFree, sortType]
  · exact checkOpenPatternWellSorted_sound (by decide +kernel)

/-- The typed equation instance and its contextual typing preservation are
both sourced from the authored presentation, not a parallel WM equation. -/
theorem structural_law_authored_equiv_and_typed_in_context
    (free : FreeTypeContext) (context : OneHoleContext)
    (bound : List TypeExpr) (ambientType : TypeExpr)
    {first second : WMTerm .evidence}
    (law : EvidenceStructuralLaw first second)
    (typed : AtomsTyped free first)
    (sourceTyped : HasType wmStructuralLanguageDef free bound
      (context.fill (encodeWM first)) ambientType) :
    (langGSLT wmStructuralLanguageDef).Equiv
      (context.fill (encodeWM first)) (context.fill (encodeWM second)) ∧
    HasType wmStructuralLanguageDef free bound
      (context.fill (encodeWM second)) ambientType := by
  constructor
  · exact equationEquiv_fill context
      (typed_structural_law_authored_equivalent free law typed)
  · exact structural_law_typed_in_context free context bound ambientType
      law typed sourceTyped

/-- A named observation under both a `Combine` argument and a binder is an
inhabited instance of contextual structural replacement. -/
theorem specimen_structural_under_lambda :
    let observation : WMTerm .evidence :=
      .extract (.state "world") (.query "question")
    let context : OneHoleContext :=
      .lambda none (.apply "Combine" [pEvidenceZero] .hole [])
    (langGSLT wmStructuralLanguageDef).Equiv
      (context.fill (encodeWM (.combine observation .zero)))
      (context.fill (encodeWM observation)) ∧
    HasType wmStructuralLanguageDef specimenFree []
      (context.fill (encodeWM observation))
      (.arrow (.base "State") (.base "BinaryEvidence")) := by
  dsimp
  apply structural_law_authored_equiv_and_typed_in_context
    specimenFree
    (.lambda none (.apply "Combine" [pEvidenceZero] .hole [])) []
    (.arrow (.base "State") (.base "BinaryEvidence"))
    (EvidenceStructuralLaw.zero
      (.extract (.state "world") (.query "question")))
  · simp [AtomsTyped, specimenFree, sortType]
  · exact checkHasType_sound (by decide +kernel)

/-- The missing associativity of the directed WM presentation is one
authored equation in the structural presentation, with exactly the same
encoded evidence terms on both sides. -/
theorem authored_assoc_closes_directed_gap :
    (langGSLT wmStructuralLanguageDef).Equiv
      (encodeWM WMCalculusRewriteCompletenessBoundary.leftAssoc)
      (encodeWM WMCalculusRewriteCompletenessBoundary.rightAssoc) ∧
    ¬ WMContextStepStar WMCalculusRewriteCompletenessBoundary.leftAssoc
        WMCalculusRewriteCompletenessBoundary.rightAssoc := by
  constructor
  · exact combine_assoc_equivalent _ _ _
  · exact semantic_assoc_not_contextually_reachable.2.1

/-- A raw equation instance may substitute a State into the equation's
BinaryEvidence variable. Source validation checks the schema, not this
instance. Such a pattern is outside the sorted term language. -/
theorem ill_sorted_zero_instance :
    (langGSLT wmStructuralLanguageDef).Equiv
      (pCombine (pRevise (.fvar "w1") (.fvar "w2")) pEvidenceZero)
      (pRevise (.fvar "w1") (.fvar "w2")) :=
  combine_zero_equivalent _

theorem closed_zero_well_sorted :
    HasType wmStructuralLanguageDef FreeTypeContext.empty []
      pEvidenceZero (.base "BinaryEvidence") := by
  apply (checkHasType_eq_true_iff (by decide +kernel)).1
  decide +kernel

theorem state_pattern_not_evidence (free : FreeTypeContext) :
    ¬ HasType wmStructuralLanguageDef free []
      (pRevise (.fvar "w1") (.fvar "w2"))
      (.base "BinaryEvidence") := by
  intro typed
  have accepted := (checkHasType_eq_true_iff (by decide +kernel)).2 typed
  have rejected :
      checkHasType wmStructuralLanguageDef free []
        (pRevise (.fvar "w1") (.fvar "w2"))
        (.base "BinaryEvidence") = false := by
    simp [checkHasType, wmStructuralLanguageDef, LanguageDef.ofCore, coreTerms,
      reviseDecl, extractDecl, combineDecl, evidenceZeroDecl,
      pRevise]
  rw [rejected] at accepted
  cases accepted

/-- The raw authored equation relation does not preserve every typed open
fiber. Substituting a State atom for the zero equation's BinaryEvidence
variable makes its target a well-sorted State and its source ill-sorted.
Typed open equation instances, not global raw-fiber stability, are needed. -/
theorem structural_not_openEquationFiberStable :
    ¬ Mettapedia.GSLT.LanguageDef.OpenEquationFiberStable
        wmStructuralLanguageDef := by
  intro stable
  let free : FreeTypeContext := fun _ => some (.base "State")
  have targetTyped : OpenPatternWellSorted wmStructuralLanguageDef free []
      (.base "State") (.fvar "w") := by
    apply checkOpenPatternWellSorted_sound
    decide +kernel
  have sourceTyped : OpenPatternWellSorted wmStructuralLanguageDef free []
      (.base "State") (pCombine (.fvar "w") pEvidenceZero) :=
    (stable (combine_zero_contextStep (.fvar "w"))).mpr targetTyped
  have accepted :=
    (checkOpenPatternWellSorted_eq_true_iff wmStructuralLanguageDef free []
      (.base "State") (pCombine (.fvar "w") pEvidenceZero)).2 sourceTyped
  have rejected :
      checkOpenPatternWellSorted wmStructuralLanguageDef free []
        (.base "State") (pCombine (.fvar "w") pEvidenceZero) = false := by
    decide +kernel
  rw [rejected] at accepted
  cases accepted

/-- Evidence extraction remains a directed authored step. -/
theorem evidence_add_computes (first second query : Pattern) :
    langSemanticReduces wmStructuralLanguageDef
      (pExtract (pRevise first second) query)
      (pCombine (pExtract first query) (pExtract second query)) := by
  apply langReduces_to_semantic
  unfold langReduces langReducesUsing
  let bindings : Bindings := [("q", query), ("W2", second), ("W1", first)]
  refine step_of_rule
    (relEnv := RelationEnv.empty) (lang := wmStructuralLanguageDef)
    (rule := ruleEvidenceAdd) (initialBindings := bindings)
    (finalBindings := bindings)
    extraction_is_directed ?_ (by exact .nil) ?_ ?_
  · simp [bindings, ruleEvidenceAdd, pExtract, pRevise,
      matchPattern, matchArgs, mergeBindings]
  · simp [bindings, ruleEvidenceAdd, applyPremisesWithEnv]
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_applyBindings
      _ _ _ (by decide +kernel)]
    simp [bindings, ruleEvidenceAdd, pExtract, pCombine, applyBindings]

theorem encoded_extraction_computes
    (first second : WMTerm .state) (query : WMTerm .query) :
    langSemanticReduces wmStructuralLanguageDef
      (encodeWM (.extract (.revise first second) query))
      (encodeWM (.combine (.extract first query) (.extract second query))) :=
  evidence_add_computes _ _ _

/-- The authored extraction computation acts between two terms of the same
native open evidence fiber. Its computational direction is retained; the
structural Combine laws above remain equations. -/
theorem encoded_extraction_computes_native_open
    (free : FreeTypeContext) (bound : List TypeExpr)
    (first second : WMTerm .state) (query : WMTerm .query)
    (typed : AtomsTyped free (.extract (.revise first second) query)) :
    langSemanticReduces wmStructuralLanguageDef
      (encodeWM (.extract (.revise first second) query))
      (encodeWM (.combine (.extract first query) (.extract second query))) ∧
    OpenPatternWellSorted wmStructuralLanguageDef free bound
      (sortType .evidence) (encodeWM (.extract (.revise first second) query)) ∧
    OpenPatternWellSorted wmStructuralLanguageDef free bound
      (sortType .evidence)
        (encodeWM (.combine (.extract first query) (.extract second query))) := by
  refine ⟨encoded_extraction_computes first second query,
    (encodeWM_openPatternWellSorted_iff_bound wmStructuralLanguageDef rfl
      free bound _).2 typed, ?_⟩
  have targetTyped : AtomsTyped free
      (.combine (.extract first query) (.extract second query)) :=
    ⟨⟨typed.1.1, typed.2⟩, ⟨typed.1.2, typed.2⟩⟩
  exact (encodeWM_openPatternWellSorted_iff_bound wmStructuralLanguageDef rfl
    free bound _).2 targetTyped

/-! ## What the authored presentation can express -/

/-- One authored equation or one directed computation, placed in a
syntax-derived one-hole context. This is a conversion step, not an execution
step: the equivalence closure below deliberately forgets orientation. -/
def AuthoredContextStep (source target : Pattern) : Prop :=
  ∃ (context : OneHoleContext) (redex contractum : Pattern),
    source = context.fill redex ∧ target = context.fill contractum ∧
      ((langGSLT wmStructuralLanguageDef).Equiv redex contractum ∨
        langSemanticReduces wmStructuralLanguageDef redex contractum)

def AuthoredConversion : Pattern → Pattern → Prop :=
  Relation.EqvGen AuthoredContextStep

/-- An authored contextual generator remains the same generator after
insertion into a larger syntax-derived context. -/
theorem authoredContextStep_fill (outer : OneHoleContext)
    {source target : Pattern} (step : AuthoredContextStep source target) :
    AuthoredContextStep (outer.fill source) (outer.fill target) := by
  obtain ⟨inner, redex, contractum, sourceEq, targetEq, root⟩ := step
  refine ⟨outer.comp inner, redex, contractum, ?_, ?_, root⟩
  · simp [sourceEq, OneHoleContext.fill_comp]
  · simp [targetEq, OneHoleContext.fill_comp]

theorem authoredConversion_of_equation {source target : Pattern}
    (equivalent : (langGSLT wmStructuralLanguageDef).Equiv source target) :
    AuthoredConversion source target :=
  Relation.EqvGen.rel _ _ ⟨.hole, source, target, rfl, rfl, Or.inl equivalent⟩

theorem authoredConversion_of_computation {source target : Pattern}
    (step : langSemanticReduces wmStructuralLanguageDef source target) :
    AuthoredConversion source target :=
  Relation.EqvGen.rel _ _ ⟨.hole, source, target, rfl, rfl, Or.inr step⟩

theorem authoredConversion_fill (context : OneHoleContext)
    {source target : Pattern} (conversion : AuthoredConversion source target) :
    AuthoredConversion (context.fill source) (context.fill target) := by
  induction conversion with
  | rel _ _ generator =>
      exact Relation.EqvGen.rel _ _
        (authoredContextStep_fill context generator)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ first second =>
      exact Relation.EqvGen.trans _ _ _ first second

theorem authoredConversion_combine {first first' second second' : Pattern}
    (left : AuthoredConversion first first')
    (right : AuthoredConversion second second') :
    AuthoredConversion (pCombine first second) (pCombine first' second') := by
  have leftStep := authoredConversion_fill
    (.apply "Combine" [] .hole [second]) left
  have rightStep := authoredConversion_fill
    (.apply "Combine" [first'] .hole []) right
  exact Relation.EqvGen.trans _ _ _
    (by simpa [AuthoredConversion, OneHoleContext.fill, pCombine] using leftStep)
    (by simpa [AuthoredConversion, OneHoleContext.fill, pCombine] using rightStep)

/-- Every generator of the complete typed evidence conversion can be
replayed in the actual authored equation/rewrite presentation. -/
theorem authoredConversion_of_evidenceConversion
    {first second : WMTerm .evidence}
    (conversion : WMCalculusEvidenceConversion.EvidenceConversion first second) :
    AuthoredConversion (encodeWM first) (encodeWM second) := by
  induction conversion with
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ ihFirst ihSecond =>
      exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond
  | combine _ _ ihFirst ihSecond =>
      exact authoredConversion_combine ihFirst ihSecond
  | comm _ _ =>
      exact authoredConversion_of_equation (combine_comm_equivalent _ _)
  | assoc _ _ _ =>
      exact authoredConversion_of_equation (combine_assoc_equivalent _ _ _)
  | zero _ =>
      exact authoredConversion_of_equation (combine_zero_equivalent _)
  | extract _ _ _ =>
      exact authoredConversion_of_computation (encoded_extraction_computes _ _ _)

/-- Completeness in one direction for the encoded, typed evidence language.
The converse is not asserted for the generic raw matcher, which admits
ill-sorted equation instances outside this image. -/
theorem allReadingsAgree_implies_authoredConversion
    (first second : WMTerm .evidence)
    (agree : ∀ (State Query V : Type)
      (reading : Mettapedia.OSLF.Framework.WMCalculusSemantics.WMReading State Query V),
      reading.CoreLaws → reading.denote first = reading.denote second) :
    AuthoredConversion (encodeWM first) (encodeWM second) :=
  authoredConversion_of_evidenceConversion
    ((WMCalculusEvidenceConversion.conversion_iff_allReadings first second).2 agree)

#print axioms structural_validation
#print axioms structural_equations_sorted
#print axioms structural_rules_sorted
#print axioms directed_vs_structural_rules
#print axioms combine_zero_equivalent
#print axioms combine_assoc_equivalent
#print axioms encoded_structural_law_equivalent
#print axioms structural_law_allReadings
#print axioms authored_assoc_closes_directed_gap
#print axioms ill_sorted_zero_instance
#print axioms closed_zero_well_sorted
#print axioms state_pattern_not_evidence
#print axioms structural_not_openEquationFiberStable
#print axioms evidence_add_computes
#print axioms encoded_extraction_computes
#print axioms encoded_extraction_computes_native_open
#print axioms typed_structural_law_open_instance
#print axioms typed_structural_law_authored_equivalent
#print axioms encoded_evidence_replacement_typed_in_context
#print axioms structural_law_authored_equiv_and_typed_in_context
#print axioms specimen_structural_under_lambda
#print axioms encoded_evidence_replacement_openPatternWellSorted_in_context
#print axioms structural_law_authored_equiv_and_native_open_in_context
#print axioms structural_law_native_open_equation_setoid
#print axioms specimen_structural_under_lambda_native_open
#print axioms named_evidence_open_not_closed
#print axioms authoredConversion_of_evidenceConversion
#print axioms authoredContextStep_fill
#print axioms allReadingsAgree_implies_authoredConversion

end Mettapedia.OSLF.Framework.WMCalculusStructuralPresentation
