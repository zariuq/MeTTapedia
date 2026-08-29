import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.GSLT.LanguageDef.ExtensionGluing

/-!
# Conservative finite ground-fact extensions

A finite fact table is an independently authored proof calculus: one fresh
judgment declaration and zero-premise, metavariable-free rules.  This module
derives local rule validity from ground payloads, validates the fact calculus
on its own, and glues it to any compatible validated base calculus.

The construction authenticates facts only.  It does not turn encoded data into
an open object-language rule, perform substitution, or grant conversion
authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GroundFactExtension

open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.ExtensionGluing
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The object-language coordinate of every validated calculus is itself a
validated language definition. -/
theorem validated_languageValid (definition : ValidatedCalculusLanguageDef) :
    definition.1.toLanguageDef.validate = [] := by
  have valid := definition.2
  simp only [CalculusLanguageDef.isValid, Bool.and_eq_true] at valid
  have localRules : definition.1.hasValidLocalRules = true := valid.1.1.1
  simp only [CalculusLanguageDef.hasValidLocalRules, Bool.and_eq_true] at localRules
  simpa using localRules.1.1

/-! ## Constructor stability across disjoint syntax growth -/

/-- Add constructor rows while leaving every other language coordinate
unchanged. -/
def withAddedTerms (base : LanguageDef) (added : List GrammarRule) :
    LanguageDef :=
  { base with terms := base.terms ++ added }

/-- A successful constructor lookup survives appending a disjoint constructor
family.  This is the precise stability fact needed by proof-calculus layers
whose wire patterns use only older constructors. -/
theorem languageHasConstructorArity_withAddedTerms
    (base : LanguageDef) (added : List GrammarRule)
    (disjoint :
      List.Disjoint (base.terms.map (fun term => term.label))
        (added.map (fun term => term.label)))
    {head : String} {arity : Nat}
    (valid : languageHasConstructorArity base head arity = true) :
    languageHasConstructorArity (withAddedTerms base added) head arity = true := by
  unfold languageHasConstructorArity at valid ⊢
  change
    (match (base.terms ++ added).filter
        (fun declaration => declaration.label == head) with
      | [declaration] => declaration.params.length == arity
      | _ => false) = true
  rw [List.filter_append]
  cases filteredBase :
      base.terms.filter (fun declaration => declaration.label == head) with
  | nil => simp [filteredBase] at valid
  | cons declaration rest =>
      cases rest with
      | nil =>
          have declarationFiltered :
              declaration ∈ base.terms.filter
                (fun candidate => candidate.label == head) := by
            simp [filteredBase]
          have declarationInfo := List.mem_filter.mp declarationFiltered
          have addedEmpty :
              added.filter (fun candidate => candidate.label == head) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro candidate candidateMember candidateMatches
            have baseLabelMember :
                declaration.label ∈
                  base.terms.map (fun term => term.label) :=
              List.mem_map.mpr
                ⟨declaration, declarationInfo.1, rfl⟩
            have addedLabelMember :
                candidate.label ∈
                  added.map (fun term => term.label) :=
              List.mem_map.mpr ⟨candidate, candidateMember, rfl⟩
            have declarationHead : declaration.label = head :=
              beq_iff_eq.mp declarationInfo.2
            have candidateHead : candidate.label = head :=
              beq_iff_eq.mp candidateMatches
            exact (List.disjoint_left.mp disjoint)
              baseLabelMember
              (declarationHead.trans candidateHead.symm ▸ addedLabelMember)
          simp [filteredBase, addedEmpty] at valid ⊢
          exact valid
      | cons second tail => simp [filteredBase] at valid

/-- Constructor-arity refinement is the exact hypothesis under which fixed
schema fragments remain valid. -/
def ConstructorArityRefines (source target : LanguageDef) : Prop :=
  ∀ {head : String} {arity : Nat},
    languageHasConstructorArity source head arity = true →
      languageHasConstructorArity target head arity = true

mutual

theorem fixedConstructorsValid_of_refines
    {source target : LanguageDef}
    (refines : ConstructorArityRefines source target)
    (pattern : Pattern)
    (valid : fixedConstructorsValid source pattern = true) :
    fixedConstructorsValid target pattern = true := by
  cases pattern with
  | bvar index => simp [fixedConstructorsValid]
  | fvar name => simp [fixedConstructorsValid]
  | apply head arguments =>
      simp only [fixedConstructorsValid, Bool.and_eq_true] at valid ⊢
      exact
        ⟨refines valid.1,
          fixedConstructorListsValid_of_refines refines arguments valid.2⟩
  | lambda binder body =>
      simpa [fixedConstructorsValid] using
        fixedConstructorsValid_of_refines refines body
          (by simpa [fixedConstructorsValid] using valid)
  | multiLambda arity binders body =>
      simpa [fixedConstructorsValid] using
        fixedConstructorsValid_of_refines refines body
          (by simpa [fixedConstructorsValid] using valid)
  | subst body replacement =>
      simp only [fixedConstructorsValid, Bool.and_eq_true] at valid ⊢
      exact
        ⟨fixedConstructorsValid_of_refines refines body valid.1,
          fixedConstructorsValid_of_refines refines replacement valid.2⟩
  | collection collectionType elements rest =>
      simpa [fixedConstructorsValid] using
        fixedConstructorListsValid_of_refines refines elements
          (by simpa [fixedConstructorsValid] using valid)
termination_by sizeOf pattern

theorem fixedConstructorListsValid_of_refines
    {source target : LanguageDef}
    (refines : ConstructorArityRefines source target)
    (patterns : List Pattern)
    (valid : fixedConstructorListsValid source patterns = true) :
    fixedConstructorListsValid target patterns = true := by
  cases patterns with
  | nil => simp [fixedConstructorListsValid]
  | cons pattern patterns =>
      simp only [fixedConstructorListsValid, Bool.and_eq_true] at valid ⊢
      exact
        ⟨fixedConstructorsValid_of_refines refines pattern valid.1,
          fixedConstructorListsValid_of_refines refines patterns valid.2⟩
termination_by sizeOf patterns

end

/-! ## Ground patterns have no schema metavariables or collection tails -/

mutual

theorem occurrences_eq_nil_of_groundAt
    (depth : Nat) (pattern : Pattern)
    (ground : pattern.isGroundAt depth = true) :
    patternMetavariableOccurrencesAt depth pattern = [] := by
  cases pattern with
  | bvar index => simp [patternMetavariableOccurrencesAt]
  | fvar name => simp [Pattern.isGroundAt] at ground
  | apply head arguments =>
      simpa [patternMetavariableOccurrencesAt] using
        occurrencesList_eq_nil_of_groundAt depth arguments ground
  | lambda binder body =>
      simpa [patternMetavariableOccurrencesAt] using
        occurrences_eq_nil_of_groundAt (depth + 1) body ground
  | multiLambda arity binders body =>
      simpa [patternMetavariableOccurrencesAt] using
        occurrences_eq_nil_of_groundAt (depth + arity) body ground
  | subst body replacement =>
      simp only [Pattern.isGroundAt, Bool.and_eq_true] at ground
      simp [patternMetavariableOccurrencesAt,
        occurrences_eq_nil_of_groundAt (depth + 1) body ground.1,
        occurrences_eq_nil_of_groundAt depth replacement ground.2]
  | collection collectionType elements rest =>
      simp only [Pattern.isGroundAt, Bool.and_eq_true] at ground
      simpa [patternMetavariableOccurrencesAt] using
        occurrencesList_eq_nil_of_groundAt depth elements ground.1
termination_by sizeOf pattern

theorem occurrencesList_eq_nil_of_groundAt
    (depth : Nat) (patterns : List Pattern)
    (ground : Pattern.isGroundListAt depth patterns = true) :
    patternsMetavariableOccurrencesAt depth patterns = [] := by
  cases patterns with
  | nil => simp [patternsMetavariableOccurrencesAt]
  | cons pattern patterns =>
      simp only [Pattern.isGroundListAt, Bool.and_eq_true] at ground
      simp [patternsMetavariableOccurrencesAt,
        occurrences_eq_nil_of_groundAt depth pattern ground.1,
        occurrencesList_eq_nil_of_groundAt depth patterns ground.2]
termination_by sizeOf patterns

end

mutual

theorem noCollectionRest_of_groundAt
    (depth : Nat) (pattern : Pattern)
    (ground : pattern.isGroundAt depth = true) :
    patternHasNoCollectionRest pattern = true := by
  cases pattern with
  | bvar index => simp [patternHasNoCollectionRest]
  | fvar name => simp [patternHasNoCollectionRest]
  | apply head arguments =>
      simpa [patternHasNoCollectionRest] using
        noCollectionRestList_of_groundAt depth arguments ground
  | lambda binder body =>
      simpa [patternHasNoCollectionRest] using
        noCollectionRest_of_groundAt (depth + 1) body ground
  | multiLambda arity binders body =>
      simpa [patternHasNoCollectionRest] using
        noCollectionRest_of_groundAt (depth + arity) body ground
  | subst body replacement =>
      simp only [Pattern.isGroundAt, Bool.and_eq_true] at ground
      simp [patternHasNoCollectionRest,
        noCollectionRest_of_groundAt (depth + 1) body ground.1,
        noCollectionRest_of_groundAt depth replacement ground.2]
  | collection collectionType elements rest =>
      simp only [Pattern.isGroundAt, Bool.and_eq_true] at ground
      cases rest with
      | none =>
          simpa [patternHasNoCollectionRest] using
            noCollectionRestList_of_groundAt depth elements ground.1
      | some restName => simp at ground
termination_by sizeOf pattern

theorem noCollectionRestList_of_groundAt
    (depth : Nat) (patterns : List Pattern)
    (ground : Pattern.isGroundListAt depth patterns = true) :
    patternsHaveNoCollectionRest patterns = true := by
  cases patterns with
  | nil => simp [patternsHaveNoCollectionRest]
  | cons pattern patterns =>
      simp only [Pattern.isGroundListAt, Bool.and_eq_true] at ground
      simp [patternsHaveNoCollectionRest,
        noCollectionRest_of_groundAt depth pattern ground.1,
        noCollectionRestList_of_groundAt depth patterns ground.2]
termination_by sizeOf patterns

end

/-! ## An independently valid finite fact calculus -/

/-- One fact row.  The outer judgment head is supplied by the family; the row
owns a unique rule identifier and the exact closed argument vector. -/
structure Row (language : LanguageDef) (judgment : JudgmentDecl) where
  id : RuleId
  arguments : List Pattern
  idNonempty : (id.value != "") = true
  arity : arguments.length = judgment.arity
  ground : Pattern.isGroundListAt 0 arguments = true
  canonical : Pattern.hasCanonicalBinderMetadataList arguments = true
  fixedConstructors : fixedConstructorListsValid language arguments = true

namespace Row

def conclusion {language : LanguageDef} {judgment : JudgmentDecl}
    (row : Row language judgment) : Pattern :=
  .apply judgment.head row.arguments

def rule {language : LanguageDef} {judgment : JudgmentDecl}
    (row : Row language judgment) : RuleSchema where
  id := row.id
  metavariables := []
  premises := []
  conclusion := row.conclusion

theorem conclusion_ground {language : LanguageDef}
    {judgment : JudgmentDecl} (row : Row language judgment) :
    row.conclusion.isGround = true := by
  simpa [conclusion, Pattern.isGround, Pattern.isGroundAt] using row.ground

theorem rule_isLocallyValid {language : LanguageDef}
    {judgment : JudgmentDecl} (row : Row language judgment) :
    RuleSchema.isLocallyValid row.rule = true := by
  have occurrences : RuleSchema.occurrences row.rule = [] := by
    change patternsMetavariableOccurrencesAt 0 [row.conclusion] = []
    simp [patternsMetavariableOccurrencesAt,
      occurrences_eq_nil_of_groundAt 0 row.conclusion row.conclusion_ground]
  have wellScoped : row.conclusion.isWellScoped = true :=
    isWellScoped_of_isGround row.conclusion_ground
  have noRest : patternHasNoCollectionRest row.conclusion = true :=
    noCollectionRest_of_groundAt 0 row.conclusion row.conclusion_ground
  simp only [RuleSchema.isLocallyValid]
  rw [occurrences]
  simp [RuleSchema.metavariableNames, RuleSchema.patterns, rule,
    row.idNonempty]
  exact
    ⟨⟨by simpa [conclusion] using wellScoped,
       by simpa [conclusion] using noRest⟩,
     by simpa [conclusion, Pattern.hasCanonicalBinderMetadata] using
       row.canonical⟩

end Row

/-- A finite family admitted independently of any base proof calculus. -/
structure Family (language : LanguageDef) where
  judgment : JudgmentDecl
  rows : List (Row language judgment)
  languageValid : language.validate = []
  judgmentHeadNonempty : (judgment.head != "") = true
  judgmentTermDisjoint :
    (!(language.terms.any fun declaration =>
      declaration.label == judgment.head)) = true
  judgmentNotReserved :
    (!([Pattern.zipHead, Pattern.mapHead, Pattern.evalHead].contains
      judgment.head)) = true
  ruleIdsDistinct :
    (((rows.map fun row => row.id).eraseDups.length ==
      (rows.map fun row => row.id).length)) = true

namespace Family

def calculus {language : LanguageDef} (family : Family language) :
    ProofCalculus where
  judgments := [family.judgment]
  rules := family.rows.map Row.rule
  conversion := none

def definition {language : LanguageDef} (family : Family language) :
    CalculusLanguageDef :=
  CalculusLanguageDef.extend language family.calculus

theorem rules_locallyValid {language : LanguageDef}
    (family : Family language) :
    family.definition.rules.all RuleSchema.isLocallyValid = true := by
  apply List.all_eq_true.mpr
  intro rule member
  rcases List.mem_map.mp member with ⟨row, rowMember, rfl⟩
  exact row.rule_isLocallyValid

theorem rule_isValidIn {language : LanguageDef}
    (family : Family language) (row : Row language family.judgment) :
    RuleSchema.isValidIn family.definition row.rule = true := by
  unfold RuleSchema.isValidIn
  rw [row.rule_isLocallyValid]
  simp [RuleSchema.patterns, Row.rule, Row.conclusion, definition, calculus,
    CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, row.arity,
    row.fixedConstructors]

theorem rules_validIn {language : LanguageDef}
    (family : Family language) :
    family.definition.rules.all (RuleSchema.isValidIn family.definition) =
      true := by
  apply List.all_eq_true.mpr
  intro rule member
  rcases List.mem_map.mp member with ⟨row, rowMember, rfl⟩
  exact family.rule_isValidIn row

/-- Ground facts form a valid proof calculus before they are attached to any
larger calculus. -/
theorem definition_valid {language : LanguageDef}
    (family : Family language) : family.definition.isValid = true := by
  have localRules : family.definition.hasValidLocalRules = true := by
    unfold CalculusLanguageDef.hasValidLocalRules
    change
      (language.validate.isEmpty &&
        family.definition.rules.all RuleSchema.isLocallyValid &&
        family.definition.ruleIds.eraseDups.length ==
          family.definition.ruleIds.length) = true
    rw [family.languageValid]
    simp only [List.isEmpty_nil, Bool.true_and]
    rw [family.rules_locallyValid]
    simp only [Bool.true_and]
    simpa [definition, calculus, CalculusLanguageDef.ruleIds,
      Function.comp_def, Row.rule] using family.ruleIdsDistinct
  have signature : family.definition.judgmentSignatureValid = true := by
    have reserved :
        family.judgment.head ≠ Pattern.zipHead ∧
          family.judgment.head ≠ Pattern.mapHead ∧
          family.judgment.head ≠ Pattern.evalHead := by
      simpa using family.judgmentNotReserved
    have singletonDistinct :
        (([family.judgment.head].eraseDups.length == 1)) = true :=
      (eraseDups_length_iff_nodup [family.judgment.head]).2 (by simp)
    simp [CalculusLanguageDef.judgmentSignatureValid,
      CalculusLanguageDef.judgmentHeads, definition, calculus,
      family.judgmentHeadNonempty, family.judgmentTermDisjoint,
      reserved, singletonDistinct]
  have conversion : family.definition.conversionDeclarationValid = true := by
    simp [CalculusLanguageDef.conversionDeclarationValid, definition, calculus]
  simp [CalculusLanguageDef.isValid, localRules, signature,
    family.rules_validIn, conversion]

def validated {language : LanguageDef} (family : Family language) :
    ValidatedCalculusLanguageDef :=
  ⟨family.definition, family.definition_valid⟩

end Family

/-! ## Conservative gluing over a validated base -/

/-- A fact family whose sole judgment and every rule identifier are fresh for
one validated base calculus. -/
structure Over (base : ValidatedCalculusLanguageDef) where
  family : Family base.1.toLanguageDef
  judgmentFresh :
    (!(base.1.judgments.any fun existing =>
      existing.head == family.judgment.head)) = true
  ruleIdsFresh :
    family.rows.all (fun row =>
      !(base.1.rules.any fun existing => existing.id == row.id)) = true

namespace Over

def delta {base : ValidatedCalculusLanguageDef} (over : Over base) :
    CalculusLanguageExtension where
  newJudgments := [over.family.judgment]
  newRules := over.family.rows.map Row.rule

theorem compatible {base : ValidatedCalculusLanguageDef}
    (over : Over base) :
    Compatible base.1.toCalculus over.family.calculus := by
  constructor
  · intro head baseMember factMember
    simp [Family.calculus] at factMember
    subst head
    rcases List.mem_map.mp baseMember with ⟨declaration, member, equality⟩
    have found :
        base.1.judgments.any (fun existing =>
          existing.head == over.family.judgment.head) = true := by
      apply List.any_eq_true.mpr
      exact ⟨declaration, member, by simp [equality]⟩
    have fresh := over.judgmentFresh
    rw [found] at fresh
    simp at fresh
  · intro id baseMember factMember
    rcases List.mem_map.mp baseMember with ⟨baseRule, baseRuleMember, equality⟩
    rcases List.mem_map.mp factMember with ⟨factRule, factRuleMember, factEquality⟩
    rcases List.mem_map.mp factRuleMember with ⟨row, rowMember, rowEquality⟩
    subst factRule
    simp [Row.rule] at factEquality
    have baseIdEq : baseRule.id = row.id := equality.trans factEquality.symm
    have rowsFresh := List.all_eq_true.mp over.ruleIdsFresh row rowMember
    have found :
        base.1.rules.any (fun existing => existing.id == row.id) = true := by
      apply List.any_eq_true.mpr
      exact ⟨baseRule, baseRuleMember, by simp [baseIdEq]⟩
    rw [found] at rowsFresh
    simp at rowsFresh
  · exact Or.inr rfl

theorem delta_apply_eq_merge {base : ValidatedCalculusLanguageDef}
    (over : Over base) :
    over.delta.apply base.1 =
      CalculusLanguageDef.extend base.1.toLanguageDef
        (mergeOf base.1.toCalculus over.family.calculus) := by
  apply CalculusLanguageDef.ext <;>
    simp [delta, CalculusLanguageExtension.apply,
      CalculusLanguageDef.extend, mergeOf, Family.calculus]

theorem target_valid {base : ValidatedCalculusLanguageDef}
    (over : Over base) : (over.delta.apply base.1).isValid = true := by
  have baseValid :
      (CalculusLanguageDef.extend base.1.toLanguageDef
        base.1.toCalculus).isValid = true := by
    simpa using base.2
  have glued :=
    (gluing_of_compatible base.1.toLanguageDef base.1.toCalculus
      over.family.calculus baseValid over.family.definition_valid
      over.compatible).2
  rw [over.delta_apply_eq_merge]
  exact glued

theorem delta_disjoint {base : ValidatedCalculusLanguageDef}
    (over : Over base) : over.delta.disjointFrom base.1 = true := by
  simp only [delta, CalculusLanguageExtension.disjointFrom,
    List.all_nil, Bool.true_and, List.all_cons,
    Bool.and_true]
  rw [Bool.and_eq_true]
  constructor
  · exact over.judgmentFresh
  · simpa [Row.rule] using over.ruleIdsFresh

theorem delta_policy {base : ValidatedCalculusLanguageDef}
    (over : Over base) :
    over.delta.policyHolds base.1 .newJudgmentsOnly = true := by
  unfold CalculusLanguageExtension.policyHolds
  change
    (over.family.rows.map Row.rule).all (fun rule =>
      match rule.conclusion with
      | .apply head _ =>
          !(base.1.judgments.any fun judgment => judgment.head == head)
      | _ => false) = true
  rw [List.all_map]
  apply List.all_eq_true.mpr
  intro row member
  change
    (!(base.1.judgments.any fun judgment =>
      judgment.head == over.family.judgment.head)) = true
  exact over.judgmentFresh

/-- The generic conservative admission result. -/
def validatedExtension {base : ValidatedCalculusLanguageDef}
    (over : Over base) : ValidatedCalculusLanguageExtension base where
  extension := over.delta
  policy := .newJudgmentsOnly
  disjoint := over.delta_disjoint
  policyHolds := over.delta_policy
  valid := over.target_valid

/-- A fact layer cannot silently reuse a judgment head already present in its
base. -/
theorem judgment_not_in_base {base : ValidatedCalculusLanguageDef}
    (over : Over base) :
    over.family.judgment.head ∉ base.1.judgmentHeads := by
  intro member
  rcases List.mem_map.mp member with ⟨declaration, declarationMember, equality⟩
  have found :
      base.1.judgments.any (fun existing =>
        existing.head == over.family.judgment.head) = true := by
    apply List.any_eq_true.mpr
    exact ⟨declaration, declarationMember, by simp [equality]⟩
  have fresh := over.judgmentFresh
  rw [found] at fresh
  simp at fresh

end Over

#print axioms Row.rule_isLocallyValid
#print axioms validated_languageValid
#print axioms languageHasConstructorArity_withAddedTerms
#print axioms fixedConstructorListsValid_of_refines
#print axioms Family.definition_valid
#print axioms Over.target_valid
#print axioms Over.validatedExtension
#print axioms Over.judgment_not_in_base

end Mettapedia.GSLT.LanguageDef.GroundFactExtension
