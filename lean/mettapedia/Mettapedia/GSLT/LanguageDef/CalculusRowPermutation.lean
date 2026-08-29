import Mathlib.Data.List.Perm.Basic
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# Order-insensitive rows of a flat calculus language

Incremental compilation and batch generation may emit the same declarations
in different orders.  This module records exactly the row families whose
order is observationally irrelevant to the admitted relational calculus:
sorts, constructors, judgment declarations, and inference rules.  Authored
equations and object-language rewrites remain byte-for-byte fixed because
their operational order can be significant.

`CalculusRowPermutation` is intentionally weaker than equality and stronger
than equality of row counts.  It retains every declaration with its
multiplicity.  For equation- and rewrite-free calculi, admission transports
across the relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Two flat calculi have the same declarations, possibly in different
order, while retaining the exact object-language dynamics. -/
structure CalculusRowPermutation
    (first second : CalculusLanguageDef) : Prop where
  name : first.name = second.name
  types : first.types.Perm second.types
  terms : first.terms.Perm second.terms
  equations : first.equations = second.equations
  rewrites : first.rewrites = second.rewrites
  judgments : first.judgments.Perm second.judgments
  rules : first.rules.Perm second.rules
  conversion : first.conversion = second.conversion

namespace CalculusRowPermutation

/-- Declaration-row permutation is reflexive. -/
theorem refl (definition : CalculusLanguageDef) :
    CalculusRowPermutation definition definition where
  name := rfl
  types := .refl _
  terms := .refl _
  equations := rfl
  rewrites := rfl
  judgments := .refl _
  rules := .refl _
  conversion := rfl

/-- Declaration-row permutation is symmetric. -/
theorem symm {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second) :
    CalculusRowPermutation second first where
  name := permutation.name.symm
  types := permutation.types.symm
  terms := permutation.terms.symm
  equations := permutation.equations.symm
  rewrites := permutation.rewrites.symm
  judgments := permutation.judgments.symm
  rules := permutation.rules.symm
  conversion := permutation.conversion.symm

/-- Declaration-row permutation is transitive. -/
theorem trans {first second third : CalculusLanguageDef}
    (earlier : CalculusRowPermutation first second)
    (later : CalculusRowPermutation second third) :
    CalculusRowPermutation first third where
  name := earlier.name.trans later.name
  types := earlier.types.trans later.types
  terms := earlier.terms.trans later.terms
  equations := earlier.equations.trans later.equations
  rewrites := earlier.rewrites.trans later.rewrites
  judgments := earlier.judgments.trans later.judgments
  rules := earlier.rules.trans later.rules
  conversion := earlier.conversion.trans later.conversion

/-- Applying the same ordered extension to both sides retains the relation. -/
theorem apply_extension {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second)
    (extension : CalculusLanguageExtension) :
    CalculusRowPermutation (extension.apply first) (extension.apply second) where
  name := by simp [CalculusLanguageExtension.apply, permutation.name]
  types := permutation.types.append_right extension.newTypes
  terms := permutation.terms.append_right extension.newTerms
  equations := by
    simp [CalculusLanguageExtension.apply, permutation.equations]
  rewrites := by
    simp [CalculusLanguageExtension.apply, permutation.rewrites]
  judgments := permutation.judgments.append_right extension.newJudgments
  rules := permutation.rules.append_right extension.newRules
  conversion := permutation.conversion

private theorem all_eq_of_perm {α : Type} {first second : List α}
    (permutation : first.Perm second) (predicate : α → Bool) :
    first.all predicate = second.all predicate := by
  by_cases allFirst : ∀ element ∈ first, predicate element = true
  · rw [List.all_eq_true.mpr allFirst, List.all_eq_true.mpr]
    intro element membership
    exact allFirst element (permutation.mem_iff.mpr membership)
  · have notAllSecond :
        ¬ ∀ element ∈ second, predicate element = true := by
      intro allSecond
      exact allFirst fun element membership =>
        allSecond element (permutation.mem_iff.mp membership)
    cases firstAll : first.all predicate with
    | false =>
        cases secondAll : second.all predicate with
        | false => rfl
        | true => exact absurd (List.all_eq_true.mp secondAll) notAllSecond
    | true => exact absurd (List.all_eq_true.mp firstAll) allFirst

private theorem all_congr_on {α : Type} {first second : α → Bool}
    (elements : List α)
    (pointwise : ∀ element ∈ elements, first element = second element) :
    elements.all first = elements.all second := by
  induction elements with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.all_cons]
      rw [pointwise head (by simp)]
      rw [inductionHypothesis fun element membership =>
        pointwise element (by simp [membership])]

private theorem any_eq_of_perm {α : Type} {first second : List α}
    (permutation : first.Perm second) (predicate : α → Bool) :
    first.any predicate = second.any predicate := by
  induction permutation with
  | nil => rfl
  | cons _ _ inductionHypothesis =>
      simp [inductionHypothesis]
  | swap first second rest =>
      simp [Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
  | trans _ _ firstEquality secondEquality =>
      exact firstEquality.trans secondEquality

private theorem eraseDups_length_le {α : Type} [BEq α] :
    (values : List α) → values.eraseDups.length ≤ values.length
  | [] => by simp
  | value :: values => by
      rw [List.eraseDups_cons]
      simp only [List.length_cons, Nat.succ_le_succ_iff]
      exact
        (eraseDups_length_le
          (values.filter fun candidate => !candidate == value)).trans
        (List.length_filter_le (fun candidate => !candidate == value) values)
termination_by values => values.length
decreasing_by
  simpa using Nat.lt_succ_of_le
    (List.length_filter_le (fun candidate => !candidate == value) values)

private theorem nodup_of_eraseDups_length_eq
    {α : Type} [BEq α] [LawfulBEq α] :
    (values : List α) → values.eraseDups.length = values.length → values.Nodup
  | [] => by simp
  | value :: values => by
      intro lengthEquality
      rw [List.eraseDups_cons] at lengthEquality
      simp only [List.length_cons, Nat.succ.injEq] at lengthEquality
      let filtered := values.filter fun candidate => !candidate == value
      change filtered.eraseDups.length = values.length at lengthEquality
      have erasedLength : filtered.eraseDups.length ≤ filtered.length :=
        eraseDups_length_le filtered
      have filteredLength : filtered.length ≤ values.length :=
        List.length_filter_le (fun candidate => !candidate == value) values
      have reverseLength : values.length ≤ filtered.length := by
        rw [← lengthEquality]
        exact erasedLength
      have equalLengths : filtered.length = values.length :=
        Nat.le_antisymm filteredLength reverseLength
      have allRetained : ∀ candidate ∈ values,
          !candidate == value = true :=
        List.length_filter_eq_length_iff.mp equalLengths
      have filterEquality : filtered = values :=
        List.filter_eq_self.mpr allRetained
      have recursiveLength :
          filtered.eraseDups.length = filtered.length :=
        lengthEquality.trans equalLengths.symm
      have tailNodup : filtered.Nodup :=
        nodup_of_eraseDups_length_eq filtered recursiveLength
      rw [filterEquality] at tailNodup
      simp only [List.nodup_cons]
      refine ⟨?_, tailNodup⟩
      intro membership
      have impossible := allRetained value membership
      simp at impossible
termination_by values => values.length
decreasing_by
  simpa [filtered] using Nat.lt_succ_of_le
    (List.length_filter_le (fun candidate => !candidate == value) values)

private theorem eraseDups_length_eq_of_nodup
    {α : Type} [BEq α] [LawfulBEq α] :
    (values : List α) → values.Nodup →
      values.eraseDups.length = values.length
  | [], _ => rfl
  | value :: values, nodup => by
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      have headFresh : value ∉ values := (List.nodup_cons.mp nodup).1
      have tailNodup : values.Nodup := (List.nodup_cons.mp nodup).2
      have filterEquality :
          (values.filter fun candidate => !candidate == value) = values := by
        apply List.filter_eq_self.mpr
        intro candidate membership
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
          beq_eq_false_iff_ne, ne_eq]
        intro equality
        exact headFresh (equality ▸ membership)
      rw [filterEquality, eraseDups_length_eq_of_nodup values tailNodup]

private theorem nodupCheck_eq_of_perm {α : Type} [BEq α] [LawfulBEq α]
    {first second : List α} (permutation : first.Perm second) :
    (first.eraseDups.length == first.length) =
      (second.eraseDups.length == second.length) := by
  by_cases firstNodup : first.Nodup
  · rw [beq_iff_eq.mpr (eraseDups_length_eq_of_nodup _ firstNodup),
      beq_iff_eq.mpr
        (eraseDups_length_eq_of_nodup _
          (permutation.nodup_iff.mp firstNodup))]
  · have secondNotNodup : ¬second.Nodup := fun secondNodup =>
      firstNodup (permutation.nodup_iff.mpr secondNodup)
    cases firstCheck : (first.eraseDups.length == first.length) with
    | false =>
        cases secondCheck : (second.eraseDups.length == second.length) with
        | false => rfl
        | true =>
            exact absurd
              (nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp secondCheck))
              secondNotNodup
    | true =>
        exact absurd
          (nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp firstCheck))
          firstNodup

private def singletonMap {α β : Type} (fallback : β) (map : α → β) :
    List α → β
  | [element] => map element
  | _ => fallback

private theorem singletonMap_eq_of_perm {α β : Type}
    (fallback : β) (map : α → β) {first second : List α}
    (permutation : first.Perm second) :
    singletonMap fallback map first = singletonMap fallback map second := by
  induction permutation with
  | nil => rfl
  | @cons element first second permutation inductionHypothesis =>
      cases first <;> cases second <;>
        simp_all [singletonMap]
  | swap first second rest =>
      rfl
  | trans _ _ firstEquality secondEquality =>
      exact firstEquality.trans secondEquality

theorem typeNames_perm {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second) :
    first.toLanguageDef.typeNames.Perm second.toLanguageDef.typeNames := by
  simpa [LanguageDef.typeNames] using permutation.types.map (·.name)

theorem judgmentHeads_perm {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second) :
    first.judgmentHeads.Perm second.judgmentHeads := by
  simpa [CalculusLanguageDef.judgmentHeads] using
    permutation.judgments.map (·.head)

theorem ruleIds_perm {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second) :
    first.ruleIds.Perm second.ruleIds := by
  simpa [CalculusLanguageDef.ruleIds] using permutation.rules.map (·.id)

private theorem validateTerm_eq_nil_of_typeNames_perm
    (first second : LanguageDef) (term : GrammarRule)
    (typeNames : first.typeNames.Perm second.typeNames)
    (clean : first.validateTerm term = []) :
    second.validateTerm term = [] := by
  simp only [LanguageDef.validateTerm, List.append_eq_nil_iff] at clean ⊢
  refine ⟨⟨?_, ?_⟩, clean.2⟩
  · have categoryMember : term.category ∈ first.typeNames := by
      by_contra absent
      simp [absent] at clean
    simp [typeNames.mem_iff.mp categoryMember]
  · rw [List.flatMap_eq_nil_iff]
    intro parameter parameterMembership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro name nameMembership
    apply typeNames.mem_iff.mp
    have parameterClean :=
      (List.flatMap_eq_nil_iff.mp clean.1.2) parameter parameterMembership
    exact LanguageDef.baseName_mem_of_validateTypeExpr_eq_nil
      first.typeNames s!"term {term.label}"
      (TermParam.typeExpr parameter) parameterClean nameMembership

/-- Structural language admission transports when object-language dynamics
are absent.  The theorem is row-wise: it does not re-run the source checker. -/
theorem language_validate_of_no_dynamics
    {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second)
    (firstEquations : first.equations = [])
    (firstRewrites : first.rewrites = [])
    (firstValid : first.toLanguageDef.validate = []) :
    second.toLanguageDef.validate = [] := by
  have typeNames := permutation.typeNames_perm
  have secondEquations : second.equations = [] := by
    rw [← permutation.equations, firstEquations]
  have secondRewrites : second.rewrites = [] := by
    rw [← permutation.rewrites, firstRewrites]
  apply LanguageDef.validate_eq_nil_of_rows
  · exact (typeNames.nodup_iff).mp
      (LanguageDef.typeNames_nodup_of_validate_eq_nil
        first.toLanguageDef firstValid)
  · exact ((permutation.terms.map (·.label)).nodup_iff).mp
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        first.toLanguageDef firstValid)
  · simp [secondEquations]
  · simp [secondRewrites]
  · intro term membership
    apply validateTerm_eq_nil_of_typeNames_perm
      first.toLanguageDef second.toLanguageDef term typeNames
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
      first.toLanguageDef firstValid term
      (permutation.terms.mem_iff.mpr membership)
  · intro equation membership
    simp [secondEquations] at membership
  · intro rewrite membership
    simp [secondRewrites] at membership

theorem lookupJudgment_eq {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second)
    (head : String) (arity : Nat) :
    first.lookupJudgment? head arity = second.lookupJudgment? head arity := by
  unfold CalculusLanguageDef.lookupJudgment?
  simpa only [singletonMap] using
    singletonMap_eq_of_perm none some
      (permutation.judgments.filter fun declaration =>
        declaration.head == head && declaration.arity == arity)

private theorem languageHasConstructorArity_eq
    {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second)
    (head : String) (arity : Nat) :
    languageHasConstructorArity first.toLanguageDef head arity =
      languageHasConstructorArity second.toLanguageDef head arity := by
  unfold languageHasConstructorArity
  simpa only [singletonMap] using
    singletonMap_eq_of_perm false
      (fun declaration : GrammarRule => declaration.params.length == arity)
      (permutation.terms.filter fun declaration => declaration.label == head)

mutual

private theorem fixedConstructorsValid_eq
    {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second) :
    (pattern : Pattern) →
      fixedConstructorsValid first.toLanguageDef pattern =
        fixedConstructorsValid second.toLanguageDef pattern
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply head arguments => by
      simp only [fixedConstructorsValid]
      rw [languageHasConstructorArity_eq permutation,
        fixedConstructorListsValid_eq permutation arguments]
  | .lambda _ body => by
      simpa only [fixedConstructorsValid] using
        fixedConstructorsValid_eq permutation body
  | .multiLambda _ _ body => by
      simpa only [fixedConstructorsValid] using
        fixedConstructorsValid_eq permutation body
  | .subst body replacement => by
      simp only [fixedConstructorsValid]
      rw [fixedConstructorsValid_eq permutation body,
        fixedConstructorsValid_eq permutation replacement]
  | .collection _ elements _ => by
      simpa only [fixedConstructorsValid] using
        fixedConstructorListsValid_eq permutation elements

private theorem fixedConstructorListsValid_eq
    {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second) :
    (patterns : List Pattern) →
      fixedConstructorListsValid first.toLanguageDef patterns =
        fixedConstructorListsValid second.toLanguageDef patterns
  | [] => rfl
  | pattern :: patterns => by
      simp only [fixedConstructorListsValid]
      rw [fixedConstructorsValid_eq permutation pattern,
        fixedConstructorListsValid_eq permutation patterns]

end

private theorem judgmentSchemaValid_eq
    {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second)
    (pattern : Pattern) :
    first.judgmentSchemaValid pattern = second.judgmentSchemaValid pattern := by
  cases pattern with
  | apply head arguments =>
      simp only [CalculusLanguageDef.judgmentSchemaValid]
      rw [permutation.lookupJudgment_eq,
        fixedConstructorListsValid_eq permutation arguments]
  | bvar index => rfl
  | fvar name => rfl
  | lambda name body => rfl
  | multiLambda name arity body => rfl
  | subst body replacement => rfl
  | collection collectionType elements rest => rfl

theorem ruleValidIn_eq {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second)
    (rule : RuleSchema) :
    RuleSchema.isValidIn first rule = RuleSchema.isValidIn second rule := by
  unfold RuleSchema.isValidIn
  congr 2
  congr 1
  apply all_congr_on
  intro pattern _membership
  exact judgmentSchemaValid_eq permutation pattern

theorem judgmentSignatureValid_eq {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second) :
    first.judgmentSignatureValid = second.judgmentSignatureValid := by
  let firstHeads := first.judgmentHeads
  let secondHeads := second.judgmentHeads
  have headsPermutation : firstHeads.Perm secondHeads :=
    permutation.judgmentHeads_perm
  have judgmentsAll :
      first.judgments.all (fun judgment => judgment.head != "") =
        second.judgments.all (fun judgment => judgment.head != "") :=
    all_eq_of_perm permutation.judgments _
  have headNodup := nodupCheck_eq_of_perm headsPermutation
  have constructorMembership (head : String) :
      (first.terms.any fun declaration => declaration.label == head) =
        (second.terms.any fun declaration => declaration.label == head) :=
    any_eq_of_perm permutation.terms _
  have headsAll :
      firstHeads.all (fun head =>
          !(first.terms.any fun declaration => declaration.label == head) &&
            !([Pattern.zipHead, Pattern.mapHead, Pattern.evalHead].contains head)) =
        secondHeads.all (fun head =>
          !(second.terms.any fun declaration => declaration.label == head) &&
            !([Pattern.zipHead, Pattern.mapHead, Pattern.evalHead].contains head)) := by
    calc
      _ = secondHeads.all (fun head =>
          !(first.terms.any fun declaration => declaration.label == head) &&
            !([Pattern.zipHead, Pattern.mapHead, Pattern.evalHead].contains head)) :=
        all_eq_of_perm headsPermutation _
      _ = _ := by
        apply all_congr_on
        intro head _membership
        rw [constructorMembership head]
  unfold CalculusLanguageDef.judgmentSignatureValid
  rw [judgmentsAll, headNodup, headsAll]

theorem conversionDeclarationValid_eq {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second) :
    first.conversionDeclarationValid = second.conversionDeclarationValid := by
  unfold CalculusLanguageDef.conversionDeclarationValid
  rw [← permutation.conversion]
  cases first.conversion with
  | none => rfl
  | some declaration =>
      simp only
      rw [permutation.lookupJudgment_eq]

/-- Complete calculus admission transports across declaration-row
permutation for equation- and rewrite-free calculi. -/
theorem target_isValid_of_no_dynamics
    {first second : CalculusLanguageDef}
    (permutation : CalculusRowPermutation first second)
    (firstEquations : first.equations = [])
    (firstRewrites : first.rewrites = [])
    (firstValid : first.isValid = true) :
    second.isValid = true := by
  have firstLocal : first.hasValidLocalRules = true := by
    simp only [CalculusLanguageDef.isValid, Bool.and_eq_true] at firstValid
    exact firstValid.1
  have firstLanguage : first.toLanguageDef.validate = [] := by
    simp only [CalculusLanguageDef.hasValidLocalRules, Bool.and_eq_true] at firstLocal
    simpa using firstLocal.1.1
  have secondLanguage := permutation.language_validate_of_no_dynamics
    firstEquations firstRewrites firstLanguage
  have localRules :
      second.rules.all RuleSchema.isLocallyValid =
        first.rules.all RuleSchema.isLocallyValid :=
    (all_eq_of_perm permutation.rules RuleSchema.isLocallyValid).symm
  have ruleIds := nodupCheck_eq_of_perm permutation.ruleIds_perm
  have secondLocal : second.hasValidLocalRules = true := by
    unfold CalculusLanguageDef.hasValidLocalRules
    rw [secondLanguage]
    simp only [List.isEmpty_nil, Bool.true_and]
    rw [localRules, ← ruleIds]
    unfold CalculusLanguageDef.hasValidLocalRules at firstLocal
    simpa using firstLocal
  have rulesValid :
      second.rules.all (RuleSchema.isValidIn second) =
        first.rules.all (RuleSchema.isValidIn first) := by
    calc
      _ = first.rules.all (RuleSchema.isValidIn second) :=
        (all_eq_of_perm permutation.rules
          (RuleSchema.isValidIn second)).symm
      _ = _ := by
        apply all_congr_on
        intro rule _membership
        exact (permutation.ruleValidIn_eq rule).symm
  unfold CalculusLanguageDef.isValid
  rw [secondLocal, ← permutation.judgmentSignatureValid_eq,
    rulesValid, ← permutation.conversionDeclarationValid_eq]
  simpa [CalculusLanguageDef.isValid] using firstValid

/-! ## Positive and negative controls -/

namespace Canary

private def carrierA : TypeDecl := TypeDecl.plain "row-permutation:A"
private def carrierB : TypeDecl := TypeDecl.plain "row-permutation:B"

private def constructorA : GrammarRule where
  label := "row-permutation:a"
  category := carrierA.name
  params := []
  syntaxPattern := []

private def constructorB : GrammarRule where
  label := "row-permutation:b"
  category := carrierB.name
  params := []
  syntaxPattern := []

private def judgmentA : JudgmentDecl := ⟨"row-permutation:J", 1⟩
private def judgmentB : JudgmentDecl := ⟨"row-permutation:K", 1⟩

private def ruleA : RuleSchema where
  id := ⟨"row-permutation:rule-a"⟩
  metavariables := []
  premises := []
  conclusion := .apply judgmentA.head [.apply constructorA.label []]

private def ruleB : RuleSchema where
  id := ⟨"row-permutation:rule-b"⟩
  metavariables := []
  premises := []
  conclusion := .apply judgmentB.head [.apply constructorB.label []]

private def authored : CalculusLanguageDef where
  name := "row-permutation"
  types := [carrierA, carrierB]
  terms := [constructorA, constructorB]
  equations := []
  rewrites := []
  judgments := [judgmentA, judgmentB]
  rules := [ruleA, ruleB]

private def reordered : CalculusLanguageDef where
  name := "row-permutation"
  types := [carrierB, carrierA]
  terms := [constructorB, constructorA]
  equations := []
  rewrites := []
  judgments := [judgmentB, judgmentA]
  rules := [ruleB, ruleA]

private theorem authored_valid : authored.isValid = true := by
  decide

private theorem reorderedRows : CalculusRowPermutation authored reordered where
  name := rfl
  types := List.Perm.swap carrierB carrierA []
  terms := List.Perm.swap constructorB constructorA []
  equations := rfl
  rewrites := rfl
  judgments := List.Perm.swap judgmentB judgmentA []
  rules := List.Perm.swap ruleB ruleA []
  conversion := rfl

/-- Reordering every static declaration family preserves admission. -/
theorem reordered_valid : reordered.isValid = true :=
  reorderedRows.target_isValid_of_no_dynamics rfl rfl authored_valid

private def droppedRule : CalculusLanguageDef :=
  { authored with rules := [ruleA] }

/-- Equal row counts are not enough: dropping a proof rule is rejected by the
permutation relation. -/
theorem dropped_rule_not_permutation :
    ¬ CalculusRowPermutation authored droppedRule := by
  intro permutation
  have lengths := permutation.rules.length_eq
  simp [authored, droppedRule] at lengths

end Canary

#print axioms refl
#print axioms symm
#print axioms trans
#print axioms apply_extension
#print axioms language_validate_of_no_dynamics
#print axioms lookupJudgment_eq
#print axioms ruleValidIn_eq
#print axioms judgmentSignatureValid_eq
#print axioms target_isValid_of_no_dynamics
#print axioms Canary.reordered_valid
#print axioms Canary.dropped_rule_not_permutation

end CalculusRowPermutation

end Mettapedia.GSLT.LanguageDef
