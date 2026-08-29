import Mettapedia.Languages.Metamath.SourceInferenceProjection
import Mettapedia.Languages.Metamath.InferenceProjectionInvariants
import Mathlib.Data.List.Nodup
import Std.Data.String.ToNat

/-!
# Validation of source-generated inference languages

The source projection is fail-closed at its three semantic namespace gates.
This module proves that passing those gates produces a contextually valid
calculus language, so proof reflection can construct the required validated target
rather than receive it from a caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceInferenceProjectionValidation

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSideConditions
open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-- Append a finite source vocabulary and source rule table to the fixed
Metamath side-condition calculus. -/
def sourceInferenceLanguageDef
    (vocabulary : List String) (sourceRules : List SourceRuleSchema) :
    CalculusLanguageDef :=
  CalculusLanguageDef.extend (languageWithSourceVocabulary vocabulary)
    { judgments := judgmentDecls ++ [provesDecl]
      rules := sideRules ++ sourceRules }

/-- The raw language selected after the three source-projection gates. -/
def rawSourceInferenceLanguageDef (source : SourcePrefix) : CalculusLanguageDef :=
  sourceInferenceLanguageDef (sourcePrefixVocabulary source)
    (sourceGeneratedRules source)

/-- Fixed Metamath side-condition calculus with the source-provability
judgment declared, before adding any prefix-indexed constructors or rules. -/
def sourceInferenceBaseLanguageDef : CalculusLanguageDef :=
  CalculusLanguageDef.extend dataLanguage
    { judgments := judgmentDecls ++ [provesDecl]
      rules := sideRules }

theorem sourceInferenceBaseLanguageDef_judgmentSignatureValid :
    sourceInferenceBaseLanguageDef.judgmentSignatureValid = true := by
  simp [sourceInferenceBaseLanguageDef,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    judgmentDecls, provesDecl, dataLanguage, dataConstructor,
    dataTypeName, stringHead, nilHead, consHead, constSymHead, varSymHead,
    formulaHead, dvPairHead, frameHead, bindingHead, substitutionHead,
    appendHead, lookupHead, substBodyHead, applySubstHead, varsHead,
    memberHead, dvRelHead, allWithHead, allPairsHead, dvListsHead,
    dvOKHead, provesHead, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead]
  decide

structure SourceProjectionGates (source : SourcePrefix) : Prop where
  prefixValid : sourcePrefixValid source = true
  vocabularyValid :
    sourceVocabularyValid (sourcePrefixVocabulary source) = true
  ruleIdsDisjoint :
    sourceRuleIdsDisjoint
      (List.map Mettapedia.OSLF.MeTTaIL.Syntax.RuleSchema.id
        (sourceGeneratedRules source)) = true

private theorem guard_some {condition : Prop} [Decidable condition]
    {result : Unit} (guarded : guard condition = some result) : condition := by
  by_contra falseCondition
  simp [guard, falseCondition] at guarded

theorem sourceProjectionGates_of_generated
    {source : SourcePrefix} {definition : CalculusLanguageDef}
    (generated :
      calculusLanguageDefOfSourcePrefix? source = some definition) :
    SourceProjectionGates source := by
  unfold calculusLanguageDefOfSourcePrefix? at generated
  simp only [Option.bind_eq_bind] at generated
  rw [Option.bind_eq_some_iff] at generated
  rcases generated with ⟨unitPrefix, guardedPrefix, generated⟩
  rw [Option.bind_eq_some_iff] at generated
  rcases generated with ⟨unitVocabulary, guardedVocabulary, generated⟩
  rw [Option.bind_eq_some_iff] at generated
  rcases generated with ⟨unitRules, guardedRules, _⟩
  exact
    { prefixValid := guard_some guardedPrefix
      vocabularyValid := guard_some guardedVocabulary
      ruleIdsDisjoint := guard_some guardedRules }

theorem definition_eq_rawSourceInferenceLanguageDef_of_generated
    {source : SourcePrefix} {definition : CalculusLanguageDef}
    (generated :
      calculusLanguageDefOfSourcePrefix? source = some definition) :
    definition = rawSourceInferenceLanguageDef source := by
  unfold calculusLanguageDefOfSourcePrefix? at generated
  simp only [Option.bind_eq_bind] at generated
  repeat' first
    | rw [Option.bind_eq_some_iff] at generated
      rcases generated with ⟨_, _, generated⟩
  simpa [rawSourceInferenceLanguageDef, sourceInferenceLanguageDef] using
    Option.some.inj generated.symm

/-- Passing the three source-owned projection gates constructs exactly the
raw language derived from that source prefix.  This is the forward
counterpart of `sourceProjectionGates_of_generated`: callers need not execute
the partial generator merely to recover its successful result. -/
theorem calculusLanguageDefOfSourcePrefix_eq_some_rawSourceInferenceLanguageDef
    (source : SourcePrefix) (gates : SourceProjectionGates source) :
    calculusLanguageDefOfSourcePrefix? source =
      some (rawSourceInferenceLanguageDef source) := by
  unfold calculusLanguageDefOfSourcePrefix?
  rw [gates.prefixValid]
  simp only [guard]
  rw [gates.vocabularyValid]
  rw [gates.ruleIdsDisjoint]
  rfl

private theorem sourceVocabularyValid_nodup
    {heads : List String} (valid : sourceVocabularyValid heads = true) :
    heads.Nodup := by
  simp only [sourceVocabularyValid, Bool.and_eq_true, beq_iff_eq] at valid
  exact nodup_of_eraseDups_length_eq heads valid.2

private theorem eraseDups_length_eq_of_nodup_strings :
    (values : List String) → values.Nodup →
      values.eraseDups.length = values.length
  | [], _ => rfl
  | value :: values, nodup => by
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      have headAbsent : value ∉ values := (List.nodup_cons.mp nodup).1
      have tailNodup : values.Nodup := (List.nodup_cons.mp nodup).2
      have filtered :
          (values.filter fun candidate => !candidate == value) = values := by
        apply List.filter_eq_self.mpr
        intro candidate member
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
          beq_eq_false_iff_ne, ne_eq]
        intro equal
        exact headAbsent (equal ▸ member)
      rw [filtered, eraseDups_length_eq_of_nodup_strings values tailNodup]

private theorem eraseDups_eq_self_of_nodup
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    (values : List alpha) → values.Nodup → values.eraseDups = values
  | [], _ => rfl
  | value :: values, nodup => by
      rw [List.eraseDups_cons]
      have headAbsent : value ∉ values := (List.nodup_cons.mp nodup).1
      have tailNodup : values.Nodup := (List.nodup_cons.mp nodup).2
      have filtered :
          (values.filter fun candidate => !candidate == value) = values := by
        apply List.filter_eq_self.mpr
        intro candidate member
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
          beq_eq_false_iff_ne]
        intro equal
        exact headAbsent (equal ▸ member)
      rw [filtered, eraseDups_eq_self_of_nodup values tailNodup]

private theorem sourceVocabularyValid_head
    {heads : List String} (valid : sourceVocabularyValid heads = true)
    {head : String} (member : head ∈ heads) :
    head ≠ "" ∧ (!head.startsWith reservedRulePrefix) = true ∧
      (!reservedProjectionHeads.contains head) = true := by
  simp only [sourceVocabularyValid, Bool.and_eq_true] at valid
  have accepted := List.all_eq_true.mp valid.1 head member
  simp only [Bool.and_eq_true, bne_iff_ne] at accepted
  exact ⟨accepted.1.1, accepted.1.2, accepted.2⟩

private theorem sourceVocabularyValid_not_mem_reserved
    {heads : List String} (valid : sourceVocabularyValid heads = true)
    {head : String} (reserved : head ∈ reservedProjectionHeads) :
    head ∉ heads := by
  intro member
  have rejected := (sourceVocabularyValid_head valid member).2.2
  have notReserved : head ∉ reservedProjectionHeads := by
    simpa [List.contains_iff_mem] using rejected
  exact notReserved reserved

private theorem sourceVocabularyValid_ne_reserved
    {heads : List String} (valid : sourceVocabularyValid heads = true)
    {head reservedHead : String} (member : head ∈ heads)
    (reserved : reservedHead ∈ reservedProjectionHeads) :
    head ≠ reservedHead := by
  intro equal
  subst head
  exact sourceVocabularyValid_not_mem_reserved valid reserved member

private theorem sourceJudgmentHead_mem_reserved
    {declaration : JudgmentDecl}
    (member : declaration ∈ judgmentDecls ++ [provesDecl]) :
    declaration.head ∈ reservedProjectionHeads := by
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with sideMember | rfl
  · have mapped :=
      List.mem_map_of_mem (f := JudgmentDecl.head) sideMember
    have sideHead : declaration.head ∈ reservedJudgmentHeads := by
      simpa [judgmentDecls, reservedJudgmentHeads] using mapped
    simp [reservedProjectionHeads, reservedInternalHeads, sideHead]
  · simp [provesDecl, reservedProjectionHeads]

private theorem sourceJudgmentHeadString_mem_reserved
    {head : String}
    (member : head ∈ (judgmentDecls ++ [provesDecl]).map JudgmentDecl.head) :
    head ∈ reservedProjectionHeads := by
  rcases List.mem_map.mp member with ⟨declaration, declarationMember, rfl⟩
  exact sourceJudgmentHead_mem_reserved declarationMember

private theorem languageWithSourceVocabulary_validate
    (heads : List String) (valid : sourceVocabularyValid heads = true) :
    (languageWithSourceVocabulary heads).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly
  all_goals
    simp [languageWithSourceVocabulary, dataConstructor,
      nullaryDataConstructor, dataTypeName, stringHead, nilHead, consHead,
      constSymHead, varSymHead, formulaHead, dvPairHead, frameHead,
      bindingHead, substitutionHead, LanguageDef.typeNames,
      TypeDecl.plain, TermParam.typeExpr, TypeExpr.baseNames]
  exact
    ⟨ sourceVocabularyValid_not_mem_reserved valid (by
        simp [reservedProjectionHeads, reservedInternalHeads,
          reservedDataHeads, stringHead])
    , sourceVocabularyValid_not_mem_reserved valid (by
        simp [reservedProjectionHeads, reservedInternalHeads,
          reservedDataHeads, nilHead])
    , sourceVocabularyValid_not_mem_reserved valid (by
        simp [reservedProjectionHeads, reservedInternalHeads,
          reservedDataHeads, consHead])
    , sourceVocabularyValid_not_mem_reserved valid (by
        simp [reservedProjectionHeads, reservedInternalHeads,
          reservedDataHeads, constSymHead])
    , sourceVocabularyValid_not_mem_reserved valid (by
        simp [reservedProjectionHeads, reservedInternalHeads,
          reservedDataHeads, varSymHead])
    , sourceVocabularyValid_not_mem_reserved valid (by
        simp [reservedProjectionHeads, reservedInternalHeads,
          reservedDataHeads, formulaHead])
    , sourceVocabularyValid_not_mem_reserved valid (by
        simp [reservedProjectionHeads, reservedInternalHeads,
          reservedDataHeads, dvPairHead])
    , sourceVocabularyValid_not_mem_reserved valid (by
        simp [reservedProjectionHeads, reservedInternalHeads,
          reservedDataHeads, frameHead])
    , sourceVocabularyValid_not_mem_reserved valid (by
        simp [reservedProjectionHeads, reservedInternalHeads,
          reservedDataHeads, bindingHead])
    , sourceVocabularyValid_not_mem_reserved valid (by
        simp [reservedProjectionHeads, reservedInternalHeads,
          reservedDataHeads, substitutionHead])
    , by
        simpa [Function.comp_def, nullaryDataConstructor, dataConstructor] using
          sourceVocabularyValid_nodup valid ⟩

private theorem sourceInferenceLanguageDef_judgmentSignatureValid
    (heads : List String) (sourceRules : List SourceRuleSchema)
    (valid : sourceVocabularyValid heads = true) :
    (sourceInferenceLanguageDef heads sourceRules).judgmentSignatureValid =
      true := by
  have base := sourceInferenceBaseLanguageDef_judgmentSignatureValid
  unfold CalculusLanguageDef.judgmentSignatureValid at base ⊢
  simp only [sourceInferenceBaseLanguageDef, sourceInferenceLanguageDef,
    CalculusLanguageDef.extend, languageWithSourceVocabulary,
    Bool.and_eq_true] at base ⊢
  refine ⟨⟨base.1.1, base.1.2⟩, ?_⟩
  apply List.all_eq_true.mpr
  intro judgmentHead judgmentHeadMember
  have baseDeclaration :=
    List.all_eq_true.mp base.2 judgmentHead judgmentHeadMember
  simp only [Bool.and_eq_true] at baseDeclaration ⊢
  refine ⟨?_, baseDeclaration.2⟩
  have newTermsAbsent :
      (heads.map nullaryDataConstructor).any
          (fun term => term.label == judgmentHead) = false := by
    rw [List.any_eq_false]
    intro term termMember
    rcases List.mem_map.mp termMember with ⟨head, headMember, rfl⟩
    have unequal := sourceVocabularyValid_ne_reserved valid headMember
      (sourceJudgmentHeadString_mem_reserved judgmentHeadMember)
    simp [nullaryDataConstructor, dataConstructor, unequal]
  rw [List.any_append, newTermsAbsent, Bool.or_false]
  exact baseDeclaration.1

/-! ## Constructor lookup in the extended data language -/

private theorem filter_eq_singleton_of_nodup_mem
    {values : List String} {target : String}
    (nodup : values.Nodup) (member : target ∈ values) :
    values.filter (fun value => value == target) = [target] := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.nodup_cons] at nodup
      by_cases equal : head = target
      · subst head
        have tailFilter :
            tail.filter (fun value => value == target) = [] := by
          rw [List.filter_eq_nil_iff]
          intro value valueMember
          simp only [Bool.not_eq_true, beq_eq_false_iff_ne]
          intro valueEqual
          exact nodup.1 (valueEqual ▸ valueMember)
        simp [tailFilter]
      · have targetTail : target ∈ tail := by
          rcases List.mem_cons.mp member with headEqual | tailMember
          · exact (equal headEqual.symm).elim
          · exact tailMember
        have headFalse : (head == target) = false :=
          beq_eq_false_iff_ne.mpr equal
        simp [headFalse, inductionHypothesis nodup.2 targetTail]

private theorem filter_eq_singleton_of_map_nodup_mem
    {alpha beta : Type} [BEq beta] [LawfulBEq beta]
    (key : alpha → beta) :
    (values : List alpha) → (target : alpha) →
      (values.map key).Nodup → target ∈ values →
      values.filter (fun value => key value == key target) = [target]
  | [], _, _, member => by simp at member
  | head :: tail, target, nodup, member => by
      simp only [List.map_cons, List.nodup_cons] at nodup
      by_cases elementEqual : head = target
      · subst target
        have tailFilter :
            tail.filter (fun value => key value == key head) = [] := by
          rw [List.filter_eq_nil_iff]
          intro value valueMember
          simp only [Bool.not_eq_true, beq_eq_false_iff_ne]
          intro equal
          apply nodup.1
          rw [← equal]
          exact List.mem_map_of_mem valueMember
        simp [tailFilter]
      · have headKeyNe : key head ≠ key target := by
          intro equal
          apply nodup.1
          rw [equal]
          exact List.mem_map_of_mem (by
            rcases List.mem_cons.mp member with headMember | tailMember
            · exact (elementEqual headMember.symm).elim
            · exact tailMember)
        have targetTail : target ∈ tail := by
          rcases List.mem_cons.mp member with headMember | tailMember
          · exact (elementEqual headMember.symm).elim
          · exact tailMember
        have headFalse : (key head == key target) = false :=
          beq_eq_false_iff_ne.mpr headKeyNe
        simp [headFalse,
          filter_eq_singleton_of_map_nodup_mem key tail target nodup.2
            targetTail]

private theorem lookupJudgment?_eq_some_of_signatureValid
    (definition : CalculusLanguageDef)
    (signatureValid : definition.judgmentSignatureValid = true)
    {declaration : JudgmentDecl}
    (member : declaration ∈ definition.judgments) :
    definition.lookupJudgment? declaration.head declaration.arity =
      some declaration := by
  simp only [CalculusLanguageDef.judgmentSignatureValid, Bool.and_eq_true,
    beq_iff_eq] at signatureValid
  have headsNodup : (definition.judgmentHeads).Nodup := by
    exact nodup_of_eraseDups_length_eq _ signatureValid.1.2
  have headFilter :
      definition.judgments.filter
          (fun candidate => candidate.head == declaration.head) =
        [declaration] := by
    exact filter_eq_singleton_of_map_nodup_mem JudgmentDecl.head
      definition.judgments declaration headsNodup member
  have combinedFilter :
      definition.judgments.filter (fun candidate =>
          candidate.head == declaration.head &&
            candidate.arity == declaration.arity) = [declaration] := by
    have filterFactorization :
        definition.judgments.filter (fun candidate =>
            candidate.head == declaration.head &&
              candidate.arity == declaration.arity) =
          (definition.judgments.filter (fun candidate =>
              candidate.head == declaration.head)).filter
            (fun candidate => candidate.arity == declaration.arity) := by
      symm
      rw [List.filter_filter]
      simp [Bool.and_comm]
    rw [filterFactorization, headFilter]
    simp
  unfold CalculusLanguageDef.lookupJudgment?
  rw [combinedFilter]

private theorem languageWithSourceVocabulary_has_source_constructor
    {heads : List String} (valid : sourceVocabularyValid heads = true)
    {head : String} (member : head ∈ heads) :
    languageHasConstructorArity
        (languageWithSourceVocabulary heads) head 0 = true := by
  have baseTermsAbsent :
      dataLanguage.terms.filter
          (fun declaration => declaration.label == head) = [] := by
    rw [List.filter_eq_nil_iff]
    intro declaration declarationMember
    simp only [Bool.not_eq_true, beq_eq_false_iff_ne]
    intro labelEqual
    have labelReserved : declaration.label ∈ reservedDataHeads := by
      have mapped :=
        List.mem_map_of_mem (f := GrammarRule.label) declarationMember
      simpa [dataLanguage, reservedDataHeads, dataConstructor] using mapped
    exact sourceVocabularyValid_ne_reserved valid member
      (by
        simp [reservedProjectionHeads, reservedInternalHeads, labelReserved])
      labelEqual.symm
  have sourceTermsSingleton :
      (heads.map nullaryDataConstructor).filter
          (fun declaration => declaration.label == head) =
        [nullaryDataConstructor head] := by
    rw [List.filter_map]
    simpa [Function.comp_def, nullaryDataConstructor, dataConstructor] using
      congrArg (List.map nullaryDataConstructor)
        (filter_eq_singleton_of_nodup_mem
          (sourceVocabularyValid_nodup valid) member)
  unfold languageHasConstructorArity
  rw [show (languageWithSourceVocabulary heads).terms =
      dataLanguage.terms ++ heads.map nullaryDataConstructor by rfl]
  rw [List.filter_append, baseTermsAbsent, sourceTermsSingleton]
  simp [nullaryDataConstructor, dataConstructor]

private theorem languageWithSourceVocabulary_preserves_constructor
    {heads : List String} {head : String} (absent : head ∉ heads)
    (arity : Nat) :
    languageHasConstructorArity
        (languageWithSourceVocabulary heads) head arity =
      languageHasConstructorArity dataLanguage head arity := by
  have sourceTermsAbsent :
      (heads.map nullaryDataConstructor).filter
          (fun declaration => declaration.label == head) = [] := by
    rw [List.filter_eq_nil_iff]
    intro declaration declarationMember
    rcases List.mem_map.mp declarationMember with
      ⟨sourceHead, sourceHeadMember, rfl⟩
    simp only [Bool.not_eq_true, nullaryDataConstructor, dataConstructor,
      beq_eq_false_iff_ne]
    intro equal
    exact absent (equal ▸ sourceHeadMember)
  unfold languageHasConstructorArity
  rw [show (languageWithSourceVocabulary heads).terms =
      dataLanguage.terms ++ heads.map nullaryDataConstructor by rfl]
  rw [List.filter_append, sourceTermsAbsent, List.append_nil]

private theorem languageWithSourceVocabulary_preserves_reserved_constructor
    {heads : List String} (valid : sourceVocabularyValid heads = true)
    {head : String} (reserved : head ∈ reservedProjectionHeads)
    (arity : Nat) :
    languageHasConstructorArity
        (languageWithSourceVocabulary heads) head arity =
      languageHasConstructorArity dataLanguage head arity :=
  languageWithSourceVocabulary_preserves_constructor
    (sourceVocabularyValid_not_mem_reserved valid reserved) arity

private theorem dataLanguage_constructor_head_reserved
    {head : String} {arity : Nat}
    (accepted : languageHasConstructorArity dataLanguage head arity = true) :
    head ∈ reservedProjectionHeads := by
  unfold languageHasConstructorArity at accepted
  generalize filteredEquation :
      dataLanguage.terms.filter
        (fun declaration => declaration.label == head) = filtered
      at accepted
  cases filtered with
  | nil => simp at accepted
  | cons declaration rest =>
      cases rest with
      | nil =>
          have declarationMember : declaration ∈ dataLanguage.terms := by
            have : declaration ∈
                dataLanguage.terms.filter
                  (fun candidate => candidate.label == head) := by
              rw [filteredEquation]
              simp
            exact (List.mem_filter.mp this).1
          have declarationHead : declaration.label = head := by
            have : declaration ∈
                dataLanguage.terms.filter
                  (fun candidate => candidate.label == head) := by
              rw [filteredEquation]
              simp
            exact beq_iff_eq.mp (List.mem_filter.mp this).2
          have mapped :=
            List.mem_map_of_mem (f := GrammarRule.label) declarationMember
          have reservedData : declaration.label ∈ reservedDataHeads := by
            simpa [dataLanguage, reservedDataHeads, dataConstructor] using mapped
          subst head
          simp [reservedProjectionHeads, reservedInternalHeads, reservedData]
      | cons second tail => simp at accepted

private theorem languageWithSourceVocabulary_preserves_accepted_constructor
    {heads : List String} (valid : sourceVocabularyValid heads = true)
    {head : String} {arity : Nat}
    (accepted : languageHasConstructorArity dataLanguage head arity = true) :
    languageHasConstructorArity
        (languageWithSourceVocabulary heads) head arity = true := by
  rw [languageWithSourceVocabulary_preserves_reserved_constructor valid
    (dataLanguage_constructor_head_reserved accepted)]
  exact accepted

mutual
private theorem fixedConstructorsValid_mono
    (base target : LanguageDef)
    (preserve : ∀ head arity,
      languageHasConstructorArity base head arity = true →
        languageHasConstructorArity target head arity = true) :
    (pattern : Pattern) →
      fixedConstructorsValid base pattern = true →
        fixedConstructorsValid target pattern = true
  | .bvar index, _ => by simp [fixedConstructorsValid]
  | .fvar name, _ => by simp [fixedConstructorsValid]
  | .apply head arguments, valid => by
      simp only [fixedConstructorsValid, Bool.and_eq_true] at valid ⊢
      exact
        ⟨preserve head arguments.length valid.1,
          fixedConstructorListsValid_mono base target preserve arguments
            valid.2⟩
  | .lambda binder body, valid => by
      simp only [fixedConstructorsValid] at valid ⊢
      exact fixedConstructorsValid_mono base target preserve body valid
  | .multiLambda arity binders body, valid => by
      simp only [fixedConstructorsValid] at valid ⊢
      exact fixedConstructorsValid_mono base target preserve body valid
  | .subst body replacement, valid => by
      simp only [fixedConstructorsValid, Bool.and_eq_true] at valid ⊢
      exact
        ⟨fixedConstructorsValid_mono base target preserve body valid.1,
          fixedConstructorsValid_mono base target preserve replacement
            valid.2⟩
  | .collection kind elements rest, valid => by
      simp only [fixedConstructorsValid] at valid ⊢
      exact fixedConstructorListsValid_mono base target preserve elements valid
termination_by pattern => sizeOf pattern

private theorem fixedConstructorListsValid_mono
    (base target : LanguageDef)
    (preserve : ∀ head arity,
      languageHasConstructorArity base head arity = true →
        languageHasConstructorArity target head arity = true) :
    (patterns : List Pattern) →
      fixedConstructorListsValid base patterns = true →
        fixedConstructorListsValid target patterns = true
  | [], _ => by simp [fixedConstructorListsValid]
  | pattern :: patterns, valid => by
      simp only [fixedConstructorListsValid, Bool.and_eq_true] at valid ⊢
      exact
        ⟨fixedConstructorsValid_mono base target preserve pattern valid.1,
          fixedConstructorListsValid_mono base target preserve patterns
            valid.2⟩
termination_by patterns => sizeOf patterns
end

private theorem sideDefinition_lookup_proves_none (arity : Nat) :
    sideDefinition.lookupJudgment? provesHead arity = none := by
  simp [CalculusLanguageDef.lookupJudgment?, judgmentDecls,
    provesHead, appendHead, lookupHead, substBodyHead, applySubstHead,
    varsHead, memberHead, dvRelHead, allWithHead, allPairsHead,
    dvListsHead, dvOKHead]

private theorem sourceInferenceLanguageDef_preserves_side_lookup
    (heads : List String) (sourceRules : List SourceRuleSchema)
    {head : String} {arity : Nat} {declaration : JudgmentDecl}
    (lookup :
      sideDefinition.lookupJudgment? head arity = some declaration) :
    (sourceInferenceLanguageDef heads sourceRules).lookupJudgment?
        head arity = some declaration := by
  have headNe : head ≠ provesHead := by
    intro equal
    subst head
    rw [sideDefinition_lookup_proves_none] at lookup
    contradiction
  unfold CalculusLanguageDef.lookupJudgment? at lookup ⊢
  change
    (match (judgmentDecls ++ [provesDecl]).filter (fun candidate =>
        candidate.head == head && candidate.arity == arity) with
    | [candidate] => some candidate
    | _ => none) = some declaration
  rw [List.filter_append]
  have extraAbsent :
      [provesDecl].filter (fun candidate =>
          candidate.head == head && candidate.arity == arity) = [] := by
    simp [provesDecl, Ne.symm headNe]
  rw [extraAbsent, List.append_nil]
  exact lookup

private theorem sideJudgmentSchemaValid_in_sourceInferenceLanguageDef
    (heads : List String) (sourceRules : List SourceRuleSchema)
    (vocabularyValid : sourceVocabularyValid heads = true)
    (pattern : Pattern)
    (valid : sideDefinition.judgmentSchemaValid pattern = true) :
    (sourceInferenceLanguageDef heads sourceRules).judgmentSchemaValid
        pattern = true := by
  cases pattern with
  | bvar index => simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | fvar name => simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | lambda binder body =>
      simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | multiLambda arity binders body =>
      simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | subst body replacement =>
      simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | collection kind elements rest =>
      simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | apply head arguments =>
      simp only [CalculusLanguageDef.judgmentSchemaValid, Bool.and_eq_true]
        at valid ⊢
      cases lookupEquation :
          sideDefinition.lookupJudgment? head arguments.length with
      | none => simp [lookupEquation] at valid
      | some declaration =>
          refine ⟨?_, ?_⟩
          · rw [sourceInferenceLanguageDef_preserves_side_lookup
              heads sourceRules lookupEquation]
            rfl
          · have baseFixed := valid.2
            exact fixedConstructorListsValid_mono sideDefinition.toLanguageDef
              (sourceInferenceLanguageDef heads sourceRules).toLanguageDef
              (fun constructorHead constructorArity accepted => by
                have acceptedData :
                    languageHasConstructorArity dataLanguage constructorHead
                      constructorArity = true := by
                  unfold languageHasConstructorArity at accepted ⊢
                  exact accepted
                have extendedAccepted :=
                  languageWithSourceVocabulary_preserves_accepted_constructor
                    vocabularyValid acceptedData
                unfold languageHasConstructorArity at extendedAccepted ⊢
                exact extendedAccepted)
              arguments baseFixed

private theorem sourceInferenceLanguageDef_has_source_constructor
    {heads : List String} (sourceRules : List SourceRuleSchema)
    (vocabularyValid : sourceVocabularyValid heads = true)
    {head : String} (member : head ∈ heads) :
    languageHasConstructorArity
        (sourceInferenceLanguageDef heads sourceRules).toLanguageDef head 0 = true := by
  have accepted := languageWithSourceVocabulary_has_source_constructor
    vocabularyValid member
  unfold languageHasConstructorArity at accepted ⊢
  exact accepted

private theorem sourceInferenceLanguageDef_preserves_accepted_constructor
    {heads : List String} (sourceRules : List SourceRuleSchema)
    (vocabularyValid : sourceVocabularyValid heads = true)
    {head : String} {arity : Nat}
    (accepted : languageHasConstructorArity dataLanguage head arity = true) :
    languageHasConstructorArity
        (sourceInferenceLanguageDef heads sourceRules).toLanguageDef
        head arity = true := by
  have extended :=
    languageWithSourceVocabulary_preserves_accepted_constructor
      vocabularyValid accepted
  unfold languageHasConstructorArity at extended ⊢
  exact extended

private theorem fixedConstructorListsValid_of_forall
    (language : LanguageDef) :
    (patterns : List Pattern) →
      (∀ pattern ∈ patterns,
        fixedConstructorsValid language pattern = true) →
      fixedConstructorListsValid language patterns = true
  | [], _ => by simp [fixedConstructorListsValid]
  | pattern :: patterns, valid => by
      simp only [fixedConstructorListsValid, Bool.and_eq_true]
      exact
        ⟨valid pattern (by simp),
          fixedConstructorListsValid_of_forall language patterns (by
            intro tail tailMember
            exact valid tail (by simp [tailMember]))⟩

private theorem fixedConstructorsValid_apply_of
    (language : LanguageDef) (head : String) {arguments : List Pattern}
    (headValid :
      languageHasConstructorArity language head arguments.length = true)
    (argumentsValid : ∀ argument ∈ arguments,
      fixedConstructorsValid language argument = true) :
    fixedConstructorsValid language (.apply head arguments) = true := by
  simp only [fixedConstructorsValid, Bool.and_eq_true]
  exact
    ⟨headValid,
      fixedConstructorListsValid_of_forall language arguments argumentsValid⟩

private theorem sideRules_isValidIn_sourceInferenceLanguageDef
    (heads : List String) (sourceRules : List SourceRuleSchema)
    (vocabularyValid : sourceVocabularyValid heads = true) :
    sideRules.all
      (RuleSchema.isValidIn
        (sourceInferenceLanguageDef heads sourceRules)) = true := by
  have sideValid := sideDefinition_valid
  simp only [CalculusLanguageDef.isValid, Bool.and_eq_true] at sideValid
  have sideRulesValid :
      sideRules.all (RuleSchema.isValidIn sideDefinition) = true :=
    sideValid.1.2
  apply List.all_eq_true.mpr
  intro rule ruleMember
  have baseRuleValid :=
    List.all_eq_true.mp sideRulesValid rule ruleMember
  simp only [RuleSchema.isValidIn, Bool.and_eq_true] at baseRuleValid ⊢
  refine ⟨baseRuleValid.1, ?_, baseRuleValid.2.2⟩
  apply List.all_eq_true.mpr
  intro pattern patternMember
  exact sideJudgmentSchemaValid_in_sourceInferenceLanguageDef
    heads sourceRules vocabularyValid pattern
      (List.all_eq_true.mp baseRuleValid.2.1 pattern patternMember)

/-! ## Rule-identifier separation -/

private theorem sourcePrefixRuleLabels_valid
    {source : SourcePrefix} (valid : sourcePrefixValid source = true) :
    sourceRuleLabelsValid (sourcePrefixRuleLabels source) = true := by
  simp only [sourcePrefixValid, Bool.and_eq_true] at valid
  exact valid.2

private theorem sourcePrefixRuleLabels_nodup
    {source : SourcePrefix} (valid : sourcePrefixValid source = true) :
    (sourcePrefixRuleLabels source).Nodup := by
  have labelsValid := sourcePrefixRuleLabels_valid valid
  simp only [sourceRuleLabelsValid, Bool.and_eq_true, beq_iff_eq] at labelsValid
  exact nodup_of_eraseDups_length_eq _ labelsValid.2

private theorem sourceGeneratedRuleIds_nodup
    {source : SourcePrefix} (valid : sourcePrefixValid source = true) :
    ((sourceGeneratedRules source).map RuleSchema.id).Nodup := by
  apply List.Nodup.of_map RuleId.value
  rw [List.map_map]
  change ((sourceGeneratedRules source).map (fun rule => rule.id.value)).Nodup
  rw [sourceGeneratedRuleIdValues]
  exact sourcePrefixRuleLabels_nodup valid

private theorem sideRuleIds_nodup :
    (sideRules.map RuleSchema.id).Nodup := by
  decide

private theorem sourceGeneratedRuleId_not_startsWith_reservedRulePrefix
    {source : SourcePrefix}
    (disjoint :
      sourceRuleIdsDisjoint
        ((sourceGeneratedRules source).map RuleSchema.id) = true)
    {id : RuleId}
    (member : id ∈ (sourceGeneratedRules source).map RuleSchema.id) :
    (!id.value.startsWith reservedRulePrefix) = true := by
  exact List.all_eq_true.mp disjoint id member

private theorem combinedRuleIds_nodup
    {source : SourcePrefix} (prefixValid : sourcePrefixValid source = true)
    (disjoint :
      sourceRuleIdsDisjoint
        ((sourceGeneratedRules source).map RuleSchema.id) = true) :
    ((sideRules ++ sourceGeneratedRules source).map RuleSchema.id).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨sideRuleIds_nodup, sourceGeneratedRuleIds_nodup prefixValid, ?_⟩
  intro sideId sideMember sourceId sourceMember equal
  subst sourceId
  have begins := sideRuleId_startsWith_reservedRulePrefix sideMember
  have doesNotBegin :=
    sourceGeneratedRuleId_not_startsWith_reservedRulePrefix disjoint sourceMember
  change (!sideId.value.startsWith "$mm.") = true at doesNotBegin
  rw [begins] at doesNotBegin
  contradiction

private theorem combinedRuleIds_eraseDups_length
    {source : SourcePrefix} (prefixValid : sourcePrefixValid source = true)
    (disjoint :
      sourceRuleIdsDisjoint
        ((sourceGeneratedRules source).map RuleSchema.id) = true) :
    (((sideRules ++ sourceGeneratedRules source).map RuleSchema.id).eraseDups).length =
      ((sideRules ++ sourceGeneratedRules source).map RuleSchema.id).length := by
  rw [eraseDups_eq_self_of_nodup _
    (combinedRuleIds_nodup prefixValid disjoint)]

/-! ## Generated metavariable names -/

private theorem hypothesisBodyFormalName_injective :
    Function.Injective hypothesisBodyFormalName := by
  intro left right equal
  apply Nat.repr_injective
  simpa [hypothesisBodyFormalName, Nat.toString_eq_repr] using equal

private theorem hypothesisBodyFormalName_ne_conclusionBodyFormalName
    (index : Nat) :
    hypothesisBodyFormalName index != conclusionBodyFormalName := by
  apply bne_iff_ne.mpr
  change ("H" ++ toString index ++ "Body" : String) ≠ "ConclusionBody"
  intro equal
  have firstCharacter :=
    congrArg (fun value : String => value.toList.head?) equal
  simp at firstCharacter

private theorem hypothesisBodyFormalName_ne_empty (index : Nat) :
    hypothesisBodyFormalName index != "" := by
  apply bne_iff_ne.mpr
  change ("H" ++ toString index ++ "Body" : String) ≠ ""
  simp

private theorem assertionHypothesisFormalNames_eq_range
    (index : Nat) (hypotheses : List HypothesisView) :
    (assertionHypothesisFormalsFrom index hypotheses).map Prod.fst =
      (List.range' index hypotheses.length).map
        hypothesisBodyFormalName := by
  induction hypotheses generalizing index with
  | nil => rfl
  | cons hypothesis hypotheses inductionHypothesis =>
      rw [show assertionHypothesisFormalsFrom index
            (hypothesis :: hypotheses) =
          (hypothesisBodyFormalName index, 0) ::
            assertionHypothesisFormalsFrom (index + 1) hypotheses by rfl]
      simp [List.range', inductionHypothesis]

private theorem assertionHypothesisFormalNames_nodup
    (index : Nat) (hypotheses : List HypothesisView) :
    ((assertionHypothesisFormalsFrom index hypotheses).map Prod.fst).Nodup := by
  rw [assertionHypothesisFormalNames_eq_range]
  exact List.Nodup.map hypothesisBodyFormalName_injective List.nodup_range'

private theorem assertionRuleFormalNames_nodup
    (callerFrame : RuntimeFrame) (assertion : AssertionView) :
    ((assertionRule callerFrame assertion).metavariables.map Prod.fst).Nodup := by
  rw [show (assertionRule callerFrame assertion).metavariables =
      assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
        [(conclusionBodyFormalName, 0)] by rfl]
  simp only [List.map_append, List.map_singleton, List.nodup_append,
    List.nodup_singleton, true_and]
  refine ⟨assertionHypothesisFormalNames_nodup 0 assertion.hypotheses, ?_⟩
  intro name nameMember conclusion conclusionMember
  simp only [List.mem_singleton] at conclusionMember
  subst conclusion
  rw [assertionHypothesisFormalNames_eq_range] at nameMember
  rcases List.mem_map.mp nameMember with ⟨index, _, rfl⟩
  exact (bne_iff_ne.mp
    (hypothesisBodyFormalName_ne_conclusionBodyFormalName index))

private theorem assertionRuleFormalNames_nonempty
    (callerFrame : RuntimeFrame) (assertion : AssertionView) :
    (RuleSchema.metavariableNames (assertionRule callerFrame assertion)).all
      (fun name => name != "") = true := by
  unfold RuleSchema.metavariableNames
  rw [show (assertionRule callerFrame assertion).metavariables =
      assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
        [(conclusionBodyFormalName, 0)] by rfl]
  simp only [List.map_append, List.map_singleton, List.all_append,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, by decide⟩
  rw [assertionHypothesisFormalNames_eq_range]
  apply List.all_eq_true.mpr
  intro name nameMember
  rcases List.mem_map.mp nameMember with ⟨index, _, rfl⟩
  exact hypothesisBodyFormalName_ne_empty index

/-! ## Structural validity of generated data patterns -/

private def SchemaGroundAt (depth : Nat) (pattern : Pattern) : Prop :=
  patternMetavariableOccurrencesAt depth pattern = [] ∧
    Pattern.isWellScopedAt depth pattern = true ∧
    patternHasNoCollectionRest pattern = true ∧
    pattern.hasCanonicalBinderMetadata = true

private def SchemaGroundListAt
    (depth : Nat) (patterns : List Pattern) : Prop :=
  patternsMetavariableOccurrencesAt depth patterns = [] ∧
    Pattern.isWellScopedListAt depth patterns = true ∧
    patternsHaveNoCollectionRest patterns = true ∧
    Pattern.hasCanonicalBinderMetadataList patterns = true

private theorem schemaGroundListAt_nil (depth : Nat) :
    SchemaGroundListAt depth [] := by
  simp [SchemaGroundListAt, patternsMetavariableOccurrencesAt,
    Pattern.isWellScopedListAt, patternsHaveNoCollectionRest,
    Pattern.hasCanonicalBinderMetadataList]

private theorem schemaGroundListAt_cons
    {depth : Nat} {pattern : Pattern} {patterns : List Pattern}
    (headGround : SchemaGroundAt depth pattern)
    (tailGround : SchemaGroundListAt depth patterns) :
    SchemaGroundListAt depth (pattern :: patterns) := by
  rcases headGround with ⟨headOccurrences, headScoped, headNoRest,
    headCanonical⟩
  rcases tailGround with ⟨tailOccurrences, tailScoped, tailNoRest,
    tailCanonical⟩
  simp [SchemaGroundListAt, patternsMetavariableOccurrencesAt,
    Pattern.isWellScopedListAt, patternsHaveNoCollectionRest,
    Pattern.hasCanonicalBinderMetadataList, headOccurrences,
    tailOccurrences, headScoped, tailScoped, headNoRest, tailNoRest,
    headCanonical, tailCanonical]

private theorem schemaGroundAt_apply
    {depth : Nat} (head : String) {arguments : List Pattern}
    (argumentsGround : SchemaGroundListAt depth arguments) :
    SchemaGroundAt depth (.apply head arguments) := by
  simpa [SchemaGroundAt, SchemaGroundListAt,
    patternMetavariableOccurrencesAt, Pattern.isWellScopedAt,
    patternHasNoCollectionRest, Pattern.hasCanonicalBinderMetadata]
    using argumentsGround

private theorem schemaGroundAt_fvar_declared
    (depth : Nat) (name : String) :
    patternMetavariableOccurrencesAt depth (.fvar name) = [(name, depth)] ∧
      Pattern.isWellScopedAt depth (.fvar name) = true ∧
      patternHasNoCollectionRest (.fvar name) = true ∧
      Pattern.hasCanonicalBinderMetadata (.fvar name) = true := by
  simp [patternMetavariableOccurrencesAt, Pattern.isWellScopedAt,
    patternHasNoCollectionRest, Pattern.hasCanonicalBinderMetadata]

private theorem schemaGroundAt_encodeString (depth : Nat) (value : String) :
    SchemaGroundAt depth (encodeString value) := by
  apply schemaGroundAt_apply
  apply schemaGroundListAt_cons
  · exact schemaGroundAt_apply value (schemaGroundListAt_nil depth)
  · exact schemaGroundListAt_nil depth

private theorem schemaGroundAt_encodeListWith
    {alpha : Type} (depth : Nat) (encode : alpha → Pattern)
    (elementGround : ∀ value, SchemaGroundAt depth (encode value)) :
    ∀ values, SchemaGroundAt depth (encodeListWith encode values)
  | [] => schemaGroundAt_apply nilHead (schemaGroundListAt_nil depth)
  | value :: values =>
      schemaGroundAt_apply consHead
        (schemaGroundListAt_cons (elementGround value)
          (schemaGroundListAt_cons
            (schemaGroundAt_encodeListWith depth encode elementGround values)
            (schemaGroundListAt_nil depth)))

private theorem schemaGroundAt_encodeSym (depth : Nat) (symbol : RuntimeSym) :
    SchemaGroundAt depth (encodeSym symbol) := by
  cases symbol with
  | const name | var name =>
      apply schemaGroundAt_apply
      exact schemaGroundListAt_cons (schemaGroundAt_encodeString depth name)
        (schemaGroundListAt_nil depth)

private theorem schemaGroundAt_encodeFormula
    (depth : Nat) (formula : ConstantHeadedFormula) :
    SchemaGroundAt depth (encodeFormula formula) := by
  apply schemaGroundAt_apply
  exact schemaGroundListAt_cons
    (schemaGroundAt_encodeString depth formula.typecode)
    (schemaGroundListAt_cons
      (schemaGroundAt_encodeListWith depth encodeSym
        (schemaGroundAt_encodeSym depth) formula.body)
      (schemaGroundListAt_nil depth))

private theorem schemaGroundAt_encodeDVPair
    (depth : Nat) (pair : String × String) :
    SchemaGroundAt depth (encodeDVPair pair) := by
  apply schemaGroundAt_apply
  exact schemaGroundListAt_cons
    (schemaGroundAt_encodeString depth pair.1)
    (schemaGroundListAt_cons (schemaGroundAt_encodeString depth pair.2)
      (schemaGroundListAt_nil depth))

private theorem schemaGroundAt_encodeSourceFrame
    (depth : Nat) (frame : SourceFrame) :
    SchemaGroundAt depth (encodeSourceFrame frame) := by
  apply schemaGroundAt_apply
  exact schemaGroundListAt_cons
    (schemaGroundAt_encodeListWith depth encodeDVPair
      (schemaGroundAt_encodeDVPair depth) frame.distinctVariables)
    (schemaGroundListAt_cons
      (schemaGroundAt_encodeListWith depth encodeString
        (schemaGroundAt_encodeString depth) frame.hypothesisLabels)
      (schemaGroundListAt_nil depth))

private def SchemaAllowedAt
    (formals : List (String × Nat)) (depth : Nat)
    (pattern : Pattern) : Prop :=
  (patternMetavariableOccurrencesAt depth pattern).all
      (fun occurrence => formals.contains occurrence) = true ∧
    Pattern.isWellScopedAt depth pattern = true ∧
    patternHasNoCollectionRest pattern = true ∧
    pattern.hasCanonicalBinderMetadata = true

private theorem schemaAllowedAt_of_ground
    {formals : List (String × Nat)} {depth : Nat} {pattern : Pattern}
    (ground : SchemaGroundAt depth pattern) :
    SchemaAllowedAt formals depth pattern := by
  rcases ground with ⟨occurrences, wellScoped, noRest, canonical⟩
  simp [SchemaAllowedAt, occurrences, wellScoped, noRest, canonical]

private theorem schemaAllowedAt_fvar
    {formals : List (String × Nat)} {depth : Nat} {name : String}
    (declared : (name, depth) ∈ formals) :
    SchemaAllowedAt formals depth (.fvar name) := by
  simp [SchemaAllowedAt, patternMetavariableOccurrencesAt,
    Pattern.isWellScopedAt, patternHasNoCollectionRest,
    Pattern.hasCanonicalBinderMetadata, declared]

private theorem schemaAllowedPatterns_sound
    {formals : List (String × Nat)} {depth : Nat}
    (patterns : List Pattern)
    (allowed : ∀ pattern ∈ patterns,
      SchemaAllowedAt formals depth pattern) :
    (patternsMetavariableOccurrencesAt depth patterns).all
        (fun occurrence => formals.contains occurrence) = true ∧
      Pattern.isWellScopedListAt depth patterns = true ∧
      patternsHaveNoCollectionRest patterns = true ∧
      Pattern.hasCanonicalBinderMetadataList patterns = true := by
  induction patterns with
  | nil =>
      simp [patternsMetavariableOccurrencesAt,
        Pattern.isWellScopedListAt,
        patternsHaveNoCollectionRest,
        Pattern.hasCanonicalBinderMetadataList]
  | cons pattern patterns inductionHypothesis =>
      have headAllowed := allowed pattern (by simp)
      have tailAllowed := inductionHypothesis (by
        intro tail tailMember
        exact allowed tail (by simp [tailMember]))
      rcases headAllowed with
        ⟨headOccurrences, headScoped, headNoRest, headCanonical⟩
      rcases tailAllowed with
        ⟨tailOccurrences, tailScoped, tailNoRest, tailCanonical⟩
      simp only [patternsMetavariableOccurrencesAt, List.all_append,
        Pattern.isWellScopedListAt, patternsHaveNoCollectionRest,
        Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
      exact
        ⟨⟨headOccurrences, tailOccurrences⟩,
          ⟨headScoped, tailScoped⟩,
          ⟨headNoRest, tailNoRest⟩,
          ⟨headCanonical, tailCanonical⟩⟩

private theorem schemaAllowedAt_apply
    {formals : List (String × Nat)} {depth : Nat}
    (head : String) {arguments : List Pattern}
    (allowed : ∀ argument ∈ arguments,
      SchemaAllowedAt formals depth argument) :
    SchemaAllowedAt formals depth (.apply head arguments) := by
  have argumentsSound := schemaAllowedPatterns_sound arguments allowed
  simpa [SchemaAllowedAt, patternMetavariableOccurrencesAt,
    Pattern.isWellScopedAt, patternHasNoCollectionRest,
    Pattern.hasCanonicalBinderMetadata] using argumentsSound

private theorem schemaAllowedAt_unary
    {formals : List (String × Nat)} {depth : Nat}
    (head : String) {argument : Pattern}
    (allowed : SchemaAllowedAt formals depth argument) :
    SchemaAllowedAt formals depth (.apply head [argument]) := by
  apply schemaAllowedAt_apply
  intro candidate member
  simp only [List.mem_singleton] at member
  subst candidate
  exact allowed

private theorem schemaAllowedAt_binary
    {formals : List (String × Nat)} {depth : Nat}
    (head : String) {left right : Pattern}
    (leftAllowed : SchemaAllowedAt formals depth left)
    (rightAllowed : SchemaAllowedAt formals depth right) :
    SchemaAllowedAt formals depth (.apply head [left, right]) := by
  apply schemaAllowedAt_apply
  intro candidate member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact leftAllowed
  · exact rightAllowed

private theorem schemaAllowedAt_ternary
    {formals : List (String × Nat)} {depth : Nat}
    (head : String) {first second third : Pattern}
    (firstAllowed : SchemaAllowedAt formals depth first)
    (secondAllowed : SchemaAllowedAt formals depth second)
    (thirdAllowed : SchemaAllowedAt formals depth third) :
    SchemaAllowedAt formals depth (.apply head [first, second, third]) := by
  apply schemaAllowedAt_apply
  intro candidate member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact firstAllowed
  · exact secondAllowed
  · exact thirdAllowed

private theorem schemaAllowedAt_mono
    {smaller larger : List (String × Nat)} {depth : Nat} {pattern : Pattern}
    (inclusion : ∀ formal ∈ smaller, formal ∈ larger)
    (allowed : SchemaAllowedAt smaller depth pattern) :
    SchemaAllowedAt larger depth pattern := by
  rcases allowed with ⟨occurrences, wellScoped, noRest, canonical⟩
  refine ⟨?_, wellScoped, noRest, canonical⟩
  apply List.all_eq_true.mpr
  intro occurrence occurrenceMember
  have inSmaller : occurrence ∈ smaller := by
    have := List.all_eq_true.mp occurrences occurrence occurrenceMember
    simpa [List.contains_iff_mem] using this
  exact List.contains_iff_mem.mpr (inclusion occurrence inSmaller)

private theorem schemaAllowedAt_encodeListWith
    {alpha : Type} {formals : List (String × Nat)} (depth : Nat)
    (encode : alpha → Pattern)
    (elementAllowed : ∀ value, SchemaAllowedAt formals depth (encode value)) :
    ∀ values, SchemaAllowedAt formals depth (encodeListWith encode values)
  | [] => schemaAllowedAt_of_ground
      (schemaGroundAt_apply nilHead (schemaGroundListAt_nil depth))
  | value :: values =>
      schemaAllowedAt_apply consHead (by
        intro argument argumentMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at argumentMember
        rcases argumentMember with rfl | rfl
        · exact elementAllowed value
        · exact schemaAllowedAt_encodeListWith depth encode elementAllowed values)

private theorem schemaAllowedAt_encodeListWith_of_mem
    {alpha : Type} {formals : List (String × Nat)} (depth : Nat)
    (encode : alpha → Pattern) :
    ∀ values,
      (∀ value ∈ values, SchemaAllowedAt formals depth (encode value)) →
      SchemaAllowedAt formals depth (encodeListWith encode values)
  | [], _ => schemaAllowedAt_of_ground
      (schemaGroundAt_apply nilHead (schemaGroundListAt_nil depth))
  | value :: values, allowed =>
      schemaAllowedAt_apply consHead (by
        intro argument argumentMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at argumentMember
        rcases argumentMember with rfl | rfl
        · exact allowed value (by simp)
        · exact schemaAllowedAt_encodeListWith_of_mem depth encode values (by
            intro tail tailMember
            exact allowed tail (by simp [tailMember])))

private theorem assertionHypothesisProvesFrom_allowed
    {formals : List (String × Nat)}
    (index : Nat) (hypotheses : List HypothesisView)
    (formalsContain : ∀ formal ∈
      assertionHypothesisFormalsFrom index hypotheses, formal ∈ formals) :
    ∀ pattern ∈ assertionHypothesisProvesFrom index hypotheses,
      SchemaAllowedAt formals 0 pattern := by
  induction hypotheses generalizing index with
  | nil => simp
  | cons hypothesis hypotheses inductionHypothesis =>
      intro pattern patternMember
      simp only [assertionHypothesisProvesFrom_cons, List.mem_cons]
        at patternMember
      rcases patternMember with rfl | tailMember
      · apply schemaAllowedAt_unary provesHead
        apply schemaAllowedAt_binary formulaHead
        · exact schemaAllowedAt_of_ground
            (schemaGroundAt_encodeString 0 hypothesis.typecode)
        · apply schemaAllowedAt_fvar
          apply formalsContain
          rw [assertionHypothesisFormalsFrom_cons]
          exact List.mem_cons_self
      · apply inductionHypothesis (index := index + 1)
        · intro formal formalMember
          apply formalsContain
          rw [assertionHypothesisFormalsFrom_cons]
          exact List.mem_cons_of_mem _ formalMember
        · exact tailMember

private theorem assertionBindingsFrom_allowed
    {formals : List (String × Nat)}
    (index : Nat) (hypotheses : List HypothesisView)
    (formalsContain : ∀ formal ∈
      assertionHypothesisFormalsFrom index hypotheses, formal ∈ formals) :
    ∀ pattern ∈ assertionBindingsFrom index hypotheses,
      SchemaAllowedAt formals 0 pattern := by
  induction hypotheses generalizing index with
  | nil => simp
  | cons hypothesis hypotheses inductionHypothesis =>
      cases hypothesis with
      | floating label typecode variableName =>
          intro pattern patternMember
          simp only [assertionBindingsFrom_floating, List.mem_cons]
            at patternMember
          rcases patternMember with rfl | tailMember
          · apply schemaAllowedAt_binary bindingHead
            · exact schemaAllowedAt_of_ground
                (schemaGroundAt_encodeString 0 variableName)
            · apply schemaAllowedAt_binary formulaHead
              · exact schemaAllowedAt_of_ground
                  (schemaGroundAt_encodeString 0 typecode)
              · apply schemaAllowedAt_fvar
                apply formalsContain
                rw [assertionHypothesisFormalsFrom_cons]
                exact List.mem_cons_self
          · apply inductionHypothesis (index := index + 1)
            · intro formal formalMember
              apply formalsContain
              rw [assertionHypothesisFormalsFrom_cons]
              exact List.mem_cons_of_mem _ formalMember
            · exact tailMember
      | essential label formula =>
          intro pattern patternMember
          simp only [assertionBindingsFrom_essential] at patternMember
          apply inductionHypothesis (index := index + 1)
          · intro formal formalMember
            apply formalsContain
            rw [assertionHypothesisFormalsFrom_cons]
            exact List.mem_cons_of_mem _ formalMember
          · exact patternMember

private theorem sourceAssertionSubstitution_allowed
    {formals : List (String × Nat)} (assertion : SourceAssertion)
    (formalsContain : ∀ formal ∈
      assertionHypothesisFormalsFrom 0 assertion.hypotheses,
      formal ∈ formals) :
    SchemaAllowedAt formals 0 (sourceAssertionSubstitution assertion) := by
  apply schemaAllowedAt_unary substitutionHead
  apply schemaAllowedAt_encodeListWith_of_mem 0 id
  intro binding bindingMember
  exact assertionBindingsFrom_allowed 0 assertion.hypotheses
    formalsContain binding bindingMember

private theorem assertionEssentialChecksFrom_allowed
    {formals : List (String × Nat)}
    (substitution : Pattern)
    (substitutionAllowed : SchemaAllowedAt formals 0 substitution)
    (index : Nat) (hypotheses : List HypothesisView)
    (formalsContain : ∀ formal ∈
      assertionHypothesisFormalsFrom index hypotheses, formal ∈ formals) :
    ∀ pattern ∈ assertionEssentialChecksFrom substitution index hypotheses,
      SchemaAllowedAt formals 0 pattern := by
  induction hypotheses generalizing index with
  | nil => simp
  | cons hypothesis hypotheses inductionHypothesis =>
      cases hypothesis with
      | floating label typecode variableName =>
          intro pattern patternMember
          simp only [assertionEssentialChecksFrom_floating] at patternMember
          apply inductionHypothesis (index := index + 1)
          · intro formal formalMember
            apply formalsContain
            rw [assertionHypothesisFormalsFrom_cons]
            exact List.mem_cons_of_mem _ formalMember
          · exact patternMember
      | essential label formula =>
          intro pattern patternMember
          simp only [assertionEssentialChecksFrom_essential, List.mem_cons]
            at patternMember
          rcases patternMember with rfl | tailMember
          · apply schemaAllowedAt_ternary applySubstHead
            · exact substitutionAllowed
            · exact schemaAllowedAt_of_ground
                (schemaGroundAt_encodeFormula 0 formula)
            · apply schemaAllowedAt_binary formulaHead
              · exact schemaAllowedAt_of_ground
                  (schemaGroundAt_encodeString 0 formula.typecode)
              · apply schemaAllowedAt_fvar
                apply formalsContain
                rw [assertionHypothesisFormalsFrom_cons]
                exact List.mem_cons_self
          · apply inductionHypothesis (index := index + 1)
            · intro formal formalMember
              apply formalsContain
              rw [assertionHypothesisFormalsFrom_cons]
              exact List.mem_cons_of_mem _ formalMember
            · exact tailMember

private theorem sourceAssertionRule_patterns_allowed
    (callerFrame : SourceFrame) (assertion : SourceAssertion) :
    let formals :=
      assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
        [(conclusionBodyFormalName, 0)]
    ∀ pattern ∈ RuleSchema.patterns
        (sourceAssertionRule callerFrame assertion),
      SchemaAllowedAt formals 0 pattern := by
  let formals :=
    assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
      [(conclusionBodyFormalName, 0)]
  change ∀ pattern ∈ RuleSchema.patterns
      (sourceAssertionRule callerFrame assertion),
    SchemaAllowedAt formals 0 pattern
  have hypothesisFormalsContain : ∀ formal ∈
      assertionHypothesisFormalsFrom 0 assertion.hypotheses,
      formal ∈ formals := by
    intro formal formalMember
    exact List.mem_append_left _ formalMember
  have conclusionFormal : (conclusionBodyFormalName, 0) ∈ formals := by
    exact List.mem_append_right _ (by simp)
  have substitutionAllowed :
      SchemaAllowedAt formals 0 (sourceAssertionSubstitution assertion) :=
    sourceAssertionSubstitution_allowed assertion hypothesisFormalsContain
  have resultFormulaAllowed :
      SchemaAllowedAt formals 0
        (Builder.formula (encodeString assertion.formula.typecode)
          (.fvar conclusionBodyFormalName)) := by
    apply schemaAllowedAt_binary formulaHead
    · exact schemaAllowedAt_of_ground
        (schemaGroundAt_encodeString 0 assertion.formula.typecode)
    · exact schemaAllowedAt_fvar conclusionFormal
  have premisesEquation :
      (sourceAssertionRule callerFrame assertion).premises =
        assertionHypothesisProvesFrom 0 assertion.hypotheses ++
          assertionEssentialChecksFrom
              (sourceAssertionSubstitution assertion) 0 assertion.hypotheses ++
          [ dvOK (sourceAssertionSubstitution assertion)
              (encodeSourceFrame callerFrame)
              (encodeSourceFrame assertion.frame)
          , applySubst (sourceAssertionSubstitution assertion)
              (encodeFormula assertion.formula)
              (Builder.formula (encodeString assertion.formula.typecode)
                (.fvar conclusionBodyFormalName)) ] := by
    rfl
  have conclusionEquation :
      (sourceAssertionRule callerFrame assertion).conclusion =
        proves
          (Builder.formula (encodeString assertion.formula.typecode)
            (.fvar conclusionBodyFormalName)) := by
    rfl
  intro pattern patternMember
  unfold RuleSchema.patterns at patternMember
  rw [premisesEquation, conclusionEquation] at patternMember
  rcases List.mem_append.mp patternMember with premiseMember | conclusionMember
  · rcases List.mem_append.mp premiseMember with generatedMember | terminalMember
    · rcases List.mem_append.mp generatedMember with
        hypothesisMember | essentialMember
      · exact assertionHypothesisProvesFrom_allowed 0 assertion.hypotheses
          hypothesisFormalsContain pattern hypothesisMember
      · exact assertionEssentialChecksFrom_allowed
          (sourceAssertionSubstitution assertion) substitutionAllowed 0
          assertion.hypotheses hypothesisFormalsContain pattern essentialMember
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at terminalMember
      rcases terminalMember with rfl | rfl
      · apply schemaAllowedAt_ternary dvOKHead
        · exact substitutionAllowed
        · exact schemaAllowedAt_of_ground
            (schemaGroundAt_encodeSourceFrame 0 callerFrame)
        · exact schemaAllowedAt_of_ground
            (schemaGroundAt_encodeSourceFrame 0 assertion.frame)
      · apply schemaAllowedAt_ternary applySubstHead
        · exact substitutionAllowed
        · exact schemaAllowedAt_of_ground
            (schemaGroundAt_encodeFormula 0 assertion.formula)
        · exact resultFormulaAllowed
  · simp only [List.mem_singleton] at conclusionMember
    subst pattern
    exact schemaAllowedAt_unary provesHead resultFormulaAllowed

private theorem hypothesisBodyFormal_occurs_in_proves
    (index : Nat) (typecode : String) :
    (hypothesisBodyFormalName index, 0) ∈
      patternMetavariableOccurrencesAt 0
        (proves
          (Builder.formula (encodeString typecode)
            (.fvar (hypothesisBodyFormalName index)))) := by
  simp [proves, encodeString, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt]

private theorem assertionHypothesisFormal_occurs
    (index : Nat) (hypotheses : List HypothesisView) :
    ∀ formal ∈ assertionHypothesisFormalsFrom index hypotheses,
      formal ∈ patternsMetavariableOccurrencesAt 0
        (assertionHypothesisProvesFrom index hypotheses) := by
  induction hypotheses generalizing index with
  | nil => simp
  | cons hypothesis hypotheses inductionHypothesis =>
      intro formal formalMember
      rw [assertionHypothesisFormalsFrom_cons] at formalMember
      rw [assertionHypothesisProvesFrom_cons]
      simp only [patternsMetavariableOccurrencesAt, List.mem_append]
      rcases List.mem_cons.mp formalMember with rfl | tailMember
      · exact Or.inl
          (hypothesisBodyFormal_occurs_in_proves index hypothesis.typecode)
      · exact Or.inr
          (inductionHypothesis (index + 1) formal tailMember)

private theorem conclusionBodyFormal_occurs_in_proves
    (typecode : String) :
    (conclusionBodyFormalName, 0) ∈
      patternMetavariableOccurrencesAt 0
        (proves
          (Builder.formula (encodeString typecode)
            (.fvar conclusionBodyFormalName))) := by
  simp [proves, encodeString, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt]

private theorem patternOccurrence_mem_of_pattern_mem
    {depth : Nat} {pattern : Pattern} {patterns : List Pattern}
    (patternMember : pattern ∈ patterns) {occurrence : String × Nat}
    (occurrenceMember :
      occurrence ∈ patternMetavariableOccurrencesAt depth pattern) :
    occurrence ∈ patternsMetavariableOccurrencesAt depth patterns := by
  induction patterns with
  | nil => simp at patternMember
  | cons head tail inductionHypothesis =>
      rw [patternsMetavariableOccurrencesAt, List.mem_append]
      rcases List.mem_cons.mp patternMember with rfl | tailMember
      · exact Or.inl occurrenceMember
      · exact Or.inr (inductionHypothesis tailMember)

private theorem patternOccurrences_mono
    {depth : Nat} {smaller larger : List Pattern}
    (inclusion : ∀ pattern ∈ smaller, pattern ∈ larger)
    {occurrence : String × Nat}
    (occurrenceMember :
      occurrence ∈ patternsMetavariableOccurrencesAt depth smaller) :
    occurrence ∈ patternsMetavariableOccurrencesAt depth larger := by
  induction smaller with
  | nil => simp [patternsMetavariableOccurrencesAt] at occurrenceMember
  | cons head tail inductionHypothesis =>
      rw [patternsMetavariableOccurrencesAt, List.mem_append]
        at occurrenceMember
      rcases occurrenceMember with headMember | tailMember
      · exact patternOccurrence_mem_of_pattern_mem
          (inclusion head (by simp)) headMember
      · apply inductionHypothesis
        · intro pattern patternMember
          exact inclusion pattern (by simp [patternMember])
        · exact tailMember

private theorem sourceAssertionRule_formal_occurs
    (callerFrame : SourceFrame) (assertion : SourceAssertion) :
    ∀ formal ∈ (sourceAssertionRule callerFrame assertion).metavariables,
      formal ∈ RuleSchema.occurrences
        (sourceAssertionRule callerFrame assertion) := by
  have formalsEquation :
      (sourceAssertionRule callerFrame assertion).metavariables =
        assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
          [(conclusionBodyFormalName, 0)] := by
    rfl
  have premisesEquation :
      (sourceAssertionRule callerFrame assertion).premises =
        assertionHypothesisProvesFrom 0 assertion.hypotheses ++
          assertionEssentialChecksFrom
              (sourceAssertionSubstitution assertion) 0 assertion.hypotheses ++
          [ dvOK (sourceAssertionSubstitution assertion)
              (encodeSourceFrame callerFrame)
              (encodeSourceFrame assertion.frame)
          , applySubst (sourceAssertionSubstitution assertion)
              (encodeFormula assertion.formula)
              (Builder.formula (encodeString assertion.formula.typecode)
                (.fvar conclusionBodyFormalName)) ] := by
    rfl
  have conclusionEquation :
      (sourceAssertionRule callerFrame assertion).conclusion =
        proves
          (Builder.formula (encodeString assertion.formula.typecode)
            (.fvar conclusionBodyFormalName)) := by
    rfl
  intro formal formalMember
  rw [formalsEquation, List.mem_append] at formalMember
  unfold RuleSchema.occurrences RuleSchema.patterns
  rw [premisesEquation, conclusionEquation]
  rcases formalMember with hypothesisFormal | conclusionFormal
  · apply patternOccurrences_mono (smaller :=
        assertionHypothesisProvesFrom 0 assertion.hypotheses)
    · intro pattern patternMember
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact patternMember
    · exact assertionHypothesisFormal_occurs 0 assertion.hypotheses
        formal hypothesisFormal
  · simp only [List.mem_singleton] at conclusionFormal
    subst formal
    apply patternOccurrence_mem_of_pattern_mem
      (pattern :=
        proves
          (Builder.formula (encodeString assertion.formula.typecode)
            (.fvar conclusionBodyFormalName)))
    · exact List.mem_append_right _ (by simp)
    · exact conclusionBodyFormal_occurs_in_proves assertion.formula.typecode

private theorem sourceAssertionRule_isLocallyValid
    (callerFrame : SourceFrame) (assertion : SourceAssertion)
    (labelNonempty : assertion.label != "") :
    RuleSchema.isLocallyValid
        (sourceAssertionRule callerFrame assertion) = true := by
  let rule := sourceAssertionRule callerFrame assertion
  have formalsEquation :
      rule.metavariables =
        assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
          [(conclusionBodyFormalName, 0)] := by
    rfl
  have idNonempty : (rule.id.value != "") = true := by
    change ((sourceAssertionRule callerFrame assertion).id.value != "") = true
    rw [sourceAssertionRule_id_value]
    exact labelNonempty
  have namesNonempty :
      (RuleSchema.metavariableNames rule).all
          (fun name => name != "") = true := by
    change
      (RuleSchema.metavariableNames
        (assertionRule callerFrame.toRuntime
          assertion.toProjectionView)).all (fun name => name != "") = true
    exact assertionRuleFormalNames_nonempty callerFrame.toRuntime
      assertion.toProjectionView
  have namesNodup :
      (RuleSchema.metavariableNames rule).Nodup := by
    unfold RuleSchema.metavariableNames
    rw [formalsEquation]
    exact assertionRuleFormalNames_nodup callerFrame.toRuntime
      assertion.toProjectionView
  have namesUnique :
      (RuleSchema.metavariableNames rule).eraseDups.length ==
        (RuleSchema.metavariableNames rule).length := by
    rw [eraseDups_eq_self_of_nodup _ namesNodup]
    exact beq_iff_eq.mpr rfl
  have patternsAllowed : ∀ pattern ∈ RuleSchema.patterns rule,
      SchemaAllowedAt rule.metavariables 0 pattern := by
    intro pattern patternMember
    rw [formalsEquation]
    exact sourceAssertionRule_patterns_allowed callerFrame assertion
      pattern patternMember
  have patternListSound :=
    schemaAllowedPatterns_sound (RuleSchema.patterns rule) patternsAllowed
  have occurrencesAllowed :
      (RuleSchema.occurrences rule).all
          (fun occurrence => rule.metavariables.contains occurrence) = true := by
    exact patternListSound.1
  have everyFormalOccurs :
      rule.metavariables.all
          (fun formal => (RuleSchema.occurrences rule).contains formal) = true := by
    apply List.all_eq_true.mpr
    intro formal formalMember
    exact List.contains_iff_mem.mpr
      (sourceAssertionRule_formal_occurs callerFrame assertion formal
        formalMember)
  have patternsScoped :
      (RuleSchema.patterns rule).all Pattern.isWellScoped = true := by
    apply List.all_eq_true.mpr
    intro pattern patternMember
    have allowed := patternsAllowed pattern patternMember
    exact allowed.2.1
  have patternsNoRest :
      (RuleSchema.patterns rule).all patternHasNoCollectionRest = true := by
    apply List.all_eq_true.mpr
    intro pattern patternMember
    exact (patternsAllowed pattern patternMember).2.2.1
  have patternsCanonical :
      (RuleSchema.patterns rule).all
          Pattern.hasCanonicalBinderMetadata = true := by
    apply List.all_eq_true.mpr
    intro pattern patternMember
    exact (patternsAllowed pattern patternMember).2.2.2
  simp only [RuleSchema.isLocallyValid, Bool.and_eq_true]
  exact
    ⟨⟨⟨⟨⟨⟨⟨idNonempty, namesNonempty⟩, namesUnique⟩,
      occurrencesAllowed⟩, everyFormalOccurs⟩, patternsScoped⟩,
      patternsNoRest⟩, patternsCanonical⟩

private theorem activeHypothesisRule_isLocallyValid
    (hypothesis : HypothesisView)
    (labelNonempty : hypothesis.label != "") :
    RuleSchema.isLocallyValid (activeHypothesisRule hypothesis) = true := by
  have formulaGround := schemaGroundAt_encodeFormula 0 hypothesis.formula
  rcases formulaGround with
    ⟨formulaOccurrences, formulaScoped, formulaNoRest, formulaCanonical⟩
  simp only [RuleSchema.isLocallyValid]
  rw [show ((activeHypothesisRule hypothesis).id.value != "") = true by
    rw [activeHypothesisRule_id_value]
    exact labelNonempty]
  simp [RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, activeHypothesisRule,
    proves, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, formulaOccurrences,
    formulaScoped, formulaNoRest, formulaCanonical]

private theorem sourcePrefixRuleLabel_nonempty
    {source : SourcePrefix} (valid : sourcePrefixValid source = true)
    {label : String} (member : label ∈ sourcePrefixRuleLabels source) :
    label != "" := by
  have labelsValid := sourcePrefixRuleLabels_valid valid
  simp only [sourceRuleLabelsValid, Bool.and_eq_true] at labelsValid
  have accepted := List.all_eq_true.mp labelsValid.1 label member
  simp only [Bool.and_eq_true] at accepted
  exact accepted.1

private theorem sourceGeneratedRules_areLocallyValid
    (source : SourcePrefix) (valid : sourcePrefixValid source = true) :
    (sourceGeneratedRules source).all RuleSchema.isLocallyValid = true := by
  rw [sourceGeneratedRules, List.all_append]
  simp only [Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro rule ruleMember
    rcases List.mem_map.mp ruleMember with ⟨hypothesis, hypothesisMember, rfl⟩
    apply activeHypothesisRule_isLocallyValid
    apply sourcePrefixRuleLabel_nonempty valid
    unfold sourcePrefixRuleLabels
    exact List.mem_append_left _
      (List.mem_map_of_mem hypothesisMember)
  · apply List.all_eq_true.mpr
    intro rule ruleMember
    rcases List.mem_map.mp ruleMember with ⟨assertion, assertionMember, rfl⟩
    apply sourceAssertionRule_isLocallyValid
    apply sourcePrefixRuleLabel_nonempty valid
    unfold sourcePrefixRuleLabels
    exact List.mem_append_right _
      (List.mem_map_of_mem assertionMember)

private theorem sideRules_areLocallyValid :
    sideRules.all RuleSchema.isLocallyValid = true := by
  have valid := sideDefinition_valid
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules,
    Bool.and_eq_true] at valid
  exact valid.1.1.1.1.2

private theorem rawSourceInferenceLanguageDef_hasValidLocalRules
    (source : SourcePrefix) (gates : SourceProjectionGates source) :
    (rawSourceInferenceLanguageDef source).hasValidLocalRules = true := by
  unfold CalculusLanguageDef.hasValidLocalRules
  simp only [rawSourceInferenceLanguageDef, sourceInferenceLanguageDef,
    Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa using languageWithSourceVocabulary_validate
      (sourcePrefixVocabulary source) gates.vocabularyValid
  · change
      (sideRules ++ sourceGeneratedRules source).all
        RuleSchema.isLocallyValid = true
    rw [List.all_append]
    simp only [Bool.and_eq_true]
    exact
      ⟨sideRules_areLocallyValid,
        sourceGeneratedRules_areLocallyValid source gates.prefixValid⟩
  · exact beq_iff_eq.mpr
      (combinedRuleIds_eraseDups_length gates.prefixValid
        gates.ruleIdsDisjoint)

/-! ## Source-vocabulary coverage -/

private theorem sourcePrefixVocabulary_mem_of_raw_mem
    (source : SourcePrefix) {value : String}
    (member : value ∈
      stringsOfSourceFrame source.callerFrame ++
        source.activeHypotheses.flatMap stringsOfHypothesis ++
        source.assertions.flatMap stringsOfSourceAssertion) :
    value ∈ sourcePrefixVocabulary source := by
  unfold sourcePrefixVocabulary
  rw [mem_sortStrings_iff, List.mem_eraseDups]
  exact member

private theorem sourcePrefixVocabulary_callerFrame
    (source : SourcePrefix) {value : String}
    (member : value ∈ stringsOfSourceFrame source.callerFrame) :
    value ∈ sourcePrefixVocabulary source := by
  apply sourcePrefixVocabulary_mem_of_raw_mem source
  exact List.mem_append_left _ (List.mem_append_left _ member)

private theorem sourcePrefixVocabulary_activeHypothesis
    (source : SourcePrefix) {hypothesis : HypothesisView}
    (hypothesisMember : hypothesis ∈ source.activeHypotheses)
    {value : String} (valueMember : value ∈ stringsOfHypothesis hypothesis) :
    value ∈ sourcePrefixVocabulary source := by
  apply sourcePrefixVocabulary_mem_of_raw_mem source
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr
    ⟨hypothesis, hypothesisMember, valueMember⟩

private theorem sourcePrefixVocabulary_assertion
    (source : SourcePrefix) {assertion : SourceAssertion}
    (assertionMember : assertion ∈ source.assertions)
    {value : String}
    (valueMember : value ∈ stringsOfSourceAssertion assertion) :
    value ∈ sourcePrefixVocabulary source := by
  apply sourcePrefixVocabulary_mem_of_raw_mem source
  apply List.mem_append_right
  exact List.mem_flatMap.mpr
    ⟨assertion, assertionMember, valueMember⟩

private theorem stringsOfHypothesis_formula
    (hypothesis : HypothesisView) {value : String}
    (member : value ∈ stringsOfFormula hypothesis.formula) :
    value ∈ stringsOfHypothesis hypothesis := by
  simp [stringsOfHypothesis, member]

private theorem stringsOfSourceAssertion_formula
    (assertion : SourceAssertion) {value : String}
    (member : value ∈ stringsOfFormula assertion.formula) :
    value ∈ stringsOfSourceAssertion assertion := by
  simp [stringsOfSourceAssertion, member]

private theorem stringsOfSourceAssertion_frame
    (assertion : SourceAssertion) {value : String}
    (member : value ∈ stringsOfSourceFrame assertion.frame) :
    value ∈ stringsOfSourceAssertion assertion := by
  unfold stringsOfSourceAssertion
  exact List.mem_cons_of_mem _
    (List.mem_append_left _ (List.mem_append_right _ member))

private theorem stringsOfSourceAssertion_hypothesis
    (assertion : SourceAssertion) {hypothesis : HypothesisView}
    (hypothesisMember : hypothesis ∈ assertion.hypotheses)
    {value : String} (valueMember : value ∈ stringsOfHypothesis hypothesis) :
    value ∈ stringsOfSourceAssertion assertion := by
  simp only [stringsOfSourceAssertion, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (List.mem_flatMap.mpr
    ⟨hypothesis, hypothesisMember, valueMember⟩))

/-! ## Fixed-constructor coverage of source encodings -/

private theorem sourceInferenceLanguageDef_rawString_fixed
    {heads : List String} (sourceRules : List SourceRuleSchema)
    (vocabularyValid : sourceVocabularyValid heads = true)
    (value : String) (member : value ∈ heads) :
    fixedConstructorsValid
        (sourceInferenceLanguageDef heads sourceRules).toLanguageDef
        (Builder.rawString value) = true := by
  apply fixedConstructorsValid_apply_of
  · exact sourceInferenceLanguageDef_has_source_constructor sourceRules
      vocabularyValid member
  · intro argument argumentMember
    simp at argumentMember

private theorem sourceInferenceLanguageDef_encodeString_fixed
    {heads : List String} (sourceRules : List SourceRuleSchema)
    (vocabularyValid : sourceVocabularyValid heads = true)
    (value : String) (member : value ∈ heads) :
    fixedConstructorsValid
        (sourceInferenceLanguageDef heads sourceRules).toLanguageDef
        (encodeString value) = true := by
  apply fixedConstructorsValid_apply_of
  · apply sourceInferenceLanguageDef_preserves_accepted_constructor
      sourceRules vocabularyValid
    simpa using (show
      languageHasConstructorArity dataLanguage stringHead 1 = true by decide)
  · intro argument argumentMember
    simp only [List.mem_singleton] at argumentMember
    subst argument
    exact sourceInferenceLanguageDef_rawString_fixed sourceRules
      vocabularyValid value member

private theorem sourceInferenceLanguageDef_encodeListWith_fixed
    {alpha : Type} {heads : List String}
    (sourceRules : List SourceRuleSchema)
    (vocabularyValid : sourceVocabularyValid heads = true)
    (encode : alpha → Pattern) :
    ∀ values,
      (∀ value ∈ values,
        fixedConstructorsValid
          (sourceInferenceLanguageDef heads sourceRules).toLanguageDef
          (encode value) = true) →
      fixedConstructorsValid
        (sourceInferenceLanguageDef heads sourceRules).toLanguageDef
        (encodeListWith encode values) = true
  | [], _ => by
      apply fixedConstructorsValid_apply_of
      · apply sourceInferenceLanguageDef_preserves_accepted_constructor
          sourceRules vocabularyValid
        simpa using (show
          languageHasConstructorArity dataLanguage nilHead 0 = true by decide)
      · intro argument argumentMember
        simp at argumentMember
  | value :: values, elementsValid => by
      apply fixedConstructorsValid_apply_of
      · apply sourceInferenceLanguageDef_preserves_accepted_constructor
          sourceRules vocabularyValid
        simpa using (show
          languageHasConstructorArity dataLanguage consHead 2 = true by decide)
      · intro argument argumentMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at argumentMember
        rcases argumentMember with rfl | rfl
        · exact elementsValid value (by simp)
        · apply sourceInferenceLanguageDef_encodeListWith_fixed sourceRules
            vocabularyValid encode values
          intro tail tailMember
          exact elementsValid tail (by simp [tailMember])

private theorem sourceInferenceLanguageDef_encodeSym_fixed
    {heads : List String} (sourceRules : List SourceRuleSchema)
    (vocabularyValid : sourceVocabularyValid heads = true)
    (symbol : RuntimeSym) (member : symbol.value ∈ heads) :
    fixedConstructorsValid
        (sourceInferenceLanguageDef heads sourceRules).toLanguageDef
        (encodeSym symbol) = true := by
  cases symbol with
  | const name =>
      apply fixedConstructorsValid_apply_of
      · apply sourceInferenceLanguageDef_preserves_accepted_constructor
          sourceRules vocabularyValid
        simpa using (show
          languageHasConstructorArity dataLanguage constSymHead 1 = true by
            decide)
      · intro argument argumentMember
        simp only [List.mem_singleton] at argumentMember
        subst argument
        exact sourceInferenceLanguageDef_encodeString_fixed sourceRules
          vocabularyValid name member
  | var name =>
      apply fixedConstructorsValid_apply_of
      · apply sourceInferenceLanguageDef_preserves_accepted_constructor
          sourceRules vocabularyValid
        simpa using (show
          languageHasConstructorArity dataLanguage varSymHead 1 = true by
            decide)
      · intro argument argumentMember
        simp only [List.mem_singleton] at argumentMember
        subst argument
        exact sourceInferenceLanguageDef_encodeString_fixed sourceRules
          vocabularyValid name member

private theorem sourceInferenceLanguageDef_encodeFormula_fixed
    {heads : List String} (sourceRules : List SourceRuleSchema)
    (vocabularyValid : sourceVocabularyValid heads = true)
    (formula : ConstantHeadedFormula)
    (declared : ∀ value ∈ stringsOfFormula formula, value ∈ heads) :
    fixedConstructorsValid
        (sourceInferenceLanguageDef heads sourceRules).toLanguageDef
        (encodeFormula formula) = true := by
  apply fixedConstructorsValid_apply_of
  · apply sourceInferenceLanguageDef_preserves_accepted_constructor
      sourceRules vocabularyValid
    simpa using (show
      languageHasConstructorArity dataLanguage formulaHead 2 = true by decide)
  · intro argument argumentMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at argumentMember
    rcases argumentMember with rfl | rfl
    · exact sourceInferenceLanguageDef_encodeString_fixed sourceRules
        vocabularyValid formula.typecode
        (declared formula.typecode (by simp [stringsOfFormula]))
    · apply sourceInferenceLanguageDef_encodeListWith_fixed sourceRules
        vocabularyValid encodeSym formula.body
      intro symbol symbolMember
      apply sourceInferenceLanguageDef_encodeSym_fixed sourceRules
        vocabularyValid symbol
      apply declared symbol.value
      simp [stringsOfFormula, List.mem_map_of_mem symbolMember]

private theorem sourceInferenceLanguageDef_encodeDVPair_fixed
    {heads : List String} (sourceRules : List SourceRuleSchema)
    (vocabularyValid : sourceVocabularyValid heads = true)
    (pair : String × String) (leftMember : pair.1 ∈ heads)
    (rightMember : pair.2 ∈ heads) :
    fixedConstructorsValid
        (sourceInferenceLanguageDef heads sourceRules).toLanguageDef
        (encodeDVPair pair) = true := by
  apply fixedConstructorsValid_apply_of
  · apply sourceInferenceLanguageDef_preserves_accepted_constructor
      sourceRules vocabularyValid
    simpa using (show
      languageHasConstructorArity dataLanguage dvPairHead 2 = true by decide)
  · intro argument argumentMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at argumentMember
    rcases argumentMember with rfl | rfl
    · exact sourceInferenceLanguageDef_encodeString_fixed sourceRules
        vocabularyValid pair.1 leftMember
    · exact sourceInferenceLanguageDef_encodeString_fixed sourceRules
        vocabularyValid pair.2 rightMember

private theorem sourceInferenceLanguageDef_encodeSourceFrame_fixed
    {heads : List String} (sourceRules : List SourceRuleSchema)
    (vocabularyValid : sourceVocabularyValid heads = true)
    (frame : SourceFrame)
    (declared : ∀ value ∈ stringsOfSourceFrame frame, value ∈ heads) :
    fixedConstructorsValid
        (sourceInferenceLanguageDef heads sourceRules).toLanguageDef
        (encodeSourceFrame frame) = true := by
  apply fixedConstructorsValid_apply_of
  · apply sourceInferenceLanguageDef_preserves_accepted_constructor
      sourceRules vocabularyValid
    simpa using (show
      languageHasConstructorArity dataLanguage frameHead 2 = true by decide)
  · intro argument argumentMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at argumentMember
    rcases argumentMember with rfl | rfl
    · apply sourceInferenceLanguageDef_encodeListWith_fixed sourceRules
        vocabularyValid encodeDVPair frame.distinctVariables
      intro pair pairMember
      apply sourceInferenceLanguageDef_encodeDVPair_fixed sourceRules
          vocabularyValid pair
      · apply declared pair.1
        unfold stringsOfSourceFrame
        exact List.mem_append_left _ (List.mem_flatMap.mpr
          ⟨pair, pairMember, by simp⟩)
      · apply declared pair.2
        unfold stringsOfSourceFrame
        exact List.mem_append_left _ (List.mem_flatMap.mpr
          ⟨pair, pairMember, by simp⟩)
    · apply sourceInferenceLanguageDef_encodeListWith_fixed sourceRules
        vocabularyValid encodeString frame.hypothesisLabels
      intro label labelMember
      apply sourceInferenceLanguageDef_encodeString_fixed sourceRules
        vocabularyValid label
      apply declared label
      unfold stringsOfSourceFrame
      exact List.mem_append_right _ labelMember

end Mettapedia.Languages.Metamath.SourceInferenceProjectionValidation
