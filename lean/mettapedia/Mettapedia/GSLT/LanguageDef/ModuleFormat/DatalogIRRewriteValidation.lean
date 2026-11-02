import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRProjectionAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSourcePlan
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseValidationFlow
import Mettapedia.OSLF.MeTTaIL.PlainRuleValidation

/-! Compiled Datalog clauses satisfy the actual rewrite validator. Typed
schemas provide constructor and scope evidence, generated name domains
exclude constructor collisions, and ordered premise flow supplies outputs. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.RewriteValidation

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match GeneralRuleBindingInference GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem constructor_heads : ∀ name ∈ Query.baseLanguage.terms.map GrammarRule.label,
    name.toList.head? ≠ some 'p' ∧ name.toList.head? ≠ some 'v' ∧ name.toList.head? ≠ some 'a' := by
  decide +kernel

private theorem role_not_constructor (role : Names.Role) : Names.encode role ∉ Query.baseLanguage.terms.map GrammarRule.label := by
  intro member
  have different := constructor_heads _ member
  cases role <;> simp [Names.encode,Join.relationSlot,Join.literalSlot,Join.logicalVariable,
    Join.anonymousVariable,String.toList_append] at different

private theorem references_declared {language : LanguageDef} {free : FreeTypeContext}
    {pattern : Pattern} {type : TypeExpr} (typed : HasType language free [] pattern type) :
    ∀ reference ∈ pattern.constructorRefs, reference ∈ RewriteValidationCertificate.constructorSignatures language := by
  intro reference member
  obtain ⟨declaration,present,named,arity⟩ := typed.constructorReferencesDeclared reference member
  exact List.mem_map.mpr ⟨declaration,present,Prod.ext named arity⟩

theorem body_pattern (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule)
    (pattern : Pattern) (member : pattern ∈ rule.premises.flatMap LanguageDef.premisePatterns) :
    VectorFirstOrder pattern ∧ ∃ type, HasType language (GeneralPremise.lookupRuleType? rule) [] pattern type := by
  obtain ⟨premise,present,inside⟩ := List.mem_flatMap.mp member
  obtain ⟨relation,arguments,rfl⟩ := ProjectionAdmission.rule_queries pools ordinal clause rule compiled premise present
  obtain ⟨index,atPremise⟩ := List.mem_iff_getElem?.mp present
  obtain ⟨argumentIndex,atArgument⟩ := List.mem_iff_getElem?.mp inside
  exact ProjectionAdmission.query_schema_typed language terms pools ordinal clause rule compiled index relation arguments atPremise argumentIndex pattern atArgument

theorem rewrite_valid (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (ordinal : Nat) (clause : Clause)
    (source : ProgramGrounding.ClauseAt program ordinal clause) (rule : RewriteRule)
    (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule) :
    LanguageDef.validateRewrite prepared.compiled rule = [] := by
  have terms : prepared.compiled.terms = Query.baseLanguage.terms := SourcePlan.plan_grammar program seeds prepared accepted []
  have labelsUnique : (prepared.compiled.terms.map GrammarRule.label).Nodup := by rw [terms]; decide +kernel
  have typeNames : prepared.compiled.typeNames = Query.baseLanguage.typeNames := by
    obtain ⟨core,values,_,_,rfl⟩ := PlanReading.prepared_payload program seeds prepared accepted
    rfl
  have leftShape : VectorFirstOrder rule.left := by
    rw [(FiringReading.compiled_fields prepared.vocabulary ordinal clause rule compiled).1]
    exact RequestInstances.request_shape prepared.vocabulary
  have rightShape := InstanceMatching.atom_shape prepared.vocabulary clause.body.length clause.head rule.right
    (FiringReading.compiled_fields prepared.vocabulary ordinal clause rule compiled).2
  have leftTyped := SchemaAdmission.left_typed prepared.compiled terms prepared.vocabulary ordinal clause rule compiled
  have rightTyped := SchemaAdmission.head_typed prepared.compiled terms prepared.vocabulary ordinal clause rule compiled
  have bodyTyped := body_pattern prepared.compiled terms prepared.vocabulary ordinal clause rule compiled
  have queries := ProjectionAdmission.rule_queries prepared.vocabulary ordinal clause rule compiled
  have contextAvoids : ∀ entry ∈ rule.typeContext,
      entry.1 ∉ RewriteValidationCertificate.constructorLabels prepared.compiled := by
    intro entry member
    rw [BindingContext.compiled_context prepared.vocabulary ordinal clause rule compiled] at member
    obtain ⟨role,rfl⟩ := BindingContext.context_roles prepared.vocabulary clause entry member
    simpa only [RewriteValidationCertificate.constructorLabels,terms] using role_not_constructor role
  have fvarsAvoid : ∀ pattern type, VectorFirstOrder pattern →
      HasType prepared.compiled (GeneralPremise.lookupRuleType? rule) [] pattern type →
      ∀ name ∈ pattern.freeFvarNames, name ∉ RewriteValidationCertificate.constructorLabels prepared.compiled := by
    intro pattern type shape typed name member
    obtain ⟨sort,found⟩ := typed.freeType_of_mem_freeFvarNames_of_isObjectPattern (vector_object shape) member
    rw [GeneralPremise.lookupRuleType?_eq_lookup] at found
    obtain ⟨entry,present,same⟩ := List.lookup_isSome_iff.mp
      (show (rule.typeContext.lookup name).isSome = true by rw [found]; rfl)
    rw [beq_iff_eq.mp same]
    exact contextAvoids entry present
  have premiseTypes : rule.premises.flatMap LanguageDef.premiseStepTypeExprs = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro premise member
    obtain ⟨relation,arguments,rfl⟩ := queries premise member
    rfl
  have premiseBinders : (rule.premises.flatMap LanguageDef.premisePatterns).flatMap LanguageDef.patternBinderNames = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro pattern member
    exact LanguageDef.patternBinderNames_eq_nil_of_binderFree pattern (vector_binderFree (bodyTyped pattern member).1)
  have quantifiers : rule.premises.flatMap LanguageDef.premiseForAllParams = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro premise member
    obtain ⟨relation,arguments,rfl⟩ := queries premise member
    rfl
  have actualSource : ProgramGrounding.ClauseAt prepared.source ordinal clause := by
    rw [(Executable.prepare_typed program seeds prepared accepted).1]
    exact source
  have flow := FlowAdmission.clause_premises_admitted prepared.compiled terms prepared [] ordinal clause actualSource rule compiled
  apply RewriteValidationCertificate.validateRewrite_eq_nil labelsUnique
  refine {
    contextTypes := ?_, premiseTypes := ?_, leftDeclared := references_declared leftTyped,
    rightDeclared := references_declared rightTyped, premisesDeclared := ?_, allPatternsScoped := ?_,
    fvarsAvoidConstructors := ?_, bindersAvoidConstructors := ?_, contextAvoidsConstructors := contextAvoids,
    rightBound := GeneralPremise.validator_right_bound _ _ _ _ flow }
  · intro entry member name inside
    rw [BindingContext.compiled_context prepared.vocabulary ordinal clause rule compiled] at member
    obtain ⟨role,rfl⟩ := BindingContext.context_roles prepared.vocabulary clause entry member
    rw [typeNames]
    cases role <;> simp only [BindingContext.roleType,TypeExpr.baseNames,List.mem_singleton] at inside
    all_goals subst name; decide +kernel
  · intro type member
    rw [premiseTypes] at member
    cases member
  · intro pattern member
    obtain ⟨shape,type,typed⟩ := bodyTyped pattern member
    exact references_declared typed
  · apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨leftTyped.isWellScopedAt,rightTyped.isWellScopedAt⟩,?_⟩
    apply List.all_eq_true.mpr
    intro premise member
    obtain ⟨relation,arguments,rfl⟩ := queries premise member
    apply List.all_eq_true.mpr
    intro pattern inside
    obtain ⟨shape,type,typed⟩ := bodyTyped pattern (List.mem_flatMap.mpr ⟨.relationQuery relation arguments,member,inside⟩)
    exact typed.isWellScopedAt
  · intro name member
    have used := List.mem_eraseDups.mp member
    rcases List.mem_append.mp used with sides | body
    · rcases List.mem_append.mp sides with left | right
      · apply fvarsAvoid _ _ leftShape leftTyped
        simpa [LanguageDef.patternFvarNames] using left
      · apply fvarsAvoid _ _ rightShape rightTyped
        simpa [LanguageDef.patternFvarNames] using right
    · obtain ⟨premise,present,inPremise⟩ := List.mem_flatMap.mp body
      obtain ⟨relation,arguments,rfl⟩ := queries premise present
      have used : name ∈ arguments.flatMap Pattern.freeFvarNames := by
        simpa [LanguageDef.premiseFvarNames,LanguageDef.patternFvarNames] using inPremise
      obtain ⟨pattern,inside,inPattern⟩ := List.mem_flatMap.mp used
      obtain ⟨shape,type,typed⟩ := bodyTyped pattern (List.mem_flatMap.mpr ⟨.relationQuery relation arguments,present,inside⟩)
      exact fvarsAvoid pattern type shape typed name inPattern
  · intro name member
    simp only [LanguageDef.patternBinderNames_eq_nil_of_binderFree _ (vector_binderFree leftShape),
      LanguageDef.patternBinderNames_eq_nil_of_binderFree _ (vector_binderFree rightShape),premiseBinders,quantifiers,
      List.nil_append,List.eraseDups_nil] at member
    cases member

#print axioms rewrite_valid

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.RewriteValidation
