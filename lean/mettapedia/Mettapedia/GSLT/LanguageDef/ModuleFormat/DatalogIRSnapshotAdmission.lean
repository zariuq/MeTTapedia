import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPlanAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRCanonicalProvider
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSnapshotTermination

/-! Global admission of prepared immutable snapshots. Registered references,
canonical provider rows, finite query strata and the selected collection
profile discharge their existing checks. Language validation is retained as
an explicit hypothesis until the generated rewrite rows are validated. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SnapshotAdmission

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission

theorem reference_names_unique (pools : Join.Pools) : ((Executable.freeTypes pools).map Prod.fst).Nodup := by
  simp only [Executable.freeTypes,List.map_append,List.map_map,Function.comp_def]
  apply List.Nodup.append
  · apply List.Nodup.map _ List.nodup_range
    intro first second same
    exact Executable.relationRef_injective (congrArg Pattern.fvar same)
  · apply List.Nodup.map _ List.nodup_range
    intro first second same
    exact Executable.valueRef_injective (congrArg Pattern.fvar same)
  · apply List.disjoint_left.mpr
    intro name relation literal
    obtain ⟨first,_,rfl⟩ := List.mem_map.mp relation
    obtain ⟨second,_,same⟩ := List.mem_map.mp literal
    exact Executable.relation_value_disjoint first second (congrArg Pattern.fvar same.symm)

private theorem type_names (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) :
    prepared.compiled.typeNames = Query.baseLanguage.typeNames := by
  obtain ⟨core,values,_,_,rfl⟩ := PlanReading.prepared_payload program seeds prepared accepted
  rfl

theorem free_context_checked (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) :
    checkFreeContext (Executable.snapshot prepared known) = true := by
  have relationDeclared : declaredType prepared.compiled (.base "DlRelation") = true := by
    unfold declaredType
    rw [type_names program seeds prepared accepted]
    decide +kernel
  have valueDeclared : declaredType prepared.compiled (.base "DlValue") = true := by
    unfold declaredType
    rw [type_names program seeds prepared accepted]
    decide +kernel
  simp only [checkFreeContext,Executable.snapshot,reference_names_unique,decide_true,Bool.true_and]
  apply List.all_eq_true.mpr
  intro entry member
  rcases List.mem_append.mp member with relation | literal
  · obtain ⟨index,_,rfl⟩ := List.mem_map.mp relation
    exact relationDeclared
  · obtain ⟨index,_,rfl⟩ := List.mem_map.mp literal
    exact valueDeclared

theorem query_strata_checked (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) :
    GeneralPremise.checkStepStratification (executionLanguage (Executable.snapshot prepared known) Executable.permissions) = true := by
  apply List.all_eq_true.mpr
  intro entry member
  rcases entry with ⟨rule,index⟩
  have atRule := List.mk_mem_zipIdx_iff_getElem?.mp member
  have queries := SnapshotTermination.rule_queries program seeds prepared accepted known index rule atRule
  have empty : rule.premises.flatMap GeneralPremise.stepSources = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro premise present
    obtain ⟨relation,arguments,rfl⟩ := queries premise present
    rfl
  simp only [empty,List.all_nil]

theorem set_profile_checked (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) :
    setDecompositionFree (Executable.snapshot prepared known) Executable.permissions = true := by
  have noSet : prepared.compiled.usesCollection .hashSet = false := by
    unfold LanguageDef.usesCollection
    rw [show prepared.compiled.terms = Query.baseLanguage.terms from SourcePlan.plan_grammar program seeds prepared accepted known]
    decide +kernel
  simp only [setDecompositionFree,Executable.snapshot,noSet,Bool.not_false,Bool.true_or]

theorem complete_of_language_valid (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern)
    (canonical : ClosureMachine.CanonicalFacts prepared known) (valid : prepared.compiled.validate = []) :
    (Executable.plan prepared known).complete = true := by
  have freeChecked := free_context_checked program seeds prepared accepted known
  have providerChecked := ClosureMachine.canonical_closed program seeds prepared accepted known canonical
  have rulesChecked := PlanAdmission.rule_obligations_empty program seeds prepared accepted known
  have strataChecked := query_strata_checked program seeds prepared accepted known
  have setsChecked := set_profile_checked program seeds prepared accepted known
  have reflection : (Reflection.validate prepared.compiled Executable.permissions.reflection).isEmpty = true := by
    simp [Executable.permissions,Reflection.validate,Reflection.ReflectionProfile.empty]
  have equations : prepared.compiled.equations = [] := by
    obtain ⟨core,values,_,_,rfl⟩ := PlanReading.prepared_payload program seeds prepared accepted
    rfl
  have selectedEmpty : selectedEquations (Executable.snapshot prepared known) Executable.permissions = [] := by
    simp [selectedEquations,Executable.snapshot,equations]
  have missingRules : missing Executable.permissions.ruleIndices prepared.compiled.rewrites.length = [] := rfl
  have missingEquations : missing Executable.permissions.equationIndices prepared.compiled.equations.length = [] := rfl
  have noDerived : Executable.permissions.includeDerivedEquations = false := rfl
  change GeneralPremise.checkProviderClosed prepared.compiled
    (Executable.snapshot prepared known).free (Executable.snapshot prepared known).provider = true at providerChecked
  simp only [Executable.plan,Plan.complete,compile,
    show (Executable.snapshot prepared known).language = prepared.compiled from rfl,
    valid,List.isEmpty_nil,freeChecked,providerChecked,reflection,missingRules,missingEquations,
    rulesChecked,selectedEmpty,strataChecked,setsChecked,noDerived,
    Bool.false_and,Bool.false_eq_true,if_false,if_true,List.map_nil,List.flatMap_nil,List.nil_append]

#print axioms reference_names_unique
#print axioms free_context_checked
#print axioms complete_of_language_valid

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SnapshotAdmission
