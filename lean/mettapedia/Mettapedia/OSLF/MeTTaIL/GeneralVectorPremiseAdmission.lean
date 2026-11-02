import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralVectorBindingAdmission

/-! First-order schemas with fixed vectors pass root projection admission
when their actual occurrences have declared empty dependency spines. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static

open Syntax RuleBinding GeneralFirstOrderProjection

theorem raw_flow_append (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec) (first second : List Premise) (available : List String) :
    GeneralPremise.premisesFlow language provider rule spec available (first ++ second) =
      let front := GeneralPremise.premisesFlow language provider rule spec available first
      let back := GeneralPremise.premisesFlow language provider rule spec front.available second
      ⟨back.available,front.supported && back.supported⟩ := by
  induction first generalizing available with
  | nil => simp [GeneralPremise.premisesFlow]
  | cons head tail ih =>
    simp [GeneralPremise.premisesFlow,ih,Bool.and_assoc]

theorem query_argument_coherent (rule : RewriteRule) (index : Nat) (relation : String) (arguments : List Pattern)
    (selected : rule.premises[index]? = some (.relationQuery relation arguments))
    (argumentIndex : Nat) (code : Pattern) (atArgument : arguments[argumentIndex]? = some code) :
    NameCoherent rule (.premise index 0 argumentIndex) [] code := by
  intro suffix
  simp only [sitePattern?,selected,quantifiedBody?,Option.bind_eq_bind,Option.bind_some,
    atArgument,List.nil_append]

mutual
  theorem vector_projection {rule : RewriteRule} {site : RulePatternSite}
      {path : List Nat} {schema : Pattern} (shape : VectorFirstOrder schema)
      (coherent : NameCoherent rule site path schema)
      (declared : ∀ name ∈ schema.freeFvarNames,
        dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some []) :
      checkRootProjectionSchema rule (GeneralRuleBindingInference.inferredSpec rule) site path schema = true := by
    cases shape with
    | metavariable name =>
      exact beq_iff_eq.mpr (arguments?_empty_of_declared rule _ name site path
        (declared name (by simp [Pattern.freeFvarNames])) coherent.fvar rfl)
    | constructor label arguments shapes =>
      simpa only [checkRootProjectionSchema] using vector_projection_arguments shapes coherent.arguments
        (by simpa only [Pattern.freeFvarNames] using declared)
    | vector arguments shapes =>
      simpa only [checkRootProjectionSchema,Option.isNone_none,Bool.true_and] using
        vector_projection_arguments shapes coherent.collection_arguments
          (by simpa only [Pattern.freeFvarNames,Option.toList_none,List.append_nil] using declared)
  termination_by sizeOf schema

  theorem vector_projection_arguments {rule : RewriteRule} {site : RulePatternSite}
      {path : List Nat} {index : Nat} {schemas : List Pattern}
      (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema)
      (coherent : ArgumentsNameCoherent rule site path index schemas)
      (declared : ∀ name ∈ schemas.flatMap Pattern.freeFvarNames,
        dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some []) :
      checkRootProjectionArguments rule (GeneralRuleBindingInference.inferredSpec rule) site path index schemas = true := by
    cases schemas with
    | nil => rfl
    | cons schema schemas =>
      simp only [checkRootProjectionArguments,Bool.and_eq_true]
      refine ⟨vector_projection (shapes schema (List.mem_cons_self ..)) coherent.head ?_,
        vector_projection_arguments (fun child member => shapes child (List.mem_cons_of_mem _ member))
          coherent.tail ?_⟩
      · intro name member
        exact declared name (List.mem_flatMap.mpr ⟨schema,List.mem_cons_self ..,member⟩)
      · intro name member
        obtain ⟨child,childMember,present⟩ := List.mem_flatMap.mp member
        exact declared name (List.mem_flatMap.mpr ⟨child,List.mem_cons_of_mem _ childMember,present⟩)
  termination_by sizeOf schemas
end

theorem vector_projection_of_typed {language : LanguageDef} {rule : RewriteRule}
    {site : RulePatternSite} {path : List Nat} {schema : Pattern} {type : TypeExpr}
    (unique : (rule.typeContext.map Prod.fst).Nodup) (shape : VectorFirstOrder schema)
    (coherent : NameCoherent rule site path schema)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.HasType language
      (fun name => lookupRuleType? rule name) [] schema type) :
    checkRootProjectionSchema rule (GeneralRuleBindingInference.inferredSpec rule) site path schema = true := by
  apply vector_projection shape coherent
  intro name member
  obtain ⟨type,found⟩ := typed.freeType_of_mem_freeFvarNames_of_isObjectPattern
    (GeneralRuleBindingInference.vector_object shape) member
  rw [lookupRuleType?_eq_lookup] at found
  exact inferred_dependencies_of_lookup rule unique found

#print axioms vector_projection
#print axioms vector_projection_of_typed

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static
