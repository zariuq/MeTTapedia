import Mettapedia.OSLF.MeTTaIL.GeneralVectorMatchInstance
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderScopedInstance

/-! Dependency-free scoped instantiation of constructor/vector schemas
agrees with their fixed ordinary substitution. Occurrence addresses and
admitted argument metadata are used by the actual instantiator. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding ScopedRuleMatching

mutual
theorem vector_instantiation_exact {rule : RewriteRule} {spec : RuleBindingSpec}
    {operation : Pattern → Pattern → Pattern} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {assignment : ScopedRuleMatching.Assignment} {bindings : Bindings} {schema : Pattern}
    (admitted : admittedFor rule spec = true) (shape : VectorFirstOrder schema)
    (coherent : NameCoherent rule site path schema)
    (defined : GeneralPremise.BoundNames assignment schema.freeFvarNames)
    (roots : GeneralPremise.RootValues ambient assignment)
    (compatible : ScopedCompatible ambient bindings assignment)
    (declared : ∀ name ∈ schema.freeFvarNames, dependencies? spec name = some []) :
    instantiateWith? operation rule spec ambient site path 0 assignment schema = some (applyBindings bindings schema) := by
  cases shape with
  | metavariable name =>
    obtain ⟨value,found⟩ := defined name (by simp [Pattern.freeFvarNames])
    have arguments := arguments_empty_of_admitted admitted (declared name (by simp [Pattern.freeFvarNames])) coherent.fvar
    simp only [instantiateWith?,found,arguments,Option.bind_eq_bind,Option.bind_some,
      root_value_readout (roots name value found),apply_variable,compatible.lookup found,Option.getD_some]
  | constructor label arguments children =>
    have read := vector_instantiation_arguments_exact (operation := operation) admitted children coherent.arguments
      (by simpa only [Pattern.freeFvarNames] using defined) roots compatible
      (by simpa only [Pattern.freeFvarNames] using declared)
    simp only [instantiateWith?,read,Option.bind_eq_bind,Option.bind_some,applyBindings]
  | vector arguments children =>
    have read := vector_instantiation_arguments_exact (operation := operation) admitted children coherent.collection_arguments
      (by simpa only [Pattern.freeFvarNames,Option.toList_none,List.append_nil] using defined) roots compatible
      (by simpa only [Pattern.freeFvarNames,Option.toList_none,List.append_nil] using declared)
    simp only [instantiateWith?,read,Option.bind_eq_bind,Option.bind_some,applyBindings,List.append_nil]
termination_by sizeOf schema

theorem vector_instantiation_arguments_exact {rule : RewriteRule} {spec : RuleBindingSpec}
    {operation : Pattern → Pattern → Pattern} {ambient index : Nat} {site : RulePatternSite} {path : List Nat}
    {assignment : ScopedRuleMatching.Assignment} {bindings : Bindings} {schemas : List Pattern}
    (admitted : admittedFor rule spec = true) (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema)
    (coherent : ArgumentsNameCoherent rule site path index schemas)
    (defined : GeneralPremise.BoundNames assignment (schemas.flatMap Pattern.freeFvarNames))
    (roots : GeneralPremise.RootValues ambient assignment)
    (compatible : ScopedCompatible ambient bindings assignment)
    (declared : ∀ name ∈ schemas.flatMap Pattern.freeFvarNames, dependencies? spec name = some []) :
    instantiateArgsWith? operation rule spec ambient site path 0 assignment index schemas =
      some (schemas.map (applyBindings bindings)) := by
  cases schemas with
  | nil => simp only [instantiateArgsWith?,List.map_nil]
  | cons schema schemas =>
    have first := vector_instantiation_exact (operation := operation) admitted (shapes schema List.mem_cons_self) coherent.head
      (fun name member => defined name (List.mem_append_left _ member)) roots compatible
      (fun name member => declared name (List.mem_append_left _ member))
    have rest := vector_instantiation_arguments_exact (operation := operation) admitted
      (fun child member => shapes child (List.mem_cons_of_mem _ member)) coherent.tail
      (fun name member => defined name (List.mem_append_right _ member)) roots compatible
      (fun name member => declared name (List.mem_append_right _ member))
    simp only [instantiateArgsWith?,first,rest,Option.bind_eq_bind,Option.bind_some,List.map_cons]
termination_by sizeOf schemas
end

#print axioms vector_instantiation_exact
#print axioms vector_instantiation_arguments_exact

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
