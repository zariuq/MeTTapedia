import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderMatch

/-! Constructor and fixed-vector instances have ordinary relational matches.
Repeated metavariables constrain one substitution, including inside tuples. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match MatchSpec

inductive VectorFirstOrder : Pattern → Prop where
  | metavariable (name : String) : VectorFirstOrder (.fvar name)
  | constructor (label : String) (arguments : List Pattern)
      (children : ∀ argument ∈ arguments, VectorFirstOrder argument) : VectorFirstOrder (.apply label arguments)
  | vector (arguments : List Pattern)
      (children : ∀ argument ∈ arguments, VectorFirstOrder argument) : VectorFirstOrder (.collection .vec arguments none)

mutual
  theorem vector_match_instance (environment : Bindings) {schema : Pattern}
      (shape : VectorFirstOrder schema) (defined : Defined environment schema.freeFvarNames) :
      ∃ bindings, MatchRel schema (applyBindings environment schema) bindings ∧
        Compatible environment bindings ∧ (bindings.map Prod.fst).Nodup ∧
        SameNames bindings schema.freeFvarNames := by
    cases shape with
    | metavariable name => exact match_instance environment (.metavariable name) defined
    | constructor label arguments children =>
      obtain ⟨bindings,matched,compatible,unique,names⟩ := vector_arguments_instance environment children
        (by simpa only [Pattern.freeFvarNames] using defined)
      refine ⟨bindings,?_,compatible,unique,?_⟩
      · simpa only [applyBindings] using (MatchRel.apply matched (by simp) :
          MatchRel (.apply label arguments) (.apply label (arguments.map (applyBindings environment))) bindings)
      · simpa only [Pattern.freeFvarNames] using names
    | vector arguments children =>
      obtain ⟨bindings,matched,compatible,unique,names⟩ := vector_arguments_instance environment children
        (by simpa only [Pattern.freeFvarNames,Option.toList_none,List.append_nil] using defined)
      refine ⟨bindings,?_,compatible,unique,?_⟩
      · simpa only [applyBindings,List.append_nil] using (MatchRel.vector matched :
          MatchRel (.collection .vec arguments none) (.collection .vec (arguments.map (applyBindings environment)) none) bindings)
      · simpa only [Pattern.freeFvarNames,Option.toList_none,List.append_nil] using names
  termination_by sizeOf schema

  theorem vector_arguments_instance (environment : Bindings) {schemas : List Pattern}
      (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema)
      (defined : Defined environment (schemas.flatMap Pattern.freeFvarNames)) :
      ∃ bindings, MatchArgsRel schemas (schemas.map (applyBindings environment)) bindings ∧
        Compatible environment bindings ∧ (bindings.map Prod.fst).Nodup ∧
        SameNames bindings (schemas.flatMap Pattern.freeFvarNames) := by
    cases schemas with
    | nil => exact ⟨[],.nil,by simp [Compatible],by simp,by simp [SameNames]⟩
    | cons schema schemas =>
      obtain ⟨first,firstMatch,firstCompatible,firstUnique,firstNames⟩ := vector_match_instance environment
        (shapes schema List.mem_cons_self) (fun name member => defined name (List.mem_append_left _ member))
      obtain ⟨rest,restMatch,restCompatible,_,restNames⟩ := vector_arguments_instance environment
        (fun child member => shapes child (List.mem_cons_of_mem _ member))
        (fun name member => defined name (List.mem_append_right _ member))
      obtain ⟨combined,merged,compatible,unique,names⟩ := merge_compatible environment first rest firstCompatible restCompatible firstUnique
      refine ⟨combined,.cons firstMatch restMatch merged,compatible,unique,?_⟩
      intro name
      rw [names,firstNames,restNames]
      simp only [List.flatMap_cons,List.mem_append]
  termination_by sizeOf schemas
end

namespace VectorInstanceControls

def repeated : Pattern := .collection .vec [.fvar "X",.fvar "X"] none

theorem equal_occurrences_match :
    (matchPattern repeated (.collection .vec [.apply "A" [],.apply "A" []] none)).isEmpty = false := by decide +kernel

theorem unequal_occurrences_refused :
    (matchPattern repeated (.collection .vec [.apply "A" [],.apply "B" []] none)).isEmpty = true := by decide +kernel

theorem binder_outside_profile : ¬ VectorFirstOrder (.lambda none (.bvar 0)) := by
  intro shape
  cases shape

end VectorInstanceControls

#print axioms vector_match_instance
#print axioms vector_arguments_instance
#print axioms VectorInstanceControls.equal_occurrences_match
#print axioms VectorInstanceControls.unequal_occurrences_refused
#print axioms VectorInstanceControls.binder_outside_profile

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
