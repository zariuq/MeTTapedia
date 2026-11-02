import Mettapedia.OSLF.MeTTaIL.GeneralVectorInstanceAgreement

/-! A constructor/vector instance with no free variables supplies every
input capture. Missing substitutions remain visible free variables, so an
encoded closed source cannot silently mask them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match

mutual
theorem vector_missing_visible {schema : Pattern} (shape : VectorFirstOrder schema) (assignment : Bindings)
    (name : String) (present : name ∈ schema.freeFvarNames) (missing : assignment.lookup name = none) :
    name ∈ (applyBindings assignment schema).freeFvarNames := by
  cases shape with
  | metavariable other =>
      have same : name = other := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using present
      subst other
      simp only [apply_variable, missing, Option.getD_none, Pattern.freeFvarNames, List.mem_singleton]
  | constructor label arguments children =>
      simpa only [applyBindings, Pattern.freeFvarNames] using
        vector_arguments_missing_visible children assignment name
          (by simpa only [Pattern.freeFvarNames] using present) missing
  | vector arguments children =>
      simpa only [applyBindings, List.append_nil, Pattern.freeFvarNames, Option.toList_none] using
        vector_arguments_missing_visible children assignment name
          (by simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using present) missing
termination_by sizeOf schema

theorem vector_arguments_missing_visible {schemas : List Pattern}
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema) (assignment : Bindings)
    (name : String) (present : name ∈ schemas.flatMap Pattern.freeFvarNames) (missing : assignment.lookup name = none) :
    name ∈ (schemas.map (applyBindings assignment)).flatMap Pattern.freeFvarNames := by
  obtain ⟨schema, member, present⟩ := List.mem_flatMap.mp present
  exact List.mem_flatMap.mpr ⟨applyBindings assignment schema, List.mem_map_of_mem member,
    vector_missing_visible (shapes schema member) assignment name present missing⟩
termination_by sizeOf schemas
end

theorem vector_defined_of_closed_input {schema source : Pattern} (shape : VectorFirstOrder schema) (assignment : Bindings)
    (input : applyBindings assignment schema = source) (closed : source.freeFvarNames = []) :
    Defined assignment schema.freeFvarNames := by
  intro name present
  cases found : assignment.lookup name with
  | some actual => exact ⟨actual, rfl⟩
  | none =>
      have impossible := vector_missing_visible shape assignment name present found
      rw [input, closed] at impossible
      cases impossible

#print axioms vector_defined_of_closed_input

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
