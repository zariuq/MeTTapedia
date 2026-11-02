import Mettapedia.OSLF.MeTTaIL.GeneralVectorMatchInstance

/-! Restriction keeps the original binding order and every lookup at a used
name. Compiled constructor/vector instances are unchanged when all their
metavariables remain in the retained domain. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match

def restrictBindings (names : List String) (bindings : Bindings) : Bindings :=
  bindings.filter fun entry => names.contains entry.1

theorem restricted_lookup (names : List String) (bindings : Bindings) (name : String)
    (present : name ∈ names) : (restrictBindings names bindings).lookup name = bindings.lookup name := by
  have predicate : (fun entry : String × Pattern => decide (names.contains entry.1 = true ∧ (entry.1 == name) = true)) =
      (fun entry => entry.1 == name) := by
    funext entry
    by_cases same : entry.1 = name
    · simp [same,present]
    · simp [same]
  simp only [restrictBindings,Bindings.lookup,List.find?_filter]
  rw [predicate]

mutual
 theorem restricted_vector_instance (names : List String) (bindings : Bindings) {schema : Pattern}
    (shape : VectorFirstOrder schema) (included : ∀ name ∈ schema.freeFvarNames, name ∈ names) :
    applyBindings (restrictBindings names bindings) schema = applyBindings bindings schema := by
  cases shape with
  | metavariable name => rw [apply_variable,apply_variable,restricted_lookup names bindings name (included name (by simp [Pattern.freeFvarNames]))]
  | constructor label arguments children =>
    have same := restricted_vector_arguments names bindings children (by simpa only [Pattern.freeFvarNames] using included)
    simpa only [applyBindings] using congrArg (Pattern.apply label) same
  | vector arguments children =>
    have same := restricted_vector_arguments names bindings children (by
      simpa only [Pattern.freeFvarNames,Option.toList_none,List.append_nil] using included)
    simpa only [applyBindings,List.append_nil] using congrArg (fun values => Pattern.collection .vec values none) same
 termination_by sizeOf schema

 theorem restricted_vector_arguments (names : List String) (bindings : Bindings) {schemas : List Pattern}
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema)
    (included : ∀ name ∈ schemas.flatMap Pattern.freeFvarNames, name ∈ names) :
    schemas.map (applyBindings (restrictBindings names bindings)) = schemas.map (applyBindings bindings) := by
  cases schemas with
  | nil => rfl
  | cons schema schemas =>
    have first := restricted_vector_instance names bindings (shapes schema List.mem_cons_self)
      (fun name member => included name (List.mem_append_left _ member))
    have rest := restricted_vector_arguments names bindings
      (fun child member => shapes child (List.mem_cons_of_mem _ member))
      (fun name member => included name (List.mem_append_right _ member))
    exact congrArg₂ List.cons first rest
 termination_by sizeOf schemas
end

#print axioms restricted_lookup
#print axioms restricted_vector_instance

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
