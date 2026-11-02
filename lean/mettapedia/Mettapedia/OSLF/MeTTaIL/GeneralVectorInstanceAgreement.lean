import Mettapedia.OSLF.MeTTaIL.GeneralVectorMatchInstance

/-! Substitutions giving the same constructor/vector input agree at every
hole that input observes. Any output using only those holes is identical.
The statement compares substituted values, not binding-list order.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match

mutual
theorem vector_input_agreement {schema : Pattern} (shape : VectorFirstOrder schema)
    (first second : Bindings) (same : applyBindings first schema = applyBindings second schema) :
    ∀ name ∈ schema.freeFvarNames, applyBindings first (.fvar name) = applyBindings second (.fvar name) := by
  cases shape with
  | metavariable name =>
    intro actual member
    have equal : actual = name := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using member
    simpa only [equal] using same
  | constructor label arguments children =>
    have mapped := (Pattern.apply.inj (by simpa only [applyBindings] using same)).2
    simpa only [Pattern.freeFvarNames] using vector_arguments_input_agreement children first second mapped
  | vector arguments children =>
    have mapped := (Pattern.collection.inj (by simpa only [applyBindings, List.append_nil] using same)).2.1
    simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using
      vector_arguments_input_agreement children first second mapped
termination_by sizeOf schema

theorem vector_arguments_input_agreement {schemas : List Pattern}
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema) (first second : Bindings)
    (same : schemas.map (applyBindings first) = schemas.map (applyBindings second)) :
    ∀ name ∈ schemas.flatMap Pattern.freeFvarNames,
      applyBindings first (.fvar name) = applyBindings second (.fvar name) := by
  cases schemas with
  | nil => intro name impossible; cases impossible
  | cons schema rest =>
    have both := List.cons.inj same
    intro name member
    rcases List.mem_append.mp member with here | later
    · exact vector_input_agreement (shapes schema List.mem_cons_self) first second both.1 name here
    · exact vector_arguments_input_agreement (fun child member => shapes child (List.mem_cons_of_mem schema member))
        first second both.2 name later
termination_by sizeOf schemas
end

mutual
theorem vector_output_agreement {schema : Pattern} (shape : VectorFirstOrder schema)
    (first second : Bindings)
    (same : ∀ name ∈ schema.freeFvarNames, applyBindings first (.fvar name) = applyBindings second (.fvar name)) :
    applyBindings first schema = applyBindings second schema := by
  cases shape with
  | metavariable name => exact same name (by simp [Pattern.freeFvarNames])
  | constructor label arguments children =>
    have mapped := vector_arguments_output_agreement children first second (by
      simpa only [Pattern.freeFvarNames] using same)
    simpa only [applyBindings] using congrArg (Pattern.apply label) mapped
  | vector arguments children =>
    have mapped := vector_arguments_output_agreement children first second (by
      simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using same)
    simpa only [applyBindings, List.append_nil] using
      congrArg (fun items => Pattern.collection .vec items none) mapped
termination_by sizeOf schema

theorem vector_arguments_output_agreement {schemas : List Pattern}
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema) (first second : Bindings)
    (same : ∀ name ∈ schemas.flatMap Pattern.freeFvarNames,
      applyBindings first (.fvar name) = applyBindings second (.fvar name)) :
    schemas.map (applyBindings first) = schemas.map (applyBindings second) := by
  cases schemas with
  | nil => rfl
  | cons schema rest =>
    have head := vector_output_agreement (shapes schema List.mem_cons_self) first second
      (fun name member => same name (List.mem_append_left _ member))
    have tail := vector_arguments_output_agreement
      (fun child member => shapes child (List.mem_cons_of_mem schema member)) first second
      (fun name member => same name (List.mem_append_right _ member))
    simp only [List.map_cons, head, tail]
termination_by sizeOf schemas
end

theorem vector_rule_output_unique {left right : Pattern} (input : VectorFirstOrder left)
    (output : VectorFirstOrder right) (bound : ∀ name ∈ right.freeFvarNames, name ∈ left.freeFvarNames)
    (first second : Bindings) (same : applyBindings first left = applyBindings second left) :
    applyBindings first right = applyBindings second right :=
  vector_output_agreement output first second
    (fun name member => vector_input_agreement input first second same name (bound name member))

#print axioms vector_rule_output_unique

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
