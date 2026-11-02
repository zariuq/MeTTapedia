import Mettapedia.OSLF.MeTTaIL.GeneralVectorLocationTyping
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammarFirstOrder

/-! Every free input name in a constructor/vector schema has an actual
recorded inference address. Successful inspection retains its context and
source occurrence rather than merely the inferred name table.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding
open GeneralRuleBindingGrammar

mutual
theorem vector_name_address {schema : Pattern} (shape : VectorFirstOrder schema) (name : String)
    (present : name ∈ schema.freeFvarNames) (site : RulePatternSite) (path : List Nat) :
    ∃ address ∈ addresses site path schema, address.name = name := by
  cases shape with
  | metavariable actual =>
      have same : name = actual := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using present
      exact ⟨⟨actual, site, path⟩, by simp only [addresses, List.mem_singleton], same.symm⟩
  | constructor label arguments children =>
      simpa only [addresses] using vector_arguments_name_address children name
        (by simpa only [Pattern.freeFvarNames] using present) site path 0
  | vector arguments children =>
      obtain ⟨address, member, same⟩ := vector_arguments_name_address children name
        (by simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using present) site path 0
      exact ⟨address, by simpa only [addresses] using List.mem_append_left _ member, same⟩
termination_by sizeOf schema

theorem vector_arguments_name_address {schemas : List Pattern}
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema) (name : String)
    (present : name ∈ schemas.flatMap Pattern.freeFvarNames) (site : RulePatternSite) (path : List Nat) (index : Nat) :
    ∃ address ∈ argumentAddresses site path index schemas, address.name = name := by
  cases schemas with
  | nil => cases present
  | cons first rest =>
      rcases List.mem_append.mp present with here | later
      · obtain ⟨address, member, same⟩ := vector_name_address (shapes first List.mem_cons_self) name here site (path ++ [index])
        exact ⟨address, by simpa only [argumentAddresses] using List.mem_append_left _ member, same⟩
      · obtain ⟨address, member, same⟩ := vector_arguments_name_address
          (fun child member => shapes child (List.mem_cons_of_mem first member)) name later site path (index + 1)
        exact ⟨address, by simpa only [argumentAddresses] using List.mem_append_right _ member, same⟩
termination_by sizeOf schemas
end

theorem option_mapM_member_image {α β : Type} (inputs : List α) (emit : α → Option β) (outputs : List β)
    (read : inputs.mapM emit = some outputs) (input : α) (present : input ∈ inputs) :
    ∃ output ∈ outputs, emit input = some output := by
  induction inputs generalizing outputs with
  | nil => cases present
  | cons first rest ih =>
      cases firstRead : emit first with
      | none => simp [List.mapM_cons, firstRead] at read
      | some firstOutput =>
          cases restRead : rest.mapM emit with
          | none => simp [List.mapM_cons, firstRead, restRead] at read
          | some remaining =>
              have same : firstOutput :: remaining = outputs := by simpa [List.mapM_cons, firstRead, restRead] using read
              subst outputs
              rcases List.mem_cons.mp present with rfl | later
              · exact ⟨firstOutput, List.mem_cons_self, firstRead⟩
              · obtain ⟨output, member, found⟩ := ih remaining restRead later
                exact ⟨output, List.mem_cons_of_mem firstOutput member, found⟩

theorem inspect_name_covered {language : LanguageDef} {context : List (String × TypeExpr)} {schema : Pattern}
    {expected : TypeExpr} {rows : List Occurrence} (shape : VectorFirstOrder schema)
    (read : inspect language context .left [] expected schema = some rows) (name : String)
    (present : name ∈ schema.freeFvarNames) :
    ∃ row ∈ rows, row.name = name ∧ row.bound = [] ∧
      contextAt? language context [] expected schema row.path = some ([], row.result) := by
  obtain ⟨address, member, named⟩ := vector_name_address shape name present .left []
  obtain ⟨row, rowMember, rowRead⟩ := option_mapM_member_image _ _ rows read address member
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at rowRead
  obtain ⟨⟨bound, result⟩, found, same⟩ := rowRead
  change some (Occurrence.mk address bound result) = some row at same
  cases Option.some.inj same
  have noBinders := GeneralRuleBindingGrammar.contextAt?_binderFree language context [] expected schema address.path bound result
    (GeneralRuleBindingInference.vector_binderFree shape) found
  subst bound
  exact ⟨_, rowMember, named, rfl, found⟩

#print axioms inspect_name_covered

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
