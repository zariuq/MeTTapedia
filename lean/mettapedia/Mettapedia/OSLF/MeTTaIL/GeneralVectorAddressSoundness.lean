import Mettapedia.OSLF.MeTTaIL.GeneralVectorOccurrenceCoverage

/-! Every inference address recorded from a constructor/vector schema
selects the recorded metavariable in that schema. Child indexes and path
prefixes retain their authored order.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding GeneralRuleBindingGrammar

mutual
theorem vector_address_sound {schema : Pattern} (shape : VectorFirstOrder schema)
    (site : RulePatternSite) (path : List Nat) (address : Address) (member : address ∈ addresses site path schema) :
    ∃ suffix, address.path = path ++ suffix ∧ occurrenceAt? schema suffix = some address.name := by
  cases shape with
  | metavariable name =>
      have same : address = ⟨name, site, path⟩ := by simpa only [addresses, List.mem_singleton] using member
      subst address
      exact ⟨[], by simp, rfl⟩
  | constructor label arguments children =>
      obtain ⟨index, suffix, _, same, found⟩ := vector_argument_address_sound children site path 0 address
        (by simpa only [addresses] using member)
      refine ⟨index :: suffix, by simpa only [Nat.zero_add] using same, ?_⟩
      simpa only [occurrenceAt?] using found
  | vector arguments children =>
      have inside : address ∈ argumentAddresses site path 0 arguments := by
        simpa only [addresses, Option.toList_none, List.map_nil, List.append_nil] using member
      obtain ⟨index, suffix, selected, same, found⟩ := vector_argument_address_sound children site path 0 address inside
      refine ⟨index :: suffix, by simpa only [Nat.zero_add] using same, ?_⟩
      have before : index < arguments.length := by simpa using selected
      simpa only [occurrenceAt?, before, if_true] using found
termination_by sizeOf schema

theorem vector_argument_address_sound {schemas : List Pattern}
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema) (site : RulePatternSite) (path : List Nat)
    (offset : Nat) (address : Address) (member : address ∈ argumentAddresses site path offset schemas) :
    ∃ index suffix, schemas[index]?.isSome = true ∧
      address.path = path ++ (offset + index) :: suffix ∧
      ((schemas[index]?).bind (occurrenceAt? · suffix)) = some address.name := by
  cases schemas with
  | nil => simp only [argumentAddresses, List.not_mem_nil] at member
  | cons first rest =>
      simp only [argumentAddresses, List.mem_append] at member
      rcases member with here | later
      · obtain ⟨suffix, same, found⟩ := vector_address_sound (shapes first List.mem_cons_self) site (path ++ [offset]) address here
        exact ⟨0, suffix, rfl, by simpa only [Nat.add_zero, List.append_assoc, List.singleton_append] using same, found⟩
      · obtain ⟨index, suffix, selected, same, found⟩ := vector_argument_address_sound
          (fun child present => shapes child (List.mem_cons_of_mem first present)) site path (offset + 1) address later
        refine ⟨index + 1, suffix, selected, ?_, found⟩
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using same
termination_by sizeOf schemas
end

#print axioms vector_address_sound

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
