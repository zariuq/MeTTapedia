import Mettapedia.OSLF.MeTTaIL.GeneralVectorAddressSoundness

/-! Constructor/vector traversal records each physical occurrence once.
Repeated metavariable names retain distinct paths; a later sibling cannot
reuse a path belonging to an earlier constructor argument.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax RuleBinding GeneralRuleBindingGrammar

mutual
theorem vector_address_paths_unique {schema : Pattern} (shape : VectorFirstOrder schema)
    (site : RulePatternSite) (path : List Nat) :
    ((addresses site path schema).map Address.path).Nodup := by
  cases shape with
  | metavariable name => simp [addresses]
  | constructor label arguments children =>
      simpa only [addresses] using vector_argument_paths_unique children site path 0
  | vector elements children =>
      simpa only [addresses, Option.toList_none, List.map_nil, List.append_nil] using
        vector_argument_paths_unique children site path 0
termination_by sizeOf schema

theorem vector_argument_paths_unique {schemas : List Pattern}
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) :
    ((argumentAddresses site path offset schemas).map Address.path).Nodup := by
  cases schemas with
  | nil => simp [argumentAddresses]
  | cons first rest =>
      simp only [argumentAddresses, List.map_append]
      apply List.Nodup.append
      · exact vector_address_paths_unique (shapes first List.mem_cons_self) site (path ++ [offset])
      · exact vector_argument_paths_unique
          (fun child member => shapes child (List.mem_cons_of_mem first member)) site path (offset + 1)
      · apply List.disjoint_left.mpr
        intro address firstMember laterMember
        obtain ⟨firstAddress, firstAt, firstSame⟩ := List.mem_map.mp firstMember
        obtain ⟨laterAddress, laterAt, laterSame⟩ := List.mem_map.mp laterMember
        obtain ⟨firstSuffix, firstPath, _⟩ := vector_address_sound
          (shapes first List.mem_cons_self) site (path ++ [offset]) firstAddress firstAt
        obtain ⟨index, laterSuffix, _, laterPath, _⟩ := vector_argument_address_sound
          (fun child member => shapes child (List.mem_cons_of_mem first member)) site path (offset + 1) laterAddress laterAt
        have same : path ++ offset :: firstSuffix = path ++ ((offset + 1) + index) :: laterSuffix := by
          simpa only [List.append_assoc, List.singleton_append] using
            firstPath.symm.trans (firstSame.trans (laterSame.symm.trans laterPath))
        have heads := (List.cons.inj (List.append_cancel_left same)).1
        omega
termination_by sizeOf schemas
end

#print axioms vector_address_paths_unique
#print axioms vector_argument_paths_unique

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
