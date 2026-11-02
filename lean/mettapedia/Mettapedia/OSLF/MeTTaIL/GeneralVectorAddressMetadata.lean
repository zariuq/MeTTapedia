import Mettapedia.OSLF.MeTTaIL.GeneralVectorAddressUniqueness
import Mettapedia.Data.List.OptionMapM

/-! Successful grammar inspection preserves the source addresses exactly.
Constructor/vector occurrences retain their site and cross no binders.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax RuleBinding GeneralRuleBindingGrammar

mutual
theorem vector_address_site {schema : Pattern} (shape : VectorFirstOrder schema)
    (site : RulePatternSite) (path : List Nat) (address : Address)
    (member : address ∈ addresses site path schema) : address.site = site := by
  cases shape with
  | metavariable name =>
      have same : address = ⟨name, site, path⟩ := by simpa only [addresses, List.mem_singleton] using member
      exact congrArg Address.site same
  | constructor label arguments children =>
      exact vector_argument_address_site children site path 0 address (by simpa only [addresses] using member)
  | vector elements children =>
      exact vector_argument_address_site children site path 0 address
        (by simpa only [addresses, Option.toList_none, List.map_nil, List.append_nil] using member)
termination_by sizeOf schema

theorem vector_argument_address_site {schemas : List Pattern}
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema) (site : RulePatternSite)
    (path : List Nat) (offset : Nat) (address : Address)
    (member : address ∈ argumentAddresses site path offset schemas) : address.site = site := by
  cases schemas with
  | nil => simp only [argumentAddresses, List.not_mem_nil] at member
  | cons first rest =>
      simp only [argumentAddresses] at member
      rcases List.mem_append.mp member with here | later
      · exact vector_address_site (shapes first List.mem_cons_self) site (path ++ [offset]) address here
      · exact vector_argument_address_site (fun child present => shapes child (List.mem_cons_of_mem first present))
          site path (offset + 1) address later
termination_by sizeOf schemas
end

theorem vector_occurrence_depth {schema : Pattern} (shape : VectorFirstOrder schema)
    (path : List Nat) (name : String) (depth : Nat) (found : occurrenceAt? schema path = some name) :
    occurrenceDepthAt? schema path depth = some depth := by
  induction path generalizing schema with
  | nil => cases shape <;> simp_all [occurrenceAt?, occurrenceDepthAt?]
  | cons index rest ih =>
      cases shape with
      | metavariable => cases found
      | constructor label arguments children =>
          obtain ⟨child, selected, remaining⟩ := Option.bind_eq_some_iff.mp found
          simp only [occurrenceDepthAt?, selected, Option.bind_some]
          exact ih (children child (List.mem_of_getElem? selected)) remaining
      | vector elements children =>
          simp only [occurrenceAt?] at found
          split at found
          next inside =>
            obtain ⟨child, selected, remaining⟩ := Option.bind_eq_some_iff.mp found
            simp only [occurrenceDepthAt?, inside, if_true, selected, Option.bind_some]
            exact ih (children child (List.mem_of_getElem? selected)) remaining
          next outside => split at found <;> cases found

theorem inspect_address_projection (language : LanguageDef) (context : List (String × TypeExpr))
    (site : RulePatternSite) (bound : List TypeExpr) (expected : TypeExpr) (schema : Pattern)
    (rows : List Occurrence) (read : inspect language context site bound expected schema = some rows) :
    rows.map Occurrence.toAddress = addresses site [] schema := by
  have projected := Mettapedia.Data.List.option_mapM_projection _ _ rows id Occurrence.toAddress read (by
    intro address row computed
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at computed
    obtain ⟨⟨localBound, result⟩, _, same⟩ := computed
    change some (Occurrence.mk address localBound result) = some row at same
    cases Option.some.inj same
    rfl)
  simpa only [List.map_id] using projected

theorem inspect_origin (language : LanguageDef) (context : List (String × TypeExpr))
    (site : RulePatternSite) (bound : List TypeExpr) (expected : TypeExpr) (schema : Pattern)
    (rows : List Occurrence) (read : inspect language context site bound expected schema = some rows)
    (row : Occurrence) (member : row ∈ rows) :
    row.toAddress ∈ addresses site [] schema ∧
      contextAt? language context bound expected schema row.path = some (row.bound, row.result) := by
  obtain ⟨address, present, computed⟩ := Mettapedia.Data.List.option_mapM_origin _ _ rows read row member
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at computed
  obtain ⟨⟨localBound, result⟩, located, same⟩ := computed
  change some (Occurrence.mk address localBound result) = some row at same
  cases Option.some.inj same
  exact ⟨present, located⟩

#print axioms vector_address_site
#print axioms vector_occurrence_depth
#print axioms inspect_address_projection
#print axioms inspect_origin

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
