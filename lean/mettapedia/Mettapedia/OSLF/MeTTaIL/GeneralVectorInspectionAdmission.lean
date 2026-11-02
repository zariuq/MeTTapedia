import Mettapedia.OSLF.MeTTaIL.GeneralNullarySpecificationAdmission

/-! Successful inspection of both constructor/vector sides supplies the
physical occurrence checks required by the original binding admission.
Capture-context uniqueness and coverage remain explicit here.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax RuleBinding GeneralFirstOrderProjection

theorem inspect_paths_unique (language : LanguageDef) (context : List (String × TypeExpr))
    (site : RulePatternSite) (expected : TypeExpr) (schema : Pattern) (rows : List Occurrence)
    (shape : VectorFirstOrder schema) (read : inspect language context site [] expected schema = some rows) :
    (rows.map (fun row => row.path)).Nodup := by
  have addresses := inspect_address_projection language context site [] expected schema rows read
  have projected := congrArg (List.map Address.path) addresses
  have same : rows.map (fun row => row.path) = (GeneralRuleBindingGrammar.addresses site [] schema).map Address.path := by
    simpa only [List.map_map, Function.comp_def] using projected
  rw [same]
  exact vector_address_paths_unique shape site []

theorem inspect_site (language : LanguageDef) (context : List (String × TypeExpr))
    (site : RulePatternSite) (expected : TypeExpr) (schema : Pattern) (rows : List Occurrence)
    (shape : VectorFirstOrder schema) (read : inspect language context site [] expected schema = some rows)
    (row : Occurrence) (member : row ∈ rows) : row.site = site :=
  vector_address_site shape site [] row.toAddress (inspect_origin language context site [] expected schema rows read row member).1

theorem inspect_rule_occurrence (language : LanguageDef) (context : List (String × TypeExpr))
    (rule : RewriteRule) (site : RulePatternSite) (expected : TypeExpr) (schema : Pattern) (rows : List Occurrence)
    (shape : VectorFirstOrder schema) (read : inspect language context site [] expected schema = some rows)
    (selected : sitePattern? rule site = some schema) (unbound : siteBinderDepth? rule site = some 0)
    (row : Occurrence) (member : row ∈ rows) :
    occurrenceDeclared rule ⟨row.name, row.site, row.path, []⟩ = true ∧
      occurrenceDepthAtSite? rule row.site row.path = some 0 := by
  have origin := inspect_origin language context site [] expected schema rows read row member
  have sameSite := inspect_site language context site expected schema rows shape read row member
  obtain ⟨suffix, samePath, actual⟩ := vector_address_sound shape site [] row.toAddress origin.1
  have found : occurrenceAt? schema row.path = some row.name := by
    simpa only [List.nil_append] using (samePath ▸ actual)
  constructor
  · simp only [occurrenceDeclared, sameSite, selected, Option.bind_some, found, beq_self_eq_true]
  · simp only [occurrenceDepthAtSite?, sameSite, unbound, selected]
    exact vector_occurrence_depth shape row.path row.name 0 found

theorem inspected_specification_admitted (language : LanguageDef) (rule : RewriteRule)
    (context : List (String × TypeExpr)) (expected : TypeExpr) (leftRows rightRows : List Occurrence)
    (leftShape : VectorFirstOrder rule.left) (rightShape : VectorFirstOrder rule.right)
    (leftRead : inspect language rule.typeContext .left [] expected rule.left = some leftRows)
    (rightRead : inspect language rule.typeContext .right [] expected rule.right = some rightRows)
    (unique : (context.map Prod.fst).Nodup)
    (covered : ∀ row ∈ leftRows ++ rightRows, row.name ∈ context.map Prod.fst) :
    admittedFor {rule with typeContext := context} (specification context (leftRows ++ rightRows)) = true := by
  have empty : ∀ row ∈ leftRows ++ rightRows, row.bound = [] := by
    intro row member
    rcases List.mem_append.mp member with first | last
    · exact inspect_binderFree language rule.typeContext .left [] expected rule.left leftRows
        (GeneralRuleBindingInference.vector_binderFree leftShape) leftRead row first
    · exact inspect_binderFree language rule.typeContext .right [] expected rule.right rightRows
        (GeneralRuleBindingInference.vector_binderFree rightShape) rightRead row last
  have keys : ((leftRows ++ rightRows).map fun row => (row.name, row.site, row.path)).Nodup := by
    rw [List.map_append]
    apply List.Nodup.append
    · apply List.Nodup.of_map (fun key => key.2.2)
      simpa only [List.map_map, Function.comp_def] using
        inspect_paths_unique language rule.typeContext .left expected rule.left leftRows leftShape leftRead
    · apply List.Nodup.of_map (fun key => key.2.2)
      simpa only [List.map_map, Function.comp_def] using
        inspect_paths_unique language rule.typeContext .right expected rule.right rightRows rightShape rightRead
    · apply List.disjoint_left.mpr
      intro key first last
      obtain ⟨firstRow, firstMember, firstKey⟩ := List.mem_map.mp first
      obtain ⟨lastRow, lastMember, lastKey⟩ := List.mem_map.mp last
      have firstSite := inspect_site language rule.typeContext .left expected rule.left leftRows leftShape leftRead firstRow firstMember
      have lastSite := inspect_site language rule.typeContext .right expected rule.right rightRows rightShape rightRead lastRow lastMember
      have same := congrArg (fun key => key.2.1) (firstKey.trans lastKey.symm)
      rw [firstSite, lastSite] at same
      cases same
  apply nullary_specification_admitted rule context (leftRows ++ rightRows) empty unique keys covered
  · intro row member
    rcases List.mem_append.mp member with first | last
    · exact (inspect_rule_occurrence language rule.typeContext rule .left expected rule.left leftRows
        leftShape leftRead rfl rfl row first).1
    · exact (inspect_rule_occurrence language rule.typeContext rule .right expected rule.right rightRows
        rightShape rightRead rfl rfl row last).1
  · intro row member
    rcases List.mem_append.mp member with first | last
    · exact (inspect_rule_occurrence language rule.typeContext rule .left expected rule.left leftRows
        leftShape leftRead rfl rfl row first).2
    · exact (inspect_rule_occurrence language rule.typeContext rule .right expected rule.right rightRows
        rightShape rightRead rfl rfl row last).2

#print axioms inspect_paths_unique
#print axioms inspect_rule_occurrence
#print axioms inspected_specification_admitted

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar
