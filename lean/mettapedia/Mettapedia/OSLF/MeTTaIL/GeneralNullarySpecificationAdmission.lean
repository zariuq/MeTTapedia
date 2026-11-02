import Mettapedia.OSLF.MeTTaIL.GeneralVectorAddressMetadata
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderScopedInstance

/-! A grammar-derived nullary specification is admitted when its capture
names are unique, its physical occurrence keys are unique and its recorded
sites are actual unbound occurrences of the authored rule.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax RuleBinding GeneralFirstOrderProjection

theorem dependencyRows_zero (context : List (String × TypeExpr)) (rows : List Occurrence)
    (empty : ∀ row ∈ rows, row.bound = []) :
    dependencyRows context rows = context.map (fun entry => (entry.1, ([] : List TypeExpr))) := by
  apply List.map_congr_left
  intro entry _
  cases found : rows.find? (fun row => row.name == entry.1) with
  | none => rfl
  | some row => simp only [Option.map_some, empty row (List.mem_of_find?_eq_some found), Option.getD_some]

theorem specification_dependencies_zero (rule : RewriteRule) (context : List (String × TypeExpr))
    (rows : List Occurrence) (empty : ∀ row ∈ rows, row.bound = [])
    (unique : (context.map Prod.fst).Nodup) (name : String) (member : name ∈ context.map Prod.fst) :
    dependencies? (specification context rows) name = some [] := by
  obtain ⟨entry, present, same⟩ := List.mem_map.mp member
  have existsType : (context.lookup name).isSome := List.lookup_isSome_iff.mpr
    ⟨entry, present, by simp [same]⟩
  obtain ⟨type, found⟩ := Option.isSome_iff_exists.mp existsType
  have inferred := inferred_dependencies_of_lookup (rule := {rule with typeContext := context}) unique found
  simpa only [dependencies?, specification, dependencyRows_zero context rows empty,
    GeneralRuleBindingInference.inferredSpec] using inferred

theorem nullary_specification_admitted (rule : RewriteRule) (context : List (String × TypeExpr))
    (rows : List Occurrence) (empty : ∀ row ∈ rows, row.bound = [])
    (unique : (context.map Prod.fst).Nodup)
    (keys : (rows.map fun row => (row.name, row.site, row.path)).Nodup)
    (covered : ∀ row ∈ rows, row.name ∈ context.map Prod.fst)
    (actual : ∀ row ∈ rows, occurrenceDeclared rule ⟨row.name, row.site, row.path, []⟩ = true)
    (depth : ∀ row ∈ rows, occurrenceDepthAtSite? rule row.site row.path = some 0) :
    admittedFor {rule with typeContext := context} (specification context rows) = true := by
  have dependencyNames : ((specification context rows).dependencies.map Prod.fst).Nodup := by
    simpa only [specification, dependencyRows_zero context rows empty, List.map_map, Function.comp_def] using unique
  have occurrenceKeys : ((specification context rows).occurrences.map fun row => (row.name, row.site, row.path)).Nodup := by
    simpa only [specification, List.map_map, Function.comp_def] using keys
  have lengths : (context.length == (specification context rows).dependencies.length) = true := by
    simp [specification, dependencyRows]
  have declared : context.all (fun entry => (specification context rows).dependencies.any
      (fun declared => declared.1 == entry.1)) = true := by
    apply List.all_eq_true.mpr
    intro entry present
    apply List.any_eq_true.mpr
    rw [show (specification context rows).dependencies = context.map (fun entry => (entry.1, ([] : List TypeExpr))) from
      dependencyRows_zero context rows empty]
    exact ⟨(entry.1, []), List.mem_map.mpr ⟨entry, present, rfl⟩, by simp⟩
  have occurrences : (specification context rows).occurrences.all (fun row =>
      occurrenceDeclared {rule with typeContext := context} row &&
        match dependencies? (specification context rows) row.name,
          occurrenceDepthAtSite? {rule with typeContext := context} row.site row.path with
        | some dependencies, some depth => row.arguments.length == dependencies.length &&
            row.arguments.all (fun argument => argument.isGroundAt depth)
        | _, _ => false) = true := by
    apply List.all_eq_true.mpr
    intro occurrence member
    obtain ⟨row, present, same⟩ := List.mem_map.mp member
    subst occurrence
    simp only [empty row present, List.length_nil, List.range_zero, List.map_nil]
    change (occurrenceDeclared rule ⟨row.name, row.site, row.path, []⟩ &&
      match dependencies? (specification context rows) row.name, occurrenceDepthAtSite? rule row.site row.path with
      | some dependencies, some depth => ([] : List Pattern).length == dependencies.length && ([] : List Pattern).all (fun argument => argument.isGroundAt depth)
      | _, _ => false) = true
    rw [actual row present, depth row present,
      specification_dependencies_zero rule context rows empty unique row.name (covered row present)]
    rfl
  simp only [admittedFor, unique, dependencyNames, occurrenceKeys, decide_true, lengths, declared,
    Bool.and_self, Bool.true_and]
  exact occurrences

#print axioms dependencyRows_zero
#print axioms specification_dependencies_zero
#print axioms nullary_specification_admitted

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar
