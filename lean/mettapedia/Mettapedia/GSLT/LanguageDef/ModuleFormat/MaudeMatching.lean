import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSubstitutionEncoding
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProfile

/-! The shared first-order matcher covers source substitution instances,
including repeated variables. Its returned bindings reconstruct the source
instance and every right-hand side whose variables occur on the left. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec
open GeneralFirstOrderProjection

theorem encode_firstOrder (term : Maude.Term) : FirstOrder (encode term) := by
  refine Maude.Term.rec
    (motive_1 := fun term => FirstOrder (encode term))
    (motive_2 := fun terms => ∀ pattern ∈ terms.map encode, FirstOrder pattern)
    ?_ ?_ ?_ ?_ term
  · intro name
    simpa only [encode] using FirstOrder.metavariable name
  · intro id arguments ih
    simpa only [encode] using FirstOrder.constructor id (arguments.map encode) ih
  · intro pattern member
    cases member
  · intro first rest firstIH restIH pattern member
    rcases List.mem_cons.mp member with rfl | member
    · exact firstIH
    · exact restIH pattern member

theorem encode_variables (term : Maude.Term) : (encode term).freeFvarNames = term.variables := by
  refine Maude.Term.rec
    (motive_1 := fun term => (encode term).freeFvarNames = term.variables)
    (motive_2 := fun terms => (terms.map encode).flatMap Pattern.freeFvarNames =
      terms.flatMap Maude.Term.variables)
    ?_ ?_ ?_ ?_ term
  · intro name
    simp only [encode, Pattern.freeFvarNames, Maude.Term.variables]
  · intro id arguments ih
    simpa only [encode, Pattern.freeFvarNames, Maude.Term.variables] using ih
  · rfl
  · intro first rest firstIH restIH
    simp only [List.map_cons, List.flatMap_cons, firstIH, restIH]

theorem assignmentBindings_lookup (names : List String) (assignment : Maude.Valuation)
    {name : String} (member : name ∈ names) :
    (assignmentBindings names assignment).lookup name = some (encode (assignment name)) := by
  simp only [Bindings.lookup, assignmentBindings_find names assignment member, Option.map_some]

theorem match_instance_covers (names : List String) (assignment : Maude.Valuation)
    (term : Maude.Term) (covered : ∀ name ∈ term.variables, name ∈ names) :
    ∃ bindings, bindings ∈ matchPattern (encode term) (encode (term.substitute assignment)) ∧
      Compatible (assignmentBindings names assignment) bindings ∧
      (bindings.map Prod.fst).Nodup ∧ SameNames bindings term.variables := by
  have defined : Defined (assignmentBindings names assignment) (encode term).freeFvarNames := by
    rw [encode_variables]
    intro name member
    exact ⟨encode (assignment name), assignmentBindings_lookup names assignment (covered name member)⟩
  obtain ⟨bindings, matched, compatible, unique, domain⟩ :=
    GeneralFirstOrderProjection.match_instance (assignmentBindings names assignment) (encode_firstOrder term) defined
  rw [encode_substitute names assignment term covered] at matched
  exact ⟨bindings, matchRel_complete matched, compatible, unique, (encode_variables term) ▸ domain⟩

theorem matching_reconstructs {term : Maude.Term} {target : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (encode term) target) : applyBindings bindings (encode term) = target :=
  matchPattern_correct matched (encode_firstOrder term).isMatchCorrect

theorem match_instance_readout (assignment : Maude.Valuation) (left right : Maude.Term)
    (bound : ∀ name ∈ right.variables, name ∈ left.variables) :
    ∃ bindings, bindings ∈ matchPattern (encode left) (encode (left.substitute assignment)) ∧
      applyBindings bindings (encode right) = encode (right.substitute assignment) ∧
      Compatible (assignmentBindings left.variables assignment) bindings ∧
      (bindings.map Prod.fst).Nodup ∧ SameNames bindings left.variables := by
  obtain ⟨bindings, matched, compatible, unique, names⟩ :=
    match_instance_covers left.variables assignment left (fun _ member => member)
  have recovered := compatible_readout (encode_firstOrder right) compatible (by
    intro name member
    exact (names name).mpr (bound name ((encode_variables right) ▸ member)))
  rw [encode_substitute left.variables assignment right bound] at recovered
  exact ⟨bindings, matched, recovered, compatible, unique, names⟩

theorem compatible_assignment_apply {names : List String} {assignment : Maude.Valuation}
    {bindings : Bindings} (compatible : Compatible (assignmentBindings names assignment) bindings)
    {name : String} (member : name ∈ names) (present : name ∈ bindings.map Prod.fst) :
    applyBindings bindings (.fvar name) = encode (assignment name) := by
  rw [apply_variable, compatible_lookup compatible present, assignmentBindings_lookup names assignment member]
  rfl

theorem matching_bindings_sorted (prepared : Prepared) (ambient declarations : Maude.VariableContext)
    (assignment : Maude.Valuation) (left : Maude.Term) {bindings : Bindings}
    (compatible : Compatible (assignmentBindings left.variables assignment) bindings)
    (domain : SameNames bindings left.variables)
    (distinct : (declarations.map Prod.fst).Nodup)
    (bound : ∀ name sort, (name, sort) ∈ declarations → name ∈ left.variables)
    (typed : Maude.TypedValuation prepared.source.signature ambient declarations assignment) :
    EquationSemantics.SortedBindingsIn prepared.language (freeContext ambient)
      (declarations.map fun entry => (entry.1, TypeExpr.base entry.2)) bindings := by
  intro name type member
  obtain ⟨⟨key, sort⟩, sourceMember, same⟩ := List.mem_map.mp member
  cases same
  have occurs := bound key sort sourceMember
  rw [compatible_assignment_apply compatible occurs ((domain key).mpr occurs)]
  exact ⟨encode_object _, (prepared_typing_iff prepared ambient (assignment key) sort).mpr
    (typed key sort (context_lookup_of_mem distinct sourceMember))⟩

theorem usedContext_bound {row : Maude.Row} (bound : row.inputsBound = true)
    {name sort : String} (member : (name, sort) ∈ row.usedContext) : name ∈ row.left.variables := by
  have selected : (name, sort) ∈ row.formals ∧
      name ∈ row.left.variables ++ row.right.variables ++
        row.conditions.flatMap (fun condition => condition.left.variables ++ condition.right.variables) := by
    simpa only [Maude.Row.usedContext, List.mem_filter, List.contains_iff_mem] using member
  have used : name ∈ row.left.variables ∨ name ∈ row.right.variables ++
      row.conditions.flatMap (fun condition => condition.left.variables ++ condition.right.variables) := by
    simpa only [List.mem_append, or_assoc] using selected.2
  simp only [Maude.Row.inputsBound, List.all_eq_true, List.contains_iff_mem] at bound
  exact used.elim id (bound name)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
