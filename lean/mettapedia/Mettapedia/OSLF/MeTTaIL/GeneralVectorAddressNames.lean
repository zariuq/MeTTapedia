import Mettapedia.OSLF.MeTTaIL.GeneralVectorMatchInstance

/-! Address discovery on constructor/vector schemas records exactly their
free metavariable occurrences, in authored order. Closed constants therefore
require no grammar descent during binding inference.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax GeneralFirstOrderProjection

mutual
theorem vector_address_names {pattern : Pattern} (shape : VectorFirstOrder pattern)
    (site : RulePatternSite) (path : List Nat) :
    (addresses site path pattern).map Address.name = pattern.freeFvarNames := by
  cases shape with
  | metavariable name => simp only [addresses, Pattern.freeFvarNames, List.map_cons, List.map_nil]
  | constructor label arguments children =>
    simpa only [addresses, Pattern.freeFvarNames] using vector_argument_address_names children site path 0
  | vector arguments children =>
    simpa only [addresses, Option.toList_none, List.map_nil, List.append_nil, Pattern.freeFvarNames,
      List.nil_append, List.append_nil] using vector_argument_address_names children site path 0
termination_by sizeOf pattern

theorem vector_argument_address_names {arguments : List Pattern}
    (children : ∀ argument ∈ arguments, VectorFirstOrder argument)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) :
    (argumentAddresses site path offset arguments).map Address.name = arguments.flatMap Pattern.freeFvarNames := by
  cases arguments with
  | nil => simp only [argumentAddresses, List.map_nil, List.flatMap_nil]
  | cons head tail =>
    simp only [argumentAddresses, List.map_append, List.flatMap_cons]
    rw [vector_address_names (children head List.mem_cons_self),
      vector_argument_address_names (fun child member => children child (List.mem_cons_of_mem head member))]
termination_by sizeOf arguments
end

theorem vector_addresses_closed {pattern : Pattern} (shape : VectorFirstOrder pattern)
    (closed : pattern.freeFvarNames = []) (site : RulePatternSite) (path : List Nat) :
    addresses site path pattern = [] := by
  apply List.map_eq_nil_iff.mp
  rw [vector_address_names shape, closed]

theorem vector_inspect_closed {pattern : Pattern} (shape : VectorFirstOrder pattern)
    (closed : pattern.freeFvarNames = []) (language : LanguageDef) (context : List (String × TypeExpr))
    (site : RulePatternSite) (bound : List TypeExpr) (expected : TypeExpr) :
    inspect language context site bound expected pattern = some [] := by
  simp only [inspect, vector_addresses_closed shape closed, List.mapM_nil, pure]

#print axioms vector_address_names
#print axioms vector_addresses_closed
#print axioms vector_inspect_closed

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar
