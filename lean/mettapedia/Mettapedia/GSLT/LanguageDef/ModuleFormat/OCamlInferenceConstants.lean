import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionShapes
import Mettapedia.OSLF.MeTTaIL.GeneralVectorAddressNames

/-! Compact source constants introduce no binding-inference addresses.
The statement holds at every rule site and address prefix.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralRuleBindingGrammar

theorem code_addresses (site : RulePatternSite) (path : List Nat) (reference : Nat) :
    addresses site path (code reference) = [] :=
  vector_addresses_closed (code_vector reference) (code_freeNames reference) site path

theorem literal_addresses (site : RulePatternSite) (path : List Nat) (datum : OCaml.Literal) :
    addresses site path (literal datum) = [] :=
  vector_addresses_closed (literal_vector datum) (literal_freeNames datum) site path

theorem tag_addresses (site : RulePatternSite) (path : List Nat) (typeId constructor : Nat) :
    addresses site path (tag typeId constructor) = [] :=
  vector_addresses_closed (tag_vector typeId constructor) (tag_freeNames typeId constructor) site path

theorem patternId_addresses (site : RulePatternSite) (path : List Nat) (index : Nat) :
    addresses site path (patternId index) = [] := by
  apply vector_addresses_closed _ (patternId_freeNames index)
  exact node_vector_all _ _ (vector_list_cons (digits_vector index) vector_list_nil)

#print axioms code_addresses
#print axioms literal_addresses
#print axioms tag_addresses
#print axioms patternId_addresses

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
