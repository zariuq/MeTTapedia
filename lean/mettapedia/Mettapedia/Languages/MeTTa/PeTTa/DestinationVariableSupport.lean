import Mettapedia.Languages.MeTTa.PeTTa.EagerDFS
import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# The first-order destination encoding preserves syntactic variable support

Support can be read directly from the existing occurrence-ordered atom
inventory. It need not execute the first-order term codec or inspect its
dependent argument functions. This is raw syntactic support, including
variables inside quotation, not a binding-aware notion of free variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.LP

private theorem varsList_eq_flatMap (values : List Atom) :
    SubstitutionAlgebra.vars.varsList values = values.flatMap SubstitutionAlgebra.vars := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp only [SubstitutionAlgebra.vars.varsList, List.flatMap_cons, ih]

theorem encode_variable_support (atom : Atom) :
    (encode atom).freeVars = (SubstitutionAlgebra.vars atom).toFinset := by
  induction atom using Atom.rec (motive_2 := fun values => ∀ value ∈ values,
      (encode value).freeVars = (SubstitutionAlgebra.vars value).toFinset) with
  | symbol name => simp [encode, Term.freeVars, SubstitutionAlgebra.vars]
  | var name => simp [encode, Term.freeVars, SubstitutionAlgebra.vars]
  | grounded value => simp [encode, Term.freeVars, SubstitutionAlgebra.vars]
  | expression values each =>
      rw [encode]
      ext name
      simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and,
        SubstitutionAlgebra.vars, List.mem_toFinset, varsList_eq_flatMap, List.mem_flatMap]
      constructor
      · rintro ⟨index, present⟩
        refine ⟨values[index], List.getElem_mem index.isLt, ?_⟩
        exact List.mem_toFinset.mp ((each values[index] (List.getElem_mem index.isLt)) ▸ present)
      · rintro ⟨value, present, occurs⟩
        obtain ⟨index, valid, rfl⟩ := List.mem_iff_getElem.mp present
        exact ⟨⟨index, valid⟩,
          (each values[index] (List.getElem_mem valid)).symm ▸ List.mem_toFinset.mpr occurs⟩
  | nil value member => cases member
  | cons head tail headIH tailIH value member =>
      rcases List.mem_cons.mp member with rfl | later
      · exact headIH
      · exact tailIH value later

namespace VariableSupportControls

theorem nested_repeated_variables_keep_their_support :
    (encode (.expression [.var "x", .expression [.var "y", .var "x"]])).freeVars =
      ( ["x", "y"] : List String ).toFinset := by
  rw [encode_variable_support]
  ext name
  simp [SubstitutionAlgebra.vars, SubstitutionAlgebra.vars.varsList, or_comm]

theorem a_symbol_with_the_same_spelling_is_not_a_variable :
    (encode (.symbol "x")).freeVars = ∅ ∧ (encode (.var "x")).freeVars = {"x"} := by
  simp [encode_variable_support, SubstitutionAlgebra.vars]

end VariableSupportControls

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination
