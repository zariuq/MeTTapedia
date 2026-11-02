import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderMeaning

/-! Every reachable service-cache row retains a source encoding. This
representation invariant complements typing and semantic soundness: a
typed row alone need not use a canonical source literal representation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def EncodedProviderRows (table : GeneralPremise.ProviderSnapshot) : Prop :=
  ∀ row ∈ table.rows,
    (∃ operator arguments result, row = primitiveRow operator arguments result) ∨
    (∃ index argument, row = failureRow index argument)

theorem initial_provider_rows_encoded : EncodedProviderRows provider := by
  intro row member
  cases member

theorem primitive_append_preserves_encoding (table : GeneralPremise.ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (encoded : EncodedProviderRows table) :
    EncodedProviderRows (GeneralPremise.ProviderAppend.appendRows table [primitiveRow operator arguments result]) := by
  intro row member
  rcases (GeneralPremise.ProviderAppend.row_membership table [primitiveRow operator arguments result] row).mp member with old | fresh
  · exact encoded row old
  · exact .inl ⟨operator, arguments, result, List.mem_singleton.mp fresh⟩

theorem failure_append_preserves_encoding (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (argument : OCaml.Value) (encoded : EncodedProviderRows table) :
    EncodedProviderRows (GeneralPremise.ProviderAppend.appendRows table [failureRow index argument]) := by
  intro row member
  rcases (GeneralPremise.ProviderAppend.row_membership table [failureRow index argument] row).mp member with old | fresh
  · exact encoded row old
  · exact .inr ⟨index, argument, List.mem_singleton.mp fresh⟩

theorem encoded_primitive_row (table : GeneralPremise.ProviderSnapshot) (row : GeneralPremise.ProviderRow)
    (encoded : EncodedProviderRows table) (present : row ∈ table.rows) (relation : row.relation = "ml-primitive") :
    ∃ operator arguments result, row = primitiveRow operator arguments result := by
  rcases encoded row present with primitive | ⟨index, argument, rfl⟩
  · exact primitive
  · simp [failureRow] at relation

theorem encoded_failure_row (table : GeneralPremise.ProviderSnapshot) (row : GeneralPremise.ProviderRow)
    (encoded : EncodedProviderRows table) (present : row ∈ table.rows) (relation : row.relation = "ml-pattern-failure") :
    ∃ index argument, row = failureRow index argument := by
  rcases encoded row present with ⟨operator, arguments, result, rfl⟩ | failed
  · simp [primitiveRow] at relation
  · exact failed

theorem primitive_query_row_source (table : GeneralPremise.ProviderSnapshot) (operator : OCaml.Primitive)
    (arguments : List OCaml.Value) (answer : Pattern) (encoded : EncodedProviderRows table)
    (present : (⟨"ml-primitive", [primitive operator, valueList arguments, answer]⟩ : GeneralPremise.ProviderRow) ∈ table.rows) :
    ∃ result, answer = primitiveResult result ∧ primitiveRow operator arguments result ∈ table.rows := by
  obtain ⟨actualOperator, actualArguments, result, same⟩ := encoded_primitive_row table _ encoded present rfl
  have fields := List.cons.inj (congrArg GeneralPremise.ProviderRow.values same)
  have sameOperator := primitive_injective fields.1
  have argumentsSame := (List.cons.inj fields.2).1
  have sameArguments : arguments = actualArguments := by
    rw [valueList_as_values, valueList_as_values] at argumentsSame
    exact List.map_injective_iff.mpr value_injective (values_injective argumentsSame)
  have answerSame := (List.cons.inj (List.cons.inj fields.2).2).1
  subst actualOperator actualArguments
  exact ⟨result, answerSame, same ▸ present⟩

theorem primitive_query_row_authorized (pool : List OCaml.MatchPattern) (table : GeneralPremise.ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (answer : Pattern)
    (encoded : EncodedProviderRows table) (meaning : ProviderMeaning pool table)
    (present : (⟨"ml-primitive", [primitive operator, valueList arguments, answer]⟩ : GeneralPremise.ProviderRow) ∈ table.rows) :
    ∃ result, answer = primitiveResult result ∧ operator.eval arguments = .ok result := by
  obtain ⟨result, same, cached⟩ := primitive_query_row_source table operator arguments answer encoded present
  exact ⟨result, same, meaning.1 operator arguments result cached⟩

#print axioms initial_provider_rows_encoded
#print axioms primitive_append_preserves_encoding
#print axioms failure_append_preserves_encoding
#print axioms encoded_primitive_row
#print axioms encoded_failure_row
#print axioms primitive_query_row_source
#print axioms primitive_query_row_authorized

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
