import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLowering
import Mettapedia.Data.List.IndexAllocation

/-! The actual CHR frontend's variable allocation is total on its source
scope and never aliases distinct source identities. These laws hold for
mixed spellings and anonymous occurrences, independently of parser examples.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologBindings

open CHRPrologLowering

theorem allocate_eq (source : SourceTerm) :
    allocate source = List.IndexAllocation.allocate (sourceVariables source) preferredIndex? := rfl

theorem index_lookup (allocation : Allocation) (name : Variable) :
    index? allocation name = allocation.lookup name := rfl

theorem all_variables_assigned (source : SourceTerm) (name : Variable)
    (member : name ∈ sourceVariables source) : ∃ index, index? (allocate source) name = some index := by
  rw [allocate_eq]
  simp only [index_lookup]
  exact List.IndexAllocation.assigned _ _ name member

theorem distinct_variables_do_not_alias (source : SourceTerm) (first second : Variable) (index : Nat)
    (left : index? (allocate source) first = some index)
    (right : index? (allocate source) second = some index) : first = second := by
  simp only [allocate_eq, index_lookup] at left right
  exact List.IndexAllocation.no_alias _ _ first second index left right

theorem anonymous_not_named (source : SourceTerm) (occurrence index : Nat) (name : Variable)
    (named : name.spelling ≠ "_")
    (anonymous : index? (allocate source) ⟨"_", occurrence⟩ = some index) :
    index? (allocate source) name ≠ some index := by
  intro shared
  have same := distinct_variables_do_not_alias source ⟨"_", occurrence⟩ name index anonymous shared
  exact named (congrArg (fun name : Variable => name.spelling) same).symm

theorem anonymous_occurrences_distinct (source : SourceTerm) (first second index : Nat)
    (different : first ≠ second)
    (bound : index? (allocate source) ⟨"_", first⟩ = some index) :
    index? (allocate source) ⟨"_", second⟩ ≠ some index := by
  intro shared
  have same := distinct_variables_do_not_alias source ⟨"_", first⟩ ⟨"_", second⟩ index bound shared
  exact different (congrArg (fun name : Variable => name.occurrence) same)

#print axioms all_variables_assigned
#print axioms distinct_variables_do_not_alias
#print axioms anonymous_occurrences_distinct

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologBindings
