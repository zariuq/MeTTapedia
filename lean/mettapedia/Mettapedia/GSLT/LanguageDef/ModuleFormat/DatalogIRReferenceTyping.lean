import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRReferenceCodec
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderTyping

/-! Physical references are object free names with their actual registered
sorts. Their typing uses the prepared provider context, never an empty one. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ReferenceTyping

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

private theorem lookup_exact (entries : List (String × TypeExpr)) (name : String) (type : TypeExpr)
    (member : (name,type) ∈ entries)
    (consistent : ∀ entry ∈ entries, entry.1 = name → entry.2 = type) : entries.lookup name = some type := by
  have defined : (entries.lookup name).isSome = true := List.lookup_isSome_iff.mpr ⟨(name,type),member,by simp⟩
  obtain ⟨actual,found⟩ := Option.isSome_iff_exists.mp defined
  obtain ⟨before,after,shape,_⟩ := List.lookup_eq_some_iff.mp found
  have actualMember : (name,actual) ∈ entries := by rw [shape]; simp
  have same := consistent (name,actual) actualMember rfl
  exact same ▸ found

theorem relation_lookup (pools : Join.Pools) (index : Nat) (inside : index < pools.relations.length) :
    (Executable.freeTypes pools).lookup ("dl:relation:" ++ toString index) = some (.base "DlRelation") := by
  apply lookup_exact
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨index,List.mem_range.mpr inside,rfl⟩
  · intro entry member same
    rcases List.mem_append.mp member with relation | literal
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp relation
      rfl
    · obtain ⟨other,_,rfl⟩ := List.mem_map.mp literal
      exact (Executable.relation_value_disjoint index other (congrArg Pattern.fvar same).symm).elim

theorem value_lookup (pools : Join.Pools) (index : Nat) (inside : index < pools.literals.length) :
    (Executable.freeTypes pools).lookup ("dl:value:" ++ toString index) = some (.base "DlValue") := by
  apply lookup_exact
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨index,List.mem_range.mpr inside,rfl⟩
  · intro entry member same
    rcases List.mem_append.mp member with relation | literal
    · obtain ⟨other,_,rfl⟩ := List.mem_map.mp relation
      exact (Executable.relation_value_disjoint other index (congrArg Pattern.fvar same)).elim
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp literal
      rfl

theorem relation_open (language : LanguageDef) (pools : Join.Pools) (index : Nat)
    (inside : index < pools.relations.length) : OpenPatternWellSorted language
      (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (.base "DlRelation") (Executable.relationRef index) := by
  refine ⟨.fvar ?_,rfl,rfl,rfl⟩
  rw [context_ofList_lookup]
  exact relation_lookup pools index inside

theorem value_open (language : LanguageDef) (pools : Join.Pools) (index : Nat)
    (inside : index < pools.literals.length) : OpenPatternWellSorted language
      (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (.base "DlValue") (Executable.valueRef index) := by
  refine ⟨.fvar ?_,rfl,rfl,rfl⟩
  rw [context_ofList_lookup]
  exact value_lookup pools index inside

#print axioms relation_lookup
#print axioms value_lookup
#print axioms relation_open
#print axioms value_open

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ReferenceTyping
