import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.SourceStorage

/-!
# Publishing a result root before closing the reader

Promotion here changes existing owner roots, not the term carrier or heap.
It preserves the transitive graph without copying payloads. Operational
permission is a separate lease obligation. A runtime must publish the new
strong root before releasing the cursor's root; a pointer description alone
does not perform that transition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.Promotion

open Mettapedia.Machines.ResourceOwnership

universe uValue
variable {Owner Address : Type} {Value : Type uValue} [DecidableEq Owner] [DecidableEq Address]

def publish (roots : Roots Owner Address) (receiver : Owner) (captured : List Address) : Roots Owner Address :=
  roots ∪ captured.toFinset.image (fun address => (receiver, address))

theorem promoted_root_survives_close (roots : Roots Owner Address) (reader receiver : Owner)
    (distinct : receiver ≠ reader) (captured : List Address) (address : Address) (member : address ∈ captured) :
    (receiver, address) ∈ release (publish roots receiver captured) reader := by
  rw [mem_release]
  refine ⟨Finset.mem_union.mpr (Or.inr ?_), distinct⟩
  exact Finset.mem_image.mpr ⟨address, List.mem_toFinset.mpr member, rfl⟩

theorem published_retention_check (heap : Heap Address Value) (roots : Roots Owner Address)
    (reader receiver : Owner) (distinct : receiver ≠ reader) (captured : List Address)
    (valid : ValidRoots heap roots) (allocated : ∀ address ∈ captured, address ∈ heap.allocated) :
    RequestBorrow.retentionCheck heap (release (publish roots receiver captured) reader) captured = true := by
  apply (RequestBorrow.retentionCheck_iff heap _ captured).mpr
  constructor
  · intro pair member
    have original := (mem_release _ _ pair).mp member
    rcases Finset.mem_union.mp original.1 with prior | promoted
    · exact valid pair prior
    · obtain ⟨address, present, same⟩ := Finset.mem_image.mp promoted
      cases same
      exact allocated address (List.mem_toFinset.mp present)
  · intro address member
    exact live_of_root heap _ (promoted_root_survives_close roots reader receiver distinct captured address member)
      (allocated address member)

theorem promoted_complete_cells_survive (heap : Heap Address Value) (roots : Roots Owner Address)
    (reader receiver : Owner) (distinct : receiver ≠ reader) (captured : List Address)
    (valid : ValidRoots heap roots) (allocated : ∀ address ∈ captured, address ∈ heap.allocated)
    (address : Address) (member : address ∈ captured) :
    (collect heap (release (publish roots receiver captured) reader)).lookup address = heap.lookup address := by
  have checked := published_retention_check heap roots reader receiver distinct captured valid allocated
  exact (RequestBorrow.retentionCheck_iff_preserves_lookups heap _ captured allocated).mp checked |>.2 address member

theorem one_graph_not_one_copy_per_owner (heap : Heap Address Value) (reader receiver : Owner) (address : Address) :
    footprint heap ({(reader, address), (receiver, address)} : Roots Owner Address) =
      footprint heap ({(receiver, address)} : Roots Owner Address) := by
  apply footprint_congr_rootAddresses
  simp [rootAddresses]

universe uObj uTerm
variable {Obj : Type uObj} {Tm : Obj → Type uTerm} {Occurrence : Type}

theorem published_source_survives_close (source : State Tm Occurrence) (rows : List Occurrence)
    (heap : Heap Address (Row Tm source.frame)) (address : Occurrence → Address)
    (represented : SourceStorage.RepresentsOn source rows heap address) (roots : Roots Owner Address)
    (valid : ValidRoots heap roots) (reader receiver : Owner) (distinct : receiver ≠ reader) :
    SourceStorage.RepresentsOn source rows
      (collect heap (release (publish roots receiver (rows.map address)) reader)) address := by
  have allocated : ∀ location ∈ rows.map address, location ∈ heap.allocated := by
    intro location member
    obtain ⟨occurrence, listed, rfl⟩ := List.mem_map.mp member
    obtain ⟨cell, found, _⟩ := represented occurrence listed
    exact (heap.allocated_iff _).mpr ⟨cell, found⟩
  exact SourceStorage.collect_represents source rows heap address represented _
    (published_retention_check heap roots reader receiver distinct (rows.map address) valid allocated)

#print axioms published_retention_check
#print axioms promoted_complete_cells_survive
#print axioms one_graph_not_one_copy_per_owner
#print axioms published_source_survives_close

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.Promotion
