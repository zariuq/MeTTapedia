import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.FrameFilter
import Mettapedia.Machines.ResourceOwnership

/-!
# Retained physical cells preserve the full schematic source label

Only the requested occurrence addresses are retained. The representation
relation requires actual cells, not a default value that could hide a missing
row. Complete cells preserve the stored schema, private equations and capture
arguments together. The existing heap collector supplies physical retention.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.SourceStorage

open Interface (Frames)
open Mettapedia.Machines.ResourceOwnership

universe uO uT uH
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {Occurrence Address Owner : Type} [DecidableEq Address]

def RepresentsOn (source : State Tm Occurrence) (rows : List Occurrence)
    (heap : Heap Address (Row Tm source.frame)) (address : Occurrence → Address) : Prop :=
  ∀ occurrence ∈ rows, ∃ cell,
    heap.lookup (address occurrence) = some cell ∧ cell.value = source.label occurrence

def load {frame : Obj} (heap : Heap Address (Row Tm frame)) (address : Occurrence → Address)
    (occurrence : Occurrence) : Option (Row Tm frame) :=
  (heap.lookup (address occurrence)).map Cell.value

omit [DecidableEq Address] in
theorem load_exact (source : State Tm Occurrence) (rows : List Occurrence)
    (heap : Heap Address (Row Tm source.frame)) (address : Occurrence → Address)
    (represented : RepresentsOn source rows heap address) (occurrence : Occurrence) (member : occurrence ∈ rows) :
    load heap address occurrence = some (source.label occurrence) := by
  obtain ⟨cell, found, value⟩ := represented occurrence member
  simp only [load, found, Option.map_some, value]

theorem collect_represents (source : State Tm Occurrence) (rows : List Occurrence)
    (heap : Heap Address (Row Tm source.frame)) (address : Occurrence → Address)
    (represented : RepresentsOn source rows heap address) (roots : Roots Owner Address)
    (retained : RequestBorrow.retentionCheck heap roots (rows.map address) = true) :
    RepresentsOn source rows (collect heap roots) address := by
  have covered := (RequestBorrow.retentionCheck_iff heap roots _).mp retained
  intro occurrence member
  obtain ⟨cell, found, value⟩ := represented occurrence member
  refine ⟨cell, ?_, value⟩
  rw [lookup_collect_of_live heap roots
    (covered.2 (address occurrence) (List.mem_map.mpr ⟨occurrence, member, rfl⟩))]
  exact found

theorem retained_load_exact (source : State Tm Occurrence) (rows : List Occurrence)
    (heap : Heap Address (Row Tm source.frame)) (address : Occurrence → Address)
    (represented : RepresentsOn source rows heap address) (roots : Roots Owner Address)
    (retained : RequestBorrow.retentionCheck heap roots (rows.map address) = true)
    (occurrence : Occurrence) (member : occurrence ∈ rows) :
    load (collect heap roots) address occurrence = some (source.label occurrence) :=
  load_exact source rows _ address (collect_represents source rows heap address represented roots retained) occurrence member

theorem dispatch_retained (source : State Tm Occurrence) (rows : List Occurrence)
    (heap : Heap Address (Row Tm source.frame)) (address : Occurrence → Address)
    (represented : RepresentsOn source rows heap address) (roots : Roots Owner Address)
    (retained : RequestBorrow.retentionCheck heap roots (rows.map address) = true)
    (occurrence : Occurrence) (member : occurrence ∈ rows)
    {Result : Type} (use : Row Tm source.frame → Result) :
    (load (collect heap roots) address occurrence).map use = some (use (source.label occurrence)) := by
  rw [retained_load_exact source rows heap address represented roots retained occurrence member]
  rfl

#print axioms collect_represents
#print axioms retained_load_exact
#print axioms dispatch_retained

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.SourceStorage
