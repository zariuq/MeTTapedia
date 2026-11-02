import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning
import Mathlib.Data.List.NodupEquivFin

/-! # Allocate the finite physical support of compatible read ports -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open PositiveResourceProjection (realized readFootprint)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {assignment : S} {label : O → T} {rule : RuleInstance T}

namespace ReadPlan

noncomputable def supportList (plan : ReadPlan A assignment label rule) : List O :=
  plan.prototype.toFinset.toList

theorem supportList_nodup (plan : ReadPlan A assignment label rule) : plan.supportList.Nodup :=
  Finset.nodup_toList _

theorem supportList_mem (plan : ReadPlan A assignment label rule) (occurrence : O) :
    occurrence ∈ plan.supportList ↔ occurrence ∈ plan.prototype.toFinset := Finset.mem_toList

noncomputable def supportPositions (plan : ReadPlan A assignment label rule) :
    ReadPortPushouts.Rows plan.prototype.toFinset ≃ Fin plan.supportList.length :=
  ({ toFun := fun row => ⟨row.val, (plan.supportList_mem _).mpr row.property⟩
     invFun := fun row => ⟨row.val, (plan.supportList_mem _).mp row.property⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } :
      ReadPortPushouts.Rows plan.prototype.toFinset ≃ {row // row ∈ plan.supportList}).trans
    (List.Nodup.getEquiv plan.supportList plan.supportList_nodup).symm

theorem support_get (plan : ReadPlan A assignment label rule)
    (row : ReadPortPushouts.Rows plan.prototype.toFinset) :
    plan.supportList.get (plan.supportPositions row) = row.val :=
  congrArg Subtype.val ((List.Nodup.getEquiv plan.supportList plan.supportList_nodup).apply_symm_apply _)

theorem support_bag (plan : ReadPlan A assignment label rule) :
    (plan.supportList.map (realized A assignment label) : Multiset T) =
      readFootprint A assignment label plan.selection := by
  have observed := GuardedMultisetRewriting.labels_toFinset (realized A assignment label) plan.supportList_nodup
  simpa only [supportList, Finset.toList_toFinset, selection, readFootprint] using observed.symm

end ReadPlan

/-- A distinct physical row is allocated for each read-alias class, with
the expected value under the one shared assignment. -/
structure ReadAllocation (plan : ReadPlan A assignment label rule) (world : Finset O) where
  slots : List O
  distinct : slots.Nodup
  occupied : ∀ occurrence ∈ slots, occurrence ∈ world
  matching : List.Forall₂ (fun prototype actual =>
    realized A assignment label prototype = realized A assignment label actual) plan.supportList slots

namespace ReadAllocation

variable {plan : ReadPlan A assignment label rule} {world : Finset O}

noncomputable def embedding (allocation : ReadAllocation plan world)
    (row : ReadPortPushouts.Rows plan.prototype.toFinset) : O :=
  allocation.slots.get (Fin.cast allocation.matching.length_eq (plan.supportPositions row))

theorem embedding_injective (allocation : ReadAllocation plan world) : Function.Injective allocation.embedding := by
  intro first second same
  have positions := allocation.distinct.injective_get same
  apply plan.supportPositions.injective
  apply Fin.ext
  exact congrArg (fun index : Fin allocation.slots.length => index.val) positions

theorem embedding_mem (allocation : ReadAllocation plan world)
    (row : ReadPortPushouts.Rows plan.prototype.toFinset) : allocation.embedding row ∈ allocation.slots :=
  List.get_mem _ _

theorem embedding_values (allocation : ReadAllocation plan world)
    (row : ReadPortPushouts.Rows plan.prototype.toFinset) :
    realized A assignment label (allocation.embedding row) = realized A assignment label row.val := by
  have values := allocation.matching.get (plan.supportPositions row).isLt
    (Fin.cast allocation.matching.length_eq (plan.supportPositions row)).isLt
  rw [plan.support_get row] at values
  exact values.symm

theorem embedding_surjective_slots (allocation : ReadAllocation plan world)
    (occurrence : O) (member : occurrence ∈ allocation.slots) :
    ∃ row, allocation.embedding row = occurrence := by
  obtain ⟨index, atIndex⟩ := List.mem_iff_get.mp member
  obtain ⟨row, atRow⟩ := plan.supportPositions.surjective (Fin.cast allocation.matching.length_eq.symm index)
  refine ⟨row, ?_⟩
  unfold embedding
  rw [atRow]
  simpa only [Fin.cast_cast, Fin.cast_refl, id_eq] using atIndex

theorem allocated_bag (allocation : ReadAllocation plan world) :
    labels (realized A assignment label) allocation.slots.toFinset =
      readFootprint A assignment label plan.selection := by
  rw [GuardedMultisetRewriting.labels_toFinset _ allocation.distinct, ← plan.support_bag]
  have exactMatch : List.Forall₂ Eq (plan.supportList.map (realized A assignment label))
      (allocation.slots.map (realized A assignment label)) := by
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using allocation.matching
  have values : plan.supportList.map (realized A assignment label) =
      allocation.slots.map (realized A assignment label) := by
    simpa only [List.forall₂_eq_eq_eq] using exactMatch
  exact congrArg (fun values : List T => (values : Multiset T)) values.symm

end ReadAllocation

theorem allocate_reads (plan : ReadPlan A assignment label rule) (world : Finset O)
    (fits : readFootprint A assignment label plan.selection ≤ labels (realized A assignment label) world) :
    Nonempty (ReadAllocation plan world) := by
  rw [← plan.support_bag] at fits
  obtain ⟨slots, distinct, occupied, values⟩ := GuardedMultisetRewriting.exists_occurrences
    (realized A assignment label) (plan.supportList.map (realized A assignment label)) world fits
  have matching : List.Forall₂ (fun prototype actual =>
      realized A assignment label prototype = realized A assignment label actual) plan.supportList slots := by
    have equal : List.Forall₂ Eq (plan.supportList.map (realized A assignment label))
        (slots.map (realized A assignment label)) := by
      rw [List.forall₂_eq_eq_eq]
      exact values.symm
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using equal
  exact ⟨⟨slots, distinct, occupied, matching⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning
