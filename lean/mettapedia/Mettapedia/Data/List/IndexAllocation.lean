import Mettapedia.Data.List.OptionMapM
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sigma

/-! Finite names receive distinct natural indices. A preferred allocation
is retained only when it covers the complete scope without collisions;
otherwise source positions provide a total fresh allocation. Repeated uses
of one name share its first allocation. -/

set_option autoImplicit false

namespace List.IndexAllocation

universe u
variable {α : Type u} [BEq α]

def allocate (names : List α) (preferred : α → Option Nat) : List (α × Nat) :=
  let distinct := names.eraseDups
  match distinct.mapM preferred with
  | some indices => if indices.Nodup then distinct.zip indices else distinct.zipIdx
  | none => distinct.zipIdx

theorem keys (names : List α) (preferred : α → Option Nat) :
    (allocate names preferred).map Prod.fst = names.eraseDups := by
  dsimp only [allocate]
  cases read : names.eraseDups.mapM preferred with
  | none => exact zipIdx_map_fst 0 _
  | some indices =>
      have lengths := (Mettapedia.Data.List.option_mapM_forall₂ preferred names.eraseDups indices read).length_eq
      dsimp only
      by_cases distinct : indices.Nodup
      · rw [if_pos distinct]
        exact map_fst_zip (l₁ := names.eraseDups) (l₂ := indices) (by omega)
      · rw [if_neg distinct]
        exact zipIdx_map_fst 0 _

theorem indices_distinct (names : List α) (preferred : α → Option Nat) :
    ((allocate names preferred).map Prod.snd).Nodup := by
  dsimp only [allocate]
  cases read : names.eraseDups.mapM preferred with
  | none => exact nodup_zipIdx_map_snd _
  | some indices =>
      have lengths := (Mettapedia.Data.List.option_mapM_forall₂ preferred names.eraseDups indices read).length_eq
      dsimp only
      by_cases distinct : indices.Nodup
      · rw [if_pos distinct, map_snd_zip (l₁ := names.eraseDups) (l₂ := indices) (by omega)]
        exact distinct
      · rw [if_neg distinct]
        exact nodup_zipIdx_map_snd _

theorem assigned [LawfulBEq α] (names : List α) (preferred : α → Option Nat) (name : α) (member : name ∈ names) :
    ∃ index, (allocate names preferred).lookup name = some index := by
  have present : name ∈ (allocate names preferred).map Prod.fst := by
    rw [keys]
    exact mem_eraseDups.mpr member
  obtain ⟨entry, inTable, same⟩ := mem_map.mp present
  have found : ((allocate names preferred).lookup name).isSome :=
    lookup_isSome_iff.mpr ⟨entry, inTable, beq_iff_eq.mpr same.symm⟩
  exact Option.isSome_iff_exists.mp found

theorem lookup_member [LawfulBEq α] (table : List (α × Nat)) (name : α) (index : Nat)
    (read : table.lookup name = some index) : (name, index) ∈ table := by
  obtain ⟨before, after, same, _⟩ := lookup_eq_some_iff.mp read
  rw [same]
  exact mem_append_right _ mem_cons_self

theorem no_alias [LawfulBEq α] (names : List α) (preferred : α → Option Nat) (first second : α) (index : Nat)
    (left : (allocate names preferred).lookup first = some index)
    (right : (allocate names preferred).lookup second = some index) : first = second := by
  have same := inj_on_of_nodup_map (indices_distinct names preferred)
    (lookup_member _ first index left) (lookup_member _ second index right) rfl
  exact congrArg Prod.fst same

example : allocate [8,0,8] (fun n : Nat => some n) = [(8,8),(0,0)] := by decide
example : allocate [8,0] (fun _ : Nat => some 0) = [(8,0),(0,1)] := by decide

#print axioms keys
#print axioms indices_distinct
#print axioms assigned
#print axioms no_alias

end List.IndexAllocation
