import Mettapedia.TypeTheory.MaterialSets.Hypersets.Finality
import Mettapedia.SetTheory.Profiles.ProfileConstructiveFinite

/-!
# Computable bisimulation of arbitrary finite graphs

Refinement starts with every pair of nodes and deletes pairs whose
children cannot be matched in both directions. The number of rounds is
the number of candidate pairs. The final table is the greatest
bisimulation, so its Boolean readout has exactly the kernel of Aczel
material decoration. This finite algorithm does not decide equality in
the full contextual material universe.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Finite

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ConstructiveFinite

universe u v
variable {α : Type u} {β : Type v}
variable [Enumeration α] [Enumeration β] [DecidableEq α] [DecidableEq β]
variable (left : α → α → Prop) (right : β → β → Prop)
variable [DecidableRel left] [DecidableRel right]

def Matches (table : List (α × β)) (first : α) (second : β) : Prop :=
  (∀ child, left first child → ∃ reply, right second reply ∧ (child, reply) ∈ table) ∧
  (∀ child, right second child → ∃ reply, left first reply ∧ (reply, child) ∈ table)

instance matchesDecidable (table : List (α × β)) (first : α) (second : β) :
    Decidable (Matches left right table first second) := by
  unfold Matches
  infer_instance

def refine (table : List (α × β)) : List (α × β) :=
  table.filter (fun pair => decide (Matches left right table pair.1 pair.2))

theorem mem_refine (table : List (α × β)) (first : α) (second : β) :
    (first, second) ∈ refine left right table ↔
      (first, second) ∈ table ∧ Matches left right table first second :=
  by simp only [refine, List.mem_filter, decide_eq_true_eq]

theorem refine_sublist (table : List (α × β)) : List.Sublist (refine left right table) table :=
  List.filter_sublist

theorem refine_subset (table : List (α × β)) : refine left right table ⊆ table :=
  (refine_sublist left right table).subset

def rounds : Nat → List (α × β)
  | 0 => pairElements
  | count+1 => refine left right (rounds count)

theorem rounds_succ_subset (count : Nat) :
    rounds left right (count+1) ⊆ rounds left right count :=
  refine_subset left right _

theorem unequal_rounds_card (count : Nat)
    (changes : rounds left right (count+1) ≠ rounds left right count) :
    (rounds left right (count+1)).length < (rounds left right count).length := by
  have sublist := refine_sublist left right (rounds left right count)
  exact Nat.lt_of_not_ge (fun bound => changes (sublist.eq_of_length_le bound))

theorem strict_rounds_card_bound (count : Nat)
    (changes : rounds left right (count+1) ≠ rounds left right count) :
    (rounds left right (count+1)).length + (count+1) ≤ size (α := α) * size (α := β) := by
  induction count with
  | zero =>
    have decreases := unequal_rounds_card left right 0 changes
    simpa only [rounds, pair_length] using Nat.succ_le_of_lt decreases
  | succ count previous =>
    have earlier : rounds left right (count+1) ≠ rounds left right count := by
      intro same
      apply changes
      exact congrArg (refine left right) same
    have bound := previous earlier
    have decreases := unequal_rounds_card left right (count+1) changes
    omega

/-- There is no extra stabilization hypothesis: finite cardinality
supplies the exact worst-case round bound. -/
theorem rounds_stabilize :
    rounds left right (size (α := α) * size (α := β)+1) =
      rounds left right (size (α := α) * size (α := β)) := by
  by_cases same : rounds left right (size (α := α) * size (α := β)+1) =
      rounds left right (size (α := α) * size (α := β))
  · exact same
  · have impossible := strict_rounds_card_bound left right (size (α := α) * size (α := β)) same
    omega

def stable : List (α × β) := rounds left right (size (α := α) * size (α := β))

theorem stable_fixed : refine left right (stable left right) = stable left right :=
  rounds_stabilize left right

theorem bisimulation_in_rounds (relation : α → β → Prop)
    (proof : IsBisimulation left right relation) (count : Nat)
    {first : α} {second : β} (related : relation first second) :
    (first, second) ∈ rounds left right count := by
  induction count generalizing first second with
  | zero => exact pair_complete first second
  | succ count previous =>
    apply (mem_refine left right _ _ _).mpr
    refine ⟨previous related, ?_, ?_⟩
    · intro child available
      obtain ⟨reply, available, related⟩ := (proof related).1 child available
      exact ⟨reply, available, previous related⟩
    · intro child available
      obtain ⟨reply, available, related⟩ := (proof related).2 child available
      exact ⟨reply, available, previous related⟩

theorem stable_isBisimulation :
    IsBisimulation left right (fun first second => (first, second) ∈ stable left right) := by
  intro first second related
  have retained : (first, second) ∈ refine left right (stable left right) :=
    (stable_fixed left right).symm ▸ related
  exact ((mem_refine left right _ first second).mp retained).2

theorem stable_kernel (first : α) (second : β) :
    (first, second) ∈ stable left right ↔ Bisimilar left right first second := by
  constructor
  · exact (stable_isBisimulation left right).bisimilar
  · rintro ⟨relation, proof, related⟩
    exact bisimulation_in_rounds left right relation proof _ related

def equivalent (first : α) (second : β) : Bool :=
  decide ((first, second) ∈ stable left right)

theorem equivalent_eq_true (first : α) (second : β) :
    equivalent left right first second = true ↔ Bisimilar left right first second := by
  simp only [equivalent, decide_eq_true_eq, stable_kernel]

section Material

variable {γ : Type u} [Enumeration γ] [DecidableEq γ]
variable (other : γ → γ → Prop) [DecidableRel other]

theorem equivalent_material_kernel (first : α) (second : γ) :
    equivalent left other first second = true ↔
      HSet.decorate left first = HSet.decorate other second :=
  (equivalent_eq_true left other first second).trans HSet.bisimilar_iff_decorate_eq

end Material

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Finite
