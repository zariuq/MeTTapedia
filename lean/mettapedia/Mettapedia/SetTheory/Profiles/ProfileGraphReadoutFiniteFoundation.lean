import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFinite
import Mettapedia.TypeTheory.MaterialSets.Hypersets.WellFounded

/-!
# Computed partial Foundation domains for finite graphs

Leaf elimination admits a node once all its children have been admitted.
Within the finite node bound the table stabilizes. Membership in that
table is exactly accessibility, hence exactly well-foundedness of the
node's Aczel decoration. Unreachable cycles do not disqualify a root.
This eligibility test supplies a partial readout domain, not a model of
the Foundation profile on arbitrary cyclic presentations.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Finite.Foundation

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ConstructiveFinite

universe u
variable {α : Type u} [Enumeration α] [DecidableEq α]
variable (edge : α → α → Prop) [DecidableRel edge]

def step (admitted : List α) : List α :=
  elements.filter (fun parent => decide
    (parent ∈ admitted ∨ ∀ child, edge parent child → child ∈ admitted))

theorem mem_step (admitted : List α) (parent : α) :
    parent ∈ step edge admitted ↔
      parent ∈ admitted ∨ ∀ child, edge parent child → child ∈ admitted := by
  simp only [step, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun available => available.2, fun available => ⟨complete parent, available⟩⟩

theorem subset_step (admitted : List α) : admitted ⊆ step edge admitted :=
  fun _ available => (mem_step edge admitted _).mpr (Or.inl available)

theorem step_sublist_of_subset {first second : List α} (contained : first ⊆ second) :
    List.Sublist (step edge first) (step edge second) := by
  apply filter_sublist_of_imp
  intro parent available
  apply decide_eq_true
  rcases of_decide_eq_true available with previous | children
  · exact Or.inl (contained previous)
  · exact Or.inr (fun child related => contained (children child related))

def rounds : Nat → List α
  | 0 => []
  | count+1 => step edge (rounds count)

theorem rounds_succ_sublist (count : Nat) : List.Sublist (rounds edge count) (rounds edge (count+1)) := by
  induction count with
  | zero => exact List.nil_sublist _
  | succ count previous => exact step_sublist_of_subset edge previous.subset

theorem rounds_succ_subset (count : Nat) : rounds edge count ⊆ rounds edge (count+1) :=
  (rounds_succ_sublist edge count).subset

theorem unequal_rounds_card (count : Nat)
    (changes : rounds edge (count+1) ≠ rounds edge count) :
    (rounds edge count).length < (rounds edge (count+1)).length :=
  length_lt_of_sublist_ne (rounds_succ_sublist edge count) (fun same => changes same.symm)

theorem strict_rounds_card_bound (count : Nat)
    (changes : rounds edge (count+1) ≠ rounds edge count) :
    count+1 ≤ (rounds edge (count+1)).length := by
  induction count with
  | zero => exact Nat.succ_le_of_lt (unequal_rounds_card edge 0 changes)
  | succ count previous =>
    have earlier : rounds edge (count+1) ≠ rounds edge count := by
      intro same
      apply changes
      exact congrArg (step edge) same
    have bound := previous earlier
    have increases := unequal_rounds_card edge (count+1) changes
    omega

theorem rounds_stabilize :
    rounds edge (size (α := α)+1) = rounds edge (size (α := α)) := by
  by_cases same : rounds edge (size (α := α)+1) = rounds edge (size (α := α))
  · exact same
  · have impossible := strict_rounds_card_bound edge (size (α := α)) same
    have bound : (rounds edge (size (α := α)+1)).length ≤ size (α := α) :=
      List.filter_sublist.length_le
    omega

def stable : List α := rounds edge (size (α := α))

theorem stable_fixed : step edge (stable edge) = stable edge := rounds_stabilize edge

theorem accessible_of_round (count : Nat) (parent : α) (available : parent ∈ rounds edge count) :
    Acc (Function.swap edge) parent := by
  induction count generalizing parent with
  | zero => exact False.elim (List.not_mem_nil available)
  | succ count previous =>
    rcases (mem_step edge _ parent).mp available with earlier | fresh
    · exact previous parent earlier
    · refine Acc.intro parent ?_
      intro child edgeHere
      exact previous child (fresh child edgeHere)

theorem stable_of_accessible (parent : α) (accessible : Acc (Function.swap edge) parent) :
    parent ∈ stable edge := by
  induction accessible with
  | intro parent accessible previous =>
    have next : parent ∈ step edge (stable edge) :=
      (mem_step edge _ parent).mpr (Or.inr previous)
    exact stable_fixed edge ▸ next

theorem stable_kernel (parent : α) :
    parent ∈ stable edge ↔ Acc (Function.swap edge) parent :=
  ⟨accessible_of_round edge _ parent, stable_of_accessible edge parent⟩

def eligible (parent : α) : Bool := decide (parent ∈ stable edge)

theorem eligible_accessibility (parent : α) :
    eligible edge parent = true ↔ Acc (Function.swap edge) parent := by
  simp only [eligible, decide_eq_true_eq, stable_kernel]

theorem eligible_material_domain (parent : α) :
    eligible edge parent = true ↔ (HSet.decorate edge parent).WF :=
  (eligible_accessibility edge parent).trans HSet.wf_decorate_iff.symm

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Finite.Foundation
