import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFiniteFoundation

/-!
# Boolean-table correspondence for finite graph algorithms

The pointwise Boolean relation is the mathematical counterpart of a
double-buffered finite table. Its simultaneous refinement agrees at
every round with the explicit-list solver. The analogous admission
table agrees with leaf elimination. Storage, budgets and publication
are additional realization obligations.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout.FiniteBoolean

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ConstructiveFinite

universe u v
variable {α : Type u} {β : Type v}
variable [Enumeration α] [Enumeration β] [DecidableEq α] [DecidableEq β]
variable (left : α → α → Prop) (right : β → β → Prop)
variable [DecidableRel left] [DecidableRel right]

def Matches (table : α → β → Bool) (first : α) (second : β) : Prop :=
  (∀ child, left first child → ∃ reply, right second reply ∧ table child reply = true) ∧
  (∀ child, right second child → ∃ reply, left first reply ∧ table reply child = true)

instance matchesDecidable (table : α → β → Bool) (first : α) (second : β) :
    Decidable (Matches left right table first second) := by
  unfold Matches
  infer_instance

def refine (table : α → β → Bool) (first : α) (second : β) : Bool :=
  table first second && decide (Matches left right table first second)

def rounds : Nat → α → β → Bool
  | 0 => fun _ _ => true
  | count+1 => refine left right (rounds count)

theorem rounds_correspondence (count : Nat) (first : α) (second : β) :
    rounds left right count first second = true ↔
      (first, second) ∈ Finite.rounds left right count := by
  induction count generalizing first second with
  | zero => exact ⟨fun _ => pair_complete first second, fun _ => rfl⟩
  | succ count previous =>
    rw [Finite.rounds, Finite.mem_refine]
    simp only [rounds, refine, Bool.and_eq_true, decide_eq_true_eq,
      Matches, Finite.Matches, previous]

def equivalent (first : α) (second : β) : Bool :=
  rounds left right (size (α := α) * size (α := β)) first second

theorem equivalent_eq_true (first : α) (second : β) :
    equivalent left right first second = true ↔ Bisimilar left right first second :=
  (rounds_correspondence left right _ first second).trans (Finite.stable_kernel _ _ _ _)

theorem equivalent_agrees (first : α) (second : β) :
    equivalent left right first second = Finite.equivalent left right first second := by
  have same := (equivalent_eq_true left right first second).trans
    (Finite.equivalent_eq_true left right first second).symm
  cases firstRead : equivalent left right first second <;>
    cases secondRead : Finite.equivalent left right first second <;> simp_all

section Material

variable {γ : Type u} [Enumeration γ] [DecidableEq γ]
variable (other : γ → γ → Prop) [DecidableRel other]

theorem equivalent_material_kernel (first : α) (second : γ) :
    equivalent left other first second = true ↔
      HSet.decorate left first = HSet.decorate other second :=
  (equivalent_eq_true left other first second).trans HSet.bisimilar_iff_decorate_eq

end Material

namespace Foundation

variable {δ : Type u} [Enumeration δ] [DecidableEq δ]
variable (edge : δ → δ → Prop) [DecidableRel edge]

def Admissible (admitted : δ → Bool) (parent : δ) : Prop :=
  ∀ child, edge parent child → admitted child = true

instance admissibleDecidable (admitted : δ → Bool) (parent : δ) :
    Decidable (Admissible edge admitted parent) := by
  unfold Admissible
  infer_instance

def step (admitted : δ → Bool) (parent : δ) : Bool :=
  admitted parent || decide (Admissible edge admitted parent)

def rounds : Nat → δ → Bool
  | 0 => fun _ => false
  | count+1 => step edge (rounds count)

theorem rounds_correspondence (count : Nat) (parent : δ) :
    rounds edge count parent = true ↔ parent ∈ Finite.Foundation.rounds edge count := by
  induction count generalizing parent with
  | zero => simp only [rounds, Bool.false_eq_true, Finite.Foundation.rounds, List.not_mem_nil]
  | succ count previous =>
    rw [Finite.Foundation.rounds, Finite.Foundation.mem_step]
    simp only [rounds, step, Bool.or_eq_true, decide_eq_true_eq, Admissible, previous]

def eligible (parent : δ) : Bool := rounds edge (size (α := δ)) parent

theorem eligible_accessibility (parent : δ) :
    eligible edge parent = true ↔ Acc (Function.swap edge) parent :=
  (rounds_correspondence edge _ parent).trans (Finite.Foundation.stable_kernel edge parent)

theorem eligible_material_domain (parent : δ) :
    eligible edge parent = true ↔ (HSet.decorate edge parent).WF :=
  (eligible_accessibility edge parent).trans HSet.wf_decorate_iff.symm

end Foundation

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout.FiniteBoolean
