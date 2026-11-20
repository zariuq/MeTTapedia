import Mettapedia.Logic.LP.FiniteDependencyClosure

/-!
# Repair a recursive positive fact cache after an edit

Take the dependency closure of the edited base facts and the heads
of edited rules, using edges of both programs. Neither additions nor
deletions change derivability outside that closure. Reuse old
consequences only outside it; recompute the affected heads from the
new base and the retained consequences.

This is an exact repair strategy for finite, grounded, set-valued
Horn programs, including positive cycles. It is not a signed
derivative for arbitrary recursive, multiset, or negated queries.
An equality change that also changes the carrier has to be
transported to a common fact type before applying this result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.RecursivePositiveRepair

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.FiniteDependencyClosure (closure closed roots_subset)

variable {Fact : Type*} [DecidableEq Fact] [Fintype Fact]

def changes {A : Type*} [DecidableEq A] (before after : Finset A) : Finset A :=
  (before \ after) ∪ (after \ before)

theorem changes_comm {A : Type*} [DecidableEq A] (before after : Finset A) :
    changes before after = changes after before := Finset.union_comm _ _

def downstream (program : PropProgram Fact) (fact : Fact) : Finset Fact :=
  (program.filter fun r => fact ∈ r.premises).image PropRule.head

def seedsOfChange (oldProgram newProgram : PropProgram Fact) (oldBase newBase : Finset Fact) :
    Finset Fact :=
  changes oldBase newBase ∪ (changes oldProgram newProgram).image PropRule.head

def affected (oldProgram newProgram : PropProgram Fact) (oldBase newBase : Finset Fact) :
    Finset Fact :=
  closure (downstream (oldProgram ∪ newProgram)) (seedsOfChange oldProgram newProgram oldBase newBase)

theorem affected_symm (oldProgram newProgram : PropProgram Fact) (oldBase newBase : Finset Fact) :
    affected oldProgram newProgram oldBase newBase = affected newProgram oldProgram newBase oldBase := by
  unfold affected seedsOfChange
  rw [changes_comm oldBase newBase, changes_comm oldProgram newProgram, Finset.union_comm oldProgram newProgram]

private theorem unchanged_member {A : Type*} [DecidableEq A] {old new : Finset A} {a : A}
    (oldMember : a ∈ old) (unchanged : a ∉ changes old new) : a ∈ new := by
  by_contra removed
  exact unchanged (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨oldMember, removed⟩))

private theorem base_change_affected (oldProgram newProgram : PropProgram Fact) {oldBase newBase : Finset Fact}
    {a : Fact} (changed : a ∈ changes oldBase newBase) :
    a ∈ affected oldProgram newProgram oldBase newBase :=
  roots_subset _ _ (Finset.mem_union_left _ changed)

private theorem rule_change_affected {oldProgram newProgram : PropProgram Fact} (oldBase newBase : Finset Fact)
    {r : PropRule Fact} (changed : r ∈ changes oldProgram newProgram) :
    r.head ∈ affected oldProgram newProgram oldBase newBase :=
  roots_subset _ _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ changed))

private theorem affected_head_of_affected_input {oldProgram newProgram : PropProgram Fact}
    {oldBase newBase : Finset Fact} {a : Fact} {r : PropRule Fact}
    (declared : r ∈ oldProgram ∪ newProgram)
    (uses : a ∈ r.premises) (impacted : a ∈ affected oldProgram newProgram oldBase newBase) :
    r.head ∈ affected oldProgram newProgram oldBase newBase :=
  closed _ _ impacted (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨declared, uses⟩))

theorem derivable_after_of_outside {oldProgram newProgram : PropProgram Fact} {oldBase newBase : Finset Fact}
    {a : Fact} (oldDerivation : Derivable oldProgram oldBase a)
    (outside : a ∉ affected oldProgram newProgram oldBase newBase) :
    Derivable newProgram newBase a := by
  induction oldDerivation with
  | fact fromBase =>
      exact .fact (unchanged_member fromBase (fun changed =>
        outside (base_change_affected oldProgram newProgram changed)))
  | @rule rule declared _ ih =>
      have retained : rule ∈ newProgram := unchanged_member declared (fun changed =>
        outside (rule_change_affected oldBase newBase changed))
      exact .rule retained (fun premise used =>
        ih premise used (fun changed =>
          outside (affected_head_of_affected_input (Finset.mem_union_left _ declared) used changed)))

/-- The retained cache is exact on each unaffected coordinate. The
argument is on finite derivations, not on local support counts. -/
theorem stable_outside {oldProgram newProgram : PropProgram Fact} {oldBase newBase : Finset Fact}
    {a : Fact} (outside : a ∉ affected oldProgram newProgram oldBase newBase) :
    a ∈ saturate oldProgram oldBase ↔ a ∈ saturate newProgram newBase := by
  simp only [saturate_iff_derivable]
  exact ⟨fun derivation => derivable_after_of_outside derivation outside, fun derivation =>
    derivable_after_of_outside derivation
      (affected_symm oldProgram newProgram oldBase newBase ▸ outside)⟩

def repair (oldProgram newProgram : PropProgram Fact) (oldBase newBase : Finset Fact) :
    Finset Fact :=
  let work := affected oldProgram newProgram oldBase newBase
  let keep := saturate oldProgram oldBase \ work
  saturate (newProgram.filter fun r => r.head ∈ work) (newBase ∪ keep)

theorem repair_exact (oldProgram newProgram : PropProgram Fact) (oldBase newBase : Finset Fact) :
    repair oldProgram newProgram oldBase newBase = saturate newProgram newBase := by
  let work := affected oldProgram newProgram oldBase newBase
  let keep := saturate oldProgram oldBase \ work
  let localRules := newProgram.filter fun r => r.head ∈ work
  let repaired := saturate localRules (newBase ∪ keep)
  have retained : keep ⊆ saturate newProgram newBase := by
    intro a present
    obtain ⟨old, outside⟩ := Finset.mem_sdiff.mp present
    exact (stable_outside outside).mp old
  have sound : repaired ⊆ saturate newProgram newBase := by
    intro a member
    exact derivable_subset_of_closed localRules (newBase ∪ keep) (saturate newProgram newBase)
      (Finset.union_subset (saturate_contains_facts _ _) retained)
      (fun r declared ready => rule_closed_saturate newProgram newBase (Finset.mem_filter.mp declared).1 ready)
      a (saturate_sound localRules _ _ member)
  change repaired = saturate newProgram newBase
  refine Finset.Subset.antisymm sound (fun a member => ?_)
  apply derivable_subset_of_closed newProgram newBase repaired
    (Finset.subset_union_left.trans (saturate_contains_facts localRules (newBase ∪ keep))) _
    a (saturate_sound newProgram newBase _ member)
  intro rule declared ready
  by_cases dirty : rule.head ∈ work
  · exact rule_closed_saturate localRules _ (Finset.mem_filter.mpr ⟨declared, dirty⟩) ready
  · have derivableInNew := rule_closed_saturate newProgram newBase declared (ready.trans sound)
    have wasKnown : rule.head ∈ saturate oldProgram oldBase :=
      (stable_outside dirty).mpr derivableInNew
    exact saturate_contains_facts localRules _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨wasKnown, dirty⟩))

namespace Controls

private def cycle : PropProgram (Fin 3) := {⟨{0}, 1⟩, ⟨{1}, 0⟩}

/-- Removing the only ground justification of a cycle removes both
of its consequences while retaining an unrelated seed. -/
theorem deleting_cycle_seed_invalidates_the_cycle :
    repair cycle cycle {0, 2} {2} = {2} := by
  rw [repair_exact]
  decide +kernel

theorem endpoint_subtraction_leaves_an_unsupported_fact :
    (1 : Fin 3) ∈ (saturate cycle {0, 2} \ ({0} : Finset (Fin 3))) ∧
      (1 : Fin 3) ∉ repair cycle cycle {0, 2} {2} := by
  rw [deleting_cycle_seed_invalidates_the_cycle]
  decide +kernel

private def fromNullary : PropProgram (Fin 3) := {⟨∅, 0⟩, ⟨{0}, 1⟩}
private def justImplication : PropProgram (Fin 3) := {⟨{0}, 1⟩}

theorem changing_a_rule_can_invalidate_without_any_base_edit :
    (1 : Fin 3) ∈ saturate fromNullary ∅ ∧
      repair fromNullary justImplication ∅ ∅ = ∅ := by
  rw [repair_exact]
  decide +kernel

end Controls

#print axioms stable_outside
#print axioms repair_exact
#print axioms Controls.deleting_cycle_seed_invalidates_the_cycle
#print axioms Controls.endpoint_subtraction_leaves_an_unsupported_fact
#print axioms Controls.changing_a_rule_can_invalidate_without_any_base_edit

end Mettapedia.GSLT.Contracts.RecursivePositiveRepair
