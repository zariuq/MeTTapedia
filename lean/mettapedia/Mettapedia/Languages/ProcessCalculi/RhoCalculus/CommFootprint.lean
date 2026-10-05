import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelWave
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions

/-!
# The rho COMM rule is a local bag rule

Read on the bag of top-level components, the COMM rule of the rho calculus
replaces a two-atom sub-bag — an output and an input on one channel — by a
one-atom sub-bag, the continuation with the message substituted, in any
surrounding bag.  What it depends on is all in the consumed atoms: matching is
the choice of the two atoms, the substitution is computed from them alone, and
there is no guard, no lookup in the rest of the bag, no freshness check and no
allocation.  So it is a local bag rule, and it inherits everything local bag
rules have:

* every instance has a read/write certificate at the three atom kinds it
  touches, with nothing read besides them (`comm_certified`);
* every instance of the bag rule on component lists is a rho reduction, and
  every head COMM is an instance (`reduces_of_commRule`, `commRule_of_head`);
* two COMMs touching disjoint atom kinds commute as rho reductions
  (`comm_commute`), at the observer that sees only the resulting process.

`ParallelWave.disjointComm_diamond` proves the positional version of the last
point, for four fixed positions; here the positions are irrelevant and the
condition is on kinds.

**Negative.**  Two receivers competing for one message touch the same output
atom, so their footprints overlap, and the diamond genuinely fails: after one
COMM the message is gone (`competing_comm_no_diamond`).

The diamond licenses reordering under its observer only.  An executor's own
representation (indexes, queues, allocation) owes its own synchronization
argument.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CommFootprint

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The sub-bag a COMM on channel `n` consumes. -/
def commConsumed (n q p : Pattern) : Multiset Pattern := {commOut n q, commIn n p}

/-- The sub-bag it produces. -/
def commProduced (q p : Pattern) : Multiset Pattern := {commRes p q}

/-- The COMM rule as a local bag rule. -/
def CommRule (n q p : Pattern) (source target : Multiset Pattern) : Prop :=
  BagRule (commConsumed n q p) (commProduced q p) source target

/-- The atom kinds a COMM touches. -/
def commKinds (n q p : Pattern) : Finset Pattern :=
  (commConsumed n q p).toFinset ∪ (commProduced q p).toFinset

/-- **COMM is local**: on multiplicities it has a read/write certificate that
reads nothing and writes the three kinds it touches, and on bags it is exactly
the restriction of that rule. -/
theorem comm_certified (n q p : Pattern) :
    EffectFootprinted (markingRule (commConsumed n q p) (commProduced q p)).Fires
        ∅ (commKinds n q p) ∧
      ∀ source target, CommRule n q p source target ↔
        (markingRule (commConsumed n q p) (commProduced q p)).Fires
          (marking source) (marking target) :=
  ⟨(markingRule _ _).effectFootprinted, bagRule_iff_fires _ _⟩

/-- A head COMM is an instance of the bag rule. -/
theorem commRule_of_head (n q p : Pattern) (rest : List Pattern) :
    CommRule n q p (commOut n q :: commIn n p :: rest : List Pattern)
      (commRes p q :: rest : List Pattern) :=
  ⟨rest, by simp [commConsumed], by simp [commProduced]⟩

/-- **Every instance of the bag rule on component lists is a rho reduction**:
the head COMM after a permutation of the bag. -/
theorem reduces_of_commRule {n q p : Pattern} {elements targets : List Pattern}
    (step : CommRule n q p elements targets) :
    Nonempty (Reduces (bag elements) (bag targets)) := by
  obtain ⟨frame, sourceDecomposition, targetDecomposition⟩ := step
  have sourcePerm : elements.Perm (commOut n q :: commIn n p :: frame.toList) := by
    rw [← Multiset.coe_eq_coe, sourceDecomposition, ← Multiset.cons_coe, ← Multiset.cons_coe,
      Multiset.coe_toList]
    simp [commConsumed]
  have targetPerm : targets.Perm (commRes p q :: frame.toList) := by
    rw [← Multiset.coe_eq_coe, targetDecomposition, ← Multiset.cons_coe, Multiset.coe_toList]
    simp [commProduced]
  exact ⟨Reduces.equiv (bag_perm sourcePerm) (comm_at_head n q p frame.toList)
    (bag_perm targetPerm.symm)⟩

/-- **Two COMMs touching disjoint atom kinds commute as rho reductions.** -/
theorem comm_commute {n₁ q₁ p₁ n₂ q₂ p₂ : Pattern} {elements first second : List Pattern}
    (disjoint : Disjoint (commKinds n₁ q₁ p₁) (commKinds n₂ q₂ p₂))
    (firstStep : CommRule n₁ q₁ p₁ elements first)
    (secondStep : CommRule n₂ q₂ p₂ elements second) :
    ∃ joined : List Pattern,
      Nonempty (Reduces (bag first) (bag joined)) ∧
        Nonempty (Reduces (bag second) (bag joined)) := by
  obtain ⟨joined, secondThen, firstThen⟩ := bagRule_commute disjoint firstStep secondStep
  refine ⟨joined.toList, reduces_of_commRule (n := n₂) (q := q₂) (p := p₂) ?_,
    reduces_of_commRule (n := n₁) (q := q₁) (p := p₁) ?_⟩
  · rw [Multiset.coe_toList]; exact secondThen
  · rw [Multiset.coe_toList]; exact firstThen

/-- **Competing receivers.**  One message and two receivers on its channel:
either COMM fires, the two touch the same output atom, and after either one the
other can no longer fire. -/
theorem competing_comm_no_diamond (n q p₁ p₂ : Pattern)
    (residualNotMessage : commRes p₁ q ≠ commOut n q) :
    CommRule n q p₁ ([commOut n q, commIn n p₁, commIn n p₂] : List Pattern)
        ([commRes p₁ q, commIn n p₂] : List Pattern) ∧
      ¬ Disjoint (commKinds n q p₁) (commKinds n q p₂) ∧
      ∀ target, ¬ CommRule n q p₂ ([commRes p₁ q, commIn n p₂] : List Pattern) target := by
  refine ⟨commRule_of_head n q p₁ [commIn n p₂], ?_, ?_⟩
  · rw [Finset.not_disjoint_iff]
    exact ⟨commOut n q, by simp [commKinds, commConsumed], by simp [commKinds, commConsumed]⟩
  · rintro target ⟨frame, decomposition, -⟩
    have present : commOut n q ∈
        (([commRes p₁ q, commIn n p₂] : List Pattern) : Multiset Pattern) := by
      rw [decomposition]; simp [commConsumed]
    simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with same | same
    · exact residualNotMessage same.symm
    · simp [commOut, commIn] at same

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CommFootprint

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.CommFootprint.comm_certified
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.CommFootprint.reduces_of_commRule
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.CommFootprint.comm_commute
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.CommFootprint.competing_comm_no_diamond
