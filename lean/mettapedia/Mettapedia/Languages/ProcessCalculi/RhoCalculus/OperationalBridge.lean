import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SpiceRule

/-!
# Operational Bridge for ρ-Calculus

This file makes explicit the intended layering of the ρ-calculus operational
infrastructure:

- `Reduction.Reduces` is the foundational one-step semantic relation.
- `Spice.presentMoment` is exactly the one-step semantic image of a process.
- `Spice.reachableStates p 1` is a different notion: it also includes the
  current state `p`, because it is bounded by `≤ 1` step rather than exact
  one-step reachability.
- `Context.LabeledTransition` is a contextual presentation of the same
  one-step semantics.
- `Engine.reduceStep` is an executable meta-level reducer whose outputs are
  proven sound with respect to the semantic present moment.

The point of this bridge is to keep derived tooling honest: if any layer is
misread as the semantics itself, the exact-vs-bounded distinction disappears
and "current state" gets conflated with "one-step successor".
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.OperationalBridge

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Reduction

/-- A process is in the semantic present moment of `p` exactly when it is a
    one-step reduct of `p`. -/
theorem mem_presentMoment_iff_reduces {p q : Pattern} :
    q ∈ Spice.presentMoment p ↔ Nonempty (Reduces p q) := by
  simp [Spice.presentMoment, Spice.futureStates, ReducesN.one_iff_reduces]

/-- `CanStep` is exactly nonemptiness of the semantic present moment. -/
theorem canStep_iff_presentMoment_nonempty (p : Pattern) :
    CanStep p ↔ (Spice.presentMoment p).Nonempty := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, (mem_presentMoment_iff_reduces).2 hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, (mem_presentMoment_iff_reduces).1 hq⟩

/-- Normal forms are exactly the processes whose semantic present moment is empty. -/
theorem normalForm_iff_presentMoment_eq_empty (p : Pattern) :
    NormalForm p ↔ Spice.presentMoment p = ∅ := by
  constructor
  · intro hnf
    ext q
    constructor
    · intro hq
      exact False.elim (hnf ⟨q, (mem_presentMoment_iff_reduces).1 hq⟩)
    · intro hq
      exact False.elim hq
  · intro hempty hstep
    obtain ⟨q, hq⟩ := hstep
    have hmem : q ∈ Spice.presentMoment p := (mem_presentMoment_iff_reduces).2 hq
    simp [hempty] at hmem

/-- The current state is always reachable in `≤ 1` step, which is why
    `reachableStates p 1` must not be confused with the exact one-step
    semantic present moment. -/
theorem current_mem_reachableStates_one (p : Pattern) :
    p ∈ Spice.reachableStates p 1 := by
  exact ⟨0, Nat.zero_le 1, ⟨ReducesN.zero p⟩⟩

/-- A normal form is not in its own semantic present moment. This is the
    generic witness behind the "reachable in ≤ 1 step" vs "exactly one step"
    distinction. -/
theorem current_not_mem_presentMoment_of_normalForm {p : Pattern}
    (hnf : NormalForm p) :
    p ∉ Spice.presentMoment p := by
  intro hmem
  exact hnf ⟨p, (mem_presentMoment_iff_reduces).1 hmem⟩

/-- For a normal form, `reachableStates p 1` still contains `p`, while the
    semantic present moment does not. Treating `reachableStates p 1` as
    "the one-step frontier" therefore introduces a false positive. -/
theorem reachableStates_one_false_positive_of_normalForm {p : Pattern}
    (hnf : NormalForm p) :
    p ∈ Spice.reachableStates p 1 ∧ p ∉ Spice.presentMoment p := by
  exact ⟨current_mem_reachableStates_one p, current_not_mem_presentMoment_of_normalForm hnf⟩

/-- `reachableStates p 1` splits into the current state plus the exact
    semantic one-step successors. This is the key guardrail against confusing
    `≤ 1`-step reachability with one-step semantics. -/
theorem reachableStates_one_eq_current_union_present (p : Pattern) :
    Spice.reachableStates p 1 = ({p} ∪ Spice.presentMoment p) := by
  ext q
  constructor
  · intro hq
    rcases hq with ⟨k, hk, hkq⟩
    have hk_cases : k = 0 ∨ k = 1 := by omega
    cases hk_cases with
    | inl hk0 =>
        left
        have hpq : p = q := by
          exact (ReducesN.zero_iff_eq p q).mp (by simpa [hk0] using hkq)
        simpa [Set.mem_singleton_iff] using hpq.symm
    | inr hk1 =>
        right
        simpa [Spice.presentMoment, Spice.futureStates, hk1] using hkq
  · intro hq
    rcases hq with hcur | hpres
    · have hqp : q = p := by
        simpa [Set.mem_singleton_iff] using hcur
      exact ⟨0, Nat.zero_le 1, (ReducesN.zero_iff_eq p q).mpr hqp.symm⟩
    · exact ⟨1, Nat.le_refl 1, by simpa [Spice.presentMoment, Spice.futureStates] using hpres⟩

/-- Contextual labeled transition is equivalent to exact one-step reachability
    from the filled context. -/
theorem labeledTransition_iff_presentMoment_fill {p q : Pattern} {k : Context.EvalContext} :
    Nonempty (Context.LabeledTransition p k q) ↔
      q ∈ Spice.presentMoment (Context.fillEvalContext k p) := by
  constructor
  · intro hlt
    have hred : Nonempty (Reduces (Context.fillEvalContext k p) q) :=
      Context.labeled_implies_reduces hlt
    exact (mem_presentMoment_iff_reduces).2 hred
  · intro hpm
    exact ⟨Context.LabeledTransition.from_reduction ((mem_presentMoment_iff_reduces).1 hpm)⟩

/-- Hole-labeled transition is exactly the semantic present moment of the term itself. -/
theorem labeledTransition_hole_iff_presentMoment {p q : Pattern} :
    Nonempty (Context.LabeledTransition p Context.EvalContext.hole q) ↔
      q ∈ Spice.presentMoment p := by
  simpa [Context.fillEvalContext_hole] using
    (labeledTransition_iff_presentMoment_fill (p := p) (q := q)
      (k := Context.EvalContext.hole))

/-- Every executable one-step reduct lies in the semantic present moment. -/
theorem reduceStep_mem_presentMoment {p q : Pattern} {fuel : Nat}
    (h : q ∈ Engine.reduceStep p fuel) :
    q ∈ Spice.presentMoment p := by
  have hred : Nonempty (Reduces p q) := Engine.reduceStep_sound p q fuel h
  exact (mem_presentMoment_iff_reduces).2 hred

/-- Every executable one-step reduct is reachable within the semantic
    `≤ 1`-step horizon. -/
theorem reduceStep_mem_reachableStates_one {p q : Pattern} {fuel : Nat}
    (h : q ∈ Engine.reduceStep p fuel) :
    q ∈ Spice.reachableStates p 1 := by
  exact (Spice.futureStates_subset_reachable p 1)
    (by simpa [Spice.presentMoment] using reduceStep_mem_presentMoment h)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.OperationalBridge
