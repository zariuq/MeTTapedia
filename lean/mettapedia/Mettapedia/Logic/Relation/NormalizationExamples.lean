import Mettapedia.Logic.Relation.Normalization
import Mathlib.Data.Nat.Basic

/-!
# Strategy and termination boundaries for certified normalization

Two different natural-number strategies instantiate the same normalization
construction. A branching relation exhibits why uniqueness requires confluence;
a self-loop exhibits why a complete selector cannot replace termination.
-/

namespace Mettapedia.Logic.Relation.NormalizationExamples

open _root_.Relation

def decreases (source target : Nat) : Prop := target < source

def predecessor : CompleteStepSelector decreases where
  step
    | 0 => none
    | n + 1 => some ⟨n, Nat.lt_succ_self n⟩
  none_iff_normal := by
    intro source
    cases source with
    | zero => exact ⟨fun _ target => Nat.not_lt_zero target, fun _ => rfl⟩
    | succ n => exact ⟨(fun h => nomatch h), fun h => False.elim (h n (Nat.lt_succ_self n))⟩

def jumpToZero : CompleteStepSelector decreases where
  step
    | 0 => none
    | n + 1 => some ⟨0, Nat.zero_lt_succ n⟩
  none_iff_normal := by
    intro source
    cases source with
    | zero => exact ⟨fun _ target => Nat.not_lt_zero target, fun _ => rfl⟩
    | succ n => exact ⟨(fun h => nomatch h), fun h => False.elim (h 0 (Nat.zero_lt_succ n))⟩

theorem decreases_to_zero (source : Nat) : ReflTransGen decreases source 0 := by
  cases source with
  | zero => exact .refl
  | succ n => exact .single (Nat.zero_lt_succ n)

theorem decreases_confluent : Confluent decreases :=
  fun _ left right _ _ => ⟨0, decreases_to_zero left, decreases_to_zero right⟩

/-- These strategies genuinely select different outgoing steps. -/
theorem strategies_differ : predecessor.step 3 ≠ jumpToZero.step 3 := by decide

/-- The generic theorem relates independently implemented strategies on every
natural number, using the actual well-foundedness of strict decrease. -/
theorem strategies_agree (source : Nat) :
    (predecessor.normalize source (Nat.lt_wfRel.wf.apply source)).normalForm =
      (jumpToZero.normalize source (Nat.lt_wfRel.wf.apply source)).normalForm :=
  predecessor.normalize_strategy_independent decreases_confluent jumpToZero source _

theorem predecessor_computes :
    (predecessor.normalize 3 (Nat.lt_wfRel.wf.apply 3)).normalForm = 0 := by decide +kernel

theorem jump_computes :
    (jumpToZero.normalize 3 (Nat.lt_wfRel.wf.apply 3)).normalForm = 0 := by decide +kernel

inductive Fork where
  | root | left | right
  deriving DecidableEq

inductive ForkStep : Fork → Fork → Prop where
  | left : ForkStep .root .left
  | right : ForkStep .root .right

def leftResult : NormalizationResult ForkStep .root :=
  ⟨.left, .single .left, fun _ h => nomatch h⟩

def rightResult : NormalizationResult ForkStep .root :=
  ⟨.right, .single .right, fun _ h => nomatch h⟩

/-- Reduction to normal forms alone does not make those forms unique. -/
theorem normal_forms_need_confluence :
    leftResult.normalForm ≠ rightResult.normalForm ∧ ¬ Confluent ForkStep := by
  refine ⟨by decide, ?_⟩
  intro confluent
  have equal := leftResult.eq_of_eqvGen confluent rightResult (EqvGen.refl Fork.root)
  cases equal

/-- A complete selector may keep returning a valid step forever. -/
def selfLoopSelector : CompleteStepSelector (fun a b : Unit => a = b) where
  step source := some ⟨source, rfl⟩
  none_iff_normal source :=
    ⟨(fun h => nomatch h), fun h => False.elim (h source rfl)⟩

theorem self_loop_not_accessible (source : Unit) :
    ¬ Acc (fun target source : Unit => source = target) source := by
  intro accessible
  induction accessible with
  | intro source _ ih => exact ih source rfl

#print axioms strategies_agree
#print axioms predecessor_computes
#print axioms normal_forms_need_confluence
#print axioms self_loop_not_accessible

end Mettapedia.Logic.Relation.NormalizationExamples
