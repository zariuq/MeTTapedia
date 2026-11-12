import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRebaseDomain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualTensorInterpretation

/-!
# Selected composition of two complete source-local helper runs

The construction executes the left input in the right context, then the right
input in the resulting left context. Its exact domain retains the raw empty
run case, checks initial joint consistency when work occurs and checks only
the output freshness needed by this order. It chooses no ambient scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs

variable {S : Signature} {O : Type} [DecidableEq O]

namespace ContextPlacement

abbrev swap {left right : State S O} (placed : ContextPlacement left right) : ContextPlacement right left :=
  ⟨placed.frame, placed.rightMap, placed.leftMap⟩

def swapIso {left right : State S O} (placed : ContextPlacement left right) :
    helperStep.StateIso placed.swap.state placed.state where
  frame := Frames.Iso.refl _
  knowledge := (Frames.Iso.equivalent_refl _).trans (by
    intro target mapping
    rw [Frames.models_append, Frames.models_append]
    exact and_comm)
  rename := Equiv.refl O
  present := by
    simp only [Equiv.refl_toEmbedding, Finset.map_refl]
    exact Finset.union_comm _ _

end ContextPlacement

abbrev contextualFlip : (contextualRunInterpretation (S := S) (O := O)).Flip where
  swap := ContextPlacement.swap
  stateIso := ContextPlacement.swapIso

theorem contextualFlip_lawful : (contextualFlip (S := S) (O := O)).Lawful where
  swap_swap _ := rfl
  left_natural placed := by
    change (Frames.contextual S).Agree
      ((Frames.contextual S).comp ((Frames.contextual S).id placed.frame) placed.rightMap) placed.rightMap
    intro term
    rw [(Frames.contextual S).act_comp, (Frames.contextual S).act_id]
    exact ((Frames.contextual S).equivalence _).refl _
  right_natural placed := by
    change (Frames.contextual S).Agree
      ((Frames.contextual S).comp ((Frames.contextual S).id placed.frame) placed.leftMap) placed.leftMap
    intro term
    rw [(Frames.contextual S).act_comp, (Frames.contextual S).act_id]
    exact ((Frames.contextual S).equivalence _).refl _

theorem RebasePlan.target_solvable_iff : ∀ {left right : State S O} (placed : ContextPlacement left right)
    (run : helperStep.Run left) (plan : RebasePlan S O placed run),
    (Frames.contextual S).Solvable (RebasePlan.realize placed run plan).target.state.knowledge ↔
      (Frames.contextual S).Solvable placed.state.knowledge
  | _, _, _, .nil _, .nil _ => Iff.rfl
  | _, _, placed, .cons f _ rest, .cons _ _ tail =>
      (target_solvable_iff (placed.afterLeft f) rest tail).trans (placed.after_left_solvable_iff f)

abbrev TensorPlan {left right : State S O} (placed : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right) :=
  contextualRunInterpretation.TensorPlan contextualFlip placed first second

abbrev TensorRealization {left right : State S O} (placed : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right) :=
  contextualRunInterpretation.TensorResult placed first second

def TensorPlan.realize {left right : State S O} {placed : ContextPlacement left right}
    {first : helperStep.Run left} {second : helperStep.Run right} (plan : TensorPlan placed first second) :
    TensorRealization placed first second :=
  ContextualRunInterpretation.TensorPlan.realize contextualRunInterpretation contextualFlip plan

def TensorDomain {left right : State S O} (placed : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right) : Prop :=
  ((first.word = [] ∧ second.word = []) ∨ (Frames.contextual S).Solvable placed.state.knowledge) ∧
    OutputsAvoid first right.present ∧ OutputsAvoid second first.last.present

theorem tensor_plan_iff_domain {left right : State S O} (placed : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right) :
    Nonempty (TensorPlan placed first second) ↔ TensorDomain placed first second := by
  constructor
  · rintro ⟨plan⟩
    have one := (rebase_plan_iff_aggregate placed first).mp ⟨plan.leftPlan⟩
    have two := (rebase_plan_iff_aggregate _ second).mp ⟨plan.rightPlan⟩
    have same : (Frames.contextual S).Solvable (RebasePlan.realize placed first plan.leftPlan).target.swap.state.knowledge ↔
        (Frames.contextual S).Solvable placed.state.knowledge :=
      (RebasePlan.realize placed first plan.leftPlan).target.swapIso.solvable_iff.trans
        (RebasePlan.target_solvable_iff placed first plan.leftPlan)
    refine ⟨?_, one.2, two.2⟩
    rcases one.1 with emptyFirst | solved
    · rcases two.1 with emptySecond | solved
      · exact Or.inl ⟨emptyFirst, emptySecond⟩
      · exact Or.inr (same.mp solved)
    · exact Or.inr solved
  · rintro ⟨work, firstFresh, secondFresh⟩
    have initial : first.word = [] ∨ (Frames.contextual S).Solvable placed.state.knowledge :=
      work.imp And.left id
    obtain ⟨leftPlan⟩ := (rebase_plan_iff_aggregate placed first).mpr ⟨initial, firstFresh⟩
    have same : (Frames.contextual S).Solvable (RebasePlan.realize placed first leftPlan).target.swap.state.knowledge ↔
        (Frames.contextual S).Solvable placed.state.knowledge :=
      (RebasePlan.realize placed first leftPlan).target.swapIso.solvable_iff.trans
        (RebasePlan.target_solvable_iff placed first leftPlan)
    have later : second.word = [] ∨
        (Frames.contextual S).Solvable (RebasePlan.realize placed first leftPlan).target.swap.state.knowledge :=
      work.elim (fun empty => Or.inl empty.2) (fun solved => Or.inr (same.mpr solved))
    obtain ⟨rightPlan⟩ := (rebase_plan_iff_aggregate _ second).mpr ⟨later, secondFresh⟩
    exact ⟨⟨leftPlan, rightPlan⟩⟩

theorem native_tensor_of_domain {left right : State S O} (placed : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right) (defined : TensorDomain placed first second) :
    Nonempty (TensorRealization placed first second) := by
  obtain ⟨plan⟩ := (tensor_plan_iff_domain placed first second).mpr defined
  exact ⟨TensorPlan.realize plan⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
