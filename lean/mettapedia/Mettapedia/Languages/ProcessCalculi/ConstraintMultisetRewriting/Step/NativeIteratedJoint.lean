import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeIteratedControls

/-!
# One joint state for every order, and clearness is not kept by residuals

## One joint state

`Step/NativeIteratedAgreement` shows that every two orders of a clear family end in states that agree
up to dead names. Agreement is a cospan of dead-name extensions, and two dead-name extensions of one
state amalgamate by pushout (`NativeDead.pushout`). So the finitely many final states have **one joint
state** (`one_joint_state`): every order's final state is included in one state by a dead-name
extension. The names each inclusion misses are dead.

## Clearness is not kept by residuals

The residuals of two pairwise clear firings after a third pairwise clear firing need not be clear
(`clear_not_kept`): after `X = true`, the residuals of `Y = false` and `X = Y` have no joint solution.
So the residual of a pairwise clear family is not pairwise clear, and `FamilyClear`'s joint
solvability is what `familyClear_residual` keeps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual NativeDead NativeIterated

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeIterated

variable {s : NativeState S O Γ sort}

/-- **One joint state for finitely many orders**: when the final state of the given order agrees up to
dead names with the final state of each listed order, all of them include into one state by dead-name
extensions. -/
theorem joint_of_orders {fs : List (LiveFiring s)} (clear : FamilyClear s fs) {t₀ : NativeState S O Γ sort}
    (run : Sequential s fs t₀) :
    ∀ orders : List (List (LiveFiring s)), (∀ order ∈ orders, order.Perm fs) →
      ∃ w, Nonempty (DeadExtension t₀ w) ∧
        ∀ order ∈ orders, ∀ t, Sequential s order t → Nonempty (DeadExtension t w)
  | [], _ => ⟨t₀, ⟨DeadExtension.refl t₀⟩, fun _ member => absurd member List.not_mem_nil⟩
  | order :: rest, perms => by
      obtain ⟨w, ⟨into⟩, others⟩ := joint_of_orders clear run rest fun o member => perms o (List.mem_cons_of_mem _ member)
      obtain ⟨t, other⟩ := every_order_admitted clear (perms order List.mem_cons_self)
      obtain ⟨u, ⟨first⟩, ⟨second⟩⟩ :=
        orders_agree _ fs rfl clear (perms order List.mem_cons_self) run other
      refine ⟨pushout w first, ⟨into.comp (pushoutLeft w first)⟩, fun o member t' run' => ?_⟩
      rcases List.mem_cons.mp member with rfl | inRest
      · rw [run'.unique other]
        exact ⟨second.comp (pushoutRight into first)⟩
      · obtain ⟨inclusion⟩ := others o inRest t' run'
        exact ⟨inclusion.comp (pushoutLeft w first)⟩

/-- **One joint state**: every order of a clear family ends in a state that is included, by a
dead-name extension, in one state, into which the run of the family as given is included as well. -/
theorem one_joint_state {fs : List (LiveFiring s)} (clear : FamilyClear s fs) :
    ∃ w, ∀ order : List (LiveFiring s), order.Perm fs → ∃ t, Sequential s order t ∧ Nonempty (DeadExtension t w) := by
  obtain ⟨t₀, run⟩ := every_order_admitted clear (List.Perm.refl fs)
  obtain ⟨w, _, all⟩ := joint_of_orders clear run fs.permutations fun order member => List.mem_permutations.mp member
  refine ⟨w, fun order perm => ?_⟩
  obtain ⟨t, other⟩ := every_order_admitted clear perm
  exact ⟨t, other, all order (List.mem_permutations.mpr perm) t other⟩

end NativeIterated

namespace NativeIteratedControls

/-- After `X = true`, the residuals of `X = Y` and `Y = false` have no joint solution. -/
theorem residuals_not_jointly (G : ContextualConditionalExecution.Firing pair.locals pair.state)
    (problem : problemOf pair G.selection G.rule = tellX.toNative.information) {b : Frames.Frame NativeResidualExample.tiny}
    (J : Joint (rawTarget G) (tellSame.residualAt G).toNative.information
      (problemOf (rawTarget G) (tellY.residualAt G).selection (tellY.residualAt G).rule) b) : False := by
  have unmadeSame : ∀ o ∈ tellSame.selection.taken ++ tellSame.selection.read, o ∉ G.selection.made :=
    fun _ member => absurd member List.not_mem_nil
  have unmadeY : ∀ o ∈ tellY.selection.taken ++ tellY.selection.read, o ∉ G.selection.made :=
    fun _ member => absurd member List.not_mem_nil
  have sameModels := (models_tellSame (Assignment.compose J.left (carry G))).mp
    (Joint.ofResidual G tellSame unmadeSame J.left J.left_models).left_models
  have yModels := (models_tellY (Assignment.compose J.right (carry G))).mp
    (Joint.ofResidual G tellY unmadeY J.right J.right_models).left_models
  have xModels := (models_tellX (Assignment.compose (Assignment.compose J.left (laterCaptured G))
      (ContextualComputedFreshFrame.includeSource G.update))).mp
    (Eq.mp (congrArg (ContextualResidual.Models _) problem)
      (Joint.ofResidual G tellSame unmadeSame J.left J.left_models).right_models)
  have readLeft : ∀ x : Bool, Assignment.compose J.left (carry G) (.inr x) = J.left (.inr (.inl (.inr x))) :=
    fun x => instantiate_generator J.left (.inr (.inl (.inr x)))
  have readRight : ∀ x : Bool, Assignment.compose J.right (carry G) (.inr x) = J.right (.inr (.inl (.inr x))) :=
    fun x => instantiate_generator J.right (.inr (.inl (.inr x)))
  have readKnowledge : ∀ x : Bool, Assignment.compose (Assignment.compose J.left (laterCaptured G))
      (ContextualComputedFreshFrame.includeSource G.update) (.inr x) = J.left (.inr (.inl (.inr x))) :=
    fun x => (congrArg (instantiate (Assignment.compose J.left (laterCaptured G))) (includeSource_apply G (.inr x))).trans
      ((instantiate_generator (Assignment.compose J.left (laterCaptured G)) (.inl (.inr x))).trans
        (instantiate_generator J.left (.inr (.inl (.inr x)))))
  have shared : ∀ x : Bool, J.left (.inr (.inl (.inr x))) = J.right (.inr (.inl (.inr x))) :=
    fun x => J.agree_at (.inl (.inr x))
  have clash : NativeResidualExample.bit b.arity true = NativeResidualExample.bit b.arity false :=
    xModels.symm.trans ((readKnowledge true).trans ((readLeft true).symm.trans (sameModels.trans
      ((readLeft false).trans ((shared false).trans ((readRight false).symm.trans yModels))))))
  unfold NativeResidualExample.bit at clash
  cases clash

/-- **Clearness is not kept by residuals**: after `X = true`, the residuals of `X = Y` and `Y = false` do
not leave each other clear, although the three tellers are pairwise clear. -/
theorem clear_not_kept :
    ¬ Clear (residualAfter (tellers_admitted tellX List.mem_cons_self) tellSame)
      (residualAfter (tellers_admitted tellX List.mem_cons_self) tellY).selection
      (residualAfter (tellers_admitted tellX List.mem_cons_self) tellY).rule
      (residualAfter (tellers_admitted tellX List.mem_cons_self) tellY).outputs := by
  intro clear
  obtain ⟨b, ⟨J⟩⟩ := clear.consistent
  exact residuals_not_jointly (LiveFiring.execution (tellers_admitted tellX List.mem_cons_self))
    (problemOf_execution _) J

end NativeIteratedControls

#print axioms NativeIterated.joint_of_orders
#print axioms NativeIterated.one_joint_state
#print axioms NativeIteratedControls.residuals_not_jointly
#print axioms NativeIteratedControls.clear_not_kept

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
