import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec

/-!
# Independent rules for runtime-call error recovery

Recovery closes the nearest call scope. A pending operand or continuation
discards its tentative prefix; root alternative collectors prepend their
completed answers; the call boundary returns that prefix and retains its
caller. These rules mention no recovery algorithm.
The actual source helper and fault transition preserve and reflect them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

inductive Recovers : List Answer → List Frame → List Answer → List Frame → Prop where
  | boundary (earned : List Answer) (caller : List Frame) :
      Recovers earned (.dynamicCall :: caller) earned caller
  | sequence {earned completed answers : List Answer} {pending : List Control} {frames caller : List Frame} :
      Recovers (completed ++ earned) frames answers caller →
      Recovers earned (.sequence pending completed :: frames) answers caller
  | frame (head : Frame) {earned answers : List Answer} {frames caller : List Frame}
      (notBoundary : head ≠ .dynamicCall)
      (notCollector : ∀ pending completed, head ≠ .sequence pending completed) :
      Recovers [] frames answers caller → Recovers earned (head :: frames) answers caller

theorem Recovers.computed {earned answers : List Answer} {frames caller : List Frame}
    (recovery : Recovers earned frames answers caller) :
    recoverDynamic earned frames = some (answers, caller) := by
  induction recovery with
  | boundary => rfl
  | sequence previous ih => exact ih
  | frame head notBoundary notCollector previous ih =>
      cases head with
      | dynamicCall => exact False.elim (notBoundary rfl)
      | sequence pending completed => exact False.elim (notCollector pending completed rfl)
      | _ => exact ih

theorem Recovers.of_computed (earned : List Answer) (frames : List Frame)
    (answers : List Answer) (caller : List Frame)
    (computed : recoverDynamic earned frames = some (answers, caller)) :
    Recovers earned frames answers caller := by
  induction frames generalizing earned with
  | nil => cases computed
  | cons head rest ih =>
      cases head with
      | dynamicCall =>
          simp only [recoverDynamic, Option.some.injEq, Prod.mk.injEq] at computed
          rcases computed with ⟨rfl, rfl⟩
          exact .boundary _ _
      | sequence pending completed => exact .sequence (ih (completed ++ earned) computed)
      | _ =>
          refine .frame _ ?_ ?_ (ih [] computed)
          · intro impossible
            cases impossible
          · intro pending completed impossible
            cases impossible

theorem recovery_iff (earned answers : List Answer) (frames caller : List Frame) :
    recoverDynamic earned frames = some (answers, caller) ↔ Recovers earned frames answers caller :=
  ⟨Recovers.of_computed earned frames answers caller, Recovers.computed⟩

theorem Recovers.deterministic {earned first second : List Answer} {frames left right : List Frame}
    (one : Recovers earned frames first left) (two : Recovers earned frames second right) :
    (first, left) = (second, right) :=
  Option.some.inj (one.computed.symm.trans two.computed)

theorem no_recovery_without_frames (earned answers : List Answer) (caller : List Frame) :
    ¬ Recovers earned [] answers caller := by
  intro recovery
  cases recovery

/-- A temporary argument frame does not turn tentative data into root answers.
The nearest root collector supplies the completed alternatives. -/
theorem argument_recovery (earned completed : List Answer) (target : Eval.Target)
    (arguments values : List Mettapedia.Languages.MeTTa.OSLFCore.Atom) (index : Nat)
    (pending : List Control) (caller : List Frame) :
    Recovers earned (.argument target arguments values index ::
      .sequence pending completed :: .dynamicCall :: caller) completed caller := by
  refine .frame _ (by intro impossible; cases impossible)
    (by intro pending completed impossible; cases impossible) ?_
  apply Recovers.sequence (completed := completed)
  simpa only [List.append_nil] using Recovers.boundary completed caller

/-- The source fault rule has exactly the independently specified recovery
events; the target state retains the reached effects and use counter. -/
theorem fault_transition_iff_recovery (registry : SpaceSemantics.Program) (base : Configuration)
    (reason : Effects.Fault) (next : Configuration) :
    Transition registry { base with control := .fault reason } next ↔
      ∃ answers caller, Recovers [] base.frames answers caller ∧
        next = { base with control := .returned answers, frames := caller } := by
  constructor
  · intro transition
    have computed := transition_step transition
    cases recovered : recoverDynamic [] base.frames with
    | none => simp [step, recovered] at computed
    | some pair =>
        rcases pair with ⟨answers, caller⟩
        simp only [step, recovered, Option.some.injEq] at computed
        subst next
        exact ⟨answers, caller, Recovers.of_computed [] base.frames answers caller recovered, rfl⟩
  · rintro ⟨answers, caller, recovery, rfl⟩
    exact .fault_caught rfl recovery.computed

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
