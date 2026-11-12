import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaApplicationContexts
import Mettapedia.Languages.MeTTa.PeTTa.PartialApplicationExpansion
import Mettapedia.Languages.MeTTa.PeTTa.DynamicRecovery

/-!
# Runtime application and private captures in actual PeTTa contexts

The private-carrier expansion now enters the real source machine, rather than
remaining a structural vector lemma. The dispatcher reuses held captures and
already evaluated supplied values. Its exact run law retains every outcome,
including suspension, and charges the expansion's administrative step.

Computed-head entry evaluates the head before its remaining arguments, keeping
the real dispatch continuation. Runtime calls catch callee errors at their own
boundary; completed root answers and reached effects survive recovery. This is
the source machine's completed-operand profile, not a streaming equivalence or
a specification of lambda authoring/installation and every native overload.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaDynamicContexts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying PeTTaContexts

theorem resolve_partial (bindings : Subst) (head : String) (captured : List Atom) :
    resolve bindings (Eval.partialValue head captured) =
      Eval.partialValue head (captured.map (resolve bindings)) := by
  have lists : ∀ items : List Atom,
      applySubst.applySubstList bindings items = items.map (resolve bindings) := by
    intro items
    induction items with
    | nil => rfl
    | cons first rest ih => simp [applySubst.applySubstList, ih]
  simp [Eval.partialValue, Eval.partialTag, applySubst, lists]

theorem partial_step (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (head : String) (captured supplied : List Atom) :
    step registry { base with control := .dynamic bindings (Eval.partialValue head captured) supplied } =
      some { base with
        control := .dynamic bindings (.symbol head) (captured.map (resolve bindings) ++ supplied.map (resolve bindings)) } := by
  apply transition_step
  exact .dynamic_partial rfl (by rw [resolve_partial]; rfl)

/-- No extra evaluation of stored syntax occurs during structural completion. -/
theorem partial_run (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (head : String) (captured supplied : List Atom) (fuel : Nat) :
    run registry (fuel + 1)
      { base with control := .dynamic bindings (Eval.partialValue head captured) supplied } =
      run registry fuel { base with
        control := .dynamic bindings (.symbol head) (captured.map (resolve bindings) ++ supplied.map (resolve bindings)) } :=
  run_succ_of_step registry fuel _ _ (partial_step registry base bindings head captured supplied)

theorem partial_transition_exact (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (head : String) (captured supplied : List Atom) (next : Configuration) :
    Transition registry { base with control := .dynamic bindings (Eval.partialValue head captured) supplied } next ↔
      next = { base with
        control := .dynamic bindings (.symbol head) (captured.map (resolve bindings) ++ supplied.map (resolve bindings)) } := by
  rw [← step_iff_transition, partial_step]
  simp only [Option.some.injEq, eq_comm]

/-- The earlier independently specified partial-vector operation has this
actual source consumer. Both sides retain stored-then-supplied order. -/
theorem expanded_vector (bindings : Subst) (head : String) (captured supplied : List Atom) :
    (.symbol head :: (captured.map (resolve bindings) ++ supplied.map (resolve bindings))) =
      (PartialApplicationExpansion.expand
        (⟨.symbol head, captured⟩ : PartialApplicationExpansion.Partial Atom) supplied).map (resolve bindings) := by
  simp [PartialApplicationExpansion.expand, applySubst]

theorem computed_head_shape (head : Atom) (arguments : List Atom)
    (dynamic : dynamicItems (head :: arguments) = true) :
    (∀ name tail, head :: arguments ≠ .symbol name :: tail) ∧
      partial? (.expression (head :: arguments)) = none := by
  cases head <;> simp_all [dynamicItems, partial?]

theorem computed_head_run (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (head : Atom) (arguments : List Atom)
    (dynamic : dynamicItems (head :: arguments) = true) (fuel : Nat) :
    run registry (2 + fuel) (atExpression base bindings (.expression (head :: arguments))) =
      run registry fuel (atExpression { base with
        frames := .argument .data arguments [] 0 :: .dispatch :: base.frames } bindings head) := by
  have shape := computed_head_shape head arguments dynamic
  have first := transition_step (Transition.dynamic_enter
    (registry := registry) (source := atExpression base bindings (.expression (head :: arguments)))
    rfl shape.1 shape.2 dynamic)
  have second := transition_step (Transition.evaluated_argument
    (registry := registry) (source := { base with
      control := .arguments bindings .data (head :: arguments) [] 0
      frames := .dispatch :: base.frames }) rfl rfl)
  dsimp only [atExpression] at first second ⊢
  rw [show 2 + fuel = (fuel + 1) + 1 by omega,
    run_succ_of_step registry (fuel + 1) _ _ first, run_succ_of_step registry fuel _ _ second]

/-- Runtime-head entry composes with arbitrary admitted source contexts. The
head still runs above its dispatch frame and the caller's ordered frames. -/
theorem contextual_computed_head_run (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (context : PeTTaApplicationContexts.Context) (frames : List Frame)
    (head : Atom) (arguments : List Atom)
    (admitted : PeTTaApplicationContexts.compile registry bindings context (.expression (head :: arguments)) =
      some frames) (dynamic : dynamicItems (head :: arguments) = true) (fuel : Nat) :
    run registry (PeTTaApplicationContexts.cost context + (2 + fuel))
      (atExpression base bindings
        (PeTTaApplicationContexts.plug context (.expression (head :: arguments)))) =
      run registry fuel (atExpression { base with
        frames := .argument .data arguments [] 0 :: .dispatch :: (frames ++ base.frames) } bindings head) := by
  rw [PeTTaApplicationContexts.run_context registry context base bindings _ frames admitted]
  exact computed_head_run registry { base with frames := frames ++ base.frames } bindings head arguments dynamic fuel

theorem runtime_native_entry (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (head : String) (values : List Atom)
    (native : (Eval.ioHead head || StdLib.known head) = true) :
    Transition registry { base with control := .dynamic bindings (.symbol head) values }
      { base with
        control := .arguments bindings (.function head) [] (values.map (resolve bindings)) 0
        frames := .dynamicCall :: base.frames } :=
  .dynamic_native rfl rfl native

/-- Catching a callee fault changes control and closes only that call's scope.
The reached store, I/O and source-use counter come from the faulted state. -/
theorem recovery_run (registry : SpaceSemantics.Program) (base : Configuration)
    (reason : Effects.Fault) (answers : List Answer) (remaining : List Frame)
    (recovered : Recovers [] base.frames answers remaining) (fuel : Nat) :
    run registry (fuel + 1) { base with control := .fault reason } =
      run registry fuel { base with control := .returned answers, frames := remaining } := by
  apply run_succ_of_step
  exact transition_step (.fault_caught rfl recovered.computed)

theorem recovery_transition_exact (registry : SpaceSemantics.Program) (base : Configuration)
    (reason : Effects.Fault) (answers : List Answer) (remaining : List Frame)
    (recovered : Recovers [] base.frames answers remaining) (next : Configuration) :
    Transition registry { base with control := .fault reason } next ↔
      next = { base with control := .returned answers, frames := remaining } := by
  have computed := transition_step (Transition.fault_caught (registry := registry)
    (source := { base with control := .fault reason }) rfl recovered.computed)
  rw [← step_iff_transition, computed]
  simp only [Option.some.injEq, eq_comm]

theorem recovery_keeps_effects (registry : SpaceSemantics.Program) (base : Configuration)
    (reason : Effects.Fault) (next : Configuration)
    (taken : Transition registry { base with control := .fault reason } next) :
    next.state = base.state ∧ next.input = base.input ∧ next.output = base.output ∧ next.uses = base.uses := by
  have computed := transition_step taken
  cases recovered : recoverDynamic [] base.frames with
  | none => simp [step, recovered] at computed
  | some pair =>
      rcases pair with ⟨answers, rest⟩
      simp only [step, recovered, Option.some.injEq] at computed
      subst next
      exact ⟨rfl, rfl, rfl, rfl⟩

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaDynamicContexts
