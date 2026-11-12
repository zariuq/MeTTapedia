import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextInterpretation

/-!
# Complete local helper runs placed in a native context

Each stage checks joint consistency and freshness against the fixed context.
The actual native execution follows the source candidates, transports its
continuation along the proved result isomorphism and preserves event count.
The plan domain is equivalent to the independently stated checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs

abbrev RebasePlan (S : Signature) (O : Type) [DecidableEq O] {left right : State S O}
    (placed : ContextPlacement left right) (run : helperStep.Run left) :=
  (contextualRunInterpretation (S := S) (O := O)).Plan placed run

abbrev RunRealization {S : Signature} {O : Type} [DecidableEq O] {left right : State S O}
    (placed : ContextPlacement left right) (run : helperStep.Run left) :=
  (contextualRunInterpretation (S := S) (O := O)).Realization placed run

variable {S : Signature} {O : Type} [DecidableEq O]

def RebasePlan.realize {left right : State S O} (placed : ContextPlacement left right)
    (run : helperStep.Run left) (plan : RebasePlan S O placed run) : RunRealization placed run :=
  ContextualRunInterpretation.Plan.realize contextualRunInterpretation placed run plan

def RebaseChecks : {left right : State S O} → (placed : ContextPlacement left right) → helperStep.Run left → Prop
  | _, _, _, .nil _ => True
  | _, right, placed, .cons f _ rest =>
      ((Frames.contextual S).Solvable placed.state.knowledge ∧ f.made ∉ right.present) ∧
        RebaseChecks (placed.afterLeft f) rest

theorem rebaseChecks_nil {left right : State S O} (placed : ContextPlacement left right) :
    RebaseChecks placed (.nil left) := trivial

theorem rebaseChecks_cons {left right : State S O} (placed : ContextPlacement left right)
    (f : Firing left) (allowed : helperStep.Admits f) (rest : helperStep.Run f.after) :
    RebaseChecks placed (.cons f allowed rest) ↔
      ((Frames.contextual S).Solvable placed.state.knowledge ∧ f.made ∉ right.present) ∧
        RebaseChecks (placed.afterLeft f) rest := Iff.rfl

theorem shared_checks_iff : ∀ {left right : State S O} (placed : ContextPlacement left right)
    (run : helperStep.Run left), contextualRunInterpretation.Checks placed run ↔ RebaseChecks placed run
  | _, _, _, .nil _ => Iff.rfl
  | _, right, placed, .cons f allowed rest => by
      change ((Disjoint f.selection.taken.toFinset right.present ∧
        ((Frames.contextual S).Solvable placed.state.knowledge ∧ f.made ∉ right.present)) ∧
          contextualRunInterpretation.Checks (placed.afterLeft f) rest) ↔
        (((Frames.contextual S).Solvable placed.state.knowledge ∧ f.made ∉ right.present) ∧
          RebaseChecks (placed.afterLeft f) rest)
      rw [shared_checks_iff (placed.afterLeft f) rest]
      simp [Firing.selection]

theorem rebase_plan_iff_checks {left right : State S O} (placed : ContextPlacement left right)
    (run : helperStep.Run left) : Nonempty (RebasePlan S O placed run) ↔ RebaseChecks placed run :=
  (contextualRunInterpretation.plan_iff_checks placed run).trans (shared_checks_iff placed run)

theorem native_run_of_rebase_checks {left right : State S O} (placed : ContextPlacement left right)
    (run : helperStep.Run left) (checked : RebaseChecks placed run) : Nonempty (RunRealization placed run) :=
  contextualRunInterpretation.realization_of_checks placed run ((shared_checks_iff placed run).mpr checked)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
