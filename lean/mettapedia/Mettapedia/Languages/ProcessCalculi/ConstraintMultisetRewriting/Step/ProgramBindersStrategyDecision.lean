import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersStrategyControls

/-!
# The innermost strategy is decided by certified refutation

Every equation of the strategy's step program has a Miller-pattern left-hand side when the root
program does (`strategy_patterns`): plugging, raising along a context or a path, and filling a path
with fresh sibling holes keep Miller patterns. So the guard of an innermost firing is decided by the
existing guard refuter, as the absence of a matching equation is (`ProgramBindersAbsence`):
- **sound** (`innermost_of_certified`): a certified absence admits the firing;
- **complete** (`innermost_redex_certified`): at a state in the pattern fragment, an innermost redex has
  a certifying budget;
- **controls:** at `(f (λy. (g y)))` the inner firing is certified, and the waiting root firing is never
  certified, at any budget and any depth bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Strategy

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt Op Context appT lamT)
open ContextualPatternFragment (Pattern generator_pattern)
open Nested (raiseAt raiseAt_pattern grammar)

variable {Γ : Ctx sig} {ι : Type} (program : ι → Equation sig Γ .term)

/-- **Every equation of the step program is a Miller pattern** when the root program's are. -/
theorem strategy_patterns (patterns : ∀ index, Pattern sig (program index).arity (program index).lhs) :
    ∀ key, Pattern sig (strategyProgram program key).arity (strategyProgram program key).lhs
  | .inl ⟨_, context, index⟩ =>
      atContext_pattern (grammar := grammar) context _ (raiseAt_pattern context _ (patterns index))
  | .inr ⟨_, context, ⟨Θ, path⟩, none⟩ =>
      atContext_pattern (grammar := grammar) context _
        (pathEquation_pattern path _ (generator_pattern (S := sig) (declaration := callArity Θ .term) ()))
  | .inr ⟨_, context, ⟨_, path⟩, some index⟩ =>
      atContext_pattern (grammar := grammar) context _
        (pathEquation_pattern path _ (raiseAlong_pattern path _ (raiseAt_pattern context _ (patterns index))))

variable [Fintype ι] [DecidableEq ι]

/-- **Soundness.** A certified absence turns an admitted plain firing into an admitted innermost one. -/
theorem innermost_of_certified (budget : FireKey Γ ι ⊕ CheckKey Γ ι → Nat) (state : State (strategyProgram program))
    (key : InnermostKey Γ ι) (plain : Admitted (strategyProgram program) state (fireOf key))
    (accepted : certifiesGuarded (strategyProgram program) budget state (fireOf key) (carriersOf key) = true) :
    InnermostAdmitted program state key :=
  certified_guarded budget state _ _ plain accepted

/-- **Completeness.** For a Miller-pattern program at a state in the pattern fragment, an innermost
redex, at the bound of its size, has a budget that certifies the absence of every carrier. -/
theorem innermost_redex_certified (patterns : ∀ index, Pattern sig (program index).arity (program index).lhs)
    (state : State (strategyProgram program)) (call : Term sig Γ .term)
    (determined : Determines (strategyProgram program) state call) (patterned : PatternState state)
    {Δ : Ctx sig} (context : Context Γ Δ) (index : ι) (inner : Term sig Δ .term) (isCall : call = context.plug inner)
    (matched : ∃ θ, Matches (raiseAt context (program index)) inner θ) (normal : InnerNormal program context inner) :
    ∃ budget, certifiesGuarded (strategyProgram program) budget state (fireOf ⟨Δ, context, index, termSize inner⟩)
      (carriersOf ⟨Δ, context, index, termSize inner⟩) = true := by
  have valid := (innermost_admitted_iff program state call determined ⟨Δ, context, index, termSize inner⟩).mpr
    ⟨inner, isCall, matched, normal, bounded_size inner⟩
  obtain ⟨⟨Future, future, solution, ⟨value, holds, _, _⟩⟩, _⟩ := determined
  have absent : CarriersAbsent (strategyProgram program) state (fireOf ⟨Δ, context, index, termSize inner⟩)
      (carriersOf ⟨Δ, context, index, termSize inner⟩) :=
    ((guarded_admitted_iff state value holds _ _ (fire_apart _)).mp valid).2
  exact certifies_guarded_of_absent state patterned _ (strategy_patterns program patterns _) _
    (fun carrier _ => strategy_patterns program patterns carrier) (fire_apart _) absent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Strategy

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.StrategyControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt Op Context appT lamT)
open ContextualPatternFragment (Pattern generator_pattern)
open Strategy
open Controls (Consts fC gC)
open Nested (callRoot raiseAt)

theorem gRoot_pattern : Pattern sig gRoot.arity gRoot.lhs :=
  .rigid (S := sig) LambdaContextualRung.Op.app _ (.cons _ _ (.object _) (.cons _ _ (generator_pattern _) .nil))

theorem callRoot_pattern : Pattern sig callRoot.arity callRoot.lhs :=
  .rigid (S := sig) LambdaContextualRung.Op.app _ (.cons _ _ (.object _) (.cons _ _ (generator_pattern _) .nil))

theorem both_patterns : ∀ index, Pattern sig (bothProgram index).arity (bothProgram index).lhs
  | true => callRoot_pattern
  | false => gRoot_pattern

/-- **The inner firing is certified** by the actual worklist. -/
theorem inner_certified :
    ∃ budget, certifiesGuarded (strategyProgram bothProgram) budget (initial nestedCall)
      (fireOf ⟨_, innerPosition, false, termSize innerCall⟩) (carriersOf ⟨_, innerPosition, false, termSize innerCall⟩) =
        true :=
  innermost_redex_certified bothProgram both_patterns (initial nestedCall) nestedCall (initial_determines nestedCall)
    (initial_pattern nestedCall) innerPosition false innerCall rfl ⟨fun _ => .var .zero, rfl⟩ inner_innermost

/-- **The waiting root firing is never certified**, at any budget and any depth bound: a pending or
solvable carrier is never taken for a refutation. -/
theorem root_never_certified (budget : FireKey Consts Bool ⊕ CheckKey Consts Bool → Nat) (bound : Nat) :
    certifiesGuarded (strategyProgram bothProgram) budget (initial nestedCall)
      (fireOf ⟨_, .hole, true, bound⟩) (carriersOf ⟨_, .hole, true, bound⟩) = false := by
  cases certified : certifiesGuarded (strategyProgram bothProgram) budget (initial nestedCall)
      (fireOf ⟨_, .hole, true, bound⟩) (carriersOf ⟨_, .hole, true, bound⟩) with
  | false => rfl
  | true =>
      have plain : Admitted (strategyProgram bothProgram) (initial nestedCall) (fireOf ⟨_, .hole, true, bound⟩) :=
        admitted_of_match _ _ _ nestedCall (initial_reads nestedCall) (fun _ => lamT innerCall) rfl
      exact False.elim (root_refused_on_step bound (innermost_of_certified bothProgram budget _ _ plain certified))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.StrategyControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Strategy.strategy_patterns
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Strategy.innermost_of_certified
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Strategy.innermost_redex_certified
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.StrategyControls.inner_certified
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.StrategyControls.root_never_certified
