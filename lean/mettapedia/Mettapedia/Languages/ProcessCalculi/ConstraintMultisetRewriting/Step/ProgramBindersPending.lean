import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersControls

/-!
# A non-pattern argument stays pending

`(= (f (λx. $M x x)) (λa. λb. $M a b))` at `(f (λy. y y))`. The occurrence `$M x x` applies the
hole to the same variable twice, so it is not a Miller pattern.
- **Consistent:** the call matches, by `M ↦ a a`, `a b`, `b a` or `b b`. The branch has the distinct
  answers `λa. λb. a a` and `λa. λb. b b`.
- **No principal answer:** no solution generalizes both `M ↦ a a` and `M ↦ b b`
  (`no_common_generalization`).
- **Pending:** at every fuel the actual worklist returns a residual with equations left. It never
  refutes, since the problem has solutions, and never completes, since a completed answer would be
  principal. The same holds on the step: the firing is admitted, its store has these readings,
  and the worklist on the firing problem stays pending.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt appT lamT)
open LambdaComparison (app lam app_inj lam_inj)

abbrev binary : Unit → Ctx sig := fun _ => [.term, .term]

/-- `$M x x`. -/
def holeTwice : Term (signature sig (holeArity binary)) (.term :: Consts) .term :=
  .op (.inr (.mk ())) (.cons (.var .zero) (.cons (.var .zero) .nil))

/-- `$M a b` under the binders `a` (outer) and `b` (inner). -/
def holeSpread : Term (signature sig (holeArity binary)) (.term :: .term :: Consts) .term :=
  .op (.inr (.mk ())) (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil))

def lhsTwice : Term (signature sig (holeArity binary)) Consts .term := app _ (.var .zero) (lam _ holeTwice)

def rhsSpread : Term (signature sig (holeArity binary)) Consts .term := lam _ (lam _ holeSpread)

/-- `(= (f (λx. $M x x)) (λa. λb. $M a b))`. -/
def twiceEquation : Equation sig Consts .term := ⟨Unit, inferInstance, holeArity binary, lhsTwice, rhsSpread⟩

/-- `(f (λy. y y))`. -/
def twiceCall : Term sig Consts .term := appT fC (lamT (appT (.var .zero) (.var .zero)))

/-- The substitution of the occurrence `$M x x`: both parameters become `x`. -/
def twiceArgs {W : Type} (target : W → MetaArity sig) :
    Args (signature sig target) ([Srt.term, Srt.term].map fun sort => ([], sort)) (Srt.term :: Consts) :=
  .cons (.var .zero) (.cons (.var .zero) .nil)

def twiceSub {W : Type} (target : W → MetaArity sig) :
    Sub (signature sig target) [Srt.term, Srt.term] (Srt.term :: Consts) :=
  argsToSub (twiceArgs target)

theorem twiceSub_vars {W : Type} (target : W → MetaArity sig) :
    ∀ position : Var [Srt.term, Srt.term] .term, ∃ image, twiceSub target .term position = .var image
  | .zero => ⟨.zero, rfl⟩
  | .succ .zero => ⟨.zero, rfl⟩

theorem instantiate_lhsTwice {W : Type} {target : W → MetaArity sig}
    (change : Assignment (holeArity binary) target) :
    instantiate change lhsTwice = app target (.var .zero) (lam target (bind (twiceSub target) (change ()))) := rfl

/-! ## Shapes under a variable substitution -/

theorem bind_var_shape {W : Type} {decl : W → MetaArity sig} {Δ Δ' : Ctx sig}
    (σ : Sub (signature sig decl) Δ Δ') {sort : Srt} :
    ∀ (term : Term (signature sig decl) Δ sort) (image : Var Δ' sort), bind σ term = .var image →
      ∃ position, term = .var position
  | .var position, _, _ => ⟨position, rfl⟩
  | .op _ _, _, same => by cases same

theorem bind_app_shape {W : Type} {decl : W → MetaArity sig} {Δ Δ' : Ctx sig}
    (σ : Sub (signature sig decl) Δ Δ') (vars : ∀ position : Var Δ .term, ∃ image, σ .term position = .var image) :
    ∀ (term : Term (signature sig decl) Δ .term) (first second : Term (signature sig decl) Δ' .term),
      bind σ term = app decl first second →
        ∃ left right, term = app decl left right ∧ bind σ left = first ∧ bind σ right = second
  | .var position, _, _, same => by
      obtain ⟨image, isVar⟩ := vars position
      change σ .term position = _ at same
      rw [isVar] at same
      cases same
  | .op (.inl .app) (.cons left (.cons right .nil)), _, _, same =>
      ⟨left, right, rfl, (app_inj same).1, (app_inj same).2⟩
  | .op (.inl .lam) _, _, _, same => by cases (Term.op.inj same).1
  | .op (.inr _) _, _, _, same => by cases (Term.op.inj same).1

/-- **No common generalization.** No solution of `M[x, x] ≐ x x` has both `M ↦ a a` and
`M ↦ b b` as instances. -/
theorem no_common_generalization {W : Type} {decl : W → MetaArity sig}
    (image : Term (signature sig decl) [Srt.term, Srt.term] .term)
    (solves : bind (twiceSub decl) image = app decl (.var .zero) (.var .zero))
    {W₁ : Type} {first : W₁ → MetaArity sig} (toFirst : Assignment decl first)
    (firstInstance : instantiate toFirst image = Rigid.includeTerm first (appT (.var .zero) (.var .zero)))
    {W₂ : Type} {second : W₂ → MetaArity sig} (toSecond : Assignment decl second)
    (secondInstance : instantiate toSecond image =
      Rigid.includeTerm second (appT (.var (.succ .zero)) (.var (.succ .zero)))) : False := by
  obtain ⟨left, right, rfl, leftSolves, _⟩ := bind_app_shape (twiceSub decl) (twiceSub_vars decl) image _ _ solves
  obtain ⟨position, rfl⟩ := bind_var_shape (twiceSub decl) left _ leftSolves
  have atFirst := Term.var.inj (app_inj firstInstance).1
  have atSecond := Term.var.inj (app_inj secondInstance).1
  cases atFirst.symm.trans atSecond

/-! ## The source control -/

def bothFirst : twiceEquation.Ground := fun _ => appT (.var .zero) (.var .zero)
def bothSecond : twiceEquation.Ground := fun _ => appT (.var (.succ .zero)) (.var (.succ .zero))

theorem matches_bothFirst : Matches twiceEquation twiceCall bothFirst := rfl
theorem matches_bothSecond : Matches twiceEquation twiceCall bothSecond := rfl

/-- `λa. λb. a a` and `λa. λb. b b` are answers of the branch, and they differ. -/
theorem twice_answers :
    Answers twiceEquation twiceCall (lamT (lamT (appT (.var (.succ .zero)) (.var (.succ .zero))))) ∧
      Answers twiceEquation twiceCall (lamT (lamT (appT (.var .zero) (.var .zero)))) ∧
      lamT (lamT (appT (.var (.succ .zero)) (.var (.succ .zero)))) ≠
        (lamT (lamT (appT (.var .zero) (.var .zero))) : Term sig Consts .term) :=
  ⟨⟨bothFirst, matches_bothFirst, rfl⟩, ⟨bothSecond, matches_bothSecond, rfl⟩, by intro same; cases same⟩

theorem twice_solution_shape {W : Type} {decl : W → MetaArity sig} (solution : Assignment twiceEquation.arity decl)
    (solved : ContextualResidual.Models solution (problem twiceEquation twiceCall)) :
    bind (twiceSub decl) (solution ()) = app decl (.var .zero) (.var .zero) := by
  have matched := (models_problem twiceEquation twiceCall solution).mp solved
  change instantiate solution lhsTwice = _ at matched
  rw [instantiate_lhsTwice] at matched
  exact lam_inj (app_inj matched).2

/-- The unification problem has solutions but no principal one. -/
theorem twice_no_principal {W : Type} {decl : W → MetaArity sig} (answer : Assignment twiceEquation.arity decl)
    (solved : ContextualResidual.Models answer (problem twiceEquation twiceCall))
    (factors : ∀ {Later : Type} (later : Later → MetaArity sig) (other : Assignment twiceEquation.arity later),
      ContextualResidual.Models other (problem twiceEquation twiceCall) →
        ∃ factor : Assignment decl later, ∀ hole, other hole = instantiate factor (answer hole)) : False := by
  obtain ⟨toFirst, firstComponents⟩ := factors (ground sig) (twiceEquation.assign bothFirst (ground sig))
    ((matches_iff_models _ _ _).mp matches_bothFirst)
  obtain ⟨toSecond, secondComponents⟩ := factors (ground sig) (twiceEquation.assign bothSecond (ground sig))
    ((matches_iff_models _ _ _).mp matches_bothSecond)
  exact no_common_generalization (answer ()) (twice_solution_shape answer solved)
    toFirst (firstComponents ()).symm toSecond (secondComponents ()).symm

/-- **Pending.** At every fuel the actual worklist returns a residual with equations left: it
never refutes and never completes. -/
theorem twice_pending (fuel : Nat) :
    ∃ update, ContextualFrameWorklist.run fuel twiceEquation.arity (problem twiceEquation twiceCall) =
      .residual update ∧ update.remaining ≠ [] := by
  generalize computed : ContextualFrameWorklist.run fuel twiceEquation.arity (problem twiceEquation twiceCall) = result
  cases result with
  | residual update =>
      refine ⟨update, rfl, fun empty => ?_⟩
      exact twice_no_principal update.answer (update.completed empty)
        (fun later other solved => (update.completed_models_iff empty later other).mp solved)
  | refuted proof =>
      exact False.elim (proof (ground sig) (twiceEquation.assign bothFirst (ground sig))
        ((matches_iff_models _ _ _).mp matches_bothFirst))

/-! ## On the step -/

def twiceProgram : Unit → Equation sig Consts .term := fun _ => twiceEquation

theorem twice_admitted : Admitted twiceProgram (initial twiceCall) () :=
  (valid_iff (initial twiceCall) twiceCall (initial_determines twiceCall) ()).mpr ⟨bothFirst, matches_bothFirst⟩

/-- The store after the firing is consistent and keeps both readings. -/
theorem twice_readings_on_step :
    Reads twiceProgram (destination twiceProgram (initial twiceCall) () twice_admitted)
        (lamT (lamT (appT (.var (.succ .zero)) (.var (.succ .zero))))) ∧
      Reads twiceProgram (destination twiceProgram (initial twiceCall) () twice_admitted)
        (lamT (lamT (appT (.var .zero) (.var .zero)))) :=
  ⟨(reads_iff _ _ (initial_determines twiceCall) () twice_admitted _).mpr twice_answers.1,
    (reads_iff _ _ (initial_determines twiceCall) () twice_admitted _).mpr twice_answers.2.1⟩

/-- The initial state of the non-pattern call. -/
abbrev twiceStart : State twiceProgram := initial twiceCall

abbrev twiceScope : Nat := ruleScope twiceStart.1.occupied twiceStart.2

/-- The hole's image under a solution of the firing problem. -/
abbrev holeImage {W : Type} {decl : W → MetaArity sig}
    (solution : Assignment (active twiceProgram twiceStart.1.declarations) decl) :
    Term (signature sig decl) [Srt.term, Srt.term] .term :=
  instantiate solution (schemaAt twiceProgram twiceStart.1.declarations () twiceScope ())

theorem extended_solves (θ : twiceEquation.Ground) (matched : Matches twiceEquation twiceCall θ) :
    ContextualFrameUnifier.Models (extendModel twiceProgram twiceStart.1.declarations (generator (ground sig))
        (extendGround twiceProgram () θ))
      (ContextualActivatedStep.problem (locals twiceProgram) twiceStart.1.declarations twiceStart.1.occupied
        (selection twiceStart.2) (rule twiceProgram twiceStart.1.declarations ()) twiceStart.1.inventory.rows
        twiceStart.1.inventory.configuration) := by
  rw [← extendGround_at twiceProgram () θ] at matched
  exact extended_model_solves twiceStart () (generator (ground sig)) twiceCall (initial_reads twiceCall) _ matched

theorem firing_solution_shape {W : Type} {decl : W → MetaArity sig}
    (solution : Assignment (active twiceProgram twiceStart.1.declarations) decl)
    (solved : ContextualFrameUnifier.Models solution
      (ContextualActivatedStep.problem (locals twiceProgram) twiceStart.1.declarations twiceStart.1.occupied
        (selection twiceStart.2) (rule twiceProgram twiceStart.1.declarations ()) twiceStart.1.inventory.rows
        twiceStart.1.inventory.configuration)) :
    bind (twiceSub decl) (holeImage solution) = app decl (.var .zero) (.var .zero) := by
  rw [actual_problem twiceProgram twiceStart () (Rigid.includeTerm (ground sig) twiceCall) rfl] at solved
  have matched := ((ContextualFrameUnifier.models_append _ _ _).mp solved).2 _ (List.mem_singleton_self _)
  dsimp only [Prod.fst, Prod.snd] at matched
  have called : instantiate solution (instantiate (ContextualSelectionViews.capturedTarget (locals twiceProgram)
      twiceStart.1.declarations) (Rigid.includeTerm (ground sig) twiceCall)) = Rigid.includeTerm decl twiceCall :=
    (congrArg (instantiate solution) (Rigid.instantiate_include (source := ground sig)
      (ContextualSelectionViews.capturedTarget (locals twiceProgram) twiceStart.1.declarations) twiceCall)).trans
      (Rigid.instantiate_include solution twiceCall)
  have opened := matched.trans called
  rw [← Assignment.instantiate_compose] at opened
  change instantiate _ lhsTwice = _ at opened
  rw [instantiate_lhsTwice] at opened
  exact lam_inj (app_inj opened).2

theorem factored_image {W : Type} {decl : W → MetaArity sig}
    (solution : Assignment (active twiceProgram twiceStart.1.declarations) decl)
    (θ : twiceEquation.Ground) (factor : Assignment decl (active twiceProgram (ground sig)))
    (components : ∀ identity, extendModel twiceProgram twiceStart.1.declarations (generator (ground sig))
      (extendGround twiceProgram () θ) identity = instantiate factor (solution identity)) :
    instantiate factor (holeImage solution) = Rigid.includeTerm (active twiceProgram (ground sig)) (θ ()) := by
  rw [← ContextualFrameUnifier.factor_terms _ _ factor components]
  exact (congrFun (extendModel_schema twiceProgram (ground sig) (generator (ground sig))
    (extendGround twiceProgram () θ) () twiceScope) ()).trans
    (congrArg (Rigid.includeTerm (active twiceProgram (ground sig))) (congrFun (extendGround_at twiceProgram () θ) ()))

/-- The worklist on the firing problem stays pending at every fuel. -/
theorem twice_pending_on_step (fuel : Nat) :
    ∃ update : ContextualFrameUpdate.Update (firingProblem twiceStart ()),
      (letI := (destination twiceProgram twiceStart () twice_admitted).1.equality;
        ContextualFrameWorklist.run fuel (active twiceProgram twiceStart.1.declarations)
          (firingProblem twiceStart ())) = .residual update ∧
      update.remaining ≠ [] := by
  let _ := (destination twiceProgram twiceStart () twice_admitted).1.equality
  generalize computed : ContextualFrameWorklist.run fuel (active twiceProgram twiceStart.1.declarations)
    (firingProblem twiceStart ()) = result
  cases result with
  | refuted proof =>
      exact False.elim (proof _ _ ((ContextualResidual.models_observeProblem _ _).mpr
        (extended_solves bothFirst matches_bothFirst)))
  | residual update =>
      refine ⟨update, rfl, fun empty => ?_⟩
      have answerSolves := (ContextualResidual.models_observeProblem _ _).mp (update.completed empty)
      obtain ⟨toFirst, firstComponents⟩ := (update.completed_models_iff empty _ _).mp
        ((ContextualResidual.models_observeProblem _ _).mpr (extended_solves bothFirst matches_bothFirst))
      obtain ⟨toSecond, secondComponents⟩ := (update.completed_models_iff empty _ _).mp
        ((ContextualResidual.models_observeProblem _ _).mpr (extended_solves bothSecond matches_bothSecond))
      exact no_common_generalization _ (firing_solution_shape update.answer answerSolves)
        toFirst (factored_image update.answer bothFirst toFirst firstComponents)
        toSecond (factored_image update.answer bothSecond toSecond secondComponents)

#print axioms no_common_generalization
#print axioms twice_answers
#print axioms twice_no_principal
#print axioms twice_pending
#print axioms twice_admitted
#print axioms twice_readings_on_step
#print axioms twice_pending_on_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Controls
