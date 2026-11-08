import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersStrategy

/-!
# Controls for the innermost strategy under binders

The constants are `f` and `g`, the ambient context `[f, g]`; the call is `(f (λy. (g y)))`.
- **Innermost first:** with `(= (f $x) $x)` and `(= (g $z) $z)`, both the root and the call `(g y)`
  under `λy` are redexes. The root firing waits, at every depth bound, because `(g y)` is matched
  strictly inside it; the inner firing is admitted and reads `(f (λy. y))`. Then the root fires, and the
  innermost run reaches `λy. y`, on the reference and on the step.
- **Unmatched inner call, then the outer call:** with `(= (f $x) $x)` alone, `(g y)` under `λy` is
  unmatched, so it is returned as itself; the root call is innermost and fires, reading `λy. (g y)`,
  which no equation matches anywhere. This is R95's `(f (g c))` control, under a binder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.StrategyControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt Op Context appT lamT)
open LambdaComparison (app lam app_inj lam_inj)
open Strategy
open Controls (Consts fC gC appT_inj lamT_inj)
open Nested (callRoot raiseAt)

/-! ## Equations that apply a head to their right-hand side -/

theorem instantiate_app {W X : Type} {declaration : W → MetaArity sig} {next : X → MetaArity sig}
    (change : Assignment declaration next) {Δ : Ctx sig} (function argument : Term (signature sig declaration) Δ .term) :
    instantiate change (app declaration function argument) =
      app next (instantiate change function) (instantiate change argument) := rfl

/-- The left-hand side applies a head to the right-hand side, as `(= (f $x) $x)`. -/
def ArgumentShape {Δ : Ctx sig} (e : Equation sig Δ .term) : Prop :=
  ∃ head, e.lhs = app e.arity head e.rhs

theorem argument_determinate {Δ : Ctx sig} (e : Equation sig Δ .term) (shape : ArgumentShape e) : Determinate e := by
  obtain ⟨head, same⟩ := shape
  intro W target first second call firstMatch secondMatch
  rw [same, instantiate_app] at firstMatch secondMatch
  exact (app_inj (firstMatch.trans secondMatch.symm)).2

theorem raiseOne_shape {Δ : Ctx sig} (e : Equation sig Δ .term) (shape : ArgumentShape e) :
    ArgumentShape (raiseOne Srt.term e) := by
  obtain ⟨head, same⟩ := shape
  refine ⟨raiseTerm (S := sig) (source := e.arity) Srt.term (fun _ position => .succ position) .zero head, ?_⟩
  change raiseTerm Srt.term (fun _ position => .succ position) .zero e.lhs = _
  rw [same]
  rfl

theorem raiseAt_shape {Γ Δ : Ctx sig} (context : Context Γ Δ) (e : Equation sig Γ .term) (shape : ArgumentShape e) :
    ArgumentShape (raiseAt context e) := by
  induction context with
  | hole => exact shape
  | appLeft inner _ ih => exact ih e shape
  | appRight _ inner ih => exact ih e shape
  | underLam inner ih => exact ih _ (raiseOne_shape e shape)

theorem shape_not_var {Δ : Ctx sig} (e : Equation sig Δ .term) (shape : ArgumentShape e) (position : Var Δ .term)
    (θ : e.Ground) : ¬ Matches e (.var position) θ := by
  obtain ⟨head, same⟩ := shape
  intro matched
  unfold Matches at matched
  rw [same, instantiate_app] at matched
  cases matched

theorem shape_not_lam {Δ : Ctx sig} (e : Equation sig Δ .term) (shape : ArgumentShape e)
    (body : Term sig (.term :: Δ) .term) (θ : e.Ground) : ¬ Matches e (lamT body) θ := by
  obtain ⟨head, same⟩ := shape
  intro matched
  unfold Matches at matched
  rw [same, instantiate_app] at matched
  cases matched

/-! ## Normal forms, position by position -/

theorem comp_assoc {Γ Δ Θ Ξ : Ctx sig} (first : Context Γ Δ) (second : Context Δ Θ) (third : Context Θ Ξ) :
    comp (comp first second) third = comp first (comp second third) := by
  induction first with
  | hole => rfl
  | appLeft inner argument ih => exact congrArg (fun context => Context.appLeft context argument) (ih second)
  | appRight function inner ih => exact congrArg (Context.appRight function) (ih second)
  | underLam inner ih => exact congrArg Context.underLam (ih second)

theorem comp_hole {Γ Δ : Ctx sig} (context : Context Γ Δ) : comp context .hole = context := by
  induction context with
  | hole => rfl
  | appLeft inner argument ih => exact congrArg (fun context => Context.appLeft context argument) ih
  | appRight function inner ih => exact congrArg (Context.appRight function) ih
  | underLam inner ih => exact congrArg Context.underLam ih

variable {Γ : Ctx sig} {ι : Type} (program : ι → Equation sig Γ .term)

/-- No equation matches at any position of `term`, the root included. -/
def NormalAt {Δ : Ctx sig} (context : Context Γ Δ) (term : Term sig Δ .term) : Prop :=
  ∀ {Θ : Ctx sig} (below : Context Δ Θ) (inner : Term sig Θ .term), term = below.plug inner →
    ¬ MatchesAt program (comp context below) inner

theorem normalAt_of {Δ : Ctx sig} (context : Context Γ Δ) (term : Term sig Δ .term)
    (root : ¬ MatchesAt program context term) (inside : InnerNormal program context term) :
    NormalAt program context term := by
  intro Θ below inner same
  cases below with
  | hole =>
      rw [comp_hole]
      change term = inner at same
      subst same
      exact root
  | appLeft below argument => exact inside _ inner (by simp [depth]) same
  | appRight function below => exact inside _ inner (by simp [depth]) same
  | underLam below => exact inside _ inner (by simp [depth]) same

theorem innerNormal_var {Δ : Ctx sig} (context : Context Γ Δ) (position : Var Δ .term) :
    InnerNormal program context (.var position) := by
  intro Θ below inner positive same
  cases below with
  | hole => simp [depth] at positive
  | appLeft _ _ => cases same
  | appRight _ _ => cases same
  | underLam _ => cases same

theorem innerNormal_app {Δ : Ctx sig} (context : Context Γ Δ) (function argument : Term sig Δ .term)
    (left : NormalAt program (comp context (.appLeft .hole argument)) function)
    (right : NormalAt program (comp context (.appRight function .hole)) argument) :
    InnerNormal program context (appT function argument) := by
  intro Θ below inner positive same
  cases below with
  | hole => simp [depth] at positive
  | appLeft below other =>
      obtain ⟨isFunction, isArgument⟩ := appT_inj same
      subst isArgument
      have refused := left below inner isFunction
      rwa [comp_assoc] at refused
  | appRight other below =>
      obtain ⟨isFunction, isArgument⟩ := appT_inj same
      subst isFunction
      have refused := right below inner isArgument
      rwa [comp_assoc] at refused
  | underLam _ => cases same

theorem innerNormal_lam {Δ : Ctx sig} (context : Context Γ Δ) (body : Term sig (.term :: Δ) .term)
    (inside : NormalAt program (comp context (.underLam .hole)) body) :
    InnerNormal program context (lamT body) := by
  intro Θ below inner positive same
  cases below with
  | hole => simp [depth] at positive
  | appLeft _ _ => cases same
  | appRight _ _ => cases same
  | underLam below =>
      have refused := inside below inner (lamT_inj same)
      rwa [comp_assoc] at refused

variable {program}

theorem not_matchesAt_var (shapes : ∀ index, ArgumentShape (program index)) {Δ : Ctx sig}
    (context : Context Γ Δ) (position : Var Δ .term) : ¬ MatchesAt program context (.var position) := by
  rintro ⟨index, θ, matched⟩
  exact shape_not_var _ (raiseAt_shape context _ (shapes index)) position θ matched

theorem not_matchesAt_lam (shapes : ∀ index, ArgumentShape (program index)) {Δ : Ctx sig}
    (context : Context Γ Δ) (body : Term sig (.term :: Δ) .term) : ¬ MatchesAt program context (lamT body) := by
  rintro ⟨index, θ, matched⟩
  exact shape_not_lam _ (raiseAt_shape context _ (shapes index)) body θ matched

theorem normalAt_var (shapes : ∀ index, ArgumentShape (program index)) {Δ : Ctx sig}
    (context : Context Γ Δ) (position : Var Δ .term) : NormalAt program context (.var position) :=
  normalAt_of program context _ (not_matchesAt_var shapes context position) (innerNormal_var program context position)

/-! ## The programs and the call -/

/-- `(= (g $z) $z)`. -/
def gRoot : Equation sig Consts .term :=
  ⟨Unit, inferInstance, fun _ => (Consts, .term), app _ (.var (.succ .zero)) (generator _ ()), generator _ ()⟩

/-- `(= (f $x) $x)` and `(= (g $z) $z)`. -/
def bothProgram : Bool → Equation sig Consts .term
  | true => callRoot
  | false => gRoot

/-- `(= (f $x) $x)` alone. -/
def onlyF : Unit → Equation sig Consts .term := fun _ => callRoot

theorem callRoot_shape : ArgumentShape callRoot := ⟨_, rfl⟩
theorem gRoot_shape : ArgumentShape gRoot := ⟨_, rfl⟩

theorem both_shapes : ∀ index, ArgumentShape (bothProgram index)
  | true => callRoot_shape
  | false => gRoot_shape

theorem onlyF_shapes : ∀ index, ArgumentShape (onlyF index) := fun _ => callRoot_shape

/-- `(g y)`, under `λy`. -/
def innerCall : Term sig (.term :: Consts) .term := appT (.var (.succ (.succ .zero))) (.var .zero)

/-- The position of `(g y)`: the argument of `f`, under `λy`. -/
def innerPosition : Context Consts (.term :: Consts) := .appRight fC (.underLam .hole)

/-- `(f (λy. (g y)))`. -/
def nestedCall : Term sig Consts .term := innerPosition.plug innerCall

/-- `(f (λy. y))`. -/
def afterInner : Term sig Consts .term := innerPosition.plug (.var .zero)

/-- `λy. y`. -/
def identityTerm : Term sig Consts .term := lamT (.var .zero)

/-- Under `λy`, `(g $z)` matches `(g y)`, with `$z := y`. -/
theorem g_answers_inner : Answers (raiseAt innerPosition gRoot) innerCall (.var .zero) :=
  ⟨fun _ => .var .zero, rfl, rfl⟩

/-- Under `λy`, `(f $x)` does not match `(g y)`: heads differ. -/
theorem f_not_at_inner (θ : (raiseAt innerPosition callRoot).Ground) :
    ¬ Matches (raiseAt innerPosition callRoot) innerCall θ := by
  intro matched
  have shape : (raiseAt innerPosition callRoot).lhs =
      app _ (.var (.succ .zero)) (raiseAt innerPosition callRoot).rhs := rfl
  unfold Matches at matched
  rw [shape, instantiate_app] at matched
  have heads := (app_inj matched).1
  cases heads

theorem f_answers_root : Answers callRoot nestedCall (lamT innerCall) := ⟨fun _ => lamT innerCall, rfl, rfl⟩

theorem f_answers_after : Answers callRoot afterInner identityTerm := ⟨fun _ => identityTerm, rfl, rfl⟩

/-! ## Innermost first -/

/-- The inner call is a redex. -/
theorem inner_matched : MatchesAt bothProgram innerPosition innerCall := by
  obtain ⟨θ, matched, _⟩ := g_answers_inner
  exact ⟨false, θ, matched⟩

/-- **The root waits**: `(g y)` is matched strictly inside it. -/
theorem root_not_innermost : ¬ InnerNormal bothProgram .hole nestedCall := fun normal =>
  normal innerPosition innerCall (by simp [innerPosition, depth]) rfl inner_matched

theorem inner_innermost : InnerNormal bothProgram innerPosition innerCall :=
  innerNormal_app bothProgram innerPosition _ _ (normalAt_var both_shapes _ _) (normalAt_var both_shapes _ _)

/-- **The innermost redex fires first.** -/
theorem inner_fires_first : Innermost bothProgram nestedCall afterInner :=
  ⟨_, innerPosition, false, innerCall, .var .zero, rfl, rfl, g_answers_inner, inner_innermost⟩

theorem root_after_innermost : InnerNormal bothProgram .hole afterInner :=
  innerNormal_app bothProgram .hole _ _ (normalAt_var both_shapes _ _)
    (normalAt_of bothProgram _ _ (not_matchesAt_lam both_shapes _ _)
      (innerNormal_lam bothProgram _ _ (normalAt_var both_shapes _ _)))

/-- **Then the outer call fires.** -/
theorem root_fires_after : Innermost bothProgram afterInner identityTerm :=
  ⟨_, .hole, true, afterInner, identityTerm, rfl, rfl, f_answers_after, root_after_innermost⟩

theorem innermost_run : Relation.ReflTransGen (Innermost bothProgram) nestedCall identityTerm :=
  (Relation.ReflTransGen.single inner_fires_first).tail root_fires_after

/-! ### On the step -/

theorem both_determinate {Δ : Ctx sig} (context : Context Consts Δ) (index : Bool) :
    Determinate (raiseAt context (bothProgram index)) :=
  argument_determinate _ (raiseAt_shape context _ (both_shapes index))

/-- **The root firing waits at every depth bound.** -/
theorem root_refused_on_step (bound : Nat) :
    ¬ InnermostAdmitted bothProgram (initial nestedCall) ⟨_, .hole, true, bound⟩ := by
  intro valid
  obtain ⟨inner, same, _, normal, _⟩ :=
    (innermost_admitted_iff bothProgram (initial nestedCall) nestedCall (initial_determines nestedCall) _).mp valid
  change nestedCall = inner at same
  subst same
  exact root_not_innermost normal

/-- **The inner firing is admitted**, and reads `(f (λy. y))`. -/
theorem inner_admitted_on_step :
    ∃ valid : InnermostAdmitted bothProgram (initial nestedCall) ⟨_, innerPosition, false, termSize innerCall⟩,
      Reads (strategyProgram bothProgram)
        (innermostDestination bothProgram (initial nestedCall) _ valid) afterInner := by
  have valid := (innermost_admitted_iff bothProgram (initial nestedCall) nestedCall (initial_determines nestedCall)
    ⟨_, innerPosition, false, termSize innerCall⟩).mpr
    ⟨innerCall, rfl, ⟨fun _ => .var .zero, rfl⟩, inner_innermost, bounded_size innerCall⟩
  refine ⟨valid, ?_⟩
  have readsHere := (reads_iff (initial nestedCall) nestedCall (initial_determines nestedCall) _ valid.toPlain
    afterInner).mpr ((atContext_answers (grammar := Nested.grammar) innerPosition _ _ _).mpr
      ⟨innerCall, .var .zero, rfl, rfl, g_answers_inner⟩)
  obtain ⟨Future, future, solution, readsAt⟩ := readsHere
  exact ⟨Future, future, solution, (guarded_reads_as_plain _ _ _ valid solution _).mpr readsAt⟩

/-- **The whole innermost run on the step**, through both firings. -/
theorem innermost_run_on_step :
    ∃ after, Relation.ReflTransGen (InnermostTransition bothProgram) (initial nestedCall) after ∧
      Reads (strategyProgram bothProgram) after identityTerm :=
  (innermost_execution_iff bothProgram both_determinate nestedCall identityTerm).mp innermost_run

/-! ## An unmatched inner call is returned, then the outer call fires -/

/-- Under `λy`, `(g y)` is unmatched: it is returned as itself. -/
theorem inner_unmatched : ¬ MatchesAt onlyF innerPosition innerCall := by
  rintro ⟨_, θ, matched⟩
  exact f_not_at_inner θ matched

theorem root_innermost_alone : InnerNormal onlyF .hole nestedCall :=
  innerNormal_app onlyF .hole _ _ (normalAt_var onlyF_shapes _ _)
    (normalAt_of onlyF _ _ (not_matchesAt_lam onlyF_shapes _ _)
      (innerNormal_lam onlyF _ _ (normalAt_of onlyF _ _ inner_unmatched
        (innerNormal_app onlyF _ _ _ (normalAt_var onlyF_shapes _ _) (normalAt_var onlyF_shapes _ _)))))

/-- **The outer call fires** over the returned inner call. -/
theorem outer_fires : Innermost onlyF nestedCall (lamT innerCall) :=
  ⟨_, .hole, (), nestedCall, lamT innerCall, rfl, rfl, f_answers_root, root_innermost_alone⟩

/-- `λy. (g y)` is final: no equation matches anywhere in it. -/
theorem outer_result_final (answer : Term sig Consts .term) : ¬ Innermost onlyF (lamT innerCall) answer := by
  rintro ⟨Δ, context, index, inner, result, same, _, ⟨θ, matched, _⟩, _⟩
  have normal : NormalAt onlyF .hole (lamT innerCall) :=
    normalAt_of onlyF _ _ (not_matchesAt_lam onlyF_shapes _ _)
      (innerNormal_lam onlyF _ _ (normalAt_of onlyF _ _ inner_unmatched
        (innerNormal_app onlyF _ _ _ (normalAt_var onlyF_shapes _ _) (normalAt_var onlyF_shapes _ _))))
  exact normal context inner same ⟨index, θ, matched⟩

/-- On the step: the outer firing is admitted over the unmatched inner call and reads `λy. (g y)`. -/
theorem outer_fires_on_step :
    ∃ (key : InnermostKey Consts Unit) (valid : InnermostAdmitted onlyF (initial nestedCall) key),
      Reads (strategyProgram onlyF) (innermostDestination onlyF (initial nestedCall) key valid) (lamT innerCall) :=
  (innermost_step_iff onlyF (initial nestedCall) nestedCall (initial_determines nestedCall) _).mpr outer_fires

#print axioms argument_determinate
#print axioms raiseAt_shape
#print axioms normalAt_of
#print axioms innerNormal_app
#print axioms innerNormal_lam
#print axioms root_not_innermost
#print axioms inner_fires_first
#print axioms innermost_run
#print axioms root_refused_on_step
#print axioms inner_admitted_on_step
#print axioms innermost_run_on_step
#print axioms inner_unmatched
#print axioms outer_fires
#print axioms outer_result_final
#print axioms outer_fires_on_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.StrategyControls
