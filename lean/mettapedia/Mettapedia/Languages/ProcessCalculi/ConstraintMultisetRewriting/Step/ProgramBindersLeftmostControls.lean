import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersLeftmostStep

/-!
# Controls for leftmost-innermost reduction with `Atom` positions

The constants are `f` and `g`, the ambient context `[f, g]`.

- **Two innermost redexes, the leftmost fires**: with `(= (g $z) $z)`, the term `(f (g f) (g g))`
  has the innermost redexes `(g f)` and `(g g)`. The strategy selects `(g f)` and reaches
  `(f f (g g))`; firing `(g g)` is one of R100's innermost reductions, and it is no step of the
  strategy. On the step, the key at `(g f)` is clear and the key at `(g g)` is not.
- **A redex inside an `Atom` position never fires**: with `f`'s parameter declared `atom`, the term
  `(f (g g))` has no step under `(= (g $z) $z)`: it is normal at its evaluated positions. Without the
  declaration `(g g)` fires. With `(= (f $x) $x)` too, the call `f` fires on its unevaluated
  argument and answers `(g g)`, where R100's innermost root waits.
- **R95's `(f (g c))`, under a binder**: in `(f (λy. (g y)))` with both equations, the strategy fires
  `(g y)` under `λy` first and then the root, reaching `λy. y`; with `(= (f $x) $x)` alone, the root
  fires on the unmatched inner call.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.LeftmostControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt Op Context appT lamT)
open LambdaComparison (app lam app_inj lam_inj)
open Strategy (MatchesAt InnerNormal Innermost comp depth)
open Nested (raiseAt callRoot)
open Controls (Consts fC gC appT_inj lamT_inj)
open StrategyControls
open Leftmost

/-! ## Normal forms at evaluated positions -/

section Normal

variable {H : Type} {decl : Declarations H} {Γ : Ctx sig} {ι : Type} {program : ι → Equation sig Γ .term}

theorem normalA_var (shapes : ∀ index, ArgumentShape (program index)) (amb : Var Γ .term → Option H)
    (v : Var Γ .term) : NormalA decl program amb (.var v) := by
  intro Θ below inner same _
  have zero := var_positions below inner same
  cases below with
  | hole =>
      change Term.var v = inner at same
      subst same
      exact not_matchesAt_var shapes .hole v
  | appLeft _ _ => simp [depth] at zero
  | appRight _ _ => simp [depth] at zero
  | underLam _ => simp [depth] at zero

theorem inside_app {amb : Var Γ .term → Option H} {function argument : Term sig Γ .term}
    (normalF : NormalA decl program amb function)
    (normalArg : AtomArg decl amb function ∨ NormalA decl program amb argument) :
    ∀ {Θ : Ctx sig} (below : Context Γ Θ) (inner : Term sig Θ .term), 0 < depth below →
      appT function argument = below.plug inner → ¬ Frozen decl amb below → ¬ MatchesAt program below inner := by
  intro Θ below inner positive same live
  cases below with
  | hole => simp [depth] at positive
  | appLeft below' _ =>
      obtain ⟨isFunction, -⟩ := appT_inj same
      exact normalF below' inner isFunction fun frozen => live (frozen_left_iff.mpr frozen)
  | appRight function' below' =>
      obtain ⟨isFunction, isArgument⟩ := appT_inj same
      subst isFunction
      rcases normalArg with declared | normalArg
      · exact absurd (Frozen.atom _ _ declared) live
      · exact normalArg below' inner isArgument fun frozen => live (Frozen.right _ _ frozen)
  | underLam _ => cases same

theorem inside_lam {amb : Var Γ .term → Option H} {body : Term sig (.term :: Γ) .term}
    (normalB : NormalA decl (fun index => raiseOne Srt.term (program index)) (liftAmb amb) body) :
    ∀ {Θ : Ctx sig} (below : Context Γ Θ) (inner : Term sig Θ .term), 0 < depth below →
      lamT body = below.plug inner → ¬ Frozen decl amb below → ¬ MatchesAt program below inner := by
  intro Θ below inner positive same live
  cases below with
  | hole => simp [depth] at positive
  | appLeft _ _ => cases same
  | appRight _ _ => cases same
  | underLam below' => exact normalB below' inner (lamT_inj same) fun frozen => live (frozen_lam_iff.mpr frozen)

theorem normalA_of_inside {amb : Var Γ .term → Option H} {term : Term sig Γ .term}
    (root : ¬ MatchesAt program .hole term)
    (inside : ∀ {Θ : Ctx sig} (below : Context Γ Θ) (inner : Term sig Θ .term), 0 < depth below →
      term = below.plug inner → ¬ Frozen decl amb below → ¬ MatchesAt program below inner) :
    NormalA decl program amb term := by
  intro Θ below inner same live
  cases below with
  | hole =>
      change term = inner at same
      subst same
      exact root
  | appLeft below' argument => exact inside _ inner (by simp [depth]) same live
  | appRight function below' => exact inside _ inner (by simp [depth]) same live
  | underLam below' => exact inside _ inner (by simp [depth]) same live

theorem not_atom_none {amb : Var Γ .term → Option H} (function : Term sig Γ .term) :
    ¬ AtomArg (noDeclarations H) amb function := by
  rintro ⟨h, k, -, atom⟩
  simp [noDeclarations] at atom

end Normal

theorem raised_shapes {Γ : Ctx sig} {ι : Type} {program : ι → Equation sig Γ .term}
    (shapes : ∀ index, ArgumentShape (program index)) :
    ∀ index, ArgumentShape (raiseOne Srt.term (program index)) := fun index =>
  raiseOne_shape _ (shapes index)

/-- No declarations, over the constants. -/
abbrev noDecl : Declarations (Var Consts .term) := noDeclarations _

/-- `(= (g $z) $z)` alone. -/
def onlyG : Unit → Equation sig Consts .term := fun _ => gRoot

theorem onlyG_shapes : ∀ index, ArgumentShape (onlyG index) := fun _ => gRoot_shape

/-! ## Two innermost redexes: the leftmost fires -/

/-- `(f (g f) (g g))`. -/
def twoRedexes : Term sig Consts .term := appT (appT fC (appT gC fC)) (appT gC gC)

/-- The position of `(g f)`. -/
def leftPosition : Context Consts Consts := .appLeft (.appRight fC .hole) (appT gC gC)

/-- The position of `(g g)`. -/
def rightPosition : Context Consts Consts := .appRight (appT fC (appT gC fC)) .hole

theorem g_matches_gf : Answers gRoot (appT gC fC) fC := ⟨fun _ => fC, rfl, rfl⟩

theorem g_matches_gg : Answers gRoot (appT gC gC) gC := ⟨fun _ => gC, rfl, rfl⟩

theorem matched_of_answers {ι : Type} {program : ι → Equation sig Consts .term} {index : ι}
    {term answer : Term sig Consts .term} (answered : Answers (program index) term answer) :
    MatchesAt program .hole term := by
  obtain ⟨θ, matched, -⟩ := answered
  exact ⟨index, θ, matched⟩

/-- **The strategy selects `(g f)`.** -/
theorem left_selected : Selects noDecl onlyG some twoRedexes leftPosition (appT gC fC) :=
  .left _ _ _ _ (.right _ _ _ _ (normalA_var onlyG_shapes _ _) (not_atom_none _)
    (.root _ (matched_of_answers (index := ()) g_matches_gf)
      (inside_app (normalA_var onlyG_shapes _ _) (.inr (normalA_var onlyG_shapes _ _)))))

/-- **The leftmost redex fires.** -/
theorem left_fires : StrategyStep noDecl onlyG twoRedexes (appT (appT fC fC) (appT gC gC)) :=
  ⟨_, leftPosition, (), appT gC fC, fC, left_selected, rfl, g_matches_gf⟩

/-- Firing `(g g)` is one of R100's innermost reductions. -/
theorem right_is_innermost : Innermost onlyG twoRedexes (appT (appT fC (appT gC fC)) gC) :=
  ⟨_, rightPosition, (), appT gC gC, gC, rfl, rfl, g_matches_gg,
    innerNormal_app onlyG rightPosition _ _ (normalAt_var onlyG_shapes _ _) (normalAt_var onlyG_shapes _ _)⟩

/-- **…and it is no step of the strategy**: the selected redex is `(g f)`. -/
theorem right_waits : ¬ StrategyStep noDecl onlyG twoRedexes (appT (appT fC (appT gC fC)) gC) := by
  rintro ⟨Δ, context, index, inner, result, selects, isAnswer, -⟩
  have same := step_position_unique selects left_selected
  cases same
  change appT (appT fC (appT gC fC)) gC = appT (appT fC result) (appT gC gC) at isAnswer
  have parts := (appT_inj isAnswer).2
  cases parts

/-- On the step: the key at `(g f)` is clear… -/
theorem left_key_clear : LeftmostStep.Clear onlyG leftPosition :=
  .left _ _ (.right fC .hole (normalA_var onlyG_shapes _ _) .hole)

/-- …and the key at `(g g)` is not: `(g f)` is matched in the function to its left, so no
leftmost-innermost firing of the step is keyed there. -/
theorem right_key_not_clear : ¬ LeftmostStep.Clear onlyG rightPosition := by
  intro clear
  obtain ⟨normal, -⟩ := clear.of_right
  exact normal (.appRight fC .hole) (appT gC fC) rfl (not_frozen_none _)
    (matched_of_answers (index := ()) g_matches_gf)

/-! ## A redex inside an `Atom` position never fires -/

/-- `f`'s parameter is declared `atom`; `g`'s is undeclared. -/
def fAtom : Declarations (Var Consts .term)
  | .zero => [.atom]
  | .succ _ => []

/-- `(f (g g))`. -/
def atomCall : Term sig Consts .term := appT fC (appT gC gC)

theorem f_declares_atom : AtomArg fAtom (some : Var Consts .term → Option (Var Consts .term)) fC :=
  ⟨(Var.zero : Var Consts Srt.term), 0, Spine.head Var.zero Var.zero rfl, rfl⟩

theorem g_not_at_f (argument : Term sig Consts .term) :
    ¬ MatchesAt onlyG (Context.hole : Context Consts Consts) (appT fC argument) := by
  rintro ⟨_, θ, matched⟩
  have shape : gRoot.lhs = app _ (.var (.succ .zero)) gRoot.rhs := rfl
  unfold Matches at matched
  change instantiate (gRoot.assign θ (ground sig)) gRoot.lhs = _ at matched
  rw [shape, instantiate_app] at matched
  have heads := (app_inj matched).1
  cases heads

/-- **The redex `(g g)` inside `f`'s `atom` argument never fires**: the term is normal at its
evaluated positions, so the strategy has no step. -/
theorem atom_normal : NormalA fAtom onlyG some atomCall :=
  normalA_of_inside (g_not_at_f _)
    (inside_app (normalA_var onlyG_shapes _ _) (.inl f_declares_atom))

theorem atom_never_fires (answer : Term sig Consts .term) : ¬ StrategyStep fAtom onlyG atomCall answer := by
  rintro ⟨Δ, context, index, inner, result, selects, -, -⟩
  obtain ⟨same, live, matched⟩ := selects_redex selects
  exact atom_normal context inner same live matched

/-- Without the declaration, `(g g)` fires. -/
theorem inner_fires_without_atom : StrategyStep noDecl onlyG atomCall (appT fC gC) :=
  ⟨_, .appRight fC .hole, (), appT gC gC, gC,
    .right _ _ _ _ (normalA_var onlyG_shapes _ _) (not_atom_none _)
      (.root _ (matched_of_answers (index := ()) g_matches_gg)
        (inside_app (normalA_var onlyG_shapes _ _) (.inr (normalA_var onlyG_shapes _ _)))),
    rfl, g_matches_gg⟩

theorem f_answers_data : Answers callRoot atomCall (appT gC gC) := ⟨fun _ => appT gC gC, rfl, rfl⟩

/-- **With `(= (f $x) $x)` too, `f` fires on its unevaluated argument.** -/
theorem outer_fires_on_data : StrategyStep fAtom bothProgram atomCall (appT gC gC) :=
  ⟨_, .hole, true, atomCall, appT gC gC,
    .root _ (matched_of_answers (index := true) f_answers_data)
      (inside_app (normalA_var both_shapes _ _) (.inl f_declares_atom)),
    rfl, f_answers_data⟩

/-- R100's innermost root waits here: `(g g)` is matched inside it. -/
theorem innermost_root_waits : ¬ InnerNormal bothProgram .hole atomCall := fun normal => by
  obtain ⟨θ, matched, -⟩ := g_matches_gg
  exact normal (.appRight fC .hole) (appT gC gC) (by simp [depth]) rfl ⟨false, θ, matched⟩

/-! ## R95's `(f (g c))`, under a binder -/

/-- The inner call `(g y)` under `λy` is selected first. -/
theorem inner_selected : Selects noDecl bothProgram some nestedCall innerPosition innerCall :=
  .right _ _ _ _ (normalA_var both_shapes _ _) (not_atom_none _)
    (.lam _ _ _ (.root _ inner_matched
      (inside_app (normalA_var (raised_shapes both_shapes) _ _)
        (.inr (normalA_var (raised_shapes both_shapes) _ _)))))

theorem inner_step : StrategyStep noDecl bothProgram nestedCall afterInner :=
  ⟨_, innerPosition, false, innerCall, .var .zero, inner_selected, rfl, g_answers_inner⟩

theorem after_normal_lam :
    NormalA noDecl (fun index => raiseOne Srt.term (bothProgram index)) (liftAmb some)
      (Term.var .zero : Term sig (.term :: Consts) .term) :=
  normalA_var (raised_shapes both_shapes) _ _

/-- **Then the root fires.** -/
theorem root_step : StrategyStep noDecl bothProgram afterInner identityTerm :=
  ⟨_, .hole, true, afterInner, identityTerm,
    .root _ (matched_of_answers (index := true) f_answers_after)
      (inside_app (normalA_var both_shapes _ _)
        (.inr (normalA_of_inside (not_matchesAt_lam both_shapes _ _) (inside_lam after_normal_lam)))),
    rfl, f_answers_after⟩

/-- **The leftmost-innermost run reaches `λy. y`.** -/
theorem leftmost_run : Relation.ReflTransGen (StrategyStep noDecl bothProgram) nestedCall identityTerm :=
  (Relation.ReflTransGen.single inner_step).tail root_step

/-- With `(= (f $x) $x)` alone, `(g y)` is unmatched, and the root fires. -/
theorem root_fires_on_unmatched : StrategyStep noDecl onlyF nestedCall (lamT innerCall) :=
  ⟨_, .hole, (), nestedCall, lamT innerCall,
    .root _ (matched_of_answers (index := ()) f_answers_root)
      (inside_app (normalA_var onlyF_shapes _ _)
        (.inr (normalA_of_inside (not_matchesAt_lam onlyF_shapes _ _)
          (inside_lam (normalA_of_inside
            (by
              rintro ⟨_, θ, matched⟩
              exact f_not_at_inner θ matched)
            (inside_app (normalA_var (raised_shapes onlyF_shapes) _ _)
              (.inr (normalA_var (raised_shapes onlyF_shapes) _ _)))))))),
    rfl, f_answers_root⟩

#print axioms left_selected
#print axioms left_fires
#print axioms right_is_innermost
#print axioms right_waits
#print axioms left_key_clear
#print axioms right_key_not_clear
#print axioms atom_normal
#print axioms atom_never_fires
#print axioms inner_fires_without_atom
#print axioms outer_fires_on_data
#print axioms innermost_root_waits
#print axioms inner_selected
#print axioms leftmost_run
#print axioms root_fires_on_unmatched

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.LeftmostControls
