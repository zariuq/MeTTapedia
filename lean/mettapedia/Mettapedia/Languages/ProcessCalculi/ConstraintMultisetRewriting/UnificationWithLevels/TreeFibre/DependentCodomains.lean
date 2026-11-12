import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.DependentFibre

/-!
# Codomains that use their argument: solving when the right side already fits

The solvers of arrow codes read `Π (_ : A). B` with `B` not using the argument. The reason was the narrowing, whose
forcing reads the type positions of the code; solving itself needs no shape at all.

**The rule** (`fitSolveUpdate`, `fitSolve_exact`): for `X ≐ t` at a universe, `X` declared at `U_u`, `t` without `X`
and a type of `U_u` over the telescope, and no declaration mentioning `X`, the answer `X := t` keeps the telescope and
is exact. Nothing is asked of the shape of `t`: Π types whose codomain uses the argument, Σ and identity types alike.
A store of one such equation has a principal answer (`fitSolve_principal`).

So the boundary drawn earlier at codomains that use their argument is not a boundary of solving. What stays open there is
narrowing: when an unknown inside a codomain that uses the argument is declared above `X`'s universe, the forcing that
narrows it must read through the binder.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective

variable {Head L : Type} [UniverseLevel.LevelOrder L]

section Rule

variable {S : Setting Head L}

/-- **A flex–rigid equation whose right side fits**: `X ≐ t` at `U_v`, `X : U_u`, `t` without `X`, a type of `U_u`, and
no declaration mentioning `X`. -/
structure FitSolvable {Θ : Context S.R} (e : Equation (TotalTerm Θ)) where
  v : Head
  X : Fin Θ.arity
  u : Head
  annotation_left : e.1.1.code = .head v
  annotation_right : e.2.1.code = .head v
  side_left : e.1.2.code = .var X
  declared : Ctx.lookup Θ.raw X = .head u
  universe_u : S.R.isUniverse u
  universe_v : S.R.isUniverse v
  absent : X ∉ e.2.2.code.support
  fits : Typed S.R Θ.raw e.2.2.code (.head u)
  apart : ∀ i, X ∉ (Ctx.lookup Θ.raw i).support

/-- **`X := t` is a typed substitution of the telescope.** -/
theorem fitSolve_typed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : FitSolvable e) :
    SubstMor S.R Θ.raw Θ.raw (solveSub w.X e.2.2.code) := by
  intro i
  by_cases h : i = w.X
  · rw [h, w.declared]
    change Typed S.R _ (solveSub w.X e.2.2.code w.X) (.head w.u)
    rw [solveSub_self]
    exact w.fits
  · rw [solveSub_ne _ h, subst_solveSub_fresh _ (w.apart i)]
    exact Derivable.var i

/-- **The answer `X := t`**, from the telescope itself. -/
def fitSolve {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : FitSolvable e) : Θ ⟶ Θ where
  substitution := solveSub w.X e.2.2.code
  typed := fitSolve_typed w

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **Solve `X := t`, whatever the shape of `t`**: the solved equation is removed and the rest is instantiated. -/
def fitSolveUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : FitSolvable e)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := Θ
  answer := fitSolve w
  remaining := (frames S.levels).applyStore (fitSolve w) rest
  sound := by
    intro Δ g solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · apply e_of_codes
      · change Presentation.subst (subComp g.substitution (solveSub w.X e'.2.2.code)) e'.1.1.code =
          Presentation.subst (subComp g.substitution (solveSub w.X e'.2.2.code)) e'.2.1.code
        rw [w.annotation_left, w.annotation_right]
      · change Presentation.subst (subComp g.substitution (solveSub w.X e'.2.2.code)) e'.1.2.code =
          Presentation.subst (subComp g.substitution (solveSub w.X e'.2.2.code)) e'.2.2.code
        have fixed : Presentation.subst (subComp g.substitution (solveSub w.X e'.2.2.code)) e'.2.2.code =
            Presentation.subst g.substitution e'.2.2.code := by
          change Presentation.subst (fun i => Presentation.subst g.substitution (solveSub w.X e'.2.2.code i))
            e'.2.2.code = _
          rw [← subst_comp, subst_solveSub_fresh _ w.absent]
        rw [fixed, w.side_left]
        change Presentation.subst g.substitution (solveSub w.X e'.2.2.code w.X) = _
        rw [solveSub_self]
    · exact (Frames.models_applyStore (X := frames S.levels) _ g rest).mp solved e' member
  complete := by
    intro Δ f solved
    have equation := solved e List.mem_cons_self
    have factored : homTypedEquality S.R f (f ≫ fitSolve w) := by
      refine ⟨f.typed, fun i => ?_⟩
      change Equal S.R Δ.raw (f.substitution i) (Presentation.subst f.substitution (solveSub w.X e.2.2.code i))
        (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
      by_cases h : i = w.X
      · rw [h, solveSub_self, w.declared]
        have eq := ((equivalent_iff S.levels _ _).mp equation).2
        change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
          (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at eq
        rw [w.side_left, w.annotation_left] at eq
        have tX : Typed S.R Δ.raw (f.substitution w.X) (.head w.u) := by
          have t := f.typed w.X
          rw [w.declared] at t
          exact t
        have tValue : Typed S.R Δ.raw (Presentation.subst f.substitution e.2.2.code) (.head w.u) :=
          w.fits.substitute f.typed
        exact universe_injective facts roots heads algebra rigid complete Δ.formed w.universe_u w.universe_v
          tX tValue eq
      · rw [solveSub_ne _ h]
        exact .refl (f.typed i)
    refine ⟨f, ?_, act_equal_of_substEq S.levels factored⟩
    apply (Frames.models_applyStore (X := frames S.levels) _ f rest).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels factored) rest).mp
      (fun e' member => solved e' (List.mem_cons_of_mem _ member))

include facts roots heads algebra rigid complete in
/-- **Solving a right side that fits is exact**, codomains that use their argument included. -/
theorem fitSolve_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : FitSolvable e)
    (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (fitSolve w) ((frames S.levels).applyStore (fitSolve w) rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨fitSolveUpdate facts roots heads algebra rigid complete w rest, rfl, rfl, rfl⟩

include facts roots heads algebra rigid complete in
/-- **One such equation has a principal answer**: `X := t`. -/
theorem fitSolve_principal {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : FitSolvable e) :
    (frames S.levels).Principal [e] (fitSolve w) :=
  (fitSolveUpdate facts roots heads algebra rigid complete w []).completed rfl

end Rule

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
