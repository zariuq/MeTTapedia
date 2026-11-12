import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.StepConnection

/-!
# Solved answers fix exactly the solutions: principality as an equalizer

`Frames.Principal` gives a factor through the answer, not a unique one. For the solver of cumulative
codes something sharper holds, with a canonical factor.

* Every transition's morphism is idempotent (`Rule.idempotent`), so it fixes every solution of the
  store it acts on (`fixes_of_idempotent`).
* Along a run, every solution of the first store is fixed by the run's answer and solves the
  residual (`Runs.fixes`).
* **For a solved run the solutions are exactly the assignments the answer fixes**
  (`solved_equalizer`): the solution set is the equalizer of the identity and precomposition with
  the answer. Each solution is its own factor, and the answer is idempotent (`solved_idempotent`).
* On the uniform pattern fragment every store has such an answer or no solution
  (`equalizer_or_unsolvable`).

Positive control: `X par ≐ arr (V par) gnd`, whose solutions are exactly the assignments with
`X = arr V gnd`. Negative control: the identity assignment does not solve it, and it is not fixed by
the answer (`identity_not_fixed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

universe uO uT uH

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}

theorem Agree.comp_right {a b c : Obj} {f f' : Hom b c} (same : Agree X f f') (σ : Hom a b) :
    Agree X (X.comp f σ) (X.comp f' σ) := by
  intro t
  rw [X.act_comp, X.act_comp]
  exact same _

/-- **An idempotent exact transition fixes every solution.** -/
theorem fixes_of_idempotent {a : Obj} {S : EquationStore (Tm a)} {σ : Hom a a}
    {S' : EquationStore (Tm a)} (exact : Exact X S σ S') (idem : Agree X (X.comp σ σ) σ)
    {b : Obj} (f : Hom a b) (solved : X.Models f S) : Agree X f (X.comp f σ) := by
  obtain ⟨g, fg, _⟩ := (exact b f).mp solved
  have step₁ : Agree X (X.comp f σ) (X.comp (X.comp g σ) σ) := fg.comp_right σ
  have step₂ : Agree X (X.comp (X.comp g σ) σ) (X.comp g (X.comp σ σ)) :=
    (agree_assoc σ σ g).symm
  have step₃ : Agree X (X.comp g (X.comp σ σ)) (X.comp g σ) := idem.comp_left g
  exact (fg.trans (step₃.symm.trans (step₂.symm.trans step₁.symm)))

end General

namespace CumulativeCodes

variable {v : Nat → Nat}

theorem solve_idempotent {Δ : Ctx} {X : Nat} {t : Tm} {σ : Assign v Δ Δ}
    (hσ : σ.1 = Function.update Tm.idA X t) (fresh : Tm.occurs X t = false) :
    Agree (frames v) ((frames v).comp σ σ) σ := by
  apply agree_of_unknowns
  intro W _
  show Tm.lower v (Tm.act σ.1 (σ.1 W)) = Tm.lower v (σ.1 W)
  rw [hσ]
  by_cases hW : W = X
  · subst hW
    rw [Function.update_self, solve_fixes fresh]
  · rw [Function.update_of_ne hW]
    show Tm.lower v (Tm.act (Function.update Tm.idA X t) (.app W .par)) = Tm.lower v (.app W .par)
    rw [act_app_par, Function.update_of_ne hW]
    rfl

/-- **Every transition's morphism is idempotent.** -/
theorem Rule.idempotent {Δ : Ctx} {S S' : EquationStore (Term Δ)} {σ : Assign v Δ Δ}
    (r : Rule v S Δ σ S') : Agree (frames v) ((frames v).comp σ σ) σ := by
  cases r with
  | delete _ => exact (agree_comp_id _).symm
  | decompose _ _ _ _ _ _ => exact (agree_comp_id _).symm
  | solveLeft _ fresh hσ => exact solve_idempotent hσ fresh
  | solveRight _ fresh hσ => exact solve_idempotent hσ fresh

/-- Runs of the solver at one context. -/
inductive Runs (v : Nat → Nat) {Δ : Ctx} :
    EquationStore (Term Δ) → Assign v Δ Δ → EquationStore (Term Δ) → Prop
  | refl (S : EquationStore (Term Δ)) : Runs v S ((frames v).id Δ) S
  | step {S S' R : EquationStore (Term Δ)} {σ τ : Assign v Δ Δ} :
      Rule v S Δ σ S' → Runs v S' τ R → Runs v S ((frames v).comp τ σ) R

theorem Runs.reaches {Δ : Ctx} {S R : EquationStore (Term Δ)} {σ : Assign v Δ Δ}
    (run : Runs v S σ R) : (solver v).Reaches S Δ σ R := by
  induction run with
  | refl S => exact .refl S
  | step r _ ih => exact .step r ih

/-- **Along a run, every solution is fixed by the answer and solves the residual.** -/
theorem Runs.fixes {Δ : Ctx} {S R : EquationStore (Term Δ)} {σ : Assign v Δ Δ}
    (run : Runs v S σ R) {Γ : Ctx} (f : Assign v Δ Γ) (solved : (frames v).Models f S) :
    Agree (frames v) f ((frames v).comp f σ) ∧ (frames v).Models f R := by
  induction run with
  | refl S => exact ⟨agree_comp_id f, solved⟩
  | @step S S' R σ τ r _ ih =>
      have fixed : Agree (frames v) f ((frames v).comp f σ) :=
        fixes_of_idempotent r.exact r.idempotent f solved
      have next : (frames v).Models f S' := by
        apply (solver_literal (v := v) r Γ f).mp
        rw [Frames.models_applyStore]
        exact (models_of_agree fixed S).mp solved
      obtain ⟨fixedRest, solvedR⟩ := ih next
      refine ⟨?_, solvedR⟩
      have one : Agree (frames v) ((frames v).comp f ((frames v).comp τ σ))
          ((frames v).comp ((frames v).comp f τ) σ) := agree_assoc σ τ f
      have two : Agree (frames v) ((frames v).comp ((frames v).comp f τ) σ)
          ((frames v).comp f σ) := fixedRest.symm.comp_right σ
      exact fixed.trans (two.symm.trans one.symm)

/-- **Principality as an equalizer**: for a solved run, the solutions of the store are exactly the
assignments the answer fixes. -/
theorem solved_equalizer {Δ : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ Δ}
    (run : Runs v S σ []) {Γ : Ctx} (f : Assign v Δ Γ) :
    (frames v).Models f S ↔ Agree (frames v) f ((frames v).comp f σ) := by
  constructor
  · exact fun solved => (run.fixes f solved).1
  · intro fixed
    have principal := solved_principal run.reaches
    exact (models_of_agree fixed S).mpr (Frames.models_comp principal.sound f)

/-- **The solved answer is idempotent.** -/
theorem solved_idempotent {Δ : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ Δ}
    (run : Runs v S σ []) : Agree (frames v) ((frames v).comp σ σ) σ :=
  ((run.fixes σ (solved_principal run.reaches).sound).1).symm

/-- On the fragment, the decision as runs at one context. -/
theorem decided_runs {Δ : Ctx} {p ℓ : Nat} (S : EquationStore (Term Δ)) (h : Uniform v Δ p ℓ S) :
    ∃ (σ : Assign v Δ Δ) (R : EquationStore (Term Δ)), Runs v S σ R ∧
      (R = [] ∨ ∃ r : Reason, Refutes v R r) := by
  induction S using (InvImage.wf rank rankLt_wf).induction with
  | h S ih =>
      match S, h with
      | [], _ => exact ⟨_, _, .refl [], Or.inl rfl⟩
      | e :: S, h =>
          rcases progress h with ⟨σ, S', r⟩ | ⟨reason, refuted⟩
          · obtain ⟨τ, R, run, ends⟩ := ih S' r.rank_lt (r.uniform h)
            exact ⟨_, R, .step r run, ends⟩
          · exact ⟨_, _, .refl _, Or.inr ⟨reason, refuted⟩⟩

/-- **On the uniform pattern fragment: an equalizer answer, or no solution.** -/
theorem equalizer_or_unsolvable {Δ : Ctx} {p ℓ : Nat} (S : EquationStore (Term Δ))
    (h : Uniform v Δ p ℓ S) :
    (∃ σ : Assign v Δ Δ, (frames v).Principal S σ ∧
      ∀ (Γ : Ctx) (f : Assign v Δ Γ),
        (frames v).Models f S ↔ Agree (frames v) f ((frames v).comp f σ)) ∨
      ¬ (frames v).Solvable S := by
  obtain ⟨σ, R, run, ends⟩ := decided_runs S h
  rcases ends with rfl | ⟨r, refuted⟩
  · exact Or.inl ⟨σ, solved_principal run.reaches, fun Γ f => solved_equalizer run f⟩
  · exact Or.inr (refuted_none (P := solver v) run.reaches refuted)

namespace SolverControls

/-- The run of `X par ≐ arr (V par) gnd` at one context. -/
theorem solved_runs (v : Nat → Nat) :
    Runs v [(X, target)] ((frames v).comp ((frames v).id ctx) (answer v)) [] :=
  .step (Rule.solveLeft rfl rfl rfl) (.refl _)

/-- **Positive**: the solutions are exactly the assignments fixed by the answer. -/
theorem solved_fixed_points (v : Nat → Nat) {Γ : Ctx} (f : Assign v ctx Γ) :
    (frames v).Models f [(X, target)] ↔
      Agree (frames v) f ((frames v).comp f ((frames v).comp ((frames v).id ctx) (answer v))) :=
  solved_equalizer (solved_runs v) f

/-- **Negative**: the identity does not solve the store, so it is not fixed by the answer. -/
theorem identity_not_fixed (v : Nat → Nat) :
    ¬ (frames v).Models ((frames v).id ctx) [(X, target)] ∧
      ¬ Agree (frames v) ((frames v).id ctx)
        ((frames v).comp ((frames v).id ctx) ((frames v).comp ((frames v).id ctx) (answer v))) := by
  have unsolved : ¬ (frames v).Models ((frames v).id ctx) [(X, target)] := by
    intro solved
    have h : Tm.lower v (Tm.act Tm.idA X.1) = Tm.lower v (Tm.act Tm.idA target.1) :=
      solved (X, target) List.mem_cons_self
    simp only [Tm.act_id, X, target, Tm.lower] at h
    cases h
  exact ⟨unsolved, fun fixed => unsolved ((solved_fixed_points v _).mpr fixed)⟩

end SolverControls

end CumulativeCodes

#print axioms fixes_of_idempotent
#print axioms CumulativeCodes.Rule.idempotent
#print axioms CumulativeCodes.Runs.fixes
#print axioms CumulativeCodes.solved_equalizer
#print axioms CumulativeCodes.solved_idempotent
#print axioms CumulativeCodes.equalizer_or_unsolvable
#print axioms CumulativeCodes.SolverControls.solved_fixed_points
#print axioms CumulativeCodes.SolverControls.identity_not_fixed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
