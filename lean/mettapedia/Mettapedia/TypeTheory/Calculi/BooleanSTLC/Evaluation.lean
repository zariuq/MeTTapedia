import Mettapedia.TypeTheory.Calculi.BooleanSTLC.Syntax

/-!
# Evaluation of the boolean calculus

Every term evaluates, by structural recursion, in the standard model: booleans
are Lean booleans, propositions are Lean propositions, products are pairs and
functions are functions.  The evaluation of a closed term of type `bool` is the
boolean it computes, and that of a closed proposition is its truth; these are
the two ground observations.

The module proves that evaluation commutes with renaming and substitution
(`eval_rename`, `eval_subst`), from which the computation rules of the
eliminators follow: β for abstraction (`value_app_lam_subst`), instantiation of
a boolean quantifier (`eval_allBool_subst`), and the value of a weakened
closed term (`eval_weaken`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.BooleanSTLC

/-- The standard model of types. -/
def Ty.denote : Ty → Type
  | .bool => Bool
  | .prop => Prop
  | .prod A B => A.denote × B.denote
  | .arr A B => A.denote → B.denote

/-- Environments: a value for every variable. -/
abbrev Env (Γ : Ctx) : Type := ∀ ⦃A : Ty⦄, Var Γ A → A.denote

/-- The environment of the empty context. -/
def Env.empty : Env [] := fun _ v => nomatch v

/-- Extend an environment by a value for the newest variable. -/
def Env.cons {Γ : Ctx} {A : Ty} (x : A.denote) (γ : Env Γ) : Env (A :: Γ) :=
  fun _ v => match v with
    | .zero => x
    | .succ w => γ w

/-- Evaluation in an environment. -/
def Tm.eval : {Γ : Ctx} → {A : Ty} → Tm Γ A → Env Γ → A.denote
  | _, _, .var v, γ => γ v
  | _, _, .tt, _ => true
  | _, _, .ff, _ => false
  | _, _, .ite c t e, γ => cond (c.eval γ) (t.eval γ) (e.eval γ)
  | _, _, .pair a b, γ => (a.eval γ, b.eval γ)
  | _, _, .fst p, γ => (p.eval γ).1
  | _, _, .snd p, γ => (p.eval γ).2
  | _, _, .lam b, γ => fun x => b.eval (γ.cons x)
  | _, _, .app f a, γ => f.eval γ (a.eval γ)
  | _, _, .top, _ => True
  | _, _, .bot, _ => False
  | _, _, .and p q, γ => p.eval γ ∧ q.eval γ
  | _, _, .imp p q, γ => p.eval γ → q.eval γ
  | _, _, .isTrue b, γ => b.eval γ = true
  | _, _, .allBool b, γ => ∀ x : Bool, b.eval (γ.cons x)

/-- The value of a closed term. -/
def Tm.value {A : Ty} (t : Closed A) : A.denote :=
  t.eval Env.empty

/-! ## Environments -/

theorem Env.ext {Γ : Ctx} {γ δ : Env Γ} (pointwise : ∀ (A : Ty) (v : Var Γ A), γ v = δ v) :
    γ = δ :=
  funext fun A => funext fun v => pointwise A v

theorem Env.eq_empty (γ : Env []) : γ = Env.empty :=
  Env.ext fun _ v => nomatch v

/-! ## Evaluation commutes with renaming and substitution -/

theorem Tm.eval_rename {Γ : Ctx} {A : Ty} (t : Tm Γ A) :
    ∀ {Δ : Ctx} (ρ : Ren Γ Δ) (δ : Env Δ),
      (t.rename ρ).eval δ = t.eval (fun _ v => δ (ρ v)) := by
  induction t with
  | var v => intro _ _ _; rfl
  | tt => intro _ _ _; rfl
  | ff => intro _ _ _; rfl
  | ite c t e ihc iht ihe =>
      intro _ ρ δ
      show cond _ _ _ = cond _ _ _
      rw [ihc ρ δ, iht ρ δ, ihe ρ δ]
  | pair a b iha ihb =>
      intro _ ρ δ
      show (_, _) = (_, _)
      rw [iha ρ δ, ihb ρ δ]
  | fst p ih =>
      intro _ ρ δ
      show (_ : _ × _).1 = (_ : _ × _).1
      rw [ih ρ δ]
  | snd p ih =>
      intro _ ρ δ
      show (_ : _ × _).2 = (_ : _ × _).2
      rw [ih ρ δ]
  | lam b ih =>
      intro _ ρ δ
      funext x
      show (b.rename ρ.lift).eval (δ.cons x) = b.eval (Env.cons x _)
      rw [ih ρ.lift (δ.cons x)]
      congr 1
      exact Env.ext fun _ v => by cases v <;> rfl
  | app f a ihf iha =>
      intro _ ρ δ
      show (f.rename ρ).eval δ ((a.rename ρ).eval δ) = f.eval _ (a.eval _)
      rw [ihf ρ δ, iha ρ δ]
  | top => intro _ _ _; rfl
  | bot => intro _ _ _; rfl
  | and p q ihp ihq =>
      intro _ ρ δ
      show ((p.rename ρ).eval δ ∧ (q.rename ρ).eval δ) = (p.eval _ ∧ q.eval _)
      rw [ihp ρ δ, ihq ρ δ]
  | imp p q ihp ihq =>
      intro _ ρ δ
      show ((p.rename ρ).eval δ → (q.rename ρ).eval δ) = (p.eval _ → q.eval _)
      rw [ihp ρ δ, ihq ρ δ]
  | isTrue b ih =>
      intro _ ρ δ
      show ((b.rename ρ).eval δ = true) = (b.eval _ = true)
      rw [ih ρ δ]
  | allBool b ih =>
      intro _ ρ δ
      show (∀ x : Bool, (b.rename ρ.lift).eval (δ.cons x)) = ∀ x : Bool, b.eval (Env.cons x _)
      refine forall_congr fun x => ?_
      rw [ih ρ.lift (δ.cons x)]
      congr 1
      exact Env.ext fun _ v => by cases v <;> rfl

/-- A weakened closed term evaluates to its value in every environment. -/
theorem Tm.eval_weaken {Γ : Ctx} {A : Ty} (t : Closed A) (γ : Env Γ) :
    (t.weaken : Tm Γ A).eval γ = t.value := by
  unfold Tm.weaken Tm.value
  rw [Tm.eval_rename]
  congr 1
  exact Env.eq_empty _

/-- The environment of a substitution evaluated in `δ`. -/
def Sub.eval {Γ Δ : Ctx} (σ : Sub Γ Δ) (δ : Env Δ) : Env Γ :=
  fun _ v => (σ v).eval δ

theorem Sub.eval_lift {Γ Δ : Ctx} {B : Ty} (σ : Sub Γ Δ) (δ : Env Δ) (x : B.denote) :
    (Sub.lift (B := B) σ).eval (δ.cons x) = (σ.eval δ).cons x := by
  refine Env.ext fun _ v => ?_
  cases v with
  | zero => rfl
  | succ w =>
      show ((σ w).rename Ren.weaken).eval (δ.cons x) = (σ w).eval δ
      rw [Tm.eval_rename]
      rfl

theorem Tm.eval_subst {Γ : Ctx} {A : Ty} (t : Tm Γ A) :
    ∀ {Δ : Ctx} (σ : Sub Γ Δ) (δ : Env Δ), (t.subst σ).eval δ = t.eval (σ.eval δ) := by
  induction t with
  | var v => intro _ _ _; rfl
  | tt => intro _ _ _; rfl
  | ff => intro _ _ _; rfl
  | ite c t e ihc iht ihe =>
      intro _ σ δ
      show cond _ _ _ = cond _ _ _
      rw [ihc σ δ, iht σ δ, ihe σ δ]
  | pair a b iha ihb =>
      intro _ σ δ
      show (_, _) = (_, _)
      rw [iha σ δ, ihb σ δ]
  | fst p ih =>
      intro _ σ δ
      show (_ : _ × _).1 = (_ : _ × _).1
      rw [ih σ δ]
  | snd p ih =>
      intro _ σ δ
      show (_ : _ × _).2 = (_ : _ × _).2
      rw [ih σ δ]
  | lam b ih =>
      intro _ σ δ
      funext x
      show (b.subst σ.lift).eval (δ.cons x) = b.eval ((σ.eval δ).cons x)
      rw [ih σ.lift (δ.cons x), Sub.eval_lift]
  | app f a ihf iha =>
      intro _ σ δ
      show (f.subst σ).eval δ ((a.subst σ).eval δ) = f.eval _ (a.eval _)
      rw [ihf σ δ, iha σ δ]
  | top => intro _ _ _; rfl
  | bot => intro _ _ _; rfl
  | and p q ihp ihq =>
      intro _ σ δ
      show ((p.subst σ).eval δ ∧ (q.subst σ).eval δ) = (p.eval _ ∧ q.eval _)
      rw [ihp σ δ, ihq σ δ]
  | imp p q ihp ihq =>
      intro _ σ δ
      show ((p.subst σ).eval δ → (q.subst σ).eval δ) = (p.eval _ → q.eval _)
      rw [ihp σ δ, ihq σ δ]
  | isTrue b ih =>
      intro _ σ δ
      show ((b.subst σ).eval δ = true) = (b.eval _ = true)
      rw [ih σ δ]
  | allBool b ih =>
      intro _ σ δ
      show (∀ x : Bool, (b.subst σ.lift).eval (δ.cons x)) = ∀ x : Bool, b.eval ((σ.eval δ).cons x)
      refine forall_congr fun x => ?_
      rw [ih σ.lift (δ.cons x)]
      exact congrArg b.eval (Sub.eval_lift (B := .bool) σ δ x)

/-! ## Computation rules for closed terms -/

/-- Substituting into a closed term does not change its value. -/
theorem Tm.value_subst_closed {A : Ty} (t : Closed A) (σ : Sub [] []) :
    (t.subst σ).value = t.value := by
  unfold Tm.value
  rw [Tm.eval_subst]
  congr 1
  exact Env.eq_empty _

/-- Closing the body of a binder by `σ` and evaluating at the value of `a` is
closing it by `a` and `σ`. -/
theorem Tm.eval_subst_lift_cons {Γ : Ctx} {A B : Ty} (σ : Sub Γ []) (body : Tm (A :: Γ) B)
    (a : Closed A) :
    (body.subst σ.lift).eval (Env.empty.cons a.value) = (body.subst (Sub.cons a σ)).value := by
  unfold Tm.value
  rw [Tm.eval_subst, Tm.eval_subst, Sub.eval_lift]
  congr 1
  exact Env.ext fun _ v => by cases v <;> rfl

/-- **β for closed instances.** -/
theorem Tm.value_app_lam_subst {Γ : Ctx} {A B : Ty} (σ : Sub Γ []) (body : Tm (A :: Γ) B)
    (a : Closed A) :
    (Tm.app ((Tm.lam body).subst σ) a).value = (body.subst (Sub.cons a σ)).value :=
  Tm.eval_subst_lift_cons σ body a

@[simp] theorem Tm.value_ofBool (x : Bool) : (Tm.ofBool x : Closed .bool).value = x := by
  cases x <;> rfl

/-- **Instantiation of a boolean quantifier for closed instances.** -/
theorem Tm.eval_allBool_subst {Γ : Ctx} (σ : Sub Γ []) (body : Tm (.bool :: Γ) .prop) (x : Bool) :
    (body.subst σ.lift).eval (Env.empty.cons x) =
      (body.subst (Sub.cons (Tm.ofBool x) σ)).value := by
  have := Tm.eval_subst_lift_cons σ body (Tm.ofBool x)
  rwa [Tm.value_ofBool] at this

theorem Tm.value_fill {A B : Ty} (body : Tm [A] B) (argument : Closed A) :
    (body.fill argument).value = body.eval (Env.empty.cons argument.value) := by
  unfold Tm.fill Tm.value
  rw [Tm.eval_subst]
  congr 1
  exact Env.ext fun _ v => by
    cases v with
    | zero => rfl
    | succ w => exact nomatch w

end Mettapedia.TypeTheory.Calculi.BooleanSTLC
