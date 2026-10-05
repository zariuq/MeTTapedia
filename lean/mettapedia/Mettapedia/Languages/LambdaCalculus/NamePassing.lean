import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# The reference-binding fragment of name-passing lambda calculus

The constructors and root rules are Example 30 of Williams and Stay's
`Native Type Theory`: application takes a name, `def` binds a reference,
and `carrier` supplies one fetch. This is not ordinary lambda calculus or
dependent lambda-Pi type theory.

Scopes and binder lifts use the shared intrinsically sorted variable
calculus. The expression family is parameterized by the sort alphabet and
the name sort, so the same syntax can be interpreted over the name contexts
of a target calculus without converting variable positions to strings.
Only names are substituted: they remain variables, rather than becoming
arbitrary lambda expressions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing

open Mettapedia.OSLF.Binding

variable {Srt : Type} {nm : Srt}

/-- The name-passing expression grammar, with binding as part of its type. -/
inductive Expr (nm : Srt) : List Srt → Type where
  | var {Γ} : Var Γ nm → Expr nm Γ
  | lam {Γ} : Expr nm (nm :: Γ) → Expr nm Γ
  | app {Γ} : Expr nm Γ → Var Γ nm → Expr nm Γ
  | defn {Γ} : Expr nm Γ → Expr nm (nm :: Γ) → Expr nm Γ
  | carrier {Γ} : Var Γ nm → Expr nm Γ → Expr nm Γ → Expr nm Γ

/-- Reindex names with the shared binder-fixing lift. -/
def rename : {Γ Δ : List Srt} →
    ((s : Srt) → Var Γ s → Var Δ s) → Expr nm Γ → Expr nm Δ
  | _, _, ρ, .var x => .var (ρ _ x)
  | _, _, ρ, .lam body => .lam (rename (liftRen ρ [nm]) body)
  | _, _, ρ, .app f x => .app (rename ρ f) (ρ _ x)
  | _, _, ρ, .defn value body =>
      .defn (rename ρ value) (rename (liftRen ρ [nm]) body)
  | _, _, ρ, .carrier x value body =>
      .carrier (ρ _ x) (rename ρ value) (rename ρ body)

@[simp] theorem rename_id {Γ : List Srt} (term : Expr nm Γ) :
    rename (fun _ x => x) term = term := by
  have lifted {Γ : List Srt} :
      liftRen (Γ := Γ) (fun (s : Srt) (x : Var Γ s) => x) [nm] =
        (fun _ x => x) := by
    funext s x
    cases x <;> rfl
  induction term with
  | var x => rfl
  | lam body ih =>
      simp only [rename, lifted]
      exact congrArg Expr.lam ih
  | app f x ih => simp only [rename, ih]
  | defn value body ihv ihb =>
      simp only [rename, lifted]
      exact congrArg₂ Expr.defn ihv ihb
  | carrier x value body ihv ihb => simp only [rename, ihv, ihb]

theorem rename_comp {Γ Δ Θ : List Srt}
    (ρ : (s : Srt) → Var Γ s → Var Δ s)
    (τ : (s : Srt) → Var Δ s → Var Θ s) (term : Expr nm Γ) :
    rename τ (rename ρ term) = rename (fun s x => τ s (ρ s x)) term := by
  have lifted {Γ Δ Θ : List Srt}
      (ρ : (s : Srt) → Var Γ s → Var Δ s)
      (τ : (s : Srt) → Var Δ s → Var Θ s) :
      (fun s x => liftRen τ [nm] s (liftRen ρ [nm] s x)) =
        liftRen (fun s x => τ s (ρ s x)) [nm] := by
    funext s x
    cases x <;> rfl
  induction term generalizing Δ Θ with
  | var x => rfl
  | lam body ih =>
      simp only [rename, ih]
      exact congrArg (fun r => Expr.lam (rename r body)) (lifted ρ τ)
  | app f x ih => simp only [rename, ih]
  | defn value body ihv ihb =>
      simp only [rename, ihv, ihb]
      exact congrArg (fun r => Expr.defn _ (rename r body)) (lifted ρ τ)
  | carrier x value body ihv ihb => simp only [rename, ihv, ihb]

/-- A fresh binder is introduced without capturing enclosing variables. -/
def weaken {Γ : List Srt} {fresh : Srt} (term : Expr nm Γ) :
    Expr nm (fresh :: Γ) := rename (fun _ x => .succ x) term

/-- Replace the top name by an existing name and retain enclosing variables. -/
def plugName {Γ : List Srt} (x : Var Γ nm) :
    (s : Srt) → Var (nm :: Γ) s → Var Γ s
  | _, .zero => x
  | _, .succ old => old

/-- Beta instantiation is name substitution, not arbitrary term substitution. -/
def instantiate {Γ : List Srt} (body : Expr nm (nm :: Γ))
    (argument : Var Γ nm) : Expr nm Γ := rename (plugName argument) body

/-- The two displayed root rules of the abridged source calculus. -/
inductive RootStep {Γ : List Srt} : Expr nm Γ → Expr nm Γ → Prop where
  | beta (body : Expr nm (nm :: Γ)) (argument : Var Γ nm) :
      RootStep (.app (.lam body) argument) (instantiate body argument)
  | fetch (name : Var Γ nm) (value : Expr nm Γ) :
      RootStep (.carrier name value (.var name)) value

theorem instantiate_rename {Γ Δ : List Srt}
    (ρ : (s : Srt) → Var Γ s → Var Δ s)
    (body : Expr nm (nm :: Γ)) (argument : Var Γ nm) :
    rename ρ (instantiate body argument) =
      instantiate (rename (liftRen ρ [nm]) body) (ρ _ argument) := by
  simp only [instantiate, rename_comp]
  congr 1
  funext s x
  cases x <;> rfl

/-- Every source root firing survives simultaneous substitution of names. -/
theorem RootStep.rename {Γ Δ : List Srt}
    (ρ : (s : Srt) → Var Γ s → Var Δ s)
    {source target : Expr nm Γ} (step : RootStep source target) :
    RootStep (NamePassing.rename ρ source) (NamePassing.rename ρ target) := by
  cases step with
  | beta body argument =>
      simpa only [NamePassing.rename, instantiate_rename] using
        RootStep.beta (NamePassing.rename (liftRen ρ [nm]) body) (ρ _ argument)
  | fetch name =>
      exact RootStep.fetch (ρ _ name) (NamePassing.rename ρ target)

theorem var_no_root_step {Γ : List Srt} (name : Var Γ nm)
    {target : Expr nm Γ} : ¬ RootStep (.var name) target := by
  intro step
  cases step

theorem beta_iff {Γ : List Srt} (body : Expr nm (nm :: Γ))
    (argument : Var Γ nm) (target : Expr nm Γ) :
    RootStep (.app (.lam body) argument) target ↔
      target = instantiate body argument := by
  constructor
  · intro step; cases step; rfl
  · rintro rfl; exact .beta body argument

theorem fetch_iff {Γ : List Srt} (name : Var Γ nm) (value target : Expr nm Γ) :
    RootStep (.carrier name value (.var name)) target ↔ target = value := by
  constructor
  · intro step; cases step; rfl
  · intro same; subst target; exact .fetch name value

/-- Distinct names cannot fetch one another's carrier at the root. -/
theorem distinct_name_no_fetch {Γ : List Srt} (x y : Var Γ nm)
    (different : x ≠ y) (value target : Expr nm Γ) :
    ¬ RootStep (.carrier x value (.var y)) target := by
  intro step
  cases step
  exact different rfl

/-- Evaluation contexts which expose a head computation. Lambda bodies and
stored definition/carrier values are suspended until called or fetched. -/
inductive HeadStep : {Γ : List Srt} → Expr nm Γ → Expr nm Γ → Prop where
  | root {Γ} {source target : Expr nm Γ} : RootStep source target → HeadStep source target
  | app {Γ} {function function' : Expr nm Γ} (argument : Var Γ nm) :
      HeadStep function function' →
      HeadStep (.app function argument) (.app function' argument)
  | defn {Γ} (value : Expr nm Γ) {body body' : Expr nm (nm :: Γ)} :
      HeadStep body body' → HeadStep (.defn value body) (.defn value body')
  | carrier {Γ} (name : Var Γ nm) (value : Expr nm Γ) {body body' : Expr nm Γ} :
      HeadStep body body' →
      HeadStep (.carrier name value body) (.carrier name value body')

theorem HeadStep.rename {Γ Δ : List Srt}
    (ρ : (s : Srt) → Var Γ s → Var Δ s)
    {source target : Expr nm Γ} (step : HeadStep source target) :
    HeadStep (NamePassing.rename ρ source) (NamePassing.rename ρ target) := by
  induction step generalizing Δ with
  | root rootStep => exact .root (rootStep.rename ρ)
  | app argument step ih =>
      exact .app (ρ _ argument) (ih ρ)
  | defn value step ih =>
      exact .defn (NamePassing.rename ρ value) (ih (liftRen ρ [nm]))
  | carrier name value step ih =>
      exact .carrier (ρ _ name) (NamePassing.rename ρ value) (ih ρ)

theorem lambda_no_head_step {Γ : List Srt} (body : Expr nm (nm :: Γ))
    {target : Expr nm Γ} : ¬ HeadStep (.lam body) target := by
  intro step
  cases step with
  | root impossible => cases impossible

theorem var_no_head_step {Γ : List Srt} (name : Var Γ nm)
    {target : Expr nm Γ} : ¬ HeadStep (.var name) target := by
  intro step
  cases step with
  | root impossible => cases impossible

theorem defn_variable_no_head_step {Γ : List Srt} (value : Expr nm Γ)
    (name : Var (nm :: Γ) nm) {target : Expr nm Γ} :
    ¬ HeadStep (.defn value (.var name)) target := by
  intro step
  cases step with
  | root impossible => cases impossible
  | defn value impossible => exact var_no_head_step name impossible


end Mettapedia.Languages.LambdaCalculus.NamePassing
