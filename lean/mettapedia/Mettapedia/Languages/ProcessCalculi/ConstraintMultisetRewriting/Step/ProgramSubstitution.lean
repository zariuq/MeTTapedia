import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaExecution

/-!
# Closure β and substitution β (Plotkin's correspondence), joined with contextual λ execution

The λ fragment is stated on the intrinsically scoped λ terms of the contextual account
(`LambdaContextualRung`), so that substitution is the binder-aware `inst` of the existing syntax.

* **Closure semantics** (`EvalEnv`): call-by-value evaluation in an environment of closures, the
  big-step reading of the environment machine (Landin's SECD, Felleisen–Friedman's CEK; Danvy's
  functional correspondence). Application evaluates the operator to a closure, the operand to a
  value, and the closure's body in its captured environment extended by that value.
* **Substitution semantics** (`Eval`): call-by-value evaluation of closed terms, where β substitutes
  the operand's value into the body with `inst`.
* **Read-back** (`rb`): a closure reads back as the abstraction whose body has the closure's
  environment substituted for its free variables, the environment read back in turn.
* **Plotkin's correspondence** (`plotkin_forward`, `plotkin_backward`, `plotkin_closed`): closure
  evaluation in an environment and substitution evaluation of the term with the read-back
  environment substituted agree, value for value. The key law is that β after closure read-back is
  substitution of the extended environment (`inst_lift`).
* **The join with contextual λ execution** (`eval_steps`, `eval_executes`): every substitution
  evaluation is a path of the context-indexed λ reduction (`LambdaContextualRung.Step`), so the
  contextual execution on the step (`LambdaExecution.finite_execution_iff`) reaches a state
  representing the value. Both accounts describe the same computation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramSubstitution

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.LambdaContextualRung (sig Srt Op appT lamT)

/-! ## Closures and environments -/

/-- A closure: a body under one binder, and an environment for its other free variables. -/
inductive Val where
  | clo (Γ : Ctx sig) (body : Term sig (.term :: Γ) .term) (env : (s : sig.Srt) → Var Γ s → Val)

/-- Environments give a value to every variable. -/
abbrev Env (Γ : Ctx sig) := (s : sig.Srt) → Var Γ s → Val

/-- The environment extended by a value for the new innermost variable. -/
def consEnv {Γ : Ctx sig} (w : Val) (ρ : Env Γ) : Env (.term :: Γ)
  | _, .zero => w
  | s, .succ v => ρ s v

/-- **Read-back**: a closure as the abstraction with its environment substituted. -/
def rb : Val → Term sig [] .term
  | .clo _ b ρ => lamT (bind (liftSub (fun s v => rb (ρ s v)) [.term]) b)

/-- The read-back environment, as a substitution. -/
def rbSub {Γ : Ctx sig} (ρ : Env Γ) : Sub sig Γ [] := fun s v => rb (ρ s v)

/-- The substitution with a closed term for the new innermost variable. -/
def consSub {Γ : Ctx sig} (t : Term sig [] .term) (σ : Sub sig Γ []) : Sub sig (.term :: Γ) []
  | _, .zero => t
  | s, .succ v => σ s v

theorem rbSub_cons {Γ : Ctx sig} (w : Val) (ρ : Env Γ) :
    rbSub (consEnv w ρ) = consSub (rb w) (rbSub ρ) := by
  funext s v
  cases v <;> rfl

/-- **β after read-back is substitution of the extended environment.** -/
theorem inst_lift {Γ : Ctx sig} (σ : Sub sig Γ []) (b : Term sig (.term :: Γ) .term)
    (t : Term sig [] .term) : inst (bind (liftSub σ [.term]) b) t = bind (consSub t σ) b := by
  show bind (extend t) (bind (liftSub σ [.term]) b) = _
  refine (bind_comp (liftSub σ [.term]) (extend t) b).trans ?_
  congr 1
  funext s v
  cases v with
  | zero => rfl
  | succ w => exact inst_weaken (σ s w) t

/-! ## The two semantics -/

/-- **Closure semantics**: call-by-value evaluation in an environment. -/
inductive EvalEnv : {Γ : Ctx sig} → Env Γ → Term sig Γ .term → Val → Prop
  | var {Γ : Ctx sig} (ρ : Env Γ) (x : Var Γ .term) : EvalEnv ρ (.var x) (ρ .term x)
  | lam {Γ : Ctx sig} (ρ : Env Γ) (b : Term sig (.term :: Γ) .term) : EvalEnv ρ (lamT b) (.clo Γ b ρ)
  | app {Γ Γ' : Ctx sig} {ρ : Env Γ} {f a : Term sig Γ .term} {b : Term sig (.term :: Γ') .term}
      {ρ' : Env Γ'} {w v : Val} :
      EvalEnv ρ f (.clo Γ' b ρ') → EvalEnv ρ a w → EvalEnv (consEnv w ρ') b v → EvalEnv ρ (appT f a) v

/-- **Substitution semantics**: call-by-value evaluation of closed terms, β by `inst`. -/
inductive Eval : Term sig [] .term → Term sig [] .term → Prop
  | lam (b : Term sig [.term] .term) : Eval (lamT b) (lamT b)
  | app {f a w v : Term sig [] .term} {b : Term sig [.term] .term} :
      Eval f (lamT b) → Eval a w → Eval (inst b w) v → Eval (appT f a) v

theorem eval_rb (v : Val) : Eval (rb v) (rb v) := by
  cases v with
  | clo Γ b ρ => exact .lam _

/-! ## Plotkin's correspondence -/

/-- **Closure evaluation is substitution evaluation of the read-back.** -/
theorem plotkin_forward {Γ : Ctx sig} {ρ : Env Γ} {e : Term sig Γ .term} {v : Val}
    (h : EvalEnv ρ e v) : Eval (bind (rbSub ρ) e) (rb v) := by
  induction h with
  | var ρ x => exact eval_rb (ρ .term x)
  | lam ρ b => exact .lam _
  | @app Γ Γ' ρ f a b ρ' w v hf ha hb ihf iha ihb =>
      have key : inst (bind (liftSub (rbSub ρ') [.term]) b) (rb w) = bind (rbSub (consEnv w ρ')) b := by
        rw [inst_lift, rbSub_cons]
      exact Eval.app (b := bind (liftSub (rbSub ρ') [.term]) b) ihf iha (key ▸ ihb)

/-- **Substitution evaluation of a read-back term is closure evaluation.** -/
theorem plotkin_backward {t u : Term sig [] .term} (h : Eval t u) :
    ∀ {Γ : Ctx sig} (ρ : Env Γ) (e : Term sig Γ .term), bind (rbSub ρ) e = t →
      ∃ v, EvalEnv ρ e v ∧ rb v = u := by
  induction h with
  | lam b =>
      intro Γ ρ e he
      match e, he with
      | .var x, he => exact ⟨ρ .term x, .var ρ x, he⟩
      | .op .lam (.cons b' .nil), he => exact ⟨.clo Γ b' ρ, .lam ρ b', he⟩
      | .op .app (.cons f (.cons a .nil)), he => cases he
  | @app f₀ a₀ w₀ v₀ b₀ hf ha hb ihf iha ihb =>
      intro Γ ρ e he
      match e, he with
      | .var x, he =>
          cases hx : ρ .term x with
          | clo Γ' b' ρ' =>
              have he' : rb (ρ .term x) = appT f₀ a₀ := he
              rw [hx] at he'
              cases he'
      | .op .lam (.cons b' .nil), he => cases he
      | .op .app (.cons f (.cons a .nil)), he =>
          cases he
          obtain ⟨vf, evf, rbf⟩ := ihf ρ f rfl
          obtain ⟨w, evw, rbw⟩ := iha ρ a rfl
          cases vf with
          | clo Γ' b' ρ' =>
              cases rbf
              cases rbw
              have key : bind (rbSub (consEnv w ρ')) b' =
                  inst (bind (liftSub (rbSub ρ') [.term]) b') (rb w) := by
                rw [inst_lift, rbSub_cons]
              obtain ⟨v, evb, rbv⟩ := ihb (consEnv w ρ') b' key
              exact ⟨v, .app evf evw evb, rbv⟩

/-- The empty environment. -/
def emptyEnv : Env [] := fun _ v => nomatch v

theorem rbSub_empty : rbSub emptyEnv = fun _ v => .var v := by
  funext s v
  nomatch v

/-- **Plotkin's correspondence for closed programs**: a closed term has a closure value reading
back as `u` exactly when it evaluates to `u` by substitution. -/
theorem plotkin_closed (e u : Term sig [] .term) :
    (∃ v, EvalEnv emptyEnv e v ∧ rb v = u) ↔ Eval e u := by
  have identity : bind (rbSub emptyEnv) e = e := by
    rw [rbSub_empty]
    exact bind_id e
  constructor
  · rintro ⟨v, ev, rfl⟩
    have := plotkin_forward ev
    rwa [identity] at this
  · intro h
    exact plotkin_backward h emptyEnv e identity

/-! ## The join with contextual λ execution -/

theorem congr_left {Γ : Ctx sig} {s t : Term sig Γ .term} (a : Term sig Γ .term)
    (path : Relation.ReflTransGen (LambdaContextualRung.Step Γ) s t) :
    Relation.ReflTransGen (LambdaContextualRung.Step Γ) (appT s a) (appT t a) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.appCongL a step)

theorem congr_right {Γ : Ctx sig} {s t : Term sig Γ .term} (f : Term sig Γ .term)
    (path : Relation.ReflTransGen (LambdaContextualRung.Step Γ) s t) :
    Relation.ReflTransGen (LambdaContextualRung.Step Γ) (appT f s) (appT f t) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.appCongR f step)

/-- **Every substitution evaluation is a path of context-indexed λ reduction.** -/
theorem eval_steps {t u : Term sig [] .term} (h : Eval t u) :
    Relation.ReflTransGen (LambdaContextualRung.Step []) t u := by
  induction h with
  | lam b => exact .refl
  | @app f a w v b hf ha hb ihf iha ihb =>
      exact ((congr_left a ihf).trans (congr_right (lamT b) iha)).trans
        (Relation.ReflTransGen.head (.beta b w) ihb)

/-- **The same computation on the step**: a closure evaluation of a closed program is matched by a
contextual execution on the step that reaches a state representing the read-back value. -/
theorem eval_executes {e : Term sig [] .term} {v : Val} (ev : EvalEnv emptyEnv e v) :
    ∃ after, Relation.ReflTransGen LambdaExecution.Transition (LambdaExecution.initial e) after ∧
      LambdaExecution.Represents after (rb v) :=
  (LambdaExecution.finite_execution_iff e (rb v)).mp
    (eval_steps ((plotkin_closed e (rb v)).mp ⟨v, ev, rfl⟩))

#print axioms rbSub_cons
#print axioms inst_lift
#print axioms plotkin_forward
#print axioms plotkin_backward
#print axioms plotkin_closed
#print axioms eval_steps
#print axioms eval_executes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramSubstitution
