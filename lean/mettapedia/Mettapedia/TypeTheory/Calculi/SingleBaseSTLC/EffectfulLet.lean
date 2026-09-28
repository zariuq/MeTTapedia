import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Presentation
import Mathlib.Data.List.Monad

/-!
# Scoped lexical binding with effects

This extends the existing intrinsically scoped simple-type fragment with
independent let syntax and effectful ground operations. An arbitrary lawful
monad supplies effects; no commutativity, totality, or finite-search law is
assumed. This is a comparison fragment, not the syntax of a full language.

Lowering removes every let by lambda application. Its proof preserves the
entire monadic meaning, including higher-order results and captured variables.
It does not identify relational pattern matching with lexical binding.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.EffectfulLet

open IntrinsicSTT (Ty Var Renaming liftRenaming)

universe u

@[reducible] def Value (M : Type u → Type u) (Ground : Type u) : Ty → Type u
  | .atom => Ground
  | .arr a b => Value M Ground a → M (Value M Ground b)

abbrev Env (M : Type u → Type u) (Ground : Type u) (Γ : List Ty) :=
  ∀ {a}, Var Γ a → Value M Ground a

def extend {M : Type u → Type u} {Ground : Type u} {Γ : List Ty} {a : Ty}
    (value : Value M Ground a) (env : Env M Ground Γ) : Env M Ground (a :: Γ)
  | _, .zero => value
  | _, .succ v => env v

inductive Term (M : Type u → Type u) (Ground : Type u) : List Ty → Ty → Type u where
  | var {Γ a} : Var Γ a → Term M Ground Γ a
  | lit {Γ} : Ground → Term M Ground Γ .atom
  | effect {Γ} : M Ground → Term M Ground Γ .atom
  | lam {Γ a b} : Term M Ground (a :: Γ) b → Term M Ground Γ (.arr a b)
  | app {Γ a b} : Term M Ground Γ (.arr a b) → Term M Ground Γ a → Term M Ground Γ b
  | letE {Γ a b} : Term M Ground Γ a → Term M Ground (a :: Γ) b → Term M Ground Γ b

variable {M : Type u → Type u} {Ground : Type u} {Γ Δ : List Ty} {a b : Ty}

def Term.eval [Monad M] : {Γ : List Ty} → {a : Ty} →
    Term M Ground Γ a → Env M Ground Γ → M (Value M Ground a)
  | _, _, .var v, env => pure (env v)
  | _, _, .lit value, _ => pure value
  | _, _, .effect action, _ => action
  | _, _, .lam body, env => pure (fun value => body.eval (extend value env))
  | _, _, .app fn arg, env => do
      let f ← fn.eval env
      let value ← arg.eval env
      f value
  | _, _, .letE source body, env => do
      let value ← source.eval env
      body.eval (extend value env)

def Term.lower : {Γ : List Ty} → {a : Ty} → Term M Ground Γ a → Term M Ground Γ a
  | _, _, .var v => .var v
  | _, _, .lit value => .lit value
  | _, _, .effect action => .effect action
  | _, _, .lam body => .lam body.lower
  | _, _, .app fn arg => .app fn.lower arg.lower
  | _, _, .letE source body => .app (.lam body.lower) source.lower

def Term.letFree : {Γ : List Ty} → {a : Ty} → Term M Ground Γ a → Bool
  | _, _, .var _ | _, _, .lit _ | _, _, .effect _ => true
  | _, _, .lam body => body.letFree
  | _, _, .app fn arg => fn.letFree && arg.letFree
  | _, _, .letE _ _ => false

theorem Term.lower_letFree (term : Term M Ground Γ a) : term.lower.letFree = true := by
  induction term <;> simp_all [lower, letFree]

theorem Term.lower_idempotent (term : Term M Ground Γ a) : term.lower.lower = term.lower := by
  induction term <;> simp_all [lower]

/-- Let and application have independent interpretation clauses. The
transformation is correct for all terms, not only a root redex. -/
theorem Term.eval_lower [Monad M] [LawfulMonad M] (term : Term M Ground Γ a)
    (env : Env M Ground Γ) : term.lower.eval env = term.eval env := by
  induction term with
  | var v => rfl
  | lit value => rfl
  | effect action => rfl
  | lam body ih => simp only [lower, eval, ih]
  | app fn arg ihFn ihArg => simp only [lower, eval, ihFn, ihArg]
  | letE source body ihSource ihBody =>
      simp only [lower, eval, pure_bind, ihSource, ihBody]

def Term.rename : {Γ Δ : List Ty} → Renaming Γ Δ → {a : Ty} →
    Term M Ground Γ a → Term M Ground Δ a
  | _, _, ρ, _, .var v => .var (ρ v)
  | _, _, _, _, .lit value => .lit value
  | _, _, _, _, .effect action => .effect action
  | _, _, ρ, _, .lam body => .lam (body.rename (liftRenaming ρ))
  | _, _, ρ, _, .app fn arg => .app (fn.rename ρ) (arg.rename ρ)
  | _, _, ρ, _, .letE source body => .letE (source.rename ρ) (body.rename (liftRenaming ρ))

/-- Lowering does not change the meaning of any binder index. -/
theorem Term.lower_rename (term : Term M Ground Γ a) (ρ : Renaming Γ Δ) :
    (term.rename ρ).lower = term.lower.rename ρ := by
  induction term generalizing Δ <;> simp_all [rename, lower]

def reindex (ρ : Renaming Γ Δ) (env : Env M Ground Δ) : Env M Ground Γ :=
  fun v => env (ρ v)

theorem reindex_extend (ρ : Renaming Γ Δ) (env : Env M Ground Δ)
    (value : Value M Ground a) :
    @Eq (Env M Ground (a :: Γ)) (reindex (liftRenaming ρ) (extend value env))
      (extend value (reindex ρ env)) := by
  funext type v
  cases v <;> rfl

/-- Ambient renaming is capture avoiding, also under effectful lets. -/
theorem Term.eval_rename [Monad M] (term : Term M Ground Γ a)
    (ρ : Renaming Γ Δ) (env : Env M Ground Δ) :
    (term.rename ρ).eval env = term.eval (reindex ρ env) := by
  induction term generalizing Δ with
  | var v => rfl
  | lit value => rfl
  | effect action => rfl
  | lam body ih => simp only [rename, eval, ih, reindex_extend]
  | app fn arg ihFn ihArg => simp only [rename, eval, ihFn, ihArg]
  | letE source body ihSource ihBody =>
      simp only [rename, eval, ihSource, ihBody, reindex_extend]

/-- Match binding has an additional computation which lexical binding lacks.
It may fail, branch, constrain an existing environment, or perform effects. -/
def matchBind [Monad M] {α β ε : Type u} (source : M α) (matchValue : α → M ε)
    (body : ε → M β) : M β := source >>= fun value => matchValue value >>= body

theorem matchBind_pure_match [Monad M] [LawfulMonad M] {α β ε : Type u}
    (source : M α) (extension : α → ε) (body : ε → M β) :
    matchBind source (fun value => pure (extension value)) body =
      source >>= fun value => body (extension value) := by
  simp only [matchBind, pure_bind]

/-- A telescope of sequential bindings. Later producers see all earlier
values, and each step may bind a different type, including function types. -/
inductive Bindings (M : Type u → Type u) (Ground : Type u) : List Ty → List Ty → Type u where
  | nil {Γ : List Ty} : Bindings M Ground Γ Γ
  | cons {Γ Δ : List Ty} {a : Ty} :
      Term M Ground Γ a → Bindings M Ground (a :: Γ) Δ → Bindings M Ground Γ Δ

def Bindings.run [Monad M] : {Γ Δ : List Ty} → Bindings M Ground Γ Δ →
    Env M Ground Γ → M (Env M Ground Δ)
  | _, _, .nil, env => pure env
  | _, _, .cons source rest, env => do
      let value ← source.eval env
      rest.run (extend value env)

/-- Source elaboration of a lexical let-star into nested individual lets. -/
def letStar : {Γ Δ : List Ty} → Bindings M Ground Γ Δ →
    Term M Ground Δ a → Term M Ground Γ a
  | _, _, .nil, body => body
  | _, _, .cons source rest, body => .letE source (letStar rest body)

/-- Independently executing the environment telescope agrees with its
nested source elaboration. Associativity retains evaluation order. -/
theorem eval_letStar [Monad M] [LawfulMonad M] (bindings : Bindings M Ground Γ Δ)
    (body : Term M Ground Δ a) (env : Env M Ground Γ) :
    (letStar bindings body).eval env = (bindings.run env >>= fun next => body.eval next) := by
  induction bindings with
  | nil => simp only [letStar, Bindings.run, pure_bind]
  | cons source rest ih => simp only [letStar, Term.eval, Bindings.run, bind_assoc, ih]

def emptyEnv : Env M Ground [] := fun v => nomatch v

structure Closure (M : Type u → Type u) (Ground : Type u) (a : Ty) where
  context : List Ty
  body : Term M Ground context a
  environment : Env M Ground context

def Closure.run [Monad M] (closure : Closure M Ground a) : M (Value M Ground a) :=
  closure.body.eval closure.environment

def Closure.lower (closure : Closure M Ground a) : Closure M Ground a :=
  { closure with body := closure.body.lower }

theorem Closure.run_lower [Monad M] [LawfulMonad M] (closure : Closure M Ground a) :
    closure.lower.run = closure.run :=
  Term.eval_lower closure.body closure.environment

/-! Executable positive and negative controls. -/

def captured : Term Id Nat [] .atom :=
  .letE (.lit 7) (.app (.lam (.var (.succ .zero))) (.lit 99))

theorem captured_outer_value : captured.eval emptyEnv = 7 := rfl
theorem captured_lower_value : captured.lower.eval emptyEnv = 7 := by
  rw [Term.eval_lower]; rfl

def shadowed : Term Id Nat [] .atom :=
  .letE (.lit 7) (.letE (.lit 99) (.var .zero))

theorem shadowed_inner_value : shadowed.eval emptyEnv = 99 := rfl

def tick : StateM Nat Nat := fun state => (state, state + 1)

def sharedUse : Term (StateM Nat) Nat [] .atom :=
  .letE (.effect tick) (.letE (.var .zero) (.var (.succ .zero)))

/-- Expanding both variable occurrences back into the effect duplicates it. -/
def repeatedUse : Term (StateM Nat) Nat [] .atom :=
  .letE (.effect tick) (.effect tick)

theorem shared_runs_once : (sharedUse.eval emptyEnv).run 0 = (0, 1) := rfl
theorem repeated_runs_twice : (repeatedUse.eval emptyEnv).run 0 = (1, 2) := rfl
theorem substitution_of_computation_changes_effects :
    (sharedUse.eval emptyEnv).run 0 ≠ (repeatedUse.eval emptyEnv).run 0 := by
  rw [shared_runs_once, repeated_runs_twice]
  change ((0, 1) : Nat × Nat) ≠ (1, 2)
  decide

def ignoredEffect : Term (StateM Nat) Nat [] .atom :=
  .letE (.effect tick) (.lit 42)

theorem unused_binder_still_runs_source :
    (ignoredEffect.eval emptyEnv).run 0 = (42, 1) := rfl

def storedVariable (value : Nat) : Closure Id Nat .atom where
  context := [.atom]
  body := .var .zero
  environment := extend value emptyEnv

/-- Identical open syntax can have different captured meanings. Saving only
the printed body cannot implement closure-preserving evaluation. -/
theorem forgetting_capture_changes_meaning :
    (storedVariable 7).body = (storedVariable 99).body ∧
      (storedVariable 7).run ≠ (storedVariable 99).run := by
  constructor
  · rfl
  · change (7 : Nat) ≠ 99
    decide

def mark (event : String) : StateM (List String) Nat :=
  fun trace => (0, trace ++ [event])

def orderedEffects (first second : String) : Term (StateM (List String)) Nat [] .atom :=
  .letE (.effect (mark first)) (.effect (mark second))

theorem interchanging_effectful_bindings_is_observable :
    ((orderedEffects "A" "B").eval emptyEnv).run [] ≠
      ((orderedEffects "B" "A").eval emptyEnv).run [] := by
  change ((0, ["A", "B"]) : Nat × List String) ≠ (0, ["B", "A"])
  decide

/-- A repeated variable pattern accepts equal coordinates only. -/
def diagonal (pair : Nat × Nat) : List Nat :=
  if pair.1 = pair.2 then [pair.1] else []

theorem relational_matching_is_not_lexical_binding :
    matchBind (M := List) [(1, 2)] diagonal (fun n => [n]) = [] ∧
    ([(1, 2)].flatMap fun pair => [pair.1]) = [1] := by decide

theorem choice_is_selected_once :
    (do let x ← [1, 2]; pure (x, x) : List (Nat × Nat)) = [(1, 1), (2, 2)] := rfl

theorem recomputing_choice_adds_answers :
    (do let x ← [1, 2]; let y ← [1, 2]; pure (x, y) : List (Nat × Nat)) =
      [(1, 1), (1, 2), (2, 1), (2, 2)] := rfl

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.EffectfulLet
