import Mettapedia.Languages.LambdaCalculus.NamePassing

/-!
# Persistent environments for the nonrecursive name-passing fragment

Dal Zilio, `A Bisimulation for the Blue Calculus` (INRIA RR-3664, 1999),
Section 2.1 gives the definition rule
`def p = R in E[p] --> def p = R in E[R]`, provided the binders of `E`
capture neither `p` nor free names of `R`. Evaluation contexts exclude
abstractions and stored declaration values.

Here definitions use the existing nonrecursive `Expr.defn`: their value is
scoped outside the newly defined name. `FetchAt` identifies the selected
active occurrence independently of any target execution. Its binder case
weakens both the queried name and the fetched value, making the freshness
condition structural. The retained definition supports further fetches.
The full recursive blue calculus and its locality discipline are separate
from this nonrecursive fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.Environment

open Mettapedia.OSLF.Binding

variable {Srt : Type} {nm : Srt}

theorem rename_weaken {Γ Δ : List Srt}
    (ρ : (s : Srt) → Var Γ s → Var Δ s) (value : Expr nm Γ) :
    NamePassing.rename (liftRen ρ [nm]) (NamePassing.weaken value) =
      NamePassing.weaken (NamePassing.rename ρ value) := by
  unfold NamePassing.weaken
  rw [NamePassing.rename_comp, NamePassing.rename_comp]
  rfl

/-- A selected reference fetch in an active context. The binder case moves
the original reference and its value past a fresh nested definition. -/
inductive FetchAt : {Γ : List Srt} → Var Γ nm → Expr nm Γ →
    Expr nm Γ → Expr nm Γ → Prop where
  | here {Γ} (name : Var Γ nm) (value : Expr nm Γ) :
      FetchAt name value (.var name) value
  | app {Γ} {name : Var Γ nm} {value function function' : Expr nm Γ}
      (argument : Var Γ nm) :
      FetchAt name value function function' →
      FetchAt name value (.app function argument) (.app function' argument)
  | defn {Γ} {name : Var Γ nm} {value : Expr nm Γ}
      (stored : Expr nm Γ) {body body' : Expr nm (nm :: Γ)} :
      FetchAt (.succ name) (NamePassing.weaken value) body body' →
      FetchAt name value (.defn stored body) (.defn stored body')
  | carrier {Γ} {name : Var Γ nm} {value body body' : Expr nm Γ}
      (subject : Var Γ nm) (stored : Expr nm Γ) :
      FetchAt name value body body' →
      FetchAt name value (.carrier subject stored body) (.carrier subject stored body')

/-- Contextual lookup commutes with simultaneous name substitution, including
the scopes of nested definitions. -/
theorem FetchAt.rename {Γ Δ : List Srt}
    (ρ : (s : Srt) → Var Γ s → Var Δ s) {name : Var Γ nm}
    {value source target : Expr nm Γ} (fetch : FetchAt name value source target) :
    FetchAt (ρ _ name) (NamePassing.rename ρ value)
      (NamePassing.rename ρ source) (NamePassing.rename ρ target) := by
  induction fetch generalizing Δ with
  | here name value => exact .here (ρ _ name) (NamePassing.rename ρ value)
  | app argument fetch ih => exact .app (ρ _ argument) (ih ρ)
  | defn stored fetch ih =>
      apply FetchAt.defn (NamePassing.rename ρ stored)
      simpa only [rename_weaken, liftRen] using ih (liftRen ρ [nm])
  | carrier subject stored fetch ih =>
      exact .carrier (ρ _ subject) (NamePassing.rename ρ stored) (ih ρ)

theorem fetch_variable_iff {Γ : List Srt} (name query : Var Γ nm)
    (value target : Expr nm Γ) :
    FetchAt name value (.var query) target ↔ query = name ∧ target = value := by
  constructor
  · intro fetch
    cases fetch
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .here _ _

theorem fetch_distinct_variable {Γ : List Srt} (name query : Var Γ nm)
    (different : query ≠ name) (value target : Expr nm Γ) :
    ¬ FetchAt name value (.var query) target := by
  intro fetch
  exact different ((fetch_variable_iff name query value target).mp fetch).1

theorem fetch_not_under_lambda {Γ : List Srt} (name : Var Γ nm)
    (value : Expr nm Γ) (body : Expr nm (nm :: Γ)) {target : Expr nm Γ} :
    ¬ FetchAt name value (.lam body) target := by
  intro fetch
  cases fetch

/-- Source computation distinguishes beta, one-shot carrier consumption,
and persistent environment reads. These are communication events; structural
scope changes are not counted as extra source communications. -/
inductive Action where
  | beta
  | carrierFetch
  | environmentFetch
  deriving DecidableEq, Repr

inductive Step : Action → {Γ : List Srt} → Expr nm Γ → Expr nm Γ → Prop where
  | beta {Γ} (body : Expr nm (nm :: Γ)) (argument : Var Γ nm) :
      Step .beta (.app (.lam body) argument) (NamePassing.instantiate body argument)
  | carrierFetch {Γ} (name : Var Γ nm) (value : Expr nm Γ)
      {body body' : Expr nm Γ} : FetchAt name value body body' →
      Step .carrierFetch (.carrier name value body) body'
  | environmentFetch {Γ} (value : Expr nm Γ) {body body' : Expr nm (nm :: Γ)} :
      FetchAt .zero (NamePassing.weaken value) body body' →
      Step .environmentFetch (.defn value body) (.defn value body')
  | app {Γ kind} {function function' : Expr nm Γ} (argument : Var Γ nm) :
      Step kind function function' →
      Step kind (.app function argument) (.app function' argument)
  | defn {Γ kind} (value : Expr nm Γ) {body body' : Expr nm (nm :: Γ)} :
      Step kind body body' → Step kind (.defn value body) (.defn value body')
  | carrier {Γ kind} (name : Var Γ nm) (value : Expr nm Γ)
      {body body' : Expr nm Γ} :
      Step kind body body' →
      Step kind (.carrier name value body) (.carrier name value body')

theorem Step.rename {Γ Δ : List Srt}
    (ρ : (s : Srt) → Var Γ s → Var Δ s) {kind : Action}
    {source target : Expr nm Γ} (step : Step kind source target) :
    Step kind (NamePassing.rename ρ source) (NamePassing.rename ρ target) := by
  induction step generalizing Δ with
  | beta body argument =>
      simpa only [NamePassing.rename, NamePassing.instantiate_rename] using
        Step.beta (NamePassing.rename (liftRen ρ [nm]) body) (ρ _ argument)
  | carrierFetch name value fetch =>
      exact .carrierFetch (ρ _ name) (NamePassing.rename ρ value) (fetch.rename ρ)
  | environmentFetch value fetch =>
      apply Step.environmentFetch (NamePassing.rename ρ value)
      simpa only [rename_weaken, liftRen] using fetch.rename (liftRen ρ [nm])
  | app argument step ih => exact .app (ρ _ argument) (ih ρ)
  | defn value step ih => exact .defn (NamePassing.rename ρ value) (ih (liftRen ρ [nm]))
  | carrier name value step ih =>
      exact .carrier (ρ _ name) (NamePassing.rename ρ value) (ih ρ)

/-- The previous abridged head semantics is a subrelation of this extension. -/
theorem headStep_included {Γ : List Srt} {source target : Expr nm Γ}
    (step : NamePassing.HeadStep source target) : ∃ kind, Step kind source target := by
  induction step with
  | root step =>
      cases step with
      | beta body argument => exact ⟨.beta, .beta body argument⟩
      | fetch name => exact ⟨.carrierFetch, .carrierFetch name _ (.here name _)⟩
  | app argument step ih =>
      obtain ⟨kind, firing⟩ := ih
      exact ⟨kind, .app argument firing⟩
  | defn value step ih =>
      obtain ⟨kind, firing⟩ := ih
      exact ⟨kind, .defn value firing⟩
  | carrier name value step ih =>
      obtain ⟨kind, firing⟩ := ih
      exact ⟨kind, .carrier name value firing⟩

/-- Fetching releases the value but retains its definition. -/
theorem definition_fetch {Γ : List Srt} (value : Expr nm Γ) :
    Step .environmentFetch (.defn value (.var .zero))
      (.defn value (NamePassing.weaken value)) :=
  .environmentFetch value (.here .zero (NamePassing.weaken value))

theorem variable_no_step {Γ : List Srt} (name : Var Γ nm) {kind : Action}
    {target : Expr nm Γ} : ¬ Step kind (.var name) target := by
  intro step
  cases step

theorem lambda_no_step {Γ : List Srt} (body : Expr nm (nm :: Γ)) {kind : Action}
    {target : Expr nm Γ} : ¬ Step kind (.lam body) target := by
  intro step
  cases step

end Mettapedia.Languages.LambdaCalculus.NamePassing.Environment
