import Mettapedia.Languages.Agda.Adequacy.StaticObservation

/-!
# Renaming and substitution of successful observations

All structural actions below are the signature's existing `rename`, `bind`,
and binder lifts. The observation uses the source's existing actions on its
result. Substitution correspondence requires the actual variable images to
have the specified source observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Observation

open Mettapedia.OSLF.Binding
open Structural (sig scope)

def Result.rename {n m : Nat} (ρ : StaticSpecification.Renaming n m) :
    {s : Structural.Srt} → Result n s → Result m s
  | .term => StaticSpecification.Term.rename ρ
  | .type => StaticSpecification.Ty.rename ρ
  | .elim => StaticSpecification.Elim.rename ρ
  | .spine => List.map (StaticSpecification.Elim.rename ρ)
  | .sort | .level => id

private def combine {α β γ : Type} (f : α → β → γ) (a : Option α) (b : Option β) : Option γ := do
  let a ← a
  let b ← b
  pure (f a b)

private theorem unary_natural {α β γ δ : Type} (f : α → β) (g : γ → δ)
    (r : α → γ) (t : β → δ) (a : Option α) (b : Option γ)
    (same : b = a.map r) (commutes : ∀ x, g (r x) = t (f x)) :
    b.map g = (a.map f).map t := by
  rw [same]
  cases a with
  | none => rfl
  | some x => exact congrArg some (commutes x)

private theorem binary_natural {α β γ α' β' γ' : Type}
    (f : α → β → γ) (g : α' → β' → γ')
    (r : α → α') (s : β → β') (t : γ → γ')
    (a : Option α) (b : Option β) (a' : Option α') (b' : Option β')
    (first : a' = a.map r) (second : b' = b.map s)
    (commutes : ∀ x y, g (r x) (s y) = t (f x y)) :
    combine g a' b' = (combine f a b).map t := by
  rw [first, second]
  cases a with
  | none => rfl
  | some x =>
      cases b with
      | none => rfl
      | some y => exact congrArg some (commutes x y)

theorem observe_rename {n m : Nat} {s : Structural.Srt}
    (ρ : StaticSpecification.Renaming n m) (input : Term sig (scope n) s) :
    observe (rename (embedRen ρ) input) = (observe input).map (Result.rename ρ) := by
  match input with
  | .var v =>
      have sort := scope_sort v
      subst s
      rw [← embed_readVar v]
      change some (StaticSpecification.Term.var (readVar (embedRen ρ _ (embedVar (readVar v))))) = _
      rw [embedRen_var, read_embedVar]
      change _ = (some (StaticSpecification.Term.var (readVar (embedVar (readVar v))))).map
        (Result.rename (s := .term) ρ)
      rw [read_embedVar]
      rfl
  | .op .lam (.cons body .nil) =>
      change (term (rename (liftRen (embedRen ρ) [.term]) body)).map
        (fun t => StaticSpecification.Term.lam (.bind t)) = _
      rw [← embedRen_lift]
      exact unary_natural (fun t => .lam (.bind t)) (fun t => .lam (.bind t))
        (StaticSpecification.Term.rename ρ.lift) (StaticSpecification.Term.rename ρ)
        (term body) _ (observe_rename ρ.lift body) (fun _ => rfl)
  | .op .lamNoAbs (.cons body .nil) =>
      exact unary_natural (fun t => .lam (.noBind t)) (fun t => .lam (.noBind t))
        (StaticSpecification.Term.rename ρ) (StaticSpecification.Term.rename ρ)
        (term body) _ (observe_rename ρ body) (fun _ => rfl)
  | .op .pi (.cons domain (.cons body .nil)) =>
      change combine (fun A B => StaticSpecification.Term.pi A (.bind B))
        (type (rename (embedRen ρ) domain))
        (type (rename (liftRen (embedRen ρ) [.term]) body)) = _
      rw [← embedRen_lift]
      exact binary_natural (fun A B => .pi A (.bind B)) (fun A B => .pi A (.bind B))
        (StaticSpecification.Ty.rename ρ) (StaticSpecification.Ty.rename ρ.lift)
        (StaticSpecification.Term.rename ρ) (type domain) (type body) _ _
        (observe_rename ρ domain) (observe_rename ρ.lift body) (fun _ _ => rfl)
  | .op .piNoAbs (.cons domain (.cons body .nil)) =>
      exact binary_natural (fun A B => .pi A (.noBind B)) (fun A B => .pi A (.noBind B))
        (StaticSpecification.Ty.rename ρ) (StaticSpecification.Ty.rename ρ)
        (StaticSpecification.Term.rename ρ) (type domain) (type body) _ _
        (observe_rename ρ domain) (observe_rename ρ body) (fun _ _ => rfl)
  | .op .eliminate (.cons head (.cons es .nil)) =>
      exact binary_natural StaticSpecification.Term.applySpine StaticSpecification.Term.applySpine
        (StaticSpecification.Term.rename ρ) (List.map (StaticSpecification.Elim.rename ρ))
        (StaticSpecification.Term.rename ρ) (term head) (spine es) _ _
        (observe_rename ρ head) (observe_rename ρ es)
        (fun f es => (StaticSpecification.Term.applySpine_rename f es ρ).symm)
  | .op .sortTerm (.cons sort .nil) =>
      exact unary_natural StaticSpecification.Term.sort StaticSpecification.Term.sort id
        (StaticSpecification.Term.rename ρ) (observe sort) _ (observe_rename ρ sort) (fun _ => rfl)
  | .op .el (.cons sort (.cons head .nil)) =>
      exact binary_natural StaticSpecification.Ty.el StaticSpecification.Ty.el id
        (StaticSpecification.Term.rename ρ) (StaticSpecification.Ty.rename ρ)
        (observe sort) (term head) _ _ (observe_rename ρ sort) (observe_rename ρ head) (fun _ _ => rfl)
  | .op .set (.cons level .nil) => exact observe_rename ρ level
  | .op (.levelClosed value) .nil => rfl
  | .op .apply (.cons argument .nil) =>
      exact unary_natural StaticSpecification.Elim.apply StaticSpecification.Elim.apply
        (StaticSpecification.Term.rename ρ) (StaticSpecification.Elim.rename ρ)
        (term argument) _ (observe_rename ρ argument) (fun _ => rfl)
  | .op .nil .nil => rfl
  | .op .cons (.cons head (.cons tail .nil)) =>
      exact binary_natural List.cons List.cons (StaticSpecification.Elim.rename ρ)
        (List.map (StaticSpecification.Elim.rename ρ)) (List.map (StaticSpecification.Elim.rename ρ))
        (elim head) (spine tail) _ _ (observe_rename ρ head) (observe_rename ρ tail) (fun _ _ => rfl)
  | .op .append (.cons first (.cons second .nil)) =>
      exact binary_natural List.append List.append (List.map (StaticSpecification.Elim.rename ρ))
        (List.map (StaticSpecification.Elim.rename ρ)) (List.map (StaticSpecification.Elim.rename ρ))
        (spine first) (spine second) _ _ (observe_rename ρ first) (observe_rename ρ second)
        (fun _ _ => (List.map_append ..).symm)
  | .op (.defined _) _ | .op (.constructor _) _ | .op (.natLiteral _) _
    | .op .levelTerm _ | .op .prop _ | .op (.setOmega _) _ | .op .levelSuc _
    | .op .levelMax _ | .op .levelNeutral _ | .op (.proj _) _ => rfl
termination_by termSize input
decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

def readRen {n m : Nat} (ρ : Ren sig (scope n) (scope m)) : StaticSpecification.Renaming n m :=
  fun i => readVar (ρ .term (embedVar i))

theorem embed_readRen {n m : Nat} (ρ : Ren sig (scope n) (scope m)) :
    embedRen (readRen ρ) = ρ := by
  funext s v
  have sort := scope_sort v
  subst s
  rw [← embed_readVar v, embedRen_var]
  exact embed_readVar _

/-- Every native renaming on an ordinary scope has the corresponding source action. -/
theorem observe_generic_rename {n m : Nat} {s : Structural.Srt}
    (ρ : Ren sig (scope n) (scope m)) (input : Term sig (scope n) s) :
    observe (rename ρ input) = (observe input).map (Result.rename (readRen ρ)) := by
  simpa only [embed_readRen] using observe_rename (readRen ρ) input

theorem observe_weaken {n : Nat} {s : Structural.Srt} (input : Term sig (scope n) s) :
    observe (n := n + 1) (@Mettapedia.OSLF.Binding.weaken sig (scope n) s .term input) =
      (observe input).map (Result.rename Fin.succ) := by
  have comparison := observe_rename (Fin.succ : Fin n → Fin (n + 1)) input
  rw [embedRen_succ] at comparison
  exact comparison

def Result.substitute {n m : Nat} (σ : StaticSpecification.Substitution n m) :
    {s : Structural.Srt} → Result n s → Result m s
  | .term => StaticSpecification.Term.subst σ
  | .type => StaticSpecification.Ty.subst σ
  | .elim => StaticSpecification.Elim.subst σ
  | .spine => List.map (StaticSpecification.Elim.subst σ)
  | .sort | .level => id

/-- Pointwise successful observations of the actual native variable images. -/
def SubObserves {n m : Nat} (σ : Sub sig (scope n) (scope m))
    (τ : StaticSpecification.Substitution n m) : Prop :=
  ∀ i : Fin n, term (σ .term (embedVar i)) = some (τ i)

theorem SubObserves.lift {n m : Nat} {σ : Sub sig (scope n) (scope m)}
    {τ : StaticSpecification.Substitution n m} (images : SubObserves σ τ) :
    SubObserves (n := n + 1) (m := m + 1) (liftSub σ [.term]) τ.lift := by
  intro index
  refine Fin.cases ?_ (fun i => ?_) index
  · rfl
  · change term (n := m + 1)
      (@Mettapedia.OSLF.Binding.weaken sig (scope m) .term .term (σ .term (embedVar i))) =
      some ((τ i).weaken)
    exact (observe_weaken (σ .term (embedVar i))).trans
      (congrArg (Option.map (StaticSpecification.Term.rename Fin.succ)) (images i))

theorem observe_bind {n m : Nat} {s : Structural.Srt}
    {σ : Sub sig (scope n) (scope m)} {τ : StaticSpecification.Substitution n m}
    (images : SubObserves σ τ) (input : Term sig (scope n) s) :
    observe (bind σ input) = (observe input).map (Result.substitute τ) := by
  match input with
  | .var v =>
      have sort := scope_sort v
      subst s
      rw [← embed_readVar v]
      change term (σ .term (embedVar (readVar v))) =
        (some (StaticSpecification.Term.var (readVar (embedVar (readVar v))))).map
          (Result.substitute (s := .term) τ)
      rw [images (readVar v), read_embedVar]
      rfl
  | .op .lam (.cons body .nil) =>
      exact unary_natural (fun t => .lam (.bind t)) (fun t => .lam (.bind t))
        (StaticSpecification.Term.subst τ.lift) (StaticSpecification.Term.subst τ)
        (term body) _ (observe_bind images.lift body) (fun _ => rfl)
  | .op .lamNoAbs (.cons body .nil) =>
      exact unary_natural (fun t => .lam (.noBind t)) (fun t => .lam (.noBind t))
        (StaticSpecification.Term.subst τ) (StaticSpecification.Term.subst τ)
        (term body) _ (observe_bind images body) (fun _ => rfl)
  | .op .pi (.cons domain (.cons body .nil)) =>
      exact binary_natural (fun A B => .pi A (.bind B)) (fun A B => .pi A (.bind B))
        (StaticSpecification.Ty.subst τ) (StaticSpecification.Ty.subst τ.lift)
        (StaticSpecification.Term.subst τ) (type domain) (type body) _ _
        (observe_bind images domain) (observe_bind images.lift body) (fun _ _ => rfl)
  | .op .piNoAbs (.cons domain (.cons body .nil)) =>
      exact binary_natural (fun A B => .pi A (.noBind B)) (fun A B => .pi A (.noBind B))
        (StaticSpecification.Ty.subst τ) (StaticSpecification.Ty.subst τ)
        (StaticSpecification.Term.subst τ) (type domain) (type body) _ _
        (observe_bind images domain) (observe_bind images body) (fun _ _ => rfl)
  | .op .eliminate (.cons head (.cons es .nil)) =>
      exact binary_natural StaticSpecification.Term.applySpine StaticSpecification.Term.applySpine
        (StaticSpecification.Term.subst τ) (List.map (StaticSpecification.Elim.subst τ))
        (StaticSpecification.Term.subst τ) (term head) (spine es) _ _
        (observe_bind images head) (observe_bind images es)
        (fun f es => (StaticSpecification.Term.applySpine_subst f es τ).symm)
  | .op .sortTerm (.cons sort .nil) =>
      exact unary_natural StaticSpecification.Term.sort StaticSpecification.Term.sort id
        (StaticSpecification.Term.subst τ) (observe sort) _ (observe_bind images sort) (fun _ => rfl)
  | .op .el (.cons sort (.cons head .nil)) =>
      exact binary_natural StaticSpecification.Ty.el StaticSpecification.Ty.el id
        (StaticSpecification.Term.subst τ) (StaticSpecification.Ty.subst τ)
        (observe sort) (term head) _ _ (observe_bind images sort) (observe_bind images head) (fun _ _ => rfl)
  | .op .set (.cons level .nil) => exact observe_bind images level
  | .op (.levelClosed value) .nil => rfl
  | .op .apply (.cons argument .nil) =>
      exact unary_natural StaticSpecification.Elim.apply StaticSpecification.Elim.apply
        (StaticSpecification.Term.subst τ) (StaticSpecification.Elim.subst τ)
        (term argument) _ (observe_bind images argument) (fun _ => rfl)
  | .op .nil .nil => rfl
  | .op .cons (.cons head (.cons tail .nil)) =>
      exact binary_natural List.cons List.cons (StaticSpecification.Elim.subst τ)
        (List.map (StaticSpecification.Elim.subst τ)) (List.map (StaticSpecification.Elim.subst τ))
        (elim head) (spine tail) _ _ (observe_bind images head) (observe_bind images tail) (fun _ _ => rfl)
  | .op .append (.cons first (.cons second .nil)) =>
      exact binary_natural List.append List.append (List.map (StaticSpecification.Elim.subst τ))
        (List.map (StaticSpecification.Elim.subst τ)) (List.map (StaticSpecification.Elim.subst τ))
        (spine first) (spine second) _ _ (observe_bind images first) (observe_bind images second)
        (fun _ _ => (List.map_append ..).symm)
  | .op (.defined _) _ | .op (.constructor _) _ | .op (.natLiteral _) _
    | .op .levelTerm _ | .op .prop _ | .op (.setOmega _) _ | .op .levelSuc _
    | .op .levelMax _ | .op .levelNeutral _ | .op (.proj _) _ => rfl
termination_by termSize input
decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

/-- Successful input and variable-image support give an exact successful output. -/
theorem observe_bind_of_some {n m : Nat} {s : Structural.Srt}
    {σ : Sub sig (scope n) (scope m)} {τ : StaticSpecification.Substitution n m}
    (images : SubObserves σ τ) {input : Term sig (scope n) s} {output : Result n s}
    (supported : observe input = some output) :
    observe (bind σ input) = some (Result.substitute τ output) := by
  rw [observe_bind images input, supported]
  rfl

theorem observe_rename_of_some {n m : Nat} {s : Structural.Srt}
    (ρ : Ren sig (scope n) (scope m)) {input : Term sig (scope n) s} {output : Result n s}
    (supported : observe input = some output) :
    observe (rename ρ input) = some (Result.rename (readRen ρ) output) := by
  rw [observe_generic_rename ρ input, supported]
  rfl

end Mettapedia.Languages.Agda.StaticAdequacy.Observation
