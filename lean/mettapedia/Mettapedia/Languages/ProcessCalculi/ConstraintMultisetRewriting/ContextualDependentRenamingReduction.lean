import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CallAbstraction

/-!
# Executable reduction commutes with renaming

Two partial computations **correspond** along projections when both are unfinished or both
return results with equal projections. Executable results carry derivations whose types mention
their inputs, so commutation with a renaming is stated on what the results compute: a reduct, a
synthesized type, a universe head, or success.

The bounded normalizer commutes with every renaming, at every budget, as soon as its root
evaluator does: a contraction, a congruence position and an unfinished run are all preserved by
renaming, because the strategy never inspects a variable. The root-free evaluator of a rule
package without declared computation commutes trivially.
-/

set_option autoImplicit false

universe u v w

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRenaming

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction

/-! ## Correspondence of partial results -/

/-- **Corresponding partial results**: both unfinished, or both finished with equal projections. -/
def Corr {α : Type u} {β : Type v} {γ : Type w} (f : α → γ) (g : β → γ) (x : Option α) (y : Option β) :
    Prop :=
  x.map f = y.map g

section Corr

variable {α : Type u} {β : Type v} {γ : Type w} {f : α → γ} {g : β → γ}

theorem Corr.cases {x : Option α} {y : Option β} (h : Corr f g x y) :
    (x = none ∧ y = none) ∨ ∃ a b, x = some a ∧ y = some b ∧ f a = g b := by
  cases x <;> cases y <;> simp_all [Corr]

theorem Corr.none_none : Corr f g (none : Option α) (none : Option β) := rfl

theorem Corr.some_some {a : α} {b : β} (h : f a = g b) : Corr f g (some a) (some b) :=
  congrArg some h

theorem Corr.isSome {x : Option α} {y : Option β} (h : Corr f g x y) : x.isSome = y.isSome := by
  rcases h.cases with ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl, _⟩ <;> rfl

theorem Corr.none_iff {x : Option α} {y : Option β} (h : Corr f g x y) : x = none ↔ y = none := by
  rcases h.cases with ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl, _⟩ <;> simp

/-- Equal success of two partial computations splits into the two shared outcomes. -/
theorem isSome_cases {x : Option α} {y : Option β} (h : x.isSome = y.isSome) :
    (x = none ∧ y = none) ∨ ∃ a b, x = some a ∧ y = some b := by
  cases x <;> cases y <;> simp_all

end Corr

/-! ## The bounded normalizer -/

variable {Head : Type} {R : Rules Head}

/-- A root evaluator **commutes with renaming** when it proposes the renamed contraction of a
renamed term, and nothing on a renamed term on which it proposes nothing. -/
def RootRenames (root : RootEvaluator R) : Prop :=
  ∀ {n m : Nat} (ρ : Ren n m) (term : Tm Head n),
    Corr Subtype.val (fun next => rename ρ next.val) (root (rename ρ term)) (root term)

/-- The root-free evaluator commutes with renaming. -/
theorem rootFree_renames : RootRenames (R := R) (fun _ => none) := fun _ _ => rfl

/-- A reduction strategy **commutes with renaming** when, at every budget, the renamed term
reaches the renamed reduct, and is unfinished exactly when the term is. -/
def Renames (reducer : Reducer R) : Prop :=
  ∀ (fuel : Nat) {n m : Nat} (ρ : Ren n m) (term : Tm Head n),
    Corr Subtype.val (fun result => rename ρ result.val) (reducer fuel (rename ρ term)) (reducer fuel term)

variable {root : RootEvaluator R}

private theorem root_cases (renames : RootRenames root) {n m : Nat} (ρ : Ren n m) (term : Tm Head n) :
    (root (rename ρ term) = none ∧ root term = none) ∨
      ∃ a b, root (rename ρ term) = some a ∧ root term = some b ∧ a.val = rename ρ b.val :=
  (renames ρ term).cases

private theorem step_root {n : Nat} {term : Tm Head n} {next : {target : Tm Head n // R.computation.step term target}}
    (proposed : root term = some next) : step R root term = some ⟨next.val, .root next.property⟩ := by
  rw [step.eq_def]
  dsimp only
  rw [proposed]

private theorem step_app {n : Nat} {f a : Tm Head n} (notLam : ∀ body, f ≠ .lam body)
    (quiet : root (.app f a) = none) :
    step R root (.app f a) =
      match step R root f with
      | some next => some ⟨.app next.val a, .congAppFun next.property⟩
      | none => match step R root a with
        | some next => some ⟨.app f next.val, .congAppArg next.property⟩
        | none => none := by
  rw [step.eq_9 R root _ f a notLam, quiet]
  rfl

private theorem step_fst {n : Nat} {p : Tm Head n} (notPair : ∀ x y, p ≠ .pair x y)
    (quiet : root (.fst p) = none) :
    step R root (.fst p) =
      match step R root p with
      | some next => some ⟨.fst next.val, .congFst next.property⟩
      | none => none := by
  rw [step.eq_12 R root _ p notPair, quiet]
  rfl

private theorem step_snd {n : Nat} {p : Tm Head n} (notPair : ∀ x y, p ≠ .pair x y)
    (quiet : root (.snd p) = none) :
    step R root (.snd p) =
      match step R root p with
      | some next => some ⟨.snd next.val, .congSnd next.property⟩
      | none => none := by
  rw [step.eq_14 R root _ p notPair, quiet]
  rfl

/-- **One step commutes with renaming**: the renamed term contracts to the renamed contractum, at
the same position, and is normal exactly when the term is. -/
theorem step_rename (renames : RootRenames root) {n : Nat} (term : Tm Head n) :
    ∀ {m : Nat} (ρ : Ren n m),
      Corr Subtype.val (fun next => rename ρ next.val) (step R root (rename ρ term)) (step R root term) := by
  induction term with
  | var i =>
      intro m ρ
      rcases root_cases renames ρ (.var i) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, same⟩
      · dsimp only [rename] at h₁ ⊢; simp only [step, h₁, h₂]; rfl
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same
  | const c =>
      intro m ρ
      rcases root_cases renames ρ (.const c) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, same⟩
      · dsimp only [rename] at h₁ ⊢; simp only [step, h₁, h₂]; rfl
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same
  | head h =>
      intro m ρ
      rcases root_cases renames ρ (.head h) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, same⟩
      · dsimp only [rename] at h₁ ⊢; simp only [step, h₁, h₂]; rfl
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same
  | pi A B ihA ihB =>
      intro m ρ
      rcases root_cases renames ρ (.pi A B) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, same⟩
      · dsimp only [rename] at h₁ ⊢
        simp only [step, h₁, h₂]
        rcases (ihA ρ).cases with ⟨k₁, k₂⟩ | ⟨a, b, k₁, k₂, same⟩
        · rw [k₁, k₂]
          rcases (ihB (liftRen ρ)).cases with ⟨l₁, l₂⟩ | ⟨c, d, l₁, l₂, same'⟩
          · rw [l₁, l₂]; rfl
          · rw [l₁, l₂]; exact Corr.some_some (by simp only [rename, same'])
        · rw [k₁, k₂]; exact Corr.some_some (by simp only [rename, same])
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same
  | sigma A B ihA ihB =>
      intro m ρ
      rcases root_cases renames ρ (.sigma A B) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, same⟩
      · dsimp only [rename] at h₁ ⊢
        simp only [step, h₁, h₂]
        rcases (ihA ρ).cases with ⟨k₁, k₂⟩ | ⟨a, b, k₁, k₂, same⟩
        · rw [k₁, k₂]
          rcases (ihB (liftRen ρ)).cases with ⟨l₁, l₂⟩ | ⟨c, d, l₁, l₂, same'⟩
          · rw [l₁, l₂]; rfl
          · rw [l₁, l₂]; exact Corr.some_some (by simp only [rename, same'])
        · rw [k₁, k₂]; exact Corr.some_some (by simp only [rename, same])
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same
  | id A x y ihA ihx ihy =>
      intro m ρ
      rcases root_cases renames ρ (.id A x y) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, same⟩
      · dsimp only [rename] at h₁ ⊢
        simp only [step, h₁, h₂]
        rcases (ihA ρ).cases with ⟨k₁, k₂⟩ | ⟨a, b, k₁, k₂, same⟩
        · rw [k₁, k₂]
          rcases (ihx ρ).cases with ⟨l₁, l₂⟩ | ⟨c, d, l₁, l₂, same'⟩
          · rw [l₁, l₂]
            rcases (ihy ρ).cases with ⟨o₁, o₂⟩ | ⟨e, f, o₁, o₂, same''⟩
            · rw [o₁, o₂]; rfl
            · rw [o₁, o₂]; exact Corr.some_some (by simp only [rename, same''])
          · rw [l₁, l₂]; exact Corr.some_some (by simp only [rename, same'])
        · rw [k₁, k₂]; exact Corr.some_some (by simp only [rename, same])
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same
  | lam body ih =>
      intro m ρ
      rcases root_cases renames ρ (.lam body) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, same⟩
      · dsimp only [rename] at h₁ ⊢
        simp only [step, h₁, h₂]
        rcases (ih (liftRen ρ)).cases with ⟨k₁, k₂⟩ | ⟨a, b, k₁, k₂, same⟩
        · rw [k₁, k₂]; rfl
        · rw [k₁, k₂]; exact Corr.some_some (by simp only [rename, same])
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same
  | app f a ihf iha =>
      intro m ρ
      rcases root_cases renames ρ (.app f a) with ⟨h₁, h₂⟩ | ⟨a', b', h₁, h₂, same⟩
      · by_cases isLam : ∃ body, f = .lam body
        · obtain ⟨body, rfl⟩ := isLam
          dsimp only [rename] at h₁ ⊢
          rw [step.eq_8, step.eq_8, h₁, h₂]
          exact Corr.some_some (rename_inst0 ρ a body).symm
        · have notLam : ∀ body, f ≠ .lam body := fun body same => isLam ⟨body, same⟩
          have notLam' : ∀ body, rename ρ f ≠ .lam body := by
            intro body same
            cases f <;> simp only [rename, reduceCtorEq] at same
            exact notLam _ rfl
          dsimp only [rename] at h₁ ⊢
          rw [step_app notLam' h₁, step_app notLam h₂]
          rcases (ihf ρ).cases with ⟨k₁, k₂⟩ | ⟨c, d, k₁, k₂, same'⟩
          · rw [k₁, k₂]
            rcases (iha ρ).cases with ⟨l₁, l₂⟩ | ⟨e, g, l₁, l₂, same''⟩
            · rw [l₁, l₂]; rfl
            · rw [l₁, l₂]; exact Corr.some_some (by simp only [rename, same''])
          · rw [k₁, k₂]; exact Corr.some_some (by simp only [rename, same'])
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same
  | pair x y ihx ihy =>
      intro m ρ
      rcases root_cases renames ρ (.pair x y) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, same⟩
      · dsimp only [rename] at h₁ ⊢
        simp only [step, h₁, h₂]
        rcases (ihx ρ).cases with ⟨k₁, k₂⟩ | ⟨a, b, k₁, k₂, same⟩
        · rw [k₁, k₂]
          rcases (ihy ρ).cases with ⟨l₁, l₂⟩ | ⟨c, d, l₁, l₂, same'⟩
          · rw [l₁, l₂]; rfl
          · rw [l₁, l₂]; exact Corr.some_some (by simp only [rename, same'])
        · rw [k₁, k₂]; exact Corr.some_some (by simp only [rename, same])
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same
  | fst p ih =>
      intro m ρ
      rcases root_cases renames ρ (.fst p) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, same⟩
      · by_cases isPair : ∃ x y, p = .pair x y
        · obtain ⟨x, y, rfl⟩ := isPair
          dsimp only [rename] at h₁ ⊢
          rw [step.eq_11, step.eq_11, h₁, h₂]; rfl
        · have notPair : ∀ x y, p ≠ .pair x y := fun x y same => isPair ⟨x, y, same⟩
          have notPair' : ∀ x y, rename ρ p ≠ .pair x y := by
            intro x y same
            cases p <;> simp only [rename, reduceCtorEq] at same
            exact notPair _ _ rfl
          dsimp only [rename] at h₁ ⊢
          rw [step_fst notPair' h₁, step_fst notPair h₂]
          rcases (ih ρ).cases with ⟨k₁, k₂⟩ | ⟨a, b, k₁, k₂, same⟩
          · rw [k₁, k₂]; rfl
          · rw [k₁, k₂]; exact Corr.some_some (by simp only [rename, same])
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same
  | snd p ih =>
      intro m ρ
      rcases root_cases renames ρ (.snd p) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, same⟩
      · by_cases isPair : ∃ x y, p = .pair x y
        · obtain ⟨x, y, rfl⟩ := isPair
          dsimp only [rename] at h₁ ⊢
          rw [step.eq_13, step.eq_13, h₁, h₂]; rfl
        · have notPair : ∀ x y, p ≠ .pair x y := fun x y same => isPair ⟨x, y, same⟩
          have notPair' : ∀ x y, rename ρ p ≠ .pair x y := by
            intro x y same
            cases p <;> simp only [rename, reduceCtorEq] at same
            exact notPair _ _ rfl
          dsimp only [rename] at h₁ ⊢
          rw [step_snd notPair' h₁, step_snd notPair h₂]
          rcases (ih ρ).cases with ⟨k₁, k₂⟩ | ⟨a, b, k₁, k₂, same⟩
          · rw [k₁, k₂]; rfl
          · rw [k₁, k₂]; exact Corr.some_some (by simp only [rename, same])
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same
  | refl x ih =>
      intro m ρ
      rcases root_cases renames ρ (.refl x) with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, same⟩
      · dsimp only [rename] at h₁ ⊢
        simp only [step, h₁, h₂]
        rcases (ih ρ).cases with ⟨k₁, k₂⟩ | ⟨a, b, k₁, k₂, same⟩
        · rw [k₁, k₂]; rfl
        · rw [k₁, k₂]; exact Corr.some_some (by simp only [rename, same])
      · rw [step_root h₁, step_root h₂]; exact Corr.some_some same

/-- **The bounded normalizer commutes with renaming** at every budget. -/
theorem normalize_renames (renames : RootRenames root) : Renames (normalize R root) := by
  intro fuel
  induction fuel with
  | zero => intro n m ρ term; rfl
  | succ fuel ih =>
      intro n m ρ term
      rcases (step_rename renames term ρ).cases with ⟨h₁, h₂⟩ | ⟨⟨a, pa⟩, ⟨b, pb⟩, h₁, h₂, same⟩
      · simp only [Corr, normalize, h₁, h₂, Option.map_some]
      · dsimp only at same
        subst same
        rcases (ih ρ b).cases with ⟨k₁, k₂⟩ | ⟨⟨c, pc⟩, ⟨d, pd⟩, k₁, k₂, same'⟩
        · simp only [Corr, normalize, h₁, h₂, k₁, k₂, Option.map_none]
        · simp only [Corr, normalize, h₁, h₂, k₁, k₂, Option.map_some]
          exact congrArg some same'

/-- The root-free normalizer commutes with renaming. -/
theorem rootFree_normalize_renames : Renames (normalize R (fun _ => none)) :=
  normalize_renames rootFree_renames

/-- A commuting strategy, split into its two shared outcomes, with the renamed path. -/
theorem Renames.cases {reducer : Reducer R} (renames : Renames reducer) (fuel : Nat) {n m : Nat}
    (ρ : Ren n m) (term : Tm Head n) :
    (reducer fuel (rename ρ term) = none ∧ reducer fuel term = none) ∨
      ∃ (value : Tm Head n) (path : Reduces R term value) (path' : Reduces R (rename ρ term) (rename ρ value)),
        reducer fuel (rename ρ term) = some ⟨rename ρ value, path'⟩ ∧ reducer fuel term = some ⟨value, path⟩ := by
  rcases (renames fuel ρ term).cases with ⟨h₁, h₂⟩ | ⟨⟨a, pa⟩, ⟨b, pb⟩, h₁, h₂, same⟩
  · exact .inl ⟨h₁, h₂⟩
  · dsimp only at same
    subst same
    exact .inr ⟨b, pb, pa, h₁, h₂⟩

/-- **Eventual normal forms commute with renaming**: a normal form the strategy reaches and keeps
at every larger budget is reached and kept, renamed, for the renamed term. -/
theorem Renames.eventually {reducer : Reducer R} (renames : Renames reducer) {n m : Nat} (ρ : Ren n m)
    {term : Tm Head n} {fuel : Nat} {value : Tm Head n}
    (kept : ∀ larger, fuel ≤ larger → (reducer larger term).map Subtype.val = some value) :
    ∀ larger, fuel ≤ larger → (reducer larger (rename ρ term)).map Subtype.val = some (rename ρ value) := by
  intro larger enough
  rw [(renames larger ρ term : _ = _)]
  rcases computed : reducer larger term with _ | ⟨result, path⟩
  · have := kept larger enough
    rw [computed] at this
    cases this
  · have := kept larger enough
    rw [computed] at this
    simp only [Option.map_some, Option.some.injEq] at this ⊢
    rw [this]

end ContextualDependentRenaming
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
