import Mettapedia.Languages.Agda.Specification.Syntax
import Mettapedia.Languages.Agda.Structural.Syntax

/-!
# Source-spine embedding into structural terms

The source specification and structural presentation are defined in separate
import components. This module connects their scopes and syntax. Source
neutral heads carry their spines; the structural term explicitly eliminates
that head. Type sort annotations and both abstraction forms are preserved.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Adequacy

open Mettapedia.OSLF.Binding
open Structural (sig scope)

/-- Embed a source index in the homogeneous term-variable scope. -/
def embedVar : {n : Nat} → Fin n → Var (scope n) Structural.Srt.term
  | 0, i => Fin.elim0 i
  | _ + 1, i => Fin.cases .zero (fun j => .succ (embedVar j)) i

def readVar : {n : Nat} → Var (scope n) Structural.Srt.term → Fin n
  | _ + 1, .zero => 0
  | _ + 1, .succ v => (readVar v).succ

@[simp] theorem read_embedVar : ∀ {n : Nat} (i : Fin n), readVar (embedVar i) = i
  | 0, i => Fin.elim0 i
  | _ + 1, i => by
      refine Fin.cases rfl (fun j => ?_) i
      exact congrArg Fin.succ (read_embedVar j)

@[simp] theorem embed_readVar : ∀ {n : Nat} (v : Var (scope n) Structural.Srt.term),
    embedVar (readVar v) = v
  | _ + 1, .zero => rfl
  | _ + 1, .succ v => congrArg Var.succ (embed_readVar v)

/-- Renamings at source scopes act on every structural variable, with the
sort enforced by the variable constructor. -/
def embedRen : {n m : Nat} → Specification.Renaming n m → Ren sig (scope n) (scope m)
  | _ + 1, _, ρ, _, .zero => embedVar (ρ 0)
  | _ + 1, _, ρ, _, .succ v => embedRen (fun i => ρ i.succ) _ v

@[simp] theorem embedRen_var : ∀ {n m : Nat} (ρ : Specification.Renaming n m) (i : Fin n),
    embedRen ρ _ (embedVar i) = embedVar (ρ i)
  | 0, _, _, i => Fin.elim0 i
  | _ + 1, _, ρ, i => by
      refine Fin.cases rfl (fun j => ?_) i
      exact embedRen_var (fun i => ρ i.succ) j

theorem embedRen_lift {n m : Nat} (ρ : Specification.Renaming n m) :
    embedRen (Specification.Renaming.lift ρ) = liftRen (embedRen ρ) [Structural.Srt.term] := by
  funext s v
  cases v with
  | zero => rfl
  | succ v =>
      change embedRen (fun i => (ρ i).succ) s v = Var.succ (embedRen ρ s v)
      induction n with
      | zero => cases v
      | succ n ih =>
          cases v with
          | zero => rfl
          | succ v => exact ih (fun i => ρ i.succ) v

mutual
  def embedTerm : {n : Nat} → Specification.Term n → Structural.Tm (scope n)
    | _, .var i .nil => .var (embedVar i)
    | _, .var i (.cons e es) => Structural.eliminate (.var (embedVar i)) (embedSpine (.cons e es))
    | _, .defn name .nil => Structural.defined name
    | _, .defn name (.cons e es) => Structural.eliminate (Structural.defined name) (embedSpine (.cons e es))
    | _, .con name .nil => Structural.constructor name
    | _, .con name (.cons e es) => Structural.eliminate (Structural.constructor name) (embedSpine (.cons e es))
    | _, .lam (.bind body) => Structural.lam (embedTerm body)
    | _, .lam (.noBind body) => Structural.lamNoAbs (embedTerm body)
    | _, .pi domain (.bind body) => Structural.pi (embedTy domain) (embedTy body)
    | _, .pi domain (.noBind body) => Structural.piNoAbs (embedTy domain) (embedTy body)
    | _, .sort level => Structural.sortTerm (Structural.set (Structural.levelClosed level))
    | _, .level value => Structural.levelTerm (Structural.levelClosed value)

  def embedTy : {n : Nat} → Specification.Ty n → Structural.Ty (scope n)
    | _, .el level term => Structural.el (Structural.set (Structural.levelClosed level)) (embedTerm term)

  def embedSpine : {n : Nat} → Specification.Spine n → Structural.Spine (scope n)
    | _, .nil => Structural.nil
    | _, .cons (.apply term) rest => Structural.cons (Structural.apply (embedTerm term)) (embedSpine rest)
end

mutual
  theorem embedTerm_rename {n m : Nat} (ρ : Specification.Renaming n m) (term : Specification.Term n) :
      embedTerm (term.rename ρ) = rename (embedRen ρ) (embedTerm term) := by
    match term with
    | .var i .nil => exact congrArg Term.var (embedRen_var ρ i).symm
    | .var i (.cons e es) =>
        simp only [Specification.Term.rename, embedTerm]
        change Structural.eliminate (.var (embedVar (ρ i))) (embedSpine ((Specification.Spine.cons e es).rename ρ)) =
          Structural.eliminate (.var (embedRen ρ _ (embedVar i))) (rename (embedRen ρ) (embedSpine (.cons e es)))
        rw [embedRen_var, embedSpine_rename]
    | .defn name .nil | .con name .nil => rfl
    | .defn name (.cons e es) | .con name (.cons e es) =>
        simp only [Specification.Term.rename, embedTerm]
        exact congrArg (fun spine => Structural.eliminate _ spine) (embedSpine_rename ρ (.cons e es))
    | .lam (.bind body) =>
        change Structural.lam (embedTerm (body.rename (Specification.Renaming.lift ρ))) =
          Structural.lam (rename (liftRen (embedRen ρ) [.term]) (embedTerm body))
        rw [embedTerm_rename, embedRen_lift]
        rfl
    | .lam (.noBind body) =>
        exact congrArg Structural.lamNoAbs (embedTerm_rename ρ body)
    | .pi domain (.bind body) =>
        change Structural.pi (embedTy (domain.rename ρ))
            (embedTy (body.rename (Specification.Renaming.lift ρ))) =
          Structural.pi (rename (embedRen ρ) (embedTy domain))
            (rename (liftRen (embedRen ρ) [.term]) (embedTy body))
        rw [embedTy_rename, embedTy_rename, embedRen_lift]
        rfl
    | .pi domain (.noBind body) =>
        exact congrArg₂ Structural.piNoAbs (embedTy_rename ρ domain) (embedTy_rename ρ body)
    | .sort level | .level value => rfl

  theorem embedTy_rename {n m : Nat} (ρ : Specification.Renaming n m) (ty : Specification.Ty n) :
      embedTy (ty.rename ρ) = rename (embedRen ρ) (embedTy ty) := by
    match ty with
    | .el level term => exact congrArg (Structural.el _) (embedTerm_rename ρ term)

  theorem embedSpine_rename {n m : Nat} (ρ : Specification.Renaming n m) (spine : Specification.Spine n) :
      embedSpine (spine.rename ρ) = rename (embedRen ρ) (embedSpine spine) := by
    match spine with
    | .nil => rfl
    | .cons (.apply term) rest =>
        exact congrArg₂ Structural.cons (congrArg Structural.apply (embedTerm_rename ρ term))
          (embedSpine_rename ρ rest)
end


theorem scope_sort : ∀ {n : Nat} {s : Structural.Srt}, Var (scope n) s → s = .term
  | _ + 1, _, .zero => rfl
  | _ + 1, _, .succ v => scope_sort v

theorem embedRen_succ {n : Nat} :
    embedRen (Fin.succ : Fin n → Fin (n + 1)) = fun _ v => Var.succ v := by
  funext s v
  have same := scope_sort v
  subst s
  rw [← embed_readVar v, embedRen_var]
  rfl

/-- A raw structural environment keeps source substitution images intact.
Its computation is connected to hereditary substitution by a path theorem. -/
def embedSub : {n m : Nat} → Specification.Substitution n m → Sub sig (scope n) (scope m)
  | _ + 1, _, σ, _, .zero => embedTerm (σ 0)
  | _ + 1, _, σ, _, .succ v => embedSub (fun i => σ i.succ) _ v

@[simp] theorem embedSub_var : ∀ {n m : Nat} (σ : Specification.Substitution n m) (i : Fin n),
    embedSub σ _ (embedVar i) = embedTerm (σ i)
  | 0, _, _, i => Fin.elim0 i
  | _ + 1, _, σ, i => by
      refine Fin.cases rfl (fun j => ?_) i
      exact embedSub_var (fun i => σ i.succ) j

theorem embedSub_lift {n m : Nat} (σ : Specification.Substitution n m) :
    embedSub (Specification.Substitution.lift σ) = liftSub (embedSub σ) [.term] := by
  funext s v
  cases v with
  | zero => rfl
  | succ v =>
      have same := scope_sort v
      subst s
      rw [← embed_readVar v]
      change embedSub (Specification.Substitution.lift σ) _
          (embedVar (readVar v).succ) =
        rename (fun _ v => Var.succ v) (embedSub σ _ (embedVar (readVar v)))
      rw [embedSub_var, embedSub_var]
      change embedTerm ((σ (readVar v)).rename Fin.succ) = _
      rw [embedTerm_rename, embedRen_succ]
      rfl

theorem embedSub_single {n : Nat} (term : Specification.Term n) :
    embedSub (Specification.Substitution.single term) = extend (embedTerm term) := by
  funext s v
  cases v with
  | zero => rfl
  | succ v =>
      have same := scope_sort v
      subst s
      rw [← embed_readVar v]
      change embedSub (Specification.Substitution.single term) _
          (embedVar (readVar v).succ) = Term.var (embedVar (readVar v))
      rw [embedSub_var]
      rfl

end Mettapedia.Languages.Agda.Adequacy
