import Mettapedia.Languages.Agda.StaticSpecification.Substitution
import Mettapedia.Languages.Agda.Structural.Syntax
import Mettapedia.OSLF.Syntax.BindingTelescope

/-!
# Raw static syntax in the binding signature

The independent finite-Set syntax embeds without evaluating applications.
Each source elimination contributes exactly one explicit singleton spine.
Both abstraction forms and the universe annotation of every type are retained.
Renaming and simultaneous substitution agree with the generic binding action.
This correspondence concerns raw syntax, without asserting formation or typing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy

open Mettapedia.OSLF.Binding
open Structural (sig scope)

/-- Finite positions in the source scope become typed de Bruijn variables. -/
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

theorem scope_sort {n : Nat} {s : Structural.Srt} (v : Var (scope n) s) : s = .term :=
  Telescope.variable_sort (S := sig) (b := Structural.Srt.term) v

/-- Only the environment is translated; renaming terms remains the generic action. -/
def embedRen : {n m : Nat} → StaticSpecification.Renaming n m → Ren sig (scope n) (scope m)
  | _ + 1, _, ρ, _, .zero => embedVar (ρ 0)
  | _ + 1, _, ρ, _, .succ v => embedRen (fun i => ρ i.succ) _ v

@[simp] theorem embedRen_var : ∀ {n m : Nat} (ρ : StaticSpecification.Renaming n m) (i : Fin n),
    embedRen ρ _ (embedVar i) = embedVar (ρ i)
  | 0, _, _, i => Fin.elim0 i
  | _ + 1, _, ρ, i => by
      refine Fin.cases rfl (fun j => ?_) i
      exact embedRen_var (fun i => ρ i.succ) j

theorem embedRen_lift {n m : Nat} (ρ : StaticSpecification.Renaming n m) :
    embedRen (StaticSpecification.Renaming.lift ρ) = liftRen (embedRen ρ) [.term] := by
  funext s v
  cases v with
  | zero => rfl
  | succ v =>
      have same := scope_sort v
      subst s
      rw [← embed_readVar v]
      change embedRen (StaticSpecification.Renaming.lift ρ) _
          (embedVar (readVar v).succ) = Var.succ (embedRen ρ _ (embedVar (readVar v)))
      rw [embedRen_var, embedRen_var]
      rfl

theorem embedRen_succ {n : Nat} :
    embedRen (Fin.succ : Fin n → Fin (n + 1)) = fun _ v => Var.succ v := by
  funext s v
  have same := scope_sort v
  subst s
  rw [← embed_readVar v, embedRen_var]
  rfl

theorem embedRen_id {n : Nat} :
    embedRen (id : Fin n → Fin n) = fun _ v => v := by
  funext s v
  have same := scope_sort v
  subst s
  rw [← embed_readVar v, embedRen_var]
  rfl

theorem embedRen_comp {n m k : Nat} (ρ : StaticSpecification.Renaming n m)
    (τ : StaticSpecification.Renaming m k) :
    embedRen (τ ∘ ρ) = fun s v => embedRen τ s (embedRen ρ s v) := by
  funext s v
  have same := scope_sort v
  subst s
  rw [← embed_readVar v, embedRen_var, embedRen_var, embedRen_var]
  rfl

mutual
  def embedTerm : {n : Nat} → StaticSpecification.Term n → Structural.Tm (scope n)
    | _, .var i => .var (embedVar i)
    | _, .lam (.bind body) => Structural.lam (embedTerm body)
    | _, .lam (.noBind body) => Structural.lamNoAbs (embedTerm body)
    | _, .pi domain (.bind body) => Structural.pi (embedTy domain) (embedTy body)
    | _, .pi domain (.noBind body) => Structural.piNoAbs (embedTy domain) (embedTy body)
    | _, .sort level => Structural.sortTerm (Structural.set (Structural.levelClosed level))
    | _, .elim head elimination =>
        Structural.eliminate (embedTerm head) (Structural.cons (embedElim elimination) Structural.nil)

  def embedTy : {n : Nat} → StaticSpecification.Ty n → Structural.Ty (scope n)
    | _, .el level term => Structural.el (Structural.set (Structural.levelClosed level)) (embedTerm term)

  def embedElim : {n : Nat} → StaticSpecification.Elim n → Structural.Elim (scope n)
    | _, .apply term => Structural.apply (embedTerm term)
end

def embedSpine {n : Nat} : StaticSpecification.Spine n → Structural.Spine (scope n)
  | [] => Structural.nil
  | e :: es => Structural.cons (embedElim e) (embedSpine es)

mutual
  theorem embedTerm_rename {n m : Nat} (ρ : StaticSpecification.Renaming n m)
      (term : StaticSpecification.Term n) :
      embedTerm (term.rename ρ) = rename (embedRen ρ) (embedTerm term) := by
    match term with
    | .var i => exact congrArg Term.var (embedRen_var ρ i).symm
    | .lam (.bind body) =>
        change Structural.lam (embedTerm (body.rename (StaticSpecification.Renaming.lift ρ))) =
          Structural.lam (rename (liftRen (embedRen ρ) [.term]) (embedTerm body))
        rw [embedTerm_rename, embedRen_lift]
        rfl
    | .lam (.noBind body) => exact congrArg Structural.lamNoAbs (embedTerm_rename ρ body)
    | .pi domain (.bind body) =>
        change Structural.pi (embedTy (domain.rename ρ))
            (embedTy (body.rename (StaticSpecification.Renaming.lift ρ))) =
          Structural.pi (rename (embedRen ρ) (embedTy domain))
            (rename (liftRen (embedRen ρ) [.term]) (embedTy body))
        rw [embedTy_rename, embedTy_rename, embedRen_lift]
        rfl
    | .pi domain (.noBind body) =>
        exact congrArg₂ Structural.piNoAbs (embedTy_rename ρ domain) (embedTy_rename ρ body)
    | .sort _ => rfl
    | .elim head elimination =>
        exact congrArg₂ Structural.eliminate (embedTerm_rename ρ head)
          (congrArg (fun e => Structural.cons e Structural.nil) (embedElim_rename ρ elimination))

  theorem embedTy_rename {n m : Nat} (ρ : StaticSpecification.Renaming n m)
      (ty : StaticSpecification.Ty n) :
      embedTy (ty.rename ρ) = rename (embedRen ρ) (embedTy ty) := by
    match ty with
    | .el level term => exact congrArg (Structural.el _) (embedTerm_rename ρ term)

  theorem embedElim_rename {n m : Nat} (ρ : StaticSpecification.Renaming n m)
      (elimination : StaticSpecification.Elim n) :
      embedElim (elimination.rename ρ) = rename (embedRen ρ) (embedElim elimination) := by
    match elimination with
    | .apply term => exact congrArg Structural.apply (embedTerm_rename ρ term)
end

theorem embedSpine_rename {n m : Nat} (ρ : StaticSpecification.Renaming n m)
    (spine : StaticSpecification.Spine n) :
    embedSpine (spine.map (StaticSpecification.Elim.rename ρ)) =
      rename (embedRen ρ) (embedSpine spine) := by
  induction spine with
  | nil => rfl
  | cons e es ih => exact congrArg₂ Structural.cons (embedElim_rename ρ e) ih

theorem embedTerm_weaken {n : Nat} (term : StaticSpecification.Term n) :
    embedTerm term.weaken = rename (fun _ v => Var.succ v) (embedTerm term) := by
  rw [StaticSpecification.Term.weaken, embedTerm_rename, embedRen_succ]
  rfl

theorem embedTy_weaken {n : Nat} (ty : StaticSpecification.Ty n) :
    embedTy ty.weaken = rename (fun _ v => Var.succ v) (embedTy ty) := by
  rw [StaticSpecification.Ty.weaken, embedTy_rename, embedRen_succ]
  rfl

/-- An environment adapter into native simultaneous substitution. -/
def embedSub : {n m : Nat} → StaticSpecification.Substitution n m → Sub sig (scope n) (scope m)
  | _ + 1, _, σ, _, .zero => embedTerm (σ 0)
  | _ + 1, _, σ, _, .succ v => embedSub (fun i => σ i.succ) _ v

@[simp] theorem embedSub_var : ∀ {n m : Nat} (σ : StaticSpecification.Substitution n m) (i : Fin n),
    embedSub σ _ (embedVar i) = embedTerm (σ i)
  | 0, _, _, i => Fin.elim0 i
  | _ + 1, _, σ, i => by
      refine Fin.cases rfl (fun j => ?_) i
      exact embedSub_var (fun i => σ i.succ) j

theorem embedSub_lift {n m : Nat} (σ : StaticSpecification.Substitution n m) :
    embedSub (StaticSpecification.Substitution.lift σ) = liftSub (embedSub σ) [.term] := by
  funext s v
  cases v with
  | zero => rfl
  | succ v =>
      have same := scope_sort v
      subst s
      rw [← embed_readVar v]
      change embedSub (StaticSpecification.Substitution.lift σ) _
          (embedVar (readVar v).succ) =
        rename (fun _ v => Var.succ v) (embedSub σ _ (embedVar (readVar v)))
      rw [embedSub_var, embedSub_var]
      exact embedTerm_weaken (σ (readVar v))

theorem embedSub_single {n : Nat} (term : StaticSpecification.Term n) :
    embedSub (StaticSpecification.Substitution.single term) = extend (embedTerm term) := by
  funext s v
  cases v with
  | zero => rfl
  | succ v =>
      have same := scope_sort v
      subst s
      rw [← embed_readVar v]
      change embedSub (StaticSpecification.Substitution.single term) _
          (embedVar (readVar v).succ) = Term.var (embedVar (readVar v))
      rw [embedSub_var]
      rfl

mutual
  theorem embedTerm_subst {n m : Nat} (σ : StaticSpecification.Substitution n m)
      (term : StaticSpecification.Term n) :
      embedTerm (term.subst σ) = bind (embedSub σ) (embedTerm term) := by
    match term with
    | .var i => exact (embedSub_var σ i).symm
    | .lam (.bind body) =>
        change Structural.lam (embedTerm (body.subst (StaticSpecification.Substitution.lift σ))) =
          Structural.lam (bind (liftSub (embedSub σ) [.term]) (embedTerm body))
        rw [embedTerm_subst, embedSub_lift]
        rfl
    | .lam (.noBind body) => exact congrArg Structural.lamNoAbs (embedTerm_subst σ body)
    | .pi domain (.bind body) =>
        change Structural.pi (embedTy (domain.subst σ))
            (embedTy (body.subst (StaticSpecification.Substitution.lift σ))) =
          Structural.pi (bind (embedSub σ) (embedTy domain))
            (bind (liftSub (embedSub σ) [.term]) (embedTy body))
        rw [embedTy_subst, embedTy_subst, embedSub_lift]
        rfl
    | .pi domain (.noBind body) =>
        exact congrArg₂ Structural.piNoAbs (embedTy_subst σ domain) (embedTy_subst σ body)
    | .sort _ => rfl
    | .elim head elimination =>
        exact congrArg₂ Structural.eliminate (embedTerm_subst σ head)
          (congrArg (fun e => Structural.cons e Structural.nil) (embedElim_subst σ elimination))

  theorem embedTy_subst {n m : Nat} (σ : StaticSpecification.Substitution n m)
      (ty : StaticSpecification.Ty n) :
      embedTy (ty.subst σ) = bind (embedSub σ) (embedTy ty) := by
    match ty with
    | .el level term => exact congrArg (Structural.el _) (embedTerm_subst σ term)

  theorem embedElim_subst {n m : Nat} (σ : StaticSpecification.Substitution n m)
      (elimination : StaticSpecification.Elim n) :
      embedElim (elimination.subst σ) = bind (embedSub σ) (embedElim elimination) := by
    match elimination with
    | .apply term => exact congrArg Structural.apply (embedTerm_subst σ term)
end

theorem embedSpine_subst {n m : Nat} (σ : StaticSpecification.Substitution n m)
    (spine : StaticSpecification.Spine n) :
    embedSpine (spine.map (StaticSpecification.Elim.subst σ)) =
      bind (embedSub σ) (embedSpine spine) := by
  induction spine with
  | nil => rfl
  | cons e es ih => exact congrArg₂ Structural.cons (embedElim_subst σ e) ih

theorem embedSub_id {n : Nat} :
    embedSub (StaticSpecification.Term.var : StaticSpecification.Substitution n n) =
      fun _ v => Term.var v := by
  funext s v
  have same := scope_sort v
  subst s
  rw [← embed_readVar v, embedSub_var]
  rfl

theorem embedSub_comp {n m k : Nat} (σ : StaticSpecification.Substitution n m)
    (τ : StaticSpecification.Substitution m k) :
    embedSub (fun i => (σ i).subst τ) = fun s v => bind (embedSub τ) (embedSub σ s v) := by
  funext s v
  have same := scope_sort v
  subst s
  rw [← embed_readVar v, embedSub_var, embedSub_var]
  exact embedTerm_subst τ (σ (readVar v))

theorem embedTerm_single {n : Nat} (body : StaticSpecification.Term (n + 1))
    (argument : StaticSpecification.Term n) :
    embedTerm (body.subst (StaticSpecification.Substitution.single argument)) =
      inst (embedTerm body) (embedTerm argument) := by
  rw [embedTerm_subst, embedSub_single]
  rfl

theorem embedTy_single {n : Nat} (body : StaticSpecification.Ty (n + 1))
    (argument : StaticSpecification.Term n) :
    embedTy (body.subst (StaticSpecification.Substitution.single argument)) =
      inst (embedTy body) (embedTerm argument) := by
  rw [embedTy_subst, embedSub_single]
  rfl

end Mettapedia.Languages.Agda.StaticAdequacy
