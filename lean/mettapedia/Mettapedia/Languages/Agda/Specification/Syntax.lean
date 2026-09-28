import Mathlib.Data.Fin.Basic

/-!
# The closed-level, application-only Agda spine fragment

This syntax is an independent transcription of the `Var`, `Def`, `Con`, `Lam`,
`Pi`, `Sort`, `Level`, `Abs`, and `NoAbs` shapes in Agda 2.8.0.2, commit
`cccf42fa88eae25ccbe2623f489021d2075f6f73`, `Agda.Syntax.Internal`, and the
`Apply` shape in `Agda.Syntax.Internal.Elim`.

The fragment has relevant explicit arguments, ordinary non-projection constants,
data constructors, and closed finite `Set` levels. Argument information and names of bound variables are erased. The `El` sort
annotations on Pi domains and codomains are retained. It has no definition
unfolding, record projections, interval applications, metas, or irrelevance.
`Pi` is syntax here; this module does not claim a typing or conversion judgment.

Variables are finite de Bruijn indices. Both binding and non-binding abstractions
are retained. Eliminations occur only in variable, definition, and constructor
spines, so there is no general application constructor and no syntactic beta
redex. Hereditary substitution consequently belongs to the operational judgment,
not a claimed total operation on arbitrary untyped syntax.

The independent scope precedent is Cockx's Agda Core, `Syntax.agda` at commit
`2fb9574e78326ec532dcb2af8272631c765e947d`, and `Definition.Untyped` of
`mr-ohman/logrel-mltt` at `9d6e290064962a1987c9e1a131c2fb967d6ef928`.
Those are references for scope discipline, not an assertion that their larger
languages or metatheorems have been represented here.
-/

namespace Mettapedia.Languages.Agda.Specification

abbrev Renaming (n m : Nat) := Fin n → Fin m

namespace Renaming

/-- A fresh index is fixed; older indices follow the original renaming. -/
def lift (ρ : Renaming n m) : Renaming (n + 1) (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

@[simp] theorem lift_zero (ρ : Renaming n m) : lift ρ 0 = 0 := rfl

@[simp] theorem lift_succ (ρ : Renaming n m) (i : Fin n) :
    lift ρ i.succ = (ρ i).succ := rfl

@[simp] theorem lift_id : lift (id : Renaming n n) = id := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem lift_comp (ρ : Renaming n m) (τ : Renaming m k) :
    lift (τ ∘ ρ) = lift τ ∘ lift ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end Renaming

mutual
  /-- Beta-normal, well-scoped terms in the stated application-only fragment. -/
  inductive Term : Nat → Type
    | var {n} (index : Fin n) (spine : Spine n) : Term n
    | defn {n} (name : String) (spine : Spine n) : Term n
    | con {n} (name : String) (spine : Spine n) : Term n
    | lam {n} (body : Abs n) : Term n
    | pi {n} (domain : Ty n) (codomain : TyAbs n) : Term n
    | sort {n} (level : Nat) : Term n
    | level {n} (value : Nat) : Term n

  /-- `bind` represents Agda's `Abs`; `noBind` represents `NoAbs`. -/
  inductive Abs : Nat → Type
    | bind {n} (body : Term (n + 1)) : Abs n
    | noBind {n} (body : Term n) : Abs n

  /-- Agda's `Type = El Sort Term`, restricted to closed finite `Set` sorts. -/
  inductive Ty : Nat → Type
    | el {n} (sortLevel : Nat) (term : Term n) : Ty n

  /-- An `Abs Type`, keeping the scope distinction of `Abs` and `NoAbs`. -/
  inductive TyAbs : Nat → Type
    | bind {n} (body : Ty (n + 1)) : TyAbs n
    | noBind {n} (body : Ty n) : TyAbs n

  /-- The ordinary `Apply` elimination, with explicit relevant arguments. -/
  inductive Elim : Nat → Type
    | apply {n} (argument : Term n) : Elim n

  /-- Agda's eliminations are stored in application order, from left to right. -/
  inductive Spine : Nat → Type
    | nil {n} : Spine n
    | cons {n} (head : Elim n) (tail : Spine n) : Spine n
end

namespace Spine

def append : Spine n → Spine n → Spine n
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (append xs ys)

@[simp] theorem nil_append (ys : Spine n) : append .nil ys = ys := rfl

@[simp] theorem cons_append (x : Elim n) (xs ys : Spine n) :
    append (.cons x xs) ys = .cons x (append xs ys) := rfl

@[simp] theorem append_nil (xs : Spine n) : append xs .nil = xs := by
  match xs with
  | .nil => rfl
  | .cons x xs => exact congrArg (Spine.cons x) (append_nil xs)

theorem append_assoc (xs ys zs : Spine n) :
    append (append xs ys) zs = append xs (append ys zs) := by
  match xs with
  | .nil => rfl
  | .cons x xs => exact congrArg (Spine.cons x) (append_assoc xs ys zs)

def singleton (t : Term n) : Spine n := .cons (.apply t) .nil

end Spine

mutual
  def Term.rename (ρ : Renaming n m) : Term n → Term m
    | .var i es => .var (ρ i) (es.rename ρ)
    | .defn f es => .defn f (es.rename ρ)
    | .con c es => .con c (es.rename ρ)
    | .lam b => .lam (b.rename ρ)
    | .pi a b => .pi (a.rename ρ) (b.rename ρ)
    | .sort l => .sort l
    | .level l => .level l

  def Abs.rename (ρ : Renaming n m) : Abs n → Abs m
    | .bind t => .bind (t.rename (Renaming.lift ρ))
    | .noBind t => .noBind (t.rename ρ)

  def Ty.rename (ρ : Renaming n m) : Ty n → Ty m
    | .el l t => .el l (t.rename ρ)

  def TyAbs.rename (ρ : Renaming n m) : TyAbs n → TyAbs m
    | .bind t => .bind (t.rename (Renaming.lift ρ))
    | .noBind t => .noBind (t.rename ρ)

  def Elim.rename (ρ : Renaming n m) : Elim n → Elim m
    | .apply t => .apply (t.rename ρ)

  def Spine.rename (ρ : Renaming n m) : Spine n → Spine m
    | .nil => .nil
    | .cons e es => .cons (e.rename ρ) (es.rename ρ)
end

mutual
  @[simp] theorem Term.rename_id (t : Term n) : t.rename id = t := by
    match t with
    | .var i es => exact congrArg (Term.var i) (Spine.rename_id es)
    | .defn f es => exact congrArg (Term.defn f) (Spine.rename_id es)
    | .con c es => exact congrArg (Term.con c) (Spine.rename_id es)
    | .lam b => exact congrArg Term.lam (Abs.rename_id b)
    | .pi a b => exact congrArg₂ Term.pi (Ty.rename_id a) (TyAbs.rename_id b)
    | .sort l => rfl
    | .level l => rfl

  @[simp] theorem Abs.rename_id (b : Abs n) : b.rename id = b := by
    match b with
    | .bind t =>
      simp only [Abs.rename, Renaming.lift_id]
      exact congrArg Abs.bind (Term.rename_id t)
    | .noBind t => exact congrArg Abs.noBind (Term.rename_id t)

  @[simp] theorem Ty.rename_id (a : Ty n) : a.rename id = a := by
    match a with
    | .el l t => exact congrArg (Ty.el l) (Term.rename_id t)

  @[simp] theorem TyAbs.rename_id (b : TyAbs n) : b.rename id = b := by
    match b with
    | .bind t =>
      simp only [TyAbs.rename, Renaming.lift_id]
      exact congrArg TyAbs.bind (Ty.rename_id t)
    | .noBind t => exact congrArg TyAbs.noBind (Ty.rename_id t)

  @[simp] theorem Elim.rename_id (e : Elim n) : e.rename id = e := by
    match e with
    | .apply t => exact congrArg Elim.apply (Term.rename_id t)

  @[simp] theorem Spine.rename_id (es : Spine n) : es.rename id = es := by
    match es with
    | .nil => rfl
    | .cons e es => exact congrArg₂ Spine.cons (Elim.rename_id e) (Spine.rename_id es)
end

mutual
  theorem Term.rename_comp (t : Term n) (ρ : Renaming n m) (τ : Renaming m k) :
      (t.rename ρ).rename τ = t.rename (τ ∘ ρ) := by
    match t with
    | .var i es => exact congrArg (Term.var (τ (ρ i))) (Spine.rename_comp es ρ τ)
    | .defn f es => exact congrArg (Term.defn f) (Spine.rename_comp es ρ τ)
    | .con c es => exact congrArg (Term.con c) (Spine.rename_comp es ρ τ)
    | .lam b => exact congrArg Term.lam (Abs.rename_comp b ρ τ)
    | .pi a b => exact congrArg₂ Term.pi (Ty.rename_comp a ρ τ) (TyAbs.rename_comp b ρ τ)
    | .sort l => rfl
    | .level l => rfl

  theorem Abs.rename_comp (b : Abs n) (ρ : Renaming n m) (τ : Renaming m k) :
      (b.rename ρ).rename τ = b.rename (τ ∘ ρ) := by
    match b with
    | .bind t =>
      simp only [Abs.rename, Renaming.lift_comp]
      exact congrArg Abs.bind (Term.rename_comp t (Renaming.lift ρ) (Renaming.lift τ))
    | .noBind t => exact congrArg Abs.noBind (Term.rename_comp t ρ τ)

  theorem Ty.rename_comp (a : Ty n) (ρ : Renaming n m) (τ : Renaming m k) :
      (a.rename ρ).rename τ = a.rename (τ ∘ ρ) := by
    match a with
    | .el l t => exact congrArg (Ty.el l) (Term.rename_comp t ρ τ)

  theorem TyAbs.rename_comp (b : TyAbs n) (ρ : Renaming n m) (τ : Renaming m k) :
      (b.rename ρ).rename τ = b.rename (τ ∘ ρ) := by
    match b with
    | .bind t =>
      simp only [TyAbs.rename, Renaming.lift_comp]
      exact congrArg TyAbs.bind (Ty.rename_comp t (Renaming.lift ρ) (Renaming.lift τ))
    | .noBind t => exact congrArg TyAbs.noBind (Ty.rename_comp t ρ τ)

  theorem Elim.rename_comp (e : Elim n) (ρ : Renaming n m) (τ : Renaming m k) :
      (e.rename ρ).rename τ = e.rename (τ ∘ ρ) := by
    match e with
    | .apply t => exact congrArg Elim.apply (Term.rename_comp t ρ τ)

  theorem Spine.rename_comp (es : Spine n) (ρ : Renaming n m) (τ : Renaming m k) :
      (es.rename ρ).rename τ = es.rename (τ ∘ ρ) := by
    match es with
    | .nil => rfl
    | .cons e es =>
      exact congrArg₂ Spine.cons (Elim.rename_comp e ρ τ) (Spine.rename_comp es ρ τ)
end

theorem Spine.rename_append (xs ys : Spine n) (ρ : Renaming n m) :
    (xs.append ys).rename ρ = (xs.rename ρ).append (ys.rename ρ) := by
  match xs with
  | .nil => rfl
  | .cons x xs => exact congrArg (Spine.cons (x.rename ρ)) (Spine.rename_append xs ys ρ)

/-- A variable with no eliminations. -/
def Term.bvar (i : Fin n) : Term n := .var i .nil

/-- Weakening shifts all free variables beneath one fresh binder. -/
def Term.weaken (t : Term n) : Term (n + 1) := t.rename Fin.succ

abbrev Substitution (n m : Nat) := Fin n → Term m

namespace Substitution

def identity : Substitution n n := Term.bvar

/-- Capture avoidance: the new variable is kept, old images are weakened. -/
def lift (σ : Substitution n m) : Substitution (n + 1) (m + 1) :=
  Fin.cases (Term.bvar 0) (fun i => (σ i).weaken)

/-- Replace de Bruijn zero and lower the older indices. -/
def single (t : Term n) : Substitution (n + 1) n :=
  Fin.cases t Term.bvar

@[simp] theorem lift_zero (σ : Substitution n m) : lift σ 0 = Term.bvar 0 := rfl

@[simp] theorem lift_succ (σ : Substitution n m) (i : Fin n) :
    lift σ i.succ = (σ i).weaken := rfl

@[simp] theorem single_zero (t : Term n) : single t 0 = t := rfl

@[simp] theorem single_succ (t : Term n) (i : Fin n) :
    single t i.succ = Term.bvar i := rfl

@[simp] theorem lift_identity : lift (identity : Substitution n n) = identity := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end Substitution

end Mettapedia.Languages.Agda.Specification
