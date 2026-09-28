import Mathlib.Data.Fin.Basic

/-!
# Raw syntax for finite-Set relevant Pi statics

The raw `elim` constructor and the left-to-right application of elimination lists
follow `TApp`, `EArg`, and `applyElims` in Cockx's Agda Core, `Syntax.agda`, commit
`2fb9574e78326ec532dcb2af8272631c765e947d`. Consequently beta redexes remain
syntax: applying a lambda here does not evaluate it.

The separate `Abs`/`NoAbs` scopes and the sort annotations `El Sort Term` on Pi
types follow Agda 2.8.0.2, `Agda.Syntax.Internal`, commit
`cccf42fa88eae25ccbe2623f489021d2075f6f73`. Bound names and argument information
are erased; all arguments are explicit and relevant. Only closed finite Set
levels, variables, Pi, lambda, and ordinary application are supported. There are
no signatures, declarations, constructors, level expressions, metas, records,
irrelevance, cubical operations, or cumulativity in this fragment.

This raw syntax is separate from beta-normal internal terms. It does not assert
that Agda's internal `Term` datatype stores general beta redexes. No authored
presentation or operational specification is imported.
-/

namespace Mettapedia.Languages.Agda.StaticSpecification

abbrev Renaming (n m : Nat) := Fin n → Fin m

namespace Renaming

def lift (ρ : Renaming n m) : Renaming (n + 1) (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

@[simp] theorem lift_zero (ρ : Renaming n m) : lift ρ 0 = 0 := rfl
@[simp] theorem lift_succ (ρ : Renaming n m) (i : Fin n) :
    lift ρ i.succ = (ρ i).succ := rfl

@[simp] theorem lift_id : lift (id : Renaming n n) = id := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem lift_comp (ρ : Renaming n m) (τ : Renaming m k) :
    lift (τ ∘ ρ) = lift τ ∘ lift ρ := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

end Renaming

mutual
  inductive Term : Nat → Type
    | var {n} (index : Fin n) : Term n
    | lam {n} (body : Abs n) : Term n
    | pi {n} (domain : Ty n) (codomain : TyAbs n) : Term n
    | sort {n} (level : Nat) : Term n
    | elim {n} (head : Term n) (elimination : Elim n) : Term n

  inductive Abs : Nat → Type
    | bind {n} (body : Term (n + 1)) : Abs n
    | noBind {n} (body : Term n) : Abs n

  inductive Ty : Nat → Type
    | el {n} (level : Nat) (term : Term n) : Ty n

  inductive TyAbs : Nat → Type
    | bind {n} (body : Ty (n + 1)) : TyAbs n
    | noBind {n} (body : Ty n) : TyAbs n

  inductive Elim : Nat → Type
    | apply {n} (argument : Term n) : Elim n
end

abbrev Spine (n : Nat) := List (Elim n)

def Term.app (f a : Term n) : Term n := .elim f (.apply a)

/-- Cockx's `applyElims`: store every elimination in its original order. -/
def Term.applySpine (f : Term n) : Spine n → Term n
  | [] => f
  | e :: es => (Term.elim f e).applySpine es

theorem Term.applySpine_append (f : Term n) (es fs : Spine n) :
    f.applySpine (es ++ fs) = (f.applySpine es).applySpine fs := by
  induction es generalizing f with
  | nil => rfl
  | cons e es ih => exact ih (.elim f e)

def Ty.level : Ty n → Nat | .el k _ => k
def Ty.term : Ty n → Term n | .el _ t => t
def TyAbs.level : TyAbs n → Nat
  | .bind a => a.level
  | .noBind a => a.level

/-- The type of a term inhabiting `Set k`; compare Cockx's `sortType`. -/
def Ty.universe (k : Nat) : Ty n := .el (k + 1) (.sort k)

/-- The sort of a relevant Pi is the maximum of the finite domain/codomain sorts. -/
def Ty.pi (a : Ty n) (b : TyAbs n) : Ty n :=
  .el (max a.level b.level) (.pi a b)

mutual
  def Term.rename (ρ : Renaming n m) : Term n → Term m
    | .var i => .var (ρ i)
    | .lam b => .lam (b.rename ρ)
    | .pi a b => .pi (a.rename ρ) (b.rename ρ)
    | .sort k => .sort k
    | .elim f e => .elim (f.rename ρ) (e.rename ρ)

  def Abs.rename (ρ : Renaming n m) : Abs n → Abs m
    | .bind t => .bind (t.rename (Renaming.lift ρ))
    | .noBind t => .noBind (t.rename ρ)

  def Ty.rename (ρ : Renaming n m) : Ty n → Ty m
    | .el k t => .el k (t.rename ρ)

  def TyAbs.rename (ρ : Renaming n m) : TyAbs n → TyAbs m
    | .bind a => .bind (a.rename (Renaming.lift ρ))
    | .noBind a => .noBind (a.rename ρ)

  def Elim.rename (ρ : Renaming n m) : Elim n → Elim m
    | .apply t => .apply (t.rename ρ)
end

def Term.weaken (t : Term n) : Term (n + 1) := t.rename Fin.succ
def Ty.weaken (a : Ty n) : Ty (n + 1) := a.rename Fin.succ

/-- Open a non-binding abstraction by weakening, without introducing capture. -/
def Abs.open : Abs n → Term (n + 1)
  | .bind t => t
  | .noBind t => t.weaken

def TyAbs.open : TyAbs n → Ty (n + 1)
  | .bind a => a
  | .noBind a => a.weaken

@[simp] theorem Ty.level_rename (a : Ty n) (ρ : Renaming n m) :
    (a.rename ρ).level = a.level := by cases a; rfl

@[simp] theorem TyAbs.level_rename (b : TyAbs n) (ρ : Renaming n m) :
    (b.rename ρ).level = b.level := by cases b <;> simp [rename, level]

@[simp] theorem TyAbs.level_open (b : TyAbs n) : b.open.level = b.level := by
  cases b <;> simp [TyAbs.open, level, Ty.weaken]

@[simp] theorem Ty.universe_rename (k : Nat) (ρ : Renaming n m) :
    (Ty.universe k).rename ρ = Ty.universe k := rfl

@[simp] theorem Ty.pi_rename (a : Ty n) (b : TyAbs n) (ρ : Renaming n m) :
    (pi a b).rename ρ = pi (a.rename ρ) (b.rename ρ) := by
  simp [pi, rename, Term.rename]

end Mettapedia.Languages.Agda.StaticSpecification
