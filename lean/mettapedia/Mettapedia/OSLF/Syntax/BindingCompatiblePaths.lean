import Mettapedia.OSLF.Syntax.BindingCompatibleDerivations
import Mathlib.Combinatorics.Quiver.Path

/-!
# Finite paths of compatible structural computation

Paths retain each reduction occurrence. They do not imply that every
reduction sequence terminates. The constructor lifting visits argument
positions in order, with the argument's binder context retained.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CompatibleDerivations

universe u v w
variable {S : Signature} {R : RootFamily.{u} S}

inductive Path (R : RootFamily.{u} S) :
    {Γ : Ctx S} → {s : S.Srt} → Term S Γ s → Term S Γ s → Type u where
  | refl {Γ s} (term : Term S Γ s) : Path R term term
  | cons {Γ s} {first middle last : Term S Γ s} :
      Step R first middle → Path R middle last → Path R first last

def Path.single {Γ s} {first last : Term S Γ s} (step : Step R first last) :
    Path R first last := .cons step (.refl _)

def Path.trans {Γ s} {first middle last : Term S Γ s}
    (left : Path R first middle) (right : Path R middle last) : Path R first last :=
  match left with
  | .refl _ => right
  | .cons step rest => .cons step (rest.trans right)

theorem Path.trans_refl {Γ s} {first last : Term S Γ s}
    (path : Path R first last) : path.trans (.refl last) = path := by
  induction path with
  | refl _ => rfl
  | cons step _ ih => exact congrArg (Path.cons step) ih

theorem Path.trans_assoc {Γ s} {first second third last : Term S Γ s}
    (left : Path R first second) (middle : Path R second third) (right : Path R third last) :
    (left.trans middle).trans right = left.trans (middle.trans right) := by
  induction left with
  | refl _ => rfl
  | cons step _ ih => exact congrArg (Path.cons step) (ih middle)

/-- The number of compatible steps, independently of the size of each proof. -/
def Path.length {Γ s} {first last : Term S Γ s} : Path R first last → Nat
  | .refl _ => 0
  | .cons _ rest => rest.length + 1

theorem Path.length_trans {Γ s} {first middle last : Term S Γ s}
    (left : Path R first middle) (right : Path R middle last) :
    (left.trans right).length = left.length + right.length := by
  induction left with
  | refl _ => exact (Nat.zero_add _).symm
  | cons _ rest ih =>
      change (rest.trans right).length + 1 = (rest.length + 1) + right.length
      rw [ih]
      omega

/-- Realize an ordered compatible computation in any graph whose edges
interpret the individual compatible steps. -/
def Path.toQuiver {Γ : Ctx S} {s : S.Srt} {V : Type v} [Quiver.{w} V]
    (vertices : Term S Γ s → V)
    (edges : ∀ {a b}, Step R a b → (vertices a ⟶ vertices b))
    {first last : Term S Γ s} (path : Path R first last) :
    Quiver.Path (vertices first) (vertices last) :=
  match path with
  | .refl _ => .nil
  | .cons step rest => (edges step).toPath.comp (rest.toQuiver vertices edges)

theorem Path.toQuiver_length {Γ : Ctx S} {s : S.Srt} {V : Type v} [Quiver.{w} V]
    (vertices : Term S Γ s → V)
    (edges : ∀ {a b}, Step R a b → (vertices a ⟶ vertices b))
    {first last : Term S Γ s} (path : Path R first last) :
    (path.toQuiver vertices edges).length = path.length := by
  induction path with
  | refl _ => rfl
  | cons step rest ih =>
      change ((edges step).toPath.comp (rest.toQuiver vertices edges)).length = rest.length + 1
      rw [Quiver.Path.length_comp, Quiver.Path.length_toPath, ih, Nat.add_comm]

theorem Path.toQuiver_trans {Γ : Ctx S} {s : S.Srt} {V : Type v} [Quiver.{w} V]
    (vertices : Term S Γ s → V)
    (edges : ∀ {a b}, Step R a b → (vertices a ⟶ vertices b))
    {first middle last : Term S Γ s}
    (left : Path R first middle) (right : Path R middle last) :
    (left.trans right).toQuiver vertices edges =
      (left.toQuiver vertices edges).comp (right.toQuiver vertices edges) := by
  induction left with
  | refl _ => exact (Quiver.Path.nil_comp _).symm
  | cons step rest ih =>
      change (edges step).toPath.comp ((rest.trans right).toQuiver vertices edges) = _
      rw [ih, ← Quiver.Path.comp_assoc]
      rfl

/-- Lift a finite computation through a context that preserves each step. -/
def Path.mapContext {Γ Δ : Ctx S} {s t : S.Srt}
    (context : Term S Γ s → Term S Δ t)
    (preserves : ∀ {source target}, Step R source target → Step R (context source) (context target))
    {source target : Term S Γ s} (path : Path R source target) :
    Path R (context source) (context target) :=
  match path with
  | .refl _ => .refl _
  | .cons step rest => .cons (preserves step) (rest.mapContext context preserves)

inductive ArgsPaths (R : RootFamily.{u} S) :
    {Γ : Ctx S} → {arity : List (List S.Srt × S.Srt)} →
      Args S arity Γ → Args S arity Γ → Type u where
  | nil {Γ} : ArgsPaths R (.nil : Args S [] Γ) .nil
  | cons {Γ binders s arity} {a b : Term S (binders ++ Γ) s}
      {as bs : Args S arity Γ} :
      Path R a b → ArgsPaths R as bs → ArgsPaths R (.cons a as) (.cons b bs)

/-- Lift all argument paths through a constructor (or another context
respecting argument steps), in authored argument order. -/
def ArgsPaths.mapContext :
    ∀ {Γ : Ctx S} {arity : List (List S.Srt × S.Srt)}
      {source target : Args S arity Γ}, ArgsPaths R source target →
      {Δ : Ctx S} → {s : S.Srt} →
      (context : Args S arity Γ → Term S Δ s) →
      (∀ {a b}, ArgsStep R a b → Step R (context a) (context b)) →
      Path R (context source) (context target)
  | _, _, _, _, .nil, _, _, _, _ => .refl _
  | _, _, _, _, .cons (as := as) (b := b) head tail, _, _, context, preserves =>
      (head.mapContext (fun a => context (.cons a as))
        (fun step => preserves (.head as step))).trans
      (tail.mapContext (fun bs => context (.cons b bs))
        (fun step => preserves (.tail b step)))

def Path.congr {Γ : Ctx S} {s : S.Srt} (op : S.Op s)
    {source target : Args S (S.arity op) Γ} (arguments : ArgsPaths R source target) :
    Path R (.op op source) (.op op target) :=
  arguments.mapContext (Term.op op) (Step.congr op)

def Path.substitute (rootSubst : RootSubstitution R)
    {Γ Δ : Ctx S} (σ : Sub S Γ Δ) {s : S.Srt}
    {source target : Term S Γ s} (path : Path R source target) :
    Path R (bind σ source) (bind σ target) :=
  path.mapContext (bind σ) (CompatibleDerivations.substitute rootSubst σ)

end Mettapedia.OSLF.Binding.CompatibleDerivations
