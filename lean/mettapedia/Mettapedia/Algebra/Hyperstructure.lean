import Mathlib.Data.Set.Functor

/-!
# Algebraic Hyperstructures via Mathlib's `Set` Monad

Hyperoperations, hypermagmas, and Kleisli composition for `Set`, built on
Mathlib's `LawfulMonad Set` (`Data.Set.Functor`). The powerset monad laws
are Mathlib's — we only add the hyperstructure-specific content.

## Key Results

- `HyperOp` / `Hypermagma` / `Hypersemigroup` — algebraic hyperstructures
- `hyperassoc_iff_bind` — hyperassociativity = Set-monad bind associativity
- `HyperOp.lift_assoc` — classical associativity lifts to hyperassociativity
- `kleisliAssoc` — Kleisli composition is associative (from `LawfulMonad Set`)

## What Mathlib provides (not reinvented here)

- `Set.monad` — `bind s f = ⋃ i ∈ s, f i` (Mathlib.Data.Set.Functor:99)
- `LawfulMonad Set` — all monad laws proved (Mathlib.Data.Set.Functor:110)
- `Set.bind_def` — `s >>= f = ⋃ i ∈ s, f i`

## References

- Marty (1934): "Sur une généralisation de la notion de groupe"
- Corsini & Leoreanu (2003): "Applications of Hyperstructure Theory"
- Fujita (2025): "Superhypermagma, Lie Superhypergroup"
- Fujita & Smarandache (2026): "Advancing Uncertain Combinatorics"
-/

namespace Mettapedia.Algebra

-- Use Mathlib's Set monad throughout this file
attribute [local instance] Set.monad

universe u

/-! ## §1: Hyperoperation -/

/-- A **hyperoperation** on `α`: a binary operation returning a SET of results.
    Ref: Marty (1934), Corsini & Leoreanu (2003) §1.1 -/
def HyperOp (α : Type u) := α → α → Set α

/-- Lift a classical operation to a hyperoperation via `pure` (singleton). -/
def HyperOp.lift (f : α → α → α) : HyperOp α :=
  fun a b => pure (f a b)

/-- Set extension: apply hyperoperation to all pairs from two sets.
    `A ⋆ B = ⋃ { op a b | a ∈ A, b ∈ B }` -/
def HyperOp.setExtend (op : HyperOp α) (A B : Set α) : Set α :=
  A >>= fun a => B >>= fun b => op a b

/-! ## §2: Hypermagma -/

/-- A **hypermagma**: set + hyperoperation with nonempty images.
    Ref: Fujita (2025) Definition 7 -/
structure Hypermagma (α : Type u) where
  op : HyperOp α
  nonempty_image : ∀ a b : α, (op a b).Nonempty

/-- **Hyperassociativity**: `(a ⋆ b) ⋆ {c} = {a} ⋆ (b ⋆ c)` -/
def HyperOp.isAssociative (op : HyperOp α) : Prop :=
  ∀ a b c : α, op.setExtend (op a b) (pure c) = op.setExtend (pure a) (op b c)

/-- A **hypersemigroup**: hypermagma with associative operation. -/
structure Hypersemigroup (α : Type u) extends Hypermagma α where
  assoc : op.isAssociative

/-! ## §3: Kleisli composition for `Set`

Derived directly from `LawfulMonad Set`. No hand-rolled monad laws. -/

/-- **Kleisli composition** for set-valued functions. -/
def kleisliComp (g : β → Set γ) (f : α → Set β) : α → Set γ :=
  fun a => f a >>= g

infixr:80 " ∘ₖ " => kleisliComp

/-- Kleisli composition is associative.
    Proof: one-line from `LawfulMonad Set`. -/
theorem kleisliAssoc (f : α → Set β) (g : β → Set γ) (h : γ → Set δ) :
    (h ∘ₖ g) ∘ₖ f = h ∘ₖ (g ∘ₖ f) := by
  funext a; show f a >>= (fun b => g b >>= h) = (f a >>= g) >>= h
  rw [bind_assoc]

/-- Left identity: `f ∘ₖ pure = f` -/
theorem kleisliLeftId (f : α → Set β) : f ∘ₖ (pure · : α → Set α) = f := by
  funext a; simp [kleisliComp]

/-- Right identity: `pure ∘ₖ f = f` -/
theorem kleisliRightId (f : α → Set β) : (pure · : β → Set β) ∘ₖ f = f := by
  funext a; simp [kleisliComp]

/-! ## §4: Hyperassociativity ↔ Set-bind associativity -/

/-- Set extension with singleton right = bind. -/
theorem setExtend_pure_right (op : HyperOp α) (a b c : α) :
    op.setExtend (op a b) (pure c) = op a b >>= (op · c) := by
  ext x; simp only [HyperOp.setExtend, Set.bind_def,     Set.mem_iUnion]
  constructor
  · rintro ⟨y, hy, _, rfl, hx⟩; exact ⟨y, hy, hx⟩
  · rintro ⟨y, hy, hx⟩; exact ⟨y, hy, c, rfl, hx⟩

/-- Set extension with singleton left = bind. -/
theorem setExtend_pure_left (op : HyperOp α) (a b c : α) :
    op.setExtend (pure a) (op b c) = op b c >>= (op a ·) := by
  ext x; simp only [HyperOp.setExtend, Set.bind_def,     Set.mem_iUnion]
  constructor
  · rintro ⟨_, rfl, z, hz, hx⟩; exact ⟨z, hz, hx⟩
  · rintro ⟨z, hz, hx⟩; exact ⟨a, rfl, z, hz, hx⟩

/-- **Hyperassociativity ↔ bind associativity.**
    The bridge between classical hypergroup theory and Mathlib's monad. -/
theorem hyperassoc_iff_bind (op : HyperOp α) :
    op.isAssociative ↔
    ∀ a b c : α, (op a b >>= (op · c)) = (op b c >>= (op a ·)) := by
  constructor
  · intro h a b c; rw [← setExtend_pure_right, ← setExtend_pure_left]; exact h a b c
  · intro h a b c; rw [setExtend_pure_right, setExtend_pure_left]; exact h a b c

/-! ## §5: Lifted operations preserve structure -/

/-- Lifting a classical associative operation gives a hyperassociative one. -/
theorem HyperOp.lift_assoc (f : α → α → α)
    (hassoc : ∀ a b c : α, f (f a b) c = f a (f b c)) :
    (HyperOp.lift f).isAssociative := by
  intro a b c
  rw [setExtend_pure_right, setExtend_pure_left]
  ext x; simp only [Set.bind_def, HyperOp.lift,     Set.mem_iUnion]
  constructor
  · rintro ⟨y, rfl, rfl⟩; exact ⟨_, rfl, hassoc a b _⟩
  · rintro ⟨z, rfl, rfl⟩; exact ⟨_, rfl, (hassoc _ b c).symm⟩

/-! ## §6: Interpretation

**MeTTa's nondeterministic evaluation is a hyperoperation.**

Given a space `S`, evaluation has signature `eval_S : Atom → Atom → Set Atom`.
This makes `(Atom, eval_S)` a **hypermagma** parametrized by space.

Sequential nondeterministic evaluation is **Kleisli composition** (`kleisliComp`).
`kleisliAssoc` (from `LawfulMonad Set`) proves it's associative.

`HyperOp.lift` IS Fujita/Smarandache's "hyperization."
`hyperassoc_iff_bind` IS the bridge their papers lack:
hyperassociativity = monad-bind associativity.
Classical associative operations lift to hyperassociative ones (`lift_assoc`).
-/

end Mettapedia.Algebra
