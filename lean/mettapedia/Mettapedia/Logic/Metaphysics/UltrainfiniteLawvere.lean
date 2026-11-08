import Mathlib.Logic.Unique
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Defs

/-!
# Lawvere's fixed-point theorem for types: the diagonal limit

**Lawvere's theorem** (`lawvere_fixedPoint`): if `e : A → (A → B)` is point-surjective, which for
types is surjectivity, every `f : B → B` has a fixed point. With an explicit section `s` of `e`
the fixed point is a term (`diagonalFix`, `diagonalFix_spec`): the self-application of the
diagonal `a ↦ f (e a a)`, the shape of `(λx. f (x x))(λx. f (x x))`. At `f = id` it is the
self-application of `a ↦ e a a` (`diagonalFix_id`), the shape of `Ω = (λx. x x)(λx. x x)`.

**Corollaries.**
* **Cantor** (`not_surjective_prop`, `cantor_surjective`): `¬` has no fixed point in `Prop`, so no
  `A → (A → Prop)` is surjective. Mathlib proves only this case (`Function.cantor_surjective`).
* **A self-containing type inhabits its codomain** (`nonempty_of_surjective`): the fixed point of
  the identity is an element of `B`. This is Curry's paradox read on types.
* **In types, a codomain reached by a point-surjection has at most one element**
  (`subsingleton_of_surjective`), since a type with two distinct elements has an endomap without
  fixed points.
* **The self-containing type is a One** (`unique_of_equiv_arrow`): a type `X` with
  `X ≃ (X → X)` has exactly one element. Control: `PUnit` is such a type (`punitEquivArrow`);
  `Bool` is not (`not_nonempty_bool_equiv_arrow`).
* **No internal truth predicate** (`no_truth_predicate`): there is no `Tr : X → Prop` with a
  substitution `sub : X → X → X` through which every predicate on `X` is defined by a code.

Constructivity: `lawvere_fixedPoint`, `diagonalFix_spec`, `nonempty_of_surjective` and the Cantor
case use no choice; `subsingleton_of_surjective` decides equality classically.

F. W. Lawvere, *Diagonal arguments and cartesian closed categories*, Lecture Notes in
Mathematics 92, 1969; N. Yanofsky, *A universal approach to self-referential paradoxes,
incompleteness and fixed points*, Bulletin of Symbolic Logic 9, 2003.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

universe u v

section Lawvere

variable {A : Sort u} {B : Sort v}

/-- The diagonal fixed point, from a section `s` of `e`: `e` applied to the code of the diagonal
`a ↦ f (e a a)`, at that same code. -/
def diagonalFix (e : A → A → B) (s : (A → B) → A) (f : B → B) : B :=
  e (s fun a => f (e a a)) (s fun a => f (e a a))

/-- **The diagonal fixed point is a fixed point.** -/
theorem diagonalFix_spec (e : A → A → B) (s : (A → B) → A) (section_ : ∀ g, e (s g) = g)
    (f : B → B) : f (diagonalFix e s f) = diagonalFix e s f :=
  (congrFun (section_ fun a => f (e a a)) (s fun a => f (e a a))).symm

/-- At the identity, the diagonal fixed point is the self-application of the code of
`a ↦ e a a`. -/
theorem diagonalFix_id (e : A → A → B) (s : (A → B) → A) :
    diagonalFix e s id = e (s fun a => e a a) (s fun a => e a a) :=
  rfl

/-- **Lawvere's fixed-point theorem** for types. -/
theorem lawvere_fixedPoint (e : A → A → B) (surjective : Function.Surjective e) (f : B → B) :
    ∃ b, f b = b :=
  let ⟨a, coded⟩ := surjective fun a => f (e a a)
  ⟨e a a, (congrFun coded a).symm⟩

/-- A codomain with a fixed-point-free endomap is reached by no point-surjection. -/
theorem not_surjective_of_fixedPointFree (f : B → B) (free : ∀ b, f b ≠ b) (e : A → A → B) :
    ¬ Function.Surjective e := fun surjective =>
  let ⟨b, fixed⟩ := lawvere_fixedPoint e surjective f
  free b fixed

/-- **A self-containing type inhabits its codomain**: the fixed point of the identity. -/
theorem nonempty_of_surjective (e : A → A → B) (surjective : Function.Surjective e) :
    Nonempty B :=
  let ⟨b, _⟩ := lawvere_fixedPoint e surjective id
  ⟨b⟩

/-- **A codomain reached by a point-surjection has at most one element.** -/
theorem subsingleton_of_surjective (e : A → A → B) (surjective : Function.Surjective e) :
    Subsingleton B := by
  classical
  refine ⟨fun b₀ b₁ => ?_⟩
  by_contra apart
  refine not_surjective_of_fixedPointFree (fun b => if b = b₀ then b₁ else b₀) (fun b fixed => ?_)
    e surjective
  by_cases here : b = b₀
  · rw [if_pos here] at fixed
    exact apart (here.symm.trans fixed.symm)
  · rw [if_neg here] at fixed
    exact here fixed.symm

end Lawvere

/-! ## Cantor -/

/-- `¬` has no fixed point in `Prop`. -/
theorem not_fixed_not (p : Prop) : (¬ p) ≠ p := fun same =>
  have np : ¬ p := fun hp => (Eq.mp same.symm hp) hp
  np (Eq.mp same np)

/-- **Cantor**, as the instance `B = Prop`, `f = ¬` of Lawvere's theorem. -/
theorem not_surjective_prop {A : Sort u} (e : A → A → Prop) : ¬ Function.Surjective e :=
  not_surjective_of_fixedPointFree Not not_fixed_not e

/-- Mathlib's `Function.cantor_surjective`, recovered. -/
theorem cantor_surjective {α : Type u} (f : α → Set α) : ¬ Function.Surjective f :=
  not_surjective_prop f

/-- Cantor for `Bool`: no `A → (A → Bool)` is surjective, since `not` has no fixed point. -/
theorem not_surjective_bool {A : Sort u} (e : A → A → Bool) : ¬ Function.Surjective e :=
  not_surjective_of_fixedPointFree not (fun b => by cases b <;> decide) e

/-! ## The self-containing type -/

/-- **The self-containing type is a One**: a type equivalent to its own function space has
exactly one element. -/
theorem unique_of_equiv_arrow {X : Sort u} (e : X ≃ (X → X)) : Nonempty (Unique X) :=
  let ⟨x⟩ := nonempty_of_surjective e e.surjective
  ⟨{ default := x, uniq := fun y => (subsingleton_of_surjective e e.surjective).elim y x }⟩

/-- In particular no such type has two distinct elements. -/
theorem eq_of_equiv_arrow {X : Sort u} (e : X ≃ (X → X)) (x y : X) : x = y :=
  (subsingleton_of_surjective e e.surjective).elim x y

/-- Control: `PUnit` is equivalent to its own function space. -/
def punitEquivArrow : PUnit.{u} ≃ (PUnit.{u} → PUnit.{u}) where
  toFun _ := id
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv _ := funext fun _ => rfl

/-- Control: `Bool` is not. -/
theorem not_nonempty_bool_equiv_arrow : ¬ Nonempty (Bool ≃ (Bool → Bool)) :=
  fun ⟨e⟩ => not_surjective_bool e e.surjective

/-! ## No internal truth predicate -/

/-- **No internal truth predicate**: no `Tr : X → Prop` with a substitution `sub` through which
every predicate on `X` is defined by a code, `Tr (sub c x) ↔ P x`. -/
theorem no_truth_predicate {X : Sort u} (Tr : X → Prop) (sub : X → X → X) :
    ¬ ∀ P : X → Prop, ∃ c, ∀ x, Tr (sub c x) ↔ P x := fun defines =>
  not_surjective_prop (fun c x => Tr (sub c x)) fun P =>
    let ⟨c, same⟩ := defines P
    ⟨c, funext fun x => propext (same x)⟩

end Mettapedia.Logic.Metaphysics.Ultrainfinite

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

#print axioms diagonalFix_spec
#print axioms diagonalFix_id
#print axioms lawvere_fixedPoint
#print axioms not_surjective_of_fixedPointFree
#print axioms nonempty_of_surjective
#print axioms subsingleton_of_surjective
#print axioms not_fixed_not
#print axioms not_surjective_prop
#print axioms cantor_surjective
#print axioms not_surjective_bool
#print axioms unique_of_equiv_arrow
#print axioms eq_of_equiv_arrow
#print axioms punitEquivArrow
#print axioms not_nonempty_bool_equiv_arrow
#print axioms no_truth_predicate

end Mettapedia.Logic.Metaphysics.Ultrainfinite
