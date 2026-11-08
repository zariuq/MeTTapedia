import Mathlib.Order.FixedPoints
import Mathlib.Order.Hom.Set

/-!
# Approximation fixpoint theory

The algebra of Denecker, Marek and Truszczyński ("Approximations, stable
operators, well-founded fixpoints and applications in nonmonotonic reasoning",
2000), in Mathlib's lattice language.

## The bilattice of approximations

Over a complete lattice `L`, an approximation is a pair `(x, y)`: a lower bound
`x` and an upper bound `y`. Pairs are ordered by **precision**, `(x, y) ≤ (x', y')`
when `x ≤ x'` and `y' ≤ y`. This is the product order on `L × Lᵒᵈ`
(`Approx L`), so it is a complete lattice with no further work. A pair is
**exact** when `x = y` and **consistent** when `x ≤ y`.

## Operators

An **approximating operator** is a precision-monotone `A : Approx L →o Approx L`;
it approximates `O : L → L` when it agrees with `O` on exact pairs
(`Approximates`). Its lower component is monotone in the lower bound and
antitone in the upper one (`lowerOp`, `lowerOp_anti`); dually for the upper
component (`upperOp`, `upperOp_anti`).

* The **stable operator** (`stableOp`) revises a pair `(x, y)` to
  `(lfp A(·, y).lower, lfp A(x, ·).upper)`. It is precision-monotone.
* The **Kripke–Kleene fixpoint** is the least precise fixpoint of `A`
  (`kripkeKleene`); the **well-founded fixpoint** is the least precise fixpoint of
  the stable operator (`wellFounded`).
* Stable fixpoints are fixpoints of `A` (`IsStableFixpoint.isFixed`), so the
  Kripke–Kleene fixpoint is less precise than the well-founded one
  (`kripkeKleene_le_wellFounded`), and the well-founded fixpoint is less precise
  than every stable fixpoint (`wellFounded_le`). An exact stable fixpoint is a
  fixed point of the approximated operator (`IsStableFixpoint.exact_fixed`). An
  exact well-founded fixpoint is the only exact stable fixpoint
  (`exact_stable_iff_of_wellFounded_eq`).

## Symmetric operators

An approximator is **symmetric** when its upper component is its lower component
with the arguments exchanged. Then the stable operator is
`(x, y) ↦ (C y, C x)` for one antitone operator `C` (`stableUpper_eq`), the
exchange of the two bounds (`swap`, antitone) commutes with both operators
(`map_swap`, `stableOp_swap`), and hence both least fixpoints are consistent
(`kripkeKleene_consistent`, `wellFounded_consistent`).

`OrderIso.lfp_conj` transports least fixed points along an order isomorphism.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.AFT

open OrderDual

/-- Least fixed points are carried by an order isomorphism that intertwines the operators. -/
theorem OrderIso.lfp_conj {α β : Type*} [CompleteLattice α] [CompleteLattice β] (e : α ≃o β)
    (f : α →o α) (g : β →o β) (intertwines : ∀ x, g (e x) = e (f x)) : g.lfp = e f.lfp := by
  apply le_antisymm
  · exact OrderHom.lfp_le_fixed _ (by rw [intertwines, OrderHom.map_lfp])
  · rw [← e.le_symm_apply]
    apply OrderHom.lfp_le_fixed
    apply e.injective
    rw [← intertwines, e.apply_symm_apply, OrderHom.map_lfp]

/-- Approximations of `L`: lower and upper bounds, ordered by precision. -/
abbrev Approx (L : Type*) := L × Lᵒᵈ

namespace Approx

variable {L : Type*}

/-- The pair with lower bound `x` and upper bound `y`. -/
def mk (x y : L) : Approx L := (x, toDual y)

/-- The lower bound. -/
def lower (p : Approx L) : L := p.1

/-- The upper bound. -/
def upper (p : Approx L) : L := ofDual p.2

@[simp] theorem lower_mk (x y : L) : (mk x y).lower = x := rfl
@[simp] theorem upper_mk (x y : L) : (mk x y).upper = y := rfl
@[simp] theorem mk_lower_upper (p : Approx L) : mk p.lower p.upper = p := rfl

theorem ext {p q : Approx L} (lower : p.lower = q.lower) (upper : p.upper = q.upper) : p = q :=
  Prod.ext lower upper

/-- The exact pair of `x`. -/
def exact (x : L) : Approx L := mk x x

/-- Exchange the two bounds. -/
def swap (p : Approx L) : Approx L := mk p.upper p.lower

@[simp] theorem swap_swap (p : Approx L) : p.swap.swap = p := rfl

section Order

variable [PartialOrder L]

/-- **Precision**: the lower bound rises and the upper bound falls. -/
theorem le_iff {p q : Approx L} : p ≤ q ↔ p.lower ≤ q.lower ∧ q.upper ≤ p.upper := Iff.rfl

theorem mk_le_mk {x y x' y' : L} : mk x y ≤ mk x' y' ↔ x ≤ x' ∧ y' ≤ y := Iff.rfl

theorem exact_le_exact {x y : L} : exact x ≤ exact y ↔ x = y :=
  ⟨fun h => le_antisymm h.1 h.2, fun h => h ▸ le_rfl⟩

/-- A pair is consistent when its lower bound is below its upper bound. -/
def Consistent (p : Approx L) : Prop := p.lower ≤ p.upper

/-- A pair below an exact pair in precision brackets it. -/
theorem le_exact_iff {p : Approx L} {x : L} : p ≤ exact x ↔ p.lower ≤ x ∧ x ≤ p.upper := Iff.rfl

theorem swap_anti {p q : Approx L} (h : p ≤ q) : q.swap ≤ p.swap := ⟨h.2, h.1⟩

theorem consistent_iff_le_swap (p : Approx L) : p.Consistent ↔ p ≤ p.swap :=
  ⟨fun h => ⟨h, h⟩, fun h => h.1⟩

end Order

end Approx

variable {L : Type*} [CompleteLattice L]

open Approx

variable (A : Approx L →o Approx L)

/-- `A` approximates `O`: on exact pairs it is `O`. -/
def Approximates (O : L → L) : Prop := ∀ x, A (exact x) = exact (O x)

/-- `A` is symmetric: its upper component is its lower component with the bounds exchanged. -/
def IsSymmetric : Prop := ∀ x y, (A (mk x y)).upper = (A (mk y x)).lower

/-- The lower component at a fixed upper bound, monotone in the lower bound. -/
def lowerOp (y : L) : L →o L where
  toFun x := (A (mk x y)).lower
  monotone' x x' h := (A.monotone (show mk x y ≤ mk x' y from ⟨h, le_rfl⟩)).1

/-- The upper component at a fixed lower bound, monotone in the upper bound. -/
def upperOp (x : L) : L →o L where
  toFun y := (A (mk x y)).upper
  monotone' y y' h := (A.monotone (show mk x y' ≤ mk x y from ⟨le_rfl, h⟩)).2

theorem lowerOp_anti {y y' : L} (h : y ≤ y') : lowerOp A y' ≤ lowerOp A y :=
  fun x => (A.monotone (show mk x y' ≤ mk x y from ⟨le_rfl, h⟩)).1

theorem upperOp_anti {x x' : L} (h : x ≤ x') : upperOp A x' ≤ upperOp A x :=
  fun y => (A.monotone (show mk x y ≤ mk x' y from ⟨h, le_rfl⟩)).2

/-- The lower stable revision: the least lower bound obtainable under upper bound `y`. -/
def stableLower (y : L) : L := (lowerOp A y).lfp

/-- The upper stable revision: the least upper bound obtainable under lower bound `x`. -/
def stableUpper (x : L) : L := (upperOp A x).lfp

theorem stableLower_anti {y y' : L} (h : y ≤ y') : stableLower A y' ≤ stableLower A y :=
  OrderHom.lfp.monotone (lowerOp_anti A h)

theorem stableUpper_anti {x x' : L} (h : x ≤ x') : stableUpper A x' ≤ stableUpper A x :=
  OrderHom.lfp.monotone (upperOp_anti A h)

/-- **The stable operator** `(x, y) ↦ (lfp A(·, y).lower, lfp A(x, ·).upper)`. -/
def stableOp : Approx L →o Approx L where
  toFun p := mk (stableLower A p.upper) (stableUpper A p.lower)
  monotone' _ _ h := ⟨stableLower_anti A h.2, stableUpper_anti A h.1⟩

@[simp] theorem stableOp_lower (p : Approx L) : (stableOp A p).lower = stableLower A p.upper := rfl
@[simp] theorem stableOp_upper (p : Approx L) : (stableOp A p).upper = stableUpper A p.lower := rfl

/-- The Kripke–Kleene fixpoint: the least precise fixpoint of `A`. -/
def kripkeKleene : Approx L := A.lfp

/-- The well-founded fixpoint: the least precise fixpoint of the stable operator. -/
def wellFounded : Approx L := (stableOp A).lfp

/-- A stable fixpoint is a fixpoint of the stable operator. -/
def IsStableFixpoint (p : Approx L) : Prop := stableOp A p = p

variable {A}

theorem IsStableFixpoint.isFixed {p : Approx L} (h : IsStableFixpoint A p) : A p = p := by
  have hl : stableLower A p.upper = p.lower := congrArg Approx.lower h
  have hu : stableUpper A p.lower = p.upper := congrArg Approx.upper h
  apply Approx.ext
  · have := (lowerOp A p.upper).map_lfp
    rw [← stableLower, hl] at this
    exact this
  · have := (upperOp A p.lower).map_lfp
    rw [← stableUpper, hu] at this
    exact this

theorem kripkeKleene_le_fixed {p : Approx L} (h : A p = p) : kripkeKleene A ≤ p :=
  OrderHom.lfp_le_fixed _ h

theorem wellFounded_isStableFixpoint : IsStableFixpoint A (wellFounded A) := OrderHom.map_lfp _

/-- **The well-founded fixpoint approximates every stable fixpoint.** -/
theorem wellFounded_le {p : Approx L} (h : IsStableFixpoint A p) : wellFounded A ≤ p :=
  OrderHom.lfp_le_fixed _ h

theorem kripkeKleene_le_wellFounded : kripkeKleene A ≤ wellFounded A :=
  kripkeKleene_le_fixed wellFounded_isStableFixpoint.isFixed

/-- An exact stable fixpoint is a fixed point of the approximated operator. -/
theorem IsStableFixpoint.exact_fixed {O : L → L} (approx : Approximates A O) {x : L}
    (h : IsStableFixpoint A (exact x)) : O x = x := by
  have := congrArg Approx.lower (h.isFixed.symm.trans (approx x))
  exact this.symm

/-- An exact pair is a stable fixpoint exactly when both revisions return it. -/
theorem isStableFixpoint_exact_iff {x : L} :
    IsStableFixpoint A (exact x) ↔ stableLower A x = x ∧ stableUpper A x = x :=
  ⟨fun h => ⟨congrArg Approx.lower h, congrArg Approx.upper h⟩,
    fun ⟨l, u⟩ => Approx.ext l u⟩

/-- A least fixed point that commutes with the exchange of bounds is consistent. -/
theorem lfp_consistent_of_swap (F : Approx L →o Approx L) (commutes : ∀ p, F p.swap = (F p).swap) :
    F.lfp.Consistent := by
  rw [consistent_iff_le_swap]
  exact OrderHom.lfp_le_fixed _ (by rw [commutes, OrderHom.map_lfp])

/-- An exact well-founded fixpoint is the only exact stable fixpoint. -/
theorem exact_stable_iff_of_wellFounded_eq {x : L} (h : wellFounded A = exact x) (y : L) :
    IsStableFixpoint A (exact y) ↔ y = x := by
  constructor
  · intro stable
    have := wellFounded_le stable
    rw [h, exact_le_exact] at this
    exact this.symm
  · rintro rfl
    rw [← h]
    exact wellFounded_isStableFixpoint

/-! ## Symmetric approximators -/

section Symmetric

variable (symm : IsSymmetric A)
include symm

theorem upperOp_eq (x : L) : upperOp A x = lowerOp A x := by
  ext y
  exact symm x y

theorem stableUpper_eq (x : L) : stableUpper A x = stableLower A x := by
  rw [stableUpper, upperOp_eq symm]
  rfl

theorem map_swap (p : Approx L) : A p.swap = (A p).swap :=
  Approx.ext (symm p.lower p.upper).symm (symm p.upper p.lower)

theorem stableOp_swap (p : Approx L) : stableOp A p.swap = (stableOp A p).swap :=
  Approx.ext (stableUpper_eq symm p.lower).symm (stableUpper_eq symm p.upper)

/-- For a symmetric approximator, an exact pair is a stable fixpoint when it is the lower
revision of itself. -/
theorem isStableFixpoint_exact_iff_symm {x : L} : IsStableFixpoint A (exact x) ↔ stableLower A x = x := by
  rw [isStableFixpoint_exact_iff, stableUpper_eq symm, and_self]

/-- The Kripke–Kleene fixpoint of a symmetric approximator is consistent. -/
theorem kripkeKleene_consistent : (kripkeKleene A).Consistent :=
  lfp_consistent_of_swap A (map_swap symm)

/-- The well-founded fixpoint of a symmetric approximator is consistent. -/
theorem wellFounded_consistent : (wellFounded A).Consistent :=
  lfp_consistent_of_swap (stableOp A) (stableOp_swap symm)

end Symmetric

end Mettapedia.Logic.ASP.AFT
