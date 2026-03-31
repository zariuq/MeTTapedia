import Mettapedia.Computability.PNP.PostSwitchInputObstruction

/-!
# P vs NP crux: the exact visible post-switch surface

The existing obstruction files already use the manuscript's exact post-switch
local input

`u = (z, a, b)`

with involution

`T(u) = (z, a, b xor a)`.

This file factors that object into a clean standalone interface:

* the full visible surface is the exact manuscript input itself;
* the invariant visible surface is the projection `(z, a)`;
* the fork surface is the exact retained data `((z, a), b)`.

Nothing here claims the switched witness-bit family is small.  The point is
simply to isolate the exact object on which any future compression theorem must
operate.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {k : ℕ}

/-- The manuscript's exact visible post-switch surface. -/
abbrev ExactVisiblePostSwitchSurface (Z : Type*) (k : ℕ) := PostSwitchInput Z k

/-- The always-invariant visible projection obtained by dropping the VV right-hand side. -/
abbrev InvariantPostSwitchSurface (Z : Type*) (k : ℕ) := Z × BitVec k

/-- The exact fork surface keeping the invariant projection together with the side channel `b`. -/
abbrev ForkPostSwitchSurface (Z : Type*) (k : ℕ) :=
  InvariantPostSwitchSurface Z k × BitVec k

/-- The full visible data map, written explicitly for theorem interfaces. -/
def fullVisibleData (u : ExactVisiblePostSwitchSurface Z k) :
    ExactVisiblePostSwitchSurface Z k := u

/-- The manuscript's invariant projection `(z, a)`. -/
def invariantVisibleData (u : ExactVisiblePostSwitchSurface Z k) :
    InvariantPostSwitchSurface Z k :=
  invariantProjection u

/-- The exact fork-visible data `((z, a), b)`. -/
def forkVisibleData (u : ExactVisiblePostSwitchSurface Z k) :
    ForkPostSwitchSurface Z k :=
  (invariantVisibleData u, u.b)

@[simp] theorem fullVisibleData_eq (u : ExactVisiblePostSwitchSurface Z k) :
    fullVisibleData u = u := rfl

@[simp] theorem invariantVisibleData_eq (u : ExactVisiblePostSwitchSurface Z k) :
    invariantVisibleData u = (u.z, u.a) := rfl

@[simp] theorem forkVisibleData_eq (u : ExactVisiblePostSwitchSurface Z k) :
    forkVisibleData u = ((u.z, u.a), u.b) := rfl

@[simp] theorem invariantVisibleData_tiInputMap
    (u : ExactVisiblePostSwitchSurface Z k) :
    invariantVisibleData (tiInputMap u) = invariantVisibleData u := by
  exact invariantProjection_tiInputMap u

@[simp] theorem forkVisibleData_tiInputMap
    (u : ExactVisiblePostSwitchSurface Z k) :
    forkVisibleData (tiInputMap u) = (invariantVisibleData u, vvToggle u.a u.b) := by
  cases u
  rfl

/-- The exact fork surface is definitionally equivalent to the full manuscript input. -/
def forkVisibleEquiv :
    ExactVisiblePostSwitchSurface Z k ≃ ForkPostSwitchSurface Z k where
  toFun := forkVisibleData
  invFun := fun t => ⟨t.1.1, t.1.2, t.2⟩
  left_inv := by
    intro u
    cases u
    rfl
  right_inv := by
    intro t
    cases t
    rfl

theorem forkVisibleData_injective :
    Function.Injective (forkVisibleData (Z := Z) (k := k)) :=
  forkVisibleEquiv.injective

theorem fullVisibleData_tiInputMap_eq_iff_zeroColumn
    (u : ExactVisiblePostSwitchSurface Z k) :
    fullVisibleData (tiInputMap u) = fullVisibleData u ↔ u.a = zeroVec := by
  simpa [fullVisibleData] using tiInputMap_eq_self_iff_zeroColumn u

theorem forkVisibleData_tiInputMap_eq_iff_zeroColumn
    (u : ExactVisiblePostSwitchSurface Z k) :
    forkVisibleData (tiInputMap u) = forkVisibleData u ↔ u.a = zeroVec := by
  constructor
  · intro h
    apply (tiInputMap_eq_self_iff_zeroColumn u).mp
    apply forkVisibleData_injective
    simpa [fullVisibleData] using h
  · intro hzero
    cases u with
    | mk z a b =>
        have ha : a = zeroVec := hzero
        subst ha
        change ((z, zeroVec), vvToggle zeroVec b) = ((z, zeroVec), b)
        exact congrArg (fun t => ((z, zeroVec), t)) ((vvToggle_eq_self_iff_zero zeroVec b).2 rfl)

theorem forkVisibleData_tiInputMap_ne_iff_nonzeroColumn
    (u : ExactVisiblePostSwitchSurface Z k) :
    forkVisibleData (tiInputMap u) ≠ forkVisibleData u ↔ nonzeroColumn u.a := by
  constructor
  · intro hneq
    have hneZero : u.a ≠ zeroVec := by
      intro hzero
      apply hneq
      exact (forkVisibleData_tiInputMap_eq_iff_zeroColumn u).2 hzero
    exact (nonzeroColumn_iff_ne_zero u.a).2 hneZero
  · intro hnonzero heq
    have hzero : u.a = zeroVec :=
      (forkVisibleData_tiInputMap_eq_iff_zeroColumn u).1 heq
    exact (nonzeroColumn_iff_ne_zero u.a).1 hnonzero hzero

end

end Mettapedia.Computability.PNP
