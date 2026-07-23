import Mathlib.Algebra.FreeMonoid.Basic

/-!
# The free-monoid boundary of the path algebra

Paths in a path-space algebra are words: elements of `FreeMonoid α`.  This module pins the
exact algebraic strength of that carrier, because a path algebra can be presented in two
inequivalent ways and the difference is load bearing.

* **Free monoid.**  Concatenation is associative with unit `1`, and it is *cancellative*
  (`FreeMonoid` is a `CancelMonoid`), but there are **no inverses**.  Stripping a prefix is
  therefore a **partial** operation: `unwrapPath p q` succeeds exactly when `p` is a prefix
  of `q`.
* **Group completion.**  Adjoining a formal inverse `Neg p` with the cancellation law
  `Neg p * p = 1` totalises prefix stripping, at the cost of leaving the free monoid: the
  carrier becomes a group.

The two theorems below are the precise statement that this is a *proper* extension, not a
definitional convenience:

* `no_right_inverse` — the free monoid on an inhabited alphabet is not a group;
* `unwrapPath_partial` — prefix stripping genuinely fails on some inputs, so its total form
  cannot be defined inside the free monoid.

Cancellativity is recorded as `mul_left_cancel'` for contrast: the carrier is
cancellative-but-not-a-group, which is exactly the situation in which a group completion is
the standard (and only) route to totality.

## Main definitions

* `unwrapList` / `unwrapPath` — partial prefix stripping.

## Main theorems

* `no_right_inverse` — no right-inverse function exists on `FreeMonoid α` for inhabited `α`.
* `unwrapPath_wrap` — the round trip `unwrapPath p (p * s) = some s`.
* `unwrapPath_partial` — a concrete failure witness for distinct letters.

## References

* Mathlib, `Mathlib/Algebra/FreeMonoid/Basic.lean`: `FreeMonoid`, its `CancelMonoid`
  instance, `FreeMonoid.uniqueUnits`, and the `length` homomorphism.
-/

namespace Mettapedia.OSLF.PathMap.PathAlgebra

open FreeMonoid

variable {α : Type*}

/-! ## Paths do not have inverses -/

/-- The free monoid on an inhabited alphabet admits no right-inverse function: it is
cancellative but **not** a group.  Consequently a cancellation law `Neg p * p = 1` is a
proper extension of the path algebra, not a derived convenience. -/
theorem no_right_inverse (a : α) :
    ¬ ∃ inv : FreeMonoid α → FreeMonoid α, ∀ x : FreeMonoid α, x * inv x = 1 := by
  rintro ⟨inv, h⟩
  have hlen : (FreeMonoid.of a * inv (FreeMonoid.of a)).length = 0 := by
    rw [h (FreeMonoid.of a)]
    exact FreeMonoid.length_one
  rw [FreeMonoid.length_mul, FreeMonoid.length_of] at hlen
  omega

/-- Contrast with `no_right_inverse`: the carrier *is* cancellative.  Cancellative-but-not-a-
group is precisely the setting in which a group completion is the standard route to a total
inverse. -/
theorem mul_left_cancel' {a b c : FreeMonoid α} (h : a * b = a * c) : b = c :=
  mul_left_cancel h

/-! ## Prefix stripping is partial -/

/-- Strip a prefix from a list, failing when the first argument is not a prefix. -/
def unwrapList [DecidableEq α] : List α → List α → Option (List α)
  | [], q => some q
  | _ :: _, [] => none
  | a :: p, b :: q => if a = b then unwrapList p q else none

/-- Strip a prefix path, failing when the first path is not a prefix of the second.  This is
the honest (partial) form of Zippy's `Unwrap`; the total form requires inverses, which
`no_right_inverse` rules out. -/
def unwrapPath [DecidableEq α] (p q : FreeMonoid α) : Option (FreeMonoid α) :=
  (unwrapList (FreeMonoid.toList p) (FreeMonoid.toList q)).map FreeMonoid.ofList

@[simp]
theorem unwrapList_append [DecidableEq α] (p s : List α) :
    unwrapList p (p ++ s) = some s := by
  induction p with
  | nil => simp [unwrapList]
  | cons a p ih => simp [unwrapList, ih]

/-- Round trip: wrapping by `p` and then unwrapping by `p` recovers the argument. -/
@[simp]
theorem unwrapPath_wrap [DecidableEq α] (p s : FreeMonoid α) :
    unwrapPath p (p * s) = some s := by
  simp [unwrapPath, unwrapList_append]

/-- Prefix stripping genuinely fails: for distinct letters `a ≠ b`, `unwrapPath` on the
corresponding one-letter paths is `none`.  This is the partiality that a formal inverse
would have to paper over. -/
theorem unwrapPath_partial [DecidableEq α] {a b : α} (h : a ≠ b) :
    unwrapPath (FreeMonoid.of a) (FreeMonoid.of b) = none := by
  show (unwrapList [a] [b]).map FreeMonoid.ofList = none
  simp [unwrapList, h]

end Mettapedia.OSLF.PathMap.PathAlgebra
