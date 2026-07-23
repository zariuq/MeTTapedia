import Mathlib.Algebra.Order.Kleene
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Lattice.Basic
import Mettapedia.OSLF.PathMap.PathAlgebra.FreeMonoidBoundary

/-!
# The finite-language idempotent semiring

A *space* of paths is a finite set of words.  This module equips that carrier with its
algebraic structure: union is addition, path concatenation is multiplication, the empty
space is `0`, and the space containing only the empty path is `1`.

Mathlib supplies the **infinitary** model `Language α = Set (List α)` with `Semiring` and
`KleeneAlgebra` instances (`Mathlib/Computability/Language.lean`), but there is no finite
analogue anywhere in Mathlib: no `Finset`-based idempotent semiring exists.  This module
fills that gap.

## Why the laws are stated as theorems and the structure is a `def`

`Finset` already carries a *pointwise* algebra in the `Pointwise` scope, where `1 = {1}` and
`+ = image₂ (· + ·)`.  Registering a global `Semiring (Finset (FreeMonoid α))` whose `+` is
`∪` and whose `0` is `∅` would create a diamond for any downstream file that opens
`Pointwise`.  The laws are therefore proven as ordinary theorems about explicit operations,
and the bundled structures are provided as `def`s to be introduced locally with `letI` where
a semiring is genuinely wanted.  This keeps the mathematical content complete while leaving
the ambient `Finset` instances untouched.

## Ceiling: idempotent semiring, never a Kleene algebra

`Language α` is a `KleeneAlgebra`.  The finite model **cannot** be: the Kleene star of any
finite language other than `1` is infinite, so `∗` does not restrict to `Finset`.
`IdemSemiring` is the exact ceiling here — a genuine structural difference between the finite
and infinitary path algebras, not a gap in this development.

## Main definitions

* `FinLang.add`, `FinLang.mul`, `FinLang.zero`, `FinLang.one` — the path-space operations.
* `FinLang.semiring`, `FinLang.idemSemiring` — the bundled structures (opt-in via `letI`).

## Main results

* `FinLang.add_assoc`, `add_comm`, `zero_add`, `add_zero`, `add_idem` — the additive
  idempotent-commutative-monoid laws.
* `FinLang.mul_assoc`, `one_mul`, `mul_one`, `zero_mul`, `mul_zero` — the multiplicative
  monoid-with-zero laws.
* `FinLang.left_distrib`, `right_distrib` — distributivity.

## References

* Mathlib, `Mathlib/Computability/Language.lean` — the infinitary model this mirrors.
* Mathlib, `Mathlib/Data/Set/Semiring.lean` — the `SetSemiring` synonym pattern discussed above.
-/

namespace Mettapedia.OSLF.PathMap.PathAlgebra

variable {α : Type*}

/-- `FreeMonoid α` is a bare `def` over `List α`, so the `List` decidable-equality instance
does not fire through it.  Supplying it is a prerequisite for any `Finset (FreeMonoid α)`
operation. -/
instance instDecidableEqFreeMonoid [DecidableEq α] : DecidableEq (FreeMonoid α) :=
  inferInstanceAs (DecidableEq (List α))

namespace FinLang

/-- A finite language: a finite set of paths. -/
abbrev FinLanguage (α : Type*) : Type _ := Finset (FreeMonoid α)

/-- The empty space, the additive unit. -/
def zero : FinLanguage α := (∅ : Finset (FreeMonoid α))

/-- The space containing exactly the empty path, the multiplicative unit. -/
def one : FinLanguage α := {(1 : FreeMonoid α)}

/-- Union of spaces: the additive operation. -/
def add [DecidableEq α] (s t : FinLanguage α) : FinLanguage α := s ∪ t

/-- Elementwise path concatenation: the multiplicative operation. -/
def mul [DecidableEq α] (s t : FinLanguage α) : FinLanguage α := Finset.image₂ (· * ·) s t

@[simp]
theorem mem_mul [DecidableEq α] {s t : FinLanguage α} {x : FreeMonoid α} :
    x ∈ mul s t ↔ ∃ a ∈ s, ∃ b ∈ t, a * b = x := by
  simp [mul]

/-! ## Additive structure: a commutative idempotent monoid -/

theorem add_assoc [DecidableEq α] (s t u : FinLanguage α) :
    add (add s t) u = add s (add t u) := Finset.union_assoc s t u

theorem add_comm [DecidableEq α] (s t : FinLanguage α) : add s t = add t s :=
  Finset.union_comm s t

theorem zero_add [DecidableEq α] (s : FinLanguage α) : add zero s = s :=
  Finset.empty_union s

theorem add_zero [DecidableEq α] (s : FinLanguage α) : add s zero = s :=
  Finset.union_empty s

/-- Union is idempotent -- the law that makes this an *idempotent* semiring. -/
@[simp]
theorem add_idem [DecidableEq α] (s : FinLanguage α) : add s s = s :=
  Finset.union_idempotent s

/-! ## Multiplicative structure: a monoid with zero -/

theorem mul_assoc [DecidableEq α] (s t u : FinLanguage α) :
    mul (mul s t) u = mul s (mul t u) :=
  Finset.image₂_assoc (fun a b c => _root_.mul_assoc a b c)

theorem one_mul [DecidableEq α] (s : FinLanguage α) : mul one s = s := by
  simp [mul, one]

theorem mul_one [DecidableEq α] (s : FinLanguage α) : mul s one = s := by
  simp [mul, one]

theorem zero_mul [DecidableEq α] (s : FinLanguage α) : mul zero s = zero :=
  Finset.image₂_empty_left

theorem mul_zero [DecidableEq α] (s : FinLanguage α) : mul s zero = zero :=
  Finset.image₂_empty_right

/-! ## Distributivity -/

theorem left_distrib [DecidableEq α] (s t u : FinLanguage α) :
    mul s (add t u) = add (mul s t) (mul s u) :=
  Finset.image₂_union_right

theorem right_distrib [DecidableEq α] (s t u : FinLanguage α) :
    mul (add s t) u = add (mul s u) (mul t u) :=
  Finset.image₂_union_left

/-! ## Bundled structures

Opt-in, to avoid a diamond with `Finset`'s `Pointwise` algebra.  Introduce locally with
`letI := FinLang.semiring` when semiring notation is wanted. -/

/-- The finite path-space semiring: union as addition, concatenation as multiplication. -/
@[reducible] def semiring [DecidableEq α] : Semiring (FinLanguage α) where
  zero := zero
  one := one
  add := add
  mul := mul
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib := right_distrib
  -- Because addition is idempotent, `n` copies of `s` collapse to `s` for every `n > 0`.
  -- Giving `nsmul` directly avoids needing ambient `Zero`/`Add` instances, which would
  -- mean registering global structure on `Finset` (see the module docstring).
  nsmul := fun n s => if n = 0 then zero else s
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun n s => by
    cases n with
    | zero => exact show s = add zero s from (zero_add s).symm
    | succ k => exact show s = add s s from (add_idem s).symm

/-- The finite path-space algebra is an **idempotent** semiring.  It is deliberately not a
`KleeneAlgebra`: the star of a finite language other than `1` is infinite, so `∗` does not
restrict to this carrier. -/
@[reducible] def idemSemiring [DecidableEq α] : IdemSemiring (FinLanguage α) :=
  letI := (semiring : Semiring (FinLanguage α))
  IdemSemiring.ofSemiring (fun s => by exact add_idem s)

end FinLang

end Mettapedia.OSLF.PathMap.PathAlgebra
