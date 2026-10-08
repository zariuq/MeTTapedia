import Mettapedia.Algebra.AffineMonoid
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Data.Rat.Defs

/-!
# Min-plus affine summaries

Let `G` be a linearly ordered cancellative additive commutative monoid, such as `ℕ`, `ℤ`, `ℚ`
or `ℝ`. Over the min-plus semiring `Tropical (WithTop G)`, tropical addition is `min` and
tropical multiplication is `+`. The affine summary `⟨trop a, trop b⟩` therefore acts by
`x ↦ min (x + a) b`: a finite shift `a`, then a cap `b`, where `b = ⊤` means no cap.
`minPlus a b` is this summary. Since `Tropical (WithTop G)` is a commutative semiring, every law
of `Mettapedia.Algebra.AffineMonoid` applies to it: the ordered monoid, the right action, the
homogeneous `2 × 2` matrices `!![trop a, trop b; 0, 1]` and the fold, bracketing and scan laws.

* `TropicalCoefficient.Value`: an executable tagged representation with a distinct infinity,
  minimum for alternatives and addition for sequential costs. Its injective interpretation
  agrees with `Tropical (WithTop G)`; no finite sentinel supplies its additive identity.
* `act_minPlus`: the action on every state, `⊤` included.
* `minPlus_mul`: execution-order composition,
  `minPlus a b * minPlus a' b' = minPlus (a + a') (min (b + a') b')`.
* `minPlus_pow_succ`, `minPlus_pow`: a power in closed form. For `k ≠ 0`,
  `minPlus a b ^ k = minPlus (k • a) (b + min 0 ((k - 1) • a))`. The cap of a run is its first
  cap moved by the least partial shift among `0, a, …, (k - 1) • a`, which is `0` or
  `(k - 1) • a`.
* **Caps** `minPlus 0 b`, the maps `x ↦ min x b`, are the tropical translations. They commute
  and are idempotent (`commute_minPlus_zero`, `isIdempotentElem_minPlus_zero`).
* **Shifts** `minPlus a ⊤`, the maps `x ↦ x + a`, are the tropical scalings. They commute
  (`commute_minPlus_top`) but are idempotent only for `a = 0`
  (`isIdempotentElem_minPlus_top_iff`).
* `constant c` is the constant map `x ↦ c`, over any semiring. A constant step discards
  everything before it (`mul_constant`).

The max-plus maps `x ↦ max (x + a) b` over an ordered additive group are the min-plus maps of
the negated state; the integer instance is in `Mettapedia.GSLT.TropicalExpression`. These are laws
of exact arithmetic in `G`. Overflow, cost and effects are outside this module.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.AffineSummary

open Tropical

/-! ## Constant maps over any semiring -/

section Constant

variable {R : Type*} [Semiring R]

/-- The constant map `x ↦ c`: scale `0`, offset `c`. -/
def constant (c : R) : AffineSummary R := ⟨0, c⟩

@[simp] theorem scale_constant (c : R) : (constant c).scale = 0 := rfl

@[simp] theorem offset_constant (c : R) : (constant c).offset = c := rfl

@[simp] theorem act_constant (c x : R) : (constant c).act x = c := by
  simp [act, constant]

/-- A constant step discards everything before it. -/
@[simp] theorem mul_constant (f : AffineSummary R) (c : R) : f * constant c = constant c := by
  ext <;> simp [constant]

/-- The steps after a constant step see only the constant. -/
theorem constant_mul (c : R) (f : AffineSummary R) : constant c * f = constant (f.act c) := by
  ext <;> simp [constant, act]

end Constant

/-! ## Min-plus maps -/

section MinPlus

variable {G : Type*}

/-- The min-plus map `x ↦ min (x + a) b`, shift `a` and cap `b`, where `b = ⊤` is no cap. As an
affine summary over `Tropical (WithTop G)` it is `x ↦ trop a * x + trop b`. -/
def minPlus (a : G) (b : WithTop G) : AffineSummary (Tropical (WithTop G)) :=
  ⟨trop (a : WithTop G), trop b⟩

@[simp] theorem scale_minPlus (a : G) (b : WithTop G) :
    (minPlus a b).scale = trop (a : WithTop G) := rfl

@[simp] theorem offset_minPlus (a : G) (b : WithTop G) : (minPlus a b).offset = trop b := rfl

theorem minPlus_inj {a a' : G} {b b' : WithTop G} :
    minPlus a b = minPlus a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨WithTop.coe_injective (trop_injective (congrArg scale h)),
      trop_injective (congrArg offset h)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

variable [AddCancelCommMonoid G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- The action, on every state `x`, the unreached state `⊤` included. -/
theorem act_minPlus (a : G) (b x : WithTop G) :
    (minPlus a b).act (trop x) = trop (min (x + a) b) := by
  rw [add_comm x]
  rfl

/-- The action on a finite state. -/
theorem act_minPlus_coe (a x : G) (b : WithTop G) :
    (minPlus a b).act (trop (x : WithTop G)) = trop (min ((x + a : G) : WithTop G) b) := by
  rw [act_minPlus, WithTop.coe_add]

/-- Homogeneous coordinates: the tropical matrix `!![trop a, trop b; 0, 1]`. -/
theorem matrix_minPlus (a : G) (b : WithTop G) :
    (minPlus a b).matrix = !![trop (a : WithTop G), trop b; 0, 1] := rfl

@[simp] theorem minPlus_zero_top : minPlus (0 : G) ⊤ = 1 := rfl

/-- **Execution-order composition.** Shift by `a` and cap at `b`, then shift by `a'` and cap
at `b'`: the shifts add, and the first cap is shifted by `a'` before meeting the second. -/
theorem minPlus_mul (a a' : G) (b b' : WithTop G) :
    minPlus a b * minPlus a' b' = minPlus (a + a') (min (b + a') b') := by
  ext
  · change trop ((a' : WithTop G) + a) = trop ((a + a' : G) : WithTop G)
    rw [WithTop.coe_add, add_comm]
  · change trop (min ((a' : WithTop G) + b) b') = trop (min (b + a') b')
    rw [add_comm]

/-- The least partial shift of a run of length `k + 1` lies below the one-step shift. -/
theorem min_zero_succ_nsmul_le (a : G) (k : ℕ) : min 0 ((k + 1) • a) ≤ a := by
  rcases le_total 0 a with ha | ha
  · exact (min_le_left _ _).trans ha
  · refine (min_le_right _ _).trans ?_
    rw [_root_.succ_nsmul]
    exact add_le_of_nonpos_left (nsmul_nonpos ha k)

/-- **Closed form of a power.** A run of `k + 1` equal steps shifts by `(k + 1) • a` and caps at
`b + min 0 (k • a)`, the first cap moved by the least partial shift `min 0 (k • a)` among
`0, a, …, k • a`. -/
theorem minPlus_pow_succ (a : G) (b : WithTop G) (k : ℕ) :
    minPlus a b ^ (k + 1) = minPlus ((k + 1) • a) (b + ↑(min 0 (k • a))) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, minPlus_mul, _root_.succ_nsmul _ (k + 1)]
      congr 1
      have hstep : min 0 (k • a) + a = min a ((k + 1) • a) := by
        rw [← min_add_add_right, zero_add, _root_.succ_nsmul]
      calc min (b + ↑(min 0 (k • a)) + ↑a) b
          = min (b + ↑(min a ((k + 1) • a))) (b + ↑(0 : G)) := by
            rw [add_assoc, ← WithTop.coe_add, hstep, WithTop.coe_zero, add_zero]
        _ = b + ↑(min (min a ((k + 1) • a)) 0) := by
            rw [min_add_add_left, ← WithTop.coe_min]
        _ = b + ↑(min 0 ((k + 1) • a)) := by
            rw [min_assoc, min_comm ((k + 1) • a) 0,
              min_eq_right (min_zero_succ_nsmul_le a k)]

/-- The closed form for a run of `k ≥ 1` steps: shift `k • a`, cap `b + min 0 ((k - 1) • a)`. -/
theorem minPlus_pow (a : G) (b : WithTop G) {k : ℕ} (hk : k ≠ 0) :
    minPlus a b ^ k = minPlus (k • a) (b + ↑(min 0 ((k - 1) • a))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact minPlus_pow_succ a b k

/-! ## Caps and shifts -/

/-- A cap `x ↦ min x b` is the tropical translation by `b`. -/
theorem minPlus_zero (b : WithTop G) : minPlus (0 : G) b = translation (trop b) := rfl

/-- A shift `x ↦ x + a` is the tropical scaling by `a`. -/
theorem minPlus_top (a : G) : minPlus a ⊤ = scaling (trop (a : WithTop G)) := rfl

/-- Two caps compose to the cap at the smaller bound. -/
theorem minPlus_zero_mul_minPlus_zero (b b' : WithTop G) :
    minPlus (0 : G) b * minPlus 0 b' = minPlus 0 (min b b') := by
  rw [minPlus_mul, add_zero, WithTop.coe_zero, add_zero]

/-- Caps are idempotent: capping twice at `b` is capping once. -/
theorem isIdempotentElem_minPlus_zero (b : WithTop G) : IsIdempotentElem (minPlus (0 : G) b) := by
  rw [IsIdempotentElem, minPlus_zero_mul_minPlus_zero, min_self]

/-- Caps commute. -/
theorem commute_minPlus_zero (b b' : WithTop G) : Commute (minPlus (0 : G) b) (minPlus 0 b') := by
  rw [Commute, SemiconjBy, minPlus_zero_mul_minPlus_zero, minPlus_zero_mul_minPlus_zero, min_comm]

/-- Two shifts compose to the shift by the sum. -/
theorem minPlus_top_mul_minPlus_top (a a' : G) :
    minPlus a ⊤ * minPlus a' ⊤ = minPlus (a + a') ⊤ := by
  rw [minPlus_mul, WithTop.top_add, min_self]

/-- Shifts commute. -/
theorem commute_minPlus_top (a a' : G) : Commute (minPlus a ⊤) (minPlus a' ⊤) := by
  rw [Commute, SemiconjBy, minPlus_top_mul_minPlus_top, minPlus_top_mul_minPlus_top, add_comm]

/-- A shift is idempotent only when it is the identity: a stream of shifts may be reordered, but
its duplicates count. -/
theorem isIdempotentElem_minPlus_top_iff (a : G) : IsIdempotentElem (minPlus a ⊤) ↔ a = 0 := by
  rw [IsIdempotentElem, minPlus_top_mul_minPlus_top, minPlus_inj]
  simp

end MinPlus

end Mettapedia.Algebra.AffineSummary

namespace Mettapedia.Algebra.TropicalCoefficient

universe u

/-- Tagged exact costs keep unreachable infinity distinct from every finite cost. -/
inductive Value (G : Type u) where
  | infinity
  | finite : G → Value G
  deriving DecidableEq, Repr

variable {G : Type u}

def alternative [LinearOrder G] : Value G → Value G → Value G
  | .infinity, right => right
  | left, .infinity => left
  | .finite left, .finite right => .finite (min left right)

def sequential [Add G] : Value G → Value G → Value G
  | .finite left, .finite right => .finite (left + right)
  | _, _ => .infinity

def toWithTop : Value G → WithTop G
  | .infinity => ⊤
  | .finite value => value

def fromWithTop : WithTop G → Value G
  | none => .infinity
  | some value => .finite value

@[simp] theorem from_to (value : Value G) :
    fromWithTop (toWithTop value) = value := by
  cases value <;> rfl

@[simp] theorem to_from (value : WithTop G) :
    toWithTop (fromWithTop value) = value := by
  cases value <;> rfl

theorem toWithTop_injective : Function.Injective (toWithTop (G := G)) := by
  intro left right same
  simpa using congrArg fromWithTop same

def interpret (value : Value G) : Tropical (WithTop G) :=
  Tropical.trop (toWithTop value)

theorem interpret_injective : Function.Injective (interpret (G := G)) :=
  Tropical.trop_injective.comp toWithTop_injective

@[simp] theorem interpret_infinity :
    interpret (.infinity : Value G) = 0 := rfl

@[simp] theorem interpret_finite (value : G) :
    interpret (.finite value) = Tropical.trop (value : WithTop G) := rfl

@[simp] theorem interpret_unit [Zero G] :
    interpret (.finite (0 : G)) = 1 := by
  simp [interpret, toWithTop]

theorem alternative_interpret [LinearOrder G] (left right : Value G) :
    interpret (alternative left right) = interpret left + interpret right := by
  cases left <;> cases right <;>
    apply Tropical.untrop_injective <;>
    simp [alternative, interpret, toWithTop, Tropical.untrop_add]

theorem sequential_interpret [Add G] (left right : Value G) :
    interpret (sequential left right) = interpret left * interpret right := by
  cases left <;> cases right <;>
    apply Tropical.untrop_injective <;>
    simp [sequential, interpret, toWithTop, Tropical.untrop_mul, WithTop.coe_add]

section Laws

theorem alternative_associative [LinearOrder G] (first second third : Value G) :
    alternative (alternative first second) third =
      alternative first (alternative second third) := by
  cases first <;> cases second <;> cases third <;> simp [alternative, min_assoc]

theorem alternative_commutative [LinearOrder G] (left right : Value G) :
    alternative left right = alternative right left := by
  cases left <;> cases right <;> simp [alternative, min_comm]

theorem alternative_idempotent [LinearOrder G] (value : Value G) :
    alternative value value = value := by
  cases value <;> simp [alternative]

theorem alternative_infinity [LinearOrder G] (value : Value G) :
    alternative .infinity value = value ∧ alternative value .infinity = value := by
  cases value <;> exact ⟨rfl, rfl⟩

theorem sequential_associative [AddSemigroup G] (first second third : Value G) :
    sequential (sequential first second) third =
      sequential first (sequential second third) := by
  cases first <;> cases second <;> cases third <;> simp [sequential, add_assoc]

theorem sequential_commutative [AddCommMonoid G] (left right : Value G) :
    sequential left right = sequential right left := by
  cases left <;> cases right <;> simp [sequential, add_comm]

theorem sequential_unit [AddZeroClass G] (value : Value G) :
    sequential (.finite 0) value = value ∧ sequential value (.finite 0) = value := by
  cases value <;> simp [sequential]

theorem sequential_infinity [Add G] (value : Value G) :
    sequential .infinity value = .infinity ∧ sequential value .infinity = .infinity := by
  cases value <;> exact ⟨rfl, rfl⟩

theorem sequential_distributes_left [AddCancelCommMonoid G] [LinearOrder G]
    [IsOrderedAddMonoid G] (first second third : Value G) :
    sequential first (alternative second third) =
      alternative (sequential first second) (sequential first third) := by
  apply interpret_injective
  simp only [sequential_interpret, alternative_interpret, mul_add]

theorem sequential_distributes_right [AddCancelCommMonoid G] [LinearOrder G]
    [IsOrderedAddMonoid G] (first second third : Value G) :
    sequential (alternative first second) third =
      alternative (sequential first third) (sequential second third) := by
  apply interpret_injective
  simp only [sequential_interpret, alternative_interpret, add_mul]

theorem infinity_not_finite (value : G) :
    (.infinity : Value G) ≠ .finite value := by
  intro impossible
  cases impossible

end Laws

/-- A finite sentinel cannot be the additive identity of unbounded exact costs. -/
theorem finite_sentinel_not_identity (sentinel : ℚ) :
    alternative (.finite sentinel) (.finite (sentinel + 1)) ≠
      .finite (sentinel + 1) := by
  have greater : sentinel < sentinel + 1 := lt_add_of_pos_right sentinel (by decide)
  simp only [alternative, min_eq_left greater.le]
  intro same
  exact (ne_of_lt greater) (Value.finite.inj same)

theorem exact_rational_sequence_control :
    sequential (.finite (3 / 7 : ℚ)) (.finite (1 / 3)) = .finite (16 / 21) := by
  decide +kernel

theorem infinity_control :
    alternative (.infinity : Value ℚ) (.finite 2000000) = .finite 2000000 ∧
      sequential .infinity (.finite (3 / 7 : ℚ)) = .infinity ∧
      alternative (.finite (3 / 7 : ℚ)) (.finite (1 / 3)) = .finite (1 / 3) := by
  decide +kernel

theorem finite_costs_do_not_multiply :
    sequential (.finite (3 / 7 : ℚ)) (.finite (1 / 3)) ≠ .finite (1 / 7) := by
  decide +kernel

end Mettapedia.Algebra.TropicalCoefficient
