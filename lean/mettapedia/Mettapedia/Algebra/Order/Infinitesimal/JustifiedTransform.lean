import Mettapedia.Algebra.Order.Infinitesimal.LevelSeries

/-!
# Transformations that carry their justification

A rewriting step on a numeric expression is only sound under conditions, and
the conditions are numeric facts.  Dividing through by a term is exact — but
only if that term is nonzero, and in Lean division by zero is silently `0`, so
an unjustified step does not fail loudly: it quietly returns the wrong answer.

`Justified` is the type of a transformation that cannot be built without its
proof.  A value carries the input, the output, the assumptions it needed, and a
proof that the two denote the same number.  Composition appends the assumption
lists, so what a result rests on travels with it.

* `normalize` is justified by `toHahn_norm` and assumes nothing.
* `divideByTerm` is justified only when the divisor's coefficient is nonzero;
  `tryDivideByTerm` is the checked entry point and returns `none` otherwise.
* `divideByZero_is_wrong` is the negative control: with a zero divisor the
  identity genuinely fails, so the hypothesis is doing work rather than
  decorating the statement.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

open HahnSeries LevelSeries

namespace Justified

/-- A transformation together with everything needed to trust it. -/
structure Step where
  /-- What went in. -/
  input : LevelSeries
  /-- What came out. -/
  output : LevelSeries
  /-- The numeric facts the step required, recorded by name. -/
  assumptions : List String
  /-- The two denote the same number. -/
  valid : toLevelField output = toLevelField input

/-- Doing nothing is justified, and assumes nothing. -/
def id (l : LevelSeries) : Step where
  input := l
  output := l
  assumptions := []
  valid := rfl

/-- **Canonicalisation is justified and assumption-free.** -/
def normalize (l : LevelSeries) : Step where
  input := l
  output := norm l
  assumptions := []
  valid := toLevelField_norm l

/-- **Steps compose, and their assumptions accumulate.**  A result never
loses track of what it rests on. -/
def trans (s t : Step) (h : t.input = s.output) : Step where
  input := s.input
  output := t.output
  assumptions := s.assumptions ++ t.assumptions
  valid := by rw [t.valid, h, s.valid]

theorem trans_assumptions (s t : Step) (h : t.input = s.output) :
    (trans s t h).assumptions = s.assumptions ++ t.assumptions := rfl

end Justified

/-! ## Dividing through by a term -/

/-- Divide every term by one term: subtract its level, divide by its
coefficient. -/
def divideByTerm (l : LevelSeries) (i : ℤ) (c : ℚ) : LevelSeries :=
  l.map fun t => (t.1 - i, t.2 / c)

/-- **The numeric fact the step needs.**  Multiplying the quotient back by the
divisor returns the original — provided the divisor's coefficient is nonzero.
This is where `c ≠ 0` is consumed: without it, `t.2 / c * c` is not `t.2`. -/
theorem toHahn_divideByTerm_mul {i : ℤ} {c : ℚ} (hc : c ≠ 0) :
    ∀ l : LevelSeries,
      toHahn (divideByTerm l i c) * single i c = toHahn l
  | [] => by simp [divideByTerm]
  | t :: rest => by
      have hrec := toHahn_divideByTerm_mul (i := i) (c := c) hc rest
      have hcons : divideByTerm (t :: rest) i c
          = (t.1 - i, t.2 / c) :: divideByTerm rest i c := rfl
      have h1 : t.1 - i + i = t.1 := by omega
      have h2 : t.2 / c * c = t.2 := by field_simp
      rw [hcons, toHahn_cons, add_mul, hrec, single_mul_single, h1, h2, toHahn_cons]

/-- The same statement in the ordered field. -/
theorem toLevelField_divideByTerm_mul {i : ℤ} {c : ℚ} (hc : c ≠ 0) (l : LevelSeries) :
    toLevelField (divideByTerm l i c) * toLevelField [(i, c)] = toLevelField l := by
  show toLex (toHahn (divideByTerm l i c)) * toLex (toHahn [(i, c)]) = toLex (toHahn l)
  have hone : toHahn [(i, c)] = single i c := by simp [toHahn]
  rw [hone]
  exact congrArg toLex (toHahn_divideByTerm_mul hc l)

/-- **The checked entry point.**  A zero divisor is refused; there is no way to
obtain a `Step` for it. -/
def tryDivideByTerm (l : LevelSeries) (i : ℤ) (c : ℚ) : Option Justified.Step :=
  if _hc : c = 0 then none
  else some
    { input := divideByTerm l i c
      output := divideByTerm l i c
      assumptions := ["divisor coefficient nonzero"]
      valid := rfl }

theorem tryDivideByTerm_rejects (l : LevelSeries) (i : ℤ) :
    tryDivideByTerm l i 0 = none := by
  simp [tryDivideByTerm]

theorem tryDivideByTerm_accepts {c : ℚ} (l : LevelSeries) (i : ℤ) (hc : c ≠ 0) :
    (tryDivideByTerm l i c).isSome := by
  simp [tryDivideByTerm, hc]

/-- **The negative control.**  With a zero divisor the identity is false, not
merely unproved: the left side collapses to `0` while the right side is `1`.
So the hypothesis in `toHahn_divideByTerm_mul` is load-bearing. -/
theorem divideByZero_is_wrong :
    toHahn (divideByTerm [(0, 1)] 0 0) * single (0 : ℤ) (0 : ℚ) ≠ toHahn [(0, 1)] := by
  rw [single_eq_zero, mul_zero]
  intro h
  have : (1 : ℚ) = 0 := by
    have hc := congrArg (fun x => HahnSeries.coeff x (0 : ℤ)) h
    simpa [toHahn] using hc.symm
  exact one_ne_zero this

/-! ## Dividing by `Ω` is exact and stays in the representation

The level field is a field, but this finite representation is only a ring:
inverting `Ω - 1` needs infinitely many terms.  Division by a *single term* is
the fragment that is exact and closed, and it is enough to move between
scales. -/

/-- Divide by `Ω`, shifting every level up by one. -/
def divideByOmega (l : LevelSeries) : LevelSeries := divideByTerm l (-1) 1

theorem divideByOmega_mul (l : LevelSeries) :
    toLevelField (divideByOmega l) * Om = toLevelField l := by
  have h := toLevelField_divideByTerm_mul (i := -1) (c := 1) one_ne_zero l
  rwa [show toLevelField [((-1 : ℤ), (1 : ℚ))] = Om from by
    simp [toLevelField, toHahn, Om]] at h

/-! ## Controls -/

namespace TransformControls

/-- `3Ω − 5 + 2Ω⁻¹` divided by `Ω` is `3 − 5Ω⁻¹ + 2Ω⁻²`. -/
theorem divide_sample :
    divideByOmega [(-1, 3), (0, -5), (1, 2)] = [(0, 3), (1, -5), (2, 2)] := by
  norm_num [divideByOmega, divideByTerm]

/-- The checked entry point refuses a zero divisor. -/
theorem reject_zero : tryDivideByTerm [(0, 1)] 0 0 = none :=
  tryDivideByTerm_rejects _ _

/-- And accepts a nonzero one. -/
theorem accept_nonzero : (tryDivideByTerm [(0, 1)] 0 2).isSome :=
  tryDivideByTerm_accepts _ _ (by norm_num)

/-- Composing a division with a canonicalisation keeps both assumption
records. -/
theorem composed_assumptions
    (s : Justified.Step) (h : (Justified.normalize s.output).input = s.output) :
    (Justified.trans s (Justified.normalize s.output) h).assumptions
      = s.assumptions :=
  by simp [Justified.trans, Justified.normalize]

end TransformControls

end Mettapedia.Algebra.Order.Infinitesimal

#print axioms Mettapedia.Algebra.Order.Infinitesimal.toHahn_divideByTerm_mul
#print axioms Mettapedia.Algebra.Order.Infinitesimal.toLevelField_divideByTerm_mul
#print axioms Mettapedia.Algebra.Order.Infinitesimal.divideByZero_is_wrong
#print axioms Mettapedia.Algebra.Order.Infinitesimal.divideByOmega_mul
#print axioms Mettapedia.Algebra.Order.Infinitesimal.TransformControls.divide_sample
#print axioms Mettapedia.Algebra.Order.Infinitesimal.TransformControls.reject_zero
