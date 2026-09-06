import Mettapedia.Cybernetics.DistinctionCalculus.Basic

/-!
# Pair-weighted distinction and observation change

Finite rational probabilities make the pair bracket executable. The balance
law separates change of state from change of observer. Mean distortion is a
quantitative diagnostic, not an admission judgment: it implies pointwise
preservation only on positive-mass pairs. Full support is stated when needed.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus

universe u v w

structure Distribution (V : Type u) [Fintype V] where
  weight : V → ℚ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1

namespace Distribution

variable {V : Type u} {W : Type v} {X : Type w} [Fintype V]

def pairAverage (p : Distribution V) (f : V → V → ℚ) : ℚ :=
  ∑ x, ∑ y, p.weight x * p.weight y * f x y

theorem pairAverage_nonnegative (p : Distribution V) {f : V → V → ℚ}
    (nonnegative : ∀ x y, 0 ≤ f x y) : 0 ≤ p.pairAverage f := by
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (p.nonnegative x) (p.nonnegative y)) (nonnegative x y)

theorem pairAverage_mono (p : Distribution V) {f g : V → V → ℚ}
    (bound : ∀ x y, f x y ≤ g x y) : p.pairAverage f ≤ p.pairAverage g := by
  exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (bound x y) (mul_nonneg (p.nonnegative x) (p.nonnegative y))

@[simp] theorem pairAverage_const (p : Distribution V) (c : ℚ) :
    p.pairAverage (fun _ _ => c) = c := by
  simp only [pairAverage, ← Finset.sum_mul, ← Finset.mul_sum, p.normalized, mul_one, one_mul]

theorem pairAverage_sub (p : Distribution V) (f g : V → V → ℚ) :
    p.pairAverage (fun x y => f x y - g x y) = p.pairAverage f - p.pairAverage g := by
  simp only [pairAverage, mul_sub, Finset.sum_sub_distrib]

theorem pairAverage_add (p : Distribution V) (f g : V → V → ℚ) :
    p.pairAverage (fun x y => f x y + g x y) = p.pairAverage f + p.pairAverage g := by
  simp only [pairAverage, mul_add, Finset.sum_add_distrib]

def graphtropy (p : Distribution V) (a : Tolerance V) : ℚ := p.pairAverage a.similarity

def distinction (p : Distribution V) (a : Tolerance V) : ℚ := p.pairAverage a.distance

theorem distinction_eq_one_sub (p : Distribution V) (a : Tolerance V) :
    p.distinction a = 1 - p.graphtropy a := by
  change p.pairAverage (fun x y => 1 - a.similarity x y) = 1 - p.pairAverage a.similarity
  rw [pairAverage_sub, pairAverage_const]

theorem graphtropy_bounds (p : Distribution V) (a : Tolerance V) :
    0 ≤ p.graphtropy a ∧ p.graphtropy a ≤ 1 := by
  exact ⟨p.pairAverage_nonnegative a.nonnegative,
    (p.pairAverage_mono a.bounded).trans_eq (p.pairAverage_const 1)⟩

theorem closure_increases_graphtropy (p : Distribution V) {base candidate : Tolerance V}
    (hExt : base.Extends candidate) : p.graphtropy base ≤ p.graphtropy candidate :=
  p.pairAverage_mono hExt

/-- Pair distortion measures the declared observations of a translation. -/
def distortion (p : Distribution V) (source : Tolerance V) (target : Tolerance W)
    (f : V → W) : ℚ :=
  p.pairAverage fun x y => |target.similarity (f x) (f y) - source.similarity x y|

/-- A separately declared value criterion retains the direction of change.
Neither similarity nor a nonnegative distortion determines this quantity. -/
def valueChange (p : Distribution V) (value : V → ℚ) (step : V → V) : ℚ :=
  ∑ x, p.weight x * (value (step x) - value x)

theorem distortion_nonnegative (p : Distribution V) (source : Tolerance V)
    (target : Tolerance W) (f : V → W) : 0 ≤ p.distortion source target f :=
  p.pairAverage_nonnegative fun _ _ => abs_nonneg _

/-- For nonnegative losses, a zero average forces zero on every supported pair. -/
theorem pairAverage_zero_on_support (p : Distribution V) {f : V → V → ℚ}
    (nonnegative : ∀ x y, 0 ≤ f x y) (zero : p.pairAverage f = 0)
    (x y : V) (hx : 0 < p.weight x) (hy : 0 < p.weight y) : f x y = 0 := by
  have rowZero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (p.nonnegative i) (p.nonnegative j)) (nonnegative i j))).mp zero
      x (Finset.mem_univ x)
  have entryZero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) =>
      mul_nonneg (mul_nonneg (p.nonnegative x) (p.nonnegative j)) (nonnegative x j))).mp rowZero
      y (Finset.mem_univ y)
  exact (mul_eq_zero.mp entryZero).resolve_left (ne_of_gt (mul_pos hx hy))

theorem distortion_zero_iff (p : Distribution V) (fullSupport : ∀ x, 0 < p.weight x)
    (source : Tolerance V) (target : Tolerance W) (f : V → W) :
    p.distortion source target f = 0 ↔
      ∀ x y, target.similarity (f x) (f y) = source.similarity x y := by
  constructor
  · intro zero x y
    exact sub_eq_zero.mp (abs_eq_zero.mp
      (p.pairAverage_zero_on_support (fun _ _ => abs_nonneg _) zero x y
        (fullSupport x) (fullSupport y)))
  · intro same
    simp only [distortion, same, sub_self, abs_zero, pairAverage_const]

/-- Triangle accounting for interleaved routes uses the same source pair law. -/
theorem distortion_comp_le (p : Distribution V) (a : Tolerance V) (b : Tolerance W)
    (c : Tolerance X) (f : V → W) (g : W → X) :
    p.distortion a c (g ∘ f) ≤ p.distortion a b f +
      p.pairAverage (fun x y => |c.similarity (g (f x)) (g (f y)) - b.similarity (f x) (f y)|) := by
  unfold distortion
  rw [← pairAverage_add]
  apply p.pairAverage_mono
  intro x y
  dsimp [Function.comp_def]
  have triangle := abs_sub_le (c.similarity (g (f x)) (g (f y)))
    (b.similarity (f x) (f y)) (a.similarity x y)
  linarith

/-- Changing a state and changing its observer contribute separate terms. -/
theorem change_balance (p : Distribution V) (old new : Tolerance V) (step : V → V) :
    p.graphtropy (new.pullback step) - p.graphtropy old =
      p.pairAverage (fun x y => old.similarity (step x) (step y) - old.similarity x y) -
      p.pairAverage (fun x y => old.similarity (step x) (step y) - new.similarity (step x) (step y)) := by
  rw [pairAverage_sub, pairAverage_sub]
  change p.pairAverage _ - p.pairAverage _ = _
  dsimp [Tolerance.pullback]
  ring

end Distribution

end Mettapedia.Cybernetics.DistinctionCalculus
