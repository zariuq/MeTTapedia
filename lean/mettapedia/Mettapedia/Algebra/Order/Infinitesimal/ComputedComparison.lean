import Mettapedia.Algebra.Order.Infinitesimal.LevelSeries
import Mettapedia.SetTheory.Surreal.Birthday

/-!
# Deciding, computing, and the difference

`LevelSeries.lt` has an executable decision procedure, including rational
cancellation and comparisons at repeated levels. The controls below use
`decide +kernel`, which checks the reduction in Lean's kernel, not a native
compiler oracle. `lt_iff_toLevelField_lt` separately proves that the procedure
computes the order of the denoted field elements.

Ordinary `decide` first attempts elaborator reduction. Its failure is not a
failure of kernel computation: rational cancellation and the mixed-level
comparison below are concrete counterexamples to that inference. They build
using kernel reduction in the same module and with the same imports.

The order on unrestricted `Surreal`, in contrast, obtains its `Decidable`
instance from `Classical.decRel`. It is classically decidable, but that instance
does not supply an executable comparison algorithm. The explicit surreal
examples below use order proofs rather than executing that instance.

`LevelSeries.cmp` includes `Classical.choice` in its proof dependencies. That
trace alone does not decide executability: the positive, negative and exact
cancellation controls here all reduce in the kernel. An executable fragment
requires both computations and their general semantic specification.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

open LevelSeries

/-! ## Kernel-checked comparisons

Each of these is proved by `decide +kernel`: the proof term is a computation the kernel
performed, not an argument. -/

/-- `1 < Ω`, decided. -/
theorem one_lt_omega_decided : lt one omega := by decide +kernel

/-- `Ω⁻¹ < 1`, decided. -/
theorem omegaInv_lt_one_decided : lt omegaInv one := by decide +kernel

/-- Exact rational cancellation also reduces in the kernel. -/
theorem rational_cancellation_decided : (1 : ℚ) + (-1) = 0 := by decide +kernel

/-- Repeated levels require rational addition during normalization. -/
theorem mixed_levels_decided : lt [(-1, 3), (0, -5)] [(-1, 4)] := by decide +kernel

/-- Exact cancellation of equal series is an executable negative control. -/
theorem cancellation_decided : ¬ lt [(0, 1), (0, -1)] [] := by decide +kernel

/-- `1` in the field. -/
theorem toLevelField_one : toLevelField one = 1 := by
  rw [toLevelField, toHahn_one]; rfl

/-- The reverse inequality is rejected by the same computation. -/
theorem omega_not_lt_one : ¬ lt omega one := by decide +kernel

/-- Self-comparison requires cancellation and is also kernel-computed. -/
theorem omega_not_lt_omega : ¬ lt omega omega := by decide +kernel

/-! ## And what they mean

A computation is worth something only with a theorem saying what it computes.
`lt_iff_toLevelField_lt` is that theorem, and it turns each kernel evaluation
above into a statement about the ordered field. -/

/-- **From a kernel computation to a fact about the field.** -/
theorem one_lt_omega_semantic : toLevelField one < toLevelField omega :=
  (lt_iff_toLevelField_lt one omega).mp one_lt_omega_decided

theorem omegaInv_lt_one_semantic : toLevelField omegaInv < toLevelField one :=
  (lt_iff_toLevelField_lt omegaInv one).mp omegaInv_lt_one_decided

theorem mixed_levels_semantic :
    toLevelField [(-1, 3), (0, -5)] < toLevelField [(-1, 4)] :=
  (lt_iff_toLevelField_lt _ _).mp mixed_levels_decided

theorem cancellation_semantic :
    ¬ toLevelField [(0, 1), (0, -1)] < toLevelField [] :=
  fun h => cancellation_decided ((lt_iff_toLevelField_lt _ _).mpr h)

/-- The same for the refusal: the field really does not put `Ω` below `1`. -/
theorem omega_not_lt_one_semantic : ¬ (toLevelField omega < toLevelField one) :=
  fun h => omega_not_lt_one ((lt_iff_toLevelField_lt omega one).mpr h)

/-! ## The contrast: an order with no algorithm

The surreal order is a `LinearOrder` whose decidability is `Classical.decRel`.
The instance exists, so `Decidable` is satisfied and the type is a
`LinearOrder`; nothing about that makes any comparison computable.  Facts on
this side are proved. -/

open Mettapedia.SetTheory.SignExpansion

/-- This example uses a proof about sign expansions, not classical reduction. -/
theorem zero_lt_omega_by_proof : (0 : Surreal) < Surreal.omega :=
  Surreal.zero_lt_omega

/-- And so is this, though the analogous level-series fact is a `decide`. -/
theorem half_lt_one_by_proof :
    Surreal.mk (Surreal.dyadicPre 1) < Surreal.mk (Surreal.dyadicPre 0) :=
  Surreal.dyadic_anti 0

/-! ## Controls -/

namespace ComparisonControls

/-- The executable comparison agrees with the field in both directions, so the
`decide` results above are not accidents of one example. -/
theorem decided_agrees (p q : LevelSeries) :
    lt p q ↔ toLevelField p < toLevelField q := lt_iff_toLevelField_lt p q

/-- Equal series do not compare strictly, checked by computation. -/
theorem one_not_lt_one : ¬ lt one one := by decide +kernel

end ComparisonControls

end Mettapedia.Algebra.Order.Infinitesimal

#print axioms Mettapedia.Algebra.Order.Infinitesimal.one_lt_omega_decided
#print axioms Mettapedia.Algebra.Order.Infinitesimal.one_lt_omega_semantic
#print axioms Mettapedia.Algebra.Order.Infinitesimal.zero_lt_omega_by_proof
#print axioms Mettapedia.Algebra.Order.Infinitesimal.omega_not_lt_one
#print axioms Mettapedia.Algebra.Order.Infinitesimal.rational_cancellation_decided
#print axioms Mettapedia.Algebra.Order.Infinitesimal.mixed_levels_semantic
#print axioms Mettapedia.Algebra.Order.Infinitesimal.cancellation_semantic
