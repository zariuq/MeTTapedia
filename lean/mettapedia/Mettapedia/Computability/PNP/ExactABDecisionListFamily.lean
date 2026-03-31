import Mettapedia.Computability.PNP.SharedAffineFeatureFamilies
import Mathlib.Data.Fin.Tuple.Basic

/-!
# P vs NP grassroots: a raw exact-surface decision-list family on `(a, b)`

This file makes the current shared-feature story fully concrete on the exact
post-switch surface. The shared extractor is simply the raw visible bit vector
obtained by concatenating the retained VV column bits `a` with the side-channel
bits `b`.

On top of that fixed extractor we define the fixed-order decision-list family:

* scan the raw bits of `(a, b)` in a fixed order,
* if the first active bit is at position `j`, return the response bit attached
  to `j`,
* otherwise return one default output bit.

The resulting exact-surface family has explicit code budget `2k + 1`, and the
weighted exact-recovery theorem applies to it immediately.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {k : ℕ}

/-- The canonical raw visible extractor on the exact post-switch surface:
concatenate the retained VV column bits `a` with the side-channel bits `b`. -/
def exactABVisibleData (u : ExactVisiblePostSwitchSurface Z k) : BitVec (k + k) :=
  Fin.append u.a u.b

@[simp] theorem exactABVisibleData_tiInputMap (u : ExactVisiblePostSwitchSurface Z k) :
    exactABVisibleData (tiInputMap u) = Fin.append u.a (vvToggle u.a u.b) := by
  rfl

/-- Fixed-order decision-list prediction on the raw exact visible bits `(a, b)`. -/
noncomputable def rawExactABDecisionListPredict
    (code : SharedAffineDecisionListCode (k + k))
    (u : ExactVisiblePostSwitchSurface Z k) : Bool :=
  match firstActiveFeature? (exactABVisibleData u) with
  | some j => code.1 j
  | none => code.2

/-- The corresponding raw-bit exact-surface family with budget `2k + 1`. -/
noncomputable def rawExactABDecisionListBitFamily (Z : Type*) (k : ℕ) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (k + k + 1) where
  decode raw u :=
    let code := (sharedAffineDecisionListCodeEquivBitCode (k + k)).symm raw
    rawExactABDecisionListPredict code u

@[simp] theorem rawExactABDecisionListBitFamily_decode_code
    (code : SharedAffineDecisionListCode (k + k)) :
    (rawExactABDecisionListBitFamily Z k).decode
        (sharedAffineDecisionListCodeEquivBitCode (k + k) code)
      = rawExactABDecisionListPredict code := by
  funext u
  simp [rawExactABDecisionListBitFamily, sharedAffineDecisionListCodeEquivBitCode]

/-- Exact switched families realized by a fixed-order decision list on the raw
exact visible bits `(a, b)`. -/
def RealizedByRawExactABDecisionListFamily
    {Index : Type*}
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i, ∃ code : SharedAffineDecisionListCode (k + k),
    G.predict i = rawExactABDecisionListPredict code

theorem exactVisibleCompressionTarget_of_realizedByRawExactABDecisionListFamily
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal : RealizedByRawExactABDecisionListFamily (Z := Z) (k := k) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (k + k + 1) := by
  refine ⟨rawExactABDecisionListBitFamily Z k, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedAffineDecisionListCodeEquivBitCode (k + k) code, ?_⟩
  exact (rawExactABDecisionListBitFamily_decode_code (Z := Z) (k := k) code).trans hi.symm

theorem exactVisibleCompressionTarget_of_realizedByRawExactABDecisionListFamily_twoMul
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal : RealizedByRawExactABDecisionListFamily (Z := Z) (k := k) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * k + 1) := by
  simpa [two_mul, Nat.mul_comm, Nat.add_assoc] using
    exactVisibleCompressionTarget_of_realizedByRawExactABDecisionListFamily
      (Z := Z) (k := k) (Index := Index) hreal

theorem rawExactABDecisionListRecoveryLowerBound
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SharedAffineDecisionListCode (k + k),
      target = rawExactABDecisionListPredict code)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (rawExactABDecisionListBitFamily Z k).toEncodedFamily.BadCodes target,
        agreementMass μ target ((rawExactABDecisionListBitFamily Z k).decode c.1) ≤ q) :
    1 - (2 ^ (k + k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactABDecisionListBitFamily Z k).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine exactVisible_bitFamily_exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le_of_fintype
    (F := rawExactABDecisionListBitFamily Z k)
    (μ := μ)
    (target := rawExactABDecisionListPredict code)
    (m := m)
    ?_
    hq
  refine ⟨sharedAffineDecisionListCodeEquivBitCode (k + k) code, ?_⟩
  exact rawExactABDecisionListBitFamily_decode_code (Z := Z) (k := k) code

theorem rawExactABDecisionListRecoveryLowerBound_twoMul
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SharedAffineDecisionListCode (k + k),
      target = rawExactABDecisionListPredict code)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (rawExactABDecisionListBitFamily Z k).toEncodedFamily.BadCodes target,
        agreementMass μ target ((rawExactABDecisionListBitFamily Z k).decode c.1) ≤ q) :
    1 - (2 ^ (2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactABDecisionListBitFamily Z k).bitExactRecoverySampleMass μ target m := by
  simpa [two_mul, Nat.mul_comm, Nat.add_assoc] using
    rawExactABDecisionListRecoveryLowerBound
      (Z := Z) (k := k) (μ := μ) (target := target) (m := m) htarget hq

end

end Mettapedia.Computability.PNP
