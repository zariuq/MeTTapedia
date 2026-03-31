import Mettapedia.Computability.PNP.ExactABDecisionListFamily

/-!
# P vs NP grassroots: decision-list families on `(z,a,b)` via a shared `z` extractor

The paper's post-switch local input is `u = (z, a, b)`, where `z` is obtained
from one fixed shared feature extractor on the masked block and `(a, b)` are the
VV labels.  The current raw `(a, b)` route ignores `z`; this file adds the next
candidate-facing layer by reintroducing a fixed shared binary summary of `z`.

Given a shared extractor `zfeat : Z → BitVec r`, we concatenate

* `zfeat z`,
* the retained VV column bits `a`,
* the side-channel bits `b`,

and run the same fixed-order decision-list family on that combined bit vector.
The resulting exact-surface budget is `r + 2k + 1`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ}

/-- The exact visible bit surface obtained from one shared `z` extractor
together with the raw `(a, b)` VV data. -/
def exactZABVisibleData
    (zfeat : Z → BitVec r)
    (u : ExactVisiblePostSwitchSurface Z k) : BitVec (r + (k + k)) :=
  Fin.append (zfeat u.z) (exactABVisibleData (Z := Z) (k := k) u)

@[simp] theorem exactZABVisibleData_tiInputMap
    (zfeat : Z → BitVec r)
    (u : ExactVisiblePostSwitchSurface Z k) :
    exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat (tiInputMap u) =
      Fin.append (zfeat u.z) (Fin.append u.a (vvToggle u.a u.b)) := by
  cases u
  rfl

/-- Fixed-order decision-list prediction on the exact visible bits
`(zfeat z, a, b)`. -/
noncomputable def rawExactZABDecisionListPredict
    (zfeat : Z → BitVec r)
    (code : SharedAffineDecisionListCode (r + (k + k)))
    (u : ExactVisiblePostSwitchSurface Z k) : Bool :=
  match firstActiveFeature? (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) with
  | some j => code.1 j
  | none => code.2

/-- The corresponding exact-surface bit family. -/
noncomputable def rawExactZABDecisionListBitFamily
    (Z : Type*) (r k : ℕ) (zfeat : Z → BitVec r) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) (r + (k + k) + 1) where
  decode raw u :=
    let code := (sharedAffineDecisionListCodeEquivBitCode (r + (k + k))).symm raw
    rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code u

@[simp] theorem rawExactZABDecisionListBitFamily_decode_code
    (zfeat : Z → BitVec r)
    (code : SharedAffineDecisionListCode (r + (k + k))) :
    (rawExactZABDecisionListBitFamily Z r k zfeat).decode
        (sharedAffineDecisionListCodeEquivBitCode (r + (k + k)) code) =
      rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code := by
  funext u
  simp [rawExactZABDecisionListBitFamily, sharedAffineDecisionListCodeEquivBitCode]

/-- Exact-surface families realized by fixed-order decision lists on the shared
visible bits `(zfeat z, a, b)`. -/
def RealizedByRawExactZABDecisionListFamily
    {Index : Type*}
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i, ∃ code : SharedAffineDecisionListCode (r + (k + k)),
    G.predict i = rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code

theorem exactVisibleCompressionTarget_of_realizedByRawExactZABDecisionListFamily
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (zfeat : Z → BitVec r)
    (hreal :
      RealizedByRawExactZABDecisionListFamily (Z := Z) (r := r) (k := k) zfeat G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + (k + k) + 1) := by
  refine ⟨rawExactZABDecisionListBitFamily Z r k zfeat, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedAffineDecisionListCodeEquivBitCode (r + (k + k)) code, ?_⟩
  exact (rawExactZABDecisionListBitFamily_decode_code
    (Z := Z) (r := r) (k := k) zfeat code).trans hi.symm

theorem exactVisibleCompressionTarget_of_realizedByRawExactZABDecisionListFamily_twoMul
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (zfeat : Z → BitVec r)
    (hreal :
      RealizedByRawExactZABDecisionListFamily (Z := Z) (r := r) (k := k) zfeat G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  simpa [two_mul, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    exactVisibleCompressionTarget_of_realizedByRawExactZABDecisionListFamily
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat hreal

theorem rawExactZABDecisionListRecoveryLowerBound
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SharedAffineDecisionListCode (r + (k + k)),
      target = rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code)
    {q : ℝ≥0∞}
    (hq :
      ∀ c :
        (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes target,
        agreementMass μ target
          ((rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1) ≤ q) :
    1 - (2 ^ (r + (k + k) + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine exactVisible_bitFamily_exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le_of_fintype
    (Z := Z) (k := k) (s := r + (k + k) + 1)
    (F := rawExactZABDecisionListBitFamily Z r k zfeat)
    (μ := μ)
    (target := rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code)
    (m := m)
    ?_
    hq
  refine ⟨sharedAffineDecisionListCodeEquivBitCode (r + (k + k)) code, ?_⟩
  exact rawExactZABDecisionListBitFamily_decode_code
    (Z := Z) (r := r) (k := k) zfeat code

theorem rawExactZABDecisionListRecoveryLowerBound_twoMul
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SharedAffineDecisionListCode (r + (k + k)),
      target = rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code)
    {q : ℝ≥0∞}
    (hq :
      ∀ c :
        (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes target,
        agreementMass μ target
          ((rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1) ≤ q) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass μ target m := by
  simpa [two_mul, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    rawExactZABDecisionListRecoveryLowerBound
      (Z := Z) (r := r) (k := k) zfeat (μ := μ) (target := target) (m := m) htarget hq

end

end Mettapedia.Computability.PNP
