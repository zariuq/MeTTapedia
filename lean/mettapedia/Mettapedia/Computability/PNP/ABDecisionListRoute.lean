import Mettapedia.Computability.PNP.ABVisibleSurface
import Mettapedia.Computability.PNP.ExactABDecisionListFamily

/-!
# P vs NP grassroots: pull back the raw `(a, b)` decision-list route

This file isolates one reusable route certificate:

* start with a family on the reduced raw visible surface `(a, b)`,
* realize that reduced family by fixed-order decision lists on the raw bits,
* pull it back along the projection from the exact surface `(z, a, b)`.

Once those ingredients are supplied, the exact-surface compression and
exact-recovery theorems follow immediately from the concrete raw-bit family
already defined on the exact post-switch surface.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {k : ℕ}

/-- An indexed predictor family on the reduced raw visible surface `(a, b)`. -/
abbrev ABVisibleSwitchedFamily (k : ℕ) (Index : Type*) :=
  IndexedPredictorFamily Index (ABVisibleSurface k)

/-- Fixed-order decision-list prediction on the reduced raw visible surface. -/
noncomputable def abDecisionListPredict
    (code : SharedAffineDecisionListCode (k + k))
    (x : ABVisibleSurface k) : Bool :=
  match firstActiveFeature? (abVisibleBits (k := k) x) with
  | some j => code.1 j
  | none => code.2

@[simp] theorem abDecisionListPredict_mk
    (code : SharedAffineDecisionListCode (k + k))
    (a b : BitVec k) :
    abDecisionListPredict (k := k) code (a, b) =
      match firstActiveFeature? (Fin.append a b) with
      | some j => code.1 j
      | none => code.2 := by
  simp [abDecisionListPredict, abVisibleBits]

theorem rawExactABDecisionListPredict_eq_abDecisionListPredict_comp_abVisibleData
    (code : SharedAffineDecisionListCode (k + k)) :
    rawExactABDecisionListPredict (Z := Z) (k := k) code =
      fun u => abDecisionListPredict (k := k) code (abVisibleData u) := by
  funext u
  cases u
  rfl

/-- Reduced-surface family realized by fixed-order decision lists on the raw
visible bits `(a, b)`. -/
def RealizedByABDecisionListFamily
    {Index : Type*} (H : ABVisibleSwitchedFamily k Index) : Prop :=
  ∀ i, ∃ code : SharedAffineDecisionListCode (k + k),
    H.predict i = abDecisionListPredict (k := k) code

/-- Invariance under the reduced raw visible quotient `(a, b)`. -/
def ABVisibleInvariant
    {Index : Type*} (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  ∀ i u v, abVisibleData u = abVisibleData v → G.predict i u = G.predict i v

section Lift

variable [Inhabited Z]

/-- A canonical section of the reduced raw visible projection, using a default
latent datum. -/
def abVisibleSection (x : ABVisibleSurface k) : ExactVisiblePostSwitchSurface Z k :=
  ⟨default, x.1, x.2⟩

@[simp] theorem abVisibleData_section (x : ABVisibleSurface k) :
    abVisibleData (abVisibleSection (Z := Z) (k := k) x) = x := by
  cases x
  rfl

/-- Lift an exact-surface family to the reduced raw visible surface by choosing
the canonical section. -/
def liftToABVisibleFamily
    {Index : Type*} (G : ExactVisibleSwitchedFamily Z k Index) :
    ABVisibleSwitchedFamily k Index where
  predict i x := G.predict i (abVisibleSection (Z := Z) (k := k) x)

theorem factorsThrough_abVisibleData_of_invariant
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G) :
    G.FactorsThrough abVisibleData (liftToABVisibleFamily (Z := Z) (k := k) G) := by
  intro i u
  change G.predict i u = G.predict i (abVisibleSection (Z := Z) (k := k) (abVisibleData u))
  apply hinv i u (abVisibleSection (Z := Z) (k := k) (abVisibleData u))
  cases u
  rfl

end Lift

theorem realizedByRawExactABDecisionListFamily_of_factorsThrough_ab
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedByABDecisionListFamily (k := k) H) :
    RealizedByRawExactABDecisionListFamily (Z := Z) (k := k) G := by
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨code, ?_⟩
  funext u
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = abDecisionListPredict (k := k) code (abVisibleData u) := by
          exact congrFun hi (abVisibleData u)
    _ = rawExactABDecisionListPredict (Z := Z) (k := k) code u := by
          symm
          exact congrFun
            (rawExactABDecisionListPredict_eq_abDecisionListPredict_comp_abVisibleData
              (Z := Z) (k := k) code) u

theorem exactVisibleCompressionTarget_of_factorsThrough_ab_and_decisionList
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedByABDecisionListFamily (k := k) H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (k + k + 1) := by
  exact exactVisibleCompressionTarget_of_realizedByRawExactABDecisionListFamily
    (Z := Z) (k := k)
    (realizedByRawExactABDecisionListFamily_of_factorsThrough_ab
      (Z := Z) (k := k) hfactor hreal)

theorem exactVisibleCompressionTarget_of_factorsThrough_ab_and_decisionList_twoMul
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedByABDecisionListFamily (k := k) H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * k + 1) := by
  simpa [two_mul, Nat.mul_comm, Nat.add_assoc] using
    exactVisibleCompressionTarget_of_factorsThrough_ab_and_decisionList
      (Z := Z) (k := k) hfactor hreal

section Lift

variable [Inhabited Z]

theorem exactVisibleCompressionTarget_of_invariant_and_decisionList
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedByABDecisionListFamily (k := k) (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (k + k + 1) := by
  exact exactVisibleCompressionTarget_of_factorsThrough_ab_and_decisionList
    (Z := Z) (k := k)
    (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
    hreal

theorem exactVisibleCompressionTarget_of_invariant_and_decisionList_twoMul
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedByABDecisionListFamily (k := k) (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * k + 1) := by
  simpa [two_mul, Nat.mul_comm, Nat.add_assoc] using
    exactVisibleCompressionTarget_of_invariant_and_decisionList
      (Z := Z) (k := k) hinv hreal

end Lift

theorem rawExactABDecisionListRecoveryLowerBound_of_factorsThrough_ab
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SharedAffineDecisionListCode (k + k),
      target = fun u => abDecisionListPredict (k := k) code (abVisibleData u))
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (rawExactABDecisionListBitFamily Z k).toEncodedFamily.BadCodes target,
        agreementMass μ target ((rawExactABDecisionListBitFamily Z k).decode c.1) ≤ q) :
    1 - (2 ^ (k + k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactABDecisionListBitFamily Z k).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, hcode⟩
  refine rawExactABDecisionListRecoveryLowerBound
    (Z := Z) (k := k) (μ := μ) (target := target) (m := m) ?_ hq
  refine ⟨code, ?_⟩
  rw [hcode]
  exact rawExactABDecisionListPredict_eq_abDecisionListPredict_comp_abVisibleData
    (Z := Z) (k := k) code

theorem rawExactABDecisionListRecoveryLowerBound_of_factorsThrough_ab_twoMul
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SharedAffineDecisionListCode (k + k),
      target = fun u => abDecisionListPredict (k := k) code (abVisibleData u))
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (rawExactABDecisionListBitFamily Z k).toEncodedFamily.BadCodes target,
        agreementMass μ target ((rawExactABDecisionListBitFamily Z k).decode c.1) ≤ q) :
    1 - (2 ^ (2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactABDecisionListBitFamily Z k).bitExactRecoverySampleMass μ target m := by
  simpa [two_mul, Nat.mul_comm, Nat.add_assoc] using
    rawExactABDecisionListRecoveryLowerBound_of_factorsThrough_ab
      (Z := Z) (k := k) (μ := μ) (target := target) (m := m) htarget hq

end

end Mettapedia.Computability.PNP
