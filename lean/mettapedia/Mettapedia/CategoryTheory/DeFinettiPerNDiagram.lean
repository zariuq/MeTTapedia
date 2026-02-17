import Mettapedia.CategoryTheory.DeFinettiLimitConePackage
import Mettapedia.CategoryTheory.DeFinettiPermutationCone
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.GroupTheory.Perm.Basic

/-!
# Per-`n` Diagram and Cone API for Categorical de Finetti

This file introduces a lightweight, per-`n` permutation diagram surface:
- a concrete prefix-law diagram object family,
- a cone law over finite permutations,
- and a lightweight `IsLimit`-style proposition that reuses the existing
  latent-`Theta` universal mediator API.

No quantitative rates are introduced here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open MeasureTheory
open ProbabilityTheory
open Mettapedia.Logic.Exchangeability
open Mettapedia.ProbabilityTheory.HigherOrderProbability
open CategoryTheory
open CategoryTheory.Limits

variable {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Prefix-law object at horizon `n`: distributions on `Fin n → Bool` encoded
as nonnegative masses. -/
abbrev BoolPrefixObj (n : ℕ) : Type :=
  (Fin n → Bool) → ENNReal

/-- Finite-permutation action on prefix-law objects by precomposition on tuples. -/
def boolPrefixPermAction {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (f : BoolPrefixObj n) : BoolPrefixObj n :=
  fun xs => f (permuteBoolTuple σ xs)

/-- Generic per-`n` de Finetti permutation diagram signature. -/
structure DeFinettiPerNDiagram where
  Obj : ℕ → Type
  permAction : ∀ {n : ℕ}, Equiv.Perm (Fin n) → Obj n → Obj n

/-- Canonical per-`n` Boolean-prefix diagram. -/
def deFinettiBoolPrefixDiagram : DeFinettiPerNDiagram where
  Obj := BoolPrefixObj
  permAction := @boolPrefixPermAction

/-- Cone over a per-`n` de Finetti diagram:
each leg is invariant under finite-coordinate permutation actions. -/
structure DeFinettiPerNCone (D : DeFinettiPerNDiagram) where
  leg : ∀ n : ℕ, D.Obj n
  commute : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)), D.permAction σ (leg n) = leg n

/-- Process-law cone condition specialized to the canonical Boolean-prefix diagram. -/
def IsPrefixLawCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω) : Prop :=
  ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
    boolPrefixPermAction σ (prefixLaw X μ n) = prefixLaw X μ n

/-- The specialized cone condition is equivalent to the existing permutation-cone
exchangeability interface. -/
theorem isPrefixLawCone_iff_exchangeablePrefixCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω) :
    IsPrefixLawCone (Ω := Ω) X μ ↔ ExchangeablePrefixCone X μ := by
  constructor
  · intro h n σ xs
    have hfun := congrArg (fun f => f xs) (h n σ)
    simpa [IsPrefixLawCone, boolPrefixPermAction] using hfun.symm
  · intro h n σ
    funext xs
    simpa [IsPrefixLawCone, boolPrefixPermAction] using (h n σ xs).symm

/-- Build a concrete per-`n` cone object from exchangeability. -/
def prefixLawConeOfExchangeable
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hcone : ExchangeablePrefixCone X μ) :
    DeFinettiPerNCone deFinettiBoolPrefixDiagram where
  leg n := prefixLaw X μ n
  commute n σ := by
    funext xs
    simpa [deFinettiBoolPrefixDiagram, boolPrefixPermAction] using (hcone n σ xs).symm

/-- Lightweight `IsLimit`-style proposition for the per-`n` de Finetti route:
the universal mediator API at kernel level. -/
def DeFinettiPerNIsLimit
    (X : ℕ → Ω → Bool) : Prop :=
  KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X

/-- Forward bridge: any lightweight package witness induces the per-`n`
`IsLimit`-style witness. -/
theorem deFinettiLimitConePackage_to_perNIsLimit
    (X : ℕ → Ω → Bool)
    (pkg : DeFinettiLimitConePackage (Y := Y) (Ω := Ω) X) :
    DeFinettiPerNIsLimit (Y := Y) (Ω := Ω) X :=
  pkg.universal

/-- Canonical per-`n` `IsLimit`-style witness from the default package. -/
theorem deFinettiPerNIsLimit_default
    (X : ℕ → Ω → Bool) :
    DeFinettiPerNIsLimit (Y := Y) (Ω := Ω) X := by
  exact (deFinettiLimitConePackage_default (Y := Y) (Ω := Ω) X).universal

/-! ## True Category-Theoretic Per-`n` Diagram/Cone Packaging -/

/-- Index category at horizon `n`: one object with endomorphisms
`Equiv.Perm (Fin n)`. -/
abbrev PerNPermIndex (n : ℕ) : Type :=
  CategoryTheory.SingleObj (Equiv.Perm (Fin n))

/-- The unique object in the per-`n` permutation index category. -/
abbrev perNPermStar (n : ℕ) : PerNPermIndex n :=
  CategoryTheory.SingleObj.star (Equiv.Perm (Fin n))

/-- True categorical per-`n` diagram:
the permutation index category acts on prefix-law objects
`(Fin n → Bool) → ENNReal`. -/
def perNPrefixDiagramFunctor (n : ℕ) :
    CategoryTheory.Functor (PerNPermIndex n) Type where
  obj _ := BoolPrefixObj n
  map σ := boolPrefixPermAction σ.symm
  map_id x := by
    funext f xs
    rfl
  map_comp f g := by
    funext h xs
    rfl

/-- Explicit endomorphism map of the true per-`n` diagram at the unique object. -/
def perNPrefixDiagramMap (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    BoolPrefixObj n → BoolPrefixObj n :=
  (perNPrefixDiagramFunctor n).map (X := perNPermStar n) (Y := perNPermStar n) σ

/-- Per-`n` categorical cone-commutativity for the concrete prefix law. -/
def PerNPrefixLawConeCommutes
    (X : ℕ → Ω → Bool) (μ : Measure Ω) (n : ℕ) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    perNPrefixDiagramMap n σ (prefixLaw X μ n) = prefixLaw X μ n

/-- Build a true `CategoryTheory.Limits.Cone` for a fixed horizon `n` from
the per-`n` commutativity equalities. -/
def perNPrefixLawConeOfCommutes
    (X : ℕ → Ω → Bool) (μ : Measure Ω) (n : ℕ)
    (hcomm : PerNPrefixLawConeCommutes (Ω := Ω) X μ n) :
    CategoryTheory.Limits.Cone (perNPrefixDiagramFunctor n) where
  pt := PUnit
  π :=
    { app := fun _ _ => prefixLaw X μ n
      naturality := by
        intro j j' σ
        cases j
        cases j'
        funext u
        simpa [perNPrefixDiagramMap] using (hcomm σ).symm }

/-- Cone-wrapper sanity check: the cone built from commutativity has the
expected pointwise leg at the unique object. -/
theorem perNPrefixLawConeOfCommutes_leg
    (X : ℕ → Ω → Bool) (μ : Measure Ω) (n : ℕ)
    (hcomm : PerNPrefixLawConeCommutes (Ω := Ω) X μ n) :
    (perNPrefixLawConeOfCommutes (Ω := Ω) X μ n hcomm).π.app (perNPermStar n) PUnit.unit
      = prefixLaw X μ n := by
  rfl

/-- Per-`n` categorical cone commutativity is equivalent to the original
non-categorical per-`n` prefix-law permutation invariance. -/
theorem perNPrefixLawConeCommutes_iff_prefixLawInvariance
    (X : ℕ → Ω → Bool) (μ : Measure Ω) (n : ℕ) :
    PerNPrefixLawConeCommutes (Ω := Ω) X μ n ↔
      ∀ σ : Equiv.Perm (Fin n),
        boolPrefixPermAction σ (prefixLaw X μ n) = prefixLaw X μ n := by
  constructor
  · intro hcomm σ
    simpa [PerNPrefixLawConeCommutes, perNPrefixDiagramMap, perNPermStar] using hcomm σ.symm
  · intro hperm σ
    simpa [PerNPrefixLawConeCommutes, perNPrefixDiagramMap, perNPermStar] using hperm σ.symm

/-- Global equivalence: the true categorical per-`n` cone-commutativity family
is equivalent to the existing `IsPrefixLawCone` predicate. -/
theorem isPrefixLawCone_iff_perNPrefixLawConeCommutes
    (X : ℕ → Ω → Bool) (μ : Measure Ω) :
    IsPrefixLawCone (Ω := Ω) X μ ↔
      ∀ n : ℕ, PerNPrefixLawConeCommutes (Ω := Ω) X μ n := by
  constructor
  · intro h n σ
    simpa [IsPrefixLawCone, PerNPrefixLawConeCommutes, perNPrefixDiagramMap, perNPermStar] using
      h n σ.symm
  · intro h n σ
    simpa [IsPrefixLawCone, PerNPrefixLawConeCommutes, perNPrefixDiagramMap, perNPermStar] using
      h n σ.symm

/-- Fixed-point object for the true per-`n` permutation diagram. -/
def PerNPrefixFixedPoints (n : ℕ) : Type :=
  { f : BoolPrefixObj n // ∀ σ : Equiv.Perm (Fin n), perNPrefixDiagramMap n σ f = f }

/-- Canonical fixed-point cone for the true per-`n` diagram. -/
def perNPrefixFixedPointsCone (n : ℕ) : Cone (perNPrefixDiagramFunctor n) where
  pt := PerNPrefixFixedPoints n
  π :=
    { app := fun _ f => f.1
      naturality := by
        intro j j' σ
        cases j
        cases j'
        funext f
        simpa [perNPrefixDiagramMap] using (f.2 σ).symm }

/-- The fixed-point cone is a true `CategoryTheory.Limits.IsLimit` witness
for the per-`n` permutation diagram. -/
def perNPrefixFixedPointsConeIsLimit (n : ℕ) :
    CategoryTheory.Limits.IsLimit (perNPrefixFixedPointsCone n) where
  lift s x := by
    refine ⟨s.π.app (perNPermStar n) x, ?_⟩
    intro σ
    have hnat := congrArg (fun k => k x)
      (s.π.naturality (X := perNPermStar n) (Y := perNPermStar n) (f := σ))
    simpa [perNPrefixDiagramMap] using hnat.symm
  fac s j := by
    cases j
    funext x
    rfl
  uniq s m hm := by
    funext x
    apply Subtype.ext
    have hcomp := congrArg (fun k => k x) (hm (perNPermStar n))
    simpa using hcomp

/-- True limit-cone packaging for the per-`n` permutation diagram. -/
def perNPrefixDiagramLimitCone (n : ℕ) :
    CategoryTheory.Limits.LimitCone (perNPrefixDiagramFunctor n) where
  cone := perNPrefixFixedPointsCone n
  isLimit := perNPrefixFixedPointsConeIsLimit n

/-- Bridge theorem to avoid API ambiguity:
the lightweight `DeFinettiPerNIsLimit` naming implies availability of the true
per-`n` `LimitCone` packaging. -/
theorem deFinettiPerNIsLimit_to_trueLimitCone
    (X : ℕ → Ω → Bool) (n : ℕ)
    (_h : DeFinettiPerNIsLimit (Y := Y) (Ω := Ω) X) :
    Nonempty (CategoryTheory.Limits.LimitCone (perNPrefixDiagramFunctor n)) :=
  ⟨perNPrefixDiagramLimitCone n⟩

/-- Has-limit style packaging for automation on the true per-`n` diagram. -/
theorem hasLimit_perNPrefixDiagramFunctor (n : ℕ) :
    CategoryTheory.Limits.HasLimit (perNPrefixDiagramFunctor n) := by
  exact ⟨⟨perNPrefixDiagramLimitCone n⟩⟩

/-- Instance form of `hasLimit_perNPrefixDiagramFunctor` for downstream typeclass
automation. -/
instance instHasLimitPerNPrefixDiagramFunctor (n : ℕ) :
    CategoryTheory.Limits.HasLimit (perNPrefixDiagramFunctor n) :=
  hasLimit_perNPrefixDiagramFunctor n

end Mettapedia.CategoryTheory
