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

/-! ## Exchangeability-to-Limit Factorization and Uniqueness -/

/-- The exchangeability-induced source cone at horizon `n`. -/
def exchangeablePerNSourceCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω) (n : ℕ)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ) :
    CategoryTheory.Limits.Cone (perNPrefixDiagramFunctor n) :=
  perNPrefixLawConeOfCommutes (Ω := Ω) X μ n
    ((isPrefixLawCone_iff_perNPrefixLawConeCommutes (Ω := Ω) X μ).1 hcone n)

/-- The canonical mediator from the exchangeability-induced cone to the fixed-point
limit cone at horizon `n`. -/
def exchangeablePerNLimitMediator
    (X : ℕ → Ω → Bool) (μ : Measure Ω) (n : ℕ)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ) :
    PUnit ⟶ PerNPrefixFixedPoints n :=
  (perNPrefixFixedPointsConeIsLimit n).lift
    (exchangeablePerNSourceCone (Ω := Ω) X μ n hcone)

/-- Step 1 (factorization): exchangeability-induced per-`n` cone factors through
the fixed-point limit object via the canonical mediator. -/
theorem exchangeablePerNLimitMediator_fac
    (X : ℕ → Ω → Bool) (μ : Measure Ω) (n : ℕ)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ)
    (j : PerNPermIndex n) :
    CategoryTheory.CategoryStruct.comp
      (exchangeablePerNLimitMediator (Ω := Ω) X μ n hcone)
      ((perNPrefixFixedPointsCone n).π.app j) =
    (exchangeablePerNSourceCone (Ω := Ω) X μ n hcone).π.app j := by
  exact (perNPrefixFixedPointsConeIsLimit n).fac
    (exchangeablePerNSourceCone (Ω := Ω) X μ n hcone) j

/-- Step 2 (uniqueness): the canonical mediator is the unique map with the same
cone-factorization equations, by `IsLimit.uniq`. -/
theorem exchangeablePerNLimitMediator_unique
    (X : ℕ → Ω → Bool) (μ : Measure Ω) (n : ℕ)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ)
    (m : PUnit ⟶ PerNPrefixFixedPoints n)
    (hm :
      ∀ j : PerNPermIndex n,
        CategoryTheory.CategoryStruct.comp m ((perNPrefixFixedPointsCone n).π.app j) =
          (exchangeablePerNSourceCone (Ω := Ω) X μ n hcone).π.app j) :
    m = exchangeablePerNLimitMediator (Ω := Ω) X μ n hcone := by
  exact (perNPrefixFixedPointsConeIsLimit n).uniq
    (exchangeablePerNSourceCone (Ω := Ω) X μ n hcone) m hm

/-- Predicate packaging the per-`n` limit-mediator uniqueness schema. -/
def ExchangeablePerNLimitMediatorUnique
    (X : ℕ → Ω → Bool) : Prop :=
  ∀ (μ : Measure Ω) (n : ℕ) (hcone : IsPrefixLawCone (Ω := Ω) X μ)
    (m : PUnit ⟶ PerNPrefixFixedPoints n),
      (∀ j : PerNPermIndex n,
        CategoryTheory.CategoryStruct.comp m ((perNPrefixFixedPointsCone n).π.app j) =
          (exchangeablePerNSourceCone (Ω := Ω) X μ n hcone).π.app j) →
      m = exchangeablePerNLimitMediator (Ω := Ω) X μ n hcone

/-- Canonical derivation of per-`n` mediator uniqueness from the true `IsLimit`
construction. -/
theorem exchangeablePerNLimitMediatorUnique_default
    (X : ℕ → Ω → Bool) :
    ExchangeablePerNLimitMediatorUnique (Ω := Ω) X := by
  intro μ n hcone m hm
  exact exchangeablePerNLimitMediator_unique (Ω := Ω) X μ n hcone m hm

/-- Global cross-`n` categorical packaging over the family of per-`n` diagrams.
The package stores one prefix-law cone witness and a mediator family with
factorization/uniqueness against the canonical source cones induced by that witness. -/
structure ExchangeableCrossNLimitPackage
    (X : ℕ → Ω → Bool) (μ : Measure Ω) where
  hcone : IsPrefixLawCone (Ω := Ω) X μ
  mediator : ∀ n : ℕ, PUnit ⟶ PerNPrefixFixedPoints n
  fac : ∀ (n : ℕ) (j : PerNPermIndex n),
    CategoryTheory.CategoryStruct.comp (mediator n) ((perNPrefixFixedPointsCone n).π.app j) =
      (exchangeablePerNSourceCone (Ω := Ω) X μ n hcone).π.app j
  uniq : ∀ (n : ℕ) (m : PUnit ⟶ PerNPrefixFixedPoints n),
    (∀ j : PerNPermIndex n,
      CategoryTheory.CategoryStruct.comp m ((perNPrefixFixedPointsCone n).π.app j) =
        (exchangeablePerNSourceCone (Ω := Ω) X μ n hcone).π.app j) →
      m = mediator n

/-- Cross-`n` package from a per-`n` uniqueness package plus prefix-law
exchangeability. This definition uses the uniqueness package nontrivially in `uniq`. -/
def exchangeableCrossNLimitPackage_of_isPrefixLawCone_of_perNUnique
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ)
    (huniq : ExchangeablePerNLimitMediatorUnique (Ω := Ω) X) :
    ExchangeableCrossNLimitPackage (Ω := Ω) X μ := by
  refine ⟨hcone, ?_, ?_, ?_⟩
  · intro n
    exact exchangeablePerNLimitMediator (Ω := Ω) X μ n hcone
  · intro n j
    exact exchangeablePerNLimitMediator_fac (Ω := Ω) X μ n hcone j
  · intro n m hm
    exact huniq μ n hcone m hm

/-- Default cross-`n` package from exchangeability, via the canonical per-`n`
uniqueness theorem. -/
def exchangeableCrossNLimitPackage_of_isPrefixLawCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ) :
    ExchangeableCrossNLimitPackage (Ω := Ω) X μ :=
  exchangeableCrossNLimitPackage_of_isPrefixLawCone_of_perNUnique
    (Ω := Ω) X μ hcone (exchangeablePerNLimitMediatorUnique_default (Ω := Ω) X)

/-- Substantive equivalence: per-`n` mediator uniqueness package is equivalent to
having a coherent cross-`n` package family for every exchangeable prefix-law cone. -/
theorem exchangeablePerNLimitMediatorUnique_iff_crossNPackageFamily
    (X : ℕ → Ω → Bool) :
    ExchangeablePerNLimitMediatorUnique (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) := by
  constructor
  · intro huniq μ hcone
    exact ⟨exchangeableCrossNLimitPackage_of_isPrefixLawCone_of_perNUnique
      (Ω := Ω) X μ hcone huniq⟩
  · intro hpack μ n hcone m hm
    rcases hpack μ hcone with ⟨pkg⟩
    calc
      m = pkg.mediator n := pkg.uniq n m hm
      _ = exchangeablePerNLimitMediator (Ω := Ω) X μ n hcone := by
        symm
        exact pkg.uniq n
          (exchangeablePerNLimitMediator (Ω := Ω) X μ n hcone)
          (exchangeablePerNLimitMediator_fac (Ω := Ω) X μ n hcone)

/-- Backward-compatible alias for the previous theorem name.
Prefer `exchangeablePerNLimitMediatorUnique_iff_crossNPackageFamily`. -/
@[deprecated exchangeablePerNLimitMediatorUnique_iff_crossNPackageFamily
  (since := "2026-02-17")]
theorem exchangeablePerNLimitMediatorUnique_iff_crossNLimitPackageFamily
    (X : ℕ → Ω → Bool) :
    ExchangeablePerNLimitMediatorUnique (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) :=
  exchangeablePerNLimitMediatorUnique_iff_crossNPackageFamily (Ω := Ω) X

/-- Non-essential but useful check theorem:
under the cross-`n` package, any mediator satisfying cone equations at level `n`
coincides with the canonical mediator at level `n`. -/
theorem exchangeableCrossNLimitPackage_mediator_eq_of_fac
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (pkg : ExchangeableCrossNLimitPackage (Ω := Ω) X μ)
    (n : ℕ) (m : PUnit ⟶ PerNPrefixFixedPoints n)
    (hm :
      ∀ j : PerNPermIndex n,
        CategoryTheory.CategoryStruct.comp m ((perNPrefixFixedPointsCone n).π.app j) =
          (exchangeablePerNSourceCone (Ω := Ω) X μ n pkg.hcone).π.app j) :
    m = pkg.mediator n :=
  pkg.uniq n m hm

/-- Non-essential sanity theorem: within a cross-`n` package, any two mediators
at horizon `n` satisfying the same factorization equations are equal. -/
theorem exchangeableCrossNLimitPackage_mediators_eq_of_fac
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (pkg : ExchangeableCrossNLimitPackage (Ω := Ω) X μ)
    (n : ℕ) (m₁ m₂ : PUnit ⟶ PerNPrefixFixedPoints n)
    (hm₁ :
      ∀ j : PerNPermIndex n,
        CategoryTheory.CategoryStruct.comp m₁ ((perNPrefixFixedPointsCone n).π.app j) =
          (exchangeablePerNSourceCone (Ω := Ω) X μ n pkg.hcone).π.app j)
    (hm₂ :
      ∀ j : PerNPermIndex n,
        CategoryTheory.CategoryStruct.comp m₂ ((perNPrefixFixedPointsCone n).π.app j) =
          (exchangeablePerNSourceCone (Ω := Ω) X μ n pkg.hcone).π.app j) :
    m₁ = m₂ := by
  calc
    m₁ = pkg.mediator n := exchangeableCrossNLimitPackage_mediator_eq_of_fac (Ω := Ω) X μ pkg n m₁ hm₁
    _ = m₂ := (exchangeableCrossNLimitPackage_mediator_eq_of_fac (Ω := Ω) X μ pkg n m₂ hm₂).symm

/-- Strong bridge: kernel-level universal mediator API is equivalent, in one hop,
to the global cross-`n` package family. -/
theorem kernelLatentThetaUniversalMediator_iff_crossNPackageFamily
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) := by
  constructor
  · intro _ μ hcone
    exact ⟨exchangeableCrossNLimitPackage_of_isPrefixLawCone
      (Ω := Ω) X μ hcone⟩
  · intro _
    exact deFinettiPerNIsLimit_default (Y := Y) (Ω := Ω) X

/-- Backward-compatible alias for the previous theorem name.
Prefer `kernelLatentThetaUniversalMediator_iff_crossNPackageFamily`. -/
@[deprecated kernelLatentThetaUniversalMediator_iff_crossNPackageFamily
  (since := "2026-02-17")]
theorem kernelLatentThetaUniversalMediator_iff_crossNLimitPackageFamily
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) :=
  kernelLatentThetaUniversalMediator_iff_crossNPackageFamily (Y := Y) (Ω := Ω) X

/-- Step 3 (rewrite bridge): connect the uniqueness theorem to the kernel-level
universal mediator API as a substantive equivalence. -/
theorem kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      ExchangeablePerNLimitMediatorUnique (Ω := Ω) X := by
  calc
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
        (∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
          Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ)) :=
      kernelLatentThetaUniversalMediator_iff_crossNPackageFamily
        (Y := Y) (Ω := Ω) X
    _ ↔ ExchangeablePerNLimitMediatorUnique (Ω := Ω) X :=
      (exchangeablePerNLimitMediatorUnique_iff_crossNPackageFamily
        (Ω := Ω) X).symm

end Mettapedia.CategoryTheory
