import Mettapedia.TypeTheory.DependentFamilyObserverFactorization

/-!
# Equality families over observations

Preserving selected values through an observation is weaker than preserving
the source equality family.  For `observe : Source → Target`, preservation of
equality fibres means that every source equality type is equivalent to the
corresponding target equality type.  This property is exactly injectivity of
the observation.

Equivalently, every source-anchored equality family factors through the
observation precisely when the observation is injective.  For a split
readout, this is also precisely exactness.  Consequently a deliberately lossy
extensional readout may support many dependent families while being unable to
transport source equality itself.

This result concerns Lean equality families.  It does not identify them with
an arbitrary object-language identity type, assume equality reflection, or
choose a proof-irrelevance policy.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.EqualityFamilyObserverFactorization

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.ExtensionalReadout

universe uSource uTarget

/-- An observation preserves source equality fibres when equality before and
after observation is equivalent at every pair of points. -/
structure EqualityFamilyFactorization
    {Source : Type uSource} {Target : Type uTarget}
    (observe : Source → Target) where
  identify : ∀ left right,
    (left = right) ≃ (observe left = observe right)

namespace EqualityFamilyFactorization

variable {Source : Type uSource} {Target : Type uTarget}
variable {observe : Source → Target}

/-- Every injective observation preserves equality fibres. -/
def ofInjective (injective : Function.Injective observe) :
    EqualityFamilyFactorization observe where
  identify := fun left right =>
    { toFun := congrArg observe
      invFun := fun sameObservation => injective sameObservation
      left_inv := by
        intro equality
        exact Subsingleton.elim _ _
      right_inv := by
        intro equality
        exact Subsingleton.elim _ _ }

/-- Equality-family preservation reflects target equality back to source
equality. -/
theorem reflectsEquality
    (factorization : EqualityFamilyFactorization observe)
    {left right : Source} :
    observe left = observe right → left = right :=
  factorization.identify left right |>.symm

/-- Hence every equality-family-preserving observation is injective. -/
theorem injective
    (factorization : EqualityFamilyFactorization observe) :
    Function.Injective observe := by
  intro left right sameObservation
  exact factorization.reflectsEquality sameObservation

/-- Equality-family factorization is exactly injectivity of the observation. -/
theorem nonempty_iff_injective (observe : Source → Target) :
    Nonempty (EqualityFamilyFactorization observe) ↔
      Function.Injective observe := by
  constructor
  · rintro ⟨factorization⟩
    exact factorization.injective
  · intro injective
    exact ⟨ofInjective injective⟩

/-- Lift equality-fibre preservation from proposition-valued equality to a
`Type`-valued family.  The lift is explicit because the generic dependent
family interface retains data-bearing fibres rather than ranging over
`Sort`. -/
def liftedIdentify
    (factorization : EqualityFamilyFactorization observe)
    (left right : Source) :
    PLift (left = right) ≃ PLift (observe left = observe right) where
  toFun := fun equality =>
    ⟨factorization.identify left right equality.down⟩
  invFun := fun equality =>
    ⟨(factorization.identify left right).symm equality.down⟩
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fun _ => Subsingleton.elim _ _

/-- Equality preservation supplies an ordinary family factorization for the
equality family anchored at any selected source point. -/
def anchored
    (factorization : EqualityFamilyFactorization observe) (anchor : Source) :
    FamilyFactorization observe (fun source => PLift (anchor = source)) where
  targetFamily := fun target => PLift (observe anchor = target)
  identify := factorization.liftedIdentify anchor

/-- If every anchored equality family factors through an observation, then
the observation is injective even when the target families of those
factorizations were chosen independently. -/
theorem injective_of_all_anchored_factorizations
    (allFactor : ∀ anchor,
      Nonempty
        (FamilyFactorization observe
          (fun source => PLift (anchor = source)))) :
    Function.Injective observe := by
  intro left right sameObservation
  obtain ⟨factorization⟩ := allFactor left
  exact ((factorization.fibreEquiv sameObservation).toFun ⟨rfl⟩).down

/-- The generic family-level criterion agrees with the direct equality-fibre
criterion: all anchored equality families factor exactly for injective
observations. -/
theorem all_anchored_nonempty_iff_injective (observe : Source → Target) :
    (∀ anchor,
        Nonempty
          (FamilyFactorization observe
            (fun source => PLift (anchor = source)))) ↔
      Function.Injective observe := by
  constructor
  · exact injective_of_all_anchored_factorizations
  · intro injective anchor
    exact ⟨(ofInjective injective).anchored anchor⟩

end EqualityFamilyFactorization

/-! ## Split-readout consequence -/

/-- A split extensional readout preserves every source equality fibre exactly
when the readout itself is exact. -/
theorem splitReadout_exact_iff_equalityFamilyFactorization
    {Source : Type uSource} {Target : Type uTarget}
    (readout : SplitReadout Source Target) :
    readout.Exact ↔
      Nonempty (EqualityFamilyFactorization readout.observe) := by
  rw [readout.exact_iff_faithful]
  exact
    (EqualityFamilyFactorization.nonempty_iff_injective
      readout.observe).symm

/-! ## Positive and negative controls -/

namespace Canary

/-- The identity observation preserves equality fibres. -/
def identityFactorization :
    EqualityFamilyFactorization (id : Bool → Bool) :=
  EqualityFamilyFactorization.ofInjective Function.injective_id

/-- A completion-like observation that identifies both Boolean source points. -/
def coarseBool : Bool → PUnit := fun _ => PUnit.unit

theorem coarseBool_not_injective : ¬ Function.Injective coarseBool := by
  intro injective
  exact Bool.false_ne_true (injective rfl)

/-- The coarse observation cannot preserve source equality fibres. -/
theorem coarseBool_does_not_factor_equality :
    ¬ Nonempty (EqualityFamilyFactorization coarseBool) := by
  rw [EqualityFamilyFactorization.nonempty_iff_injective]
  exact coarseBool_not_injective

/-- A split readout may be complete on visible values while refusing the
source equality family. -/
theorem split_complete_but_equality_not_factorized :
    Function.Surjective ExtensionalReadout.Canary.routeReadout.observe ∧
      ¬ Nonempty
        (EqualityFamilyFactorization
          ExtensionalReadout.Canary.routeReadout.observe) := by
  constructor
  · exact ExtensionalReadout.Canary.routeReadout.surjective
  · rw [← splitReadout_exact_iff_equalityFamilyFactorization]
    exact ExtensionalReadout.Canary.routeReadout_not_exact

/-- Paired boundary: equality-family preservation is available for an exact
observation and unavailable for a lawful lossy split readout. -/
theorem equality_factorization_boundary :
    Nonempty (EqualityFamilyFactorization (id : Bool → Bool)) ∧
      ¬ Nonempty (EqualityFamilyFactorization coarseBool) :=
  ⟨⟨identityFactorization⟩, coarseBool_does_not_factor_equality⟩

end Canary

#print axioms EqualityFamilyFactorization.reflectsEquality
#print axioms EqualityFamilyFactorization.nonempty_iff_injective
#print axioms EqualityFamilyFactorization.all_anchored_nonempty_iff_injective
#print axioms splitReadout_exact_iff_equalityFamilyFactorization
#print axioms Canary.coarseBool_does_not_factor_equality
#print axioms Canary.split_complete_but_equality_not_factorized
#print axioms Canary.equality_factorization_boundary

end Mettapedia.TypeTheory.EqualityFamilyObserverFactorization
