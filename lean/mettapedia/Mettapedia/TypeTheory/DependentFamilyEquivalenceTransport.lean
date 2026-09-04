import Mettapedia.TypeTheory.DependentFamilyObserverFactorization
import Mettapedia.TypeTheory.ExactCodeFamilyRepresentation

/-!
# Fibrewise equivalence and observer factorization

Whether a dependent family descends through an observer is invariant under a
fibrewise equivalence of families.  Consequently, adding an exact
representation layer pointwise neither creates nor destroys observer
factorization.

This is a transport theorem about dependent families.  It does not say that
an observer preserves operational histories, that code execution is a source
reduction, or that an arbitrary representation is exact.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentFamilyEquivalenceTransport

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.ExactCodeFamilyRepresentation
open Mettapedia.TypeTheory.ExactCodeModalityModel

universe uSource uTarget uFibre

namespace FamilyFactorization

variable {Source : Type uSource} {Target : Type uTarget}
variable {observe : Source → Target}
variable {first second : Source → Type uFibre}

/-- Transport a factorization across a fibrewise equivalence of its source
family. -/
def transportFibreEquiv
    (equivalence : ∀ source, first source ≃ second source)
    (factorization : FamilyFactorization observe first) :
    FamilyFactorization observe second where
  targetFamily := factorization.targetFamily
  identify := fun source =>
    (equivalence source).symm.trans (factorization.identify source)

/-- Factorization through a fixed observer is invariant under fibrewise
equivalence. -/
theorem nonempty_congr
    (equivalence : ∀ source, first source ≃ second source) :
    Nonempty (FamilyFactorization observe first) ↔
      Nonempty (FamilyFactorization observe second) := by
  constructor
  · rintro ⟨factorization⟩
    exact ⟨transportFibreEquiv equivalence factorization⟩
  · rintro ⟨factorization⟩
    exact ⟨transportFibreEquiv
      (fun source => (equivalence source).symm) factorization⟩

/-- Nonfactorization is invariant under the same fibrewise equivalence. -/
theorem not_nonempty_congr
    (equivalence : ∀ source, first source ≃ second source) :
    (¬ Nonempty (FamilyFactorization observe first)) ↔
      ¬ Nonempty (FamilyFactorization observe second) := by
  rw [not_congr (nonempty_congr equivalence)]

end FamilyFactorization

/-! ## Exact representation preserves the factorization boundary -/

/-- Exact code is fibrewise equivalent to the family it represents. -/
def codeFamilyEquiv (depth : Nat) {Source : Type uSource}
    (family : Source → Type uFibre) :
    ∀ source, codeFamily depth family source ≃ family source :=
  fun source => iterEquiv depth (family source)

/-- Adding exact representation layers preserves and reflects descent through
every observer. -/
theorem codeFamily_factorization_iff (depth : Nat)
    {Source : Type uSource} {Target : Type uTarget}
    (observe : Source → Target) (family : Source → Type uFibre) :
    Nonempty (FamilyFactorization observe (codeFamily depth family)) ↔
      Nonempty (FamilyFactorization observe family) :=
  FamilyFactorization.nonempty_congr (codeFamilyEquiv depth family)

/-- In particular, exact representation preserves and reflects failure to
descend through an observer. -/
theorem codeFamily_nonfactorization_iff (depth : Nat)
    {Source : Type uSource} {Target : Type uTarget}
    (observe : Source → Target) (family : Source → Type uFibre) :
    (¬ Nonempty
        (FamilyFactorization observe (codeFamily depth family))) ↔
      ¬ Nonempty (FamilyFactorization observe family) :=
  FamilyFactorization.not_nonempty_congr (codeFamilyEquiv depth family)

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization.Canary

/-- Positive: exact representation of a constant family still descends
through the coarse Boolean observer. -/
theorem exact_constant_family_factors (depth : Nat) :
    Nonempty
      (FamilyFactorization coarseBool
        (codeFamily depth (fun _ : Bool => PUnit))) := by
  exact (codeFamily_factorization_iff depth coarseBool
    (fun _ : Bool => PUnit)).2 ⟨constantFactors⟩

/-- Negative: exact representation does not make the varying unit/Boolean
family compatible with the same coarse observer. -/
theorem exact_varying_family_does_not_factor (depth : Nat) :
    ¬ Nonempty
      (FamilyFactorization coarseBool (codeFamily depth varying)) := by
  exact (codeFamily_nonfactorization_iff depth coarseBool varying).2
    varying_does_not_factor

/-- Paired canary: exact representation preserves both sides of the original
observer boundary. -/
theorem exact_representation_preserves_observer_boundary (depth : Nat) :
    Nonempty
        (FamilyFactorization coarseBool
          (codeFamily depth (fun _ : Bool => PUnit))) ∧
      ¬ Nonempty
        (FamilyFactorization coarseBool (codeFamily depth varying)) :=
  ⟨exact_constant_family_factors depth,
    exact_varying_family_does_not_factor depth⟩

end Canary

#print axioms FamilyFactorization.transportFibreEquiv
#print axioms FamilyFactorization.nonempty_congr
#print axioms FamilyFactorization.not_nonempty_congr
#print axioms codeFamilyEquiv
#print axioms codeFamily_factorization_iff
#print axioms codeFamily_nonfactorization_iff
#print axioms Canary.exact_constant_family_factors
#print axioms Canary.exact_varying_family_does_not_factor
#print axioms Canary.exact_representation_preserves_observer_boundary

end Mettapedia.TypeTheory.DependentFamilyEquivalenceTransport
