import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFamilies
import Mettapedia.SetTheory.Profiles.ProfileIndexedInterpretation

/-!
# Source deductions consumed by material graph readouts

The actual profile-indexed source interpretation computes matching and
membership data from law and local receipts. Atomic material consumers
can then use the corresponding quotient equalities and memberships.
This erasure does not assert that an arbitrary evidence-sensitive family
or an entire proof-relevant formula descends.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Deduction

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualGraphFormulaRealization
open ProfileIndexedCalculus

universe u
variable {D : Type u} [Category.{u} D]
variable {count : Nat} {assumptions : List (ContextualMaterialLogic.Formula count)}

/-- All adopted law occurrences and local receipt positions enter the
source interpretation before the material equality is read. -/
theorem equality (first second : Fin count)
    (source : Derivation ProfileIndexedInterpretation.commonProfile assumptions (.equal first second))
    (point : D) (environment : Environment D count point)
    (receipts : ContextualGraphRealizedDeduction.Receipts assumptions environment) :
    readout D (environment first) = readout D (environment second) :=
  (readout_kernel D _ _).mpr
    ⟨(ProfileIndexedInterpretation.contextual source point environment receipts).down⟩

theorem membership (child parent : Fin count)
    (source : Derivation ProfileIndexedInterpretation.commonProfile assumptions (.member child parent))
    (point : D) (environment : Environment D count point)
    (receipts : ContextualGraphRealizedDeduction.Receipts assumptions environment) :
    member D (readout D (environment child)) (readout D (environment parent)) :=
  ⟨(ProfileIndexedInterpretation.contextual source point environment receipts).down⟩

theorem equality_future (first second : Fin count)
    (source : Derivation ProfileIndexedInterpretation.commonProfile assumptions (.equal first second))
    {point target : D} (arrival : point ⟶ target) (environment : Environment D count point)
    (receipts : ContextualGraphRealizedDeduction.Receipts assumptions environment) :
    transport D arrival (readout D (environment first)) =
      transport D arrival (readout D (environment second)) :=
  congrArg (transport D arrival) (equality first second source point environment receipts)

theorem membership_future (child parent : Fin count)
    (source : Derivation ProfileIndexedInterpretation.commonProfile assumptions (.member child parent))
    {point target : D} (arrival : point ⟶ target) (environment : Environment D count point)
    (receipts : ContextualGraphRealizedDeduction.Receipts assumptions environment) :
    member D (transport D arrival (readout D (environment child)))
      (transport D arrival (readout D (environment parent))) :=
  member_transport D arrival (membership child parent source point environment receipts)

theorem equality_substitution {other : Nat} (indices : Fin count → Fin other)
    (first second : Fin count)
    (source : Derivation ProfileIndexedInterpretation.commonProfile assumptions (.equal first second))
    (point : D) (environment : Environment D other point)
    (receipts : ContextualGraphRealizedDeduction.Receipts assumptions (environment ∘ indices)) :
    readout D (environment (indices first)) = readout D (environment (indices second)) :=
  (readout_kernel D _ _).mpr
    ⟨(ProfileIndexedInterpretation.contextualSubstitution indices source point environment receipts).down⟩

theorem membership_substitution {other : Nat} (indices : Fin count → Fin other)
    (child parent : Fin count)
    (source : Derivation ProfileIndexedInterpretation.commonProfile assumptions (.member child parent))
    (point : D) (environment : Environment D other point)
    (receipts : ContextualGraphRealizedDeduction.Receipts assumptions (environment ∘ indices)) :
    member D (readout D (environment (indices child))) (readout D (environment (indices parent))) :=
  ⟨(ProfileIndexedInterpretation.contextualSubstitution indices source point environment receipts).down⟩

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Deduction
