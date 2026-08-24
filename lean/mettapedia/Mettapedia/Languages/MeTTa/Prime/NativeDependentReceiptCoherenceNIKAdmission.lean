import Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
import Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptCoherenceObservation

/-!
# NIK admission at the dependent-receipt coherence boundary

The observation-relative interchange theorem determines two different native
faces without imposing a global coherence quotient.

* Authored-generator count is admitted for the request that asks only for
  that invariant.
* Retaining the complete horizontal cell is admitted for the full receipt
  policy family.
* Generator count cannot be admitted for the full family because it identifies
  the two interchange histories distinguished by construction shape.

Both positive admissions are revision-indexed retained runners.  Current
activation executes the stored runner directly; a dependency change disables
activation while the complete prepared cell remains available for fallback.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeDependentReceiptCoherenceNIKAdmission

open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
open Mettapedia.TypeTheory.FreeWhiskeredCell.CoherenceObservation
open NativeDependentReceiptCoherenceObservation

/-! ## Revision-indexed positive and negative admissions -/

/-- One dependency revision is enough for the concrete boundary canary.  A
real host may replace this with its complete declaration and policy revision
product without changing the admission theorem. -/
def dependencies : DependencySystem where
  Revision := Nat
  Dependency := Unit
  Value := Nat
  read := fun revision _ => revision

def initialRevision : dependencies.Revision := by
  change Nat
  exact 0

def changedRevision : dependencies.Revision := by
  change Nat
  exact 1

/-- The compressed, interchange-insensitive native face is constructively
admitted for the exact small request it realizes. -/
def generatorCountAdmission :
    PolicyFamilyAdmittedAt dependencies initialRevision
      interchangeGeneratorOnlyFamily
      (generatorCount : AdministrativeHorizontalCell → Nat) where
  realization := {
    run := fun _ count => count
    agrees := by
      intro policy cell
      cases policy
      rfl }

/-- The proof-relevant identity face is constructively admitted for the full
history-sensitive family. -/
def retainedCellAdmission :
    PolicyFamilyAdmittedAt dependencies initialRevision interchangePolicies
      (id : AdministrativeHorizontalCell → AdministrativeHorizontalCell) where
  realization := {
    run := fun policy cell => interchangePolicies.decide policy cell
    agrees := by
      intro policy cell
      rfl }

/-- No admission record can promote the generator-count face to the full
history-sensitive request. -/
theorem no_generatorCountAdmission_for_fullFamily :
    ¬ Nonempty
      (PolicyFamilyAdmittedAt dependencies initialRevision interchangePolicies
        (generatorCount : AdministrativeHorizontalCell → Nat)) := by
  apply PolicyFamilyAdmittedAt.noAdmission_of_policy_collision
    (first := horizontalRightThenLeftAdministrativeCell)
    (second := horizontalLeftThenRightAdministrativeCell)
    generatorCount_identifies_administrative_interchange
    Policy.constructionShape
    rawShape_separates_administrative_interchange

/-! ## Current execution and stale fallback -/

def generatorCountActive : generatorCountAdmission.Active initialRevision :=
  generatorCountAdmission.activate
    (dependencies.sameDependencies_refl initialRevision)

def preparedHorizontalCell : generatorCountAdmission.PreparedState :=
  generatorCountAdmission.prepare horizontalRightThenLeftAdministrativeCell

/-- Current hot execution agrees with the semantic observation using only the
retained keyed runner. -/
theorem current_generatorCount_run_agrees :
    generatorCountActive.runPrepared preparedHorizontalCell
        GeneratorOnlyRequest.authoredGenerators =
      generatorCount horizontalRightThenLeftAdministrativeCell :=
  PolicyFamilyAdmittedAt.Active.runPrepared_eq
    generatorCountActive preparedHorizontalCell
      GeneratorOnlyRequest.authoredGenerators

/-- Changing the sole dependency changes the complete dependency view. -/
theorem revision_one_is_stale :
    generatorCountAdmission.StaleAt changedRevision := by
  intro same
  have impossible := same ()
  simp [dependencies, initialRevision, changedRevision] at impossible

/-- Staleness disables the compressed native face but preserves the exact raw
horizontal receipt cell for gradual fallback. -/
theorem stale_refuses_activation_and_preserves_receipt :
    (¬ generatorCountAdmission.Active changedRevision) ∧
      preparedHorizontalCell.fallback =
        horizontalRightThenLeftAdministrativeCell :=
  generatorCountAdmission.stale_prevents_activation_and_preserves_fallback
    revision_one_is_stale preparedHorizontalCell

/-- The entire NIK selection boundary in one theorem-sized interface. -/
theorem nik_interchange_boundary :
    Nonempty
        (PolicyFamilyAdmittedAt dependencies initialRevision
          interchangeGeneratorOnlyFamily
          (generatorCount : AdministrativeHorizontalCell → Nat)) ∧
      Nonempty
        (PolicyFamilyAdmittedAt dependencies initialRevision interchangePolicies
          (id : AdministrativeHorizontalCell → AdministrativeHorizontalCell)) ∧
      ¬ Nonempty
        (PolicyFamilyAdmittedAt dependencies initialRevision interchangePolicies
          (generatorCount : AdministrativeHorizontalCell → Nat)) ∧
      (¬ generatorCountAdmission.Active changedRevision) ∧
      preparedHorizontalCell.fallback =
        horizontalRightThenLeftAdministrativeCell :=
  ⟨⟨generatorCountAdmission⟩, ⟨retainedCellAdmission⟩,
    no_generatorCountAdmission_for_fullFamily,
    stale_refuses_activation_and_preserves_receipt⟩

#print axioms generatorCountAdmission
#print axioms retainedCellAdmission
#print axioms no_generatorCountAdmission_for_fullFamily
#print axioms current_generatorCount_run_agrees
#print axioms revision_one_is_stale
#print axioms stale_refuses_activation_and_preserves_receipt
#print axioms nik_interchange_boundary

end NativeDependentReceiptCoherenceNIKAdmission
end Mettapedia.Languages.MeTTa.Prime
