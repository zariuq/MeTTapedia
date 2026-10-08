import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementEvidence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeControls
import Mettapedia.TypeTheory.DisplayedPresheafRepresentableEvidence

/-!
# Proper refinement on a returning compiled environment call

The native certificate contains the complete source-origin arrow and a
supplied Boolean witness. Its proper refinement admits the true witness
and excludes the false one. A real compiled environment fetch and call
returns with this selected initial certificate, its computed independent
target-origin specification and its complete runtime history.

The witness is part of the native specification. The guest lambda fragment
does not execute Boolean instructions or update a current-state certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementEvidenceControls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafRepresentableEvidence DisplayedPresheafRefinementTransport
open NamePassingObserverFunctor NamePassingDependentEvidence
open NamePassingDependentRuntimeEvidence NamePassingRefinementEvidence
open NamePassingDependentRuntimeControls
open NamePassingCompilerReadback.Controls NamePassingEnvironmentControls NamePassingSpineControls

def sourceCertificates : DisplayedFamily sourcePrograms where
  obj point := (origins startPoint).obj point × Bool
  map arrow := TypeCat.ofHom fun certificate =>
    ⟨(origins startPoint).map arrow certificate.1, certificate.2⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Prod.ext
    · exact (origins startPoint).map_id_apply point certificate.1
    · rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Prod.ext
    · exact (origins startPoint).map_comp_apply first second certificate.1
    · rfl

def targetCertificates : DisplayedFamily compiledPrograms where
  obj point := (origins (compilerMap.mapElements.obj startPoint)).obj point × Bool
  map arrow := TypeCat.ofHom fun certificate =>
    ⟨(origins (compilerMap.mapElements.obj startPoint)).map arrow certificate.1, certificate.2⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Prod.ext
    · exact (origins (compilerMap.mapElements.obj startPoint)).map_id_apply point certificate.1
    · rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Prod.ext
    · exact (origins (compilerMap.mapElements.obj startPoint)).map_comp_apply first second certificate.1
    · rfl

def implementation : sourceCertificates ⟶ reindexDisplayed compilerMap targetCertificates where
  app point := TypeCat.ofHom fun certificate =>
    ⟨(originMap compilerMap startPoint).app point certificate.1, certificate.2⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Prod.ext
    · exact (originMap compilerMap startPoint).naturality_apply arrow certificate.1
    · rfl

def sourcePredicate : Subfunctor (totalSpace sourceCertificates) where
  obj _ := {entry | entry.2.2 = true}
  map _ := by intro entry belongs; exact belongs

def targetPredicate : Subfunctor (totalSpace targetCertificates) where
  obj _ := {entry | entry.2.2 = true}
  map _ := by intro entry belongs; exact belongs

theorem implementation_respects :
    sourcePredicate ≤ targetPredicate.preimage
      (DisplayedPresheafEvidenceUniversal.evidenceTotalMap compilerMap implementation) := by
  intro world entry belongs
  exact belongs

def selectedInitial : (Refinement.displayed sourceCertificates sourcePredicate).obj startPoint :=
  ⟨⟨𝟙 startPoint, true⟩, rfl⟩

/-- A false witness at the very same actual source program is excluded;
the refinement is not the unrestricted certificate family. -/
theorem source_predicate_is_proper :
    (⟨startPoint.2, (⟨𝟙 startPoint, false⟩ : sourceCertificates.obj startPoint)⟩ :
      (totalSpace sourceCertificates).obj startPoint.1) ∉ sourcePredicate.obj startPoint.1 := by
  change ¬ false = true
  decide

theorem fetched_execution_keeps_refinement :
    ∃ final, ∃ actual : ExecutionPath RhoUnaryReadback.Target (process start) final,
      ∃ receipt : RuntimeReceipt sourceCertificates targetCertificates implementation
        sourcePredicate targetPredicate implementation_respects startPoint selectedInitial
        (world names) (code start) actual,
      receipt.specification.val.1 = compilerMap.mapElements.map (𝟙 startPoint) ∧
        receipt.specification.val.2 = true ∧
        receipt.selectedReceipt.val.val.1 = start ∧
        (NamePassingValueNative.sourcePredicate names).1 receipt.execution.after ∧
        (RhoUnaryInputObservation.targetPredicate (world names) .zero).1 final := by
  obtain ⟨final, ⟨actual⟩, observed⟩ := fetched_function_returns_in_rho
  obtain ⟨receipt⟩ := retain_refined_prefix sourceCertificates targetCertificates implementation
    sourcePredicate targetPredicate implementation_respects startPoint selectedInitial
    (world names) (code start) (supplied start) actual
  refine ⟨final, actual, receipt, ?_, ?_, ?_, receipt.public_return_reflected observed, observed⟩
  · exact congrArg Prod.fst receipt.specification_value
  · exact receipt.specification_membership
  · exact receipt.selectedReceipt_origin

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementEvidenceControls
