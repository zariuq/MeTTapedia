import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedSpecifications
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeEvidence

/-!
# Generated native certificate values on actual compiled rho prefixes

Every supplied execution prefix receives the independently generated
receipt type and specification term. Their complete decoders recover the
same initial certificate and specification stored with that exact prefix,
including its reflected source path and primitive communication accounts.

Current-state evidence still requires the supplied operational functor.
The generated observer-world restriction action does not replace it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedRuntime

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open NamePassingLambda NamePassingUnaryForward NamePassingEnvironmentEquationsNative
open NamePassingDependentEvidence NamePassingDependentSpecifications
open NamePassingDependentRuntimeEvidence
open NamePassingGeneratedIndexedEvidence NamePassingGeneratedIndexedSpecifications

noncomputable section

variable {A : DisplayedFamily sourcePrograms} {B : DisplayedFamily compiledPrograms}
variable {body : A ⟶ reindexDisplayed compilerMap B} {point : sourcePrograms.Elements}
variable {evidence : A.obj point} {world : NamePassingSpine.World (scope point)}
variable {code : RhoUnaryCode.Code 0} {final : RhoUnaryReadback.TargetProcess}
variable {actual : ExecutionPath RhoUnaryReadback.Target
  (RhoUnaryReadback.runtimeProcess code world.available) final}

def generatedCertificate (receipt : Receipt A B body point evidence world code actual) :
    NativeReceipt A (compilerMap.mapElements.obj point) :=
  encodeReceipt A (compilerMap.mapElements.obj point) receipt.nativeCertificate

theorem generated_certificate_read (receipt : Receipt A B body point evidence world code actual) :
    receiptEquiv A (compilerMap.mapElements.obj point) (generatedCertificate receipt) =
      receipt.nativeCertificate := decode_encode A _ _

theorem generated_certificate_is_the_supplied_one
    (receipt : Receipt A B body point evidence world code actual) :
    generatedCertificate receipt = suppliedReceipt A point evidence := by
  rw [generatedCertificate, receipt.carried]
  rfl

def generatedSpecification (receipt : Receipt A B body point evidence world code actual) :
    NativeSpecification B (compilerMap.mapElements.obj point) :=
  applySpecification body (compilerMap.mapElements.obj point) (generatedCertificate receipt)

theorem generated_specification_read (receipt : Receipt A B body point evidence world code actual) :
    NamePassingGeneratedIndexedSpecifications.specificationEquiv B
      (compilerMap.mapElements.obj point) (generatedSpecification receipt) = receipt.specification := by
  rw [generatedSpecification, specification_current_read, generated_certificate_read]
  exact receipt.realized.symm

/-- The result keeps the actual supplied endpoint and complete receipt;
both generated decoders compute on the same execution witness. -/
theorem retain_generated_prefix (A : DisplayedFamily sourcePrograms)
    (B : DisplayedFamily compiledPrograms) (body : A ⟶ reindexDisplayed compilerMap B)
    (point : sourcePrograms.Elements) (evidence : A.obj point)
    (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
    (compiled : NamePassingRho.compile point.2 (references (scope point)) .zero world.world = some code)
    {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :
    ∃ receipt : Receipt A B body point evidence world code actual,
      receiptEquiv A (compilerMap.mapElements.obj point) (generatedCertificate receipt) =
          (carry A).app point evidence ∧
        NamePassingGeneratedIndexedSpecifications.specificationEquiv B
          (compilerMap.mapElements.obj point) (generatedSpecification receipt) = body.app point evidence := by
  obtain ⟨receipt⟩ := retain_prefix A B body point evidence world code compiled actual
  exact ⟨receipt, (generated_certificate_read receipt).trans receipt.carried,
    (generated_specification_read receipt).trans receipt.computed⟩

theorem generated_certificate_and_actual_accounts
    (receipt : Receipt A B body point evidence world code actual) :
    generatedCertificate receipt = suppliedReceipt A point evidence ∧
      receipt.execution.rho.credit + actual.length =
        8 * NamePassingRhoReadback.initializationSites point.2 + receipt.execution.charges.sum :=
  ⟨generated_certificate_is_the_supplied_one receipt, receipt.actual_work_balance⟩

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedRuntime
