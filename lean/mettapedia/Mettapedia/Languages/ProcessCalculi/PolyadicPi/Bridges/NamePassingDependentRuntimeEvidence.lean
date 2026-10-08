import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentSpecifications
import Mettapedia.GSLT.Core.OperationalReadbackEvidence

/-!
# Native specifications alongside actual core-rho execution prefixes

The supplied initial program and dependent certificate determine a native
sum receipt and its universal target specification. Every supplied actual
core-rho prefix additionally retains the source and unary paths, the exact
runtime endpoint, administrative witnesses and communication accounts.

Certificates that describe the current source state need a separate
execution-functor action. Certificates for the initial program are retained
with its history; they are not silently retyped as certificates of the final
program. This distinction applies to every coherent native specification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeEvidence

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open NamePassingLambda NamePassingUnaryForward NamePassingEnvironmentEquationsNative
open NamePassingDependentEvidence NamePassingDependentSpecifications

abbrev scope (point : sourcePrograms.Elements) : Ctx sig := point.1.unop.unop.context

structure Receipt (A : DisplayedFamily sourcePrograms) (B : DisplayedFamily compiledPrograms)
    (body : A ⟶ reindexDisplayed compilerMap B) (point : sourcePrograms.Elements)
    (evidence : A.obj point) (world : NamePassingSpine.World (scope point))
    (code : RhoUnaryCode.Code 0) {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) where
  execution : NamePassingSpine.PrefixResult point.2 world code actual
  nativeCertificate : (compiledFamily A).obj (compilerMap.mapElements.obj point)
  carried : nativeCertificate = (carry A).app point evidence
  specification : B.obj (compilerMap.mapElements.obj point)
  realized : specification = (realize body).app (compilerMap.mapElements.obj point) nativeCertificate
  computed : specification = body.app point evidence

/-- Arbitrary schedules and their supplied endpoints retain both the native
certificate and the actual execution comparison. The compilation-success
premise is the real core-rho compiler equation for this source program. -/
theorem retain_prefix (A : DisplayedFamily sourcePrograms) (B : DisplayedFamily compiledPrograms)
    (body : A ⟶ reindexDisplayed compilerMap B) (point : sourcePrograms.Elements)
    (evidence : A.obj point) (world : NamePassingSpine.World (scope point))
    (code : RhoUnaryCode.Code 0)
    (compiled : NamePassingRho.compile point.2 (references (scope point)) .zero world.world = some code)
    {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :
    Nonempty (Receipt A B body point evidence world code actual) := by
  obtain ⟨execution⟩ := NamePassingSpine.compiled_prefix_accounted point.2 world code compiled actual
  exact ⟨⟨execution, (carry A).app point evidence, rfl,
    (realize body).app (compilerMap.mapElements.obj point) ((carry A).app point evidence),
    rfl, realization_computes body point evidence⟩⟩

variable {A : DisplayedFamily sourcePrograms} {B : DisplayedFamily compiledPrograms}
variable {body : A ⟶ reindexDisplayed compilerMap B} {point : sourcePrograms.Elements}
variable {evidence : A.obj point} {world : NamePassingSpine.World (scope point)}
variable {code : RhoUnaryCode.Code 0} {final : RhoUnaryReadback.TargetProcess}
variable {actual : ExecutionPath RhoUnaryReadback.Target
  (RhoUnaryReadback.runtimeProcess code world.available) final}

/-- The operational evidence family is the existing execution-category
history functor, paired with the supplied initial native certificate. -/
def Receipt.history (receipt : Receipt A B body point evidence world code actual) :
    (OperationalReadbackEvidence.historyAndWitness (sourceTheory (scope point)) point.2
      (A.obj point)).obj receipt.execution.after :=
  ⟨receipt.execution.sourcePath, evidence⟩

theorem Receipt.history_updated (receipt : Receipt A B body point evidence world code actual) :
    (OperationalReadbackEvidence.historyAndWitness (sourceTheory (scope point)) point.2
      (A.obj point)).map receipt.execution.sourcePath ⟨.refl point.2, evidence⟩ = receipt.history := rfl

/-- Ordered uses or other proof-relevant readouts are recovered from the
original witness, while the complete runtime prefix remains in the receipt. -/
theorem Receipt.ordered_uses_retained (receipt : Receipt A B body point evidence world code actual)
    {Use : Type} (uses : A.obj point → List Use) :
    uses receipt.history.2 = uses evidence := rfl

/-- For an independently supplied operational evidence functor, the current
certificate is obtained by its actual action on the reflected source path. -/
def Receipt.currentCertificate (receipt : Receipt A B body point evidence world code actual)
    (currentEvidence : ExecutionObject (sourceTheory (scope point)) ⥤ Type)
    (initial : currentEvidence.obj point.2) : currentEvidence.obj receipt.execution.after :=
  currentEvidence.map receipt.execution.sourcePath initial

theorem Receipt.currentCertificate_composition
    (receipt : Receipt A B body point evidence world code actual)
    (currentEvidence : ExecutionObject (sourceTheory (scope point)) ⥤ Type)
    (initial : currentEvidence.obj point.2) {after : Expr (scope point)}
    (suffix : ExecutionPath (sourceTheory (scope point)) receipt.execution.after after) :
    currentEvidence.map (receipt.execution.sourcePath.append suffix) initial =
      currentEvidence.map suffix (receipt.currentCertificate currentEvidence initial) :=
  OperationalReadbackEvidence.update_composition currentEvidence receipt.execution.sourcePath suffix initial

/-- A public return at this exact supplied rho endpoint reflects to the
returned source state stored with the native certificate and history. -/
theorem Receipt.public_return_reflected
    (receipt : Receipt A B body point evidence world code actual)
    (observed : (RhoUnaryInputObservation.targetPredicate world .zero).1 final) :
    (NamePassingValueNative.sourcePredicate (scope point)).1 receipt.execution.after :=
  NamePassingSpine.current_return_reflected world
    ⟨receipt.execution.middle, ⟨receipt.execution.protocol⟩, ⟨receipt.execution.rho⟩⟩ observed

/-- The accounts belong to the supplied primitive runtime path, including
administration. Native proof transport neither erases nor funds that work. -/
theorem Receipt.actual_work_balance (receipt : Receipt A B body point evidence world code actual) :
    receipt.execution.rho.credit + actual.length =
      8 * NamePassingRhoReadback.initializationSites point.2 + receipt.execution.charges.sum :=
  receipt.execution.rhoBalance

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeEvidence
