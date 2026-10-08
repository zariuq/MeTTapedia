import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPresheafCertificateSubstitution
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeEvidence
import Mettapedia.TypeTheory.DisplayedPresheafLogicalPullback

/-!
# Generated predicate and refinement specifications at the actual compiler

The complete independently generated dependent grammar includes ordinary
propositions, mixed data and assumption contexts, and refinement judgments.
Its earned native interpretation determines coherent tree/value certificates.
Substitution along the actual context-natural compiler preserves both, and
universal sum elimination gives unique target certificate and value readouts.

Every supplied actual rho execution prefix retains that generated tree,
initial program origin, checked native value and complete reflected history.
The interface map explicitly separates semantic variable scopes from program
clients. This contract adds no dependent guest instructions, unrestricted
reflective observers or current-runtime-state certificate action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedLogicalContract

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution
open Calculi.NativeDependent RefinementPresheafCertificates
open RefinementPresheafCertificateSubstitution
open NamePassingDependentEvidence NamePassingDependentSpecifications
open NamePassingDependentRuntimeEvidence
open NamePassingUnaryForward NamePassingEnvironmentEquationsNative

variable {S : Refinement.Symbols} {D : Refinement.Signature S} {n : Nat}
variable {context : Refinement.ContextExpr S n} {term : Refinement.TermExpr S n}
variable {type : Refinement.TypeExpr S n}

variable (target : Interpretation D context term type compiledPrograms)

local instance semanticCategory : Category target.semanticContext.1.Elements :=
  categoryOfElements (target.semanticContext.1 : ContextCategoryᵒᵖ ⥤ Type)

abbrev source : Interpretation D context term type sourcePrograms :=
  reindex target compilerMap

def certificateBody : (source target).certificates ⟶
    reindexDisplayed compilerMap target.certificates :=
  (comparison target compilerMap).hom

def certificateReadout : compiledFamily (source target).certificates ⟶
    target.certificates := realize (certificateBody target)

def valueBody : (source target).certificates ⟶
    reindexDisplayed compilerMap target.valueFamily :=
  (source target).valueReadout

def valueReadout : compiledFamily (source target).certificates ⟶
    target.valueFamily := realize (valueBody target)

/-- Complete generated certificates, rather than only inhabited types,
give the actual source implementation of the target specification. -/
theorem source_body_square :
    certificateBody target ≫ (reindexFunctor compilerMap).map target.valueReadout =
      valueBody target := value_readout_square target compilerMap

/-- The two independently extended target readouts agree on every
receipt; no source preimage is selected or erased. -/
theorem target_readout_square :
    certificateReadout target ≫ target.valueReadout = valueReadout target := by
  change realize (certificateBody target) ≫ target.valueReadout = realize (valueBody target)
  rw [← realization_naturality, source_body_square]

theorem certificateReadout_unique
    (candidate : compiledFamily (source target).certificates ⟶ target.certificates)
    (computes : carry (source target).certificates ≫
      (reindexFunctor compilerMap).map candidate = certificateBody target) :
    candidate = certificateReadout target :=
  realization_unique (certificateBody target) candidate computes

theorem valueReadout_unique
    (candidate : compiledFamily (source target).certificates ⟶ target.valueFamily)
    (computes : carry (source target).certificates ≫
      (reindexFunctor compilerMap).map candidate = valueBody target) :
    candidate = valueReadout target :=
  realization_unique (valueBody target) candidate computes

theorem certificateReadout_computes (point : sourcePrograms.Elements)
    (tree : Refinement.Derivation D (.term context term type)) :
    (certificateReadout target).app (compilerMap.mapElements.obj point)
      ((carry (source target).certificates).app point
        (((source target).certificateSection tree).val point)) =
      (target.certificateSection tree).val (compilerMap.mapElements.obj point) :=
  realization_computes (certificateBody target) point
    (((source target).certificateSection tree).val point)

theorem valueReadout_computes (point : sourcePrograms.Elements)
    (tree : Refinement.Derivation D (.term context term type)) :
    (valueReadout target).app (compilerMap.mapElements.obj point)
      ((carry (source target).certificates).app point
        (((source target).certificateSection tree).val point)) =
      (target.valueSection tree).val (compilerMap.mapElements.obj point) :=
  realization_computes (valueBody target) point
    (((source target).certificateSection tree).val point)

/-- Receipt transport keeps distinct authored trees even when their
independently interpreted values coincide. -/
theorem source_receipt_tree_injective (point : sourcePrograms.Elements) :
    Function.Injective (fun tree : Refinement.Derivation D (.term context term type) =>
      (carry (source target).certificates).app point
        (((source target).certificateSection tree).val point)) :=
  (carry_injective (source target).certificates point).comp
    ((source target).certificateSection_injective point)

abbrev RuntimeReceipt (point : sourcePrograms.Elements)
    (tree : Refinement.Derivation D (.term context term type))
    (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
    {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :=
  Receipt (source target).certificates target.valueFamily (valueBody target)
    point (((source target).certificateSection tree).val point) world code actual

theorem retain_runtime_prefix (point : sourcePrograms.Elements)
    (tree : Refinement.Derivation D (.term context term type))
    (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
    (compiled : NamePassingRho.compile point.2 (references (scope point)) .zero
      world.world = some code) {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :
    Nonempty (RuntimeReceipt target point tree world code actual) :=
  retain_prefix (source target).certificates target.valueFamily (valueBody target)
    point (((source target).certificateSection tree).val point) world code compiled actual

variable {target} {point : sourcePrograms.Elements}
variable {tree : Refinement.Derivation D (.term context term type)}
variable {world : NamePassingSpine.World (scope point)} {code : RhoUnaryCode.Code 0}
variable {final : RhoUnaryReadback.TargetProcess}
variable {actual : ExecutionPath RhoUnaryReadback.Target
  (RhoUnaryReadback.runtimeProcess code world.available) final}

theorem RuntimeReceipt.tree_retained
    (receipt : RuntimeReceipt target point tree world code actual) :
    receipt.history.2.tree = tree := rfl

theorem RuntimeReceipt.origin_retained
    (receipt : RuntimeReceipt target point tree world code actual) :
    receipt.nativeCertificate.val.1 = point.2 := by
  rw [receipt.carried]
  rfl

theorem RuntimeReceipt.native_evaluator_value
    (receipt : RuntimeReceipt target point tree world code actual) :
    receipt.specification = (target.nativeSection tree).val
      (target.interface.mapElements.obj (compilerMap.mapElements.obj point)) := by
  rw [receipt.computed]
  exact native_value_substitution target compilerMap point tree

/-- The retained native section is read from the independent raw evaluator;
successful checking is earned by the complete generated rule interpretation. -/
theorem RuntimeReceipt.generated_evaluator_readout
    (receipt : RuntimeReceipt target point tree world code actual) :
    target.model.evaluateTerm target.semanticContext term =
      some ⟨target.semanticType, target.nativeSection receipt.history.2.tree⟩ :=
  target.nativeSection_readout tree

theorem RuntimeReceipt.target_certificate_value
    (receipt : RuntimeReceipt target point tree world code actual) :
    ((certificateReadout target).app (compilerMap.mapElements.obj point)
      receipt.nativeCertificate).value = receipt.specification := by
  have square := congrArg (fun operation =>
    operation.app (compilerMap.mapElements.obj point) receipt.nativeCertificate)
    (target_readout_square target)
  exact square.trans receipt.realized.symm

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedLogicalContract
