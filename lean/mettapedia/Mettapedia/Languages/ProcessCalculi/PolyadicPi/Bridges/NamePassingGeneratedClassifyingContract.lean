import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalClassifyingEvidence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedLogicalContract

/-!
# Classifying interpretation at the actual name-passing compiler

The generated source term class has a complete native image under the earned
classifying interpreter. Substitution along the actual compiler map reads
that same section at the independently supplied target interface. Universal
receipt elimination and every supplied rho execution prefix retain this image,
the exact generated tree, the source origin and the actual execution history.

These are generated specifications in the common native presheaf model. They
do not supply dependent instructions to the guest language or an action that
updates a certificate to describe the current runtime state.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedClassifyingContract

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution
open Calculi.NativeDependent ExternalPresheafCertificates
open NamePassingDependentEvidence NamePassingDependentSpecifications NamePassingDependentRuntimeEvidence
open NamePassingUnaryForward NamePassingEnvironmentEquationsNative
open NamePassingGeneratedLogicalContract

variable {S : External.Symbols} {D : External.Signature S} {n : Nat}
variable {context : External.ContextExpr S n} {term : External.TermExpr S n}
variable {type : External.TypeExpr S n}
variable (headers : External.HeaderFormation D)
variable (target : Interpretation D context term type compiledPrograms)

local instance semanticCategory : Category target.semanticContext.1.Elements :=
  categoryOfElements (target.semanticContext.1 : ContextCategoryᵒᵖ ⥤ Type)

/-- The actual universal target value receipt reads the complete image of
the supplied source term under the classifying morphism. -/
theorem universal_classifying_value (point : sourcePrograms.Elements)
    (tree : External.Derivation D (.term context term type)) :
    (valueReadout target).app (compilerMap.mapElements.obj point)
      ((carry (source target).certificates).app point
        (((source target).certificateSection tree).val point)) =
      (target.classifyingSection headers tree).val
        (target.interface.mapElements.obj (compilerMap.mapElements.obj point)) :=
  (valueReadout_computes target point tree).trans
    (target.classifying_value_readout headers tree (compilerMap.mapElements.obj point))

/-- Receipt elimination recovers the same source-class image for every
supplied retained certificate, not only one distinguished tree. -/
theorem universal_certificate_classifying_value (point : sourcePrograms.Elements)
    (certificate : (source target).Certificate point) :
    (valueReadout target).app (compilerMap.mapElements.obj point)
      ((carry (source target).certificates).app point certificate) =
      (target.classifyingSection headers certificate.tree).val
        (target.interface.mapElements.obj (compilerMap.mapElements.obj point)) := by
  rw [(source target).certificate_value_unique point certificate]
  exact universal_classifying_value headers target point certificate.tree

/-- The interface pullback commutes with the complete model-map image. -/
theorem compiler_classifying_section :
    (source target).classifyingValueSection headers = fun tree =>
      reindexDisplayedSection compilerMap target.valueFamily
        (target.classifyingValueSection headers tree) := by
  funext tree
  exact target.classifyingValueSection_substitution headers tree compilerMap

variable {headers target} {point : sourcePrograms.Elements}
variable {tree : External.Derivation D (.term context term type)}
variable {world : NamePassingSpine.World (scope point)} {code : RhoUnaryCode.Code 0}
variable {final : RhoUnaryReadback.TargetProcess}
variable {actual : ExecutionPath RhoUnaryReadback.Target
  (RhoUnaryReadback.runtimeProcess code world.available) final}

/-- The classifying value is attached to this exact supplied rho prefix.
The execution endpoint and all reflected history data remain in the receipt. -/
theorem RuntimeReceipt.classifying_value
    (receipt : RuntimeReceipt target point tree world code actual) :
    receipt.specification = (target.classifyingSection headers tree).val
      (target.interface.mapElements.obj (compilerMap.mapElements.obj point)) := by
  rw [target.classifyingSection_eq_nativeSection headers tree]
  exact receipt.native_evaluator_value

theorem RuntimeReceipt.classifying_certificate_value
    (receipt : RuntimeReceipt target point tree world code actual) :
    ((certificateReadout target).app (compilerMap.mapElements.obj point)
      receipt.nativeCertificate).value = (target.classifyingSection headers tree).val
        (target.interface.mapElements.obj (compilerMap.mapElements.obj point)) :=
  receipt.target_certificate_value.trans (RuntimeReceipt.classifying_value (headers := headers) receipt)

/-- Every supplied actual prefix admits one receipt containing the complete
classifying value and the exact supplied tree and program origin. -/
theorem retain_classifying_runtime_prefix
    (headers : External.HeaderFormation D)
    (target : Interpretation D context term type compiledPrograms)
    (point : sourcePrograms.Elements) (tree : External.Derivation D (.term context term type))
    (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
    (compiled : NamePassingRho.compile point.2 (references (scope point)) .zero
      world.world = some code) {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :
    ∃ receipt : RuntimeReceipt target point tree world code actual,
      receipt.history.2.tree = tree ∧ receipt.nativeCertificate.val.1 = point.2 ∧
        receipt.specification = (target.classifyingSection headers tree).val
          (target.interface.mapElements.obj (compilerMap.mapElements.obj point)) := by
  obtain ⟨receipt⟩ := retain_runtime_prefix target point tree world code compiled actual
  exact ⟨receipt,receipt.tree_retained,receipt.origin_retained,
    RuntimeReceipt.classifying_value (headers := headers) receipt⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedClassifyingContract
