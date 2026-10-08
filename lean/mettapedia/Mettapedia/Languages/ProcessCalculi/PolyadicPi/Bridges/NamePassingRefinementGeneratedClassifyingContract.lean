import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementClassifyingEvidence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedComprehension

/-!
# Complete classifying certificates at the name-passing compiler

The generated mixed-context term class has an earned complete image under
the actual classifying interpretation. The independent native evaluator,
interface substitution and universal compiler receipt read this same image.
Refinement decoding exposes its supplied domain inhabitant and predicate
membership. Every supplied actual rho prefix retains the exact tree, source
origin, classifying value and complete execution history.

The interpretation has strict chosen local logical operations and admitted
corrected contextual cells. This contract does not add dependent instructions
to the guest calculus or update a certificate to describe a runtime endpoint.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedClassifyingContract

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution NativeLocalTypeFormers
open Calculi.NativeDependent RefinementPresheafCertificates
open NamePassingDependentEvidence NamePassingDependentSpecifications NamePassingDependentRuntimeEvidence
open NamePassingUnaryForward NamePassingEnvironmentEquationsNative
open NamePassingRefinementGeneratedLogicalContract

variable {S : Refinement.Symbols} {D : Refinement.Signature S} {n : Nat}
variable {context : Refinement.ContextExpr S n} {term : Refinement.TermExpr S n}
variable {type : Refinement.TypeExpr S n}
variable (headers : Refinement.HeaderFormation D)
variable (target : Interpretation D context term type compiledPrograms)

local instance semanticCategory : Category target.semanticContext.1.Elements :=
  categoryOfElements (target.semanticContext.1 : ContextCategoryᵒᵖ ⥤ Type)

/-- Universal receipt elimination reads the complete generated source-class
image at the independently supplied target interface. -/
theorem universal_classifying_value (point : sourcePrograms.Elements)
    (tree : Refinement.Derivation D (.term context term type)) :
    (valueReadout target).app (compilerMap.mapElements.obj point)
      ((carry (source target).certificates).app point
        (((source target).certificateSection tree).val point)) =
      (target.classifyingSection headers tree).val
        (target.interface.mapElements.obj (compilerMap.mapElements.obj point)) :=
  (valueReadout_computes target point tree).trans
    (target.classifying_value_readout headers tree (compilerMap.mapElements.obj point))

/-- The earned whole-class comparison fixes the complete section under any
map satisfying the independent local logical and primitive laws. -/
theorem model_map_classifying_section
    (tree : Refinement.Derivation D (.term context term type))
    (mapping : Refinement.Abstract.ModelMap
      (Refinement.Contextual.Interpretation.sourceData.{0,1} headers)
      (Refinement.Contextual.Interpretation.targetData target.qualifiedModel)) :
    Refinement.Contextual.ClassifyingEvidence.sectionImage target.qualifiedModel tree
      (Refinement.NativeAbstractScope.toGeneric target.semanticContext) target.semanticType
      target.qualified_context_read target.qualified_type_read headers mapping =
        target.classifyingSection headers tree := by
  unfold RefinementPresheafCertificates.Interpretation.classifyingSection
  rw [Refinement.Contextual.ClassifyingEvidence.sectionImage_readout,
    Refinement.Contextual.ClassifyingEvidence.sectionImage_readout]

/-- Universal compiler elimination reads this same actual source-term
image for every admitted interpretation, through the supplied interface. -/
theorem universal_model_map_value (point : sourcePrograms.Elements)
    (tree : Refinement.Derivation D (.term context term type))
    (mapping : Refinement.Abstract.ModelMap
      (Refinement.Contextual.Interpretation.sourceData.{0,1} headers)
      (Refinement.Contextual.Interpretation.targetData target.qualifiedModel)) :
    (valueReadout target).app (compilerMap.mapElements.obj point)
      ((carry (source target).certificates).app point
        (((source target).certificateSection tree).val point)) =
      (Refinement.Contextual.ClassifyingEvidence.sectionImage target.qualifiedModel tree
        (Refinement.NativeAbstractScope.toGeneric target.semanticContext) target.semanticType
        target.qualified_context_read target.qualified_type_read headers mapping).val
          (target.interface.mapElements.obj (compilerMap.mapElements.obj point)) := by
  rw [model_map_classifying_section headers target tree mapping]
  exact universal_classifying_value headers target point tree

/-- Every supplied coherent certificate has this readout; no distinguished
tree or source preimage is selected by elimination. -/
theorem universal_certificate_classifying_value (point : sourcePrograms.Elements)
    (certificate : (source target).Certificate point) :
    (valueReadout target).app (compilerMap.mapElements.obj point)
      ((carry (source target).certificates).app point certificate) =
      (target.classifyingSection headers certificate.tree).val
        (target.interface.mapElements.obj (compilerMap.mapElements.obj point)) := by
  rw [(source target).certificate_value_unique point certificate]
  exact universal_classifying_value headers target point certificate.tree

/-- Program-interface substitution commutes with the actual classifying
term image, including its complete dependent function section. -/
theorem compiler_classifying_section :
    (source target).classifyingValueSection headers = fun tree =>
      reindexDisplayedSection compilerMap target.valueFamily
        (target.classifyingValueSection headers tree) := by
  funext tree
  exact target.classifyingValueSection_substitution headers tree compilerMap

variable {headers target} {point : sourcePrograms.Elements}
variable {tree : Refinement.Derivation D (.term context term type)}
variable {world : NamePassingSpine.World (scope point)} {code : RhoUnaryCode.Code 0}
variable {final : RhoUnaryReadback.TargetProcess}
variable {actual : ExecutionPath RhoUnaryReadback.Target
  (RhoUnaryReadback.runtimeProcess code world.available) final}

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

/-- The receipt is indexed by the supplied actual execution, retaining its
exact endpoint and reflected history together with the source-class image. -/
theorem retain_classifying_runtime_prefix
    (headers : Refinement.HeaderFormation D)
    (target : Interpretation D context term type compiledPrograms)
    (point : sourcePrograms.Elements) (tree : Refinement.Derivation D (.term context term type))
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
  exact ⟨receipt, receipt.tree_retained, receipt.origin_retained,
    RuntimeReceipt.classifying_value (headers := headers) receipt⟩

section Refinement

variable {domain : Refinement.TypeExpr S n} {predicate : Refinement.PropExpr S (n + 1)}
variable (headers : Refinement.HeaderFormation D)
variable (target : Interpretation D context term (.comprehension domain predicate) compiledPrograms)
variable (A : NativeType target.semanticContext.1)
variable (selected : Subfunctor ((Refinement.NativeModel ContextCategory).toCwf.ext
  target.semanticContext.1 A))
variable (domainRead : target.model.evaluateType target.semanticContext domain = some A)
variable (predicateRead : target.model.evaluatePredicate (target.semanticContext.snoc A) predicate = some selected)
variable {point : sourcePrograms.Elements}
variable {tree : Refinement.Derivation D (.term context term (.comprehension domain predicate))}
variable {world : NamePassingSpine.World (scope point)} {code : RhoUnaryCode.Code 0}
variable {final : RhoUnaryReadback.TargetProcess}
variable {actual : ExecutionPath RhoUnaryReadback.Target
  (RhoUnaryReadback.runtimeProcess code world.available) final}

open RefinementPresheafComprehensionCertificates NamePassingRefinementGeneratedComprehension

/-- The independently evaluated domain and predicate expose the complete
selected inhabitant of the actual classifying term image. -/
theorem selectedSpecification_classifying_readout
    (receipt : RuntimeReceipt target point tree world code actual) :
    selectedSpecification target A selected domainRead predicateRead receipt =
      (decoder target A selected domainRead predicateRead).hom.app
        (target.interface.mapElements.obj (compilerMap.mapElements.obj point))
          ((target.classifyingSection headers tree).val
            (target.interface.mapElements.obj (compilerMap.mapElements.obj point))) := by
  unfold selectedSpecification
  rw [RuntimeReceipt.classifying_value (headers := headers) receipt]

/-- Membership is supplied by the generated interpretation and the actual
native decoder, rather than a separate predicate-respecting body premise. -/
theorem classifying_refinement_membership
    (receipt : RuntimeReceipt target point tree world code actual) :
    (⟨(target.interface.mapElements.obj (compilerMap.mapElements.obj point)).2,
      ((decoder target A selected domainRead predicateRead).hom.app
        (target.interface.mapElements.obj (compilerMap.mapElements.obj point))
          ((target.classifyingSection headers tree).val
            (target.interface.mapElements.obj (compilerMap.mapElements.obj point)))).val⟩ :
        (totalSpace A.decoded).obj point.1) ∈ selected.obj point.1 := by
  rw [← selectedSpecification_classifying_readout headers target A selected domainRead predicateRead receipt]
  exact selectedSpecification_membership target A selected domainRead predicateRead receipt

end Refinement

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedClassifyingContract
