import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedClassifyingContract
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedControls

/-!
# Complete classifying values on guarded and varying compiler interfaces

The actual classifying source image retains independently supplied positive
numbers and witnesses in Fin (n + 1). Two different witnesses at one input
remain different after universal compiler elimination. Two different authored
trees for one raw term have the same classifying value and different complete
compiler receipts. A missing guard rejects the same raw refinement term.

A supplied environment fetch and function call reaches an actual rho public
return. Its exact prefix receipt contains the source tree, original program
and the decoded classifying refinement value. The finite and guarded data are
native specifications; they are not instructions executed by the guest term.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedClassifyingControls

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension NativeLocalTypeFormers
open Calculi.NativeDependent
open RefinementPresheafCertificates RefinementPresheafComprehensionCertificates
open NamePassingDependentEvidence NamePassingDependentRuntimeEvidence
open NamePassingDependentRuntimeControls NamePassingSpineControls
open NamePassingCompilerReadback.Controls
open NamePassingRefinementGeneratedLogicalContract NamePassingRefinementGeneratedComprehension
open NamePassingRefinementGeneratedClassifyingContract
open NamePassingRefinementGeneratedControls

noncomputable section

theorem guarded_classifying_section_computes (number : Nat) (positive : 0 < number) :
    (target number positive).classifyingSection Refinement.Controls.headerFormation tree =
      (Native.conditionalRefined (C := ContextCategory)) :=
  ((target number positive).classifyingSection_eq_nativeSection Refinement.Controls.headerFormation tree).trans
    (native_section_computes number positive)

/-- A canonical native decoder reads the independently supplied positive
number from the actual classifying source-term image. -/
theorem guarded_classifying_decoder_retains_number (number : Nat) (positive : 0 < number)
    (point : compiledPrograms.Elements) :
    ((decoder (target number positive) Native.conditionalType Native.conditionalPredicate
      Native.conditional_type_read Native.conditional_predicate_read).hom.app
        ((target number positive).interface.mapElements.obj point)
          (((target number positive).classifyingSection Refinement.Controls.headerFormation tree).val
            ((target number positive).interface.mapElements.obj point))).val = number := by
  rw [(target number positive).classifyingSection_eq_nativeSection]
  exact decoder_retains_supplied_number number positive point

theorem finite_classifying_section_computes (number : Nat) (witness : Fin (Nat.succ number)) :
    (finiteTarget number witness).classifyingSection Refinement.Controls.headerFormation finiteTree =
      (Native.finiteVariable (C := ContextCategory)) :=
  ((finiteTarget number witness).classifyingSection_eq_nativeSection Refinement.Controls.headerFormation finiteTree).trans
    (finite_native_section_computes number witness)

/-- The entire supplied finite witness survives the actual source-class
image, at its genuinely input-dependent native type. -/
theorem finite_classifying_witness_retained (number : Nat) (witness : Fin (Nat.succ number))
    (point : compiledPrograms.Elements) :
    ((finiteTarget number witness).classifyingSection Refinement.Controls.headerFormation finiteTree).val
      ((finiteTarget number witness).interface.mapElements.obj point) = witness := by
  rw [finite_classifying_section_computes]
  exact Native.supplied_finite_witness_retained point.1 number witness

/-- The supplied witness is fixed for every interpretation satisfying the
independent local constructor and declaration laws, rather than only for the
canonical interpreter. -/
theorem every_admitted_model_map_retains_finite_witness
    (number : Nat) (witness : Fin (Nat.succ number))
    (mapping : Refinement.Abstract.ModelMap
      (Refinement.Contextual.Interpretation.sourceData.{0,1} Refinement.Controls.headerFormation)
      (Refinement.Contextual.Interpretation.targetData (finiteTarget number witness).qualifiedModel))
    (point : compiledPrograms.Elements) :
    (Refinement.Contextual.ClassifyingEvidence.sectionImage
      (finiteTarget number witness).qualifiedModel finiteTree
      (Refinement.NativeAbstractScope.toGeneric (finiteTarget number witness).semanticContext)
      (finiteTarget number witness).semanticType
      (finiteTarget number witness).qualified_context_read
      (finiteTarget number witness).qualified_type_read
      Refinement.Controls.headerFormation mapping).val
        ((finiteTarget number witness).interface.mapElements.obj point) = witness := by
  rw [model_map_classifying_section Refinement.Controls.headerFormation]
  exact finite_classifying_witness_retained number witness point

theorem compiled_every_admitted_model_map_retains_finite_witness
    (number : Nat) (witness : Fin (Nat.succ number))
    (mapping : Refinement.Abstract.ModelMap
      (Refinement.Contextual.Interpretation.sourceData.{0,1} Refinement.Controls.headerFormation)
      (Refinement.Contextual.Interpretation.targetData (finiteTarget number witness).qualifiedModel)) :
    (valueReadout (finiteTarget number witness)).app (compilerMap.mapElements.obj startPoint)
      ((carry (source (finiteTarget number witness)).certificates).app startPoint
        (((source (finiteTarget number witness)).certificateSection finiteTree).val startPoint)) = witness := by
  rw [universal_model_map_value Refinement.Controls.headerFormation
    (finiteTarget number witness) startPoint finiteTree mapping]
  exact every_admitted_model_map_retains_finite_witness number witness mapping _

theorem compiled_classifying_witness_retained (number : Nat) (witness : Fin (Nat.succ number)) :
    (valueReadout (finiteTarget number witness)).app (compilerMap.mapElements.obj startPoint)
      ((carry (source (finiteTarget number witness)).certificates).app startPoint
        (((source (finiteTarget number witness)).certificateSection finiteTree).val startPoint)) = witness := by
  rw [universal_classifying_value Refinement.Controls.headerFormation]
  exact finite_classifying_witness_retained number witness _

/-- Equal scalar input does not erase distinct supplied finite witnesses. -/
theorem same_input_distinct_witnesses_survive (number : Nat)
    (first second : Fin (Nat.succ number)) (distinct : first ≠ second) :
    (valueReadout (finiteTarget number first)).app (compilerMap.mapElements.obj startPoint)
      ((carry (source (finiteTarget number first)).certificates).app startPoint
        (((source (finiteTarget number first)).certificateSection finiteTree).val startPoint)) ≠
      (valueReadout (finiteTarget number second)).app (compilerMap.mapElements.obj startPoint)
        ((carry (source (finiteTarget number second)).certificates).app startPoint
          (((source (finiteTarget number second)).certificateSection finiteTree).val startPoint)) := by
  rw [compiled_classifying_witness_retained, compiled_classifying_witness_retained]
  exact distinct

theorem authored_tree_erasure_is_detected (number : Nat) (positive : 0 < number) :
    (target number positive).classifyingSection Refinement.Controls.headerFormation tree =
      (target number positive).classifyingSection Refinement.Controls.headerFormation convertedTree ∧
    (carry (source (target number positive)).certificates).app startPoint
      (((source (target number positive)).certificateSection tree).val startPoint) ≠
      (carry (source (target number positive)).certificates).app startPoint
        (((source (target number positive)).certificateSection convertedTree).val startPoint) :=
  ⟨(target number positive).classifyingSection_derivation_independent
      Refinement.Controls.headerFormation tree convertedTree,
    compiled_tree_receipts_remain_distinct number positive⟩

theorem missing_guard_cannot_supply_the_same_value :
    (Native.model (C := ContextCategory)).evaluateTerm Native.scalarScope syntaxTerm = none :=
  Native.unrestricted_refinement_rejected startPoint.1

/-- The same receipt contains the complete classifying value, retained
source tree and origin, and a supplied actual public-return execution. -/
theorem returning_execution_with_classifying_refinement (number : Nat) (positive : 0 < number) :
    ∃ final, ∃ actual : ExecutionPath RhoUnaryReadback.Target (process start) final,
      ∃ receipt : RuntimeReceipt (target number positive) startPoint tree
        (world names) (code start) actual,
        receipt.history.2.tree = tree ∧ receipt.nativeCertificate.val.1 = startPoint.2 ∧
          receipt.specification =
            (((target number positive).classifyingSection Refinement.Controls.headerFormation tree).val
              ((target number positive).interface.mapElements.obj (compilerMap.mapElements.obj startPoint))) ∧
          (selectedSpecification (target number positive) Native.conditionalType Native.conditionalPredicate
            Native.conditional_type_read Native.conditional_predicate_read receipt).val = number ∧
          (RhoUnaryInputObservation.targetPredicate (world names) .zero).1 final := by
  obtain ⟨final, ⟨actual⟩, observed⟩ := fetched_function_returns_in_rho
  obtain ⟨receipt, retainedTree, retainedOrigin, classifyingValue⟩ :=
    retain_classifying_runtime_prefix Refinement.Controls.headerFormation (target number positive)
      startPoint tree (world names) (code start) (supplied start) actual
  refine ⟨final, actual, receipt, retainedTree, retainedOrigin, classifyingValue, ?_, observed⟩
  rw [selectedSpecification_classifying_readout Refinement.Controls.headerFormation]
  exact guarded_classifying_decoder_retains_number number positive _

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedClassifyingControls
