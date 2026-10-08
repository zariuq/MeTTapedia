import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementNativeDeclarationModels
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedComprehension
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeControls

/-!
# Generated guarded specifications on a supplied returning compiler run

An independently realized positive scalar refinement supplies a coherent
generated certificate at the actual compiler interface. Its canonical
decoder retains the supplied number and proves the interpreted positivity
predicate. The same receipt contains a supplied returning rho execution.
Different generated trees with the same raw term have equal native values
and distinct complete compiler receipts. Removing the positivity assumption
rejects the authored introduction at an actual supplied world.

The model also has genuinely varying Fin (n + 1) fibres. The guest lambda
program does not execute natural-number or finite-value instructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedControls

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension NativeLocalTypeFormers
open Calculi.NativeDependent
open Refinement (deriveList PremiseEvidence)
open RefinementPresheafCertificates RefinementPresheafComprehensionCertificates
open NamePassingDependentEvidence NamePassingDependentRuntimeEvidence
open NamePassingDependentRuntimeControls NamePassingSpineControls
open NamePassingCompilerReadback.Controls
open NamePassingRefinementGeneratedLogicalContract NamePassingRefinementGeneratedComprehension

namespace Native
export Refinement.NativeDeclarationModels
  (model realization conditionalScope conditionalType conditionalPredicate
    conditional_context_read conditional_type_read conditional_predicate_read
    conditionalRefined conditional_refinement_read positiveBase supplied_number_retained
    varying_fibre_readout fibreType unrestricted_refinement_rejected scalarScope
    finiteScope finiteVariableType finiteVariable finiteBase finite_context_read
    finite_variable_type_read finite_variable_read supplied_finite_witness_retained)
end Native

abbrev syntaxContext := Refinement.Controls.conditionalContext
abbrev syntaxDomain := Refinement.Controls.scalar 1
abbrev syntaxPredicate := Refinement.Controls.positive 1
abbrev syntaxTerm : Refinement.TermExpr Refinement.Controls.symbols 1 :=
  .refine syntaxDomain syntaxPredicate (.var 0)
abbrev syntaxType : Refinement.TypeExpr Refinement.Controls.symbols 1 :=
  .comprehension syntaxDomain syntaxPredicate
abbrev tree := Refinement.Controls.conditionalRefinement

noncomputable section

def interface (number : Nat) (positive : 0 < number) :
    compiledPrograms ⟶ (Native.conditionalScope (C := ContextCategory)).1 where
  app world := TypeCat.ofHom fun _ => Native.positiveBase world number positive
  naturality := by
    intro first second arrow
    apply ConcreteCategory.hom_ext
    intro program
    apply Subtype.ext
    rfl

def target (number : Nat) (positive : 0 < number) :
    Interpretation Refinement.Controls.signature syntaxContext syntaxTerm syntaxType compiledPrograms where
  model := Native.model
  realization := Native.realization
  semanticContext := Native.conditionalScope
  semanticType := PresheafNativeStableRefinement.chosen Native.conditionalType Native.conditionalPredicate
  contextRead := Native.conditional_context_read
  typeRead := Native.model.evaluate_comprehension Native.conditionalScope syntaxDomain syntaxPredicate
    Native.conditionalType Native.conditionalPredicate Native.conditional_type_read Native.conditional_predicate_read
  interface := interface number positive

theorem native_section_computes (number : Nat) (positive : 0 < number) :
    (target number positive).nativeSection tree = (Native.conditionalRefined (C := ContextCategory)) :=
  tree.termSection_unique Native.model Native.realization
    (NativeLocalTypeOperations.products_substitution ContextCategory)
    (NativeLocalTypeOperations.products_beta ContextCategory) (NativeLocalPiEta.products_eta ContextCategory)
    Native.conditionalScope _ Native.conditional_context_read
    (target number positive).typeRead _ Native.conditional_refinement_read

theorem decoder_retains_supplied_number (number : Nat) (positive : 0 < number)
    (point : compiledPrograms.Elements) :
    ((selectedValueReadout (target number positive) Native.conditionalType Native.conditionalPredicate
      Native.conditional_type_read Native.conditional_predicate_read).app point
        (((target number positive).certificateSection tree).val point)).val = number := by
  rw [selectedValue_computes, native_section_computes]
  change (PresheafNativeStableRefinement.forget Native.conditionalType Native.conditionalPredicate
    Native.conditionalRefined).val ⟨point.1, Native.positiveBase point.1 number positive⟩ = number
  exact Native.supplied_number_retained point.1 number positive

/-- Both runtime observation and generated predicate membership occur in one
receipt for the exact supplied source program and compiler execution. -/
theorem returning_execution_with_generated_refinement (number : Nat) (positive : 0 < number) :
    ∃ final, ∃ actual : ExecutionPath RhoUnaryReadback.Target (process start) final,
      ∃ receipt : RuntimeReceipt (target number positive) startPoint tree
        (world names) (code start) actual,
        receipt.history.2.tree = tree ∧ receipt.nativeCertificate.val.1 = startPoint.2 ∧
          (selectedSpecification (target number positive) Native.conditionalType Native.conditionalPredicate
            Native.conditional_type_read Native.conditional_predicate_read receipt).val = number ∧
          (RhoUnaryInputObservation.targetPredicate (world names) .zero).1 final := by
  obtain ⟨final, ⟨actual⟩, observed⟩ := fetched_function_returns_in_rho
  obtain ⟨receipt⟩ := retain_runtime_prefix (target number positive) startPoint tree
    (world names) (code start) (supplied start) actual
  refine ⟨final, actual, receipt, receipt.tree_retained, receipt.origin_retained, ?_, observed⟩
  rw [selectedSpecification_computes]
  exact decoder_retains_supplied_number number positive _

def formationTree : Refinement.Derivation Refinement.Controls.signature (.type syntaxContext syntaxType) :=
  deriveList (.comprehensionFormation syntaxContext syntaxDomain syntaxPredicate)
    (.cons Refinement.Controls.conditionalContextFormed
      (.cons (Refinement.Controls.scalarFormed Refinement.Controls.conditionalContextFormed)
        (.cons Refinement.Controls.conditionalPredicate .nil)))

def convertedTree : Refinement.Derivation Refinement.Controls.signature
    (.term syntaxContext syntaxTerm syntaxType) :=
  deriveList (.termConversion syntaxContext syntaxTerm syntaxType syntaxType)
    (.cons tree (.cons (deriveList (.typeReflexivity syntaxContext syntaxType) (.cons formationTree .nil)) .nil))

theorem authored_trees_remain_distinct : tree ≠ convertedTree := by
  intro equal
  have impossible := congrArg Refinement.Derivation.rootRule equal
  cases impossible

theorem compiled_tree_receipts_remain_distinct (number : Nat) (positive : 0 < number) :
    (carry (source (target number positive)).certificates).app startPoint
      (((source (target number positive)).certificateSection tree).val startPoint) ≠
    (carry (source (target number positive)).certificates).app startPoint
      (((source (target number positive)).certificateSection convertedTree).val startPoint) :=
  fun same => authored_trees_remain_distinct (source_receipt_tree_injective (target number positive) startPoint same)

/-- Erasing the retained tree keeps only an evaluator value and collapses
these distinct authored certificates. -/
theorem native_values_erase_authored_trees (number : Nat) (positive : 0 < number) :
    (valueReadout (target number positive)).app (compilerMap.mapElements.obj startPoint)
      ((carry (source (target number positive)).certificates).app startPoint
        (((source (target number positive)).certificateSection tree).val startPoint)) =
    (valueReadout (target number positive)).app (compilerMap.mapElements.obj startPoint)
      ((carry (source (target number positive)).certificates).app startPoint
        (((source (target number positive)).certificateSection convertedTree).val startPoint)) := by
  rw [valueReadout_computes, valueReadout_computes]
  exact congrArg (fun certificate => certificate.val (compilerMap.mapElements.obj startPoint))
    ((target number positive).valueSection_derivation_independent tree convertedTree)

theorem missing_positive_assumption_rejects_the_same_introduction :
    (Native.model (C := ContextCategory)).evaluateTerm Native.scalarScope syntaxTerm = none :=
  Native.unrestricted_refinement_rejected startPoint.1

theorem finite_specification_really_depends_on_its_input (point : compiledPrograms.Elements) (number : Nat) :
    (Native.fibreType (C := ContextCategory)).decoded.obj
      ⟨point.1, ⟨PUnit.unit, number⟩⟩ = Fin (Nat.succ number) :=
  Native.varying_fibre_readout point.1 number

abbrev finiteSyntaxContext : Refinement.ContextExpr Refinement.Controls.symbols 2 :=
  .snoc (.snoc .nil (Refinement.Controls.scalar 0)) (Refinement.Controls.fibre 0)

abbrev finiteSyntaxType := finiteSyntaxContext.lookup 0

def finiteTree : Refinement.Derivation Refinement.Controls.signature
    (.term finiteSyntaxContext (.var 0) finiteSyntaxType) :=
  Refinement.Controls.lookupVariable Refinement.Controls.dependentSuffixFormed.context 0

def finiteInterface (number : Nat) (witness : Fin (Nat.succ number)) :
    compiledPrograms ⟶ (Native.finiteScope (C := ContextCategory)).1 where
  app world := TypeCat.ofHom fun _ => Native.finiteBase world number witness
  naturality := by intros; rfl

def finiteTarget (number : Nat) (witness : Fin (Nat.succ number)) :
    Interpretation Refinement.Controls.signature finiteSyntaxContext (.var 0) finiteSyntaxType compiledPrograms where
  model := Native.model
  realization := Native.realization
  semanticContext := Native.finiteScope
  semanticType := Native.finiteVariableType
  contextRead := Native.finite_context_read
  typeRead := Native.finite_variable_type_read
  interface := finiteInterface number witness

theorem finite_native_section_computes (number : Nat) (witness : Fin (Nat.succ number)) :
    (finiteTarget number witness).nativeSection finiteTree = (Native.finiteVariable (C := ContextCategory)) :=
  finiteTree.termSection_unique Native.model Native.realization
    (NativeLocalTypeOperations.products_substitution ContextCategory)
    (NativeLocalTypeOperations.products_beta ContextCategory) (NativeLocalPiEta.products_eta ContextCategory)
    Native.finiteScope _ Native.finite_context_read
    (finiteTarget number witness).typeRead _ Native.finite_variable_read

theorem finite_certificate_retains_supplied_witness (number : Nat) (witness : Fin (Nat.succ number))
    (point : compiledPrograms.Elements) :
    (((finiteTarget number witness).certificateSection finiteTree).val point).value = witness := by
  change ((finiteTarget number witness).nativeSection finiteTree).val
    ((finiteTarget number witness).interface.mapElements.obj point) = witness
  rw [finite_native_section_computes]
  exact Native.supplied_finite_witness_retained point.1 number witness

theorem compiled_finite_certificate_retains_supplied_witness
    (number : Nat) (witness : Fin (Nat.succ number)) :
    (valueReadout (finiteTarget number witness)).app (compilerMap.mapElements.obj startPoint)
      ((carry (source (finiteTarget number witness)).certificates).app startPoint
        (((source (finiteTarget number witness)).certificateSection finiteTree).val startPoint)) = witness := by
  rw [valueReadout_computes]
  exact finite_certificate_retains_supplied_witness number witness _

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedControls
