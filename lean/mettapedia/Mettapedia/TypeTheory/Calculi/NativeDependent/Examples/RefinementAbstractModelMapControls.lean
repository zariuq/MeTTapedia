import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelMapReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementCanonicalModelMap
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelUniverseEvidence
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementAbstractInterpretationControls

/-!
# Generated-source images with guarded and varying native values

The canonical map from generated syntax to an independently authored native
model carries a supplied conditional-refinement certificate to its exact
natural-number section. Finite dependent fibres retain their supplied
parameter. A genuinely nonidentity argument map selects the newer variable;
using the older projection changes its reading. Deleting the positivity
assumption prevents a generated introduction tree in this same native
model. None of these comparisons identifies raw syntax with native values.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.AbstractModelMapControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualPredicateModelScopes ContextualPredicateScopeMorphism
open ContextualPredicateModelScopeUniverseLift ContextualModelTelescopes ContextualTelescopeMorphism
open ContextualComprehensionMorphism PresheafNativeStableRefinement
open Refinement.Abstract

noncomputable section

abbrev World := InterpretationControls.World
abbrev native := AbstractInterpretationControls.native

def nativeQualified : Contextual.Interpretation.QualifiedModel Controls.signature native where
  localModel := AbstractInterpretationControls.localModel
  data := AbstractInterpretationControls.model
  realization := AbstractInterpretationControls.realization
  products_substitution := AbstractInterpretationControls.qualified.stableProducts
  products_beta := AbstractInterpretationControls.qualified.productBeta
  products_eta := AbstractInterpretationControls.qualified.productEta

abbrev sourceQualified :=
  (Contextual.SyntacticModel.qualified Controls.headerFormation).carrierLift.{0,0,0,0,0,0,1,1,1,1,0}

abbrev targetQualified := nativeQualified.carrierLift.{0,1,0,1,0,0,1,1,1,1,0}
abbrev sourceBase := ContextualCwfUniverseLift.liftWithTerminal.{0,0,0,0,1,1,1,1}
  (Contextual.SyntacticModel.C Controls.signature)
abbrev targetBase := ContextualCwfUniverseLift.liftWithTerminal.{1,0,1,0,1,1,1,1} native
abbrev source := sourceQualified.data
abbrev target := targetQualified.data

def mapping : ModelMap source target :=
  Contextual.Interpretation.canonicalModelMap nativeQualified Controls.headerFormation

def sourceScope {n : Nat} {raw : ContextExpr Controls.symbols n}
    (tree : Derivation Controls.signature (.context raw)) :
    ModelScope sourceBase sourceQualified.localModel n :=
  Abstract.Derivation.contextValue source sourceQualified.realization
    sourceQualified.products_substitution sourceQualified.products_beta sourceQualified.products_eta tree

theorem sourceScope_read {n : Nat} {raw : ContextExpr Controls.symbols n}
    (tree : Derivation Controls.signature (.context raw)) :
    source.evaluateContext raw = some (sourceScope tree) :=
  Abstract.Derivation.contextValue_readout source sourceQualified.realization
    sourceQualified.products_substitution sourceQualified.products_beta sourceQualified.products_eta tree

theorem scope_image {n : Nat} {raw : ContextExpr Controls.symbols n}
    (tree : Derivation Controls.signature (.context raw))
    (scope : ModelScope targetBase targetQualified.localModel n)
    (targetRead : target.evaluateContext raw = some scope) :
    ScopeImage mapping.morphism (sourceScope tree) scope := by
  have read := mapping.evaluateContext_image raw (sourceScope tree) (sourceScope_read tree)
  have same := Option.some.inj (read.symm.trans targetRead)
  have actual := imageScope_comparison mapping.morphism mapping.predicates.assumptions (sourceScope tree)
  rw [same] at actual
  exact actual

abbrev targetConditionalScope :=
  liftScope.{1,0,1,0,0,1,1,1,1,0} AbstractInterpretationControls.conditionalScope

theorem target_conditional_context_read : target.evaluateContext Controls.conditionalContext =
    some targetConditionalScope :=
  nativeQualified.data.evaluateContext_carrierLift Controls.conditionalContext _
    AbstractInterpretationControls.conditional_context_read

def conditionalTypeTree : Derivation Controls.signature (.type Controls.conditionalContext
    (.comprehension (Controls.scalar 1) (Controls.positive 1))) :=
  deriveList (.comprehensionFormation Controls.conditionalContext (Controls.scalar 1) (Controls.positive 1))
    (.cons Controls.conditionalContextFormed
      (.cons (Controls.scalarFormed Controls.conditionalContextFormed)
        (.cons Controls.conditionalPredicate .nil)))

abbrev sourceConditionalScope := sourceScope Controls.conditionalContextFormed

def sourceConditionalType : sourceBase.toCwf.Ty sourceConditionalScope.1 :=
  Abstract.Derivation.typeValue source sourceQualified.realization
    sourceQualified.products_substitution sourceQualified.products_beta sourceQualified.products_eta
    conditionalTypeTree sourceConditionalScope (sourceScope_read Controls.conditionalContextFormed)

theorem source_conditional_type_read : source.evaluateType sourceConditionalScope
    (.comprehension (Controls.scalar 1) (Controls.positive 1)) = some sourceConditionalType :=
  Abstract.Derivation.typeValue_readout source sourceQualified.realization
    sourceQualified.products_substitution sourceQualified.products_beta sourceQualified.products_eta
    conditionalTypeTree sourceConditionalScope (sourceScope_read Controls.conditionalContextFormed)

def sourceConditionalCertificate : sourceBase.toCwf.Tm
    sourceConditionalScope.1 sourceConditionalType :=
  Abstract.Derivation.termSection source sourceQualified.realization
    sourceQualified.products_substitution sourceQualified.products_beta sourceQualified.products_eta
    Controls.conditionalRefinement sourceConditionalScope sourceConditionalType
    (sourceScope_read Controls.conditionalContextFormed) source_conditional_type_read

theorem source_conditional_certificate_read : source.evaluateTerm sourceConditionalScope
    (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0)) =
      some ⟨sourceConditionalType, sourceConditionalCertificate⟩ :=
  Abstract.Derivation.termSection_readout source sourceQualified.realization
    sourceQualified.products_substitution sourceQualified.products_beta sourceQualified.products_eta
    Controls.conditionalRefinement sourceConditionalScope sourceConditionalType
    (sourceScope_read Controls.conditionalContextFormed) source_conditional_type_read

set_option backward.isDefEq.respectTransparency false in
theorem target_conditional_certificate_read : target.evaluateTerm targetConditionalScope
    (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0)) =
      some ⟨ULift.up (chosen InterpretationControls.conditionalType InterpretationControls.conditionalPredicate),
        ULift.up InterpretationControls.conditionalRefined⟩ :=
  nativeQualified.data.evaluateTerm_carrierLift _ _ _
    AbstractInterpretationControls.conditional_refinement_read

set_option backward.isDefEq.respectTransparency false in
theorem complete_conditional_certificate_image : ValueImage mapping.morphism
    (⟨sourceConditionalType, sourceConditionalCertificate⟩ : Value sourceBase.toCwf sourceConditionalScope.1)
    (⟨ULift.up (chosen InterpretationControls.conditionalType InterpretationControls.conditionalPredicate),
      ULift.up InterpretationControls.conditionalRefined⟩ : Value targetBase.toCwf targetConditionalScope.1) :=
  mapping.evaluateTerm_image_unique _ sourceConditionalScope targetConditionalScope
    (scope_image Controls.conditionalContextFormed _ target_conditional_context_read) _ _
      source_conditional_certificate_read target_conditional_certificate_read

set_option backward.isDefEq.respectTransparency false in
theorem exact_supplied_certificate_image :
    HEq (mapping.morphism.toFamilyMorphism.mapTerm sourceConditionalCertificate)
      (ULift.up InterpretationControls.conditionalRefined) :=
  complete_conditional_certificate_image.terms

theorem supplied_positive_input_retained (world : Worldᵒᵖ) (number : Nat) (positive : 0 < number) :
    (forget InterpretationControls.conditionalType InterpretationControls.conditionalPredicate
      (ULift.up InterpretationControls.conditionalRefined).down).val
        ⟨world, InterpretationControls.positiveBase world number positive⟩ = number :=
  InterpretationControls.supplied_number_retained world number positive

abbrev targetScalarScope :=
  liftScope.{1,0,1,0,0,1,1,1,1,0} AbstractInterpretationControls.scalarScope

theorem target_scalar_context_read : target.evaluateContext (.snoc .nil (Controls.scalar 0)) =
    some targetScalarScope :=
  nativeQualified.data.evaluateContext_carrierLift _ _
    ((Refinement.ModelData.evaluateContext_compare InterpretationControls.model _).trans
      (congrArg (Option.map NativeAbstractScope.toGeneric) InterpretationControls.scalar_context_read))

theorem mapped_fibre_read : ∃ annotation : sourceBase.toCwf.Ty
    (sourceScope Controls.scalarContext).1,
    source.evaluateType (sourceScope Controls.scalarContext) (Controls.fibre 0) = some annotation ∧
    HEq (mapping.morphism.toFamilyMorphism.mapType annotation)
      (ULift.up.{1,1} InterpretationControls.fibreType) := by
  have formed := Controls.fibreFormed Controls.scalarContext
    (by simpa only [ContextExpr.lookup_zero, Controls.scalar_rename] using
      Controls.lookupVariable Controls.scalarContext 0)
  rcases (Abstract.Derivation.sound source sourceQualified.realization
    sourceQualified.products_substitution sourceQualified.products_beta sourceQualified.products_eta formed).typeAt
      _ (sourceScope_read Controls.scalarContext) with ⟨annotation, read⟩
  refine ⟨annotation, read, ?_⟩
  exact mapping.evaluateType_image_unique _ _ _
    (scope_image Controls.scalarContext targetScalarScope target_scalar_context_read) _ _ read
    (nativeQualified.data.evaluateType_carrierLift _ _ _ AbstractInterpretationControls.varying_fibre_read)

theorem actual_fibre_depends_on_input (world : Worldᵒᵖ) (number : Nat) :
    InterpretationControls.fibreType.decoded.obj
      ⟨world, (⟨PUnit.unit, number⟩ : AbstractInterpretationControls.scalarScope.1.obj world)⟩ =
        Fin (Nat.succ number) := AbstractInterpretationControls.varying_fibre_value world number

def doubleContextTree : Derivation Controls.signature
    (.context (.snoc (.snoc .nil (Controls.scalar 0)) (Controls.scalar 1))) :=
  Controls.extendContext Controls.scalarContext (Controls.scalarFormed Controls.scalarContext)

abbrev targetDoubleScope :=
  liftScope.{1,0,1,0,0,1,1,1,1,0} AbstractInterpretationControls.doubleScope

theorem target_double_context_read : target.evaluateContext
    (.snoc (.snoc .nil (Controls.scalar 0)) (Controls.scalar 1)) = some targetDoubleScope := by
  have nativeRead := InterpretationControls.model.evaluateContext_snoc _ _ _ _
    InterpretationControls.scalar_context_read InterpretationControls.scalar_variable_type_read
  have abstractRead := (Refinement.ModelData.evaluateContext_compare InterpretationControls.model _).trans
    (congrArg (Option.map NativeAbstractScope.toGeneric) nativeRead)
  exact nativeQualified.data.evaluateContext_carrierLift _ _ abstractRead

def newestArgumentTree : Derivation Controls.signature (.substitution
    (.snoc (.snoc .nil (Controls.scalar 0)) (Controls.scalar 1))
    (.snoc .nil (Controls.scalar 0)) (Controls.singletonArgument (.var 0))) :=
  Controls.scalarArguments doubleContextTree
    (by simpa only [ContextExpr.lookup_zero, Controls.scalar_rename] using
      Controls.lookupVariable doubleContextTree 0)

def sourceNewestArgument : sourceBase.toCwf.Sub (sourceScope doubleContextTree).1
    (sourceScope Controls.scalarContext).1 :=
  Abstract.Derivation.substitutionArrow source sourceQualified.realization
    sourceQualified.products_substitution sourceQualified.products_beta sourceQualified.products_eta
    newestArgumentTree (sourceScope doubleContextTree) (sourceScope Controls.scalarContext)
    (sourceScope_read doubleContextTree) (sourceScope_read Controls.scalarContext)

theorem source_newest_argument_read : source.evaluateSubstitution
    (sourceScope doubleContextTree) (sourceScope Controls.scalarContext)
    (Controls.singletonArgument (.var 0)) = some sourceNewestArgument :=
  Abstract.Derivation.substitutionArrow_readout source sourceQualified.realization
    sourceQualified.products_substitution sourceQualified.products_beta sourceQualified.products_eta
    newestArgumentTree _ _ (sourceScope_read doubleContextTree) (sourceScope_read Controls.scalarContext)

theorem actual_newer_argument_image : imageArrow mapping.morphism
    (scope_image doubleContextTree targetDoubleScope target_double_context_read).contexts
    (scope_image Controls.scalarContext targetScalarScope target_scalar_context_read).contexts
    sourceNewestArgument = ULift.up InterpretationControls.newestScalar := by
  have read := mapping.evaluateSubstitution_image _ _ _ _
    (scope_image doubleContextTree targetDoubleScope target_double_context_read)
    (scope_image Controls.scalarContext targetScalarScope target_scalar_context_read)
    _ _ source_newest_argument_read
  have independent := nativeQualified.data.evaluateSubstitution_carrierLift _ _ _ _
    AbstractInterpretationControls.newer_argument_read
  exact Option.some.inj (read.symm.trans independent)

theorem omitting_the_selected_argument_changes_the_reading :
    ULift.up InterpretationControls.newestScalar ≠
      (ULift.up (native.toCwf.wk InterpretationControls.scalarVariableType) :
        targetBase.toCwf.Sub targetDoubleScope.1 targetScalarScope.1) := by
  intro same
  exact AbstractInterpretationControls.newer_argument_is_not_older_projection (congrArg ULift.down same)

set_option backward.isDefEq.respectTransparency false in
theorem removing_positivity_prevents_a_generated_refinement :
    ¬ Nonempty (Derivation Controls.signature (.term (.snoc .nil (Controls.scalar 0))
      (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0))
      (.comprehension (Controls.scalar 1) (Controls.positive 1)))) := by
  rintro ⟨tree⟩
  rcases Abstract.Derivation.qualified_sound AbstractInterpretationControls.model
    AbstractInterpretationControls.realization
    AbstractInterpretationControls.qualified tree with ⟨Γ, A, value, contextRead, _, termRead⟩
  have nativeContext := (Refinement.ModelData.evaluateContext_compare InterpretationControls.model _).trans
    (congrArg (Option.map NativeAbstractScope.toGeneric) InterpretationControls.scalar_context_read)
  cases Option.some.inj (contextRead.symm.trans nativeContext)
  change AbstractInterpretationControls.model.evaluateTerm
    AbstractInterpretationControls.scalarScope _ = some ⟨A, value⟩ at termRead
  have impossible := AbstractInterpretationControls.unrestricted_refinement_rejected.symm.trans termRead
  cases impossible

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.AbstractModelMapControls
