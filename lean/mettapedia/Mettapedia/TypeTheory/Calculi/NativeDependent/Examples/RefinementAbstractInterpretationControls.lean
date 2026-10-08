import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractEvidenceExtraction
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementInterpretationControls

/-!
# A varying native instance of the local-model refinement interpreter

Natural-number inputs, finite dependent fibres and the proper positivity
predicate exercise the independently proved arbitrary-model rule fold.
The exact generated certificate is extracted and compared with its authored
value. A nonidentity argument map selects the newer data variable. Removing
the assumption rejects refinement, while distinct positive inputs retain
distinct values. Higher-order predicates use actual function-valued inputs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.AbstractInterpretationControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open NativeLocalTypeFormers PresheafNativeStableRefinement
open ContextualPredicateModel ContextualModelTelescopes

noncomputable section

abbrev World := InterpretationControls.World
abbrev native := InterpretationControls.native
abbrev localModel := PresheafNativePredicateModel.model World

def model : Abstract.ModelData Controls.symbols native localModel :=
  InterpretationControls.model.toAbstract

theorem realization : Abstract.SignatureRealization model Controls.signature :=
  InterpretationControls.realization.toAbstract

theorem qualified : Qualification localModel := PresheafNativePredicateModel.qualification World

abbrev scalarScope := NativeAbstractScope.toGeneric InterpretationControls.scalarScope
abbrev doubleScope := NativeAbstractScope.toGeneric InterpretationControls.doubleScope
abbrev conditionalScope := NativeAbstractScope.toGeneric InterpretationControls.conditionalScope

theorem conditional_context_read : model.evaluateContext Controls.conditionalContext =
    some conditionalScope := by
  change InterpretationControls.model.toAbstract.evaluateContext Controls.conditionalContext = _
  rw [ModelData.evaluateContext_compare, InterpretationControls.conditional_context_read,
    Option.map_some]

theorem conditional_type_read : model.evaluateType conditionalScope (Controls.scalar 1) =
    some InterpretationControls.conditionalType := by
  change InterpretationControls.model.toAbstract.evaluateType
    (NativeAbstractScope.toGeneric InterpretationControls.conditionalScope) (Controls.scalar 1) = _
  rw [ModelData.evaluateType_compare, InterpretationControls.conditional_type_read]

set_option backward.isDefEq.respectTransparency false in
theorem conditional_comprehension_read : model.evaluateType conditionalScope
    (.comprehension (Controls.scalar 1) (Controls.positive 1)) =
      some (chosen InterpretationControls.conditionalType InterpretationControls.conditionalPredicate) := by
  change InterpretationControls.model.toAbstract.evaluateType
    (NativeAbstractScope.toGeneric InterpretationControls.conditionalScope) _ = _
  exact (ModelData.evaluateType_compare InterpretationControls.model _ _).trans
    (InterpretationControls.model.evaluate_comprehension InterpretationControls.conditionalScope
    (Controls.scalar 1) (Controls.positive 1) InterpretationControls.conditionalType
    InterpretationControls.conditionalPredicate InterpretationControls.conditional_type_read
    InterpretationControls.conditional_predicate_read)

theorem conditional_refinement_read : model.evaluateTerm conditionalScope
    (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0)) =
      some ⟨chosen InterpretationControls.conditionalType InterpretationControls.conditionalPredicate,
        InterpretationControls.conditionalRefined⟩ := by
  change InterpretationControls.model.toAbstract.evaluateTerm
    (NativeAbstractScope.toGeneric InterpretationControls.conditionalScope) _ = _
  rw [ModelData.evaluateTerm_compare, InterpretationControls.conditional_refinement_read]
  rfl

/-- This result uses the arbitrary local-model tree fold, rather than the
separate native soundness theorem. -/
theorem conditional_generated_sound : Abstract.Interprets model
    (.term Controls.conditionalContext
      (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0))
      (.comprehension (Controls.scalar 1) (Controls.positive 1))) :=
  Abstract.Derivation.qualified_sound model realization qualified Controls.conditionalRefinement

def conditionalCertificate :
    (chosen InterpretationControls.conditionalType InterpretationControls.conditionalPredicate).decoded.sections :=
  Abstract.Derivation.termSection model realization qualified.stableProducts qualified.productBeta
    qualified.productEta Controls.conditionalRefinement conditionalScope _
    conditional_context_read conditional_comprehension_read

theorem conditional_certificate_exact : conditionalCertificate = InterpretationControls.conditionalRefined :=
  Abstract.Derivation.termSection_unique model realization qualified.stableProducts qualified.productBeta
    qualified.productEta Controls.conditionalRefinement conditionalScope _
    conditional_context_read conditional_comprehension_read _ conditional_refinement_read

theorem supplied_number_retained (world : Worldᵒᵖ) (number : Nat) (positive : 0 < number) :
    (forget InterpretationControls.conditionalType InterpretationControls.conditionalPredicate
      conditionalCertificate).val ⟨world, InterpretationControls.positiveBase world number positive⟩ = number := by
  rw [conditional_certificate_exact]
  exact InterpretationControls.supplied_number_retained world number positive

theorem distinct_numbers_retained (world : Worldᵒᵖ) :
    (forget InterpretationControls.conditionalType InterpretationControls.conditionalPredicate
      conditionalCertificate).val ⟨world, InterpretationControls.positiveBase world 1 (by decide)⟩ ≠
    (forget InterpretationControls.conditionalType InterpretationControls.conditionalPredicate
      conditionalCertificate).val ⟨world, InterpretationControls.positiveBase world 2 (by decide)⟩ := by
  rw [supplied_number_retained, supplied_number_retained]
  exact (by decide : (1 : Nat) ≠ 2)

theorem varying_fibre_read : model.evaluateType scalarScope (Controls.fibre 0) =
    some InterpretationControls.fibreType := by
  change InterpretationControls.model.toAbstract.evaluateType
    (NativeAbstractScope.toGeneric InterpretationControls.scalarScope) (Controls.fibre 0) = _
  rw [ModelData.evaluateType_compare, InterpretationControls.fibre_scalar_read]

theorem varying_fibre_value (world : Worldᵒᵖ) (number : Nat) :
    InterpretationControls.fibreType.decoded.obj
      ⟨world, (⟨PUnit.unit, number⟩ : scalarScope.1.obj world)⟩ = Fin (Nat.succ number) := rfl

theorem newer_argument_read : model.evaluateSubstitution doubleScope scalarScope
    (Controls.singletonArgument (.var 0)) = some InterpretationControls.newestScalar := by
  change InterpretationControls.model.toAbstract.evaluateSubstitution
    (NativeAbstractScope.toGeneric InterpretationControls.doubleScope)
    (NativeAbstractScope.toGeneric InterpretationControls.scalarScope) _ = _
  rw [ModelData.evaluateSubstitution_compare]
  apply (InterpretationControls.model.evaluateSubstitution_eq_some_iff _ _ _ _).mpr
  intro index
  cases index using Fin.cases with
  | zero =>
      exact congrArg some (InterpretationControls.newestRenaming.readout 0)
  | succ impossible => exact Fin.elim0 impossible

set_option backward.isDefEq.respectTransparency false in
theorem newer_argument_is_not_older_projection : InterpretationControls.newestScalar ≠
    native.toCwf.wk InterpretationControls.scalarVariableType := by
  intro equal
  let world : Worldᵒᵖ := Opposite.op WalkingParallelPair.zero
  let supplied : InterpretationControls.doubleScope.1.obj world :=
    ⟨⟨PUnit.unit, (1 : Nat)⟩, (2 : Nat)⟩
  have pointRead := ConcreteCategory.congr_hom (NatTrans.congr_app equal world) supplied
  have numbers : (2 : Nat) = 1 := congrArg
    (fun point : InterpretationControls.scalarScope.1.obj world => (show Nat from point.2)) pointRead
  exact (by decide : ¬ (2 : Nat) = 1) numbers

theorem unrestricted_refinement_rejected : model.evaluateTerm scalarScope
    (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0)) = none := by
  change InterpretationControls.model.toAbstract.evaluateTerm
    (NativeAbstractScope.toGeneric InterpretationControls.scalarScope) _ = _
  rw [ModelData.evaluateTerm_compare, InterpretationControls.unrestricted_refinement_rejected]
  rfl

theorem conditional_beta_sound : Abstract.Interprets model
    (.termEq Controls.conditionalContext
      (.forget (Controls.scalar 1) (Controls.positive 1)
        (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0)))
      (.var 0) (Controls.scalar 1)) :=
  Abstract.Derivation.qualified_sound model realization qualified Controls.conditionalBeta

theorem mixed_annotation_sound : Abstract.Interprets model
    (.termEq (.snoc .nil (Controls.scalar 0))
      (.refine (Controls.scalar 1) .truth (.var 0))
      (.refine (Controls.scalar 1) (.and .truth .truth) (.var 0))
      (.comprehension (Controls.scalar 1) .truth)) :=
  Abstract.Derivation.qualified_sound model realization qualified Controls.annotationRefinement

theorem higher_order_generated_sound : Abstract.Interprets model
    (.entails .nil (.all (Controls.predicateFunctionAt 0)
      (.all (Controls.scalar 1)
        (.implies Controls.appliedPredicate Controls.appliedPredicate)))) :=
  Abstract.Derivation.qualified_sound model realization qualified Controls.quantifiedPredicateFunction

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.AbstractInterpretationControls
